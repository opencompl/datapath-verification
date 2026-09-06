import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.BVComb
import DatapathVerification.BitHeap.Compressors.DaddaTree
import Std.Data.HashMap

/-!
Netlist emission for compressed bit heaps.

Serializes a two-row bit heap as a flat, hash-consed gate netlist in a
line-based text format consumed by the CIRCT `comb-verified-datapath` pass:

```
ok mul <width>
gate g0 and b0 b4
gate g1 xor g0 b2
...
row0 b0 g0 g3 -
row1 - g1 g2 g4
```

References are `b<i>` (input bit `i % w` of operand `i / w`), `g<i>` (gate
outputs, defined before use), or `c0`/`c1` (constants). A `-` in a row line
means the column has no bit there (a constant 0). Shared subcircuits are
emitted exactly once.
-/

namespace BitHeap

namespace Netlist

structure EmitState where
  lines : Array String := #[]
  cache : Std.HashMap Circuit String := {}
  nextId : Nat := 0

private def opName : Binop → String
  | .and => "and"
  | .or => "or"
  | .xor => "xor"
  | .nand => "nand"

/-- Emit a circuit as netlist gate lines, returning its reference. Shared
subcircuits are cached so each distinct gate is printed only once. -/
partial def emitCircuit (c : Circuit) : StateM EmitState String := do
  if let some r := (← MonadState.get).cache[c]? then
    return r
  let ref ← match c with
    | .bit n => pure s!"b{n}"
    | .const b => pure (if b then "c1" else "c0")
    | .binop op a b => do
        let ra ← emitCircuit a
        let rb ← emitCircuit b
        modifyGet fun s =>
          (s!"g{s.nextId}",
           { s with
              nextId := s.nextId + 1
              lines := s.lines.push s!"gate g{s.nextId} {opName op} {ra} {rb}" })
    | .unaryop .neg a => do
        -- The protocol has no unary gate; `nand x x` is the inverter.
        -- Unreachable from add/mul/zext, which never build a `neg`.
        let ra ← emitCircuit a
        modifyGet fun s =>
          (s!"g{s.nextId}",
           { s with
              nextId := s.nextId + 1
              lines := s.lines.push s!"gate g{s.nextId} nand {ra} {ra}" })
  modify fun s => { s with cache := s.cache.insert c ref }
  return ref

/--
Emit a (at most two-row) bit heap as a netlist: all gate definitions followed
by a `row0` and `row1` line with one entry per column. Fails if any column
holds more than two bits.
-/
def emitHeap (h : BitHeap w) : Except String (Array String) := Id.run do
  let mut st : EmitState := {}
  let mut row0 : Array String := #[]
  let mut row1 : Array String := #[]
  for k in List.range w do
    let bits := (h.get k).toList
    match bits with
    | [] =>
        row0 := row0.push "-"
        row1 := row1.push "-"
    | [a] =>
        let (ra, st') := (emitCircuit a).run st
        st := st'
        row0 := row0.push ra
        row1 := row1.push "-"
    | [a, b] =>
        let (ra, st') := (emitCircuit a).run st
        let (rb, st'') := (emitCircuit b).run st'
        st := st''
        row0 := row0.push ra
        row1 := row1.push rb
    | _ =>
        return .error s!"column {k} has {bits.length} bits; expected at most 2"
  let mut lines := st.lines
  lines := lines.push ("row0 " ++ " ".intercalate row0.toList)
  lines := lines.push ("row1 " ++ " ".intercalate row1.toList)
  return .ok lines

/--
Run the verified compression flow for an arithmetic circuit and emit the
result as a netlist, prefixed by the given header line.

The emitted heap is the one produced by `Chain.applyChainSafe`, so by
`Comb.ArithCircuit.compressed_toBitHeap_correct` its modular evaluation equals
the denotation of the circuit.
-/
def compressArith (header : String) (c : Comb.ArithCircuit w) :
    Except String (Array String) := do
  let h := c.toBitHeap
  let (_, adders) := DaddaTree.DaddaTree h
  match Chain.applyChainSafe adders h with
  | none => throw "adder chain replay failed applicability check"
  | some h' => do
      let lines ← emitHeap h'
      return #[header] ++ lines

/--
Verified compression of a `w`-bit multiply of two operands with live widths
`wa` and `wb`: operand bits at positions ≥ the live width are constant 0
(zero-extension) and never enter the bit heap.
-/
def compressMul (w wa wb : Nat) : Except String (Array String) := do
  if w == 0 then
    throw "width must be positive"
  let wa := min wa w
  let wb := min wb w
  if hab : wa ≤ w ∧ wb ≤ w then
    compressArith s!"ok mul {w} {wa} {wb}"
      (w := w) (.mul (.zext 0 wa hab.1) (.zext 1 wb hab.2))
  else
    throw "operand live width exceeds result width"

/--
Verified compression of a `w`-bit addition of the operands whose live widths
are given by `widths` (one entry per operand; bits above an operand's live
width are constant 0).
-/
def compressAdd (w : Nat) (widths : List Nat) : Except String (Array String) := do
  if w == 0 then
    throw "width must be positive"
  if widths.length < 2 then
    throw "addition needs at least 2 operands"
  let widths := widths.map (min · w)
  -- `min · w` guarantees the bound, but it has to be re-derived for each operand
  -- so `zext` can carry it.
  let operands : List (Comb.ArithCircuit w) :=
    widths.zipIdx.map fun (b, i) =>
      if hb : b ≤ w then .zext i b hb else .var i
  compressArith
    (s!"ok add {w} {widths.length} " ++ " ".intercalate (widths.map toString))
    (w := w) (.add operands)

/--
Parse a leaf token `<index>.<live>`: operand `index` (of `numOperands`) whose
low `live` bits are its real bits and whose bits above them are constant `0`,
so that the extension bits never enter the bit heap.
-/
private def parseLeaf (w numOperands : Nat) (s : String) :
    Except String (Comb.ArithCircuit w) :=
  match s.splitOn "." with
  | [iStr, liveStr] =>
    match iStr.toNat?, liveStr.toNat? with
    | some i, some live =>
      if i < numOperands then
        let b := min live w
        have hb : b ≤ w := Nat.min_le_right _ _
        .ok (.zext i b hb)
      else
        .error s!"leaf '{s}' addresses operand {i} of {numOperands}"
    | _, _ => .error s!"malformed leaf token '{s}'"
  | _ => .error s!"malformed leaf token '{s}'"

mutual

/-- Parse one prefix-notation expression, returning it and the leftover tokens. -/
private partial def parseExpr (w numOperands : Nat) :
    List String → Except String (Comb.ArithCircuit w × List String)
  | [] => .error "unexpected end of expression"
  | tok :: rest =>
    if tok == "mul" then do
      let (l, rest₁) ← parseExpr w numOperands rest
      let (r, rest₂) ← parseExpr w numOperands rest₁
      return (.mul l r, rest₂)
    else if tok.startsWith "add" then
      match (tok.drop 3).toNat? with
      | none => .error s!"malformed token '{tok}'"
      | some n =>
        if n < 2 then .error s!"'{tok}': addition needs at least 2 operands"
        else do
          let (args, rest') ← parseArgs w numOperands n rest
          return (.add args, rest')
    else do
      let leaf ← parseLeaf w numOperands tok
      return (leaf, rest)

/-- Parse `n` consecutive prefix-notation expressions. -/
private partial def parseArgs (w numOperands : Nat) :
    Nat → List String → Except String (List (Comb.ArithCircuit w) × List String)
  | 0, toks => .ok ([], toks)
  | n + 1, toks => do
    let (arg, toks₁) ← parseExpr w numOperands toks
    let (args, toks₂) ← parseArgs w numOperands n toks₁
    return (arg :: args, toks₂)

end

/--
Verified compression of an arbitrary sum-of-products expression over
`numOperands` `w`-bit operands, written in prefix notation:

* `mul` — a binary multiply, followed by its two operand expressions;
* `add<n>` — an `n`-ary addition (`n ≥ 2`), followed by its `n` operand
  expressions;
* `<index>.<live>` — a leaf: operand `index` whose low `live` bits are its
  real bits, zero-extended to `w` bits.

The whole expression becomes a *single* bit heap (`ArithCircuit.toBitHeap`
merges the partial products of every multiply with the bits of every addend)
and so a single compressor tree. For example
`expr 16 3 add2 mul 0.8 1.8 2.8` is the fused multiply-add `a * b + c` over
three operands with 8 live bits each — which `mul` followed by a separate
`add` cannot express.

`compressMul w a b` is `expr w 2 mul 0.a 1.b`, and `compressAdd w [w₀ … wₙ]`
is `expr w (n+1) add<n+1> 0.w₀ … n.wₙ`.
-/
def compressExpr (w numOperands : Nat) (tokens : List String) :
    Except String (Array String) := do
  if w == 0 then
    throw "width must be positive"
  let (c, rest) ← parseExpr w numOperands tokens
  unless rest.isEmpty do
    throw ("trailing tokens after expression: " ++ " ".intercalate rest)
  let header := s!"ok expr {w} {numOperands} " ++ " ".intercalate tokens
  compressArith header (w := w) c

end Netlist

end BitHeap
