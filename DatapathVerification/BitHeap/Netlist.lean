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
The operand model used by both entry points: an operand whose low `live` bits
are the real ("live") bits of the operand, with the bits above them either
constant `0` (`signed = false`, zero extension) or copies of bit `live - 1`
(`signed = true`, sign extension).
-/
def operandCircuit (w i live : Nat) (signed : Bool) : Comb.ArithCircuit w :=
  let b := min live w
  have hb : b ≤ w := Nat.min_le_right _ _
  if hpos : 0 < b then
    if signed then .sext i b hb hpos else .zext i b hb
  else
    .zext i b hb

/-- Render an operand spec as its protocol token: `<live>` or `<live>s`. -/
def specToken (live : Nat) (signed : Bool) : String :=
  toString live ++ (if signed then "s" else "")

/--
Verified compression of a `w`-bit multiply of two operands with live widths
`wa` and `wb`: operand bits at positions ≥ the live width are constant 0 when
the operand is zero-extended (`sa`/`sb` false) and copies of the operand's
sign bit when it is sign-extended (`sa`/`sb` true).
-/
def compressMul (w wa wb : Nat) (sa sb : Bool := false) : Except String (Array String) := do
  if w == 0 then
    throw "width must be positive"
  let wa := min wa w
  let wb := min wb w
  compressArith
    s!"ok mul {w} {specToken wa sa} {specToken wb sb}"
    (w := w) (.mul (operandCircuit w 0 wa sa) (operandCircuit w 1 wb sb))

/--
Verified compression of a `w`-bit addition of the operands described by
`specs` (one `(live width, signed)` pair per operand; see `operandCircuit`).
-/
def compressAdd (w : Nat) (specs : List (Nat × Bool)) : Except String (Array String) := do
  if w == 0 then
    throw "width must be positive"
  if specs.length < 2 then
    throw "addition needs at least 2 operands"
  let specs := specs.map fun (live, signed) => (min live w, signed)
  let operands : List (Comb.ArithCircuit w) :=
    specs.zipIdx.map fun ((live, signed), i) => operandCircuit w i live signed
  compressArith
    (s!"ok add {w} {specs.length} "
      ++ " ".intercalate (specs.map fun (live, signed) => specToken live signed))
    (w := w) (.add operands)

end Netlist

end BitHeap
