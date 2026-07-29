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
  compressArith s!"ok mul {w} {min wa w} {min wb w}"
    (w := w) (.mul (.var 0 wa) (.var 1 wb))

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
  compressArith
    (s!"ok add {w} {widths.length} " ++ " ".intercalate (widths.map toString))
    (w := w) (.add (widths.zipIdx.map (fun (b, i) => .var i b)))

end Netlist

end BitHeap
