import DatapathVerification.BitHeap.Netlist

/-!
Examples for the netlist emission flow (`Netlist.compressMul`), which is what
the `datapath-cli` executable exposes to the CIRCT `comb-verified-datapath`
pass.

For a `w`-bit multiply the flow is:
1. Build the partial-product bit heap of `(var 0) * (var 1)`
   (`ArithCircuit.toBitHeap`). Operand bits are numbered `b0..b(w-1)` for the
   first operand and `bw..b(2w-1)` for the second.
2. Run the Dadda tree compressor to obtain an adder chain.
3. Replay the chain with `Chain.applyChainSafe` — the verified path: by
   `compressed_toBitHeap_correct`, the resulting two-row heap evaluates
   (mod 2^w) to the product of the operands.
4. Serialize the two-row heap as a hash-consed gate netlist.
-/

namespace BitHeap

namespace NetlistExamples

open Comb

def mul3 : ArithCircuit 3 := .mul (.var 0 3) (.var 1 3)

-- Step 1: the raw partial-product heap. Column k holds all (a_i AND b_j)
-- with i + j = k; columns ≥ 3 are truncated away (we compute mod 2^3).
/--
info: {0 ↦ [(b0 ∧ b3)], 1 ↦ [(b0 ∧ b4), (b1 ∧ b3)], 2 ↦ [(b2 ∧ b3), (b0 ∧ b5), (b1 ∧ b4)]}
-/
#guard_msgs in
#eval mul3.toBitHeap

-- Step 2: the Dadda tree only needs one half adder to bring column 2 from
-- height 3 down to 2 (the carry falls off the end of the heap).
/--
info: [HA(2: (b2 ∧ b3), (b0 ∧ b5))]
-/
#guard_msgs in
#eval (DaddaTree.DaddaTree mul3.toBitHeap).2

-- Step 3: the checked replay of that chain succeeds and yields a heap of
-- height ≤ 2 — this is the heap the netlist is generated from.
/--
info: (some {0 ↦ [(b0 ∧ b3)], 1 ↦ [(b0 ∧ b4), (b1 ∧ b3)], 2 ↦ [((b2 ∧ b3) ⊕ (b0 ∧ b5)), (b1 ∧ b4)]})
-/
#guard_msgs in
#eval Chain.applyChainSafe (DaddaTree.DaddaTree mul3.toBitHeap).2 mul3.toBitHeap

-- Step 4: the serialized netlist, exactly as `datapath-cli mul 3` prints it.
-- The header echoes the operands' live widths (here full-width: 3 and 3).
/--
info: ok mul 3 3 3
gate g0 and b0 b3
gate g1 and b0 b4
gate g2 and b1 b3
gate g3 and b2 b3
gate g4 and b0 b5
gate g5 xor g3 g4
gate g6 and b1 b4
row0 g0 g1 g5
row1 - g2 g6
-/
#guard_msgs in
#eval match Netlist.compressMul 3 3 3 with
  | .ok lines => IO.println (String.intercalate "\n" lines.toList)
  | .error e => IO.println s!"error: {e}"

-- A 1-bit multiply degenerates to a single AND gate.
/--
info: ok mul 1 1 1
gate g0 and b0 b1
row0 g0
row1 -
-/
#guard_msgs in
#eval match Netlist.compressMul 1 1 1 with
  | .ok lines => IO.println (String.intercalate "\n" lines.toList)
  | .error e => IO.println s!"error: {e}"

-- Zero-extension awareness: an i6 multiply whose operands are zero-extended
-- from 3 bits (CIRCT's full-product idiom) has only 3×3 = 9 partial products
-- instead of 21 — the constant-0 upper bits never enter the heap, so the
-- whole netlist is 13 gates instead of 55.
/--
info: ok mul 6 3 3
gate g0 and b0 b6
gate g1 and b0 b7
gate g2 and b1 b6
gate g3 and b2 b6
gate g4 and b1 b7
gate g5 xor g3 g4
gate g6 and b0 b8
gate g7 and b1 b8
gate g8 and b2 b7
gate g9 xor g7 g8
gate g10 and g3 g4
gate g11 and b2 b8
gate g12 and g7 g8
row0 g0 g1 g5 g9 g11 -
row1 - g2 g6 g10 g12 -
-/
#guard_msgs in
#eval match Netlist.compressMul 6 3 3 with
  | .ok lines => IO.println (String.intercalate "\n" lines.toList)
  | .error e => IO.println s!"error: {e}"

-- Variadic addition: a 3-operand, 3-bit addition. Column 0 holds bit 0 of
-- each operand (b0, b3, b6), and so on; the Dadda tree compresses each
-- height-3 column with one half or full adder into the two final rows.
/--
info: ok add 3 3 3 3 3
gate g0 xor b3 b6
gate g1 xor b1 b4
gate g2 xor g1 b7
gate g3 and b3 b6
gate g4 xor b2 b5
gate g5 xor g4 b8
gate g6 and b1 b4
gate g7 and b1 b7
gate g8 or g6 g7
gate g9 and b4 b7
gate g10 or g8 g9
row0 g0 g2 g5
row1 b0 g3 g10
-/
#guard_msgs in
#eval match Netlist.compressAdd 3 [3, 3, 3] with
  | .ok lines => IO.println (String.intercalate "\n" lines.toList)
  | .error e => IO.println s!"error: {e}"

-- For an 8-bit multiply the Dadda tree spends 15 full adders and 6 half
-- adders (fewer than the full 16-bit product would need, since the heap is
-- truncated to 8 columns); the result is still exactly two rows of 8 columns.
/--
info: "FAs: 15, HAs: 6"
-/
#guard_msgs in
#eval Chain.printSummary
  (DaddaTree.DaddaTree (ArithCircuit.mul (w := 8) (.var 0 8) (.var 1 8)).toBitHeap).2

end NetlistExamples

end BitHeap
