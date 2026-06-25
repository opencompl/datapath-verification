import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.Column
import DatapathVerification.BitHeap.CompressionHelpers
import Std.Data.HashSet

open BitHeap

open Chain

namespace WallaceTree

/--
One pass of the Wallace tree over a single column.

Given the original bit heap `h` and an accumulator `acc` (which holds the bits
already produced by carries from previous compressions), returns the reduced original heap,
the updated accumulator, and the list of adders used to compress the column.

See comments of WallaceStage to understand the separation of `h` and `acc`.

If acc.get col has ≥ 4 bits and the original column has ≥ 3 bits, a full adder
  is inserted (consuming three bits from h, producing a sum bit in acc[col]
  and a carry bit in acc[col+1]).
If acc.get col has ≥ 4 bits but the original column has only 2 bits left,
  a half adder is used instead. This is because we cannot consume newly added bits, so we only consume the original bits in the column.
If acc.get col has exactly 3 bits, a single half adder is applied and we stop.
-/
partial def WallaceStageColumn (col : Nat) (h : BitHeap w) (acc : BitHeap w)
    : BitHeap w × BitHeap w × List Adder :=
  match (h.get col).toList with
    | x :: y :: z :: _ =>
        let ⟨newOriginal, newAcc, FA⟩ := Compression.applyFullAdder col x y z h acc
        let (finalOriginal, finalAcc, adders) := WallaceStageColumn col newOriginal newAcc
        (finalOriginal, finalAcc, FA :: adders)
    | x :: y :: [] =>
        let ⟨newOriginal, newAcc, HA⟩ := Compression.applyHalfAdder col x y h acc
        let (finalOriginal, finalAcc, adders) := WallaceStageColumn col newOriginal newAcc
        (finalOriginal, finalAcc, HA :: adders)
    | _ => (h, acc, [])

-- TODO: This is the same function as WallaceStageColumn, with incomplete termination proof.
def WallaceStageColumnNotPartial (col : Nat) (h : BitHeap w) (acc : BitHeap w)
    : BitHeap w × BitHeap w × List Adder :=
  match (h.get col).toList with
    | x :: y :: z :: _ =>
        let ⟨newOriginal, newAcc, FA⟩ := Compression.applyFullAdder col x y z h acc
        let (finalOriginal, finalAcc, adders) := WallaceStageColumn col newOriginal newAcc
        (finalOriginal, finalAcc, FA :: adders)
    | x :: y :: [] =>
        let ⟨newOriginal, newAcc, HA⟩ := Compression.applyHalfAdder col x y h acc
        let (finalOriginal, finalAcc, adders) := WallaceStageColumn col newOriginal newAcc
        (finalOriginal, finalAcc, HA :: adders)
    | _ => (h, acc, [])
  termination_by (h.get col).height
  decreasing_by
  · apply triple_removeBit_decreases col z y x h
    · have hz : z ∈ (h.get col).toList := by simp_all
      exact Std.HashSet.mem_toList.mp hz
    · have hy : y ∈ (h.get col).toList := by simp_all
      exact Std.HashSet.mem_toList.mp hy
    · have hx : x ∈ (h.get col).toList := by simp_all
      exact Std.HashSet.mem_toList.mp hx
    · sorry -- TODO: prove that x, y, z are all distinct. we know they are distinct since they are elements of HashSet.
    · sorry
    · sorry
  · apply double_removeBit_decreases col y x h
    · have hy : y ∈ (h.get col).toList := by simp_all
      exact Std.HashSet.mem_toList.mp hy
    · have hx : x ∈ (h.get col).toList := by simp_all
      exact Std.HashSet.mem_toList.mp hx
    · sorry -- TODO: prove that x and y are distinct.


/--
One full stage of Wallace tree across all columns of the bit heap.

Loops over every column in order, invoking WallaceStageColumn to compress each
one and folding the resulting adders into a running list.

The accumulator (acc : BitHeap) starts as a copy of the original BitHeap h.
Carries generated during compression are added only to acc, while the
compressed bits are removed from both acc and h (original heap).
This separation lets us track which bits are carries, since
generated carry bits contribute to the height calculation but are not themselves compressed in the same stage.
-/
def WallaceStage (h : BitHeap w) : BitHeap w × List Adder :=
  let (_, acc, adders) :=
  (List.range h.columns.size).foldl
    (fun (original, acc, adders) col =>
      let (original', acc', newAdders) := WallaceStageColumn col original acc
      -- Return modified original heap (with removal of compressed bits, but without adding carries to the columns),
      -- accumulated BitHeap, and append newAdders to the adders list.
      (original', acc', adders ++ newAdders))
      (h, h, []) -- Invoke the loop with accumulator initialized as h, and empty list of Adders.
  (acc, adders) -- Return the resulting BitHeap and list of Adders

/--
Top-level Wallace Tree function.

Repeatedly applies WallaceStage until every column has at most 2 bits.
-/
partial def WallaceTree (h : BitHeap w) : BitHeap w × List Adder :=
    if h.maxHeight ≤ 2 then
    (h, [])
  else
    let (h', adders) := WallaceStage h
    let (h'', moreAdders) := WallaceTree h'
    (h'', adders ++ moreAdders)
