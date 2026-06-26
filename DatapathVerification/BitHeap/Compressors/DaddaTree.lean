/-
Dadda's algorithm:

Input: A bit heap with maximum column height ℎ.
Output: A two-row bit heap.

(1) Compute the smallest 𝐿 such that 𝑚ₗ ≥ ℎ, where the Dadda sequence is
given by 𝑚0 = 2 and 𝑚ₗ = ⌊3/2 mₗ₋₁⌋.

(2) Starting at level 𝑙 = 𝐿, scan all columns from least-significant bit (LSB) to most-
significant bit (MSB). For each column whose height exceeds mₗ₋₁, introduce the
fewest number of FAs and at most one HA to bring the height down to mₗ₋₁. Carry
outputs are added to the next column, but should be left uncompressed until the
following level.

(3) Decrement 𝑙 and repeat until every column has height at most 2.
-/

import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.Column
import DatapathVerification.BitHeap.Compressors.CompressionHelpers
import Std.Data.HashSet

open BitHeap

open Chain

namespace DaddaTree

/--
Dadda Sequence recursively computed by mₗ = ⌊1.5mₗ₋₁⌋ with m₀ = 2.
Floor division is ensured by Nat division.
-/
def DaddaSequence : Nat → Nat
  | 0 => 2
  | l + 1 => (3 * DaddaSequence l) / 2

theorem DaddaSequence_increases (l : Nat) : DaddaSequence l < DaddaSequence (l + 1) := by
  simp [DaddaSequence]
  have : 2 ≤ DaddaSequence l := by -- we need 2 ≤ mₗ to prove that 3mₗ/2 > mₗ, since we work with Nat division.
    induction l with
    | zero => simp [DaddaSequence]
    | succ l ih =>
        simp [DaddaSequence]
        omega
  omega

/--
Compute the smallest L s.t. mₗ ≥ height,
where mₗ is the maximum height that can be compressed by L level of full-adders, computed by DaddaSequence.
-/
def findDaddaLevel (height : Nat) : Nat :=
  let rec findLevel (l : Nat) : Nat :=
    if DaddaSequence l >= height then l else findLevel (l + 1)
  termination_by height - DaddaSequence l -- we need a termination proof since l increases.
  decreasing_by
    have := DaddaSequence_increases l
    omega
  findLevel 0

/--
One pass of the Dadda tree over a single column.

Given the original bit heap `h` and an accumulator `acc` (which holds the bits
already produced by carries from previous compressions), returns the reduced original heap,
the updated accumulator, and the list of adders used to compress the column.

For each column whose height exceeds mₗ₋₁, introduces the
fewest number of FAs and at most one HA to bring the height down to mₗ₋₁.
-/
partial def DaddaStageColumn (col : Nat) (h : BitHeap w) (acc : BitHeap w) (daddaLevel : Nat)
    : BitHeap w × BitHeap w × List Adder :=
  let DaddaHeightPrev := DaddaSequence (daddaLevel - 1) -- mₗ₋₁ is the maximum height allowed in the column after this stage of compression.
  if (acc.get col).height - DaddaHeightPrev ≥ 2 then
    -- If the column height is more than one above the previous Dadda level, apply a Full Adder to compress it.
    match (h.get col).toList with
    | x :: y :: z :: _ =>
      let ⟨newOriginal, newAcc, FA⟩ := Compression.applyFullAdder col x y z h acc
      let (finalOriginal, finalAcc, adders) := DaddaStageColumn col newOriginal newAcc daddaLevel
      (finalOriginal, finalAcc, FA :: adders)
    | _ => (h, acc, [])
    else if (acc.get col).height - DaddaHeightPrev = 1 then
    -- If the column height is exactly one more than the previous Dadda level, apply a Half Adder to compress it.
    match (h.get col).toList with
    | x :: y :: _ =>
        let ⟨newOriginal, newAcc, HA⟩ := Compression.applyHalfAdder col x y h acc
        let (finalOriginal, finalAcc, adders) := DaddaStageColumn col newOriginal newAcc daddaLevel
        (finalOriginal, finalAcc, HA :: adders)
    | _ => (h, acc, [])
  else (h, acc, []) -- If the column height is less than or equal to the previous Dadda level, do nothing.

/--
One full stage of Dadda tree across all columns of the bit heap.

Loops over every column in order, invoking DaddaStageColumn to compress each
one and folding the resulting adders into a running list.
-/
partial def DaddaStage (h : BitHeap w) (daddaLevel : Nat) : BitHeap w × List Adder :=
  let (_, acc, adders) :=
  (List.range h.columns.size).foldl
    (fun (original, acc, adders) col =>
      let (original', acc', newAdders) := DaddaStageColumn col original acc daddaLevel
      -- Return modified original heap (with removal of compressed bits, but without adding carries to the columns),
      -- accumulated BitHeap, and append newAdders to the adders list.
      (original', acc', adders ++ newAdders))
      (h, h, []) -- Invoke the loop with accumulator initialized as h, and empty list of Adders.
  (acc, adders) -- Return the resulting BitHeap and list of Adders

/--
Top-level Dadda Tree function.

Repeatedly applies DaddaStage until every column has at most 2 bits.
-/
partial def DaddaTree (h : BitHeap w) : BitHeap w × List Adder :=
  let daddaLevel := findDaddaLevel h.maxHeight
  let rec loop (h : BitHeap w) (adders : List Adder) (daddaLevel : Nat) : BitHeap w × List Adder :=
    if h.maxHeight ≤ 2 then (h, adders)
    else
      let (h', newAdders) := DaddaStage h daddaLevel
      loop h' (adders ++ newAdders) (daddaLevel - 1) -- Decrement the Dadda level for the next stage.
  loop h [] daddaLevel

end DaddaTree
