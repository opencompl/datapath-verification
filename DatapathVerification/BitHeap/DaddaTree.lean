import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.Column
import Std.Data.HashSet

open BitHeap

open Chain

namespace DaddaTree

/--
Dadda Sequence recursively computed by mₗ = ⌊1.5mₗ₋₁⌋ with m₀ = 2.
Floor division is ensured from Nat division.
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
partial def DaddaRoundColumn (col : Nat) (h : BitHeap) (acc : BitHeap) (daddaLevel : Nat)
    : BitHeap × BitHeap × List Adder :=
  let DaddaHeightPrev := DaddaSequence (daddaLevel - 1) -- mₗ₋₁ is the maximum height allowed in the column after this round of compression.
  if (acc.get col).height - DaddaHeightPrev = 1 then
    -- If the column height is exactly one more than the previous Dadda level, apply a Half Adder to compress it.
    match (h.get col).toList with
    | x :: y :: _ =>
        let HA := Adder.halfAdder col x y
        let newAcc := Chain.applyAdder HA acc -- applies a Half Adder, removing compressed bits and adding sum and carry bits to acc.
        let newOriginal := h.removeBit col x |>.removeBit col y -- removes the compressed bits from the original heap.
        let (finalOriginal, finalAcc, adders) := DaddaRoundColumn col newOriginal newAcc daddaLevel
        (finalOriginal, finalAcc, HA :: adders)
    | _ => (h, acc, [])
  else if (acc.get col).height - DaddaHeightPrev ≥ 2 then
    -- If the column height is more than one above the previous Dadda level, apply a Full Adder to compress it.
    match (h.get col).toList with
    | x :: y :: z :: _ =>
      let FA := Adder.fullAdder col x y z
      let newAcc := Chain.applyAdder FA acc -- applies a Full Adder, removing compressed bits and adding sum and carry bits to acc.
      let newOriginal := h.removeBit col x |>.removeBit col y |>.removeBit col z -- removes the compressed bits from the original heap.
      let (finalOriginal, finalAcc, adders) := DaddaRoundColumn col newOriginal newAcc daddaLevel
      (finalOriginal, finalAcc, FA :: adders)
    | _ => (h, acc, [])
  else (h, acc, []) -- If the column height is less than or equal to the previous Dadda level, do nothing.

/--
One full round of Dadda tree across all columns of the bit heap.

Loops over every column in order, invoking DaddaRoundColumn to compress each
one and folding the resulting adders into a running list.
-/
partial def DaddaRound (h : BitHeap) (daddaLevel : Nat) : BitHeap × List Adder :=
  let (_, acc, adders) :=
  (List.range h.columns.size).foldl
    (fun (original, acc, adders) col =>
      let (original', acc', newAdders) := DaddaRoundColumn col original acc daddaLevel
      -- Return modified original heap (with removal of compressed bits, but without adding carries to the columns),
      -- accumulated BitHeap, and append newAdders to the adders list.
      (original', acc', adders ++ newAdders))
      (h, h, []) -- Invoke the loop with accumulator initialized as h, and empty list of Adders.
  (acc, adders) -- Return the resulting BitHeap and list of Adders

/--
Top-level Dadda Tree function.

Repeatedly applies DaddaRound until every column has at most 2 bits.
-/
partial def DaddaTree (h : BitHeap) : BitHeap × List Adder :=
  let daddaLevel := findDaddaLevel h.maxHeight
  let rec loop (h : BitHeap) (adders : List Adder) (daddaLevel : Nat) : BitHeap × List Adder :=
    if h.maxHeight ≤ 2 then (h, adders)
    else
      let (h', newAdders) := DaddaRound h daddaLevel
      loop h' (adders ++ newAdders) (daddaLevel - 1) -- Decrement the Dadda level for the next round.
  loop h [] daddaLevel

end DaddaTree
