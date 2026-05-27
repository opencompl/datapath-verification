import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.Column
import Std.Data.HashSet

open BitHeap

open Chain

namespace WallaceTree

/--
One pass of the Wallace tree over a single column.

Given the original bit heap `h` and an accumulator `acc` (which holds the bits
already produced by carries from previous compressions), returns the reduced original heap,
the updated accumulator, and the list of adders used to compress the column.

See comments of WallaceRound to understand the separation of `h` and `acc`.

If acc.get col has ≥ 4 bits and the original column has ≥ 3 bits, a full adder
  is inserted (consuming three bits from h, producing a sum bit in acc[col]
  and a carry bit in acc[col+1]).
If acc.get col has ≥ 4 bits but the original column has only 2 bits left,
  a half adder is used instead. This is because we cannot consume newly added bits, so we only consume the original bits in the column.
If acc.get col has exactly 3 bits, a single half adder is applied and we stop.
-/
partial def WallaceRoundColumn (col : Nat) (h : BitHeap) (acc : BitHeap)
    : BitHeap × BitHeap × List Adder :=
  let accHeight := (acc.get col).height
  if accHeight ≥ 4 then
    match (h.get col).toList with
    | x :: y :: z :: _ =>
        let FA := Adder.fullAdder col x y z
        let newAcc := Chain.applyAdder FA acc -- applies a Full Adder, removing compressed bits and adding sum and carry bits to acc.
        let newOriginal := h.removeBit col x |>.removeBit col y |>.removeBit col z -- removes the compressed bits from the original heap.
        let (finalOriginal, finalAcc, adders) := WallaceRoundColumn col newOriginal newAcc
        (finalOriginal, finalAcc, FA :: adders)
    | x :: y :: _ =>
        let HA := Adder.halfAdder col x y
        let newAcc := Chain.applyAdder HA acc -- applies a Half Adder, removing compressed bits and adding sum and carry bits to acc.
        let newOriginal := h.removeBit col x |>.removeBit col y -- removes the compressed bits from the original heap.
        let (finalOriginal, finalAcc, adders) := WallaceRoundColumn col newOriginal newAcc
        (finalOriginal, finalAcc, HA :: adders)
    | _ => (h, acc, [])
  else if accHeight == 3 then
    match (h.get col).toList with
    | x :: y :: _ =>
        let HA := Adder.halfAdder col x y
        let newAcc := Chain.applyAdder HA acc -- applies a Half Adder, removing compressed bits and adding sum and carry bits to acc.
        let newOriginal := h.removeBit col x |>.removeBit col y -- removes the compressed bits from the original heap.
        (newOriginal, newAcc, [HA])
    | _ => (h, acc, [])
  else
    (h, acc, [])

-- TODO: This is the same function as WallaceRoundColumn, with incomplete termination proof.
def WallaceRoundColumnNotPartial (col : Nat) (h : BitHeap) (acc : BitHeap)
    : BitHeap × BitHeap × List Adder :=
  let accHeight := (acc.get col).height
  if accHeight ≥ 4 then
    match _ : (h.get col).toList with
    | x :: y :: z :: _ =>
        let FA := Adder.fullAdder col x y z
        let newAcc := Chain.applyAdder FA acc
        let newOriginal := h.removeBit col x |>.removeBit col y |>.removeBit col z
        let (finalOriginal, finalAcc, adders) := WallaceRoundColumnNotPartial col newOriginal newAcc
        (finalOriginal, finalAcc, FA :: adders)
    | x :: y :: _ =>
        let HA := Adder.halfAdder col x y
        let newAcc := Chain.applyAdder HA acc
        let newOriginal := h.removeBit col x |>.removeBit col y
        let (finalOriginal, finalAcc, adders) := WallaceRoundColumnNotPartial col newOriginal newAcc
        (finalOriginal, finalAcc, HA :: adders)
    | _ => (h, acc, [])
  else if accHeight == 3 then
    match (h.get col).toList with
    | x :: y :: _ =>
        let HA := Adder.halfAdder col x y
        let newAcc := Chain.applyAdder HA acc
        let newOriginal := h.removeBit col x |>.removeBit col y
        (newOriginal, newAcc, [HA])
    | _ => (h, acc, [])
  else
    (h, acc, [])
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
One full round of Wallace tree across all columns of the bit heap.

Loops over every column in order, invoking WallaceRoundColumn to compress each
one and folding the resulting adders into a running list.

The accumulator (acc : BitHeap) starts as a copy of the original BitHeap h.
Carries generated during compression are added only to acc, while the
compressed bits are removed from both acc and h (original heap).
This separation lets us track which bits are carries, since
generated carry bits contribute to the height calculation but are not themselves compressed in the same round.
-/
def WallaceRound (h : BitHeap) : BitHeap × List Adder :=
  let (_, acc, adders) :=
  (List.range h.columns.size).foldl
    (fun (original, acc, adders) col =>
      let (original', acc', newAdders) := WallaceRoundColumn col original acc
      -- Return modified original heap (with removal of compressed bits, but without adding carries to the columns),
      -- accumulated BitHeap, and append newAdders to the adders list.
      (original', acc', adders ++ newAdders))
      (h, h, []) -- Invoke the loop with accumulator initialized as h, and empty list of Adders.
  (acc, adders) -- Return the resulting BitHeap and list of Adders

/--
Top-level Wallace Tree function.

Repeatedly applies WallaceRound until every column has at most 2 bits.
-/
partial def WallaceTree (h : BitHeap) : BitHeap × List Adder :=
    if h.maxHeight ≤ 2 then
    (h, [])
  else
    let (h', adders) := WallaceRound h
    let (h'', moreAdders) := WallaceTree h'
    (h'', adders ++ moreAdders)
