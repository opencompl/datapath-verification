import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain

open BitHeap

open Chain

namespace WallaceTree

-- if height >= 4, apply FA. if height = 3, apply HA.
def reduceColumnStep (col : Nat) (h : BitHeap) : Option (BitHeap × Adder) :=
    match (h.get col).toList with
  | a :: b :: c :: _ :: [] =>
      let FA := Adder.fullAdder col a b c
      some (Chain.applyAdder FA h, FA)
  | a :: b :: _ :: [] =>
      let HA := Adder.halfAdder col a b
      some (Chain.applyAdder HA h, HA)
  | _ => none

partial def WallaceRoundColumn (col : Nat) (h : BitHeap) (acc : BitHeap)
    : BitHeap × BitHeap × List Adder :=
  let accHeight := (acc.get col).height
  if accHeight ≥ 4 then
    match (h.get col).toList with
    | x :: y :: z :: _ =>
        let FA := Adder.fullAdder col x y z
        let newAcc := Chain.applyAdder FA acc
        let newOriginal := h.removeBit col x |>.removeBit col y |>.removeBit col z
        let (finalOriginal, finalAcc, adders) := WallaceRoundColumn col newOriginal newAcc
        (finalOriginal, finalAcc, FA :: adders)
    | x :: y :: _ =>
        let HA := Adder.halfAdder col x y
        let newAcc := Chain.applyAdder HA acc
        let newOriginal := h.removeBit col x |>.removeBit col y
        let (finalOriginal, finalAcc, adders) := WallaceRoundColumn col newOriginal newAcc
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

partial def WallaceRound (h : BitHeap) : BitHeap × List Adder :=
    let (_, acc, adders) :=
    (List.range h.columns.size).foldl
      (fun (original, acc, adders) col =>
        let (original', acc', newAdders) := WallaceRoundColumn col original acc
        (original', acc', adders ++ newAdders))
      (h, h, [])
  (acc, adders)

partial def WallaceTree (h : BitHeap) : BitHeap × List Adder :=
    if h.maxHeight ≤ 2 then
    (h, [])
  else
    let (h', adders) := WallaceRound h
    let (h'', moreAdders) := WallaceTree h'
    (h'', adders ++ moreAdders)
