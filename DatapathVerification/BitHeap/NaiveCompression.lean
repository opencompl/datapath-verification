import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain

open BitHeap

open Chain

namespace NaiveCompression

/- Takes the bitheap and compresses it starting from the first column as much as it can in one go.
Another difference with the Wallace tree is that this naive approach consumes carries in the same round. -/

-- if height >= 3, apply FA. if height = 2, apply HA.
def reduceColumnStep (col : Nat) (h : BitHeap) : Option (BitHeap × Adder) :=
    match (h.get col).toList with
  | a :: b :: c :: _ =>
      let FA := Adder.fullAdder col a b c
      some (Chain.applyAdder FA h, FA)
  | a :: b :: [] =>
      let HA := Adder.halfAdder col a b
      some (Chain.applyAdder HA h, HA)
  | _ => none

-- termination is guaranteed since each step reduces the height of the column.
partial def reduceColumn (col : Nat) (h : BitHeap) : BitHeap × List Adder :=
    match reduceColumnStep col h with
    | none => (h, [])
    | some (h', adder) =>
        let (h'', adders) := reduceColumn col h'
        (h'', adder :: adders)

def naiveCompression (h : BitHeap) : BitHeap × List Adder :=
    let maxIter := h.columns.size + 2 -- TODO: I am aware this is not the correct maximum bound, but it should suffice for now for our examples.
    (List.range maxIter).foldl (fun (heap, adders) col =>
        let (newHeap, newAdders) := reduceColumn col heap
        (newHeap, adders ++ newAdders)) (h, [])
