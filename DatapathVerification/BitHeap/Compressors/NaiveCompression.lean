import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain

open BitHeap

open Chain

namespace NaiveCompression

/- Takes the bitheap and compresses it starting from the first column as much as it can in one go.
Another difference with the Wallace tree is that this naive approach consumes carries in the same round. -/

-- if height >= 4, apply FA. if height = 3, apply HA.
def reduceColumnStep (col : Nat) (h : BitHeap w) : Option (BitHeap w × Adder) :=
    match (h.get col).toList with
  | a :: b :: c :: _ :: _ =>
      let FA := Adder.fullAdder col a b c
      some (Chain.applyAdder FA h, FA)
  | a :: b :: _ :: [] =>
      let HA := Adder.halfAdder col a b
      some (Chain.applyAdder HA h, HA)
  | _ => none

-- termination is guaranteed since each step reduces the height of the column.
partial def reduceColumn (col : Nat) (h : BitHeap w) : BitHeap w × List Adder :=
    match reduceColumnStep col h with
    | none => (h, [])
    | some (h', adder) =>
        let (h'', adders) := reduceColumn col h'
        (h'', adder :: adders)

def naiveCompression (h : BitHeap w) : BitHeap w × List Adder :=
    (List.range h.columns.size).foldl (fun (heap, adders) col =>
        let (newHeap, newAdders) := reduceColumn col heap
        (newHeap, adders ++ newAdders)) (h, [])
