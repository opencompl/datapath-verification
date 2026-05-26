import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.WallaceTree

namespace BitHeap

open Chain

namespace PartialProductGenerator

/-- Build a bit heap of partial products for the given bit-width. -/
def bitHeapOfPartialProducts (width : Nat) : BitHeap := Id.run do
  let mut h := BitHeap.empty
  let mut index := 0
  for i in [0:(2 * width - 1)] do
    let height := min (i + 1) (2 * width - 1 - i)
    for _ in [0:height] do
      h := h.addBit i (Circuit.bit index)
      index := index + 1
  return h

/--
info: [1, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1]
-/
#guard_msgs in
#eval (List.range 15).map (fun c => ((bitHeapOfPartialProducts 8).get c).height)

end PartialProductGenerator
end BitHeap
