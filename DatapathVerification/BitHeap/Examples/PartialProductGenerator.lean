import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.WallaceTree

namespace BitHeap

open Chain

namespace PartialProductGenerator

/-- Build a bit heap of partial products for the given bit-width. -/
def bitHeapOfPartialProducts (width : Nat) : BitHeap := Id.run do
  let mut h := BitHeap.empty
  for i in [0:width] do
    for j in [i:width+i] do
      h := h.addBit j (Circuit.bit (i * (width - 1) + j))
  return h

/--
info: [1, 2, 3, 4, 5, 6, 7, 8, 7, 6, 5, 4, 3, 2, 1]
-/
#guard_msgs in
#eval (List.range 15).map (fun c => ((bitHeapOfPartialProducts 8).get c).height)

/--
info: {0 ↦ [b0], 1 ↦ [b1, b4], 2 ↦ [b2, b5, b8], 3 ↦ [b9, b6, b3, b12], 4 ↦ [b10, b13, b7], 5 ↦ [b11, b14], 6 ↦ [b15]}
-/
#guard_msgs in
#eval bitHeapOfPartialProducts 4

end PartialProductGenerator
end BitHeap
