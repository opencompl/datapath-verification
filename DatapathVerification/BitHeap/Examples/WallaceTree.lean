import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.WallaceTree
import DatapathVerification.BitHeap.Examples.PartialProductGenerator

namespace BitHeap

open Chain
open PartialProductGenerator

namespace WallaceTreeExamples

abbrev BitEnv := Nat → Bool

def pp4 : BitHeap := bitHeapOfPartialProducts 4

/--
info: [1, 2, 3, 4, 3, 2, 1]
-/
#guard_msgs in
#eval (List.range 7).map (fun c => (pp4.get c).height)

------------- First Wallace round -------------

/--
info: [1, 2, 1, 3, 2, 3, 1]
-/
#guard_msgs in
#eval (List.range 7).map (fun c => ((WallaceTree.WallaceRound pp4).1.get c).height)

#eval (WallaceTree.WallaceRound pp4).2

-- Number of adders produced in this round.
/--
info: 3
-/
#guard_msgs in
#eval (WallaceTree.WallaceRound pp4).2.length

------------- Full Wallace tree -------------

-- Total adders in the full reduction.
/--
info: 6
-/
#guard_msgs in
#eval (WallaceTree.WallaceTree pp4).2.length


#eval (WallaceTree.WallaceTree pp4).2

/--
info: [1, 2, 1, 1, 1, 2, 2, 0]
-/
#guard_msgs in
#eval (List.range 8).map (fun c => ((WallaceTree.WallaceTree pp4).1.get c).height)

end WallaceTreeExamples
end BitHeap
