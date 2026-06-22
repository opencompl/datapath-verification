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
def pp8 : BitHeap := bitHeapOfPartialProducts 8
/--
info: [1, 2, 3, 4, 3, 2, 1]
-/
#guard_msgs in
#eval (List.range 7).map (fun c => (pp4.get c).height)

------------- First Wallace stage -------------

/--
info: [1, 1, 2, 3, 2, 2, 2]
-/
#guard_msgs in
#eval (List.range 7).map (fun c => ((WallaceTree.WallaceStage pp4).1.get c).height)

#eval (WallaceTree.WallaceStage pp4).2

-- Number of adders produced in this stage.
/--
info: 5
-/
#guard_msgs in
#eval (WallaceTree.WallaceStage pp4).2.length


def env2 : BitEnv := fun n => n = 0 || n = 2 || n = 5 || n = 6

/--
info: (some {0 ↦ [b0], 1 ↦ [(b1 ⊕ b4)], 2 ↦ [(((b2 ⊕ b5) ⊕ b8) ⊕ (b1 ∧ b4))], 3 ↦ [(((b2 ⊕ b5) ⊕ b8) ∧ (b1 ∧ b4)), ((((b9 ⊕ b6) ⊕ b3) ⊕ b12) ⊕ (((b2 ∧ b5) ∨ (b2 ∧ b8)) ∨ (b5 ∧ b8)))], 4 ↦ [((((b9 ∧ b6) ∨ (b9 ∧ b3)) ∨ (b6 ∧ b3)) ⊕ ((b10 ⊕ b13) ⊕ b7)), (((((b9 ⊕ b6) ⊕ b3) ∧ b12) ∨ (((b9 ⊕ b6) ⊕ b3) ∧ (((b2 ∧ b5) ∨ (b2 ∧ b8)) ∨ (b5 ∧ b8)))) ∨ (b12 ∧ (((b2 ∧ b5) ∨ (b2 ∧ b8)) ∨ (b5 ∧ b8))))], 5 ↦ [((b11 ⊕ b14) ⊕ (((b10 ∧ b13) ∨ (b10 ∧ b7)) ∨ (b13 ∧ b7))), ((((b9 ∧ b6) ∨ (b9 ∧ b3)) ∨ (b6 ∧ b3)) ∧ ((b10 ⊕ b13) ⊕ b7))], 6 ↦ [((b11 ⊕ b14) ∧ (((b10 ∧ b13) ∨ (b10 ∧ b7)) ∨ (b13 ∧ b7))), (b15 ⊕ (b11 ∧ b14))], 7 ↦ [(b15 ∧ (b11 ∧ b14))]})
-/
#guard_msgs in
#eval (applyChainSafe (WallaceTree.WallaceTree pp4).2 pp4)

------------- Full Wallace tree -------------

-- Total adders in the full reduction.
/--
info: 10
-/
#guard_msgs in
#eval (WallaceTree.WallaceTree pp4).2.length

#eval (WallaceTree.WallaceTree pp4).2

/--
info: [1, 1, 1, 2, 2, 2, 2, 1]
-/
#guard_msgs in
#eval (List.range 8).map (fun c => ((WallaceTree.WallaceTree pp4).1.get c).height)

#eval (WallaceTree.WallaceTree pp8).2.length

/--
info: [1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]
-/
#guard_msgs in
#eval (List.range 16).map (fun c => ((WallaceTree.WallaceTree pp8).1.get c).height)

#eval (WallaceTree.WallaceTree pp8).2
end WallaceTreeExamples
end BitHeap
