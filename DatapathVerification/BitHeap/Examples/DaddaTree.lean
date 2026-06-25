import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.DaddaTree
import DatapathVerification.BitHeap.Examples.PartialProductGenerator

namespace BitHeap

open Chain
open PartialProductGenerator

namespace DaddaTreeExamples

#eval DaddaTree.DaddaSequence 1

/--
info: [2, 3, 4, 6, 9, 13, 19, 28, 42, 63]
-/
#guard_msgs in
#eval (List.range 10).map DaddaTree.DaddaSequence

/--
info: 2
-/
#guard_msgs in
#eval DaddaTree.findDaddaLevel 4

/--
info: 4
-/
#guard_msgs in
#eval DaddaTree.findDaddaLevel 9

abbrev BitEnv := Nat → Bool

def pp4 : BitHeap 8 := bitHeapOfPartialProducts 4
def pp8 : BitHeap 16:= bitHeapOfPartialProducts 8

------------- First Dadda stage -------------

/--
info: [1, 2, 3, 3, 3, 3, 1]
-/
#guard_msgs in
#eval (List.range 7).map (fun c => ((DaddaTree.DaddaStage pp4 2).1.get c).height)

/--
info: [HA(3: b9, b6), HA(4: b10, b13)]
-/
#guard_msgs in
#eval (DaddaTree.DaddaStage pp4 2).2

/--
info: (some {0 ↦ [b0], 1 ↦ [b1, b4], 2 ↦ [(b2 ⊕ b5), b8], 3 ↦ [((b3 ⊕ b12) ⊕ (b9 ⊕ b6)), (b2 ∧ b5)], 4 ↦ [(((b3 ∧ b12) ∨ (b3 ∧ (b9 ⊕ b6))) ∨ (b12 ∧ (b9 ⊕ b6))), ((b7 ⊕ (b10 ⊕ b13)) ⊕ (b9 ∧ b6))], 5 ↦ [(((b7 ∧ (b10 ⊕ b13)) ∨ (b7 ∧ (b9 ∧ b6))) ∨ ((b10 ⊕ b13) ∧ (b9 ∧ b6))), ((b14 ⊕ b11) ⊕ (b10 ∧ b13))], 6 ↦ [b15, (((b14 ∧ b11) ∨ (b14 ∧ (b10 ∧ b13))) ∨ (b11 ∧ (b10 ∧ b13)))], 7 ↦ []})-/
#guard_msgs in
#eval (applyChainSafe (DaddaTree.DaddaTree pp4).2 pp4)

------------- Full Dadda tree for PP4 -------------

-- Total adders in the full reduction.
/--
info: "FAs: 3, HAs: 3"
-/
#guard_msgs in
#eval printSummary (DaddaTree.DaddaTree pp4).2

#eval (DaddaTree.DaddaTree pp4).2

/--
info: [1, 2, 2, 2, 2, 2, 2, 0]
-/
#guard_msgs in
#eval (List.range 8).map (fun c => ((DaddaTree.DaddaTree pp4).1.get c).height)

------------- Full Dadda tree for PP8 -------------

/--
info: [1, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 0, 0]
-/
#guard_msgs in
#eval (List.range 17).map (fun c => ((DaddaTree.DaddaTree pp8).1.get c).height)

/--
info: "FAs: 35, HAs: 7"
-/
#guard_msgs in
#eval printSummary (DaddaTree.DaddaTree pp8).2

#eval (DaddaTree.DaddaTree pp8).2

end DaddaTreeExamples
end BitHeap
