import Blase
import DatapathVerification.CSA

set_option maxHeartbeats 50000000
set_option Elab.async false
/-!
  This file compares the performance of bv_decide in different multiplication circuits.
-/

-- Namespace for the multiplication implementations defined in CSA.lean
namespace CSA

-- Multiplication implementation based on compression of partial products.
set_option trace.profiler true in
theorem mulChain_4bit (x y : BitVec 4) : mulChain x y = mulChain y x  := by
  bv_decide

set_option trace.profiler true in
theorem mulChain_5bit (x y : BitVec 5) : mulChain x y = mulChain y x  := by
  bv_decide

set_option trace.profiler true in
theorem mulChain_6bit (x y : BitVec 6) : mulChain x y = mulChain y x  := by
  bv_decide

set_option trace.profiler true in
theorem mulChain_7bit (x y : BitVec 7) : mulChain x y = mulChain y x  := by
  bv_decide

set_option trace.profiler true in
theorem mulChain_8bit (x y : BitVec 8) : mulChain x y = mulChain y x  := by
  bv_decide

set_option trace.profiler true in
theorem mulChain_9bit (x y : BitVec 9) : mulChain x y = mulChain y x  := by
  bv_decide

set_option trace.profiler true in
theorem mulChain_10bit (x y : BitVec 10) : mulChain x y = mulChain y x  := by
  bv_decide (config := { timeout := 200})

set_option trace.profiler true in
theorem mulChain_11bit (x y : BitVec 11) : mulChain x y = mulChain y x  := by
  bv_decide (config := { timeout := 200})

set_option trace.profiler true in
theorem mulChain_opt_4bit (x y : BitVec 4) : mulChain_opt x y = mulChain_opt y x  := by
  simp [mulChain_opt, partialProducts, partialProducts']
  repeat (unfold chain_opt; simp [List.reverse, List.reverseAux])
  bv_decide

set_option trace.profiler true in
theorem mulChain_opt_5bit (x y : BitVec 5) : mulChain_opt x y = mulChain_opt y x  := by
  simp [mulChain_opt, partialProducts, partialProducts']
  repeat (unfold chain_opt; simp [List.reverse, List.reverseAux])
  bv_decide

set_option trace.profiler true in
theorem mulChain_opt_6bit (x y : BitVec 6) : mulChain_opt x y = mulChain_opt y x  := by
  simp [mulChain_opt, partialProducts, partialProducts']
  repeat (unfold chain_opt; simp [List.reverse, List.reverseAux])
  bv_decide

set_option trace.profiler true in
theorem mulChain_opt_7bit (x y : BitVec 7) : mulChain_opt x y = mulChain_opt y x  := by
  simp [mulChain_opt, partialProducts, partialProducts']
  repeat (unfold chain_opt; simp [List.reverse, List.reverseAux])
  bv_decide

set_option trace.profiler true in
theorem mulChain_opt_8bit (x y : BitVec 8) : mulChain_opt x y = mulChain_opt y x  := by
  simp [mulChain_opt, partialProducts, partialProducts']
  repeat (unfold chain_opt; simp [List.reverse, List.reverseAux])
  bv_decide

set_option trace.profiler true in
theorem mulChain_opt_9bit (x y : BitVec 9) : mulChain_opt x y = mulChain_opt y x  := by
  simp [mulChain_opt, partialProducts, partialProducts']
  repeat (unfold chain_opt; simp [List.reverse, List.reverseAux])
  bv_decide

set_option trace.profiler true in
theorem mulChain_opt_10bit (x y : BitVec 10) : mulChain_opt x y = mulChain_opt y x  := by
  simp [mulChain_opt, partialProducts, partialProducts']
  repeat (unfold chain_opt; simp [List.reverse, List.reverseAux])
  bv_decide (config := { timeout := 200})

set_option trace.profiler true in
theorem mulChain_opt_11bit (x y : BitVec 11) : mulChain_opt x y = mulChain_opt y x  := by
  simp [mulChain_opt, partialProducts, partialProducts']
  repeat (unfold chain_opt; simp [List.reverse, List.reverseAux])
  bv_decide (config := { timeout := 400})

end CSA

-- Multiplication implementation used in the Bit Blaster of Lean 4.
namespace CSABlastMul

@[bv_normalize]
def mulRecRef (x y : BitVec w) (s : Nat) : BitVec w :=
  let cur := if y.getLsbD s then (x <<< s) else 0
  match s with
  | 0 => cur
  | s + 1 => mulRecRef x y s + cur

@[bv_normalize]
def mulRef (x y : BitVec w) : BitVec w :=
  mulRecRef x y (w - 1)

set_option trace.profiler true in
theorem mul_comm_4bit (x y : BitVec 4) : mulRef x y = mulRef y x  := by
    bv_decide

set_option trace.profiler true in
theorem mul_comm_5bit (x y : BitVec 5) : mulRef x y = mulRef y x  := by
    bv_decide

set_option trace.profiler true in
theorem mul_comm_6bit (x y : BitVec 6) : mulRef x y = mulRef y x  := by
    bv_decide

set_option trace.profiler true in
theorem mul_comm_7bit (x y : BitVec 7) : mulRef x y = mulRef y x  := by
    bv_decide

set_option trace.profiler true in
theorem mul_comm_8bit (x y : BitVec 8) : mulRef x y = mulRef y x  := by
    bv_decide

set_option trace.profiler true in
theorem mul_comm_9bit (x y : BitVec 9) : mulRef x y = mulRef y x  := by
    bv_decide

set_option trace.profiler true in
theorem mul_comm_10bit (x y : BitVec 10) : mulRef x y = mulRef y x  := by
  bv_decide (config := { timeout := 200})

set_option trace.profiler true in
theorem mul_comm_11bit (x y : BitVec 11) : mulRef x y = mulRef y x  := by
  bv_decide (config := { timeout := 200})

end CSABlastMul
