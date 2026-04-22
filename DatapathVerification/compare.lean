import Blase
import DatapathVerification.CSA

/-!
  This file compares the performance of bv_decide in different multiplication circuits.
-/

namespace CSA

set_option trace.profiler true in
theorem mul_comm' (x y : BitVec 9) : mulChain x y = mulChain y x  := by
  bv_decide

end CSA

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
theorem mul_comm' (x y : BitVec 9) : mulRef x y = mulRef y x  := by
    bv_decide

end CSABlastMul
