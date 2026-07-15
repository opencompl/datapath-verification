import DatapathVerification.BitHeap.BVComb

open BitHeap
open Comb

def testEnv : BitVecEnv 4 := fun i => if i = 0 then 6#4 else 3#4

-- 6x3 = 18
/--
info: 18
-/
#guard_msgs in
#eval (ArithCircuit.mul (.var 0) (.var 1) : ArithCircuit 4).toBitHeap.eval (BitVecEnv.toBitEnv testEnv)

-- 6 + 3 + 3 = 12
/--
info: 12
-/
#guard_msgs in
#eval ((ArithCircuit.add [(.var 0), (.var 1), (.var 2)] : ArithCircuit 4).toCircuitVector).eval (BitVecEnv.toBitEnv testEnv)
