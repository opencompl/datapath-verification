import DatapathVerification.BitHeap.BVComb

open BitHeap
open Comb

def testEnv : BitVecEnv 4 := fun i =>
  match i with
  | 0 => 6#4
  | 1 => 3#4
  | 2 => 5#4
  | 3 => 15#4
  | _ => 0#4

----------

/-- info: 6 -/
#guard_msgs in
#eval (ArithCircuit.var 0 : ArithCircuit 4).toBitHeap.evalMod (BitVecEnv.toBitEnv testEnv)

-- add, no overflow: (6+3) % 16 = 9
/-- info: 9 -/
#guard_msgs in
#eval (ArithCircuit.add [.var 0, .var 1] : ArithCircuit 4).toBitHeap.evalMod (BitVecEnv.toBitEnv testEnv)

-- add, WITH overflow: (6+3+5+15) % 16 = 29 % 16 = 13
/-- info: 13 -/
#guard_msgs in
#eval (ArithCircuit.add [.var 0, .var 1, .var 2, .var 3] : ArithCircuit 4).toBitHeap.evalMod (BitVecEnv.toBitEnv testEnv)

-- mul, no overflow: (3*5) % 16 = 15 % 16 = 15
/-- info: 15 -/
#guard_msgs in
#eval (ArithCircuit.mul (.var 1) (.var 2) : ArithCircuit 4).toBitHeap.evalMod (BitVecEnv.toBitEnv testEnv)

-- mul, WITH overflow: (5*15) % 16 = 75 % 16 = 11
/-- info: 11 -/
#guard_msgs in
#eval (ArithCircuit.mul (.var 2) (.var 3) : ArithCircuit 4).toBitHeap.evalMod (BitVecEnv.toBitEnv testEnv)

-- (5*5) % 16 = 25 % 16 = 9
/-- info: 9 -/
#guard_msgs in
#eval (ArithCircuit.mul (.var 2) (.var 2) : ArithCircuit 4).toBitHeap.evalMod (BitVecEnv.toBitEnv testEnv)

-- nesting: (6+3)*5 % 16 = 45 % 16 = 13
/-- info: 13 -/
#guard_msgs in
#eval (ArithCircuit.mul (.add [.var 0, .var 1]) (.var 2) : ArithCircuit 4).toBitHeap.evalMod (BitVecEnv.toBitEnv testEnv)

----------

/-- info: 13 -/
#guard_msgs in
#eval ((ArithCircuit.add [.var 0, .var 1, .var 2, .var 3] : ArithCircuit 4).toCircuitVector).eval (BitVecEnv.toBitEnv testEnv)

/-- info: 11 -/
#guard_msgs in
#eval ((ArithCircuit.mul (.var 2) (.var 3) : ArithCircuit 4).toCircuitVector).eval (BitVecEnv.toBitEnv testEnv)

/-- info: 9 -/
#guard_msgs in
#eval ((ArithCircuit.mul (.var 2) (.var 2) : ArithCircuit 4).toCircuitVector).eval (BitVecEnv.toBitEnv testEnv)

/-- info: 225 -/
#guard_msgs in
#eval ((ArithCircuit.var 3 : ArithCircuit 4).toBitHeap.mulBitHeap
        (ArithCircuit.var 3 : ArithCircuit 4).toBitHeap).eval (BitVecEnv.toBitEnv testEnv)

#eval toString ((ArithCircuit.var 3 : ArithCircuit 4).toBitHeap.mulBitHeap
        (ArithCircuit.var 3 : ArithCircuit 4).toBitHeap)
