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

------

def compressed (c : ArithCircuit w) : BitHeap w := (DaddaTree.DaddaTree c.toBitHeap).1

def addThree : ArithCircuit 4 := .add [.var 0, .var 1, .var 2]

def mulTwo : ArithCircuit 4 := .mul (.var 0) (.var 1)

/-- info: "{0 ↦ [b4, b8, b0], 1 ↦ [b1, b5, b9], 2 ↦ [b2, b10, b6], 3 ↦ [b3, b11, b7]}" -/
#guard_msgs in
#eval toString addThree.toBitHeap

/-- info:
"{0 ↦ [(b4 ⊕ b8), b0], 1 ↦ [(b4 ∧ b8), ((b1 ⊕ b5) ⊕ b9)], 2 ↦ [((b1 ∧ b5) ∨ ((b1 ⊕ b5) ∧ b9)), ((b2 ⊕ b10) ⊕ b6)], 3 ↦ [((b3 ⊕ b11) ⊕ b7), ((b2 ∧ b10) ∨ ((b2 ⊕ b10) ∧ b6))]}"
-/
#guard_msgs in
#eval toString (compressed addThree)
/-- info: "{0 ↦ [(b0 ∧ b4)], 1 ↦ [(b0 ∧ b5), (b1 ∧ b4)], 2 ↦ [((b1 ∧ b5) ⊕ (b2 ∧ b4)), (b0 ∧ b6)], 3 ↦ [((((b3 ∧ b4) ⊕ (b0 ∧ b7)) ⊕ (b2 ∧ b5)) ⊕ (b1 ∧ b6)), ((b1 ∧ b5) ∧ (b2 ∧ b4))]}" -/
#guard_msgs in
#eval toString (compressed mulTwo)

/-- info: "[HA(0: b4, b8), FA(1: b1, b5, b9), FA(2: b2, b10, b6), FA(3: b3, b11, b7)]" -/
#guard_msgs in
#eval toString (DaddaTree.DaddaTree addThree.toBitHeap).2

/-- info: "[HA(3: (b3 ∧ b4), (b0 ∧ b7)), HA(2: (b1 ∧ b5), (b2 ∧ b4)), FA(3: ((b3 ∧ b4) ⊕ (b0 ∧ b7)), (b2 ∧ b5), (b1 ∧ b6))]" -/
#guard_msgs in
#eval toString (DaddaTree.DaddaTree mulTwo.toBitHeap).2

def fma : ArithCircuit 4 := .add [mulTwo, .var 2]


/-- info: 13 -/
#guard_msgs in
#eval (compressed (.add [.var 0, .var 1, .var 2, .var 3] : ArithCircuit 4)).eval (BitVecEnv.toBitEnv testEnv)

/-- info: 11 -/
#guard_msgs in
#eval (compressed (.mul (.var 2) (.var 3) : ArithCircuit 4)).eval (BitVecEnv.toBitEnv testEnv)

--- Zero-extension Tests

-- i3 -> i6 zero extension
def mulZext : ArithCircuit 6 := .mul (.zext 0 3 (by omega)) (.zext 1 3 (by omega))

/-- info: "{0 ↦ [(b0 ∧ b6)], 1 ↦ [(b0 ∧ b7), (b1 ∧ b6)], 2 ↦ [(b2 ∧ b6), (b1 ∧ b7), (b0 ∧ b8)], 3 ↦ [(b1 ∧ b8), (b2 ∧ b7)], 4 ↦ [(b2 ∧ b8)], 5 ↦ []}" -/
#guard_msgs in
#eval toString mulZext.toBitHeap

/-- info: "[HA(2: (b2 ∧ b6), (b1 ∧ b7)), HA(3: (b1 ∧ b8), (b2 ∧ b7))]" -/
#guard_msgs in
#eval toString (DaddaTree.DaddaTree mulZext.toBitHeap).2

def testEnv6 : BitVecEnv 6 := fun i =>
  match i with
  | 0 => 5#6
  | 1 => 7#6
  | _ => 0#6

/-- info: 35 -/
#guard_msgs in
#eval (compressed mulZext).eval (BitVecEnv.toBitEnv testEnv6)

def testEnv3 : BitVecEnv 3 := fun i =>
  match i with
  | 0 => 5#3
  | 1 => 7#3
  | _ => 0#3

def mulNoZext : ArithCircuit 3 := .mul (.zext 0 3 (by omega)) (.zext 1 3 (by omega))

-- without extension we get the truncated result 3
/-- info: 3 -/
#guard_msgs in
#eval (compressed mulNoZext).eval (BitVecEnv.toBitEnv testEnv3)
