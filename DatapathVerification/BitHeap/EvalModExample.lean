import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain

namespace BitHeap

open Chain

namespace EvalModExample

abbrev BitEnv := Nat → Bool

def env1 : BitEnv := fun n => n = 0 || n = 2 || n = 4

-- A heap with width 3: only columns 0, 1, 2 contribute under evalMod.
-- Bits in column 3 (and beyond) get truncated away.
def heapWidth3 : BitHeap :=
  let h : BitHeap := ⟨3, Std.HashMap.emptyWithCapacity 0⟩
  let h := h.addBit 0 (Circuit.bit 0)
  let h := h.addBit 1 (Circuit.bit 1)
  let h := h.addBit 2 (Circuit.bit 2)
  let h := h.addBit 3 (Circuit.bit 3)  -- this contributes to eval but not evalMod
  h

-- Full eval: bit 0 = T (1), bit 1 = F (0), bit 2 = T (4), bit 3 = F (0)
-- Total = 1 + 0 + 4 + 0 = 5
/--
info: 5
-/
#guard_msgs in
#eval heapWidth3.eval (show BitEnv from env1)

-- evalMod with width 3: same as eval mod 8 = 5 mod 8 = 5
/--
info: 5
-/
#guard_msgs in
#eval heapWidth3.evalMod (show BitEnv from env1)

-- Now with bit 3 set (env2 sets bits 0, 2, 3)
def env2 : BitEnv := fun n => n = 0 || n = 2 || n = 3

-- Full eval: 1 + 0 + 4 + 8 = 13
/--
info: 13
-/
#guard_msgs in
#eval heapWidth3.eval (show BitEnv from env2)

-- evalMod: 13 mod 8 = 5 (the bit-3 contribution is truncated)
/--
info: 5
-/
#guard_msgs in
#eval heapWidth3.evalMod (show BitEnv from env2)
