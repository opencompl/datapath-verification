import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.NaiveCompression

namespace BitHeap

open Chain

namespace NaiveCompressionExamples

def threeBitsInCol1 : BitHeap :=
  let h := BitHeap.empty
  let h := h.addBit 1 (Circuit.bit 0)
  let h := h.addBit 1 (Circuit.bit 1)
  let h := h.addBit 1 (Circuit.bit 2)
  h

def fiveBitsInCol1 : BitHeap :=
  let h := BitHeap.empty
  let h := h.addBit 1 (Circuit.bit 0)
  let h := h.addBit 1 (Circuit.bit 1)
  let h := h.addBit 1 (Circuit.bit 2)
  let h := h.addBit 1 (Circuit.bit 3)
  let h := h.addBit 1 (Circuit.bit 4)
  h

def multiColSmall : BitHeap :=
  let h := BitHeap.empty
  let h := h.addBit 0 (Circuit.bit 0)
  let h := h.addBit 0 (Circuit.bit 1)
  let h := h.addBit 1 (Circuit.bit 2)
  let h := h.addBit 1 (Circuit.bit 3)
  let h := h.addBit 1 (Circuit.bit 4)
  let h := h.addBit 1 (Circuit.bit 5)
  let h := h.addBit 2 (Circuit.bit 6)
  let h := h.addBit 2 (Circuit.bit 7)
  h

abbrev BitEnv := Nat → Bool

def env1 : BitEnv := fun n => n = 0 || n = 2 || n = 4
def env2 : BitEnv := fun n => n = 0 || n = 2 || n = 5

-------------

/--
info: 4
-/
#guard_msgs in
#eval threeBitsInCol1.eval (show BitEnv from env1)

-- Chain length 1 (single FA)
/--
info: 1
-/
#guard_msgs in
#eval (NaiveCompression.reduceColumn 1 threeBitsInCol1).2.length

-- Reduced heap evaluates the same
/--
info: 4
-/
#guard_msgs in
#eval (NaiveCompression.reduceColumn 1 threeBitsInCol1).1.eval (show BitEnv from env1)

-------------

/--
info: 6
-/
#guard_msgs in
#eval fiveBitsInCol1.eval (show BitEnv from env1)

-- Chain length 2 (FA + FA)
/--
info: 2
-/
#guard_msgs in
#eval (NaiveCompression.reduceColumn 1 fiveBitsInCol1).2.length

-- Reduced heap evaluates the same
/--
info: 6
-/
#guard_msgs in
#eval (NaiveCompression.reduceColumn 1 fiveBitsInCol1).1.eval (show BitEnv from env1)


-------------
/--
info: 5
-/
#guard_msgs in
#eval multiColSmall.eval (show BitEnv from env2)

/--
info: 2
-/
#guard_msgs in
#eval (NaiveCompression.naiveCompression multiColSmall).2.length

-- Value preserved
/--
info: 5
-/
#guard_msgs in
#eval (NaiveCompression.naiveCompression multiColSmall).1.eval (show BitEnv from env2)

/--
info: 2
-/
#guard_msgs in
#eval (NaiveCompression.naiveCompression multiColSmall).1.maxHeight

/--
info: [FA(1: b2, b4, b3), HA(2: (((b2 ∧ b4) ∨ (b2 ∧ b3)) ∨ (b4 ∧ b3)), b7)]
-/
#guard_msgs in
#eval (NaiveCompression.naiveCompression multiColSmall).2

end NaiveCompressionExamples
end BitHeap
