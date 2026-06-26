import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain

namespace BitHeap

open Chain

namespace Examples

def addBitsExample (w : Nat) : BitHeap w :=
  let h := BitHeap.empty w
  let h := h.addBit 0 (Circuit.bit 0)-- add a bit in column 0
  let h := h.addBit 1 (Circuit.bit 1) -- add a bit in column 1
  let h := h.addBit 1 (Circuit.bit 1) -- add another bit in column 1
  let h := h.addBit 1 (Circuit.bit 1) -- add another bit in column 1
  let h := h.removeBit 0 (Circuit.bit 0) -- remove the bit in column 0
  let h := h.removeBit 0 (Circuit.bit 0) -- remove the bit in column 0
  h
/--
info: {0 ↦ [], 1 ↦ [b1], 2 ↦ [b1]}
-/
#guard_msgs in
#eval addBitsExample 3

abbrev BitEnv := Nat → Bool

def fourBitsInCol1 : BitHeap 4 :=
  let h := BitHeap.empty 4
  let h := h.addBit 1 (Circuit.bit 0)
  let h := h.addBit 1 (Circuit.bit 1)
  let h := h.addBit 1 (Circuit.bit 2)
  let h := h.addBit 1 (Circuit.bit 3)
  h

def compressionChain : List Adder :=
  [.fullAdder 1 (Circuit.bit 0) (Circuit.bit 1) (Circuit.bit 2)]

-- assign bits 1,2,3 to 1 and bit 0 to 0 => 3 * 2^1 = 6
/--
info: 6
-/
#guard_msgs in
#eval fourBitsInCol1.eval (show BitEnv from fun n => n = 1 || n = 2 || n = 3)

-- Result does not change after applying a full adder.
/--
info: 6
-/
#guard_msgs in
#eval (applyChain compressionChain fourBitsInCol1).eval (show BitEnv from fun n => n = 1 || n = 2 || n = 3)

def exampleHeap : BitHeap 5:=
  let h := BitHeap.empty 5
  let h := h.addBit 1 (Circuit.bit 0)
  let h := h.addBit 1 (Circuit.bit 1)
  let h := h.addBit 2 (Circuit.bit 2)
  let h := h.addBit 2 (Circuit.bit 3)
  let h := h.addBit 2 (Circuit.bit 4)
  h

/--
info: 3
-/
#guard_msgs in
#eval exampleHeap.maxHeight

/--
info: some 2
-/
#guard_msgs in
#eval exampleHeap.highestColumn

----------------------------
-- Examples of incorrect chains --

def badChain : List Adder :=
  [.halfAdder 1 (Circuit.bit 1) (Circuit.const true)]

-- The result 8 does not make sense here since we compressed a bit was not a part of the bitheap.
/--
info: 8
-/
#guard_msgs in
#eval (applyChain badChain fourBitsInCol1).eval
        (show BitEnv from fun n => n = 1 || n = 2 || n = 3)

-- Returns none since the half adder is not applicable (constant bit is not in the heap).
/--
info: none
-/
#guard_msgs in
#eval applyChainSafe badChain fourBitsInCol1

-- Returns the correct value.
/--
info: 6
-/
#guard_msgs in
#eval (applyChain compressionChain fourBitsInCol1).eval
        (show BitEnv from fun n => n = 1 || n = 2 || n = 3)

----------------------------

def exampleHeap1 : BitHeap :=
  let h := BitHeap.empty
  let h := h.addBit 0 (Circuit.bit 0)
  let h := h.addBit 1 (Circuit.bit 1)
  let h := h.addBit 2 (Circuit.bit 2)
  let h := h.addBit 3 (Circuit.bit 3)
  h

def exampleHeap2 : BitHeap :=
  let h := BitHeap.empty
  let h := h.addBit 0 (Circuit.bit 4)
  let h := h.addBit 1 (Circuit.bit 5)
  let h := h.addBit 2 (Circuit.bit 6)
  let h := h.addBit 3 (Circuit.bit 7)
  h

/--
info: {0 ↦ [b0, b4], 1 ↦ [b1, b5], 2 ↦ [b2, b6], 3 ↦ [b3, b7]}-/
#guard_msgs in
#eval addBitHeap exampleHeap1 exampleHeap2

/--
info: {0 ↦ [(b0 ∧ b4)], 1 ↦ [(b0 ∧ b5), (b1 ∧ b4)], 2 ↦ [(b1 ∧ b5), (b2 ∧ b4), (b0 ∧ b6)], 3 ↦ [(b3 ∧ b4), (b0 ∧ b7), (b2 ∧ b5), (b1 ∧ b6)], 4 ↦ [(b2 ∧ b6), (b3 ∧ b5), (b1 ∧ b7)], 5 ↦ [(b3 ∧ b6), (b2 ∧ b7)], 6 ↦ [(b3 ∧ b7)]}
-/
#guard_msgs in
#eval mulBitHeap exampleHeap1 exampleHeap2

end Examples

end BitHeap
