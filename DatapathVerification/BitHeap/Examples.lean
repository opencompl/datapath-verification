import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain

namespace BitHeap

open Chain

namespace Examples

def addBitsExample : BitHeap :=
  let h := BitHeap.empty
  let h := h.addBit 0 (Circuit.bit 0)-- add a bit in column 0
  let h := h.addBit 1 (Circuit.bit 1) -- add a bit in column 1
  let h := h.addBit 1 (Circuit.bit 1) -- add another bit in column 1
  let h := h.addBit 1 (Circuit.bit 1) -- add another bit in column 1
  let h := h.removeBit 0 (Circuit.bit 0) -- remove the bit in column 0
  let h := h.removeBit 0 (Circuit.bit 0) -- remove the bit in column 0
  h
/--
info: { columns := [(0, { elems := Std.HashSet.ofList [] }),
              (1, { elems := Std.HashSet.ofList [BitHeap.Circuit.bit 1] }),
              (2, { elems := Std.HashSet.ofList [BitHeap.Circuit.bit 1] })] }
-/
#guard_msgs in
#eval addBitsExample

abbrev BitEnv := Nat → Bool

def fourBitsInCol1 : BitHeap :=
  let h := BitHeap.empty
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

end Examples

end BitHeap
