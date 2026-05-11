import DatapathVerification.BitHeap.BitHeap

namespace BitHeap

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

end Examples

end BitHeap
