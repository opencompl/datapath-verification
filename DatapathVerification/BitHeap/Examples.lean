import DatapathVerification.BitHeap.BitHeap

open BitHeap
open BitHeap.Circuit

namespace BitHeap.Examples

def addBitsExample : BitHeap :=
  let h := BitHeap.empty
  let (h, _) := h.addBit (Circuit.bit 0) 0 -- add a bit in column 0
  let (h, _) := h.addBit (Circuit.bit 1) 1 -- add a bit in column 1
  let (h, _) := h.addBit (Circuit.bit 1) 1 -- add another bit in column 1
  let h := h.removeBit (Index.mk 0 0) -- remove the bit in column 0
  h
/--
info: { columns := [(0, { elems := [] }), (1, { elems := [BitHeap.Circuit.bit 1, BitHeap.Circuit.bit 1] })] }
-/
#guard_msgs in
#eval addBitsExample

end BitHeap.Examples
