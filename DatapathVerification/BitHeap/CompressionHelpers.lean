import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.Column
import Std.Data.HashSet

open BitHeap

open Chain

namespace Compression

def applyHalfAdder (column : Nat) (i j : Circuit) (h : BitHeap w) (acc : BitHeap w) : (BitHeap w × BitHeap w × Adder) :=
  let HA := Adder.halfAdder column i j
  let newAcc := Chain.applyAdder HA acc -- applies a Half Adder, removing compressed bits and adding sum and carry bits to acc.
  let newOriginal := h.removeBit column i |>.removeBit column j -- removes the compressed bits from the original heap.
  (newOriginal, newAcc, HA)

def applyFullAdder (column : Nat) (i j k : Circuit) (h : BitHeap w) (acc : BitHeap w) : (BitHeap w × BitHeap w × Adder) :=
  let FA := Adder.fullAdder column i j k
  let newAcc := Chain.applyAdder FA acc -- applies a Full Adder, removing compressed bits and adding sum and carry bits to acc.
  let newOriginal := h.removeBit column i |>.removeBit column j |>.removeBit column k -- removes the compressed bits from the original heap.
  (newOriginal, newAcc, FA)

end Compression
