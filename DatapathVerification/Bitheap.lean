structure WeightedBit where
  weight : Nat
  bit : Bool
  index : Nat
  deriving Repr, DecidableEq

/-- A bit heap represents a sum of weighted bits, organized into columns based on the weights
    and height of each column corresponding to the number of bits to be summed for a particular weight. -/
abbrev BitHeap := List (List WeightedBit)

namespace BitHeap

-- Get the column at the given weight.
def getColumn (h : BitHeap) (w : Nat) : List WeightedBit :=
  h.getD w []

-- The number of bits at weight `w`.
def columnHeight (h : BitHeap) (w : Nat) : Nat :=
  (getColumn h w).length

-- The number of columns.
def width (h : BitHeap) : Nat :=
  h.length

-- Get the height of the column with max height.
def getMaxHeight (h : BitHeap) : Nat :=
  sorry

-- Add a `WeightedBit` to the heap at its weight.
def addWeightedBit (h : BitHeap) (wb : WeightedBit) : BitHeap :=
  sorry

-- Remove one bit from column `w`. Returns the removed bit and the new heap.
def popBit (h : BitHeap) (w : Nat) : (WeightedBit × BitHeap) :=
  sorry

-- Remove the bit at index `i` of column `w`.
def removeBitAt (h : BitHeap) (w : Nat) (i : Nat) : BitHeap :=
  sorry

-- Remove the bit with the given unique `WeightedBit.index`, wherever it is.
def removeByIndex (h : BitHeap) (idx : Nat) : BitHeap :=
  sorry

-- The set of indices appearing in the heap.
def indices (h : BitHeap) : List Nat :=
  sorry

-- Property that all indices in the heap are unique.
def uniqueIndices (h : BitHeap) : Prop :=
  sorry

-- The natural number value of the entire heap.
def toNat (h : BitHeap) : Nat :=
  sorry

/-- Half Adder (2:2 compressor) takes 2 bits of the same weight `w`
    and produces a sum bit at weight `w` and a carry bit at weight `w+1`. -/
def halfAdder (a b : WeightedBit) : WeightedBit × WeightedBit :=
  sorry

-- Apply half adder to a column of the bit heap
def applyHalfAdder (h : BitHeap) (w : Nat) : BitHeap :=
  sorry

/-- Full Adder (3:2 compressor) takes three bits of the same weight `w`
    and produces a sum bit at weight `w` and a carry bit at weight `w+1`. -/
def fullAdder (a b c : WeightedBit) : WeightedBit × WeightedBit :=
  sorry

-- Apply full adder to the bit heap
def applyFullAdder (h : BitHeap) (w : Nat) : BitHeap :=
  sorry

/-- Applying a half adder preserves the value represented by the heap. -/
theorem applyHalfAdder_toNat (h : BitHeap) (w : Nat)
    (hgte : columnHeight h w ≥ 2) :
    toNat (applyHalfAdder h w) = toNat h :=
  sorry

/-- Applying a full adder preserves the value represented by the heap. -/
theorem applyFullAdder_toNat (h : BitHeap) (w : Nat)
    (hgte : columnHeight h w ≥ 3) :
    toNat (applyFullAdder h w) = toNat h :=
  sorry

end BitHeap
