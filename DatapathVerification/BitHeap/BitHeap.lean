import Std.Data.HashMap
import Std.Data.HashSet
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.Column

instance [BEq α] [Hashable α] [Repr α] [Repr β] : Repr (Std.HashMap α β) where
  reprPrec m _ := repr m.toList

structure BitHeap where
  columns : Std.HashMap Nat BitHeap.Column
deriving Inhabited, Repr

namespace BitHeap

open Circuit
open Column

def empty : BitHeap := ⟨Std.HashMap.emptyWithCapacity 0⟩

/--
Evaluate a bit-heap, to compute the final sum of all the bits in the heap.
-/
def eval (h : BitHeap) (env : BitEnv) : Int :=
  (h.columns.fold (init := 0) (fun acc w col => acc + (2 ^ w) * col.eval env))

structure AdderResult where
  heap : BitHeap
  sum : Circuit
  carry : Circuit

def removeBit (column : Nat) (c : Circuit) (h : BitHeap) : BitHeap :=
  ⟨h.columns.modify column (fun col => col.erase c)⟩

/--
Add a bit into the bit heap, returning a new bit heap. If the bit already exists in the column, remove it and add it to the next column.
-/
partial def addBit (column : Nat) (c : Circuit) (h : BitHeap) : BitHeap :=
  let col := h.columns.getD column (Column.empty)
  if col.contains c then
    let h := h.removeBit column c
    addBit (column + 1) c h
  else
    ⟨h.columns.insert column (col.insert c)⟩

def halfAdder (column : Nat) (i j : Circuit) (h : BitHeap) : AdderResult :=
  let h := h.removeBit column i
  let h := h.removeBit column j
  let sum := Circuit.binop .xor i j
  let carry := Circuit.binop .and i j
  let h := h.addBit column sum
  let h := h.addBit (column + 1) carry
  ⟨h, sum, carry⟩

def fullAdder (column : Nat) (i j k : Circuit) (h : BitHeap) : AdderResult :=
  let h := h.removeBit column i
  let h := h.removeBit column j
  let h := h.removeBit column k
  let sum := Circuit.binop .xor (Circuit.binop .xor i j) k
  let carry := Circuit.atLeastTwo i j k
  let h := h.addBit column sum
  let h := h.addBit (column + 1) carry
  ⟨h, sum, carry⟩

@[simp]
theorem eval_heap_addBit (column : Nat) (c : Circuit) (h : BitHeap) (env : BitEnv) :
    (h.addBit column c).eval env = h.eval env +  2^column  * (c.eval env).toInt := by
  simp [BitHeap.eval, BitHeap.addBit]
  by_cases h : (h.columns.getD column (Column.empty)).contains c
  <;> sorry

@[simp]
theorem eval_heap_removeBit (column : Nat) (c : Circuit) (h : BitHeap) (env : BitEnv) :
  (h.removeBit column c).eval env = h.eval env - 2^(column) * (c.eval env).toInt := by
  simp [BitHeap.eval, BitHeap.removeBit]
  sorry

@[simp]
theorem toNat_and (a b : Bool) :
  (a && b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b <;> simp

theorem halfAdder_correct (column : Nat) (i j : Circuit) (h : BitHeap) :
  ∀ (env : BitEnv), (h.halfAdder column i j).heap.eval env = h.eval env := by
  intros env
  simp [halfAdder]
  generalize hvi : i.eval env = vi
  generalize hvj : j.eval env = vj
  rcases vi <;> rcases vj <;> grind

theorem fullAdder_correct (column : Nat) (i j k : Circuit) (h : BitHeap) :
  ∀ (env : BitEnv), (h.fullAdder column i j k).heap.eval env = h.eval env := by
  intros env
  simp [fullAdder]
  generalize hvi : i.eval env = vi
  generalize hvj : j.eval env = vj
  generalize hvk : k.eval env = vk
  rcases vi <;> rcases vj <;> rcases vk <;> grind

end BitHeap
