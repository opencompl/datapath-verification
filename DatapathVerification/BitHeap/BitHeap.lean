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

def get (h : BitHeap) (column : Nat) : Column :=
  h.columns.getD column (Column.empty)

instance : Membership Circuit BitHeap where
  mem h c :=
    ∃ (col : Nat), c ∈ h.get col

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
  sorry

@[simp]
theorem eval_heap_removeBit (column : Nat) (c : Circuit) (h : BitHeap) (env : BitEnv) (h1 : c ∈ h.get column) :
  (h.removeBit column c).eval env = h.eval env - 2^(column) * (c.eval env).toInt := by
  simp [BitHeap.eval, BitHeap.removeBit]
  sorry

@[simp]
theorem get_removeBit_of_ne (column : Nat) (h : BitHeap) (i j : Circuit)
  (h1 : i ∈ h.get column) (hne : i ≠ j) :
  i ∈ (removeBit column j h).get column := by
  sorry

@[simp]
theorem toNat_and (a b : Bool) :
  (a && b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b <;> simp

theorem halfAdder_correct (column : Nat) (i j : Circuit) (h : BitHeap) (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (hne : i ≠ j):
  ∀ (env : BitEnv), (h.halfAdder column i j).heap.eval env = h.eval env := by
  intros env
  have h3 := get_removeBit_of_ne column h j i h2 hne.symm
  simp [halfAdder, h1, h3]
  generalize hvi : i.eval env = vi
  generalize hvj : j.eval env = vj
  rcases vi <;> rcases vj <;> grind

theorem fullAdder_correct (column : Nat) (i j k : Circuit) (h : BitHeap)
  (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (h3 : k ∈ h.get column) (hne : i ≠ j) (hne2 : i ≠ k) (hne3 : j ≠ k) :
  ∀ (env : BitEnv), (h.fullAdder column i j k).heap.eval env = h.eval env := by
  intros env
  have h4 := get_removeBit_of_ne column h j i h2 hne.symm
  have h5 := get_removeBit_of_ne column (removeBit column i h) k
  have h6 := h5 j (get_removeBit_of_ne column h k i h3 hne2.symm) hne3.symm
  simp [fullAdder, h1, h4, h6]
  generalize hvi : i.eval env = vi
  generalize hvj : j.eval env = vj
  generalize hvk : k.eval env = vk
  rcases vi <;> rcases vj <;> rcases vk <;> grind

end BitHeap
