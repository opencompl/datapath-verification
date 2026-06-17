import Std.Data.HashMap
import Std.Data.HashSet
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.Column
import Std.Tactic.BVDecide

structure BitHeap where
  width : Nat
  columns : Std.HashMap Nat BitHeap.Column
deriving Inhabited

namespace BitHeap

open Circuit
open Column

instance : ToString BitHeap where
  toString h :=
    let entries := h.columns.toList.mergeSort (fun a b => a.1 ≤ b.1)
    "{" ++ String.intercalate ", " (entries.map (fun (k, v) => s!"{k} ↦ {v}")) ++ "}"

def empty : BitHeap := ⟨0, Std.HashMap.emptyWithCapacity 0⟩

/--
Evaluate a bit-heap, to compute the final sum of all the bits in the heap.
-/
def eval (h : BitHeap) (env : BitEnv) : Int :=
  (h.columns.fold (init := 0) (fun acc w col => acc + (2 ^ w) * col.eval env))

/--
Evaluate a bit-heap modulo 2^width, to compute the final sum of all the bits in the heap.
-/
def evalMod (h : BitHeap) (env : BitEnv) : Int :=
  h.eval env % 2^(h.width)

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
  ⟨h.width, h.columns.modify column (fun col => col.erase c)⟩

-- Maximum height across all columns
def maxHeight (h : BitHeap) : Nat :=
  h.columns.fold (init := 0) (fun acc _ col => max acc col.height)

-- Highest column of the BitHeap, return none if BitHeap is empty
def highestColumn (h : BitHeap) : Option Nat :=
  let target := h.maxHeight
  h.columns.toList.findSome? (fun (idx, col) => if col.height == target then some idx else none)

/--
Add a bit into the bit heap, returning a new bit heap. If the bit already exists in the column, remove it and add it to the next column.
-/
partial def addBit (column : Nat) (c : Circuit) (h : BitHeap) : BitHeap :=
  let col := h.columns.getD column (Column.empty)
  if col.contains c then
    let h := h.removeBit column c
    addBit (column + 1) c h
  else
    ⟨h.width, h.columns.insert column (col.insert c)⟩

-- TODO: make this variable size add
def addBitHeap (h1 h2 : BitHeap) : BitHeap :=
  let h : BitHeap := ⟨h1.width, Std.HashMap.emptyWithCapacity 0⟩
  let h := h1.columns.fold (fun acc col column =>
             column.elems.toList.foldl (fun acc' c => acc'.addBit col c) acc) h
  let h := h2.columns.fold (fun acc col column =>
             column.elems.toList.foldl (fun acc' c => acc'.addBit col c) acc) h
  h

def mulBitHeap (h1 h2 : BitHeap) : BitHeap :=
  let newWidth := max h1.width h2.width
  let h : BitHeap := ⟨newWidth, Std.HashMap.emptyWithCapacity 0⟩
  let h := h1.columns.fold (fun acc col1 column1 =>
             h2.columns.fold (fun acc' col2 column2 =>
               column1.elems.toList.foldl (fun acc'' c1 =>
                 column2.elems.toList.foldl (fun acc''' c2 =>
                   acc'''.addBit (col1 + col2) (Circuit.binop .and c1 c2)) acc'') acc') acc) h
  h

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

theorem removeBit_decreases_size (col : Nat) (c : Circuit) (h : BitHeap) (h1: c ∈ h.get col) :
    ((removeBit col c h).get col).height < (h.get col).height := by
    sorry

theorem double_removeBit_decreases (col : Nat) (c₁ c₂ : Circuit) (h : BitHeap)
    (h1 : c₁ ∈ h.get col) (h2 : c₂ ∈ h.get col) (hne : c₁ ≠ c₂) :
  ((removeBit col c₁ (removeBit col c₂ h)).get col).height < (h.get col).height := by
    have h1' : c₁ ∈ (removeBit col c₂ h).get col :=
      get_removeBit_of_ne col h c₁ c₂ h1 hne
    exact Nat.lt_trans
      (removeBit_decreases_size col c₁ (removeBit col c₂ h) h1')
      (removeBit_decreases_size col c₂ h h2)

theorem triple_removeBit_decreases (col : Nat) (c₁ c₂ c₃ : Circuit) (h : BitHeap)
    (h1 : c₁ ∈ h.get col) (h2 : c₂ ∈ h.get col) (h3 : c₃ ∈ h.get col)
    (hne12 : c₁ ≠ c₂) (hne13 : c₁ ≠ c₃) (hne23 : c₂ ≠ c₃) :
  ((removeBit col c₁ (removeBit col c₂ (removeBit col c₃ h))).get col).height < (h.get col).height := by
    have h1' : c₁ ∈ (removeBit col c₃ h).get col :=
      get_removeBit_of_ne col h c₁ c₃ h1 hne13
    have h2' : c₂ ∈ (removeBit col c₃ h).get col :=
      get_removeBit_of_ne col h c₂ c₃ h2 hne23
    exact Nat.lt_trans
      (double_removeBit_decreases col c₁ c₂ (removeBit col c₃ h) h1' h2' hne12)
      (removeBit_decreases_size col c₃ h h3)

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

-- TODO: Seems to me we need the termination proof of addBit first
@[simp]
theorem halfAdder_preserves_width (column : Nat) (i j : Circuit) (h : BitHeap) :
    (h.halfAdder column i j).heap.width = h.width := by
  simp [halfAdder, removeBit]
  sorry

theorem halfAdder_correct_mod (column : Nat) (i j : Circuit) (h : BitHeap)
  (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (hne : i ≠ j) :
  ∀ (env : BitEnv), (h.halfAdder column i j).heap.evalMod env = h.evalMod env := by
  intros env
  simp [evalMod]
  rw [halfAdder_correct column i j h h1 h2 hne env]

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

-- TODO: Seems to me we need the termination proof of addBit first
@[simp]
theorem fullAdder_preserves_width (column : Nat) (i j k : Circuit) (h : BitHeap) :
    (h.fullAdder column i j k).heap.width = h.width := by
  simp [fullAdder, removeBit]
  sorry

theorem fullAdder_correct_mod (column : Nat) (i j k : Circuit) (h : BitHeap)
  (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (h3 : k ∈ h.get column) (hne : i ≠ j) (hne2 : i ≠ k) (hne3 : j ≠ k) :
  ∀ (env : BitEnv), (h.fullAdder column i j k).heap.evalMod env = h.evalMod env := by
  intros env
  simp [evalMod]
  rw [fullAdder_correct column i j k h h1 h2 h3 hne hne2 hne3 env]

end BitHeap
