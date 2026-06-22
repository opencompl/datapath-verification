import Std.Data.HashMap
import Std.Data.HashSet
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.Column
import Mathlib.Tactic.SplitIfs
import Std.Data.HashMap.Lemmas
import Std.Tactic.Do

structure BitHeap (width : Nat) where
  columns : Vector BitHeap.Column width
deriving Inhabited

namespace BitHeap

open Circuit
open Column

instance : ToString (BitHeap w) where
  toString h :=
    let entries := h.columns.toList.zipIdx
    "{" ++ String.intercalate ", " (entries.map (fun (v, k) => s!"{k} ↦ {v}")) ++ "}"

def empty (w : Nat) : BitHeap w := ⟨Vector.replicate w Column.empty⟩

def width (h : BitHeap w) : Nat :=
  h.columns.size
/--
Evaluate a bit-heap, to compute the final sum of all the bits in the heap.
-/
def eval (h : BitHeap w) (env : BitEnv) : Int :=
  h.columns.toList.zipIdx.foldl (fun acc (col, idx) => acc + 2^idx * col.eval env) 0

/--
Evaluate a bit-heap modulo 2^width, to compute the final sum of all the bits in the heap.
-/
def evalMod (h : BitHeap w) (env : BitEnv) : Int :=
  h.eval env % 2^(h.width)

def get (h : BitHeap w) (column : Nat) : Column :=
  h.columns.getD column (Column.empty)

theorem get_eq_getD (h : BitHeap w) (column : Nat) :
    h.get column = (h.columns[column]?).getD Column.empty := by
  simp [get]
  sorry

instance : Membership Circuit (BitHeap w) where
  mem h c :=
    ∃ (col : Nat), c ∈ h.get col

def removeBit (column : Nat) (c : Circuit) (h : BitHeap w) : BitHeap w :=
  ⟨h.columns.setIfInBounds column ((h.get column).erase c)⟩

-- Maximum height across all columns
def maxHeight (h : BitHeap w) : Nat :=
  h.columns.foldl (fun acc col => max acc col.height) 0

-- Highest column of the BitHeap, return none if BitHeap is empty
def highestColumn (h : BitHeap w) : Option Nat :=
  let target := h.maxHeight
  if target == 0 then none else
  h.columns.toList.zipIdx.findSome?
    (fun (col, idx) => if col.height == target then some idx else none)

/--
Add a bit into the bit heap, returning a new bit heap.
If the bit already exists in the column, remove it and add it to the next column.
Stops carrying when the column exceeds the width of the bit heap.
-/
def addBit (column : Nat) (c : Circuit) (h : BitHeap w) : BitHeap w :=
  if h_bounds : column >= h.width then h else
  have h1 : column < h.width := by omega
  let col := h.get column
    if !col.contains c then
      ⟨h.columns.set column (col.insert c) h1⟩
      else  addBit (column + 1) c (h.removeBit column c)
  termination_by h.width - column
  decreasing_by
    have hw : (removeBit column c h).width = h.width := by rfl
    rw [hw]
    omega

@[simp]
theorem removeBit_width (column : Nat) (c : Circuit) (h : BitHeap w) :
    (removeBit column c h).width = h.width := by rfl

@[simp]
theorem addBit_width (column : Nat) (c : Circuit) (h : BitHeap w) :
    (addBit column c h).width = h.width := by
  fun_induction addBit with
  | case1 => rfl
  | case2 => rfl
  | case3 col h h1 h2 h3 h4 ih =>
    rw [ih]
    rw [removeBit_width]

structure AdderResult (w : Nat) where
  heap : BitHeap w
  sum : Circuit
  carry : Circuit

def halfAdder (column : Nat) (i j : Circuit) (h : BitHeap w) : AdderResult w :=
  let h := h.removeBit column i
  let h := h.removeBit column j
  let sum := Circuit.binop .xor i j
  let carry := Circuit.binop .and i j
  let h := h.addBit column sum
  let h := h.addBit (column + 1) carry
  ⟨h, sum, carry⟩

def fullAdder (column : Nat) (i j k : Circuit) (h : BitHeap w) : AdderResult w :=
  let h := h.removeBit column i
  let h := h.removeBit column j
  let h := h.removeBit column k
  let sum := Circuit.binop .xor (Circuit.binop .xor i j) k
  let carry := Circuit.atLeastTwo i j k
  let h := h.addBit column sum
  let h := h.addBit (column + 1) carry
  ⟨h, sum, carry⟩

@[simp]
theorem evalMod_heap_removeBit (column : Nat) (c : Circuit) (h : BitHeap w) (env : BitEnv) (h1 : c ∈ h.get column) :
  (h.removeBit column c).evalMod env = (h.evalMod env - 2^(column) * (c.eval env).toInt) % 2^(h.width) := by
  unfold evalMod
  rw [removeBit_width]
  simp [eval, removeBit]
  have : (h.get column |>.erase c).eval env = (h.get column).eval env - 2 ^ column * (c.eval env).toInt := by
    sorry
  -- have : (h.columns.modify column fun col => col.erase c)  = h.columns - 2 ^ column * (c.eval env).toInt := by sorry
  sorry

theorem by_pow2_of_zero_eval (h : BitHeap w) (h1 : col ≥ h.width) :
  (2 : Int) ^ h.width ∣ (2 : Int) ^ col := by
  sorry
  -- exact Nat.pow_dvd_pow_iff_le_right'.mpr h1 -> this works for Nat.

/--
Relate BitHeap.env to sum of a list. (Nat x Column) comes from Std.HashMap.toList, since it returns (Key x Value) pairs.
-/
theorem foldl_sum (l : List (Nat × Column)) (env : BitEnv) (a : Int) :
  l.foldl (fun acc (p : Nat × Column) => acc + 2 ^ p.1 * (p.2.eval env : Int)) a =
    a + (l.map (fun p => 2 ^ p.1 * (p.2.eval env : Int))).sum := by
  induction l generalizing a with
  | nil => simp
  | cons p ps ih =>
    grind

@[simp]
theorem evalMod_heap_addBit (column : Nat) (c : Circuit) (h : BitHeap w) (env : BitEnv) :
    (h.addBit column c).evalMod env = (h.evalMod env +  2^column  * (c.eval env).toInt) % 2^(h.width) := by
  fun_induction addBit with
  | case1 col h h1 =>
    simp [evalMod]
    have h3 : 2 ^ col * (c.eval env).toInt % 2 ^ h.width = 0 := by
      generalize hvi : c.eval env = vi
      rcases vi
      · simp
      · simp only [Bool.toInt_true]
        rw [Int.mul_one]
        apply Int.emod_eq_zero_of_dvd
        exact_mod_cast by_pow2_of_zero_eval h h1
    simp [Int.add_emod, h3]
  | case2 col h h1 =>
    simp only [evalMod, Int.emod_add_emod]
    sorry
  | case3 _ _ _ h2 h1 ih =>
    sorry

@[simp]
theorem get_removeBit_of_ne (column : Nat) (h : BitHeap w) (i j : Circuit)
  (h1 : i ∈ h.get column) (hne : i ≠ j) :
  i ∈ (removeBit column j h).get column := by
  rw [get_eq_getD] at h1
  rw [get_eq_getD]
  simp only [removeBit]
  rcases hcol : h.columns[column]?
  · simp_all only
    grind
  · sorry

theorem removeBit_decreases_size (col : Nat) (c : Circuit) (h : BitHeap w) (h1: c ∈ h.get col) :
    ((removeBit col c h).get col).height < (h.get col).height := by
  simp only [removeBit, height_eq_size]
  simp [erase]
  sorry

theorem double_removeBit_decreases (col : Nat) (c₁ c₂ : Circuit) (h : BitHeap w)
    (h1 : c₁ ∈ h.get col) (h2 : c₂ ∈ h.get col) (hne : c₁ ≠ c₂) :
  ((removeBit col c₁ (removeBit col c₂ h)).get col).height < (h.get col).height := by
    have h1' : c₁ ∈ (removeBit col c₂ h).get col :=
      get_removeBit_of_ne col h c₁ c₂ h1 hne
    exact Nat.lt_trans
      (removeBit_decreases_size col c₁ (removeBit col c₂ h) h1')
      (removeBit_decreases_size col c₂ h h2)

theorem triple_removeBit_decreases (col : Nat) (c₁ c₂ c₃ : Circuit) (h : BitHeap w)
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
theorem halfAdder_preserves_width (column : Nat) (i j : Circuit) (h : BitHeap w) :
    (h.halfAdder column i j).heap.width = h.width := by
  simp [halfAdder, removeBit]
  sorry

theorem halfAdder_correct_mod (column : Nat) (i j : Circuit) (h : BitHeap w)
  (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (hne : i ≠ j) :
  ∀ (env : BitEnv), (h.halfAdder column i j).heap.evalMod env = h.evalMod env := by
  intros env
  have h3 := get_removeBit_of_ne column h j i h2 hne.symm
  simp [halfAdder, evalMod_heap_addBit, addBit_width, removeBit_width]
  simp only [evalMod_heap_removeBit, h1, h3]
  simp [evalMod]
  generalize hvi : i.eval env = vi
  generalize hvj : j.eval env = vj
  rcases vi <;> rcases vj <;> simp_all
  grind

@[simp]
theorem fullAdder_preserves_width (column : Nat) (i j k : Circuit) (h : BitHeap w) :
    (h.fullAdder column i j k).heap.width = h.width := by
  simp [fullAdder, removeBit]
  sorry

theorem fullAdder_correct_mod (column : Nat) (i j k : Circuit) (h : BitHeap w)
  (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (h3 : k ∈ h.get column) (hne : i ≠ j) (hne2 : i ≠ k) (hne3 : j ≠ k) :
  ∀ (env : BitEnv), (h.fullAdder column i j k).heap.evalMod env = h.evalMod env := by
  intros env
  have h4 := get_removeBit_of_ne column h j i h2 hne.symm
  have h5 := get_removeBit_of_ne column (removeBit column i h) k
  have h6 := h5 j (get_removeBit_of_ne column h k i h3 hne2.symm) hne3.symm
  simp [fullAdder, evalMod_heap_addBit, addBit_width, removeBit_width]
  simp only [evalMod_heap_removeBit, h1, h4, h6]
  simp [evalMod]
  generalize hvi : i.eval env = vi
  generalize hvj : j.eval env = vj
  generalize hvk : k.eval env = vk
  rw [Int.add_emod]
  rcases vi <;> rcases vj <;> rcases vk <;> simp_all <;> grind

end BitHeap
