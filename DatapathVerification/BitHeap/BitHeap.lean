import Std.Data.HashSet
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.Column
import Mathlib.Tactic.SplitIfs
import Mathlib.Algebra.Divisibility.Basic

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

/--
Horner's method to compute the weighted sum
-/
def HornersMethod (env : BitEnv) : List Column → Nat
  | [] => 0
  | c :: rest => (c.eval env) + 2 * HornersMethod env rest

/--
Evaluate a bit-heap, to compute the final sum of all the bits in the heap.
-/
def eval (h : BitHeap w) (env : BitEnv) : Nat :=
  HornersMethod env h.columns.toList
  -- h.columns.toList.zipIdx.foldl (fun acc (col, idx) => acc + 2^idx * col.eval env) 0

/--
Evaluate a bit-heap modulo 2^width, to compute the final sum of all the bits in the heap.
-/
def evalMod (h : BitHeap w) (env : BitEnv) : Int :=
  h.eval env % 2^(w)

def get (h : BitHeap w) (column : Nat) : Column :=
  h.columns.getD column (Column.empty)

-- if index is in bounds, getD returns the value
theorem getD_in_bounds (h : BitHeap w) (column : Nat) (h1 : column < w) :
    h.get column = h.columns[column] := by
  simp [get, Vector.getD]
  rw [Vector.getElem_eq_getElem?_get, Vector.getD_getElem?]
  simp [h1]

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
  if h_bounds : column >= w then h else
  have h1 : column < w := by omega
  let col := h.get column
    if !col.contains c then
      ⟨h.columns.set column (col.insert c) h1⟩
      else addBit (column + 1) c (h.removeBit column c)

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
  (h.removeBit column c).evalMod env = (h.evalMod env - 2^(column) * (c.eval env).toInt) % 2^(w) := by
  unfold evalMod
  simp [eval, removeBit]
  have : (h.get column |>.erase c).eval env = (h.get column).eval env - 2 ^ column * (c.eval env).toInt := by
    sorry
  -- have : (h.columns.modify column fun col => col.erase c)  = h.columns - 2 ^ column * (c.eval env).toInt := by sorry
  sorry

-- Basically eval_insertColumn_eq_eval_add, but for HornersMethod. Adding a new column to a list is equivalent
-- to adding the new column's evaluation to the old evaluation, and subtracting the old column's evaluation.
theorem hornersMethod_set (env : BitEnv) (l : List Column) (k : Nat) (v : Column) (hk : k < l.length) :
    (HornersMethod env (l.set k v) : Int)
      = HornersMethod env l + 2^k * (v.eval env : Int) - 2^k * ((l[k]'hk).eval env : Int) := by
  induction l generalizing k with
  | nil =>
    simp at hk
  | cons c cs ih =>
    cases k with
    | zero =>
      simp [HornersMethod, List.set]
      grind
    | succ j =>
      simp [HornersMethod]
      grind

@[grind => ]
theorem eval_insertColumn_eq_eval_add (h : BitHeap w) (k : Nat) (v : Column) (env : BitEnv) (h1 : k < w) :
    ({ columns := h.columns.set k v h1 } : BitHeap w).eval env
      = h.eval env + 2 ^ k * (v.eval env : Int) - 2 ^ k * ((h.get k).eval env : Int) := by
  simp only [BitHeap.eval, Vector.toList_set]
  rw [hornersMethod_set env h.columns.toList k v (by simpa using h1)]
  simp only [Vector.getElem_toList, Int.sub_right_inj]
  rw [getD_in_bounds h k h1]

@[grind => ]
theorem eval_eraseColumn_eq_eval_sub (h : BitHeap w) (k : Nat) (env : BitEnv) (h1 : k < w) :
    ({ columns := h.columns.set k (Column.empty) h1} : BitHeap w).eval env
      = h.eval env - 2 ^ k * ((h.get k).eval env : Int) := by
  simp only [BitHeap.eval, Vector.toList_set]
  rw [hornersMethod_set env h.columns.toList k (Column.empty) (by simpa using h1)]
  simp only [empty_eval_zero, Int.cast_ofNat_Int, Int.mul_zero, Int.add_zero, Vector.getElem_toList,
    Int.sub_right_inj]
  rw [getD_in_bounds h k h1]

theorem eval_insertColumn (h : BitHeap w) (k : Nat) (col : Column) (env : BitEnv) (h1 : k < w) :
    ({ columns := h.columns.set k col h1 } : BitHeap w).eval env
      = ({ columns := h.columns.set k (Column.empty) h1} : BitHeap w).eval env + 2 ^ k * (col.eval env : Nat) := by
  have := eval_insertColumn_eq_eval_add h k col env h1
  have := eval_eraseColumn_eq_eval_sub h k env h1
  grind only

theorem eval_eraseColumn (h : BitHeap w) (k : Nat) (env : BitEnv) (h1 : k < w) :
    h.eval env
      = ({ columns := h.columns.set k (Column.empty) h1} : BitHeap w).eval env + 2 ^ k * ((h.get k).eval env : Nat) := by
  have := eval_eraseColumn_eq_eval_sub h k env h1
  grind

@[simp]
theorem evalMod_heap_addBit (column : Nat) (c : Circuit) (h : BitHeap w) (env : BitEnv) :
    (h.addBit column c).evalMod env = (h.evalMod env +  2^column  * (c.eval env).toInt) % 2^(w) := by
  fun_induction addBit with
  | case1 col h h1 =>
    simp [evalMod]
    have h3 : 2 ^ col * (c.eval env).toInt % 2 ^ w = 0 := by
      generalize hvi : c.eval env = vi
      rcases vi
      · simp
      · simp only [Bool.toInt_true]
        rw [Int.mul_one]
        apply Int.emod_eq_zero_of_dvd
        have : (2:Nat)^w ∣ (2:Nat)^col := Nat.pow_dvd_pow 2 h1
        exact Int.natAbs_dvd_natAbs.mp this
    simp [Int.add_emod, h3]
  | case2 column h h4 h3 col h1 =>
    simp only [evalMod, Int.emod_add_emod]
    have : ({ columns := h.columns.set column (col.insert c) h3 } : BitHeap w).eval env = (h.eval env + 2 ^ column * (c.eval env).toInt) := by
      rw [eval_insertColumn]
      rw [eval_eraseColumn h column env h3]
      rw [Column.eval_insert]
      · push_cast
        cases c.eval env <;> simp <;> grind
      · simp_all
    rw [this]
  | case3 col h h4 h3 h2 h1 ih =>
    rw [ih]
    rw [evalMod_heap_removeBit]
    have : (- 2 ^ col * (c.eval env).toInt + 2 ^ (col + 1) * (c.eval env).toInt) = 2 ^ col * (c.eval env).toInt := by grind
    rw [← this]
    simp_all -- this looks very ugly
    grind
    simp_all
    grind

theorem get_removeBit_self (column : Nat) (c : Circuit) (h : BitHeap w) (hb : column < w) :
    (removeBit column c h).get column = (h.get column).erase c := by
  simp only [removeBit]
  rw [getD_in_bounds] <;> grind

@[simp]
theorem get_removeBit_of_ne (column : Nat) (h : BitHeap w) (i j : Circuit)
  (h1 : i ∈ h.get column) (hne : i ≠ j) : i ∈ (removeBit column j h).get column := by
  by_cases hb : column < w
  · rw [get_removeBit_self _ _ _ hb]
    exact (erase_eq_erase (h.get column) h1 (id (Ne.symm hne))).mpr h1
  · have hr : removeBit column j h = h := by
      simp only [removeBit]
      rw [Vector.setIfInBounds_eq_of_size_le]
      grind
    rw [hr]
    exact h1

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

theorem halfAdder_correct_mod (column : Nat) (i j : Circuit) (h : BitHeap w)
  (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (hne : i ≠ j) :
  ∀ (env : BitEnv), (h.halfAdder column i j).heap.evalMod env = h.evalMod env := by
  intros env
  have h3 := get_removeBit_of_ne column h j i h2 hne.symm
  simp [halfAdder, evalMod_heap_addBit]
  simp only [evalMod_heap_removeBit, h1, h3]
  simp [evalMod]
  generalize hvi : i.eval env = vi
  generalize hvj : j.eval env = vj
  rcases vi <;> rcases vj <;> simp_all
  grind

theorem fullAdder_correct_mod (column : Nat) (i j k : Circuit) (h : BitHeap w)
  (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (h3 : k ∈ h.get column) (hne : i ≠ j) (hne2 : i ≠ k) (hne3 : j ≠ k) :
  ∀ (env : BitEnv), (h.fullAdder column i j k).heap.evalMod env = h.evalMod env := by
  intros env
  have h4 := get_removeBit_of_ne column h j i h2 hne.symm
  have h5 := get_removeBit_of_ne column (removeBit column i h) k
  have h6 := h5 j (get_removeBit_of_ne column h k i h3 hne2.symm) hne3.symm
  simp [fullAdder, evalMod_heap_addBit]
  simp only [evalMod_heap_removeBit, h1, h4, h6]
  simp [evalMod]
  generalize hvi : i.eval env = vi
  generalize hvj : j.eval env = vj
  generalize hvk : k.eval env = vk
  rw [Int.add_emod]
  rcases vi <;> rcases vj <;> rcases vk <;> simp_all <;> grind

end BitHeap
