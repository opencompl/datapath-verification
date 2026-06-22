import Std.Data.HashMap
import Std.Data.HashSet
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.Column

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
Add a bit into the bit heap, returning a new bit heap. If the bit already exists in the column, remove it and add it to the next column.
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

theorem by_pow2_of_zero_eval (h : BitHeap w) (h1 : col ≥ h.width) :
  (2 : Int) ^ h.width ∣ (2 : Int) ^ col := by
  sorry
  -- exact Nat.pow_dvd_pow_iff_le_right'.mpr h1 -> this works for Nat.

@[simp]
theorem eval_heap_addBit (column : Nat) (c : Circuit) (h : BitHeap w) (env : BitEnv) :
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
  | case2 col h h1 h2 ih =>
    sorry
  | case3 col h h1 h2 ih =>
    sorry

@[simp]
theorem eval_heap_removeBit (column : Nat) (c : Circuit) (h : BitHeap w) (env : BitEnv) (h1 : c ∈ h.get column) :
  (h.removeBit column c).eval env = h.eval env - 2^(column) * (c.eval env).toInt := by
  simp [BitHeap.eval, BitHeap.removeBit]
  sorry

@[simp]
theorem get_removeBit_of_ne (column : Nat) (h : BitHeap w) (i j : Circuit)
  (h1 : i ∈ h.get column) (hne : i ≠ j) :
  i ∈ (removeBit column j h).get column := by
  sorry

theorem removeBit_decreases_size (col : Nat) (c : Circuit) (h : BitHeap w) (h1: c ∈ h.get col) :
    ((removeBit col c h).get col).height < (h.get col).height := by
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
theorem toNat_and (a b : Bool) :
  (a && b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b <;> simp

theorem halfAdder_correct (column : Nat) (i j : Circuit) (h : BitHeap w) (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (hne : i ≠ j):
  ∀ (env : BitEnv), (h.halfAdder column i j).heap.eval env = h.eval env := by
  intros env
  have h3 := get_removeBit_of_ne column h j i h2 hne.symm
  simp [halfAdder, h1, h3]
  generalize hvi : i.eval env = vi
  generalize hvj : j.eval env = vj
  rcases vi <;> rcases vj <;> grind

-- TODO: Seems to me we need the termination proof of addBit first
@[simp]
theorem halfAdder_preserves_width (column : Nat) (i j : Circuit) (h : BitHeap w) :
    (h.halfAdder column i j).heap.width = h.width := by
  simp [halfAdder, removeBit]
  sorry

theorem halfAdder_correct_mod (column : Nat) (i j : Circuit) (h : BitHeap w)
  (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (hne : i ≠ j) :
  ∀ (env : BitEnv), (h.halfAdder column i j).heap.evalMod env = h.evalMod env := by
  intros env
  simp [evalMod]
  rw [halfAdder_correct column i j h h1 h2 hne env]

theorem fullAdder_correct (column : Nat) (i j k : Circuit) (h : BitHeap w)
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
theorem fullAdder_preserves_width (column : Nat) (i j k : Circuit) (h : BitHeap w) :
    (h.fullAdder column i j k).heap.width = h.width := by
  simp [fullAdder, removeBit]
  sorry

theorem fullAdder_correct_mod (column : Nat) (i j k : Circuit) (h : BitHeap w)
  (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (h3 : k ∈ h.get column) (hne : i ≠ j) (hne2 : i ≠ k) (hne3 : j ≠ k) :
  ∀ (env : BitEnv), (h.fullAdder column i j k).heap.evalMod env = h.evalMod env := by
  intros env
  simp [evalMod]
  rw [fullAdder_correct column i j k h h1 h2 h3 hne hne2 hne3 env]

end BitHeap
