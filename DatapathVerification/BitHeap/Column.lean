import Std.Data.HashSet
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.HashSetLemmas

namespace BitHeap

open Circuit

/--
A column of a bit heap.
-/
structure Column where
  elems : Std.HashSet Circuit
deriving Inhabited

instance : ToString Column where
  toString col := toString col.elems.toList

namespace Column

def contains (col : Column) (c : Circuit) : Bool :=
  col.elems.contains c

instance : Membership Circuit Column where
  mem col c := c ∈ col.elems

@[simp]
theorem mem_iff_contains (col : Column) (c : Circuit) : c ∈ col ↔ col.contains c := by
  rfl

def empty : Column := ⟨Std.HashSet.emptyWithCapacity 0⟩

def eval (col : Column) (env : BitEnv) : Nat :=
  (col.elems.fold (init := 0) (fun acc (c : Circuit) => acc + (c.eval env).toNat))

def insert (col : Column) (c : Circuit) : Column :=
  let col := ⟨col.elems.insert c⟩
  col

def erase (col : Column) (c : Circuit) : Column :=
  let col := ⟨col.elems.erase c⟩
  col

def height (col : Column) : Nat :=
  col.elems.size

@[simp]
theorem height_eq_size (col : Column) : col.height = col.elems.size := rfl

@[simp]
theorem empty_eval_zero (col : Column) (env : BitEnv) (h : col = Column.empty) : col.eval env = 0 := by
  simp_all [eval, empty]
  rw [Std.HashSet.fold_eq_foldl_toList]
  simp

def toList (col : Column) : List Circuit :=
  col.elems.toList

theorem erase_eq_erase (col : Column) (he : d ∈ col) (hne : c ≠ d) : d ∈ col.erase c ↔ d ∈ col := by
  simp_all [erase, contains]

theorem foldl_sum (l : List Circuit) (env : BitEnv) (a : Nat) :
  l.foldl (fun acc (c : Circuit) => acc + (c.eval env).toNat) a =
    a + (l.map (fun c => (c.eval env).toNat)).sum := by
  induction l generalizing a with
  | nil => simp
  | cons p ps ih =>
    grind

theorem Std.HashSet.erase_toList_perm_filter_toList [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]
  (m : Std.HashSet α) :
    (m.erase d).toList.Perm (m.toList.filter (fun x => (x == d) = false)) := by
  sorry

theorem eval_erase (col : Column) (c : Circuit) (env : BitEnv) (h : c ∈ col) :
    (col.erase c).eval env = col.eval env - (c.eval env).toNat := by
  simp [eval, erase]
  repeat rw [Std.HashSet.fold_eq_foldl_toList, foldl_sum]
  simp only [Nat.zero_add]
  have : col.elems.toList.Perm (c :: (col.elems.erase c).toList) := by
    sorry
  grind

@[simp]
theorem eval_insert (col : Column) (c : Circuit) (env : BitEnv) (h : c ∉ col) :
    (col.insert c).eval env = col.eval env + (c.eval env).toNat := by
  simp [eval, insert]
  repeat rw [Std.HashSet.fold_eq_foldl_toList, foldl_sum]
  simp only [Nat.zero_add]
  have : ((col.elems.insert c).toList).Perm (c :: col.elems.toList) := by
    have key := col.elems.toList_insert_perm (k := c)
    have h' : c ∉ col.elems := by exact h
    rw [if_neg h'] at key
    exact key
  grind

end Column

end BitHeap
