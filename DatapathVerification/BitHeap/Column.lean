import Std.Data.HashSet
import DatapathVerification.BitHeap.Circuit

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

def toList (col : Column) : List Circuit :=
  col.elems.toList

theorem erase_eq_erase (col : Column) (he : d ∈ col) (hne : c ≠ d) : d ∈ col.erase c ↔ d ∈ col := by
  simp_all [erase, contains]

@[simp]
theorem eval_erase (col : Column) (c : Circuit) (env : BitEnv) (h : c ∈ col) :
    (col.erase c).eval env = col.eval env - (c.eval env).toInt := by
  simp [eval, erase]
  sorry

@[simp]
theorem eval_insert (col : Column) (c : Circuit) (env : BitEnv) (h : c ∉ col) :
    (col.insert c).eval env = col.eval env + (c.eval env).toInt := by
  simp [eval, insert]
  sorry

end Column

end BitHeap
