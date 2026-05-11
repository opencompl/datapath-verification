import Std.Data.HashSet
import DatapathVerification.BitHeap.Circuit

namespace BitHeap

open Circuit

/--
A column of a bit heap.
-/
structure Column where
  elems : Std.HashSet Circuit
deriving Inhabited, Repr

namespace Column

def empty : Column := ⟨Std.HashSet.emptyWithCapacity 0⟩

def insert (col : Column) (c : Circuit) : Column :=
  let col := ⟨col.elems.insert c⟩
  col

def contains (col : Column) (c : Circuit) : Bool :=
  col.elems.contains c

def eval (col : Column) (env : BitEnv) : Nat :=
  (col.elems.fold (init := 0) (fun acc (c : Circuit) => acc + (c.eval env).toNat))

end Column

end BitHeap
