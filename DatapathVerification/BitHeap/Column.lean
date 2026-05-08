import DatapathVerification.BitHeap.Circuit

open BitHeapCircuit

namespace BitheapColumn
/--
A bit heap, indexed by the number of bits in the heap.
-/
structure Column where
  elems : List Circuit
deriving Inhabited, Repr

def Column.empty : Column := ⟨[]⟩

def Column.insert (col : Column) (c : Circuit): Column × Nat :=
  let newIndex := col.elems.length
  let col := ⟨c :: col.elems⟩
  (col, newIndex)

def Column.eval (col : Column) (env : BitEnv) : Nat :=
  (col.elems.map (fun (c : Circuit) => (c.eval env).toNat)).sum

def Column.getD (col : Column) (i : Nat) (default : Circuit) : Circuit :=
  col.elems.getD i default

end BitheapColumn
