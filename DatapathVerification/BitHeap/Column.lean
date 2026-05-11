import DatapathVerification.BitHeap.Circuit

namespace BitHeap

open Circuit

/--
A bit heap, indexed by the number of bits in the heap.
-/
structure Column where
  elems : List Circuit
deriving Inhabited, Repr

namespace Column

def empty : Column := ⟨[]⟩

def insert (col : Column) (c : Circuit): Column × Nat :=
  let newIndex := col.elems.length
  let col := ⟨c :: col.elems⟩
  (col, newIndex)

def eval (col : Column) (env : BitEnv) : Nat :=
  (col.elems.map (fun (c : Circuit) => (c.eval env).toNat)).sum

def getD (col : Column) (i : Nat) (default : Circuit) : Circuit :=
  col.elems.getD i default

end Column

end BitHeap
