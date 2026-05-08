import Std.Data.HashMap
import Std.Data.HashSet

inductive Binop
| xor | or | and | nand
deriving Repr, DecidableEq, Inhabited, Hashable

/-- A circuit that describes a logical operation.-/
inductive Circuit
| bit (varIndex : Nat)
| binop (op : Binop) (a b : Circuit)
| const (val : Bool)
deriving Repr, DecidableEq, Inhabited, Hashable

/-- The number of variables in a circuit. -/
def Circuit.numVars (c : Circuit) : Nat :=
  match c with
  | .bit varIndex => varIndex + 1
  | .binop _ a b => max a.numVars b.numVars
  | .const _ => 0

/-- An environment assigns a value to each bit, where bits are given by natural number indexes. -/
def BitEnv := Nat → Bool

/-- Evaluate a circuit under a given environment. -/
def Circuit.eval (c : Circuit) (env : BitEnv) : Bool :=
  match c with
  | .bit varIndex => env varIndex
  | .binop op a b =>
    let aval := a.eval env
    let bval := b.eval env
    match op with
    | .xor => aval != bval
    | .or => aval || bval
    | .and => aval && bval
    | .nand => !(aval && bval)
  | .const val => val

def Circuit.atLeastTwo (a b c : Circuit) : Circuit :=
  Circuit.binop .or (Circuit.binop .or (Circuit.binop .and a b) (Circuit.binop .and a c)) (Circuit.binop .and b c)

/--
A bit heap, indexed by the number of bits in the heap.
-/
structure Column where
  elems : List Circuit
deriving Inhabited, Repr

instance [BEq α] [Hashable α] [Repr α] [Repr β] : Repr (Std.HashMap α β) where
  reprPrec m _ := repr m.toList

structure BitHeap where
  columns : Std.HashMap Nat Column
deriving Inhabited, Repr

def evalColumn (col : List Circuit) (env : BitEnv) : Nat :=
  (col.map (fun (c : Circuit) => (c.eval env).toNat)).sum

/--
Evaluate a bit-heap, to compute the final sum of all the bits in the heap.
-/
def BitHeap.eval (h : BitHeap) (env : BitEnv) : Int :=
  (h.columns.fold (init := 0) (fun acc w col => acc + (2 ^ w) * evalColumn col.elems env))

/-
An index into a bit-heap, to point at particular bits to create new operations.
-/
structure BitHeap.Index where
  column : Nat
  index : Nat

/-- Get an element from the bit heap. -/
def BitHeap.get (h : BitHeap) (i : Index) : Circuit :=
  (h.columns.get! i.column).elems[i.index]!

namespace BitHeap

-- def BitHeap.empty : BitHeap := ⟨[]⟩
def BitHeap.empty : BitHeap := ⟨Std.HashMap.emptyWithCapacity 0⟩

/--
Add a bit into the bit heap, returning a new bit heap, and an index to the added bit.
-/
def addBit (h : BitHeap) (c : Circuit) (w : Nat) : BitHeap × Index :=
  let columns := h.columns
  let col := (columns.getD w ⟨[]⟩).elems
  let newCol := col ++ [c]
  ⟨⟨h.columns.insert w ⟨newCol⟩⟩, ⟨w, col.length⟩⟩

def removeBit (h : BitHeap) (i : Index) : BitHeap :=
  let columns := h.columns
  let col := columns[i.column]! -- panic if index does not exist
  let newCol := col.elems.eraseIdx i.index
  let newColumns := columns.insert i.column ⟨newCol⟩
  ⟨newColumns⟩

def addBitsExample : BitHeap :=
  let h := BitHeap.empty
  let (h, _) := h.addBit (Circuit.bit 0) 0 -- add a bit in column 0
  let (h, _) := h.addBit (Circuit.bit 1) 1 -- add a bit in column 1
  let (h, _) := h.addBit (Circuit.bit 1) 1 -- add another bit in column 1
  let h := h.removeBit (Index.mk 0 0) -- remove the bit in column 0
  h

/--
info: { columns := [(0, { elems := [] }), (1, { elems := [Circuit.bit 1, Circuit.bit 1] })] }
-/
#guard_msgs in
#eval addBitsExample

structure AdderResult where
  heap : BitHeap
  sumIndex : Index
  carryIndex : Index

def halfAdder (h : BitHeap) (i j : Index) (hij : i.column = j.column) : AdderResult :=
  let bi := h.get i
  let bj := h.get j
  let h := h.removeBit i
  let h := h.removeBit j
  let sum := Circuit.binop .xor bi bj -- Circuit.atLeastTwo bi bj (Circuit.const false)
  let carry := Circuit.binop .and bi bj
  let (h, sumIndex) := h.addBit sum i.column
  let (h, carryIndex) := h.addBit carry (i.column + 1)
  ⟨h, sumIndex, carryIndex⟩

def fullAdder (h : BitHeap) (i j k: Index) (hij : i.column = j.column) (hik : i.column = k.column) : AdderResult :=
  let bi := h.get i
  let bj := h.get j
  let bk := h.get k
  let h := h.removeBit i
  let h := h.removeBit j
  let h := h.removeBit k
  let sum := Circuit.binop .xor (Circuit.binop .xor bi bj) bk
  let carry := Circuit.atLeastTwo bi bj bk
  let (h, sumIndex) := h.addBit sum i.column
  let (h, carryIndex) := h.addBit carry (i.column + 1)
  ⟨h, sumIndex, carryIndex⟩

@[simp]
theorem eval_heap_addBit (h : BitHeap) (c : Circuit) (w : Nat) (env : BitEnv) :
    (h.addBit c w).fst.eval env = h.eval env +  2^w  * (c.eval env).toInt := by
  sorry

@[simp]
theorem eval_heap_removeBit (h : BitHeap) (i : Index) (env : BitEnv) :
  (h.removeBit i).eval env = h.eval env - 2^(i.column) * ((h.get i).eval env).toInt := by
  simp [BitHeap.eval, BitHeap.removeBit]
  sorry

@[simp]
theorem get_removeBit_of_ne (h : BitHeap) (i j : Index) (hijne : i ≠ j) :
  (h.removeBit i).get j = h.get j := by sorry

@[simp]
theorem Circuit.const_false_eval_eq :
  (Circuit.const false).eval env = false := by simp [Circuit.eval]

@[simp]
theorem Circuit.eval_and (a b : Circuit) (env : BitEnv) :
    (Circuit.binop .and a b).eval env = ((a.eval env) && (b.eval env)) := by
  simp [Circuit.eval]

@[simp]
theorem Circuit.eval_xor (a b : Circuit) (env : BitEnv) :
    (Circuit.binop .xor a b).eval env = ((a.eval env) != (b.eval env)) := by
  simp [Circuit.eval]

@[simp]
theorem Circuit.eval_atLeastTwo (a b c : Circuit) (env : BitEnv) :
  (Circuit.atLeastTwo a b c).eval env = ((a.eval env) && (b.eval env) || (a.eval env) && (c.eval env) || (b.eval env) && (c.eval env)) := by
  simp [Circuit.eval, Circuit.atLeastTwo]

@[simp]
theorem toNat_and (a b : Bool) :
  (a && b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b <;> simp

theorem halfAdder_correct (h : BitHeap) (i j : Index)
  (hij : i.column = j.column) (hijne : i ≠ j) :
  ∀ (env : BitEnv), (h.halfAdder i j hij).heap.eval env = h.eval env := by
  intros env
  simp [halfAdder, hijne]
  generalize hvi : (h.get i).eval env = vi
  generalize hvj : (h.get j).eval env = vj
  rcases vi <;> rcases vj <;> grind

theorem fullAdder_correct (h : BitHeap) (i j k : Index)
  (hij : i.column = j.column) (hik : i.column = k.column)
  (hijne : i ≠ j) (hikne : i ≠ k) (hjkne : j ≠ k) :
  ∀ (env : BitEnv), (h.fullAdder i j k hij hik).heap.eval env = h.eval env := by
  intros env
  simp [fullAdder, hijne, hikne, hjkne]
  generalize hvi : (h.get i).eval env = vi
  generalize hvj : (h.get j).eval env = vj
  generalize hvk : (h.get k).eval env = vk
  rcases vi <;> rcases vj <;> rcases vk <;> grind

end BitHeap
