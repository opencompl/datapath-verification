import Std.Data.HashMap
import Std.Data.HashSet

inductive Binop
| xor | or | and | nand
deriving Repr, DecidableEq, Inhabited, Hashable

/-- A circuit that describes a logical operation.-/
inductive Circuit
| bit (varIndex : Nat)
| binop (op : Binop) ( a b : Circuit)
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

def Circuit.atLeastTwo (a b c : Circuit) : Circuit := sorry

/--
A bit heap, indexed by the number of bits in the heap.
-/
structure BitHeap where
  -- columns : Std.HashMap Nat (Array Circuit)
  columns : List (List Circuit)

deriving Repr, Inhabited

def evalColumn (col : List Circuit) (env : BitEnv) : Nat :=
  (col.map (fun (c : Circuit) => (c.eval env).toNat)).sum


/--
Evaluate a bit-heap, to compute the final sum of all the bits in the heap.
-/
def BitHeap.eval (h : BitHeap) (env : BitEnv) : Int :=
  (h.columns.zipIdx.map (fun (col, w) => w * evalColumn col env)).sum

/-
An index into a bit-heap, to point at particular bits to create new operations.
-/
structure BitHeap.Index where
  column : Nat
  index : Nat

/-- Get an element from the bit heap. -/
def BitHeap.get (h : BitHeap) (i : Index) : Circuit :=
  h.columns[i.column]![i.index]!

namespace BitHeap

def BitHeap.empty : BitHeap := ⟨[]⟩

/--
Add a bit into the bit heap, returning a new bit heap, and an index to the added bit.
-/
def addBit (h : BitHeap) (c : Circuit) (w : Nat) : BitHeap × Index :=
  sorry

def removeBit (h : BitHeap) (i : Index) : BitHeap :=
  sorry


def exampleHeapWithOneVariable : BitHeap :=
  let c := Circuit.bit 0 -- x0
  let h := BitHeap.empty
  let (h, idx) := h.addBit c 1
  h

structure HalfAdderResult where
  heap : BitHeap
  sumIndex : Index
  carryIndex : Index

def halfAdder (h : BitHeap) (i j : Index) (hij : i.column = j.column) : HalfAdderResult :=
  let bi := h.get i
  let bj := h.get j
  let h := h.removeBit i
  let h := h.removeBit j
  let sum := Circuit.binop .xor bi bj -- Circuit.atLeastTwo bi bj (Circuit.const false)
  let carry := Circuit.binop .and bi bj
  let (h, sumIndex) := h.addBit sum i.column
  let (h, carryIndex) := h.addBit carry (i.column + 1)
  ⟨h, sumIndex, carryIndex⟩

@[simp]
theorem eval_heap_addBit (h : BitHeap) (c : Circuit) (w : Nat) (env : BitEnv) :
    (h.addBit c w).fst.eval env = h.eval env +  2^w  * (c.eval env).toInt :=  by
  sorry

@[simp]
theorem eval_heap_removeBit (h : BitHeap) (i : Index) (env : BitEnv) :
  (h.removeBit i).eval env = h.eval env - 2^(i.column) * ((h.get i).eval env).toInt := sorry

@[simp]
theorem get_removeBit_of_ne (h : BitHeap) (i j : Index) (hijne : i ≠ j) :
  (h.removeBit i).get j = h.get j := sorry

@[simp]
theorem Circuit.const_false_eval_eq :
  (Circuit.const false).eval env = false := by simp [Circuit.eval]

@[simp]
theorem Circuit.atLeastTwo_eval_eq (a b c : Circuit) (env : BitEnv) :
  (Circuit.atLeastTwo a b c).eval env =
  ((a.eval env) && (b.eval env) || (a.eval env) && (c.eval env) || (b.eval env) && (c.eval env)) := sorry

@[simp]
theorem Circuit.eval_and (a b : Circuit) (env : BitEnv) :
    (Circuit.binop .and a b).eval env = ((a.eval env) && (b.eval env)) := by
  simp [Circuit.eval]

@[simp]
theorem Circuit.eval_xor (a b : Circuit) (env : BitEnv) :
    (Circuit.binop .xor a b).eval env = ((a.eval env) != (b.eval env)) := by
  simp [Circuit.eval]


@[simp]
theorem toNat_and (a b : Bool) :
  (a && b).toNat = a.toNat * b.toNat := by
  cases a <;> cases b <;> simp

@[simp]
theorem Int.pow_succ (a : Int) (b : Nat) : a ^ (b + 1) = a ^ b * a := by
  grind only

theorem halfAdder_correct (h : BitHeap) (i j : Index)
  (hij : i.column = j.column) (hijne : i ≠ j) :
  ∀ (env : BitEnv), (h.halfAdder i j hij).heap.eval env = h.eval env := by
  intros env
  simp [halfAdder, hijne]
  generalize hvi : (h.get i).eval env = vi
  generalize hvj : (h.get j).eval env = vj
  rcases vi <;> rcases vj
  · simp
  · simp_all
  · simp_all
  · simp_all; grind only



end BitHeap
