import Std.Data.HashMap
import Std.Data.HashSet
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.Column

open BitHeapCircuit
open BitheapColumn

instance [BEq α] [Hashable α] [Repr α] [Repr β] : Repr (Std.HashMap α β) where
  reprPrec m _ := repr m.toList

structure BitHeap where
  columns : Std.HashMap Nat Column
deriving Inhabited, Repr

/--
Evaluate a bit-heap, to compute the final sum of all the bits in the heap.
-/
def BitHeap.eval (h : BitHeap) (env : BitEnv) : Int :=
  (h.columns.fold (init := 0) (fun acc w col => acc + (2 ^ w) * col.eval env))

/-
An index into a bit-heap, to point at particular bits to create new operations.
-/
structure BitHeap.Index where
  column : Nat
  index : Nat

/-- Get an element from the bit heap. -/
def BitHeap.get (h : BitHeap) (i : Index) : Circuit :=
  match h.columns.get? i.column with
  | none => Circuit.const false
  | some col => (col.getD i.index (Circuit.const false))

namespace BitHeap

def BitHeap.empty : BitHeap := ⟨Std.HashMap.emptyWithCapacity 0⟩

/--
Add a bit into the bit heap, returning a new bit heap, and an index to the added bit.
-/
def addBit (h : BitHeap) (c : Circuit) (w : Nat) : BitHeap × Index :=
  let col := h.columns.getD w (Column.empty)
  let (col, newIndex) := col.insert c
  ⟨⟨h.columns.insert w col⟩, ⟨w, newIndex⟩⟩

def removeBit (h : BitHeap) (i : Index) : BitHeap :=
  ⟨h.columns.modify i.column (fun col => ⟨col.elems.eraseIdx i.index⟩)⟩

def addBitsExample : BitHeap :=
  let h := BitHeap.empty
  let (h, _) := h.addBit (Circuit.bit 0) 0 -- add a bit in column 0
  let (h, _) := h.addBit (Circuit.bit 1) 1 -- add a bit in column 1
  let (h, _) := h.addBit (Circuit.bit 1) 1 -- add another bit in column 1
  let h := h.removeBit (Index.mk 0 0) -- remove the bit in column 0
  h

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
