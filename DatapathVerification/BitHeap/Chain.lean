import DatapathVerification.BitHeap.BitHeap

namespace BitHeap

open Circuit

namespace Chain

/-- A single step in the chain, either a half adder or a full adder -/
inductive Adder where
| halfAdder (column : Nat) (a b : Circuit)
| fullAdder (column : Nat) (a b c : Circuit)

/-- Apply an adder to a bit heap returning the updated heap -/
def applyAdder (adder : Adder) (h : BitHeap) : BitHeap :=
  match adder with
  | .halfAdder column i j => (h.halfAdder column i j).heap
  | .fullAdder column i j k => (h.fullAdder column i j k).heap

/-- Apply a list of adders, from front to the back -/
def applyChain (adders : List Adder) (h : BitHeap) : BitHeap :=
  match adders with
  | [] => h
  | s :: rest => applyChain rest (applyAdder s h)

/-- Preconditions for each step in the chain -/
def ChainPreconditions (steps : List Adder) (h : BitHeap) : Prop :=
  match steps with
  | [] => True
  | s :: rest =>
      (match s with
       | .halfAdder col i j =>
           i ∈ h.get col ∧ j ∈ h.get col ∧ i ≠ j
       | .fullAdder col i j k =>
           i ∈ h.get col ∧ j ∈ h.get col ∧ k ∈ h.get col
             ∧ i ≠ j ∧ i ≠ k ∧ j ≠ k)
      ∧ ChainPreconditions rest (applyAdder s h)

/-- Main correctness theorem for the chain.
    Applying the chain preserves the heap's value under all evaluation environments-/
theorem applyChain_correct (steps : List Adder) (h : BitHeap)
  (hwf : ChainPreconditions steps h) :
  ∀ (env : BitEnv), (applyChain steps h).eval env = h.eval env := by
  intros env
  induction steps generalizing h with
  | nil => rfl
  | cons s rest ih =>
    simp [applyChain]
    simp [ChainPreconditions] at hwf
    rw [ih]
    cases s with
    | halfAdder =>
      simp [applyAdder, halfAdder_correct, hwf]
    | fullAdder =>
      simp [applyAdder, fullAdder_correct, hwf]
    grind

end Chain

end BitHeap
