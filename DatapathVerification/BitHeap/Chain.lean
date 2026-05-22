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
    Applying the chain preserves the heap's value under all evaluation environments -/
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

/-- Check if a single step of the chain is applicable -/
def isApplicable (step: Adder) (h : BitHeap) : Bool :=
  match step with
    | .halfAdder col i j =>
      let column := h.get col
      column.contains i && column.contains j && i != j
    | .fullAdder col i j k =>
      let column := h.get col
      column.contains i && column.contains j && column.contains k && i != j && i != k && j != k

/-- Apply a chain of adders if they are applicable, otherwise return none -/
def applyChainSafe (steps : List Adder) (h : BitHeap) : Option BitHeap :=
  match steps with
  | [] => some h
  | s :: rest =>
    if isApplicable s h then
      applyChainSafe rest (applyAdder s h)
    else
      none

/-- If a chain of adders is applicable (it does not return none), then it preserves the heap's value -/
theorem applyChainSafe_correct (steps : List Adder) (h h' : BitHeap) (env : BitEnv)
    (heq : applyChainSafe steps h = some h') :
    h'.eval env = h.eval env := by
  induction steps generalizing h with
  | nil =>
    simp [applyChainSafe] at heq
    rw [heq]
  | cons s rest ih =>
    simp [applyChainSafe] at heq
    obtain ⟨hleft, hright⟩ := heq
    have ih_applied := ih (applyAdder s h) hright
    rw [ih_applied]
    simp_all [applyAdder, isApplicable]
    cases s with
      simp at hleft
    | halfAdder =>
      obtain ⟨⟨i_in_col, j_in_col⟩, not_eq⟩ := hleft
      rw [halfAdder_correct _ _ _ _ i_in_col j_in_col not_eq]
    | fullAdder =>
      obtain ⟨⟨⟨⟨⟨hi, hj⟩, hk⟩, hij⟩, hik⟩, hjk⟩ := hleft
      exact fullAdder_correct _ _ _ _ _ hi hj hk hij hik hjk env

end Chain

end BitHeap
