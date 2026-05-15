import DatapathVerification.BitHeap.BitHeap

namespace BitHeap

open Circuit

namespace Chain

inductive Adder where
| halfAdder (column : Nat) (a b : Circuit)
| fullAdder (column : Nat) (a b c : Circuit)

def applyAdder (adder : Adder) (h : BitHeap) : BitHeap :=
  match adder with
  | .halfAdder column i j => (h.halfAdder column i j).heap
  | .fullAdder column i j k => (h.fullAdder column i j k).heap

theorem applyAdder_halfAdder_correct (column : Nat) (i j : Circuit) (h : BitHeap)
    (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (hne : i ≠ j) :
    ∀ (env : BitEnv), (applyAdder (.halfAdder column i j) h).eval env = h.eval env := by
    intros env
    simp [applyAdder]
    exact halfAdder_correct column i j h h1 h2 hne env

theorem applyAdder_fullAdder_correct (column : Nat) (i j k : Circuit) (h : BitHeap)
    (h1 : i ∈ h.get column) (h2 : j ∈ h.get column) (h3 : k ∈ h.get column) (hne : i ≠ j) (hne2 : i ≠ k) (hne3 : j ≠ k) :
    ∀ (env : BitEnv), (applyAdder (.fullAdder column i j k) h).eval env = h.eval env := by
    intros env
    simp [applyAdder]
    exact fullAdder_correct column i j k h h1 h2 h3 hne hne2 hne3 env

def applyChain (adders : List Adder) (h : BitHeap) : BitHeap :=
  match adders with
  | [] => h
  | s :: rest => applyChain rest (applyAdder s h)

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

theorem applyChain_correct (steps : List Adder) (h : BitHeap) (env : BitEnv)
  (hwf : ChainPreconditions steps h) :
  (applyChain steps h).eval env = h.eval env := by
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
