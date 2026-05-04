import Blase

/-!
  This file proves the correctness of a carry-save adder (CSA) in Lean 4.
-/

namespace CSA

-- The result of a carry-save adder consists of a partial sum `s` and carry bits `t`.
structure CSAResult (w : ℕ) where
  s : BitVec w
  t : BitVec w

-- The carry-save adder splits the sum into a partial sum `s` and
-- carry bits `t`, such that the original sum is recovered by
-- adding `s` to the carries shifted left by 1 (i.e., t * 2).
@[bv_normalize]
def carrySave (w : ℕ) (a b c : BitVec w) : CSAResult w :=
  let s := a ^^^ b ^^^ c
  let t := (a &&& b ||| a &&& c ||| b &&& c)
  ⟨s, t⟩

/--
info: { s := 0x5#4, t := 0x5#4 }
-/
#guard_msgs in
#eval carrySave 4 5 5 5

-- a + b + c = CSA(a, b, c)
@[bv_normalize]
theorem carrySaveAdder (w : ℕ) (a b c : BitVec w) :
    let ⟨s, t⟩ := carrySave w a b c
    a + b + c = s + t <<< 1 := by
    simp [carrySave]
    bv_automata_classic

-- a + b + c + d = CSA(CSA(a, b, c), d)
theorem carrySaveAdder4Input (w : ℕ) (a b c d : BitVec w) :
    let ⟨s1, t1⟩ := carrySave w a b c
    let ⟨s2, t2⟩ := carrySave w s1 (t1 <<< 1) d
    a + b + c + d = s2 + t2 <<< 1 := by
    simp [carrySave]
    bv_automata_classic

-- CSA(CSA(p1, p2, p3), p4), with p1, p2, p3, p4 being the partial products of a 4-bit multiplication.
def mul4 (a b : BitVec 4) : BitVec 4 :=
  -- partial products
  let p0 : BitVec 4 := (BitVec.ofBool a[0]).zeroExtend 4 * b
  let p1 : BitVec 4 := ((BitVec.ofBool a[1]).zeroExtend 4 * b) <<< 1
  let p2 : BitVec 4 := ((BitVec.ofBool a[2]).zeroExtend 4 * b) <<< 2
  let p3 : BitVec 4 := ((BitVec.ofBool a[3]).zeroExtend 4 * b) <<< 3
  -- sum partial products
  let ⟨s1, t1⟩ := carrySave 4 p0 p1 p2
  let ⟨s2, t2⟩ := carrySave 4 s1 (t1 <<< 1) p3
  s2 + (t2 <<< 1)

/--
info: 12#4
-/
#guard_msgs in
#eval mul4 4 3

-- a*b = (a[0] * b) + (2 * a[1] * b) + (4 * a[2] * b) + (8 * a[3] * b)
@[simp]
theorem mul4_partial_products (a b : BitVec 4) :
    let p0 : BitVec 4 := (BitVec.ofBool a[0]).zeroExtend 4 * b
    let p1 : BitVec 4 := ((BitVec.ofBool a[1]).zeroExtend 4 * b) <<< 1
    let p2 : BitVec 4 := ((BitVec.ofBool a[2]).zeroExtend 4 * b) <<< 2
    let p3 : BitVec 4 := ((BitVec.ofBool a[3]).zeroExtend 4 * b) <<< 3
    a * b = p0 + p1 + p2 + p3 := by
    bv_decide

-- a * b = CSA(CSA(p0, p1, p2), p3)
theorem mul4_correct (a b : BitVec 4) : a * b = mul4 a b := by
  rw [mul4_partial_products]
  simp only [mul4, carrySave]
  bv_decide

-- N:2 compressor implementation.
-- Takes a list of n Bitvectors and reduces them to 2 Bitvectors (sum and carry) using a tree of carry-save adders.
@[bv_normalize]
def chain {w : Nat} (v : List (BitVec w)) : CSAResult w :=
  match v with
  | [] => ⟨0, 0⟩
  | [a] => ⟨a, 0⟩
  | [a,b] => carrySave w a b 0
  | [a,b,c] => carrySave w a b c
  | a :: rest =>
    -- drop the first element; `(n+1) - 1 = n` is definitional, so no cast is needed.
    let ⟨sum, carry⟩ := chain rest
    let ⟨s, t⟩ := carrySave w sum (carry <<< 1) a -- the chained carry is shifted left by 1 to align with the next input.
    ⟨s, t⟩ -- return the carry without shifting, the next level handles it.

/--
info: { s := 0x00a#10, t := 0x005#10 }
-/
#guard_msgs in
#eval chain (v := [5#10, 2#10, 3#10, 7#10, 3#10])

-- Sum all elements of a list of Bitvectors.
def list_sum {w : Nat} (v : List (BitVec w)) : BitVec w :=
  match v with
  | [] => 0
  | a :: rest => (list_sum rest) + a

/--
info: 20#10
-/
#guard_msgs in
#eval list_sum (v := [5#10, 2#10, 3#10, 7#10, 3#10])

/-- Main correctness theorem for N:2 compressor chain.
For a list of Bitvectors, the compressor chain reduces it to a pair (s,t)
such that the sum of all elements in the list equals s + t <<< 1. -/
theorem chain_correct {w : Nat} (v : List (BitVec w)) :
    let ⟨s, t⟩ := chain v
    list_sum v = s + t <<< 1 := by
  induction v with
  | nil =>
    simp [chain, list_sum]
  | cons hd rest ih =>
    match hrest : rest with
    | [] =>
      simp [chain, list_sum]
    | [a] =>
      simp only [chain, list_sum, carrySave]
      clear ih hrest rest
      bv_automata_classic
    | [a, b] =>
      simp only [chain, list_sum, carrySave]
      clear ih hrest rest
      bv_automata_classic
    | a :: b :: c :: rest' =>
      simp only [chain, list_sum, carrySave] at ih ⊢
      simp only [ih]
      clear ih hrest
      bv_automata_classic

/-!
  N:2 compressor implementation with a more optimized structure. Instead of chaining the carry-save adders in a linear fashion,
  we compress the input list in a more balanced way. First we compress the first three elements, then we create a new list with the sum and carry from the first compression, and the remaining elements.
  We then reverse this new list and apply the chain_opt function recursively. This enables applying the carry chain adders to the front and back of the list in parallel.
-/
@[bv_normalize]
def chain_opt {w : Nat} (v : List (BitVec w)) : CSAResult w :=
  match v with
  | [] => ⟨0, 0⟩
  | [a] => ⟨a, 0⟩
  | [a,b] => carrySave w a b 0
  | [a,b,c] => carrySave w a b c
  | a :: b :: c :: rest =>
    let ⟨sum, carry⟩ := carrySave w a b c
    let new_list := sum :: (carry <<< 1) :: rest
    let back := new_list.reverse
    let ⟨sum, carry⟩ := chain_opt back
    ⟨sum, carry⟩
  termination_by v.length
  decreasing_by
    simp

#eval chain_opt (v := [5#10, 2#10, 3#10, 7#10, 3#10])

theorem chain_opt_correct {w : Nat} (v : List (BitVec w)) :
    let ⟨s, t⟩ := chain_opt v
    list_sum v = s + t <<< 1 := by
  induction v with
  | nil =>
    simp [chain_opt, list_sum]
  | cons hd rest ih =>
    match hrest : rest with
    | [] =>
      simp [chain_opt, list_sum]
    | [a] =>
      simp only [chain_opt, list_sum, carrySave]
      clear ih hrest rest
      bv_automata_classic
    | [a, b] =>
      simp only [chain_opt, list_sum, carrySave]
      clear ih hrest rest
      bv_automata_classic
    | a :: b :: c :: rest' =>
      simp only [chain_opt, list_sum, carrySave] at ih ⊢
      simp
      unfold chain_opt at ih ⊢
      clear ih hrest
      sorry
      -- bv_automata_classic

-- Recursive partial-products: produces `[p_{n-1}, p_{n-2}, ..., p_0]`
-- where `p_i = (y[i] ? x : 0) <<< i`.
@[bv_normalize]
def partialProducts' {w : Nat} (x y : BitVec w) : Nat → List (BitVec w)
  | 0 => []
  | n + 1 =>
    let cur := if y.getLsbD n then (x <<< n) else 0
    cur :: partialProducts' x y n

@[bv_normalize]
def partialProducts {w : Nat} (x y : BitVec w) : List (BitVec w) :=
  partialProducts' x y w

/--
info: [0#8, 0#8, 0#8, 0#8, 0#8, 0#8, 102#8, 51#8]
-/
#guard_msgs in
#eval partialProducts (51#8) (3#8)

-- Multiplication circuit: build partial products, compress them with the chain of carry-save adders, and sum the results.
@[bv_normalize]
def mulChain {w : Nat} (a b : BitVec w) : BitVec w :=
  let ⟨s, t⟩ := chain (partialProducts a b)
  s + t <<< 1

@[bv_normalize]
def mulChain_opt {w : Nat} (a b : BitVec w) : BitVec w :=
  let ⟨s, t⟩ := chain_opt (partialProducts a b)
  s + t <<< 1
/--
info: 153#8
-/
#guard_msgs in
#eval mulChain (51#8) (3#8)
#eval mulChain_opt (51#8) (3#8)

end CSA
