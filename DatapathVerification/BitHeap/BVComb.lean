import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.Compressors.DaddaTree
import DatapathVerification.BitHeap.Compressors.NaiveCompression


open BitHeap
namespace Comb

inductive ArithBinopKind
| add
| mul

-- inductive ArithUnopKind
-- | neg

-- inductive BooleanBinopKind
-- | and | or | xor

inductive ArithCircuit : Nat → Type
  | var (varIndex : Nat) : ArithCircuit w
  | add (args : List (ArithCircuit w)) : ArithCircuit w
  | mul (l r : ArithCircuit w) : ArithCircuit w
  -- | arithunop (kind : ArithUnopKind) (width : Nat) (arg : ArithCircuit)
  -- | bvbinop (kind : BooleanBinopKind) (width : Nat) (l r : ArithCircuit)

def BitVecEnv (w : Nat) := Nat → BitVec w

def BitVecEnv.toBitEnv (bv : BitVecEnv w) : Circuit.BitEnv :=
  fun n => (bv (n / w)).getLsbD (n % w)

/--
Convert a bitheap into a new bitheap that has a single row,
by using the naive compression algorithm.
-/
def BitHeap.toSingleRow (bh : BitHeap w) : CircuitVector :=
    let (pp1, _) := NaiveCompression.naiveCompression bh
    pp1.columns.toArray.map fun col => col.elems.toList.headD (.const false)

namespace ArithCircuit

/--
Given a bitvector (x : BV 3), build a bitheap
```
*   *  *
x2 x1 x0
```
-/
def bitheapOfVar (varIndex : Nat) : BitHeap w :=
  -- | We need to know that this index is unique which is a gigantic pain.
  List.range w |>.foldl (fun bh i => bh.addBit i (BitHeap.Circuit.bit (varIndex * w + i))) (BitHeap.empty w)

def toBitHeap : ArithCircuit w → BitHeap w
  | .var varIndex => bitheapOfVar varIndex
  | .add args => BitHeap.addBitHeap (args.map toBitHeap)
  | .mul l r => BitHeap.truncate ((toBitHeap l).mulBitHeap (toBitHeap r)) w (by omega)

def denote (ρ : BitVecEnv w) : ArithCircuit w → BitVec w
  | .var i => ρ i
  | .add args => (args.map (denote ρ)).foldl (· + ·) 0
  | .mul l r => denote ρ l * denote ρ r

def toCircuitVector (c : ArithCircuit w) : CircuitVector :=
  let bh := c.toBitHeap
  BitHeap.toSingleRow bh

theorem BitVecEnv.toBitEnv_apply (bv : BitVecEnv w) (i k : Nat) (hk : k < w) :
    bv.toBitEnv (i * w + k) = (bv i).getLsbD k := by
  simp [BitVecEnv.toBitEnv]
  have h1 : (i * w + k) / w = i := by
    have hw : 0 < w := by grind
    rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.add_eq_left, Nat.div_eq_of_lt hk]
  have h2 : k % w = k := by
    exact Nat.mod_eq_of_lt hk
  simp [h1, h2]

theorem bitheapOfVar_go (i : Nat) (bv : BitVecEnv w) (k : Nat) (hk : k ≤ w) :
    ((List.range k).foldl
        (fun bh j => bh.addBit j (.bit (i * w + j)))
        (BitHeap.empty w)).eval bv.toBitEnv
      = (bv i).toNat % 2 ^ k := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, empty_eval, pow_zero]
    grind
  | succ m ih =>
    rw [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    sorry


theorem toBitHeap_correct (c : ArithCircuit w) (bv : BitVecEnv w) :
    c.toBitHeap.evalMod bv.toBitEnv = ((c.denote bv).toNat : Int):= by
  fun_induction toBitHeap with
  | case1 varIndex =>
    simp only [BitHeap.evalMod, bitheapOfVar]
    rw [bitheapOfVar_go varIndex bv w (le_refl w)]
    simp [denote]
    norm_cast
    rw [BitVec.toNat_mod_cancel]
  | case2 =>
    sorry
  | case3 =>
    sorry

end ArithCircuit

end Comb
