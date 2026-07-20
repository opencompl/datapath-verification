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

theorem foldl_addBit_evalMod  (idx : Nat) (h : BitHeap w) (cs : List Circuit) :
  (List.foldl (fun a c => addBit idx c a) h cs).evalMod env
    = (h.evalMod env + (cs.map (fun c => 2^idx * (c.eval env).toInt)).sum) % 2^w := by
    induction cs generalizing h with
    | nil =>
      simp [evalMod]
    | cons c tl ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, BitHeap.evalMod_heap_addBit, Int.emod_add_emod]
      grind

theorem foldl_columns_evalMod (acc : BitHeap w) (ps : List (Column × Nat)) :
    (ps.foldl (fun a p => List.foldl (fun a' c => addBit p.2 c a') a p.1.elems.toList)
        acc).evalMod env
      = (acc.evalMod env
          + (ps.map (fun p =>
              (p.1.elems.toList.map (fun c => 2^p.2 * (c.eval env).toInt)).sum)).sum) % 2^w := by
    induction ps generalizing acc with
    | nil =>
      simp [evalMod]
    | cons p tl ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, foldl_addBit_evalMod, Int.emod_add_emod]
      grind

theorem hornersMethod_eq_sum_zipIdx (env : Circuit.BitEnv) (l : List Column) (s : Nat) :
    (2^s : Int) * (HornersMethod env l : Int)
      = ((l.zipIdx s).map (fun p =>
          (p.1.elems.toList.map (fun c => 2^p.2 * (c.eval env).toInt)).sum)).sum := by
  induction l generalizing s with
  | nil =>
    simp [HornersMethod]
  | cons p ps ih =>
    simp [HornersMethod, List.zipIdx_cons, List.map_cons, List.sum_cons]
    rw [← ih]
    rw [Int.mul_add]
    have : 2 ^ s * (2 * ↑(HornersMethod env ps)) = 2 ^ (s + 1) * (HornersMethod env ps) := by
      grind
    norm_cast
    simp [this, Column.eval_eq_sum]
    induction p.elems.toList with
    | nil =>
      simp
    | cons c tl ih' =>
      simp only [List.map_cons, List.sum_cons]
      grind

theorem eval_eq_sum_columns (h : BitHeap w) (env : Circuit.BitEnv) :
    ((h.eval env : Int))
      = (h.columns.toList.zipIdx.map (fun p =>
          (p.1.elems.toList.map (fun c => 2^p.2 * (c.eval env).toInt)).sum)).sum := by
  simp [eval]
  have h0 := hornersMethod_eq_sum_zipIdx env h.columns.toList 0
  simp only [pow_zero, one_mul] at h0
  exact h0

theorem mergeInto_evalMod(acc h : BitHeap w) :
    (mergeInto acc h).evalMod env = (acc.evalMod env + h.evalMod env) % 2^w := by
  simp [mergeInto]
  rw [Vector.foldl, ←Array.foldl_toList]
  rw [foldl_columns_evalMod]
  simp only [evalMod, Vector.toArray_zipIdx, Array.toList_zipIdx, Int.emod_add_emod,
    Int.add_emod_emod]
  rw [eval_eq_sum_columns, eval_eq_sum_columns]
  grind

theorem foldl_mergeInto_evalMod (hs : List (BitHeap w)) (acc : BitHeap w) :
    (hs.foldl mergeInto acc).evalMod env
      = (acc.evalMod env + (hs.map (·.evalMod env)).sum) % 2^w := by
    induction hs generalizing acc with
    | nil =>
      simp only [evalMod, List.foldl_nil, List.map_nil, List.sum_nil, add_zero, dvd_refl,
        Int.emod_emod_of_dvd]
    | cons h tl ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih]
      rw [mergeInto_evalMod]
      simp
      grind

theorem foldl_add_init {w : ℕ} (acc hd : BitVec w) (tl : List (BitVec w)) :
    List.foldl (· + ·) (acc + hd) tl = List.foldl (· + ·) acc tl + hd := by
  induction tl generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons]
    rw [← ih]
    grind

theorem foldl_add_toNat_go (acc : BitVec w) (l : List (BitVec w)) :
    ((l.foldl (· + ·) acc).toNat : Int)
      = ((acc.toNat : Int) + (l.map (fun x => (x.toNat : Int))).sum) % 2^w := by
  induction l with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, add_zero]
    norm_cast
    simp only [BitVec.toNat_mod_cancel]
  | cons hd tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons]
    rw [foldl_add_init]
    rw [BitVec.toNat_add]
    simp [ih]
    grind

theorem toBitHeap_correct (c : ArithCircuit w) (bv : BitVecEnv w) :
    c.toBitHeap.evalMod bv.toBitEnv = ((c.denote bv).toNat : Int):= by
  fun_induction toBitHeap with
  | case1 varIndex =>
    simp only [BitHeap.evalMod, bitheapOfVar]
    rw [bitheapOfVar_go varIndex bv w (le_refl w)]
    simp [denote]
    norm_cast
    rw [BitVec.toNat_mod_cancel]
  | case2 args ih =>
    simp only [denote, BitHeap.addBitHeap]
    rw [foldl_mergeInto_evalMod]
    rw [foldl_add_toNat_go]
    simp only [empty_evalMod, List.map_map, zero_add, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
      Nat.zero_mod, Int.cast_ofNat_Int]
    congr 1
    congr 1
    simp only [List.map_inj_left, Function.comp_apply]
    assumption
  | case3 l r ih1 ih2=>
    sorry

end ArithCircuit

end Comb
