import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Circuit
import DatapathVerification.BitHeap.Compressors.DaddaTree
import DatapathVerification.BitHeap.Compressors.NaiveCompression
import Mathlib.Algebra.BigOperators.Ring.List


open BitHeap
namespace Comb

inductive ArithBinopKind
| add
| mul

inductive ArithCircuit : Nat → Type
  | var (varIndex : Nat) : ArithCircuit w
  | add (args : List (ArithCircuit w)) : ArithCircuit w
  | mul (l r : ArithCircuit w) : ArithCircuit w
  | zext (varIndex : Nat) (b : Nat) (hbw : b ≤ w) : ArithCircuit w -- `b`-bit variable zero-extended to `w` bits.
  | sext (varIndex : Nat) (b : Nat) (hbw : b ≤ w) (hb : 0 < b) : ArithCircuit w -- `b`-bit variable sign-extended to `w` bits.

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

Only the lowest `bits` are added as variables. Remaning bits are 0's.
-/
def bitheapOfVar (varIndex : Nat) (bits : Nat) : BitHeap w :=
  -- | We need to know that this index is unique which is a gigantic pain.
  List.range bits
    |>.foldl (fun bh i => bh.addBit i (BitHeap.Circuit.bit (varIndex * w + i))) (BitHeap.empty w)

/--
Given a bitvector (x : BV 3) sign-extended to width `w`, build a bitheap
```
x2 x2 x2 ... x2 x1 x0
```
Columns `0` to `bits - 1` hold the live bits of the variable; every column from
`bits` to `w - 1` holds a copy of the sign bit (column `bits - 1`), matching
`BitVec.signExtend`.
-/
def bitheapOfVarSext (varIndex : Nat) (bits : Nat) : BitHeap w :=
  let base := bitheapOfVar varIndex bits (w := w)
  (List.range (w - bits)).foldl
    (fun bh k => bh.addBit (bits + k) (BitHeap.Circuit.bit (varIndex * w + bits - 1))) base

def toBitHeap : ArithCircuit w → BitHeap w
  | .var varIndex => bitheapOfVar varIndex w
  | .add args => BitHeap.addBitHeap (args.map toBitHeap)
  | .mul l r => BitHeap.truncate ((toBitHeap l).mulBitHeap (toBitHeap r)) w (by omega)
  | .zext varIndex b _ => bitheapOfVar varIndex b
  | .sext varIndex b _ _ => bitheapOfVarSext varIndex b

def denote (ρ : BitVecEnv w) : ArithCircuit w → BitVec w
  | .var i => ρ i
  | .add args => (args.map (denote ρ)).foldl (· + ·) 0
  | .mul l r => denote ρ l * denote ρ r
  | .zext i b _ => ((ρ i).setWidth b).setWidth w
  | .sext i b _ _ => ((ρ i).setWidth b).signExtend w

def toCircuitVector (c : ArithCircuit w) : CircuitVector :=
  let bh := c.toBitHeap
  BitHeap.toSingleRow bh

theorem toBitEnv_apply (bv : BitVecEnv w) (i k : Nat) (hk : k < w) :
    bv.toBitEnv (i * w + k) = (bv i).getLsbD k := by
  simp only [BitVecEnv.toBitEnv, Nat.mul_add_mod_self_right]
  have h1 : (i * w + k) / w = i := by
    have hw : 0 < w := by grind
    rw [Nat.mul_comm, Nat.mul_add_div hw, Nat.add_eq_left, Nat.div_eq_of_lt hk]
  have h2 : k % w = k := by
    exact Nat.mod_eq_of_lt hk
  simp [h1, h2]

theorem toNat_mod_two_pow_succ (x : BitVec n) (m : Nat) :
    x.toNat % 2 ^ (m + 1) = x.toNat % 2 ^ m + 2 ^ m * (x.getLsbD m).toNat := by
  rw [Nat.mod_pow_succ, ← BitVec.testBit_toNat, Nat.toNat_testBit]

theorem natCast_emod_two_pow_of_lt {a w : Nat} (ha : a < 2 ^ w) :
    ((a : Int)) % 2 ^ w = (a : Int) := by
  have e : ((2 : Int) ^ w) = ((2 ^ w : Nat) : Int) := by grind
  rw [e, ← Int.natCast_emod, Nat.mod_eq_of_lt ha]

theorem bitheapOfVar_go (i : Nat) (bv : BitVecEnv w) (k : Nat) (hk : k ≤ w) :
    ((List.range k).foldl
        (fun bh j => bh.addBit j (.bit (i * w + j)))
        (BitHeap.empty w)).evalMod bv.toBitEnv
      = (bv i).toNat % 2 ^ k := by
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, empty_evalMod, pow_zero]
    grind
  | succ m ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      evalMod_heap_addBit, ih (by omega), Circuit.eval, toBitEnv_apply bv i m (by omega)]
    have key : ((bv i).toNat % 2 ^ m : Int) + 2 ^ m * ((bv i).getLsbD m).toInt
        = (((bv i).toNat % 2 ^ (m + 1) : Nat) : Int) := by
      rw [toNat_mod_two_pow_succ]; cases (bv i).getLsbD m <;> grind
    have hlt : (bv i).toNat % 2 ^ (m + 1) < 2 ^ w :=
      ((bv i).toNat.mod_lt (Nat.two_pow_pos _)).trans_le (Nat.pow_le_pow_right (by omega) (by omega))
    grind [natCast_emod_two_pow_of_lt hlt]

/--
`Nat`-valued closed form for the value contributed by the low `bits` live columns together
with `k` sign-replicated columns above them: `(bv i).toNat % 2^bits`, plus (if the sign bit is
set) another `2^(bits+k) - 2^bits` from the replicated sign bit occupying columns
`bits, ..., bits+k-1`.
-/
def signFillNat (x : BitVec n) (bits k : Nat) : Nat :=
  x.toNat % 2 ^ bits + if x.getLsbD (bits - 1) then 2 ^ (bits + k) - 2 ^ bits else 0

theorem signFillNat_lt (x : BitVec n) (bits k w : Nat) (hbits : 0 < bits) (hk : bits + k ≤ w) :
    signFillNat x bits k < 2 ^ w := by
  simp only [signFillNat]
  have h1 : x.toNat % 2 ^ bits < 2 ^ bits := Nat.mod_lt _ (Nat.two_pow_pos _)
  have h2 : (2:Nat) ^ bits ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) (by omega)
  have h3 : (2:Nat) ^ (bits + k) ≤ 2 ^ w := Nat.pow_le_pow_right (by omega) hk
  set a := x.toNat % 2 ^ bits
  split <;> omega

theorem signFillNat_succ (x : BitVec n) (bits k : Nat) (hbits : 0 < bits) :
    signFillNat x bits (k + 1)
      = signFillNat x bits k + 2 ^ (bits + k) * (x.getLsbD (bits - 1)).toNat := by
  simp only [signFillNat]
  have hge : (2:Nat) ^ bits ≤ 2 ^ (bits + k) := Nat.pow_le_pow_right (by omega) (by omega)
  have hstep : (2:Nat) ^ (bits + (k + 1)) = 2 ^ (bits + k) + 2 ^ (bits + k) := by
    rw [show bits + (k + 1) = (bits + k) + 1 by omega, pow_succ]; omega
  set a := x.toNat % 2 ^ bits
  cases x.getLsbD (bits - 1) <;> simp; omega

/--
Closed form for the sign-fill fold: the low `bits` columns hold `(bv i).toNat % 2^bits`
as usual, and each of the `k` sign-replicated columns above it contributes another copy
of the sign bit.
-/
theorem bitheapOfVarSext_go (i : Nat) (bv : BitVecEnv w) (bits k : Nat)
    (hbits : 0 < bits) (hk : bits + k ≤ w) :
    ((List.range k).foldl
        (fun bh j => bh.addBit (bits + j) (.bit (i * w + bits - 1)))
        (bitheapOfVar i bits (w := w))).evalMod bv.toBitEnv
      = ((signFillNat (bv i) bits k : Nat) : Int) := by
  have hsign : bv.toBitEnv (i * w + bits - 1) = (bv i).getLsbD (bits - 1) := by
    have : i * w + bits - 1 = i * w + (bits - 1) := by omega
    rw [this, toBitEnv_apply bv i (bits - 1) (by omega)]
  induction k with
  | zero =>
    simp only [List.range_zero, List.foldl_nil, signFillNat, add_zero, Nat.sub_self]
    simp only [ite_self]
    show (bitheapOfVar i bits (w := w)).evalMod bv.toBitEnv = _
    exact bitheapOfVar_go i bv bits (by omega)
  | succ m ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil,
      evalMod_heap_addBit, ih (by omega), Circuit.eval, hsign]
    have hnat : signFillNat (bv i) bits m + 2 ^ (bits + m) * ((bv i).getLsbD (bits - 1)).toNat
        = signFillNat (bv i) bits (m + 1) := (signFillNat_succ (bv i) bits m hbits).symm
    have hlt := signFillNat_lt (bv i) bits (m + 1) w hbits hk
    have hcast : ((bv i).getLsbD (bits - 1)).toInt = (((bv i).getLsbD (bits - 1)).toNat : Int) := by
      cases (bv i).getLsbD (bits - 1) <;> simp
    have hpow : (2 : Int) ^ (bits + m) = ((2 ^ (bits + m) : Nat) : Int) := by push_cast; rfl
    rw [hcast, hpow, ← Nat.cast_mul, ← Nat.cast_add, hnat]
    exact natCast_emod_two_pow_of_lt hlt

/--
`signFillNat` is exactly the `Nat` value of the sign-extension: the low `bits` bits of `x`
kept as-is, plus `2^w - 2^bits` when the sign bit is set.
-/
theorem signFillNat_eq_signExtend_toNat {n : Nat} (x : BitVec n) (bits w : Nat)
    (hbits : 0 < bits) (hbw : bits ≤ w) :
    signFillNat x bits (w - bits) = (((x.setWidth bits).signExtend w).toNat) := by
  have hlt : x.toNat % 2 ^ bits < 2 ^ w :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
      (Nat.pow_le_pow_right (by omega) hbw)
  have hw : bits + (w - bits) = w := by omega
  simp only [signFillNat, hw, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    BitVec.msb_setWidth, Nat.mod_eq_of_lt hlt, hbits, decide_true, Bool.true_and]

theorem foldl_addBit_evalMod  (idx : Nat) (h : BitHeap w) (cs : List Circuit) :
  (List.foldl (fun a c => addBit idx c a) h cs).evalMod env
    = (h.evalMod env + (cs.map (fun c => 2^idx * (c.eval env).toInt)).sum) % 2^w := by
    induction cs generalizing h with
    | nil =>
      simp only [evalMod, List.foldl_nil, List.map_nil, List.sum_nil, add_zero, dvd_refl,
        Int.emod_emod_of_dvd]
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
      simp only [evalMod, List.foldl_nil, List.map_nil, List.sum_nil, add_zero, dvd_refl,
        Int.emod_emod_of_dvd]
    | cons p tl ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, foldl_addBit_evalMod, Int.emod_add_emod]
      grind

theorem eval_eq_sum_columns (h : BitHeap w) (env : Circuit.BitEnv) :
    ((h.eval env : Int))
      = (h.columns.toList.zipIdx.map (fun p =>
          (p.1.elems.toList.map (fun c => 2^p.2 * (c.eval env).toInt)).sum)).sum := by
  simp only [eval]
  have h0 := hornersMethod_eq_sum_zipIdx env h.columns.toList 0
  simp only [pow_zero, one_mul] at h0
  exact h0

theorem mergeInto_evalMod(acc h : BitHeap w) :
    (mergeInto acc h).evalMod env = (acc.evalMod env + h.evalMod env) % 2^w := by
  simp only [mergeInto, Vector.foldl, ←Array.foldl_toList, foldl_columns_evalMod]
  simp only [evalMod, Vector.toArray_zipIdx, Array.toList_zipIdx, Int.emod_add_emod,
    Int.add_emod_emod,eval_eq_sum_columns, eval_eq_sum_columns]
  grind

theorem foldl_mergeInto_evalMod (hs : List (BitHeap w)) (acc : BitHeap w) :
    (hs.foldl mergeInto acc).evalMod env
      = (acc.evalMod env + (hs.map (·.evalMod env)).sum) % 2^w := by
    induction hs generalizing acc with
    | nil =>
      simp only [evalMod, List.foldl_nil, List.map_nil, List.sum_nil, add_zero, dvd_refl,
        Int.emod_emod_of_dvd]
    | cons h tl ih =>
      simp only [List.foldl_cons, ih, mergeInto_evalMod, Int.emod_add_emod, List.map_cons,
        List.sum_cons]
      grind

theorem foldl_add_init {w : ℕ} (acc hd : BitVec w) (tl : List (BitVec w)) :
    List.foldl (· + ·) (acc + hd) tl = List.foldl (· + ·) acc tl + hd := by
  induction tl generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.foldl_cons, ← ih]
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
    simp only [List.foldl_cons, foldl_add_init, BitVec.toNat_add, Int.natCast_emod, Nat.cast_add,
      ih, Nat.cast_pow, Nat.cast_ofNat, Int.emod_add_emod, List.map_cons, List.sum_cons]
    grind

theorem foldl_andBit_evalMod (env : Circuit.BitEnv) (idx : Nat) (c1 : Circuit)
    (cs : List Circuit) (h : BitHeap v) :
    (cs.foldl (fun a c2 => a.addBit idx (.binop .and c1 c2)) h).evalMod env
      = (h.evalMod env + 2^idx * (c1.eval env).toInt
          * (cs.map (fun c => (c.eval env).toInt)).sum) % 2^v := by
  induction cs generalizing h with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, mul_zero, add_zero,
      BitHeap.evalMod, dvd_refl, Int.emod_emod_of_dvd]
  | cons c tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih,
      BitHeap.evalMod_heap_addBit, Circuit.eval_and, Column.toInt_and_eq_mul, Int.emod_add_emod]
    grind

theorem mulColumns_evalMod (env : Circuit.BitEnv) (acc : BitHeap v)
    (col0 col1 : Column) (idx : Nat) :
    (mulColumns acc col0 col1 idx).evalMod env
      = (acc.evalMod env
          + 2^idx * (col0.eval env : Int) * (col1.eval env : Int)) % 2^v := by
  simp only [mulColumns, Column.eval_eq_sum col0, Column.eval_eq_sum col1]
  generalize col0.elems.toList = l0
  induction l0 generalizing acc with
  | nil =>
    simp only [List.foldl_nil, List.map_nil, List.sum_nil, mul_zero, zero_mul, add_zero,
      BitHeap.evalMod, dvd_refl, Int.emod_emod_of_dvd]
  | cons c1 tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, foldl_andBit_evalMod,
      Int.emod_add_emod]
    grind

theorem foldl_mulColumns_evalMod (env : Circuit.BitEnv) (col0 : Column) (i0 : Nat)
    (qs : List (Column × Nat)) (acc : BitHeap v) :
    (qs.foldl (fun a q => mulColumns a col0 q.1 (i0 + q.2)) acc).evalMod env
      = (acc.evalMod env + (col0.eval env : Int)
          * (qs.map (fun q => 2^(i0 + q.2) * (q.1.eval env : Int))).sum) % 2^v := by
  induction qs generalizing acc with
  | nil =>
    simp only [evalMod, List.foldl_nil, List.map_nil, List.sum_nil, mul_zero, add_zero, dvd_refl,
      Int.emod_emod_of_dvd]
  | cons q tl ih =>
    simp only [List.foldl_cons, List.map_cons, List.sum_cons, ih, mulColumns_evalMod,
      Int.emod_add_emod]
    grind

theorem mulRow_evalMod (env : Circuit.BitEnv) (col0 : Column) (i0 : Nat)
    (h1 : BitHeap w) (acc : BitHeap v) :
    (h1.columns.zipIdx.foldl
        (fun acc' q => mulColumns acc' col0 q.1 (i0 + q.2)) acc).evalMod env
      = (acc.evalMod env
          + 2^i0 * (col0.eval env : Int) * (h1.eval env : Int)) % 2^v := by
  rw [Vector.foldl, ← Array.foldl_toList, foldl_mulColumns_evalMod, Vector.toArray_zipIdx, Array.toList_zipIdx]
  have hsum : (col0.eval env : Int)
        * ((h1.columns.toList.zipIdx.map
            (fun q => 2^(i0 + q.2) * (q.1.eval env : Int))).sum)
      = 2^i0 * (col0.eval env : Int) * (h1.eval env : Int) := by
    have hz := BitHeap.hornersMethod_mul_eq_sum_zipIdx env h1.columns.toList i0 0
    have heval : (h1.eval env : Int) = HornersMethod env h1.columns.toList := by
      simp only [eval]
    rw [heval, ← hz, Nat.add_zero]
    grind
  simp only [Vector.toList] at hsum ⊢
  rw [hsum]

theorem foldl_mulRow_evalMod (env : Circuit.BitEnv) (h1 : BitHeap w)
    (ps : List (Column × Nat)) (acc : BitHeap v) :
    (ps.foldl (fun a p =>
        h1.columns.zipIdx.foldl
          (fun a' q => mulColumns a' p.1 q.1 (p.2 + q.2)) a) acc).evalMod env
      = (acc.evalMod env
          + (ps.map (fun p => 2^p.2 * (p.1.eval env : Int))).sum
              * (h1.eval env : Int)) % 2^v := by
  induction ps generalizing acc with
  | nil =>
    simp only [evalMod, List.foldl_nil, List.map_nil, List.sum_nil, zero_mul, add_zero, dvd_refl,
      Int.emod_emod_of_dvd]
  | cons p tl ih =>
    simp only [List.foldl_cons, ih, mulRow_evalMod, Int.emod_add_emod, List.map_cons, List.sum_cons]
    grind

theorem mulBitHeap_evalMod (h0 h1 : BitHeap w) (env : Circuit.BitEnv) :
    (h0.mulBitHeap h1).evalMod env
      = ((h0.eval env : Int) * (h1.eval env : Int)) % 2^(2*w - 1) := by
  simp only [mulBitHeap]
  rw [←Vector.foldl_toList, foldl_mulRow_evalMod]
  congr 1
  simp only [empty_evalMod, Vector.toList_zipIdx, zero_add, mul_eq_mul_right_iff,
    Int.natCast_eq_zero, eval]
  left
  have h0 := hornersMethod_eq_sum_zipIdx env h0.columns.toList 0
  simp_all [pow_zero, one_mul, Column.eval_eq_sum, List.sum_map_mul_left]

theorem toBitHeap_correct (c : ArithCircuit w) (bv : BitVecEnv w) :
    c.toBitHeap.evalMod bv.toBitEnv = ((c.denote bv).toNat : Int) := by
  fun_induction toBitHeap with
  | case1 varIndex =>
    simp only [bitheapOfVar, denote,
      bitheapOfVar_go varIndex bv w (le_refl w)]
    norm_cast
    rw [BitVec.toNat_mod_cancel]
  | case2 args ih =>
    simp only [addBitHeap, foldl_mergeInto_evalMod, empty_evalMod, List.map_map, zero_add, denote,
      BitVec.ofNat_eq_ofNat, foldl_add_toNat_go, BitVec.toNat_ofNat, Nat.zero_mod, Nat.cast_zero]
    congr 2
    simp only [List.map_inj_left, Function.comp_apply]
    exact ih
  | case3 l r ih1 ih2 =>
    simp only [denote]
    simp only [BitHeap.evalMod] at ih1 ih2
    have hdvd : ((2:Int)^w) ∣ ((2:Int)^(2*w - 1)) := pow_dvd_pow 2 (by omega)
    rw [evalMod_truncateMod, BitVec.toNat_mul, mulBitHeap_evalMod, Int.emod_emod_of_dvd _ hdvd, Int.mul_emod, ih1, ih2]
    congr 1
  | case4 varIndex b hbw =>
    simp only [bitheapOfVar, denote, bitheapOfVar_go varIndex bv b hbw]
    have hlt : (bv varIndex).toNat % 2 ^ b < 2 ^ w :=
      Nat.lt_of_lt_of_le (Nat.mod_lt _ (Nat.two_pow_pos _))
        (Nat.pow_le_pow_right (by omega) hbw)
    simp [BitVec.toNat_setWidth, Nat.mod_eq_of_lt hlt]
  | case5 varIndex b hbw hb =>
    simp only [bitheapOfVarSext, denote,
      bitheapOfVarSext_go varIndex bv b (w - b) hb (by omega)]
    rw [signFillNat_eq_signExtend_toNat (bv varIndex) b w hb hbw]

theorem compressed_toBitHeap_correct (c : ArithCircuit w) (bv : BitVecEnv w)
    (adders : List Chain.Adder) (h' : BitHeap w)
    (heq : Chain.applyChainSafe adders c.toBitHeap = some h') :
    h'.evalMod bv.toBitEnv = ((c.denote bv).toNat : Int) := by
  rw [Chain.applyChainSafe_correct_mod adders c.toBitHeap h' heq, toBitHeap_correct]

end ArithCircuit

end Comb
