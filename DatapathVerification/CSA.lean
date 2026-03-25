import Blase

structure CSAResult (w : ℕ) where
  s : BitVec w
  t : BitVec (w + 1)

def carrySave : (w : ℕ) → BitVec w → BitVec w → BitVec w → CSAResult w
  | 0, _, _, _ => ⟨0#0, 0#1⟩
  | n + 1, a, b, c =>
    let aLo : BitVec n := a.truncate n
    let bLo : BitVec n := b.truncate n
    let cLo : BitVec n := c.truncate n
    let ⟨S, T⟩ := carrySave n aLo bLo cLo
    let aMsb := a[n]
    let bMsb := b[n]
    let cMsb := c[n]
    let x := aMsb ^^ bMsb
    let sum := x ^^ cMsb
    let carry := (aMsb && bMsb) || (cMsb && x)
    ⟨BitVec.cons sum S, BitVec.cons carry T⟩

#eval carrySave 32 5 7 3

theorem BitVec.eq_cons_truncate (a b c : BitVec (n + 1)) :
    a ^^^ b ^^^ c = BitVec.cons (a.msb ^^ b.msb ^^ c.msb)
                                (a.truncate n ^^^ b.truncate n ^^^ c.truncate n) := by
  ext i
  simp only [BitVec.getElem_xor, BitVec.getElem_cons]
  by_cases h : i = 0 <;> grind

theorem carrySave_s_eq_xor (a b c : BitVec w) :
    (carrySave w a b c).s = a ^^^ b ^^^ c := by
  induction w with
  | zero => grind
  | succ n ih =>
    unfold carrySave
    simp only
    rw [ih]
    grind

theorem carrySave_t_eq_shift (a b c : BitVec w) :
    (carrySave w a b c).t = (a &&& b ||| a &&& c ||| b &&& c).zeroExtend (w+1) <<< 1 := by
  induction w with
  | zero =>
    unfold carrySave
    bv_normalize
  | succ n ih =>
    unfold carrySave
    simp only
    rw [ih]
    set x := a &&& b ||| a &&& c ||| b &&& c
    set trunc_and := BitVec.truncate n a &&& BitVec.truncate n b |||
               BitVec.truncate n a &&& BitVec.truncate n c |||
               BitVec.truncate n b &&& BitVec.truncate n c
    have hta : trunc_and = BitVec.truncate n x := by grind
    have hcarry : (a[n] && b[n] || c[n] && (a[n] ^^ b[n])) = x[n] := by grind
    rw [hta, hcarry]
    ext i
    by_cases hi0 : i = 0
    · grind
    · by_cases hi : i = n + 1 <;> grind

theorem cons_toNat_toNat_pow2 {a : BitVec w} {b : Bool} : (a.cons b).toNat = b.toNat * (2^(w)) + a.toNat:= by
  cases b with
  | false => grind
  | true =>
    rw [BitVec.toNat_cons']
    simp
    omega

theorem fulladder_arith (a b c : Bool) :
  a.toNat + b.toNat + c.toNat =
  2 * ((a && b) || (c && (a ^^ b))).toNat + (a ^^ b ^^ c).toNat := by
  cases a <;> cases b <;> cases c <;> decide

theorem toNat_toNat_truncate (a : BitVec w) (h: 1 ≤ w) : a.toNat = (a[w-1].toNat * (2^(w-1))) + (a.truncate (w-1)).toNat := by
  simp only [BitVec.truncate_eq_setWidth, BitVec.toNat_setWidth]
  have hmsb : a[w-1].toNat = a.toNat / 2^(w-1) := by
    simp only [Bool.toNat, BitVec.getElem_eq_testBit_toNat, Nat.testBit, Nat.shiftRight_eq_div_pow,
      Nat.one_and_eq_mod_two, Nat.mod_two_bne_zero]
    have : a.toNat / 2 ^ (w - 1) % 2 = a.toNat / 2 ^ (w - 1) := by
        simp only [Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
        refine Nat.div_lt_of_lt_mul ?_
        have h1 : 2 ^ (w-1) * 2 = 2 ^ w := by refine Nat.two_pow_pred_mul_two ?_; omega
        simp [h1]; omega
    by_cases h : a.toNat / 2 ^ (w - 1) % 2 == 1
    · simp only [h, cond_true]
      simp_all only [beq_iff_eq]
    · simp_all only [beq_iff_eq, Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
      have : a.toNat / 2 ^ (w - 1) = 0 := by
        have h_nat : 0 ≤ a.toNat / 2 ^ (w - 1) := Nat.zero_le _
        omega
      simp [this]
  simp [hmsb]
  rw [Nat.div_add_mod']

theorem carry_save_adder_toNat (a b c : BitVec w) :
    a.toNat + b.toNat + c.toNat =  ((carrySave w a b c).t).toNat + ((carrySave w a b c).s).toNat := by
  induction w with
  | zero => simp [carrySave]; grind
  | succ n ih =>
    unfold carrySave
    simp only
    rw [toNat_toNat_truncate a (by omega), toNat_toNat_truncate b (by omega), toNat_toNat_truncate c (by omega)]
    simp only [cons_toNat_toNat_pow2]
    have ih_inst := ih (a.truncate n) (b.truncate n) (c.truncate n)
    simp only [Nat.add_one_sub_one]
    have := fulladder_arith a[n] b[n] c[n]
    ac_nf at *
    grind

theorem carrySave_t_eq_and_shift {a b c : BitVec w}
    (ha : a.msb = false) (hb : b.msb = false) (hc : c.msb = false) :
    (carrySave w a b c).t.toNat = ((a &&& b ||| a &&& c ||| b &&& c) <<< 1).toNat := by
  rw [carrySave_t_eq_shift a b c]
  set x := a &&& b ||| a &&& c ||| b &&& c with hx_def
  have hz : (x.zeroExtend (w+1) <<< 1).toNat = (x <<< 1).toNat := by
    have h : x.msb = false := by grind
    simp
    have : x.toNat <<< 1 < 2 ^ (w) := by
      have : x.toNat < 2 ^ (w-1) := by grind
      rw [Nat.shiftLeft_eq]
      grind
    repeat rw [Nat.mod_eq_of_lt (by omega)]
  rw [hz]

theorem BitVec.add_add_eq
    (a b c : BitVec w)
    (ha : a.msb = false)
    (hb : b.msb = false)
    (hc : c.msb = false) :
    a + b + c = (a &&& b ||| a &&& c ||| b &&& c) <<< 1 + (a ^^^ b ^^^ c) := by
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_add, Nat.mod_add_mod]
  rw [carry_save_adder_toNat, carrySave_t_eq_and_shift ha hb hc, carrySave_s_eq_xor]

theorem BitVec.add_add_eq_bv_automata
    (a b c : BitVec w) :
    a + b + c = (a &&& b ||| a &&& c ||| b &&& c) <<< 1 + (a ^^^ b ^^^ c) := by
    bv_automata_classic
