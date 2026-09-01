/-
# Dadda-tree optimality, machine-checked

The textbook claim (Dadda [Dad65], Parhami [Par10], quoted as "believed
optimal, no formal proof known"): Dadda's compression scheme is optimal among
compressor-tree schedules. This file proves the claim at the *shape* level
(column heights — the identity of the circuits in a column is irrelevant to
adder counts), for the hardware-cost metric 2·#FA + #HA (`Schedule.cost`;
pure FA-counting is not a meaningful metric, since FAs can be traded for
HA-spreading whenever free columns are in carry reach):

 1. **Dadda is NOT cost-optimal on arbitrary heaps**
    (`dadda_not_cost_optimal`, machine-checked) — optimality is specific to
    the taper of multiplier partial-product heaps (`ppShape`).

 2. **The level structure is irrelevant for the cost metric.** Per-column
    conservation over a whole schedule,

        mⱼ + 2Fⱼ + Hⱼ = nⱼ + Aⱼ₋₁      (Fⱼ/Hⱼ = total FA/HA at column j,
                                          Aⱼ = Fⱼ + Hⱼ = carries j → j+1)

    turns any schedule of any depth into a feasible tally chain, and the
    greedy chain provably dominates all of them (`greedyCost_le_chain`,
    `cost_lower_bound`).

 3. **MAIN THEOREM, fully proved for ALL k and ALL output widths, with NO
    `sorry` and NO `native_decide`** (`dadda_cost_optimal_pp_anyDepth`,
    `dadda_cost_optimal_pp_anyWidth`): on the k×k partial-product heap — at
    the canonical width 2k−1 or with any number of spill columns — every
    legal schedule of every depth costs at least as much as Dadda. The Dadda
    side is evaluated by the trapezoid invariant
    — after the stage with target t the shape is exactly
    [1, …, t−1] ++ [t]×(2k−2t+2) ++ [t−2, …, 1] — whose per-column tallies
    telescope to the greedy fold value (`go_tally`, `dadda_le_greedy_pp`).
    Axioms: `propext`, `Classical.choice`, `Quot.sound`.
-/
import DatapathVerification.BitHeap.BitHeap
import DatapathVerification.BitHeap.Chain
import DatapathVerification.BitHeap.Compressors.DaddaTree

namespace DaddaOpt

variable {w : Nat}

/-! ## 1. The model: shapes, stages, schedules -/

/-- The *shape* of a bit heap: just its column heights. -/
abbrev Shape (w : Nat) := Vector Nat w

def maxH (n : Shape w) : Nat := n.foldl max 0

/-- Compressed to at most two rows. -/
def Compressed (n : Shape w) : Prop := ∀ j : Fin w, n[j] ≤ 2

/-- One compression level: how many FAs and HAs are placed in each column. -/
structure Stage (w : Nat) where
  fa : Vector Nat w
  ha : Vector Nat w

namespace Stage

def faCount (s : Stage w) : Nat := s.fa.toList.sum

def haCount (s : Stage w) : Nat := s.ha.toList.sum

/-- Area-like cost of one stage: an FA is roughly twice an HA. -/
def cost (s : Stage w) : Nat := 2 * s.faCount + s.haCount

/-- A stage is legal on shape `n` iff
  * adders only consume bits present at the start of the level
    (carries produced within a level stay uncompressed until the next one), and
  * the MSB column hosts no adders (no overflow out of the heap). -/
def Legal (s : Stage w) (n : Shape w) : Prop :=
  (∀ j : Fin w, 3 * s.fa[j] + 2 * s.ha[j] ≤ n[j]) ∧
  s.fa.getD (w - 1) 0 + s.ha.getD (w - 1) 0 = 0

/-- Apply one level: column j loses `3·fa + 2·ha` input bits, gets back
`fa + ha` sum bits, and receives `fa + ha` carries from column j−1.
(For legal stages the Nat subtraction below is exact.) -/
def apply (s : Stage w) (n : Shape w) : Shape w :=
  Vector.ofFn fun j =>
    n[j] - (2 * s.fa[j] + s.ha[j])
      + if _ : 1 ≤ j.val then
          s.fa[j.val - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt)
            + s.ha[j.val - 1]'(Nat.lt_of_le_of_lt (Nat.sub_le _ _) j.isLt)
        else 0

end Stage

/-- A schedule = a sequence of levels. This is the universe the optimality
theorems quantify over. -/
abbrev Schedule (w : Nat) := List (Stage w)

def Schedule.Legal : Schedule w → Shape w → Prop
  | [], _ => True
  | s :: ss, n => s.Legal n ∧ Schedule.Legal ss (s.apply n)

def Schedule.run (S : Schedule w) (n : Shape w) : Shape w :=
  S.foldl (fun m s => s.apply m) n

def Schedule.numFA (S : Schedule w) : Nat := (S.map Stage.faCount).sum

def Schedule.numHA (S : Schedule w) : Nat := (S.map Stage.haCount).sum

/-- Area-like hardware cost: a full adder is roughly twice a half adder. -/
def Schedule.cost (S : Schedule w) : Nat := 2 * S.numFA + S.numHA

lemma Schedule.cost_cons (s : Stage w) (ss : Schedule w) :
    Schedule.cost (s :: ss) = s.cost + ss.cost := by
  simp [Schedule.cost, Schedule.numFA, Schedule.numHA, Stage.cost]
  omega

/-- `S` compresses `n` down to a two-row heap. -/
def Reduces (S : Schedule w) (n : Shape w) : Prop :=
  S.Legal n ∧ Compressed (S.run n)

/-! Everything above is decidable, so concrete claims about concrete shapes
and schedules can be settled by `native_decide`. -/

instance (s : Stage w) (n : Shape w) : Decidable (s.Legal n) := by
  unfold Stage.Legal; infer_instance

instance (n : Shape w) : Decidable (Compressed n) := by
  unfold Compressed; infer_instance

def Schedule.decLegal : (S : Schedule w) → (n : Shape w) → Decidable (S.Legal n)
  | [], _ => isTrue trivial
  | s :: ss, n =>
    have : Decidable (Schedule.Legal ss (s.apply n)) := Schedule.decLegal ss (s.apply n)
    inferInstanceAs (Decidable (_ ∧ _))

instance (S : Schedule w) (n : Shape w) : Decidable (S.Legal n) := Schedule.decLegal S n

instance (S : Schedule w) (n : Shape w) : Decidable (Reduces S n) := by
  unfold Reduces; infer_instance

/-! ## 2. Dadda at the shape level — total, no `partial` -/

/-- Carries flowing into column j at the current level, produced by the columns
below it (LSB→MSB scan). `target` is m_{l−1}. An excess of k over the target is
removed with ⌊k/2⌋ FAs (net −2 each) and (k mod 2) HAs (net −1), i.e. exactly
Dadda's "fewest FAs and at most one HA". -/
def carryIn (target : Nat) (n : Shape w) : Nat → Nat
  | 0 => 0
  | j + 1 =>
    let k := n.getD j 0 + carryIn target n j - target
    k / 2 + k % 2

def daddaStage (target : Nat) (n : Shape w) : Stage w where
  fa := Vector.ofFn fun j => (n[j] + carryIn target n j.val - target) / 2
  ha := Vector.ofFn fun j => (n[j] + carryIn target n j.val - target) % 2

/-- The full Dadda schedule: levels L, L−1, …, 1 with targets
m_{L−1}, …, m_0 = 2, where L = `findDaddaLevel (maxH n)`. -/
def daddaSchedule (n : Shape w) : Schedule w :=
  go (DaddaTree.findDaddaLevel (maxH n)) n
where
  go : Nat → Shape w → Schedule w
  | 0, _ => []
  | l + 1, m =>
    let s := daddaStage (DaddaTree.DaddaSequence l) m
    s :: go l (s.apply m)

/-- Column heights of the k×k multiplier partial-product heap, embedded in
width w: column j has height min(j+1, 2k−1−j). -/
def ppShape (k w : Nat) : Shape w :=
  Vector.ofFn fun j => min (j.val + 1) (2 * k - 1 - j.val)

/-! ## 3. The partial-product hypothesis is necessary (machine-checked)

On degenerate heaps Dadda's fixed level-target ladder wastes work: a single
column of height 6 is finished by two FAs in one level ([6] → [2,2], cost 4),
while Dadda spends 1 FA + 3 HAs (cost 5) walking its target ladder. -/

/-- One level, two FAs in column 0: [6] → [2,2]. Cost 4 beats Dadda's 5. -/
def faPair6 : Schedule 3 :=
  [⟨⟨#[2, 0, 0], rfl⟩, ⟨#[0, 0, 0], rfl⟩⟩]

/-- **Dadda is not cost-optimal on arbitrary heaps**: the partial-product
hypothesis in the main theorem is necessary. -/
theorem dadda_not_cost_optimal :
    ∃ (w : Nat) (n : Shape w) (S : Schedule w),
      Reduces S n ∧ S.length ≤ (daddaSchedule n).length ∧
      S.cost < (daddaSchedule n).cost := by
  refine ⟨3, ⟨#[6, 0, 0], rfl⟩, faPair6, ?_, ?_, ?_⟩ <;> native_decide

/-! ## 4. The level-free lower bound (MAIN RESULT)

For the cost metric the level structure is irrelevant. Define per-column
tallies over the whole schedule: Fⱼ/Hⱼ = total FAs/HAs ever placed at column
j, Aⱼ = Fⱼ + Hⱼ (= carries emitted from j into j+1). Bits at column j come
only from: the original nⱼ, carries from below (Aⱼ₋₁), and sum outputs of
column-j adders (Aⱼ). Column-wise conservation gives, for the final shape m:

    mⱼ + 2Fⱼ + Hⱼ = nⱼ + Aⱼ₋₁            (†)

Write rⱼ = 2Fⱼ + Hⱼ (the column's cost) and cⱼ = Aⱼ₋₁ (carry-in). Then any
legal schedule — of ANY length — satisfies, at every column,

    nⱼ + cⱼ ≤ rⱼ + 2,   rⱼ ≤ nⱼ + cⱼ,   rⱼ ≤ 2·cⱼ₊₁ ≤ 2rⱼ,   c₀ = 0, c_w = 0

(the first from mⱼ ≤ 2, the second from mⱼ ≥ 0, the third from
2(F+H) ≥ 2F+H ≥ F+H, the last from the MSB rule). `greedyCost` folds the
greedy solution of this relaxation — rⱼ = max(0, nⱼ + cⱼ − 2), carry-out
⌈rⱼ/2⌉ — and `greedyCost_le_chain` proves it DOMINATES every feasible chain:
from a pointwise-smaller carry, greedy pays less at the column and its
carry-out stays pointwise smaller, so the ordering propagates. Hence
(`cost_lower_bound`) greedyCost lower-bounds the cost of every schedule of
every depth, on every shape. On partial-product heaps the bound is tight and
equals Dadda's cost 2k² − 7k + 5. -/

section LevelFree

/-- A per-column tally sequence satisfying the relaxation constraints. -/
def TallyChain : List Nat → Nat → List Nat → Prop
  | [], c, rs => c = 0 ∧ rs = []
  | h :: t, c, rs => ∃ r rs' c', rs = r :: rs' ∧
      h + c ≤ r + 2 ∧ r ≤ h + c ∧ r ≤ 2 * c' ∧ c' ≤ r ∧ TallyChain t c' rs'

/-- Greedy solution of the relaxation: pay the minimum rⱼ = max(0, nⱼ+c−2)
at each column, forward the minimum carry ⌈rⱼ/2⌉. Linear time. -/
def greedyCost : List Nat → Nat → Nat
  | [], _ => 0
  | h :: t, c => (h + c - 2) + greedyCost t ((h + c - 2 + 1) / 2)

/-- **Greedy dominance**: starting from a carry ≤ the chain's, the greedy
fold costs no more than any feasible tally chain. (Greedy's carry stays
pointwise below the chain's: ⌈r̂/2⌉ ≤ ⌈r/2⌉ ≤ c'.) -/
theorem greedyCost_le_chain : ∀ (cols : List Nat) (c ĉ : Nat) (rs : List Nat),
    ĉ ≤ c → TallyChain cols c rs → greedyCost cols ĉ ≤ rs.sum := by
  intro cols
  induction cols with
  | nil =>
    intro c ĉ rs _ h
    simp only [TallyChain] at h
    simp [greedyCost, h.2]
  | cons hcol t ih =>
    intro c ĉ rs hle h
    simp only [TallyChain] at h
    obtain ⟨r, rs', c', hrs, h1, h2, h3, h4, hchain⟩ := h
    subst hrs
    simp only [greedyCost, List.sum_cons]
    have hr : hcol + ĉ - 2 ≤ r := by omega
    have hc' : (hcol + ĉ - 2 + 1) / 2 ≤ c' := by omega
    have := ih c' ((hcol + ĉ - 2 + 1) / 2) rs' hc' hchain
    omega

/-! ### From schedules to tallies: the conservation identity (†) -/

/-- Total FAs a schedule ever places at column j (0 when out of bounds). -/
def faTally (S : Schedule w) (j : Nat) : Nat := (S.map fun s => s.fa.getD j 0).sum

/-- Total HAs a schedule ever places at column j. -/
def haTally (S : Schedule w) (j : Nat) : Nat := (S.map fun s => s.ha.getD j 0).sum

/-- Carries ever received by column j (= adders ever placed at column j−1). -/
def carryTally (S : Schedule w) (j : Nat) : Nat :=
  if j = 0 then 0 else faTally S (j - 1) + haTally S (j - 1)

@[simp] lemma faTally_nil (j : Nat) : faTally ([] : Schedule w) j = 0 := rfl

@[simp] lemma haTally_nil (j : Nat) : haTally ([] : Schedule w) j = 0 := rfl

@[simp] lemma faTally_cons (s : Stage w) (ss : Schedule w) (j : Nat) :
    faTally (s :: ss) j = s.fa.getD j 0 + faTally ss j := by
  simp [faTally]

@[simp] lemma haTally_cons (s : Stage w) (ss : Schedule w) (j : Nat) :
    haTally (s :: ss) j = s.ha.getD j 0 + haTally ss j := by
  simp [haTally]

lemma carryTally_nil (j : Nat) : carryTally ([] : Schedule w) j = 0 := by
  unfold carryTally; split <;> simp

lemma carryTally_cons (s : Stage w) (ss : Schedule w) (j : Nat) :
    carryTally (s :: ss) j
      = (if j = 0 then 0 else s.fa.getD (j - 1) 0 + s.ha.getD (j - 1) 0)
        + carryTally ss j := by
  unfold carryTally
  split
  · simp
  · simp only [faTally_cons, haTally_cons]
    omega

@[simp] lemma Schedule.run_nil (n : Shape w) : Schedule.run [] n = n := rfl

@[simp] lemma Schedule.run_cons (s : Stage w) (ss : Schedule w) (n : Shape w) :
    Schedule.run (s :: ss) n = Schedule.run ss (s.apply n) := rfl

lemma vgetD_eq {v : Vector Nat w} {j : Nat} (hj : j < w) : v.getD j 0 = v[j] := by
  simp [Vector.getD, hj]

/-- One stage of column-j conservation: output + spend = input + carry-in. -/
lemma stage_balance {s : Stage w} {n : Shape w} (hleg : s.Legal n)
    (j : Nat) (hj : j < w) :
    (s.apply n).getD j 0 + (2 * s.fa.getD j 0 + s.ha.getD j 0)
      = n.getD j 0
        + (if j = 0 then 0 else s.fa.getD (j - 1) 0 + s.ha.getD (j - 1) 0) := by
  have hb := hleg.1 ⟨j, hj⟩
  simp only [Fin.getElem_fin] at hb
  simp only [vgetD_eq hj]
  by_cases h0 : j = 0
  · subst h0
    unfold Stage.apply
    rw [Vector.getElem_ofFn]
    simp
    omega
  · have hj1 : j - 1 < w := by omega
    simp only [if_neg h0, vgetD_eq hj1]
    unfold Stage.apply
    rw [Vector.getElem_ofFn]
    simp only [Fin.getElem_fin]
    rw [dif_pos (show 1 ≤ j by omega)]
    omega

/-- Whole-schedule column-j conservation (identity (†)):
final + 2·Fⱼ + Hⱼ = initial + Aⱼ₋₁. Levels play no role. -/
lemma run_balance : ∀ (S : Schedule w) (n : Shape w), S.Legal n →
    ∀ (j : Nat), j < w →
    (S.run n).getD j 0 + (2 * faTally S j + haTally S j)
      = n.getD j 0 + carryTally S j := by
  intro S
  induction S with
  | nil =>
    intro n _ j hj
    simp [carryTally_nil]
  | cons s ss ih =>
    intro n hleg j hj
    have hb := stage_balance (hleg.1 : (s : Stage w).Legal n) j hj
    have hr := ih (s.apply n) hleg.2 j hj
    simp only [Schedule.run_cons, faTally_cons, haTally_cons, carryTally_cons]
    omega

/-- No stage ever places an adder at the MSB column, so the MSB tally is 0. -/
lemma tally_msb_zero : ∀ (S : Schedule w) (n : Shape w), S.Legal n → 0 < w →
    faTally S (w - 1) = 0 ∧ haTally S (w - 1) = 0 := by
  intro S
  induction S with
  | nil => simp
  | cons s ss ih =>
    intro n hleg hw
    obtain ⟨hfa, hha⟩ := ih (s.apply n) hleg.2 hw
    have hmsb : s.fa.getD (w - 1) 0 + s.ha.getD (w - 1) 0 = 0 :=
      (hleg.1 : (s : Stage w).Legal n).2
    simp only [faTally_cons, haTally_cons, hfa, hha]
    omega

/-! ### Assembling the chain and the main lower bound -/

/-- The schedule's per-column cost list r₀, …, r_{w−1} with rⱼ = 2Fⱼ + Hⱼ. -/
def tallyList (S : Schedule w) : List Nat :=
  (List.range w).map fun j => 2 * faTally S j + haTally S j

private lemma sum_map_add (l : List Nat) (f g : Nat → Nat) :
    (l.map fun x => f x + g x).sum = (l.map f).sum + (l.map g).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private lemma sum_map_two_mul (l : List Nat) (f : Nat → Nat) :
    (l.map fun x => 2 * f x).sum = 2 * (l.map f).sum := by
  induction l with
  | nil => rfl
  | cons a t ih => simp only [List.map_cons, List.sum_cons, ih]; omega

private lemma range_map_getD (v : Vector Nat w) :
    (List.range w).map (fun j => v.getD j 0) = v.toList := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_map, List.getElem_range]
    have hi : i < w := by simpa using h1
    rw [vgetD_eq hi]
    simp

private lemma stage_cost_sum (s : Stage w) :
    ((List.range w).map fun j => 2 * s.fa.getD j 0 + s.ha.getD j 0).sum
      = s.cost := by
  rw [sum_map_add (List.range w) (fun j => 2 * s.fa.getD j 0) (fun j => s.ha.getD j 0),
    sum_map_two_mul, range_map_getD, range_map_getD]
  rfl

/-- The chain's total cost is exactly the schedule's cost (sum swap). -/
lemma tallyList_sum (S : Schedule w) : (tallyList S).sum = Schedule.cost S := by
  induction S with
  | nil =>
    simp [tallyList, Schedule.cost, Schedule.numFA, Schedule.numHA]
  | cons s ss ih =>
    have e : tallyList (s :: ss)
        = (List.range w).map fun j =>
            (2 * s.fa.getD j 0 + s.ha.getD j 0) + (2 * faTally ss j + haTally ss j) := by
      apply List.map_congr_left
      intro j _
      simp only [faTally_cons, haTally_cons]
      omega
    rw [e, sum_map_add (List.range w) (fun j => 2 * s.fa.getD j 0 + s.ha.getD j 0)
        (fun j => 2 * faTally ss j + haTally ss j),
      stage_cost_sum, Schedule.cost_cons]
    have ih' : (List.map (fun j => 2 * faTally ss j + haTally ss j)
        (List.range w)).sum = Schedule.cost ss := ih
    omega

/-- Every legal, compressing schedule induces a feasible tally chain from any
column j onward. -/
theorem chain_from (S : Schedule w) (n : Shape w) (hleg : S.Legal n)
    (hcomp : Compressed (S.run n)) (j : Nat) (hj : j ≤ w) :
    TallyChain (n.toList.drop j) (carryTally S j) ((tallyList S).drop j) := by
  rcases Nat.lt_or_ge j w with hlt | hge
  · have hjt : j < n.toList.length := by simpa using hlt
    have hjr : j < (tallyList S).length := by simpa [tallyList] using hlt
    rw [List.drop_eq_getElem_cons hjt, List.drop_eq_getElem_cons hjr]
    simp only [TallyChain]
    have hbal := run_balance S n hleg j hlt
    have hm2 : (S.run n).getD j 0 ≤ 2 := by
      have := hcomp ⟨j, hlt⟩
      rw [vgetD_eq hlt]
      simpa using this
    have hval : (tallyList S)[j]'hjr = 2 * faTally S j + haTally S j := by
      simp [tallyList]
    have hnval : n.toList[j]'hjt = n.getD j 0 := by
      rw [vgetD_eq hlt]
      simp
    refine ⟨(tallyList S)[j]'hjr, (tallyList S).drop (j + 1),
      faTally S j + haTally S j, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hval, hnval]; omega
    · rw [hval, hnval]; omega
    · rw [hval]; omega
    · rw [hval]; omega
    · have hcarry : carryTally S (j + 1) = faTally S j + haTally S j := by
        simp [carryTally]
      rw [← hcarry]
      exact chain_from S n hleg hcomp (j + 1) hlt
  · have hjw : j = w := Nat.le_antisymm hj hge
    rw [hjw, List.drop_eq_nil_of_le (by simp),
      List.drop_eq_nil_of_le (by simp [tallyList])]
    simp only [TallyChain]
    refine ⟨?_, trivial⟩
    rcases Nat.eq_zero_or_pos w with h0 | hpos
    · simp [carryTally, h0]
    · obtain ⟨hfa, hha⟩ := tally_msb_zero S n hleg hpos
      unfold carryTally
      rw [if_neg (by omega), hfa, hha]
  termination_by w - j

/-- **THE LEVEL-FREE LOWER BOUND (fully proved, kernel-checked).** For every
shape and every legal schedule that compresses it — with NO bound on the
number of levels — the greedy relaxation value bounds the schedule's hardware
cost from below. All optimality questions about compressor trees under the
2·#FA + #HA metric reduce to evaluating the linear-time fold `greedyCost`. -/
theorem cost_lower_bound (n : Shape w) (S : Schedule w)
    (hleg : S.Legal n) (hcomp : Compressed (S.run n)) :
    greedyCost n.toList 0 ≤ S.cost := by
  have hch := chain_from S n hleg hcomp 0 (Nat.zero_le w)
  have hc0 : carryTally S 0 = 0 := by simp [carryTally]
  rw [hc0] at hch
  simp only [List.drop_zero] at hch
  exact (greedyCost_le_chain _ 0 0 _ (Nat.le_refl 0) hch).trans
    (le_of_eq (tallyList_sum S))

/-! ## 5. Consequences: Dadda cost-optimality with NO level hypothesis -/


/-! ### The fold identity: Dadda meets the greedy bound

Proof architecture (every leaf is `omega`):
 * All carry trajectories in sight — Dadda stages AND the greedy fold — have
   ONE closed form: `carryIn t X j = min (min (j−t) (P−t)) ((2k+1−t) − j)`,
   where P is the profile height (previous target, or k for the pp heap).
 * After a Dadda stage with target t the shape is exactly the trapezoid
   `trapH k t`: ramp 1…t−1, plateau t (length 2k−2t+2), tail t−2…1.
 * The per-column tallies of the whole cascade then telescope column-locally
   (`go_tally`), summing to the greedy step values pointwise — so
   `tallyList_sum` closes the theorem with no cost algebra at all. -/

section DaddaGreedyIdentity

private lemma dseq_two_le (l : Nat) : 2 ≤ DaddaTree.DaddaSequence l := by
  induction l with
  | zero => simp [DaddaTree.DaddaSequence]
  | succ l ih => simp [DaddaTree.DaddaSequence]; omega

private lemma dseq_succ (l : Nat) :
    DaddaTree.DaddaSequence (l + 1) = 3 * DaddaTree.DaddaSequence l / 2 := rfl

private lemma findLevel_ge (h l : Nat) :
    h ≤ DaddaTree.DaddaSequence (DaddaTree.findDaddaLevel.findLevel h l) := by
  fun_induction DaddaTree.findDaddaLevel.findLevel h l with
  | _ => simp_all

private lemma findLevel_pred_lt (h l : Nat) :
    ∀ i, l ≤ i → i < DaddaTree.findDaddaLevel.findLevel h l →
      DaddaTree.DaddaSequence i < h := by
  fun_induction DaddaTree.findDaddaLevel.findLevel h l with
  | case1 l hcond =>
    intro i hli hlt
    omega
  | case2 l hcond ih =>
    intro i hli hlt
    rcases Nat.eq_or_lt_of_le hli with rfl | h'
    · omega
    · exact ih i h' hlt

private lemma findDaddaLevel_unfold (h : Nat) :
    DaddaTree.findDaddaLevel h = DaddaTree.findDaddaLevel.findLevel h 0 := rfl

private lemma list_foldl_max_le {l : List Nat} {a b : Nat}
    (ha : a ≤ b) (h : ∀ x ∈ l, x ≤ b) : l.foldl max a ≤ b := by
  induction l generalizing a with
  | nil => exact ha
  | cons x t ih =>
    exact ih (max_le ha (h x List.mem_cons_self)) fun y hy => h y (List.mem_cons_of_mem _ hy)

private lemma init_le_foldl_max : ∀ (l : List Nat) (a : Nat), a ≤ l.foldl max a
  | [], a => le_refl a
  | x :: t, a => le_trans (le_max_left a x) (init_le_foldl_max t (max a x))

private lemma list_le_foldl_max {l : List Nat} (a : Nat) {x : Nat} (hx : x ∈ l) :
    x ≤ l.foldl max a := by
  induction l generalizing a with
  | nil => simp at hx
  | cons y t ih =>
    rcases List.mem_cons.mp hx with rfl | h
    · exact le_trans (le_max_right a x) (init_le_foldl_max t (max a x))
    · exact ih _ h

private lemma maxH_eq_foldl (n : Shape w) : maxH n = n.toList.foldl max 0 := by
  simp [maxH, Vector.foldl]

/-- The k×k partial-product heap has maximum height k (any padding). -/
private lemma maxH_pp (k p : Nat) (hk : 1 ≤ k) :
    maxH (ppShape k (2 * k - 1 + p)) = k := by
  rw [maxH_eq_foldl]
  apply Nat.le_antisymm
  · apply list_foldl_max_le (Nat.zero_le k)
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    have hiw : i < 2 * k - 1 + p := by simpa using hi
    simp only [Vector.getElem_toList, ppShape, Vector.getElem_ofFn]
    omega
  · have hk1 : k - 1 < (ppShape k (2 * k - 1 + p)).toList.length := by
      simpa using by omega
    have hval : (ppShape k (2 * k - 1 + p)).toList[k - 1] = k := by
      simp only [Vector.getElem_toList, ppShape, Vector.getElem_ofFn]
      omega
    have := List.getElem_mem hk1
    rw [hval] at this
    exact list_le_foldl_max 0 this

/-- Height profile of the trapezoid left behind by a Dadda stage with target
t: ramp 1…t−1, plateau t, tail t−2…1. The Nat-truncated formula is valid for
ALL j (0 beyond the width). -/
def trapH (k t j : Nat) : Nat :=
  if j + 1 < t then j + 1 else if j ≤ 2 * k - t then t else 2 * k - 1 - j

def trap (k t p : Nat) : Shape (2 * k - 1 + p) := Vector.ofFn fun j => trapH k t j.val

private lemma trap_getD (k t p : Nat) (h2 : 2 ≤ t) (htk : t ≤ k) (j : Nat) :
    (trap k t p).getD j 0 = trapH k t j := by
  by_cases hj : j < 2 * k - 1 + p
  · rw [vgetD_eq hj]
    simp [trap]
  · have h0 : (trap k t p).getD j 0 = 0 := by simp [Vector.getD, hj]
    rw [h0]
    unfold trapH
    split_ifs <;> omega

private lemma pp_getD (k p : Nat) (j : Nat) :
    (ppShape k (2 * k - 1 + p)).getD j 0 = min (j + 1) (2 * k - 1 - j) := by
  by_cases hj : j < 2 * k - 1 + p
  · rw [vgetD_eq hj]
    simp [ppShape]
  · have h0 : (ppShape k (2 * k - 1 + p)).getD j 0 = 0 := by simp [Vector.getD, hj]
    rw [h0]
    omega

/-- Closed form of the stage-carry trajectory on a trapezoid: the carry ramps
up from column t, saturates at t'−t across the plateau, and ramps back down
near the MSB end. Valid for every j (0 beyond the action). -/
private lemma carry_trap (k t t' p : Nat) (h2 : 2 ≤ t) (htt : t < t') (ht'k : t' ≤ k) :
    ∀ j, carryIn t (trap k t' p) j
      = min (min (j - t) (t' - t)) ((2 * k + 1 - t) - j) := by
  intro j
  induction j with
  | zero => simp only [carryIn]; omega
  | succ j ih =>
    simp only [carryIn]
    rw [trap_getD k t' p (by omega) ht'k, ih]
    unfold trapH
    split_ifs <;> omega

/-- Same closed form on the partial-product heap itself (profile height k). -/
private lemma carry_pp (k t p : Nat) (h2 : 2 ≤ t) (htk : t < k) :
    ∀ j, carryIn t (ppShape k (2 * k - 1 + p)) j
      = min (min (j - t) (k - t)) ((2 * k + 1 - t) - j) := by
  intro j
  induction j with
  | zero => simp only [carryIn]; omega
  | succ j ih =>
    simp only [carryIn]
    rw [pp_getD, ih]
    omega

private lemma trap_getElem (k t p : Nat) (j : Nat) (hj : j < 2 * k - 1 + p) :
    (trap k t p)[j] = trapH k t j := by
  simp [trap]

private lemma stage_fa_getElem {w : Nat} (t : Nat) (n : Shape w) (j : Nat) (hj : j < w) :
    (daddaStage t n).fa[j] = (n[j] + carryIn t n j - t) / 2 := by
  simp [daddaStage]

private lemma stage_ha_getElem {w : Nat} (t : Nat) (n : Shape w) (j : Nat) (hj : j < w) :
    (daddaStage t n).ha[j] = (n[j] + carryIn t n j - t) % 2 := by
  simp [daddaStage]

/-- Per-column spend of one Dadda stage is exactly the excess (parity-free):
2·⌊e/2⌋ + e % 2 = e. -/
private lemma stage_tally {w : Nat} (t : Nat) (n : Shape w) (j : Nat) (hj : j < w) :
    2 * (daddaStage t n).fa.getD j 0 + (daddaStage t n).ha.getD j 0
      = n.getD j 0 + carryIn t n j - t := by
  rw [vgetD_eq hj, vgetD_eq hj, vgetD_eq hj, stage_fa_getElem t n j hj,
    stage_ha_getElem t n j hj]
  omega

/-- Raw effect of one Dadda stage on a column, unconditionally:
new = n − e + c where e = n + c ∸ t is the excess and c the carry-in. -/
private lemma stage_apply_getD {w : Nat} (t : Nat) (n : Shape w) (j : Nat) (hj : j < w) :
    ((daddaStage t n).apply n).getD j 0
      = n.getD j 0 - (n.getD j 0 + carryIn t n j - t) + carryIn t n j := by
  rw [vgetD_eq hj]
  unfold Stage.apply
  rw [Vector.getElem_ofFn]
  simp only [Fin.getElem_fin]
  rw [stage_fa_getElem t n j hj, stage_ha_getElem t n j hj]
  by_cases h1 : 1 ≤ j
  · rw [dif_pos h1, stage_fa_getElem t n (j - 1) (by omega),
      stage_ha_getElem t n (j - 1) (by omega)]
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have hcar : carryIn t n (i + 1)
        = (n.getD i 0 + carryIn t n i - t) / 2 + (n.getD i 0 + carryIn t n i - t) % 2 := by
      simp only [carryIn]
    have hgi : n.getD i 0 = n[i]'(by omega) := vgetD_eq (by omega)
    have hgj : n.getD (i + 1) 0 = n[i + 1]'hj := vgetD_eq hj
    simp only [Nat.add_sub_cancel]
    omega
  · have hj0 : j = 0 := by omega
    subst hj0
    rw [dif_neg h1]
    have hg : n.getD 0 0 = n[0]'hj := vgetD_eq hj
    simp only [carryIn]
    omega

/-- One Dadda stage turns the t'-trapezoid into the t-trapezoid. -/
private lemma stage_apply_trap (k t t' p : Nat) (h2 : 2 ≤ t) (htt : t < t')
    (ht'k : t' ≤ k) (htame : t' ≤ 2 * t) :
    (daddaStage t (trap k t' p)).apply (trap k t' p) = trap k t p := by
  apply Vector.ext
  intro j hj
  have h := stage_apply_getD t (trap k t' p) j hj
  rw [vgetD_eq hj] at h
  rw [h, trap_getElem k t p j hj, trap_getD k t' p (by omega) ht'k,
    carry_trap k t t' p h2 htt ht'k j]
  unfold trapH
  split_ifs <;> omega

/-- The first Dadda stage turns the partial-product heap into a trapezoid. -/
private lemma stage_apply_pp (k t p : Nat) (h2 : 2 ≤ t) (htk : t < k)
    (htame : k ≤ 2 * t) :
    (daddaStage t (ppShape k (2 * k - 1 + p))).apply (ppShape k (2 * k - 1 + p))
      = trap k t p := by
  apply Vector.ext
  intro j hj
  have h := stage_apply_getD t (ppShape k (2 * k - 1 + p)) j hj
  rw [vgetD_eq hj] at h
  rw [h, trap_getElem k t p j hj, pp_getD, carry_pp k t p h2 htk j]
  unfold trapH
  split_ifs <;> omega

set_option maxHeartbeats 1600000 in
/-- **The tally telescope**: running the Dadda cascade from the t-trapezoid
down to target 2, the total per-column spend is the interval-partition value
min(J, t) − 2 (J = min(j, 2k+1−j)), shifted by the shape difference. Each
inductive step is the interval identity — pure linear arithmetic. -/
private lemma go_tally (k p : Nat) (hk : 3 ≤ k) :
    ∀ (l : Nat), DaddaTree.DaddaSequence l < k → ∀ (j : Nat), j < 2 * k - 1 + p →
      2 * faTally (daddaSchedule.go l (trap k (DaddaTree.DaddaSequence l) p)) j
        + haTally (daddaSchedule.go l (trap k (DaddaTree.DaddaSequence l) p)) j
        + trapH k 2 j
      = trapH k (DaddaTree.DaddaSequence l) j
        + (min (min j (2 * k + 1 - j)) (DaddaTree.DaddaSequence l) - 2) := by
  intro l
  induction l with
  | zero =>
    intro _ j hj
    simp only [daddaSchedule.go, faTally_nil, haTally_nil, DaddaTree.DaddaSequence]
    omega
  | succ l ih =>
    intro hlk j hj
    have hd2 := dseq_two_le l
    have hinc := DaddaTree.DaddaSequence_increases l
    have hlk' : DaddaTree.DaddaSequence l < k := lt_trans hinc hlk
    have htame : DaddaTree.DaddaSequence (l + 1) ≤ 2 * DaddaTree.DaddaSequence l := by
      rw [dseq_succ]; omega
    simp only [daddaSchedule.go]
    rw [stage_apply_trap k (DaddaTree.DaddaSequence l) (DaddaTree.DaddaSequence (l + 1))
      p hd2 hinc (le_of_lt hlk) htame]
    rw [faTally_cons, haTally_cons]
    have hst := stage_tally (DaddaTree.DaddaSequence l)
      (trap k (DaddaTree.DaddaSequence (l + 1)) p) j (by omega)
    rw [trap_getD k (DaddaTree.DaddaSequence (l + 1)) p (by omega) (le_of_lt hlk),
      carry_trap k (DaddaTree.DaddaSequence l) (DaddaTree.DaddaSequence (l + 1))
        p hd2 hinc (le_of_lt hlk) j] at hst
    have hih := ih hlk' j hj
    unfold trapH at hst hih ⊢
    split_ifs at hst hih ⊢ <;> omega

set_option maxHeartbeats 1600000 in
/-- Top level: total per-column tallies of the full Dadda schedule on the
k×k partial-product heap equal the greedy step values. -/
private lemma dadda_tally_pp (k p : Nat) (hk : 3 ≤ k) (j : Nat)
    (hj : j < 2 * k - 1 + p) :
    2 * faTally (daddaSchedule (ppShape k (2 * k - 1 + p))) j
      + haTally (daddaSchedule (ppShape k (2 * k - 1 + p))) j
      + trapH k 2 j
    = min (j + 1) (2 * k - 1 - j) + (min (min j (2 * k + 1 - j)) k - 2) := by
  have hL1 : k ≤ DaddaTree.DaddaSequence (DaddaTree.findDaddaLevel k) := by
    rw [findDaddaLevel_unfold]; exact findLevel_ge k 0
  have hLpos : 1 ≤ DaddaTree.findDaddaLevel k := by
    by_contra h
    have h0 : DaddaTree.findDaddaLevel k = 0 := by omega
    rw [h0] at hL1
    simp [DaddaTree.DaddaSequence] at hL1
    omega
  have hLlt : DaddaTree.DaddaSequence (DaddaTree.findDaddaLevel k - 1) < k := by
    apply findLevel_pred_lt k 0 _ (Nat.zero_le _)
    rw [← findDaddaLevel_unfold]
    omega
  obtain ⟨L', hL'⟩ : ∃ L', DaddaTree.findDaddaLevel k = L' + 1 :=
    ⟨DaddaTree.findDaddaLevel k - 1, by omega⟩
  unfold daddaSchedule
  rw [maxH_pp k p (by omega), hL']
  simp only [daddaSchedule.go]
  have hd2 := dseq_two_le L'
  have hdlt : DaddaTree.DaddaSequence L' < k := by
    rw [hL'] at hLlt
    simpa using hLlt
  have htame : k ≤ 2 * DaddaTree.DaddaSequence L' := by
    rw [hL', dseq_succ] at hL1
    omega
  rw [stage_apply_pp k (DaddaTree.DaddaSequence L') p hd2 hdlt htame]
  rw [faTally_cons, haTally_cons]
  have hst := stage_tally (DaddaTree.DaddaSequence L') (ppShape k (2 * k - 1 + p)) j hj
  rw [pp_getD, carry_pp k (DaddaTree.DaddaSequence L') p hd2 hdlt j] at hst
  have hih := go_tally k p hk L' hdlt j hj
  unfold trapH at hih ⊢
  split_ifs at hih ⊢ <;> omega

/-- The greedy fold, evaluated: it sums the per-column excesses along the
`carryIn 2` trajectory. -/
private lemma greedy_drop {w : Nat} (n : Shape w) (j : Nat) (hj : j ≤ w) :
    greedyCost (n.toList.drop j) (carryIn 2 n j)
      = (((List.range w).map fun i => n.getD i 0 + carryIn 2 n i - 2).drop j).sum := by
  rcases Nat.lt_or_ge j w with hlt | hge
  · have hjt : j < n.toList.length := by simpa using hlt
    have hjr : j < ((List.range w).map fun i =>
        n.getD i 0 + carryIn 2 n i - 2).length := by simpa using hlt
    rw [List.drop_eq_getElem_cons hjt, List.drop_eq_getElem_cons hjr]
    simp only [greedyCost, List.sum_cons]
    have hnv : n.toList[j]'hjt = n.getD j 0 := by
      rw [vgetD_eq hlt]; simp
    have hrv : (((List.range w).map fun i =>
        n.getD i 0 + carryIn 2 n i - 2)[j]'hjr) = n.getD j 0 + carryIn 2 n j - 2 := by
      simp
    have hstep : (n.getD j 0 + carryIn 2 n j - 2 + 1) / 2 = carryIn 2 n (j + 1) := by
      simp only [carryIn]
      omega
    rw [hnv, hrv, hstep, greedy_drop n (j + 1) hlt]
  · have hjw : j = w := Nat.le_antisymm hj hge
    rw [hjw, List.drop_eq_nil_of_le (by simp), List.drop_eq_nil_of_le (by simp)]
    simp [greedyCost]
  termination_by w - j

private lemma greedy_eq_sum {w : Nat} (n : Shape w) :
    greedyCost n.toList 0
      = ((List.range w).map fun i => n.getD i 0 + carryIn 2 n i - 2).sum := by
  have h := greedy_drop n 0 (Nat.zero_le w)
  simpa [carryIn] using h

end DaddaGreedyIdentity

/-- **The fold identity, PROVED for all k and all output widths 2k−1+p**:
Dadda's cost on the k×k partial-product heap is at most the greedy relaxation
value (in fact equal; both are 2k² − 7k + 5 for k ≥ 3, at any padding — the
spill columns are provably inert).

The proof: `tallyList_sum` reduces Dadda's cost to its per-column tallies;
`go_tally`/`dadda_tally_pp` (the trapezoid-invariant telescope) evaluate
those tallies in closed form; `greedy_eq_sum`/`carry_pp` evaluate the greedy
fold to the same expression; the two agree pointwise by linear arithmetic. -/
lemma dadda_le_greedy_pp (k p : Nat) :
    (daddaSchedule (ppShape k (2 * k - 1 + p))).cost
      ≤ greedyCost (ppShape k (2 * k - 1 + p)).toList 0 := by
  by_cases hk : 3 ≤ k
  · rw [← tallyList_sum, greedy_eq_sum]
    apply le_of_eq
    unfold tallyList
    congr 1
    apply List.map_congr_left
    intro j hjmem
    have hj : j < 2 * k - 1 + p := List.mem_range.mp hjmem
    have ht := dadda_tally_pp k p hk j hj
    have hc := carry_pp k 2 p (le_refl 2) (by omega) j
    rw [pp_getD, hc]
    unfold trapH at ht
    split_ifs at ht <;> omega
  · -- k ≤ 2: the heap is already two rows, Dadda's schedule is empty.
    have hnil : daddaSchedule (ppShape k (2 * k - 1 + p)) = [] := by
      have hle : maxH (ppShape k (2 * k - 1 + p)) ≤ 2 := by
        rw [maxH_eq_foldl]
        apply list_foldl_max_le (by omega)
        intro x hx
        obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
        have hiw : i < 2 * k - 1 + p := by simpa using hi
        simp only [Vector.getElem_toList, ppShape, Vector.getElem_ofFn]
        omega
      have hlvl : DaddaTree.findDaddaLevel (maxH (ppShape k (2 * k - 1 + p))) = 0 := by
        rw [findDaddaLevel_unfold, DaddaTree.findDaddaLevel.findLevel]
        rw [if_pos (by simp [DaddaTree.DaddaSequence]; omega)]
      unfold daddaSchedule
      rw [hlvl]
      rfl
    rw [hnil]
    exact Nat.zero_le _

/-- **THE THEOREM — Dadda cost-optimality for ALL k, fully proved.**
On the k×k multiplier partial-product heap, every legal compression
schedule — with NO restriction on the number of levels — costs at least as
much (2·#FA + #HA) as Dadda's schedule. Kernel-checked end to end: the only
axioms are `propext`, `Classical.choice`, `Quot.sound`. -/
theorem dadda_cost_optimal_pp_anyDepth (k : Nat) (S : Schedule (2 * k - 1))
    (hS : Reduces S (ppShape k (2 * k - 1))) :
    (daddaSchedule (ppShape k (2 * k - 1))).cost ≤ S.cost :=
  (dadda_le_greedy_pp k 0).trans (cost_lower_bound _ S hS.1 hS.2)

/-- **Width-generalized main theorem**: the same, with any number p of spill
columns beyond the 2k−1 partial-product columns. Extra output width — the
loophole that broke pure-FA-count optimality — does not help any competitor
under the cost metric. -/
theorem dadda_cost_optimal_pp_anyWidth (k p : Nat) (S : Schedule (2 * k - 1 + p))
    (hS : Reduces S (ppShape k (2 * k - 1 + p))) :
    (daddaSchedule (ppShape k (2 * k - 1 + p))).cost ≤ S.cost :=
  (dadda_le_greedy_pp k p).trans (cost_lower_bound _ S hS.1 hS.2)

end LevelFree

end DaddaOpt
