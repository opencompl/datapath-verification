# A Machine-Checked Proof that Dadda's Compressor Tree is Cost-Optimal

*Companion document to `DaddaOptimality.lean`. All results are formalized in
Lean 4 with no `sorry`. The main theorem and its entire proof chain are
kernel-checked without `native_decide`; the only axioms are `propext`,
`Classical.choice`, `Quot.sound` — the standard axioms of Lean's type
theory. (One side result, the counterexample of §5, is checked by
`native_decide`.)*

## 1. Abstract

Dadda's algorithm (1965) compresses the partial-product heap of a k×k
multiplier down to two rows using full adders (FAs) and half adders (HAs).
The literature (Parhami; quoted in de Dinechin–Kumm) states that the scheme
is *believed* optimal, "however, a formal proof for this is missing to the
best of the authors' knowledge."

We prove:

> **Theorem** (`dadda_cost_optimal_pp_anyWidth`). For every k and every
> output width 2k−1+p, every legal compression schedule that reduces the k×k
> partial-product heap to two rows — using *any* number of levels — has
> hardware cost 2·#FA + #HA at least that of Dadda's schedule.

Two findings shape the statement. First, the folklore claim as literally
stated — optimality of the *full-adder count* — is **false**: FAs can be
traded for HA chains whenever spare columns are in carry reach, so pure FA
count is not a meaningful objective (machine-checked counterexamples existed
at an earlier stage of this development; see §6). The robust objective is
the area-like cost 2·#FA + #HA, under which an FA costs about twice an HA.
Second, and centrally: for this cost metric **the timing structure of the
circuit is irrelevant** — the optimality question collapses to a
one-dimensional flow problem over column totals. That collapse is what makes
a complete formal proof feasible.

## 2. The model: what is a schedule?

The formalization is at the **shape level**: a bit heap is abstracted to its
column heights, since which particular signal sits in a column cannot affect
adder counts.

```lean
abbrev Shape (w : Nat) := Vector Nat w          -- column heights, LSB first
def Compressed (n : Shape w) : Prop := ∀ j, n[j] ≤ 2
```

A **stage** is one level of the compressor tree, described by how many FAs
and HAs it places in each column:

```lean
structure Stage (w : Nat) where
  fa : Vector Nat w
  ha : Vector Nat w
```

A stage is **legal** on shape `n` when (i) its adders only consume bits that
exist at the start of the level — an FA consumes 3 bits, an HA 2, so
`3·fa[j] + 2·ha[j] ≤ n[j]`; and (ii) the most significant column hosts no
adders, so no carry is silently dropped off the edge of the heap. Applying a
stage is arithmetic: column j loses its consumed bits, regains one sum bit
per adder, and receives one carry per adder of column j−1:

```lean
n'[j] = n[j] − (2·fa[j] + ha[j]) + (fa[j−1] + ha[j−1])
```

Note the model's timing discipline: carries produced *within* a level land in
the next column but cannot be consumed until the *next* level — exactly the
standard compressor-tree semantics.

A **schedule** is any finite sequence of stages, and this is the universe the
theorem quantifies over:

```lean
abbrev Schedule (w : Nat) := List (Stage w)

def Schedule.Legal : Schedule w → Shape w → Prop
  | [],      _ => True
  | s :: ss, n => s.Legal n ∧ Legal ss (s.apply n)

def Reduces (S : Schedule w) (n : Shape w) : Prop :=
  S.Legal n ∧ Compressed (S.run n)
```

"All possible schedules" therefore means: any number of levels, any placement
of any number of FAs/HAs per column per level, subject only to bit
availability and the no-overflow rule. Wallace trees, Dadda trees, and every
irregular hand-optimized reduction are points in this space. The objective is

```lean
def Schedule.cost (S : Schedule w) : Nat := 2 * S.numFA + S.numHA
```

Dadda's own algorithm is defined in the same language, as a total function
(`daddaSchedule`): compute the target ladder d₀ = 2, d_{l+1} = ⌊3d_l/2⌋, and
at each level scan columns LSB→MSB, reducing each column to the current
target with ⌊excess/2⌋ FAs and (excess mod 2) HAs. The k×k partial-product
heap is `ppShape k`, with column heights min(j+1, 2k−1−j).

The main theorem, precisely:

```lean
theorem dadda_cost_optimal_pp_anyWidth (k p : Nat) (S : Schedule (2*k−1+p))
    (hS : Reduces S (ppShape k (2*k−1+p))) :
    (daddaSchedule (ppShape k (2*k−1+p))).cost ≤ S.cost
```

There is no hypothesis on `S.length`: the adversary may use arbitrarily many
levels. There is no restriction to "reasonable" strategies. The padding `p`
allows the output rows to spill beyond the partial-product columns.

## 3. Proof, from above

The proof has two independent halves that meet at a linear-time fold called
`greedyCost`.

**Half 1 — every schedule pays at least the greedy value.** Forget time.
For a whole schedule define per-column tallies F_j, H_j (total FAs/HAs ever
placed at column j) and A_j = F_j + H_j; since every adder emits exactly one
carry, A_j is also the total carry traffic from column j to j+1. Bits at
column j come only from the original n_j, carries A_{j−1}, and sum outputs
A_j; balancing gives the conservation law

    m_j + 2F_j + H_j = n_j + A_{j−1}        (m = final shape).

Writing r_j = 2F_j + H_j — which is exactly column j's contribution to the
cost — every legal schedule of every depth satisfies the four constraints
`n_j + c_j ≤ r_j + 2`, `r_j ≤ n_j + c_j`, `⌈r_j/2⌉ ≤ c_{j+1} ≤ r_j`,
`c_0 = c_w = 0`, where c_j = A_{j−1}. All timing information is gone.
`greedyCost` folds the pointwise-cheapest solution of this system (pay
`max(0, n_j + c_j − 2)`, forward the minimal carry `⌈r/2⌉`), and a short
induction shows it **dominates every feasible solution**: from a smaller
carry, greedy pays less at the column *and* its carry-out stays smaller, so
the advantage propagates. Hence `greedyCost n ≤ S.cost` for every schedule
on every shape (`cost_lower_bound`).

**Half 2 — Dadda pays exactly the greedy value on partial-product heaps.**
Dadda's schedule is analyzed through two structural facts.

*The trapezoid invariant.* After the Dadda stage with target t on the k×k
heap, the shape is exactly

    1, 2, …, t−1,   t, t, …, t,   t−2, t−3, …, 1
    └── ramp ──┘   └ 2k−2t+2 ┘    └── tail ──┘

For example, k = 4: `1 2 3 4 3 2 1 → 1 2 3 3 3 3 1 → 1 2 2 2 2 2 2`.

*The tally telescope.* Dadda's total cost is summed column-wise rather than
stage-wise. Within one column, a stage's spend is
e = (height before) + (carry-in) − (height after), so summing over stages the
heights cancel in pairs, leaving

    total spend at column j = initial − final + Σ carry-ins.

The carry-ins have a single closed form (§4), and summed over the target
ladder they tile an interval — independently of where the ladder's floor
function places the individual targets. The result equals the greedy
payment at column j, pointwise. Chaining the halves proves the theorem.

The conceptual takeaway: under the cost metric, a compressor tree is not
really a scheduling object but a **flow network** — each column forwards
⌈excess/2⌉ carries upward and pays for what it destroys — and Dadda's
level-by-level ladder is one particular way of routing the unique cheapest
flow. That is *why* a sixty-year-old heuristic is exactly optimal.

## 4. Proof, in detail

**Conservation (`stage_balance`, `run_balance`).** For a legal stage,
`(s.apply n)[j] + (2·fa_j + ha_j) = n[j] + (fa+ha)[j−1]` — exact even over
truncated Nat subtraction, because legality bounds consumption. Folding over
the schedule gives the tally identity (†) above. Proof: induction over the
stage list; each step is `omega`.

**The chain abstraction (`TallyChain`, `costDP…`→`greedyCost_le_chain`).**
`TallyChain cols c rs` packages the four constraints as an inductive
predicate over the column list. `chain_from` shows any legal, compressing
schedule induces a chain from its tallies (the MSB rule closes the final
carry), and `tallyList_sum` shows the chain's total is the schedule's cost —
a sum interchange. The greedy dominance lemma is ten lines: if ĉ ≤ c then
`max(0, h+ĉ−2) ≤ r` by the chain's cap constraint, and
`⌈max(0, h+ĉ−2)/2⌉ ≤ ⌈r/2⌉ ≤ c'`, so the invariant "greedy's carry ≤ chain's
carry" self-propagates and the costs compare term by term. Greedy's final
carry is 0 *for free* — it sits below the chain's, which ends at 0.

**One carry formula (`carry_trap`, `carry_pp`).** Every carry trajectory in
the development — each Dadda stage, and the greedy fold itself (which is the
"stage with target 2") — satisfies

    carryIn t X j = min( min(j − t, P − t), (2k+1−t) − j )

where P is the profile height of X (the previous target for a trapezoid, k
for the partial-product heap). The carry ramps up linearly from column t,
saturates at P−t across the plateau, and ramps down near the MSB end; the
Nat-truncated formula is valid for *all* j, including padding columns, where
it evaluates to 0. Proof: induction on j; each step substitutes the shape's
height formula and closes with `omega` (which handles ⌈·/2⌉, min, and
truncated subtraction natively).

**The trapezoid step (`stage_apply_trap`, `stage_apply_pp`).** The raw
per-column effect of a Dadda stage is `n_j − e_j + c_j` with
e_j = n_j + c_j ∸ t; substituting the carry formula and splitting on the
trapezoid's regions shows the result is precisely the next trapezoid. The
tameness side condition (carries never exceed the target, needed for
exactness of the truncated subtraction) is discharged by t′ ≤ 2t, which the
Dadda ladder satisfies since ⌊3t/2⌋ ≤ 2t.

**The telescope (`go_tally`, `dadda_tally_pp`).** By induction over the
target ladder: the tallies of the cascade starting at the t-trapezoid equal

    trapH k t j + ( min( min(j, 2k+1−j), t ) − 2 )  −  trapH k 2 j.

The inductive step adds one stage's spend e_j to the induction hypothesis and
must produce the same expression one target higher — this is the interval
identity `min(J,t)−2 + (piece for [t,t′)) = min(J,t′)−2`, and it holds for
*any* increasing ladder, which is why the Dadda sequence's floors never enter
the argument. Every case is `split_ifs <;> omega`. Instantiated at the top
(profile k, first stage from `ppShape`), the total tally at column j is
`pp_j + (min(J,k)−2) − trapH k 2 j` — exactly the greedy fold's payment
(`greedy_eq_sum` + the carry formula at t = 2). Summing over columns closes
`dadda_le_greedy_pp`, and with Half 1, the theorem.

**Degenerate cases.** For k ≤ 2 the heap is already two rows: Dadda's ladder
has zero levels, its schedule is `[]`, and cost 0 is trivially optimal. This
is proved directly (not by evaluation), keeping the whole chain kernel-pure.

## 5. Why this metric, and why the heap shape matters

Both hypotheses of the theorem are necessary, and the development proves it:

- **Cost, not FA count.** By the conservation law, FAs are the only bit
  destroyers, so "minimize FAs" is the same as "maximize surviving bits" —
  which a competitor can game by parking excess bits in spare columns using
  HA chains that the FA metric doesn't charge for. The cost metric
  2·#FA + #HA charges for exactly that traffic, and it is the combination
  under which cost is a function of column totals alone.
- **Partial-product heaps, not arbitrary ones** (`dadda_not_cost_optimal`,
  machine-checked). On a single column of height 6, two FAs finish in one
  level ([6] → [2,2], cost 4) while Dadda walks its ladder for cost 5.
  Dadda's fixed target ladder is tuned to the taper of multiplier heaps;
  on degenerate shapes it wastes work. Padded *rectangles* also beat Dadda,
  so the taper — not mere fullness — is essential.

## 6. Scope, trust, and provenance

- **Trusted base.** Lean 4 kernel; axioms `propext`, `Classical.choice`,
  `Quot.sound`. No `sorry` anywhere; the main theorem's chain uses no
  `native_decide` (only the §5 counterexample does). ~850 lines over the
  project's existing `DaddaTree` definitions (`DaddaSequence`,
  `findDaddaLevel`).
- **Abstraction boundary.** The theorem lives at the shape level. It governs
  every compressor tree built from FAs and HAs under standard level
  semantics, but it does not (yet) connect to the project's executable
  bit-heap implementation (`DaddaTree.DaddaTree` on `BitHeap`, which is
  `partial` and reasons about named circuit signals); that refinement is
  future work, as is extending the stage alphabet beyond FA/HA (e.g. 4:2
  compressors), where the optimality question reopens.
- **Provenance of the argument.** The proof was found by refutation-first
  exploration: exhaustive search over the schedule space for small k
  refuted the FA-count folklore, identified the cost metric as the robust
  objective, and produced the trapezoid invariant and carry formulas as
  conjectures — each validated computationally (all stages, k ≤ 40, and
  general target pairs) before formalization. The earlier level-budgeted
  results (a verified bounded-model-checking pass for fixed k) were strictly
  subsumed by the level-free argument and removed.

## 7. A step-by-step walkthrough

This section retells the proof in plain language, in the order the Lean file
builds it. It says the same things as §3 and §4, but slowly, and it assumes
you have not memorized the notation.

The overall shape is a sandwich. We define a simple number, the *greedy
cost*, that depends only on the starting heap. Steps 1 through 4 show that no
schedule whatsoever can cost less than this number. Steps 5 through 9 show
that Dadda's schedule costs exactly this number on a multiplier heap. Step 10
puts the two together, and optimality falls out.

### Steps 1–4: nobody can beat the greedy cost

**Step 1. Follow the bits through one level.** Pick a single column and a
single level of the tree. Some bits are sitting in that column when the level
begins. The adders placed there eat some of those bits and hand back a sum
bit each, so on balance a full adder removes two bits from the column and a
half adder removes one. Meanwhile the column below has been running its own
adders, and each of them — full or half — throws exactly one carry bit
upward into our column.

Bits do not appear or vanish for any other reason, so the books have to
balance: what the column is left holding, plus what it destroyed, equals what
it was holding to begin with, plus the carries it received. This is proved as
`stage_balance`. The bookkeeping is done in the natural numbers, where
subtraction truncates at zero, so the identity could in principle be spoiled
by a column trying to consume more bits than it has — but the legality
condition forbids exactly that, which is why the equation is exact rather
than an inequality.

**Step 2. Add up all the levels.** Now stop looking at one level and add the
step-1 equation over the entire schedule. The intermediate heights telescope
away: the height a column ends one level at is the height it starts the next
level at, so all of them cancel except the first and the last. What remains
mentions only the heap we started from, the heap we finished with, and the
*grand totals* of adders placed in each column over the whole run.

This is the crucial move, proved as `run_balance`. The statement that comes
out no longer mentions levels at all. It does not care whether the schedule
took three levels or three hundred, or in what order it did anything. From
here on, a schedule is just a table of column totals.

**Step 3. Write down what those totals must satisfy.** Reading off step 2,
together with the requirement that the schedule actually finishes (every
column ends at height two or less) and the rule that nothing may be placed in
the top column, we get four simple facts relating each column's total spend
to the carries flowing between neighbors. A column cannot spend more than the
bits available to it; it must spend enough to get down to two; and the
carries it sends up are at least half its spend and at most all of it.

We package those four facts as a `TallyChain`, and `chain_from` proves that
every legal, finishing schedule gives rise to one. A separate accounting
lemma, `tallyList_sum`, checks that adding up a chain's per-column spends
reproduces the schedule's cost exactly — the chain has not thrown away the
quantity we care about, it has only forgotten the timing.

**Step 4. The cheapest chain is the obvious one.** Given the constraints of
step 3, what is the least a chain can cost? The natural guess is to be as
stingy as possible at every column, starting from the least significant and
working upward: spend only what you must to reach height two, and forward
only the minimum number of carries that the spend forces. That greedy walk is
`greedyCost`. It has to run in that direction, because carries travel from a
column to its more significant neighbor, so a column can only be settled once
everything feeding it has been.

Greedy is genuinely optimal, and the reason is a small piece of luck. Suppose
greedy arrives at some column carrying fewer bits in than a rival chain does.
Then greedy has less to clean up, so it pays less at that column — and
because it paid less, it also sends fewer carries onward. Its advantage is
not spent, it is preserved into the next column. So a single induction along
the columns, carrying the invariant *greedy's carry is never larger than the
rival's*, compares the two costs term by term. This is
`greedyCost_le_chain`, and combined with step 3 it gives `cost_lower_bound`:
**every** schedule that reduces a heap costs at least that heap's greedy
cost.

Half the sandwich is now done, and note how little was assumed. The rival
schedule may use any number of levels and any arrangement of adders. It never
had to be reasonable.

### Steps 5–9: Dadda hits the greedy cost exactly

The other half is a computation. We need Dadda's actual cost on a multiplier
heap, in closed form, and it must come out equal to the greedy number.

**Step 5. Notice the shape Dadda leaves behind.** Run Dadda by hand on a
multiplier heap and the intermediate heaps are always the same kind of
figure: heights climbing 1, 2, 3, … up to the current target, then a flat
plateau at the target, then a short descent to 1 at the top end. We call it a
trapezoid and define its height profile as `trapH`. This is the invariant the
rest of the computation hangs on.

**Step 6. Work out where the carries go.** To push the invariant through one
level we need to know, for every column, how many carries arrive from below.
On a trapezoid this turns out to have a clean description: near the bottom
the carry count climbs by one per column, then it flattens out at a value
determined by the profile height, then it falls off again as the heap tapers
toward the top. One formula built from two `min`s captures all three regions
at once, and it stays correct in the padding columns above the heap, where it
simply evaluates to zero.

This is `carry_trap` (and `carry_pp` for the original heap). Each is proved
by induction on the column index; every individual step is arithmetic that
`omega` settles on its own, including the halving, the `min`s, and the
truncated subtraction.

**Step 7. Check the invariant survives a level.** With the carry formula in
hand, apply one Dadda level to a trapezoid and compute the resulting heights
region by region. The answer is the next trapezoid down — `stage_apply_trap`
— and applying the very first level to the multiplier heap produces the first
trapezoid, `stage_apply_pp`. There is one side condition: the arithmetic is
only exact if the carries never overrun the target, which holds because
consecutive Dadda targets satisfy `⌊3t/2⌋ ≤ 2t`.

**Step 8. Add up Dadda's cost the other way round.** Dadda is defined level
by level, so the obvious way to total its cost is level by level too. Doing
it column by column is much better. Within one column, what a level spends is
just its height before, plus its carry-in, minus its height after. Sum that
over all levels and the heights cancel in pairs exactly as they did in step
2, leaving only the initial height, the final height, and the sum of all the
carry-ins — and step 6 already told us every one of those carry-ins.

Summing the carry formula over the target ladder is where a pleasant surprise
appears. The individual pieces tile an interval, and the tiling identity holds
for *any* increasing sequence of targets. Dadda's particular ladder, with its
floor function `⌊3t/2⌋`, never has to be analyzed at all — only the fact that
it increases. This is `go_tally`, lifted to the real heap by
`dadda_tally_pp`.

**Step 9. Compare with greedy.** Now evaluate the greedy walk of step 4 on
the multiplier heap. Greedy is nothing more exotic than a Dadda level whose
target happens to be two, so the very same carry formula from step 6 applies
to it, and `greedy_eq_sum` turns the fold into a sum of per-column payments.
Set the two closed forms side by side and they agree column by column. Adding
over the columns gives `dadda_le_greedy_pp`: Dadda's cost on a k×k heap is
its greedy cost.

### Step 10: put the halves together

For any schedule `S` that reduces the k×k partial-product heap, step 9 says
Dadda's cost equals the greedy cost, and step 4 says the greedy cost is at
most `S`'s cost. Chaining them gives `dadda.cost ≤ S.cost`, which is
`dadda_cost_optimal_pp_anyWidth`.

Small multipliers need a word of their own. When k is 2 or less the heap is
already two rows tall, Dadda's schedule is the empty list, and its cost is
zero, which nothing can beat. That case is argued directly rather than by
asking Lean to evaluate anything, so the whole chain stays kernel-checkable.
