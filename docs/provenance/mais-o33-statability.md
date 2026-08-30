# Reading MAIS issue #9's candidate for MAIS-O33, clause by clause

MAIS-O33 (`prob:corruption`, MAIS-A2 Problem 4.12 in the pinned source; see
[`mais-source-pin.md`](mais-source-pin.md)) is answered; the result is in
[`mais-o33-refutation.md`](mais-o33-refutation.md) and the row is `CONJ-023`.

**This note is the reading audit that preceded the check**, and it is kept
because that is a different thing from a machine-check and is worth having on the
record: it is one reader going through the candidate negative resolution
submitted as MAIS issue [#9](https://github.com/lionellevine/MAIS/issues/9),
clause by clause, against the pinned agenda. It found no error in the argument.
It is a triage by one reader, not a referee report, and it is not a check —
nothing in it is verified by the build.

It was written before the goal layer existed, so its estimates of what the row
would cost are superseded by what was actually built; where a clause below
records a cost or a blocker, read it as the estimate at the time of reading. The
two that mattered are named in the refutation note: the congruence lemma for
`ProbabilityTheory.Kernel.traj` turned out to be unnecessary at an
action-independent instance, and the history reading recorded below as safe is
not safe and is closed by proof instead.

## The verdict

**The candidate is sound, and its reading of print is print's own.** What stood
between the row and a statement was not the argument but the vocabulary:
`prob:corruption` is stated over the goal-based setting of
Richens–Abel–Bellot–Everitt, and at the time of this reading the repository had
no goal layer at all. The three objects the row needs — composite goals,
goal-conditioned agents, first-action maps — were each judged statable, and all
three were then built, in `AISafetyAtlas.Causal.Goal`,
`AISafetyAtlas.Causal.GoalDynamics` and `AISafetyAtlas.Causal.Corruption`.

Two findings lower the estimate from where `CONJ-023`'s `blocked_on` had it.
Mathlib carries Ionescu–Tulcea (`ProbabilityTheory.Kernel.traj`), so the measure
on infinite trajectories that *"eventually"* goals need is a dependency rather
than a project. And the candidate's argument does **not** need the hardest thing
it appears to need; see *The `δ = 0` trap* below.

## What print asks for

Read from `agendas/A2/MAIS-A2.tex` at the pin. A **sub-goal** is `α = (op, 𝐠)`
with `𝐠 ⊆ 𝐒 × 𝐀` and `op ∈ {⊤, ○, ◇}` (*Now*, *Next*, *Eventually*), with an
achievement time on a trajectory. A **sequential goal** `ψ = ⟨α₁,…,α_k⟩` is
satisfied when `α₁` has finite achievement time `T` and the trajectory shifted
past `T` satisfies `⟨α₂,…,α_k⟩`; its **depth** is `k`. A **composite goal** is a
finite disjunction of sequential goals,

> identified semantically with its set of disjuncts as in the Conventions block;
> its depth is the maximum over disjuncts.

so `𝚿_n`, the composite goals of depth at most `n`, is the set of **finite sets**
of sequential goals of depth `≤ n`. With `Q` sequential goals available that is
`2^Q − 1` composite goals. A **goal-conditioned agent** is a deterministic map
from (history, goal) pairs to actions, and is `(δ,n)`-bounded when

    P(τ ⊨ ψ | π, s₀) ≥ (1 − δ) · max_{π'} P(τ ⊨ ψ | π', s₀)

for every `ψ ∈ 𝚿_n` and every start state. All analyst-visible data is the
first-action map `f_π : 𝐒 × 𝚿_n → 𝐀`.

`prob:corruption` then asks for the supremum `η*` of the uniformly tolerable
persistent-corruption fractions, and whether it is positive.

## Clause by clause

**Amended 2026-08-30.** The syntax and the trajectory semantics are no longer
absent: `AISafetyAtlas.Causal.Goal` carries them, and with them the candidate's
Lemma 2. The table below is updated; the probabilistic half is what is left.

| Clause | Statable? | Rests on | Present |
|---|---|---|---|
| Sub-goals, `op ∈ {⊤,○,◇}`, `𝐠 ⊆ 𝐒 × 𝐀` | yes | `Finset` over a product of fintypes | `SubGoal` |
| Sequential goal, recursive satisfaction with a shift | yes | `List` plus a shift on trajectories | `Satisfies` |
| Composite goal = **set** of disjuncts, depth = max | yes | `Finset` of sequential goals | `CompositeGoal` |
| `𝚿_n` finite | yes | fintype of bounded-depth lists | `compositeGoals`, `card_compositeGoals` |
| the counting bound on goals with no immediate win | yes | `Finset` powerset arithmetic | `card_compositeGoals_avoiding`, `exceptional_ratio_lt` |
| finite communicating stationary cMP | yes | a stochastic matrix per action | `ControlledMarkovProcess`, `Communicating` |
| the two separated kernels, and disjoint balls | yes | elementary arithmetic | `Examples.Causal.ControlledProcess` |
| `P(τ ⊨ ψ | π, s₀)`, all three operators | yes | `ProbabilityTheory.Kernel.traj` (Ionescu–Tulcea), with `X n = 𝐒` because a deterministic policy leaves only the transitions to chance | `trajectoryLaw`, `achieveProb` |
| `max_{π'}` over policies | **as written, no** | attainment of the supremum over policies on a finite cMP. See below | `optimalProb`, as `⨆` |
| `(δ,n)`-bounded agent | yes, as `⨆` | the above | `IsDeltaBounded`, shown inhabited |
| first-action map `f_π` | yes | function out of `𝐒 × 𝚿_n` | `firstActionMap` |
| `η`-corruption: one **fixed** `ρ` within `η·|𝐒 × 𝚿_n|` of `f_π` | yes | Hamming count on a fintype | — |
| randomized adaptive analyst with a query budget | yes | a probability measure on outputs, given oracle access | — |
| the reconstruction target and `2/3` success | yes | sup-norm on kernels | — |

Nothing here is *unstatable*. Every row without a checkmark is work, not a
blocker of the kind `CONJ-018`–`CONJ-024` mostly record.

## The `δ = 0` trap, and why the candidate does not fall into it

Print writes `\max_{\pi'}`, which **presupposes** the supremum over policies is
attained. That presupposition is not free: for *Eventually* goals it is the
statement that optimal deterministic policies exist for reachability objectives
on a finite controlled Markov process — true, standard, and absent from Mathlib.
A faithful transcription would render `max` as `⨆` and record the presupposition
rather than assume it, which is the same presupposition-versus-precondition
pattern `CONJ-003`'s retired sibling records.

Issue #9 takes `n = 101` and **`δ = 0`**. At `δ = 0` the bound reads
`P(τ ⊨ ψ | π, s₀) = ⨆_{π'} …`, so the two agents it constructs must be *exactly*
optimal at every one of the `|𝐒| · (2^Q − 1)` pairs, and the attainment theorem
is unavoidable.

**It is avoidable, and print allows the avoidance.** `prob:corruption`
quantifies over every finite instance with `|𝐀| ≥ 2`, `n > 1` and
`(n−1)(1−δ) > 4`; the candidate needs `δ = 0` for nothing except the arithmetic
of the reconstruction radius. Take `δ = 1/2` and `n = 101`:

- `(n−1)(1−δ) = 50 > 4`, so the instance is admissible;
- `τ = 2/√((n−1)(1−δ)) = 2/√50 = 0.2828…`, so the two required balls are
  disjoint as soon as `‖P⁰ − P¹‖_∞ > 2τ = 0.5657…`, and the candidate's kernels
  are `0.8` apart;
- the uncorrupted endpoint still clears: the cited extraction bound is
  `√(2/((n−1)(1−δ))) = 0.2 ≤ τ`.

At `δ > 0` no attainment is needed. For each `(s₀, ψ)` pick a deterministic
policy within a factor `(1−δ)` of the supremum — ordinary `⨆`-approximation,
`exists_lt_of_lt_csSup` — and splice the choices, which is legitimate because a
goal-conditioned agent reads the goal *and* recovers `s₀` from the history. At
the pairs the counting lemma covers, the supremum is `1` and is attained by
playing `a*`, so the prescribed first action survives the splice. The spliced
agent is `(1/2, n)`-bounded by construction, which also makes `A(E,n,δ)`
provably nonempty — something the `δ = 0` reading cannot claim without the
attainment theorem either.

**Same conclusion, one large dependency less.** The atlas should run the
candidate at `δ = 1/2`.

## The counting, machine-checked

Issue #9's Lemma 2 is the load-bearing combinatorial claim, and it is correct as
stated. Since 2026-08-30 it is checked rather than read:
`AISafetyAtlas.Causal.card_compositeGoals_avoiding` and
`AISafetyAtlas.Causal.exceptional_ratio_lt`. Fix `a* ∈ 𝐀` and a start state `s`. The depth-one *Now* goals
`⟨(⊤, 𝐠)⟩` with `(s, a*) ∈ 𝐠` number

    R = 2^{|𝐒||𝐀| − 1},

since a subset of `𝐒 × 𝐀` containing one fixed pair is a subset of the rest.
Any composite goal containing one of these as a disjunct is achieved with
probability `1` by playing `a*` at `s`, **in every environment**, because a
*Now* condition reads `(s₀, a₀)` and never the kernel. Of the `2^Q − 1` nonempty
subsets of the `Q` sequential goals, those meeting none of the `R` number
`2^{Q−R} − 1`, so the exceptional fraction at `s` is

    c_R = (2^{Q−R} − 1)/(2^Q − 1) < 2^{Q−R}/2^{Q−1} = 2^{1−R},

and averaging the same bound over `s` gives the normalized Hamming bound. With
`|𝐀| = 2` and `|𝐒| = m` this is `2^{1 − 2^{2m−1}}`, below any `η > 0` once
`m ≳ ½ log₂(1 + log₂(1/η))` — doubly exponential, which is why the construction
has room to spare.

**This is where the "all subsets" reading earns its keep.** Under a reading in
which a composite goal is a disjunction of at most `n` sub-goals, `|𝚿_n| ≈ Q^n`
and the exceptional fraction is `((Q−R)/Q)^n`, which is not small. The candidate
flags the sensitivity in its own scope paragraph; the pinned agenda settles it in
the candidate's favour, in the sentence quoted above.

## Three readings, recorded rather than assumed

The layer built so far makes three choices print does not force. All three are
now written into the modules; two are harmless in a direction that can be
stated, and one is closed by proof.

**1. The history carries states only. — Corrected 2026-08-30: the argument
below is wrong, and the axis is now closed by proof.** Print's history is the
trajectory prefix `(s₀, a₀, …, s_t)` — states *and* actions — and
`Causal.GoalDynamics.GoalHistory` carries the states.

~~The direction is what makes this safe here. Every `GoalPolicy` is realized by
a full-history policy, so the agents admitted are a sub-collection of print's,
and `prob:corruption`'s adversary chooses from print's larger one. A larger
agent class only makes uniform tolerability harder, so `η*` over print's class
is at most `η*` over this one.~~

That compares agent *classes* and forgets that the boundedness threshold moves
with them. `(δ,n)`-boundedness is `P(π) ≥ (1−δ)·max_{π'} P(π')`, and if
trajectory-prefix policies could achieve more than state policies, the printed
threshold would be higher and a state policy near-optimal among state policies
need not be in print's `A(E,n,δ)` at all. The refutation's witnesses would then
not be print's agents, and nothing would transfer.

**They cannot achieve more, and this is now proved.**
`AISafetyAtlas.Causal.FullPolicy` is print's type;
`AISafetyAtlas.Causal.inducedPolicy` computes the action a trajectory-prefix
policy takes as a function of the states, by running the same rule at earlier
times; `AISafetyAtlas.Causal.liftPolicy` embeds back and
`inducedPolicy_liftPolicy` says the round trip is the identity. Hence
`AISafetyAtlas.Causal.optimalProbFull_eq`: the two suprema are equal, so
`isDeltaBoundedFull_lift_iff` makes the two boundedness clauses select the same
agents and `firstActionMapFull_lift` makes them show the analyst the same data.

**2. The empty disjunction is excluded from `𝚿_n`.** Print writes *"a finite
disjunction of sequential goals"* and does not settle whether zero disjuncts
count; the candidate treats both. `compositeGoals` excludes it, giving
`2^Q - 1`. **Closed by proof**: `exceptional_ratio_lt_with_empty` shows the
counting bound survives the other reading, where the count is `2^Q` and the
fraction is `2^{-R}` rather than `2^{1-R}` — on one hypothesis fewer. The choice
changes the count and not the conclusion.

**3. `max` becomes `⨆`.** Discussed under *The `δ = 0` trap* above. The two
readings agree wherever print's presupposition holds, and diverge only at
`δ = 0`, which is the reason for running at `δ = 1/2`. Since `⨆ ≥ max`, the
sup-reading selects a *sub-collection* of print's `A(E,n,δ)`, so a refutation
quantified over it is the stronger result — which is the direction argument
reading 1 failed to make.

## The rest of the argument

Given the layer, what remains is elementary and needs no query complexity:

- two kernels agreeing off the row `(0,b)`, `0.1` against `0.9` there and mass
  `0.9/(m−1)` against `0.1/(m−1)` spread over the other states — rows sum to `1`,
  every entry positive, hence communicating, and `‖P⁰ − P¹‖_∞ = 0.8`;
- `ρ = f¹` is an admissible `η`-corruption in **both** worlds — distance `0` in
  one, below `η` in the other by the counting lemma;
- every query returns the same answer in both worlds, so a randomized adaptive
  analyst has one output law `μ`, and uniform success would need
  `μ(B₀) ≥ 2/3` and `μ(B₁) ≥ 2/3` for disjoint `B₀, B₁`.

No query bound is used, so the polynomial budget is irrelevant: this is
indistinguishability, not query complexity. The `η = 0` endpoint is the cited
extraction theorem.

## What the atlas would have to build

Named so the absence is checkable rather than asserted:

- ~~`AISafetyAtlas.Causal.SequentialGoal` and
  `AISafetyAtlas.Causal.CompositeGoal`, with achievement times and the shift~~ —
  landed 2026-08-30 in `AISafetyAtlas.Causal.Goal`;
- ~~`AISafetyAtlas.Causal.ControlledMarkovProcess`~~ — landed 2026-08-30, with
  the candidate's own two kernels worked out and their reconstruction balls
  shown disjoint at `n = 101`, `δ = 1/2`;
- ~~the trajectory law, the `(δ,n)`-bounded predicate over `⨆`, and the
  first-action map~~ — landed 2026-08-30 in `AISafetyAtlas.Causal.GoalDynamics`;
- ~~**one lemma**: that `trajectoryLaw` at a start state depends on the policy
  only through its values on histories beginning there~~ — **Corrected
  2026-08-30: not needed.** The estimate assumed the environments had to be the
  candidate's, whose kernels read the action. On an **action-independent**
  environment — print's own class, the one its myopic converse is stated over —
  `AISafetyAtlas.Causal.trajectoryLaw_congr` makes the trajectory law *the same
  measure* for every policy, and the splice goes through unconditionally
  (`AISafetyAtlas.Causal.exists_isDeltaBounded_prescribing`). A congruence lemma
  for `ProbabilityTheory.Kernel.traj` would be needed again for a family whose
  transitions read the action, which is what `CONJ-022`/MAIS-O32 is about;
- ~~`AISafetyAtlas.Causal.PersistentAdversary` and
  `AISafetyAtlas.Causal.succeedsWithProbability`~~ — **Corrected 2026-08-30:
  landed** as `AISafetyAtlas.Causal.IsCorruption`,
  `AISafetyAtlas.Causal.FirstActionStrategy`,
  `AISafetyAtlas.Causal.FirstActionEstimator`,
  `AISafetyAtlas.Causal.runFirstActionTranscript` and
  `AISafetyAtlas.Causal.Succeeds`, none of them under the names this note
  guessed.

The trajectory measure is a Mathlib import. The attainment theorem is **not**
required if the row runs at `δ > 0`, and is required if it insists on print's
`max` at `δ = 0`; that choice is the one real fidelity decision in the layer, and
it should be made in the open rather than by whichever `δ` a candidate happened
to pick.

## Credit

The construction, the counting lemma, the two kernels and the indistinguishability
step are MAIS issue [#9](https://github.com/lionellevine/MAIS/issues/9)'s —
Svyatoslav Novikov (kumino), generated by OpenAI Codex, 2026-08-04, offered under
CC BY 4.0, with no human referee review claimed. This note is an audit against
the pinned agenda, not a machine-check, and it found no error to report.

The impossibility theorem is proved elsewhere —
`AISafetyAtlas.Examples.Conjectures.MAIS.not_uniformlyTolerable`, on the witness
`AISafetyAtlas.Examples.Causal.O33Corruption.exists_not_tolerantAt` — by a proof
that follows this candidate's strategy at a *different* instance. So what the
build checks is the candidate's **claim** and not its proof, and this note is the
only thing in the tree that engaged with the proof at all. See
[`mais-o33-refutation.md`](mais-o33-refutation.md).
