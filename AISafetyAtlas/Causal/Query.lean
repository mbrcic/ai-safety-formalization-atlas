module

public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Causal.MarginClass
public import AISafetyAtlas.Causal.ModelSpace
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
public import Mathlib.Data.ENat.Lattice

/-!
# The query model of MAIS-A2 `subsec:queries`

MAIS-A2 fixes one interaction protocol that all of its query problems (O25, O2,
O35) quantify over, and states it once. This module is that protocol, and it is
built to the printed sentences rather than to what is convenient downstream.

Four printed commitments drive the shapes here:

* **Queries carry rational weights, tables are real.** *"the `t`th query is a
  triple `(σ_t, 𝐎'_t, w_t)` with **rational** mixture weights"*, while
  `def:margin`'s tables are real. So a query is a rational object acting on a
  real model; `ShiftedQuery` keeps `ProbMixture C dim ℚ` and meets the value
  field through `ProbMixture.mapRat`. Widening the weights would state a problem
  the source does not pose.
* **The analyst may randomize.** *"the infimum over **(randomized)** analyst
  strategies"*. A deterministic strategy is a special case, and randomization
  genuinely lowers minimax risk, so a deterministic-only infimum is a different
  quantity.
* **The error is averaged, then maximized.** *"the infimum … of the supremum,
  over models in the class and admissible adversaries, of the **expected**
  error"*. Expectation is over the analyst's randomization only — the oracle is
  the policy-probability one, whose answers are exact.
* **The risk is an infimum, not an existential.** A budget is feasible when the
  *infimum* is at most `ε`. Reading it as "some strategy achieves `≤ ε`" is
  strictly stronger whenever the infimum is not attained.

Randomization is rendered in behavioural form — a distribution over the next
query given the transcript so far — rather than as a distribution over whole
deterministic strategies. Both are standard and agree under **perfect recall**,
which is why the transcript records the analyst's own queries and not only the
answers: an analyst that forgets what it played does not have perfect recall,
the two forms come apart, and the behavioural reading would then be a genuine
restriction rather than a presentation choice. With the queries recorded, the
behavioural form is the literal reading of *"the analyst **adaptively** issues
queries"*, and it is the one `PMF.bind` builds directly.

Nothing here is a conjecture. MAIS-O25 and MAIS-O26 are both phrased in this
layer. O26's class is cut by MAIS-O24's polynomial list, which
`Causal.O24Solution` supplies; a rational stand-in for it would be a different
statement.

**One rendering here looked like a live scope axis and is now proved not to
be.** `RandomizedEstimator` returns a `PMF`, so an analyst's output law is
countably supported, while `subsec:queries` says only that the analyst *"outputs
`(Ĝ, θ̂)`"* and the model space is uncountable. That shrinks the set the infimum
ranges over, so a priori `exactMinimaxRisk` and `exactMinimalBudget` could only
rise, and any finite upper bound stated over them would be **stronger** than
print's.

They do not rise. `measureMinimaxRisk` is the same definition over **arbitrary**
probability measures on the model space, and the two agree —
`measureMinimaxRisk_eq_exactMinimaxRisk`. So does `N(ε)`,
`measureMinimalBudget_eq_exactMinimalBudget`, which is the quantity MAIS-O25 and
MAIS-O26 are actually stated over.

The argument is the one `AISafetyAtlas.Causal.ModelSpace` sets up. The printed
error is `1`-Lipschitz in the estimate at a fixed graph, so rounding an estimate
onto a grid of spacing `ε` moves the error by `O(ε)`
(`modelError_roundDown_le`), and rounded models form a **countable** set
(`countable_range_roundDown`), which is exactly what a `PMF` can be supported
on. `MeasureEstimator.discretize` performs that rounding, so every measure
estimator has a `PMF` estimator within `O(ε)` of it. Since the risk is an
infimum and `ε` is arbitrary, the two infima agree. Only the one-sided bound is
used; `modelError_roundDown_le` proves the two-sided form and the other half is
not needed.

What this does **not** say is that the two estimator classes are in bijection,
or that a given measure estimator has a `PMF` equivalent at equal risk. Neither
is true, and neither is claimed: the statement is about the infima.

The *query* side carries no matching restriction, and that is now a theorem
rather than a remark. `instCountableShiftedQuery` proves the query type is
countable — print's *"rational mixture weights"* is what makes it so — and on a
countable type every probability measure is countably supported, so
`PMF (ShiftedQuery sk)` is already the general object. `def:local`'s simplex of
**all** mixtures is what the policy family is indexed by.
-/

namespace AISafetyAtlas.Causal

open scoped ENNReal

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [CharZero 𝕜]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {dim : C → ℕ}

/-! ## Expectation against a `PMF`

`PMF α` is a subtype of `α → ℝ≥0∞` for an arbitrary `α`, so it needs no
measurable structure on the strategy or transcript spaces. That is why the
expectation below is a `tsum` rather than a Bochner integral: the analyst's
randomization lives on types (queries, models) that carry no σ-algebra and do
not need one. -/

/-- The expected value of a real function against a probability mass function. -/
public noncomputable def pmfExpect {α : Type*} (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑' a, (p a).toReal * f a

@[simp] public theorem pmfExpect_pure {α : Type*} (a : α) (f : α → ℝ) :
    pmfExpect (PMF.pure a) f = f a := by
  unfold pmfExpect
  rw [tsum_eq_single a]
  · simp
  · intro b hb
    simp [PMF.pure_apply, hb]

/-! ## An expectation toolkit

`pmfExpect` is a `tsum` in `ℝ`, so monotonicity is not free the way it would be
in `ℝ≥0∞`: `tsum_le_tsum` wants summability on both sides. Every function pushed
through it below is bounded — the printed error is bounded by `1` — so these
lemmas take an explicit bound rather than trying to be general. -/

/-- A `PMF`'s masses sum to `1` as reals. -/
public theorem hasSum_pmf_toReal {α : Type*} (p : PMF α) :
    HasSum (fun a ↦ (p a).toReal) 1 := by
  have hne : ∀ a, p a ≠ ⊤ := fun a ↦ PMF.apply_ne_top p a
  have hsum : ∑' a, (p a : ℝ≥0∞) ≠ ⊤ := by
    rw [p.tsum_coe]; exact ENNReal.one_ne_top
  have h := ENNReal.hasSum_toReal hsum
  rwa [← ENNReal.tsum_toReal_eq hne, p.tsum_coe, ENNReal.toReal_one] at h

public theorem summable_pmfExpect {α : Type*} (p : PMF α) {f : α → ℝ} {C : ℝ}
    (hf : ∀ a, |f a| ≤ C) : Summable fun a ↦ (p a).toReal * f a := by
  refine Summable.of_norm_bounded ((hasSum_pmf_toReal p).summable.mul_right C) fun a ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hf a) ENNReal.toReal_nonneg

@[simp] public theorem pmfExpect_const {α : Type*} (p : PMF α) (c : ℝ) :
    pmfExpect p (fun _ ↦ c) = c := by
  unfold pmfExpect
  rw [tsum_mul_right, (hasSum_pmf_toReal p).tsum_eq, one_mul]

public theorem pmfExpect_mono {α : Type*} (p : PMF α) {f g : α → ℝ} {C : ℝ}
    (hf : ∀ a, |f a| ≤ C) (hg : ∀ a, |g a| ≤ C) (h : ∀ a, f a ≤ g a) :
    pmfExpect p f ≤ pmfExpect p g :=
  Summable.tsum_le_tsum (fun a ↦ mul_le_mul_of_nonneg_left (h a) ENNReal.toReal_nonneg)
    (summable_pmfExpect p hf) (summable_pmfExpect p hg)

public theorem pmfExpect_add_const {α : Type*} (p : PMF α) {f : α → ℝ} {C : ℝ}
    (hf : ∀ a, |f a| ≤ C) (c : ℝ) :
    pmfExpect p (fun a ↦ f a + c) = pmfExpect p f + c := by
  unfold pmfExpect
  have hsplit : ∀ a, (p a).toReal * (f a + c)
      = (p a).toReal * f a + (p a).toReal * c := fun a ↦ by ring
  simp only [hsplit]
  rw [(summable_pmfExpect p hf).tsum_add ((hasSum_pmf_toReal p).summable.mul_right c),
    tsum_mul_right, (hasSum_pmf_toReal p).tsum_eq, one_mul]

/-- Expectation is additive on bounded functions.

Stated with an explicit bound for the same reason the rest of this toolkit is:
`pmfExpect` is a `tsum` in `ℝ`, so splitting one needs summability of both
halves, and every function pushed through here is bounded by `1`. -/
public theorem pmfExpect_add {α : Type*} (p : PMF α) {f g : α → ℝ} {C : ℝ}
    (hf : ∀ a, |f a| ≤ C) (hg : ∀ a, |g a| ≤ C) :
    pmfExpect p (fun a ↦ f a + g a) = pmfExpect p f + pmfExpect p g := by
  unfold pmfExpect
  have hsplit : ∀ a, (p a).toReal * (f a + g a)
      = (p a).toReal * f a + (p a).toReal * g a := fun a ↦ by ring
  simp only [hsplit]
  exact (summable_pmfExpect p hf).tsum_add (summable_pmfExpect p hg)

/-- A function bounded below has an expectation bounded below — the mirror of
`pmfExpect_le`, and the direction a minimax **lower** bound needs. -/
public theorem le_pmfExpect {α : Type*} (p : PMF α) {f : α → ℝ} {C : ℝ}
    (hf : ∀ a, |f a| ≤ C) (c : ℝ) (h : ∀ a, c ≤ f a) : c ≤ pmfExpect p f := by
  have hc : ∀ a, |(fun _ : α ↦ c) a| ≤ max C |c| := fun _ ↦ le_max_right _ _
  have hf' : ∀ a, |f a| ≤ max C |c| := fun a ↦ (hf a).trans (le_max_left _ _)
  simpa using pmfExpect_mono p hc hf' h

/-- A bounded function has a bounded expectation. -/
public theorem pmfExpect_le {α : Type*} (p : PMF α) {f : α → ℝ} {C : ℝ}
    (hf : ∀ a, |f a| ≤ C) (c : ℝ) (h : ∀ a, f a ≤ c) : pmfExpect p f ≤ c := by
  have hc : ∀ a, |(fun _ : α ↦ c) a| ≤ max C |c| := fun _ ↦ le_max_right _ _
  have hf' : ∀ a, |f a| ≤ max C |c| := fun a ↦ (hf a).trans (le_max_left _ _)
  simpa using pmfExpect_mono p hf' hc h

/-! ## Queries and answers -/

/-- One exact-policy query: a visible mask, a **rational** intervention mixture,
and the assignment at which the policy probability is read.

`subsec:queries` writes the query as `(σ_t, 𝐎'_t, w_t)` with rational mixture
weights, `𝐎'_t ⊆ 𝐎`, and `w_t ∈ dom(𝐎'_t)`. All three are here; `visible_subset`
is the containment print states. -/
public structure ShiftedQuery (sk : Skeleton C dim Bool 𝕜) where
  visible : Finset C
  visible_subset : visible ⊆ sk.observed
  mix : ProbMixture C dim ℚ
  observation : Assignment C dim

/-- **The query type is countable.**

The analyst's *query* randomization is therefore not restricted by rendering it
as a `PMF`: on a countable type every probability measure is countably
supported, so `PMF (ShiftedQuery sk)` is already the general object.

This is print's own doing rather than a modelling choice. `subsec:queries` fixes
the mixture weights to be **rational**, and the mask `𝐎'_t` and the observation
`w_t` range over finite types, so the whole triple ranges over a countable set.
The restriction that does bite is on the analyst's *output*, which print leaves
unconstrained — see the module docstring. -/
public instance instCountableShiftedQuery (sk : Skeleton C dim Bool 𝕜) :
    Countable (ShiftedQuery sk) := by
  apply Function.Injective.countable
    (f := fun q : ShiftedQuery sk ↦ (q.visible, q.mix, q.observation))
  rintro ⟨v, hv, m, o⟩ ⟨v', hv', m', o'⟩ h
  simp only [Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  rfl

/-- The **policy-probability oracle** answer: *"the answer is the exact number
`π_{σ_t, 𝐎'_t}(w_t)`"*.

The policy family is an adversarial input fixed before the interaction, which is
what preserves print's *"arbitrary randomization at exact ties"*; answering from
a canonical optimal family instead would make the query problem easier than the
one posed. The rational query weights meet the model's value field here. -/
public noncomputable def exactPolicyAnswer (sk : Skeleton C dim Bool 𝕜)
    (family : PolicyFamily sk) (q : ShiftedQuery sk) : 𝕜 :=
  (family q.visible q.visible_subset (q.mix.mapRat 𝕜)).prob q.observation true

/-- **The answer reads only the visible coordinates of the observation.**

Print writes the query as `(σ_t, 𝐎'_t, w_t)` with `w_t ∈ dom(𝐎'_t)`, an
assignment to the visible subset alone, while `ShiftedQuery.observation` is a
full `Assignment C dim`. The extra coordinates are not a wider query: `Policy`
carries `prob_parents` as a **field**, so every policy in every family reads only
its visible variables, and the answer therefore factors through the restriction.

Stated because a reader cannot see it from `ShiftedQuery`'s own type, and an
answer that did depend on hidden coordinates would make the atlas analyst
strictly more powerful than print's -- lowering `N(ε)` and weakening every bound
phrased over it. This is the certificate that it does not. -/
public theorem exactPolicyAnswer_congr_observation (sk : Skeleton C dim Bool 𝕜)
    (family : PolicyFamily sk) (q : ShiftedQuery sk) (w : Assignment C dim)
    (h : ∀ c ∈ q.visible, q.observation c = w c) :
    exactPolicyAnswer sk family q
      = exactPolicyAnswer sk family { q with observation := w } :=
  (family q.visible q.visible_subset (q.mix.mapRat 𝕜)).prob_parents _ _ _ h

/-! ## Randomized adaptive analysts -/

/-- The analyst's record of the interaction so far: the queries it issued **and**
the answers it got back.

Recording the queries is not bookkeeping. A randomized analyst knows which query
it drew, and two different sampled queries can return the same answer — so a
strategy reading answers alone cannot tell them apart, and the analyst would have
*less* information than print gives it. It also breaks the justification for
using behavioural randomization at all: behavioural and mixed strategies agree
under **perfect recall**, and an analyst that forgets its own moves does not have
perfect recall. -/
public abbrev Transcript (sk : Skeleton C dim Bool 𝕜) :=
  List (ShiftedQuery sk × 𝕜)

/-- A randomized adaptive query strategy: a distribution over the next query,
given the transcript so far. A deterministic strategy is the special case whose
distributions are all `PMF.pure`. -/
public abbrev RandomizedQueryStrategy (sk : Skeleton C dim Bool 𝕜) :=
  Transcript sk → PMF (ShiftedQuery sk)

/-- The analyst's output after the interaction: *"After `N` queries the analyst
outputs `(Ĝ, θ̂)`"*, which is a model. Randomized, for the same reason the
strategy is, and reading the full transcript for the same reason. -/
public abbrev RandomizedEstimator (C : Type*) [Fintype C] [DecidableEq C]
    (dim : C → ℕ) (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] :=
  ∀ sk : Skeleton C dim Bool 𝕜, Transcript sk → PMF (Model C dim 𝕜)

/-- The distribution over transcripts after `n` queries.

Only the analyst randomizes: the oracle answer is the exact number
`exactPolicyAnswer`, so each step extends the transcript deterministically once
the query is drawn. -/
@[expose] public noncomputable def runRandomizedTranscript (sk : Skeleton C dim Bool 𝕜)
    (family : PolicyFamily sk) (strategy : RandomizedQueryStrategy sk) :
    ℕ → PMF (Transcript sk)
  | 0 => PMF.pure []
  | n + 1 =>
      (runRandomizedTranscript sk family strategy n).bind fun history ↦
        PMF.map (fun q ↦ history ++ [(q, exactPolicyAnswer sk family q)])
          (strategy history)

/-! ## Risk, at the reals

`def:margin`'s tables are real and an expectation is a real number, so the risk
layer is stated at `ℝ` rather than at a general value field. The protocol above
stays generic because it is reusable; the quantities print calls a *risk* and a
*budget* are not. -/

/-- The expected error of one randomized analyst against one model and one
adversarial policy family, after `n` queries.

`subsec:queries`: *"The **error** against `M = (G, θ)` is `e(M; Ĝ, θ̂) := 1` if
`Ĝ ≠ G`, and otherwise the maximum entrywise difference of the tables"* — which
is `modelError`. The expectation is over the analyst's randomization, taken in
both places it occurs: the transcript and the output. -/
public noncomputable def exactExpectedError [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (M : Model C dim ℝ) (family : PolicyFamily sk)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : RandomizedEstimator C dim ℝ) (n : ℕ) : ℝ :=
  pmfExpect (runRandomizedTranscript sk family strategy n) fun history ↦
    pmfExpect (estimator sk history) fun Mhat ↦ modelError M Mhat

/-- The supremum print maximizes over: *"the supremum, over models in the class
and admissible adversaries, of the expected error"*.

`AdmissibleFamily M sk 0` is *"admissible at level `δ`"* at `δ = 0`, which
`subsec:queries` says *"forces optimality, with arbitrary randomization at exact
ties"* — the exact-oracle setting O25 is stated in. -/
public noncomputable def exactAnalystRisk [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (n : ℕ)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : RandomizedEstimator C dim ℝ) : ℝ :=
  sSup {e : ℝ | ∃ M ∈ modelClass, ∃ family : PolicyFamily sk,
    AdmissibleFamily M sk 0 family ∧
      e = exactExpectedError sk M family strategy estimator n}

/-- The supremum over an empty model class is zero, following the real
conditional-complete-lattice convention used by the query definitions. -/
@[simp] public theorem exactAnalystRisk_empty [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (n : ℕ)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : RandomizedEstimator C dim ℝ) :
    exactAnalystRisk sk ∅ n strategy estimator = 0 := by
  unfold exactAnalystRisk
  simp

/-- **The minimax risk at budget `n`**, as `subsec:queries` defines it: the
*infimum* over randomized analyst strategies of `exactAnalystRisk`.

The infimum is the printed word and it is load-bearing. Asking instead for *some*
strategy achieving a given level is strictly stronger whenever the infimum is
not attained, and would make a budget print calls feasible infeasible here. -/
@[expose] public noncomputable def exactMinimaxRisk [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ (strategy : RandomizedQueryStrategy sk)
    (estimator : RandomizedEstimator C dim ℝ),
      r = exactAnalystRisk sk modelClass n strategy estimator}

/-- **`N(ε)`**: *"the minimal budget `N(ε)` such that the minimax risk over `𝒩`
at budget `N(ε)` … is at most `ε`"*.

Valued in `ℕ∞`, and the `⊤` case is the point. When no budget achieves risk `ε`
there is no such minimal budget and print's `N(ε)` does not exist, so a
`ℕ`-valued definition has to invent a value; returning `0` says *zero queries
suffice*, which is the opposite of the truth and makes any upper bound on `N(ε)`
hold vacuously on exactly the instances print would answer *no* for. `sInf ∅ = ⊤`
in `ℕ∞` says what print says. -/
@[expose] public noncomputable def exactMinimalBudget [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (ε : ℝ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ m : ℕ, (m : ℕ∞) = n ∧ exactMinimaxRisk sk modelClass m ≤ ε}

/-- A strategy is **non-adaptive** when it never reads an *answer*: transcripts
with the same queries get the same next-query law.

This is weaker than requiring the law to depend only on the round number, and
deliberately so. A non-adaptive analyst may draw a whole **correlated** schedule
of queries in advance — that is a randomized non-adaptive analyst, and print's
comparison is against those, not only against product schedules. With the
queries recorded in the transcript, a behavioural strategy can carry that
correlation forward by reading what it already played; asking instead that the
law depend only on `history.length` would force the rounds independent and
compare O25's adaptive analyst against an artificially weak opponent. -/
@[expose] public def IsNonadaptiveRandomizedStrategy (sk : Skeleton C dim Bool 𝕜)
    (strategy : RandomizedQueryStrategy sk) : Prop :=
  ∀ h h' : Transcript sk,
    h.map Prod.fst = h'.map Prod.fst → strategy h = strategy h'

/-- The minimax risk when the analyst is restricted to non-adaptive strategies,
which is the other quantity `prob:exact`'s decide-clause compares. -/
public noncomputable def nonadaptiveExactMinimaxRisk [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (modelClass : Set (Model C dim ℝ)) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ (strategy : RandomizedQueryStrategy sk)
    (estimator : RandomizedEstimator C dim ℝ),
      IsNonadaptiveRandomizedStrategy sk strategy ∧
        r = exactAnalystRisk sk modelClass n strategy estimator}

/-- `N(ε)` for a non-adaptive analyst. -/
public noncomputable def nonadaptiveExactMinimalBudget [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (modelClass : Set (Model C dim ℝ)) (ε : ℝ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ m : ℕ, (m : ℕ∞) = n ∧
    nonadaptiveExactMinimaxRisk sk modelClass m ≤ ε}

/-! ## The unrestricted analyst output

`RandomizedEstimator` returns a `PMF`, hence a countably supported output law,
where `subsec:queries` says only that the analyst *"outputs `(Ĝ, θ̂)`"*. The
general object is an arbitrary probability measure on the model space, which
`Causal.ModelSpace` supplies the measurable structure for.

The two risks below are the same definition over the two estimator classes. The
`PMF` class embeds in the measure class, so the general infimum is at most the
restricted one — and that inequality, proved here, is the **direction** of the
deviation. It says a budget computed in this
file can only be *larger* than print's, so a finite upper bound on it is
stronger than print's claim, never weaker.

The reverse inequality closes the axis and is proved below.
`MeasureEstimator.discretize` rounds a measure estimator onto the countable grid
of `Model.roundDown` — costing `O(ε)` by `modelError_roundDown_le`, countable by
`countable_range_roundDown` — and `exactMinimaxRisk_le_measureMinimaxRisk` pushes
that bound through the supremum and the infimum. `measureMinimaxRisk_eq_exactMinimaxRisk`
and `measureMinimalBudget_eq_exactMinimalBudget_binary` are the equalities, so
`N(ε)` is the same number over either estimator class, so the choice of
estimator class is not a scope axis for any statement phrased over `N(ε)`. -/

/-- The analyst's output as an **arbitrary** probability measure on models. This
is the object `subsec:queries` actually describes. -/
public abbrev MeasureEstimator (C : Type*) [Fintype C] [DecidableEq C]
    (dim : C → ℕ) :=
  ∀ sk : Skeleton C dim Bool ℝ, Transcript sk →
    MeasureTheory.ProbabilityMeasure (Model C dim ℝ)

/-- A `PMF`-valued estimator is a measure-valued one. This is the inclusion that
makes the restricted class a subclass rather than a different object. -/
@[expose] public noncomputable def RandomizedEstimator.toMeasureEstimator
    (estimator : RandomizedEstimator C dim ℝ) : MeasureEstimator C dim :=
  fun sk history ↦ ⟨(estimator sk history).toMeasure, inferInstance⟩

/-- The printed error is integrable against any finite measure: it is measurable
and bounded by `1`. -/
public theorem integrable_modelError [Nonempty C] (M : Model C dim ℝ)
    (μ : MeasureTheory.Measure (Model C dim ℝ)) [MeasureTheory.IsFiniteMeasure μ] :
    MeasureTheory.Integrable (fun M' ↦ modelError M M') μ := by
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
    (measurable_modelError M).aestronglyMeasurable ?_
  filter_upwards with M'
  rw [Real.norm_eq_abs, abs_of_nonneg (modelError_nonneg M M')]
  exact modelError_le_one M M'

/-- Against a `PMF`'s own measure, the Bochner integral is the sum `pmfExpect`
computes. This is what makes the inclusion above risk-preserving rather than
merely type-correct. -/
public theorem integral_toMeasure_modelError [Nonempty C] (M : Model C dim ℝ)
    (p : PMF (Model C dim ℝ)) :
    ∫ M', modelError M M' ∂p.toMeasure = pmfExpect p fun M' ↦ modelError M M' := by
  rw [PMF.integral_eq_tsum p _ (integrable_modelError M p.toMeasure)]
  simp [pmfExpect, smul_eq_mul]

/-- The expected error against an arbitrary output law. -/
public noncomputable def measureExpectedError [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (M : Model C dim ℝ) (family : PolicyFamily sk)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : MeasureEstimator C dim) (n : ℕ) : ℝ :=
  pmfExpect (runRandomizedTranscript sk family strategy n) fun history ↦
    ∫ Mhat, modelError M Mhat ∂(estimator sk history : MeasureTheory.Measure _)

/-- The supremum over the class and the admissible adversaries, at an arbitrary
output law. -/
public noncomputable def measureAnalystRisk [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (n : ℕ)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : MeasureEstimator C dim) : ℝ :=
  sSup {e : ℝ | ∃ M ∈ modelClass, ∃ family : PolicyFamily sk,
    AdmissibleFamily M sk 0 family ∧
      e = measureExpectedError sk M family strategy estimator n}

/-- **The minimax risk print defines**, with the analyst's output law
unrestricted. -/
@[expose] public noncomputable def measureMinimaxRisk [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (modelClass : Set (Model C dim ℝ)) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ (strategy : RandomizedQueryStrategy sk)
    (estimator : MeasureEstimator C dim),
      r = measureAnalystRisk sk modelClass n strategy estimator}

/-- `N(ε)` with the analyst's output law unrestricted. -/
@[expose] public noncomputable def measureMinimalBudget [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (modelClass : Set (Model C dim ℝ)) (ε : ℝ) : ℕ∞ :=
  sInf {n : ℕ∞ | ∃ m : ℕ, (m : ℕ∞) = n ∧ measureMinimaxRisk sk modelClass m ≤ ε}

/-! ## The inclusion is risk-preserving -/

public theorem measureExpectedError_toMeasureEstimator [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (M : Model C dim ℝ) (family : PolicyFamily sk)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : RandomizedEstimator C dim ℝ) (n : ℕ) :
    measureExpectedError sk M family strategy estimator.toMeasureEstimator n
      = exactExpectedError sk M family strategy estimator n := by
  unfold measureExpectedError exactExpectedError
  refine congrArg _ (funext fun history ↦ ?_)
  exact integral_toMeasure_modelError M (estimator sk history)

public theorem measureAnalystRisk_toMeasureEstimator [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (modelClass : Set (Model C dim ℝ)) (n : ℕ)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : RandomizedEstimator C dim ℝ) :
    measureAnalystRisk sk modelClass n strategy estimator.toMeasureEstimator
      = exactAnalystRisk sk modelClass n strategy estimator := by
  unfold measureAnalystRisk exactAnalystRisk
  refine congrArg sSup (Set.ext fun e ↦ ?_)
  simp only [Set.mem_ofPred_eq,
    measureExpectedError_toMeasureEstimator sk _ _ strategy estimator n]

/-! ## Every risk is non-negative

Needed so the infima are over sets bounded below, which is what makes the
comparison below a statement about real numbers rather than about `sInf ∅`. -/

public theorem pmfExpect_nonneg {α : Type*} (p : PMF α) {f : α → ℝ}
    (hf : ∀ a, 0 ≤ f a) : 0 ≤ pmfExpect p f :=
  tsum_nonneg fun a ↦ mul_nonneg ENNReal.toReal_nonneg (hf a)

public theorem measureExpectedError_nonneg [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (M : Model C dim ℝ) (family : PolicyFamily sk)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : MeasureEstimator C dim) (n : ℕ) :
    0 ≤ measureExpectedError sk M family strategy estimator n :=
  pmfExpect_nonneg _ fun _ ↦
    MeasureTheory.integral_nonneg fun M' ↦ modelError_nonneg M M'

public theorem measureAnalystRisk_nonneg [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (n : ℕ)
    (strategy : RandomizedQueryStrategy sk) (estimator : MeasureEstimator C dim) :
    0 ≤ measureAnalystRisk sk modelClass n strategy estimator := by
  refine Real.sSup_nonneg fun e he ↦ ?_
  obtain ⟨M, -, family, -, rfl⟩ := he
  exact measureExpectedError_nonneg sk M family strategy estimator n

/-! ## The restricted risk is the larger one

This is the direction of the deviation, as a theorem. Restricting the analyst's
output law to a countably supported one shrinks the set the infimum ranges over,
so the budget computed in this file can only be larger than print's — and a
finite upper bound on it is therefore **stronger** than print's claim, never
weaker. -/

public theorem measureMinimaxRisk_le_exactMinimaxRisk [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (modelClass : Set (Model C dim ℝ)) (n : ℕ)
    (hq : Nonempty (ShiftedQuery sk)) (hm : Nonempty (Model C dim ℝ)) :
    measureMinimaxRisk sk modelClass n ≤ exactMinimaxRisk sk modelClass n := by
  classical
  set S : Set ℝ := {r : ℝ | ∃ (strategy : RandomizedQueryStrategy sk)
    (estimator : MeasureEstimator C dim),
      r = measureAnalystRisk sk modelClass n strategy estimator} with hS
  have hbdd : BddBelow S := by
    refine ⟨0, ?_⟩
    intro r hr
    obtain ⟨strategy, estimator, rfl⟩ := hr
    exact measureAnalystRisk_nonneg sk modelClass n strategy estimator
  have hne : {r : ℝ | ∃ (strategy : RandomizedQueryStrategy sk)
      (estimator : RandomizedEstimator C dim ℝ),
        r = exactAnalystRisk sk modelClass n strategy estimator}.Nonempty :=
    ⟨_, ⟨fun _ ↦ PMF.pure (Classical.arbitrary (ShiftedQuery sk)),
      fun _ _ ↦ PMF.pure (Classical.arbitrary (Model C dim ℝ)), rfl⟩⟩
  refine csInf_le_csInf hbdd hne ?_
  intro r hr
  obtain ⟨strategy, estimator, rfl⟩ := hr
  exact ⟨strategy, estimator.toMeasureEstimator,
    (measureAnalystRisk_toMeasureEstimator sk modelClass n strategy estimator).symm⟩

/-! ## The reverse inequality

`measureMinimaxRisk_le_exactMinimaxRisk` says the restricted infimum is the
larger. This section proves it is not strictly larger, so the two agree and the
`PMF` rendering costs nothing.

The argument is the one `Causal.ModelSpace` sets up. Given any measure-valued
estimator, round its output onto a grid of spacing `ε`: the error moves by at
most `K · ε` where `K` bounds the variable dimensions, and rounded models range
over a **countable** set, so the rounded output law is a `PMF`. That exhibits a
`PMF` estimator whose risk exceeds the measure estimator's by at most `K · ε`.
Since the risk is an infimum and `ε` is arbitrary, the two infima agree.

Only the **one-sided** bound is used. `modelError_roundDown_le` proves the
two-sided form, and the extra half is not needed. -/

private theorem abs_modelError_le [Nonempty C] (M M' : Model C dim ℝ) :
    |modelError M M'| ≤ 1 := by
  rw [abs_of_nonneg (modelError_nonneg M M')]
  exact modelError_le_one M M'

/-- The dimension bound used throughout: the largest variable arity. -/
@[expose] public noncomputable def dimBound (C : Type*) [Fintype C] (dim : C → ℕ) : ℕ :=
  Finset.univ.sup dim

omit [DecidableEq C] in
public theorem dim_le_dimBound (c : C) : dim c ≤ dimBound C dim :=
  Finset.le_sup (Finset.mem_univ c)

/-- **Rounding a measure estimator gives a `PMF` estimator.** The output law is
pushed onto the countable set of rounded models, where `Measure.toPMF` applies,
and mapped back along the inclusion. -/
@[expose] public noncomputable def MeasureEstimator.discretize
    (estimator : MeasureEstimator C dim) {ε : ℝ} (hε : 0 < ε) :
    RandomizedEstimator C dim ℝ := fun sk history ↦
  haveI : Countable ↥(Set.range fun M : Model C dim ℝ ↦ M.roundDown hε) :=
    (countable_range_roundDown hε).to_subtype
  let g : Model C dim ℝ → ↥(Set.range fun M : Model C dim ℝ ↦ M.roundDown hε) :=
    fun M ↦ ⟨M.roundDown hε, Set.mem_range_self M⟩
  let nu : MeasureTheory.Measure ↥(Set.range fun M : Model C dim ℝ ↦ M.roundDown hε) :=
    MeasureTheory.Measure.map g
      (estimator sk history : MeasureTheory.Measure (Model C dim ℝ))
  haveI : MeasureTheory.IsProbabilityMeasure nu :=
    MeasureTheory.Measure.isProbabilityMeasure_map
      ((measurable_roundDown hε).subtype_mk).aemeasurable
  PMF.map Subtype.val nu.toPMF

/-- The discretized estimator's expectation is the original's, taken along the
rounding map. -/
public theorem pmfExpect_discretize [Nonempty C] (M : Model C dim ℝ)
    (estimator : MeasureEstimator C dim) {ε : ℝ} (hε : 0 < ε)
    (sk : Skeleton C dim Bool ℝ) (history : Transcript sk) :
    pmfExpect (estimator.discretize hε sk history) (fun M' ↦ modelError M M')
      = ∫ M', modelError M (M'.roundDown hε)
          ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ)) := by
  classical
  have : Countable ↥(Set.range fun M : Model C dim ℝ ↦ M.roundDown hε) :=
    (countable_range_roundDown hε).to_subtype
  have : MeasureTheory.IsProbabilityMeasure
      (MeasureTheory.Measure.map
        (fun M : Model C dim ℝ ↦ (⟨M.roundDown hε, Set.mem_range_self M⟩ :
          ↥(Set.range fun M : Model C dim ℝ ↦ M.roundDown hε)))
        (estimator sk history : MeasureTheory.Measure (Model C dim ℝ))) :=
    MeasureTheory.Measure.isProbabilityMeasure_map
      ((measurable_roundDown hε).subtype_mk).aemeasurable
  have hq : (estimator.discretize hε sk history).toMeasure
      = MeasureTheory.Measure.map (fun M' : Model C dim ℝ ↦ M'.roundDown hε)
          (estimator sk history : MeasureTheory.Measure (Model C dim ℝ)) := by
    simp only [MeasureEstimator.discretize]
    rw [← PMF.toMeasure_map _ _ measurable_subtype_coe,
      MeasureTheory.Measure.toPMF_toMeasure,
      MeasureTheory.Measure.map_map measurable_subtype_coe
        ((measurable_roundDown hε).subtype_mk)]
    rfl
  rw [← integral_toMeasure_modelError M (estimator.discretize hε sk history), hq,
    MeasureTheory.integral_map (measurable_roundDown hε).aemeasurable
      (measurable_modelError M).aestronglyMeasurable]

private theorem integrable_modelError_roundDown [Nonempty C] (M : Model C dim ℝ)
    {ε : ℝ} (hε : 0 < ε) (μ : MeasureTheory.Measure (Model C dim ℝ))
    [MeasureTheory.IsFiniteMeasure μ] :
    MeasureTheory.Integrable (fun M' ↦ modelError M (M'.roundDown hε)) μ := by
  refine MeasureTheory.Integrable.mono' (MeasureTheory.integrable_const (1 : ℝ))
    ((measurable_modelError M).comp (measurable_roundDown hε)).aestronglyMeasurable ?_
  filter_upwards with M'
  rw [Real.norm_eq_abs]
  exact abs_modelError_le M _

/-- **The `O(ε)` cost, at one transcript law.** -/
public theorem exactExpectedError_discretize_le [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (M : Model C dim ℝ) (family : PolicyFamily sk)
    (strategy : RandomizedQueryStrategy sk) (estimator : MeasureEstimator C dim)
    (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    exactExpectedError sk M family strategy (estimator.discretize hε) n
      ≤ measureExpectedError sk M family strategy estimator n
        + (dimBound C dim : ℝ) * ε := by
  have hstep : ∀ history : Transcript sk,
      pmfExpect (estimator.discretize hε sk history) (fun M' ↦ modelError M M')
        ≤ (∫ M', modelError M M'
            ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ)))
          + (dimBound C dim : ℝ) * ε := by
    intro history
    rw [pmfExpect_discretize M estimator hε sk history]
    have hpt : ∀ M' : Model C dim ℝ,
        modelError M (M'.roundDown hε)
          ≤ modelError M M' + (dimBound C dim : ℝ) * ε := by
      intro M'
      have h := abs_le.mp
        (modelError_roundDown_le M M' hε (dimBound C dim) fun c ↦ dim_le_dimBound c)
      linarith [h.2]
    calc ∫ M', modelError M (M'.roundDown hε)
            ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ))
        ≤ ∫ M', (modelError M M' + (dimBound C dim : ℝ) * ε)
            ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ)) :=
          MeasureTheory.integral_mono (integrable_modelError_roundDown M hε _)
            ((integrable_modelError M _).add (MeasureTheory.integrable_const _)) hpt
      _ = _ := by
          rw [MeasureTheory.integral_add (integrable_modelError M _)
            (MeasureTheory.integrable_const _), MeasureTheory.integral_const]
          simp
  have hK0 : (0 : ℝ) ≤ (dimBound C dim : ℝ) * ε :=
    mul_nonneg (Nat.cast_nonneg _) hε.le
  have hg1 : ∀ history : Transcript sk,
      |∫ M', modelError M M'
        ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ))| ≤ 1 := by
    intro history
    have h0 : 0 ≤ ∫ M', modelError M M'
        ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ)) :=
      MeasureTheory.integral_nonneg fun M' ↦ modelError_nonneg M M'
    have h1 : (∫ M', modelError M M'
        ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ))) ≤ 1 := by
      calc ∫ M', modelError M M'
            ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ))
          ≤ ∫ _M' : Model C dim ℝ, (1 : ℝ)
            ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ)) :=
            MeasureTheory.integral_mono (integrable_modelError M _)
              (MeasureTheory.integrable_const _) fun M' ↦ modelError_le_one M M'
        _ = 1 := by simp
    rw [abs_of_nonneg h0]
    exact h1
  have hf1 : ∀ history : Transcript sk,
      |pmfExpect (estimator.discretize hε sk history)
        (fun M' ↦ modelError M M')| ≤ 1 := by
    intro history
    rw [abs_of_nonneg (pmfExpect_nonneg _ fun M' ↦ modelError_nonneg M M')]
    exact pmfExpect_le _ (fun M' ↦ abs_modelError_le M M') 1
      fun M' ↦ modelError_le_one M M'
  unfold exactExpectedError measureExpectedError
  calc pmfExpect (runRandomizedTranscript sk family strategy n)
        (fun history ↦ pmfExpect (estimator.discretize hε sk history)
          fun Mhat ↦ modelError M Mhat)
      ≤ pmfExpect (runRandomizedTranscript sk family strategy n)
          (fun history ↦ (∫ Mhat, modelError M Mhat
            ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ)))
              + (dimBound C dim : ℝ) * ε) :=
        pmfExpect_mono _ (C := 1 + (dimBound C dim : ℝ) * ε)
          (fun history ↦ (hf1 history).trans (by linarith))
          (fun history ↦ (abs_add_le _ _).trans (by
            have := hg1 history
            rw [abs_of_nonneg hK0]
            linarith))
          hstep
    _ = pmfExpect (runRandomizedTranscript sk family strategy n)
          (fun history ↦ ∫ Mhat, modelError M Mhat
            ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ)))
          + (dimBound C dim : ℝ) * ε :=
        pmfExpect_add_const _ hg1 _

/-! ## Through the supremum and the infimum -/

public theorem exactExpectedError_nonneg [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (M : Model C dim ℝ) (family : PolicyFamily sk)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : RandomizedEstimator C dim ℝ) (n : ℕ) :
    0 ≤ exactExpectedError sk M family strategy estimator n :=
  pmfExpect_nonneg _ fun _ ↦ pmfExpect_nonneg _ fun M' ↦ modelError_nonneg M M'

public theorem exactAnalystRisk_nonneg [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (n : ℕ)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : RandomizedEstimator C dim ℝ) :
    0 ≤ exactAnalystRisk sk modelClass n strategy estimator := by
  refine Real.sSup_nonneg fun e he ↦ ?_
  obtain ⟨M, -, family, -, rfl⟩ := he
  exact exactExpectedError_nonneg sk M family strategy estimator n

public theorem measureExpectedError_le_one [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (M : Model C dim ℝ) (family : PolicyFamily sk)
    (strategy : RandomizedQueryStrategy sk)
    (estimator : MeasureEstimator C dim) (n : ℕ) :
    measureExpectedError sk M family strategy estimator n ≤ 1 := by
  refine pmfExpect_le _ (C := 1) (fun history ↦ ?_) 1 fun history ↦ ?_
  · rw [abs_of_nonneg (MeasureTheory.integral_nonneg fun M' ↦ modelError_nonneg M M')]
    calc ∫ M', modelError M M'
          ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ))
        ≤ ∫ _M' : Model C dim ℝ, (1 : ℝ)
          ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ)) :=
          MeasureTheory.integral_mono (integrable_modelError M _)
            (MeasureTheory.integrable_const _) fun M' ↦ modelError_le_one M M'
      _ = 1 := by simp
  · calc ∫ M', modelError M M'
          ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ))
        ≤ ∫ _M' : Model C dim ℝ, (1 : ℝ)
          ∂(estimator sk history : MeasureTheory.Measure (Model C dim ℝ)) :=
          MeasureTheory.integral_mono (integrable_modelError M _)
            (MeasureTheory.integrable_const _) fun M' ↦ modelError_le_one M M'
      _ = 1 := by simp

private theorem bddAbove_measureRisk [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (n : ℕ)
    (strategy : RandomizedQueryStrategy sk) (estimator : MeasureEstimator C dim) :
    BddAbove {e : ℝ | ∃ M ∈ modelClass, ∃ family : PolicyFamily sk,
      AdmissibleFamily M sk 0 family ∧
        e = measureExpectedError sk M family strategy estimator n} := by
  refine ⟨1, ?_⟩
  rintro e ⟨M, -, family, -, rfl⟩
  exact measureExpectedError_le_one sk M family strategy estimator n

/-- **The `O(ε)` cost, through the supremum.** -/
public theorem exactAnalystRisk_discretize_le [Nonempty C] (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (n : ℕ)
    (strategy : RandomizedQueryStrategy sk) (estimator : MeasureEstimator C dim)
    {ε : ℝ} (hε : 0 < ε) :
    exactAnalystRisk sk modelClass n strategy (estimator.discretize hε)
      ≤ measureAnalystRisk sk modelClass n strategy estimator
        + (dimBound C dim : ℝ) * ε := by
  have hK0 : (0 : ℝ) ≤ (dimBound C dim : ℝ) * ε :=
    mul_nonneg (Nat.cast_nonneg _) hε.le
  refine Real.sSup_le ?_ (by
    have := measureAnalystRisk_nonneg sk modelClass n strategy estimator
    linarith)
  rintro e ⟨M, hM, family, hfam, rfl⟩
  refine le_trans (exactExpectedError_discretize_le sk M family strategy estimator n hε) ?_
  have hmem : measureExpectedError sk M family strategy estimator n
      ≤ measureAnalystRisk sk modelClass n strategy estimator :=
    le_csSup (bddAbove_measureRisk sk modelClass n strategy estimator)
      ⟨M, hM, family, hfam, rfl⟩
  linarith

/-- **The reverse inequality.** The unrestricted infimum is not strictly smaller,
so restricting the analyst's output law to a countably supported one costs
nothing at the level of the minimax risk. -/
public theorem exactMinimaxRisk_le_measureMinimaxRisk [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (modelClass : Set (Model C dim ℝ)) (n : ℕ)
    (hq : Nonempty (ShiftedQuery sk)) (hm : Nonempty (Model C dim ℝ)) :
    exactMinimaxRisk sk modelClass n ≤ measureMinimaxRisk sk modelClass n := by
  classical
  have hbdd : BddBelow {r : ℝ | ∃ (strategy : RandomizedQueryStrategy sk)
      (estimator : RandomizedEstimator C dim ℝ),
        r = exactAnalystRisk sk modelClass n strategy estimator} := by
    refine ⟨0, ?_⟩
    intro r hr
    obtain ⟨strategy, estimator, rfl⟩ := hr
    exact exactAnalystRisk_nonneg sk modelClass n strategy estimator
  have hne : {r : ℝ | ∃ (strategy : RandomizedQueryStrategy sk)
      (estimator : MeasureEstimator C dim),
        r = measureAnalystRisk sk modelClass n strategy estimator}.Nonempty :=
    ⟨_, ⟨fun _ ↦ PMF.pure (Classical.arbitrary (ShiftedQuery sk)),
      RandomizedEstimator.toMeasureEstimator
        (fun _ _ ↦ PMF.pure (Classical.arbitrary (Model C dim ℝ))), rfl⟩⟩
  refine le_of_forall_pos_le_add fun δ hδ ↦ ?_
  set K : ℕ := dimBound C dim with hK
  have hεpos : 0 < δ / (K + 1) := by positivity
  have hKε : (K : ℝ) * (δ / (K + 1)) ≤ δ := by
    rw [mul_div_assoc'] at *
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hδ.le, Nat.cast_nonneg (α := ℝ) K]
  have hkey : exactMinimaxRisk sk modelClass n - δ
      ≤ measureMinimaxRisk sk modelClass n := by
    unfold measureMinimaxRisk
    refine le_csInf hne ?_
    rintro r ⟨strategy, estimator, rfl⟩
    have hstep : exactMinimaxRisk sk modelClass n
        ≤ exactAnalystRisk sk modelClass n strategy (estimator.discretize hεpos) :=
      csInf_le hbdd ⟨strategy, estimator.discretize hεpos, rfl⟩
    have hbound := exactAnalystRisk_discretize_le sk modelClass n strategy estimator hεpos
    linarith
  linarith

/-- **The printed minimax risk, both readings agreeing.** -/
public theorem measureMinimaxRisk_eq_exactMinimaxRisk [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (modelClass : Set (Model C dim ℝ)) (n : ℕ)
    (hq : Nonempty (ShiftedQuery sk)) (hm : Nonempty (Model C dim ℝ)) :
    measureMinimaxRisk sk modelClass n = exactMinimaxRisk sk modelClass n :=
  le_antisymm (measureMinimaxRisk_le_exactMinimaxRisk sk modelClass n hq hm)
    (exactMinimaxRisk_le_measureMinimaxRisk sk modelClass n hq hm)

/-- **`N(ε)` agrees too**, which is the statement MAIS-O25 and MAIS-O26 are made
of. Equality of the risks at *every* budget makes the two feasible-budget sets
the same set, so their infima agree. -/
public theorem measureMinimalBudget_eq_exactMinimalBudget [Nonempty C]
    (sk : Skeleton C dim Bool ℝ) (modelClass : Set (Model C dim ℝ)) (ε : ℝ)
    (hq : Nonempty (ShiftedQuery sk)) (hm : Nonempty (Model C dim ℝ)) :
    measureMinimalBudget sk modelClass ε = exactMinimalBudget sk modelClass ε := by
  unfold measureMinimalBudget exactMinimalBudget
  congr 1
  ext k
  simp only [Set.mem_ofPred_eq,
    measureMinimaxRisk_eq_exactMinimaxRisk sk modelClass _ hq hm]

/-! ## The equality is unconditional where the conjectures live

The two theorems above carry nonemptiness side conditions, because a `PMF` needs
an inhabited carrier and the witnesses in their proofs are `PMF.pure`. Both hold
for `def:cid`'s binary chance variables, so the closure is not conditional at the
quantifier MAIS-O25 and MAIS-O26 are stated at. -/

/-- A binary model always exists: no parents and a fair coin at every variable. -/
public instance instNonemptyBinaryModel :
    Nonempty (Model C (binaryDim C) ℝ) :=
  ⟨{ dim_pos := fun _ ↦ by norm_num
     parents := fun _ ↦ ∅
     acyclic := ⟨fun _ ↦ 0, by simp⟩
     cpt := fun _ _ _ ↦ 1 / 2
     cpt_parents := fun _ _ _ _ _ ↦ rfl
     cpt_nonneg := fun _ _ _ ↦ by norm_num
     cpt_sum := fun _ _ ↦ by rw [Fin.sum_univ_two]; norm_num }⟩

/-- A query always exists: mask nothing, intervene nowhere, read the all-zero
observation. -/
public instance instNonemptyShiftedQuery (sk : Skeleton C (binaryDim C) Bool ℝ) :
    Nonempty (ShiftedQuery sk) :=
  ⟨{ visible := ∅
     visible_subset := Finset.empty_subset _
     mix := ProbMixture.dirac (𝕜 := ℚ) fun _ ↦ id
     observation := fun _ ↦ 0 }⟩

/-- **`N(ε)` is print's, unconditionally, on binary chance variables.** This is
the form MAIS-O25 and MAIS-O26 consume. -/
public theorem measureMinimalBudget_eq_exactMinimalBudget_binary [Nonempty C]
    (sk : Skeleton C (binaryDim C) Bool ℝ)
    (modelClass : Set (Model C (binaryDim C) ℝ)) (ε : ℝ) :
    measureMinimalBudget sk modelClass ε = exactMinimalBudget sk modelClass ε :=
  measureMinimalBudget_eq_exactMinimalBudget sk modelClass ε
    (instNonemptyShiftedQuery sk) (instNonemptyBinaryModel)

/-- The same for the risk. -/
public theorem measureMinimaxRisk_eq_exactMinimaxRisk_binary [Nonempty C]
    (sk : Skeleton C (binaryDim C) Bool ℝ)
    (modelClass : Set (Model C (binaryDim C) ℝ)) (n : ℕ) :
    measureMinimaxRisk sk modelClass n = exactMinimaxRisk sk modelClass n :=
  measureMinimaxRisk_eq_exactMinimaxRisk sk modelClass n
    (instNonemptyShiftedQuery sk) (instNonemptyBinaryModel)

end AISafetyAtlas.Causal
