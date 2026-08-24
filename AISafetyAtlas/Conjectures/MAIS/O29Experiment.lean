module

public import AISafetyAtlas.Conjectures.MAIS.O29

/-!
# The sampled Boltzmann experiment

`prob:boltzmann`(a) is a question about the *map* from models to Boltzmann
behaviour, and the atlas answers it in `O29.lean` with no statistics at all: two
models, one response family. Clauses (b) and (c) are different in kind. They
speak about a **minimax risk at budget `N`**, which means an analyst that issues
queries, receives *sampled* answers, and outputs a model — the statistical
experiment the exact-oracle layer in `AISafetyAtlas.Causal.Query` builds for
`prob:exact`, with the oracle replaced.

That replacement is the whole of this module. Everything else is a mirror of the
exact layer, deliberately so: `ShiftedQuery` is the same printed triple
`(σ_t, 𝐎'_t, w_t)`, the transcript records queries beside answers for the same
perfect-recall reason, the estimator is the same `PMF (Model …)`, and the risk is
the same infimum of a supremum. Two things differ, and both are print's doing.

**The answer is a coin, not a number**, and print names three observation models,
so which one (b) uses is a reading and needs its evidence. `subsec:queries`
offers the policy-probability oracle (the exact number `π_{σ,𝐎'}(w)`), the
sampled action (`A_t ∼ Bernoulli(π_{σ,𝐎'}(w_t))`, with repeated experiments at
one query conditionally independent), and the corrupted sampled action.

`prob:boltzmann`(b) is the **sampled action**, and the tell is in its own
sentence: it expects *"the smooth local rate (typically proportional to
`1/(β√N)`)"*. A `√N` is what sampling noise produces; an exact-number oracle has
no `√N` in it, because there is nothing to average. Corruption is excluded
because (b) names no level `ζ`.

So `Transcript` becomes `List (ShiftedQuery × Bool)` and the transcript law
depends on the model rather than only on the analyst's coins. That is what makes
(b) a statistics problem and (a) not.

**This module's floor does not contradict that expected rate.** `1/(β√N)` is
what print expects where the class is generic; the class the floor is proved on
contains a behavioural collision, and `q:ident`'s negative answer says such
classes exist inside `𝕄(sk, λ)`. At such a class the `β → ∞` limit is the
noiseless regime, which is exactly where MAIS-O23 already says two models are
indistinguishable — so the risk staying up is the same fact seen through a
different channel, not a competing claim about the rate.

**There is no adversarial policy family, and that is print's word rather than
an inference.** `subsec:queries` defines the minimax risk as an infimum over
analysts of a supremum *"over models in the class and admissible adversaries"*,
and then introduces this channel as *"a useful **non-adversarial**
specialization"*. The exact layer needs the adversary because *"arbitrary
randomization at exact ties"* leaves the policy-probability oracle's answer
underdetermined; here the response law is a softmax of the model's own expected
utilities, pinned by the model and `β`, with `1/2` at zero-probability
observations as `subsec:queries` stipulates. The supremum over adversaries is
over a singleton, so dropping it changes nothing — and quantifying over one
would add a hypothesis print explicitly removes.

`E_M^{𝐎'}(d, w; σ)` is print's *conditional* expectation
`Σ_z u(d,z) P_M(𝐙 = z ∣ 𝐎' = w; σ)`, which is why
`boltzmannTrueProbability` divides `Model.fibreScore` by `fibreMass`. The
sampled answer is print's *"`A_t ∼ Bernoulli(π(w_t))`"*, drawn afresh at each
step because print says *"repeated experiments at the same query are
conditionally independent"*.

**What this module does and does not settle.** It states the experiment and
proves that the minimax risk sits between `1/2` and `1` whenever the class
contains two Boltzmann-indistinguishable models with **different graphs** — a
floor from the two-point argument and a ceiling from print's error being bounded
by `1`. On such a class that is `prob:boltzmann`(b) answered up to a factor of
two, uniformly in the budget and in `β`: the rate is `Θ(1)`, so there is nothing
to deteriorate as `β → 0` and no `(N, β)` crossover to characterize, because the
risk never decays.

What is **not** here is (b) on a class where the risk *does* decay, which is
where its rate, its `β → 0` deterioration and its crossover live, and which needs
mathematics this module contains none of. Nor is (c)'s design problem. A
determine-problem is not a *conjecture* row; it carries a **target** row naming
its specification, and `IsBoltzmannRiskRate` below is CONJ-016's. Clause (c) has a blocked row,
CONJ-020, because the risk here is already an infimum over analysts and there is
no object over which to state a maximization.

**What a downstream module can unfold.** `boltzmannAnswer`,
`runBoltzmannTranscript` and `boltzmannMinimaxRisk` carry `@[expose]`, so their
bodies cross the module boundary. `boltzmannExpectedError` and
`boltzmannAnalystRisk` do not: a `public def` exports its type and not its body,
so a downstream file can name them and prove nothing about them directly. That
is deliberate for now — the results here are consumed through
`half_le_boltzmannMinimaxRisk_of_collision` rather than by unfolding — but it is
the same wall MAIS-O27 hit, where a claim about the radius came to live in a
coverage note instead of in a theorem. Anyone reasoning about the risk from
another module should expose them or add characterization lemmas rather than
restate the definitions.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}

/-! ## The response is a probability -/

omit [Nonempty C] in
/-- The Boltzmann response probability is nonnegative.

Both branches are: the zero-mass branch is `1/2` by `subsec:queries`'s uniform
stipulation, and the softmax branch is a quotient of positive exponentials. -/
public theorem boltzmannTrueProbability_nonneg (M : Model C dim ℝ)
    (sk : Skeleton C dim Bool ℝ) (visible : Finset C) (mix : ProbMixture C dim ℝ)
    (observation : Assignment C dim) (β : ℝ) :
    0 ≤ boltzmannTrueProbability M sk visible mix observation β := by
  unfold boltzmannTrueProbability
  split
  · norm_num
  · exact div_nonneg (Real.exp_nonneg _)
      (by positivity)

omit [Nonempty C] in
/-- The Boltzmann response probability is at most `1`: the softmax denominator
exceeds its numerator by the other action's exponential, which is positive. -/
public theorem boltzmannTrueProbability_le_one (M : Model C dim ℝ)
    (sk : Skeleton C dim Bool ℝ) (visible : Finset C) (mix : ProbMixture C dim ℝ)
    (observation : Assignment C dim) (β : ℝ) :
    boltzmannTrueProbability M sk visible mix observation β ≤ 1 := by
  unfold boltzmannTrueProbability
  split
  · norm_num
  · rw [div_le_one (by positivity)]
    have := Real.exp_pos (β * M.fibreScore sk visible mix observation false /
      fibreMass M visible mix observation)
    linarith

/-! ## The sampled oracle -/

/-- The Boltzmann answer to one printed query: a single binary response drawn at
the model's own response probability.

The query's mixture weights are rational, as `subsec:queries` fixes them, and
meet the model's real value field through `ProbMixture.mapRat` — the same
crossing `exactPolicyAnswer` makes. -/
@[expose] public noncomputable def boltzmannAnswer (M : Model C dim ℝ)
    (sk : Skeleton C dim Bool ℝ) (β : ℝ) (q : ShiftedQuery sk) : PMF Bool :=
  PMF.ofFintype
    (fun b ↦ ENNReal.ofReal
      (if b then
        boltzmannTrueProbability M sk q.visible (q.mix.mapRat ℝ) q.observation β
      else
        1 - boltzmannTrueProbability M sk q.visible (q.mix.mapRat ℝ) q.observation β))
    (by
      have h0 := boltzmannTrueProbability_nonneg M sk q.visible (q.mix.mapRat ℝ)
        q.observation β
      have h1 := boltzmannTrueProbability_le_one M sk q.visible (q.mix.mapRat ℝ)
        q.observation β
      have hsum : ∑ b : Bool, ENNReal.ofReal
          (if b then
            boltzmannTrueProbability M sk q.visible (q.mix.mapRat ℝ) q.observation β
          else
            1 - boltzmannTrueProbability M sk q.visible (q.mix.mapRat ℝ) q.observation β)
          = ENNReal.ofReal
              (boltzmannTrueProbability M sk q.visible (q.mix.mapRat ℝ) q.observation β)
            + ENNReal.ofReal
              (1 - boltzmannTrueProbability M sk q.visible (q.mix.mapRat ℝ) q.observation β) := by
        simp
      rw [hsum, ← ENNReal.ofReal_add h0 (by linarith)]
      norm_num)

omit [Nonempty C] in
/-- **Behaviourally identical models answer identically.** `BoltzmannBehaviorEq`
equates the response probability at every mask inside `𝐎`, every mixture and
every observation; a `ShiftedQuery` carries exactly such a triple, with
`visible_subset` supplying the containment. -/
public theorem boltzmannAnswer_congr {sk : Skeleton C dim Bool ℝ} {β : ℝ}
    {M M' : Model C dim ℝ} (h : BoltzmannBehaviorEq sk β M M') (q : ShiftedQuery sk) :
    boltzmannAnswer M sk β q = boltzmannAnswer M' sk β q := by
  refine PMF.ext fun b ↦ ?_
  simp only [boltzmannAnswer, PMF.ofFintype_apply,
    h q.visible q.visible_subset (q.mix.mapRat ℝ) q.observation]

omit [Nonempty C] in
/-- **The channel loses nothing but the response probability.**

`boltzmannAnswer_congr` says equal response probabilities give equal answer
laws. This is its converse, and it is the lemma that keeps the floor below from
being an artefact of a degenerate oracle: a channel that ignored the model — one
that returned a fixed coin, say — would satisfy `boltzmannAnswer_congr`
vacuously and would floor the risk for a reason having nothing to do with a
collision. It cannot happen here, because the answer law determines the number
it was built from.

So the transcript-law collision proved below is exactly the behavioural
collision, neither more nor less. -/
public theorem boltzmannTrueProbability_of_answer_eq {sk : Skeleton C dim Bool ℝ}
    {β : ℝ} {M M' : Model C dim ℝ} (q : ShiftedQuery sk)
    (h : boltzmannAnswer M sk β q = boltzmannAnswer M' sk β q) :
    boltzmannTrueProbability M sk q.visible (q.mix.mapRat ℝ) q.observation β =
      boltzmannTrueProbability M' sk q.visible (q.mix.mapRat ℝ) q.observation β := by
  have happ := congrArg (fun p : PMF Bool ↦ p true) h
  simp only [boltzmannAnswer, PMF.ofFintype_apply, if_true] at happ
  exact (ENNReal.ofReal_eq_ofReal_iff
    (boltzmannTrueProbability_nonneg M sk q.visible (q.mix.mapRat ℝ) q.observation β)
    (boltzmannTrueProbability_nonneg M' sk q.visible (q.mix.mapRat ℝ) q.observation β)).1
    happ

/-! ## Transcripts, analysts and risk -/

/-- The analyst's record: the queries it issued and the **sampled responses** it
got back. Recording the queries is the perfect-recall requirement the exact
layer's `Transcript` documents; here it matters more, since two different
queries very often return the same bit. -/
public abbrev BoltzmannTranscript (sk : Skeleton C dim Bool ℝ) :=
  List (ShiftedQuery sk × Bool)

/-- A randomized adaptive query strategy against the Boltzmann channel. -/
public abbrev BoltzmannQueryStrategy (sk : Skeleton C dim Bool ℝ) :=
  BoltzmannTranscript sk → PMF (ShiftedQuery sk)

/-- The analyst's output after the interaction: a model, randomized, reading the
full transcript. -/
public abbrev BoltzmannEstimator (C : Type*) [Fintype C] [DecidableEq C]
    (dim : C → ℕ) :=
  ∀ sk : Skeleton C dim Bool ℝ, BoltzmannTranscript sk → PMF (Model C dim ℝ)

/-- The distribution over transcripts after `n` queries.

Unlike the exact layer, **the model appears here**: each step draws a query from
the strategy and then a response from that query's Boltzmann law, so the
transcript is a sample from an experiment indexed by `M`. That dependence is the
statistical content of `prob:boltzmann`(b). -/
@[expose] public noncomputable def runBoltzmannTranscript (sk : Skeleton C dim Bool ℝ)
    (M : Model C dim ℝ) (β : ℝ) (strategy : BoltzmannQueryStrategy sk) :
    ℕ → PMF (BoltzmannTranscript sk)
  | 0 => PMF.pure []
  | n + 1 =>
      (runBoltzmannTranscript sk M β strategy n).bind fun history ↦
        (strategy history).bind fun q ↦
          PMF.map (fun b ↦ history ++ [(q, b)]) (boltzmannAnswer M sk β q)

omit [Nonempty C] in
/-- **Two Boltzmann-indistinguishable models induce the same experiment.**

Every step of the interaction reads the model only through `boltzmannAnswer`, so
if the answers agree at every query the transcript laws agree at every budget.
This is why `prob:boltzmann`(a) has teeth for (b): a collision in (a) is not
merely a collision of behaviour, it is a collision of the entire statistical
experiment, and no amount of sampling separates the two models. -/
public theorem runBoltzmannTranscript_congr {sk : Skeleton C dim Bool ℝ} {β : ℝ}
    {M M' : Model C dim ℝ} (h : BoltzmannBehaviorEq sk β M M')
    (strategy : BoltzmannQueryStrategy sk) (n : ℕ) :
    runBoltzmannTranscript sk M β strategy n
      = runBoltzmannTranscript sk M' β strategy n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      unfold runBoltzmannTranscript
      rw [ih]
      exact congrArg _ (funext fun history ↦ congrArg _
        (funext fun q ↦ congrArg _ (boltzmannAnswer_congr h q)))

/-- The expected error of one randomized analyst against one model, after `n`
sampled queries. The expectation is over both of the analyst's randomizations
and over the channel's noise. -/
public noncomputable def boltzmannExpectedError (sk : Skeleton C dim Bool ℝ)
    (M : Model C dim ℝ) (β : ℝ) (strategy : BoltzmannQueryStrategy sk)
    (estimator : BoltzmannEstimator C dim) (n : ℕ) : ℝ :=
  pmfExpect (runBoltzmannTranscript sk M β strategy n) fun history ↦
    pmfExpect (estimator sk history) fun Mhat ↦ modelError M Mhat

/-- The supremum over the class, which is what a minimax risk maximizes. -/
public noncomputable def boltzmannAnalystRisk (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (β : ℝ) (n : ℕ)
    (strategy : BoltzmannQueryStrategy sk)
    (estimator : BoltzmannEstimator C dim) : ℝ :=
  sSup {e : ℝ | ∃ M ∈ modelClass,
    e = boltzmannExpectedError sk M β strategy estimator n}

/-- **The Boltzmann minimax risk at budget `n`**: the infimum over randomized
analysts of `boltzmannAnalystRisk`. The infimum is print's word, and it is the
reason a lower bound proved here is a lower bound on print's quantity rather
than on some analyst's performance. -/
@[expose] public noncomputable def boltzmannMinimaxRisk (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (β : ℝ) (n : ℕ) : ℝ :=
  sInf {r : ℝ | ∃ (strategy : BoltzmannQueryStrategy sk)
    (estimator : BoltzmannEstimator C dim),
      r = boltzmannAnalystRisk sk modelClass β n strategy estimator}

/-! ## Elementary bounds -/

public theorem boltzmannExpectedError_nonneg (sk : Skeleton C dim Bool ℝ)
    (M : Model C dim ℝ) (β : ℝ) (strategy : BoltzmannQueryStrategy sk)
    (estimator : BoltzmannEstimator C dim) (n : ℕ) :
    0 ≤ boltzmannExpectedError sk M β strategy estimator n :=
  pmfExpect_nonneg _ fun _ ↦ pmfExpect_nonneg _ fun Mhat ↦ modelError_nonneg M Mhat

public theorem boltzmannExpectedError_le_one (sk : Skeleton C dim Bool ℝ)
    (M : Model C dim ℝ) (β : ℝ) (strategy : BoltzmannQueryStrategy sk)
    (estimator : BoltzmannEstimator C dim) (n : ℕ) :
    boltzmannExpectedError sk M β strategy estimator n ≤ 1 := by
  refine pmfExpect_le _ (C := 1) (fun history ↦ ?_) 1 fun history ↦ ?_
  · rw [abs_of_nonneg (pmfExpect_nonneg _ fun Mhat ↦ modelError_nonneg M Mhat)]
    exact pmfExpect_le _ (fun Mhat ↦ by
      rw [abs_of_nonneg (modelError_nonneg M Mhat)]
      exact modelError_le_one M Mhat) 1 fun Mhat ↦ modelError_le_one M Mhat
  · exact pmfExpect_le _ (fun Mhat ↦ by
      rw [abs_of_nonneg (modelError_nonneg M Mhat)]
      exact modelError_le_one M Mhat) 1 fun Mhat ↦ modelError_le_one M Mhat

/-- Every analyst's risk on a nonempty class is at least its error against any
one member: the supremum is over a set bounded by `1`, so `le_csSup` applies. -/
public theorem boltzmannExpectedError_le_analystRisk {sk : Skeleton C dim Bool ℝ}
    {modelClass : Set (Model C dim ℝ)} {β : ℝ} {n : ℕ}
    {strategy : BoltzmannQueryStrategy sk} {estimator : BoltzmannEstimator C dim}
    {M : Model C dim ℝ} (hM : M ∈ modelClass) :
    boltzmannExpectedError sk M β strategy estimator n
      ≤ boltzmannAnalystRisk sk modelClass β n strategy estimator := by
  refine le_csSup ⟨1, ?_⟩ ⟨M, hM, rfl⟩
  rintro e ⟨N, -, rfl⟩
  exact boltzmannExpectedError_le_one sk N β strategy estimator n

/-- Every analyst's risk is at most `1`, on any class including the empty one:
`Real.sSup_le` supplies the empty case, where the convention gives `0`. -/
public theorem boltzmannAnalystRisk_le_one (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (β : ℝ) (n : ℕ)
    (strategy : BoltzmannQueryStrategy sk)
    (estimator : BoltzmannEstimator C dim) :
    boltzmannAnalystRisk sk modelClass β n strategy estimator ≤ 1 := by
  refine Real.sSup_le ?_ zero_le_one
  rintro e ⟨N, -, rfl⟩
  exact boltzmannExpectedError_le_one sk N β strategy estimator n

public theorem boltzmannAnalystRisk_nonneg (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (β : ℝ) (n : ℕ)
    (strategy : BoltzmannQueryStrategy sk)
    (estimator : BoltzmannEstimator C dim) :
    0 ≤ boltzmannAnalystRisk sk modelClass β n strategy estimator := by
  refine Real.sSup_nonneg ?_
  rintro e ⟨N, -, rfl⟩
  exact boltzmannExpectedError_nonneg sk N β strategy estimator n

/-- **The minimax risk is at most `1`.** Trivial as mathematics and not as
bookkeeping: paired with a floor it is what turns *"the risk does not vanish"*
into *"the risk is determined up to a constant"*, which is the shape
`prob:boltzmann`(b) asks its answer in.

The two instance arguments are the ones `Causal.Query`'s own closure theorems
carry, and for the same reason: a `PMF` needs an inhabited carrier, and the
witness analyst here is a pair of `PMF.pure`s. Both hold at `def:cid`'s binary
chance variables. -/
public theorem boltzmannMinimaxRisk_le_one (sk : Skeleton C dim Bool ℝ)
    [Nonempty (ShiftedQuery sk)] [Nonempty (Model C dim ℝ)]
    (modelClass : Set (Model C dim ℝ)) (β : ℝ) (n : ℕ) :
    boltzmannMinimaxRisk sk modelClass β n ≤ 1 := by
  refine le_trans (csInf_le ⟨0, ?_⟩ ⟨fun _ ↦ PMF.pure (Classical.arbitrary (ShiftedQuery sk)),
    fun _ _ ↦ PMF.pure (Classical.arbitrary (Model C dim ℝ)), rfl⟩) ?_
  · rintro r ⟨strategy, estimator, rfl⟩
    exact boltzmannAnalystRisk_nonneg sk modelClass β n strategy estimator
  · exact boltzmannAnalystRisk_le_one sk modelClass β n _ _

/-! ## The two-point floor

This is the step `conjectures.yaml`'s CONJ-008 entry says is missing, and says
correctly: `boltzmann_minimax_floor` bounds a **deterministic** estimator, and
deterministic strategies are a subset of randomized ones, so a lower bound on
their infimum carries no information about print's. The bound below is at
print's own quantifier — the infimum over randomized analysts. -/

omit [Nonempty C] in
private theorem inner_error_abs_le_one {sk : Skeleton C dim Bool ℝ}
    [Nonempty C] (estimator : BoltzmannEstimator C dim)
    (N : Model C dim ℝ) (history : BoltzmannTranscript sk) :
    |pmfExpect (estimator sk history) fun Mhat ↦ modelError N Mhat| ≤ 1 := by
  rw [abs_of_nonneg (pmfExpect_nonneg _ fun Mhat ↦ modelError_nonneg N Mhat)]
  exact pmfExpect_le _ (fun Mhat ↦ by
    rw [abs_of_nonneg (modelError_nonneg N Mhat)]
    exact modelError_le_one N Mhat) 1 fun Mhat ↦ modelError_le_one N Mhat

/-- **A Boltzmann collision floors the minimax risk at `1/2`, at every budget and
every inverse temperature.**

Two models of the class with different graphs and identical Boltzmann behaviour
induce the *same* transcript law, by `runBoltzmannTranscript_congr`, so an
analyst's output law is one and the same distribution under both. Print's error
is `1` against whichever graph the output misses, so the two expected errors sum
to at least `1` and their maximum — which the class supremum dominates — is at
least `1/2`. No budget helps, because the budget only lengthens a transcript
whose law does not depend on which of the two models is true.

**What this is and is not.** It is a lower bound on `prob:boltzmann`(b)'s
quantity, over the class it is stated on, uniform in `N` and in `β`. Paired with
`boltzmannMinimaxRisk_le_one` it determines that quantity up to a factor of two
on such a class — the rate is `Θ(1)`, hence no `β → 0` deterioration and no
`(N, β)` crossover. It says nothing about a class where the risk does decay,
which is where the rest of (b) lives.

The graph condition is not decoration: without it `modelError` is the table
supremum rather than `1`, `one_le_modelError_add` does not apply, and the floor
is not `1/2`. A same-graph Boltzmann collision is a collision and does not floor
the risk. So any positive rate answer to (b) has to restrict the class away from
graph-differing collisions specifically.

**`[Nonempty (ShiftedQuery sk)]` is a hypothesis print does not write, and it is
load-bearing for truth rather than for the proof.** With no query available no
analyst exists, so the set `boltzmannMinimaxRisk` takes the infimum of is empty,
the lattice convention gives `sInf ∅ = 0`, and the bound below is false. Print
takes an inhabited query set for granted — `subsec:queries` builds every protocol
out of triples `(σ, 𝐎', w)` — so this is the printed setting made explicit and
not a restriction of it, and it is satisfied at the witness class in
`Examples/Conjectures/MAIS/O29.lean`. It is the same convention
`realRegretRadius` carries a warning about on the other side, where an empty
margin class makes a *positive* answer to `prob:floor`(a) cheap. -/
public theorem half_le_boltzmannMinimaxRisk_of_collision
    {sk : Skeleton C dim Bool ℝ} [Nonempty (ShiftedQuery sk)]
    {modelClass : Set (Model C dim ℝ)} {β : ℝ} {M M' : Model C dim ℝ}
    (hM : M ∈ modelClass) (hM' : M' ∈ modelClass)
    (hpar : M.parents ≠ M'.parents) (hbeh : BoltzmannBehaviorEq sk β M M')
    (n : ℕ) :
    1 / 2 ≤ boltzmannMinimaxRisk sk modelClass β n := by
  refine le_csInf ⟨boltzmannAnalystRisk sk modelClass β n
      (fun _ ↦ PMF.pure (Classical.arbitrary (ShiftedQuery sk)))
      (fun _ _ ↦ PMF.pure M), ⟨_, _, rfl⟩⟩ ?_
  rintro r ⟨strategy, estimator, rfl⟩
  have hlaw := runBoltzmannTranscript_congr hbeh strategy n
  have hsum : boltzmannExpectedError sk M β strategy estimator n
      + boltzmannExpectedError sk M' β strategy estimator n
      = pmfExpect (runBoltzmannTranscript sk M β strategy n) fun history ↦
          pmfExpect (estimator sk history) fun Mhat ↦
            modelError M Mhat + modelError M' Mhat := by
    unfold boltzmannExpectedError
    rw [← hlaw, ← pmfExpect_add _ (C := 1)
      (inner_error_abs_le_one estimator M) (inner_error_abs_le_one estimator M')]
    exact congrArg _ (funext fun history ↦
      (pmfExpect_add _ (C := 1)
        (fun Mhat ↦ by
          rw [abs_of_nonneg (modelError_nonneg M Mhat)]
          exact modelError_le_one M Mhat)
        (fun Mhat ↦ by
          rw [abs_of_nonneg (modelError_nonneg M' Mhat)]
          exact modelError_le_one M' Mhat)).symm)
  have hone : 1 ≤ boltzmannExpectedError sk M β strategy estimator n
      + boltzmannExpectedError sk M' β strategy estimator n := by
    rw [hsum]
    refine le_pmfExpect _ (C := 2) (fun history ↦ ?_) 1 fun history ↦ ?_
    · rw [abs_of_nonneg (pmfExpect_nonneg _ fun Mhat ↦ by
        have := modelError_nonneg M Mhat
        have := modelError_nonneg M' Mhat
        linarith)]
      exact pmfExpect_le _ (C := 2) (fun Mhat ↦ by
        rw [abs_of_nonneg (by
          have := modelError_nonneg M Mhat
          have := modelError_nonneg M' Mhat
          linarith)]
        have := modelError_le_one M Mhat
        have := modelError_le_one M' Mhat
        linarith) 2 fun Mhat ↦ by
          have := modelError_le_one M Mhat
          have := modelError_le_one M' Mhat
          linarith
    · refine le_pmfExpect _ (C := 2) (fun Mhat ↦ ?_) 1
        fun Mhat ↦ one_le_modelError_add hpar Mhat
      rw [abs_of_nonneg (by
        have := modelError_nonneg M Mhat
        have := modelError_nonneg M' Mhat
        linarith)]
      have := modelError_le_one M Mhat
      have := modelError_le_one M' Mhat
      linarith
  have h1 : boltzmannExpectedError sk M β strategy estimator n
      ≤ boltzmannAnalystRisk sk modelClass β n strategy estimator :=
    boltzmannExpectedError_le_analystRisk hM
  have h2 : boltzmannExpectedError sk M' β strategy estimator n
      ≤ boltzmannAnalystRisk sk modelClass β n strategy estimator :=
    boltzmannExpectedError_le_analystRisk hM'
  linarith

/-! ## MAIS-O29(b) as a specification over a supplied rate

`prob:boltzmann`(b) reads *"for each fixed finite `β`, determine the minimax
risk at budget `N` up to constants, including the deterioration as `β → 0`"*.
That is a determine-clause and no `Prop` is `Same` as it, but *"this rate is the
answer"* is a proposition, and it is the one a solver would prove. -/

/-- **A candidate rate is correct when it brackets the risk up to absolute
constants.**

The constants are quantified *before* the budget and the inverse temperature,
which is what *"up to constants"* means and what makes the statement have
content: constants allowed to depend on `(N, β)` could bracket anything. Print
names the `β → 0` deterioration in the same sentence, and a rate uniform in both
arguments is what carries it — a bound holding for each `β` separately says
nothing about how the risk behaves as `β` shrinks. -/
public noncomputable def IsBoltzmannRiskRate (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (rate : ℕ → ℝ → ℝ) : Prop :=
  ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
    ∀ (n : ℕ) (β : ℝ), 0 < β →
      c₁ * rate n β ≤ boltzmannMinimaxRisk sk modelClass β n ∧
        boltzmannMinimaxRisk sk modelClass β n ≤ c₂ * rate n β

/-- The specification unfolds, since a `public def` exports its type and not its
body and a witness module has to supply the two brackets. -/
public theorem isBoltzmannRiskRate_iff (sk : Skeleton C dim Bool ℝ)
    (modelClass : Set (Model C dim ℝ)) (rate : ℕ → ℝ → ℝ) :
    IsBoltzmannRiskRate sk modelClass rate ↔
      ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧
        ∀ (n : ℕ) (β : ℝ), 0 < β →
          c₁ * rate n β ≤ boltzmannMinimaxRisk sk modelClass β n ∧
            boltzmannMinimaxRisk sk modelClass β n ≤ c₂ * rate n β := Iff.rfl

end AISafetyAtlas.Conjectures.MAIS
