module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import AISafetyAtlas.Examples.Causal.OneNodeClass
public import AISafetyAtlas.Examples.Causal.Query
public import AISafetyAtlas.Examples.Conjectures.MAIS.Common

/-!
# MAIS-O29(a) resolved, and a floor under (b)

Part (a) is discharged at every positive `β`.

Two results here speak to part (b) and they are not the same statement, which is
why both are kept. `boltzmann_minimax_floor` bounds a **deterministic**
estimator, and `prob:boltzmann`(b) takes an infimum over randomized ones, so it
is *not* a bound on print's quantity — deterministic strategies are a subset, and
a lower bound on the larger infimum says nothing about the smaller.
`half_le_boltzmannMinimaxRisk_collision` is the bound at print's quantifier: the
randomized minimax risk over the sampled experiment, floored at `1/2` on the full
margin class, uniformly in the budget and in `β`.

Paired with `boltzmannMinimaxRisk_le_one`, that floor **determines** (b)'s
quantity up to a factor of two at this skeleton —
`boltzmannMinimaxRisk_collision_bounds` — uniformly in the budget and in `β`.
There is no rate here to deteriorate as `β → 0` and no `(N, β)` crossover to
characterize, because the risk never decays. That answers (b) at one print-legal
instance and not at every one; on a class where the risk *does* decay, none of
(b) is touched.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal


/-! ## MAIS-O29(a): the checked collision survives the Boltzmann channel

The O23 witness pair has equal masked transforms on the real chart. Because
`skel` observes nothing, every Boltzmann fibre is the whole space, so both fibre
masses are `1` and the response is a softmax of the two full expectations
`E[u d]`. A two-point softmax depends only on the *difference* of its scores,
and `Model.fibreScore_true_sub_false` names that difference as `Δmask`. Equal
transforms therefore pin the response at every inverse temperature at once.

This runs through the general
`boltzmannBehaviorEq_of_behaviorEq_of_observed_empty` rather than through the
witness's own arithmetic, so it says something about every behavioral collision
on an unobserving skeleton and not only about this pair. -/

/-- At the empty mask the fibre is the whole space. -/
public theorem fibreScore_empty (M : Model (Fin 2) (binaryDim (Fin 2)) ℚ)
    (mix : ProbMixture (Fin 2) (binaryDim (Fin 2)) ℚ)
    (obs : Assignment (Fin 2) (binaryDim (Fin 2))) (d : Bool) :
    M.fibreScore skel ∅ mix obs d = ∑ v, M.jointProbMix mix.1 v * u d v :=
  Finset.sum_congr (Finset.filter_true_of_mem (by simp)) (fun _ _ ↦ rfl)

/-- The two Boltzmann scores are the transform's affine halves: their sum is the
total mass `1` and their difference is `Δ`. -/
public theorem fibreScore_empty_eq_of_Δmix
    (M M' : Model (Fin 2) (binaryDim (Fin 2)) ℚ)
    (mix : ProbMixture (Fin 2) (binaryDim (Fin 2)) ℚ)
    (obs : Assignment (Fin 2) (binaryDim (Fin 2))) (d : Bool)
    (h : M.Δmix g mix.1 = M'.Δmix g mix.1) :
    M.fibreScore skel ∅ mix obs d = M'.fibreScore skel ∅ mix obs d := by
  have key : ∀ N : Model (Fin 2) (binaryDim (Fin 2)) ℚ,
      2 * (∑ v, N.jointProbMix mix.1 v * u d v)
        = (if d then (1 : ℚ) else -1) * N.Δmix g mix.1 + 1 := by
    intro N
    have hsum : ∑ v, N.jointProbMix mix.1 v = 1 := N.jointProbMix_sum mix
    rw [Finset.mul_sum]
    have hpt : ∀ v, 2 * (N.jointProbMix mix.1 v * u d v)
        = (if d then (1 : ℚ) else -1) * (N.jointProbMix mix.1 v * g v)
          + N.jointProbMix mix.1 v := by
      intro v
      cases d <;> simp [u] <;> ring
    rw [Finset.sum_congr rfl fun v _ ↦ hpt v, Finset.sum_add_distrib,
      ← Finset.mul_sum, hsum]
    rfl
  rw [fibreScore_empty, fibreScore_empty]
  have hM := key M
  have hM' := key M'
  rw [h] at hM
  linarith

/-- **MAIS-O29(a), negative branch, machine-checked.** The O23 margin-class
collision on the source's real chart is also a Boltzmann collision, at every
positive inverse temperature. -/
public theorem boltzmann_collision_real (β : ℝ)
    {M M' : Model (Fin 2) (binaryDim (Fin 2)) ℝ}
    (hbeh : (skel.mapRat ℝ).BehaviorEq M M') :
    BoltzmannBehaviorEq (skel.mapRat ℝ) β M M' :=
  boltzmannBehaviorEq_of_behaviorEq_of_observed_empty (by simp [skel]) hbeh β

/-- **CONJ-008 is resolved.** -/
public theorem maisO29_boltzmannNotInjective_holds :
    maisO29_boltzmannNotInjective := by
  intro β _
  obtain ⟨hlam, M, M', hM, hM', _, hne, hbeh⟩ := margin_class_not_identifiable_real
  exact ⟨1, skel.mapRat ℝ, ((lam : ℚ) : ℝ), hlam, M, M', hM, hM', hne,
    boltzmann_collision_real β hbeh⟩

/-! ## MAIS-O29(b): the same collision puts a floor under the minimax risk

Problem 4.8(b) asks for the minimax risk at budget `N`, including its behaviour
as `β → 0`. On the full margin class that question has no vanishing answer: the
pair below induces *literally the same* responses at every query and every
temperature, so no procedure reading those responses can separate them, at any
budget. (b) is therefore only well posed on a genericity-restricted subclass —
the same move O26 makes when it passes from `M(s,λ)` to `M(s,λ,μ)`.

**What is proved here, and what is not.** The floor below is over
**deterministic** estimators. Print's risk is an infimum over *randomized*
analyst strategies, and deterministic ones are a subset, so a floor on the
deterministic infimum bounds the **larger** quantity and does not bound print's.
For the two colliding models, randomization gives a `1/2` lower bound for the
two-model subproblem, hence for print's full-class minimax risk. The full-class
value need not equal `1/2` and is **not determined here**. `CONJ-008` records the
same retraction and stays `RESOLVED` for part (a) only.

This is the behaviour-factoring form of the obstruction, which is what the
current definitions can state. The sampled form — an estimator reading `N` draws
from these responses — needs the statistical-experiment layer the coverage matrix
still lists as absent. That the law of the sample is a function of the response
probabilities makes the implication plausible; no such derivation is carried out
here, so it is a conjecture about this development and not a consequence of
it. -/

/-- The complete Boltzmann behaviour of a model on the real chart. Since `skel`
observes nothing, the empty mask is the only admissible one, so this function
*is* the whole behaviour family rather than one component of it. -/
public noncomputable def boltzmannBehavior
    (M : Model (Fin 2) (binaryDim (Fin 2)) ℝ) (β : ℝ) :
    ProbMixture (Fin 2) (binaryDim (Fin 2)) ℝ →
      Assignment (Fin 2) (binaryDim (Fin 2)) → ℝ :=
  fun mix obs ↦ boltzmannTrueProbability M (skel.mapRat ℝ) ∅ mix obs β

public theorem boltzmannBehavior_collision (β : ℝ)
    {M M' : Model (Fin 2) (binaryDim (Fin 2)) ℝ}
    (hbeh : (skel.mapRat ℝ).BehaviorEq M M') :
    boltzmannBehavior M β = boltzmannBehavior M' β := by
  funext mix obs
  exact boltzmann_collision_real β hbeh ∅ (by simp [skel]) mix obs

/-- One estimate cannot be close to two models with different graphs: the graph
mismatch alone already costs the maximal model error. -/
public theorem modelError_floor_of_parents_ne
    (M M' E : Model (Fin 2) (binaryDim (Fin 2)) ℝ) (h : M.parents ≠ M'.parents) :
    1 ≤ max (modelError M E) (modelError M' E) := by
  by_cases hM : M.parents = E.parents
  · have hM' : M'.parents ≠ E.parents := fun hc ↦ h (hM.trans hc.symm)
    have hone : modelError M' E = 1 := by unfold modelError; rw [if_neg hM']
    rw [hone]
    exact le_max_right _ _
  · have hone : modelError M E = 1 := by unfold modelError; rw [if_neg hM]
    rw [hone]
    exact le_max_left _ _

/-- **A deterministic estimator is maximally wrong on one of two colliding
models**, at every positive inverse temperature. The bound mentions no query
budget because it does not depend on one: the two models are indistinguishable
through this channel however long the analyst looks.

**This is not a lower bound on MAIS-O29(b)'s minimax risk, and an earlier
version of this docstring said it was.** `subsec:queries` defines that risk as
*"the infimum over (randomized) analyst strategies of the supremum … of the
expected error"*. Deterministic strategies are a **subset** of the randomized
ones, so an infimum over them is `≥` the infimum print takes, and bounding the
larger quantity from below says nothing about the smaller one. The direction is
wrong, not merely the constant.

The constant is wrong too, and the gap is exactly the randomization: against
these two models the analyst who returns each graph with probability `1/2` has
expected error about `1/2` in both. So `1/2`, not `1`, is the value of the
two-model subproblem, and it lower-bounds print's full-class minimax risk
without upper-bounding it — the full class also requires estimating tables.

**That `1/2` bound is proved**, at print's own quantifier, by
`half_le_boltzmannMinimaxRisk_collision` below, over the sampled experiment in
`AISafetyAtlas.Conjectures.MAIS.O29Experiment`. This theorem is kept because it
is what a *deterministic* reading gives and because the distinction between the
two is the thing a reader most needs to see; it is no longer the strongest
statement here.

`e` itself is print's, not an atlas convention: *"the error against `M = (G,θ)`
is `1` if `Ĝ ≠ G`, and otherwise the maximum entrywise difference of the
tables"*, which is what `modelError` computes. -/
public theorem boltzmann_minimax_floor (β : ℝ)
    (est : (ProbMixture (Fin 2) (binaryDim (Fin 2)) ℝ →
      Assignment (Fin 2) (binaryDim (Fin 2)) → ℝ) →
      Model (Fin 2) (binaryDim (Fin 2)) ℝ)
    {M M' : Model (Fin 2) (binaryDim (Fin 2)) ℝ} (hp : M.parents ≠ M'.parents)
    (hbeh : (skel.mapRat ℝ).BehaviorEq M M') :
    1 ≤ max (modelError M (est (boltzmannBehavior M β)))
        (modelError M' (est (boltzmannBehavior M' β))) := by
  rw [boltzmannBehavior_collision β hbeh]
  exact modelError_floor_of_parents_ne M M' _ hp


/-! ## MAIS-O29(b) at print's own quantifier

The theorem above is about a deterministic estimator, and the paragraph in its
docstring explains why that is the wrong direction for a minimax lower bound.
This is the right one: the infimum over **randomized** analysts, over the
sampled Boltzmann experiment, at every budget and every inverse temperature.

The mechanism is that the collision is not merely behavioural. Because the
response law at every printed query is a function of the model only through
`boltzmannTrueProbability`, two Boltzmann-indistinguishable models induce the
same distribution over transcripts — `runBoltzmannTranscript_congr` — so the
analyst's output law is one and the same under both, however many queries it
issues. Print's error is `1` against whichever graph that output misses, so the
two expected errors sum to at least `1`. -/

/-- **A floor under MAIS-O29(b)'s minimax risk on the full margin class**, at
every budget `n` and every inverse temperature `β`.

`prob:boltzmann`(b) asks to determine the minimax risk at budget `N` up to
constants, including its deterioration as `β → 0`. This does not determine it.
What it settles is that the quantity does not vanish on `𝕄(sk, λ)` at this
skeleton — not as the budget grows, and not as `β` varies — so any rate answer
to (b) has to restrict the class away from **graph-differing** collisions like
this one, which is the same move `conj:exact` makes when it passes from
`𝕄(sk, λ)` to `𝕄(sk, λ, μ)`. The graph condition is what makes the error `1`
against the model the output misses; two Boltzmann-indistinguishable models
sharing a graph do not floor the risk at `1/2`.

The class here is the printed margin class itself, not a two-point subclass: the
supremum over a larger class only rises, so a floor proved through two of its
members floors the whole class. -/
public theorem half_le_boltzmannMinimaxRisk_collision (β : ℝ) (n : ℕ) :
    1 / 2 ≤ boltzmannMinimaxRisk (skel.mapRat ℝ)
      {N | (skel.mapRat ℝ).MarginClass N ((lam : ℚ) : ℝ)} β n := by
  obtain ⟨-, M, M', hM, hM', hpar, -, hbeh⟩ := margin_class_not_identifiable_real
  exact half_le_boltzmannMinimaxRisk_of_collision hM hM' hpar
    (boltzmann_collision_real β hbeh) n


/-- **MAIS-O29(b) determined up to a factor of two at the collision skeleton**,
uniformly in the budget and in the inverse temperature.

`prob:boltzmann`(b) asks, *"for each fixed finite `β`, determine the minimax risk
at budget `N` up to constants, including the deterioration as `β → 0`"*, and then
to characterize the `(N, β)` crossover from the smooth local rate to the
noiseless adaptive-search regime as `β → ∞`. On this class the answer is that
there is no rate: the risk is pinned between `1/2` and `1` at **every** budget
and **every** positive `β`, so it neither deteriorates as `β → 0` nor improves as
`β → ∞`, and no crossover exists to characterize.

That is a complete answer to (b) at one print-legal instance and not at every
one, the same standing as the MAIS-O27(a) negative instance. It is also the
reason (b) is interesting elsewhere: a class where the risk *does* decay must
exclude graph-differing Boltzmann collisions, and `conj:exact` shows the shape
such an exclusion takes when it passes from `𝕄(sk, λ)` to `𝕄(sk, λ, μ)`.

The upper half is not a claim about this witness — every minimax risk here is at
most `1`, because print's error is. Its content is entirely in being paired with
the floor. -/
public theorem boltzmannMinimaxRisk_collision_bounds (β : ℝ) (n : ℕ) :
    1 / 2 ≤ boltzmannMinimaxRisk (skel.mapRat ℝ)
        {N | (skel.mapRat ℝ).MarginClass N ((lam : ℚ) : ℝ)} β n ∧
      boltzmannMinimaxRisk (skel.mapRat ℝ)
        {N | (skel.mapRat ℝ).MarginClass N ((lam : ℚ) : ℝ)} β n ≤ 1 :=
  ⟨half_le_boltzmannMinimaxRisk_collision β n,
    boltzmannMinimaxRisk_le_one _ _ β n⟩


/-- **The risk is `Θ(1)` at the collision skeleton: it lies in `[1/2, 1]` at
every budget and every inverse temperature.**

`IsBoltzmannRiskRate` is the specification a proposed answer to
`prob:boltzmann`(b) has to satisfy, and this is the first answer to satisfy it.

**Reading the numbers, because three of them are easy to confuse.** The
`fun _ _ ↦ 1` below is the *rate function*, not a value of the risk: the
specification asks for `c₁ · rate ≤ risk ≤ c₂ · rate`, and the proof supplies
`c₁ = 1/2` and `c₂ = 1`. So what is proved about the risk is `1/2 ≤ risk ≤ 1`,
and the constant rate says only that this bracket does not move with the budget
or the temperature — the risk is `Θ(1)`.

The lower `1/2` is `half_le_boltzmannMinimaxRisk_collision`, over **randomized**
adaptive analysts, and it is the number with content: the transcript law is the
same under both models, so the analyst's output law is one distribution, the two
expected errors sum to at least `1`, and the class supremum dominates their
maximum. The upper `1` is `boltzmannMinimaxRisk_le_one` and is trivial — print's
error is bounded by `1`, so every minimax risk here is — with its whole value in
being paired with the floor.

Neither is `boltzmann_minimax_floor`'s `1`. That one bounds a **deterministic**
estimator's error against whichever of the two models it misses, and it is
*retracted* as a bound on print's quantity: deterministic strategies are a
subset of randomized ones, so a lower bound on the larger infimum says nothing
about the smaller. It survives above as history, not as evidence.

The content is in what the constant rate *denies*. `prob:boltzmann`(b) expects a
smooth local rate *"typically proportional to `1/(β√N)`"* and asks for the
deterioration as `β → 0` and the `(N, β)` crossover as `β → ∞`. A rate that does
not vary in either argument says there is no deterioration and no crossover
here: the risk never decays, because the class contains two models with
different graphs that no amount of sampling separates. Any answer with a `√N` in
it therefore lives on a class that excludes graph-differing Boltzmann
collisions, and `q:ident`'s negative answer says such collisions exist inside
`𝕄(sk, λ)`.

**Non-vacuity, which is why this theorem is here and not just the two bounds.**
A specification nobody has satisfied is indistinguishable from one that cannot
be satisfied, and the difference is exactly what a reader wants to know. -/
public theorem isBoltzmannRiskRate_collision :
    IsBoltzmannRiskRate (skel.mapRat ℝ)
      {N | (skel.mapRat ℝ).MarginClass N ((lam : ℚ) : ℝ)} (fun _ _ ↦ 1) := by
  -- Through the characterization rather than by unfolding: `IsBoltzmannRiskRate`
  -- is a `public def`, so its body does not cross the module boundary.
  refine (isBoltzmannRiskRate_iff _ _ _).mpr
    ⟨1 / 2, 1, by norm_num, by norm_num, fun n β _ ↦ ?_⟩
  obtain ⟨hlow, hhigh⟩ := boltzmannMinimaxRisk_collision_bounds β n
  constructor
  · simpa using hlow
  · simpa using hhigh


end AISafetyAtlas.Examples.Conjectures.MAIS
