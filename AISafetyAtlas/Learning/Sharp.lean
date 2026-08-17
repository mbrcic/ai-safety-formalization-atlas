module

public import AISafetyAtlas.Learning
public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Fintype.Powerset
public import AISafetyAtlas.Combinatorics.PermInvariance

/-!
# The sharp No Free Lunch: closed under permutation, both directions

`AISafetyAtlas.Learning` proves No Free Lunch for the **uniform** average over
all objectives. That is one point of a much larger picture, and the picture has
an exact boundary: NFL holds for a weighting of the objectives **if and only if**
that weighting is invariant under permutations of the search domain.

This is `CT-10`. Sources:

* D. Schumacher, M. D. Vose, L. D. Whitley, *The No Free Lunch and Problem
  Description Length*, GECCO 2001 — the first closed-under-permutation
  characterization, stated for a **set** of objectives.
* C. Igel, M. Toussaint, *A No-Free-Lunch Theorem for Non-Uniform Distributions
  of Target Functions*, J. Math. Modelling and Algorithms 3(4), 2004,
  doi `10.1023/B:JMMA.0000049381.24625.f7` — both directions, for a
  **distribution**.

## Why this is the general statement

The uniform cores already in `AISafetyAtlas.Learning` are the special case of a
constant weight, which is permutation-invariant for trivial reasons; that
derivation is `no_free_lunch_embedding_of_sharp`. The set form of
Schumacher–Vose–Whitley is the case of an indicator weight
(`permInvariant_of_closedUnderPermutation`).

The condition is also what makes NFL *vacuous* in practice: real priors over
learning problems are structured, hence not permutation-symmetric, hence outside
the hypothesis. Knowing the exact boundary is what lets a consumer say so.

## Where this is stronger than the printed sources

| | printed | this module |
|---|---|---|
| weight | a probability distribution over objectives | **any** real-valued weight — no nonnegativity, no normalization |
| the necessary direction | assumes NFL for all algorithms, all lengths, all measures | assumes it only for **schedules**, at the single length `m = \|X\|`, and only at **indicator** measures |

Splitting the two directions this way is the substantive gain: the hypothesis of
`permInvariant_of_nfl` is much weaker than the conclusion of
`nfl_adaptive_of_permInvariant`, so the `iff` in `nfl_adaptive_iff_permInvariant`
is not the sharpest form of either half. Dropping nonnegativity and normalization
matters because it makes the result applicable to signed weightings —
differences of two priors, for instance — for which "distribution" is the wrong
word and the printed statements do not apply.

**Not a widening: the sample length.** NFL at every sample length `m` is *not* a
gain over print, though it can look like one. Igel–Toussaint's
Theorem 5 already concludes "for any two algorithms `a` and `b`, any value
`k ∈ ℝ`, any `m ∈ {1, …, |X|}`, and any performance measure `c`" — every sample
length and every cost measure are in the printed statement. The sufficient
direction here matches print on that axis; it does not exceed it.

## The algorithm class

Both sources quantify over **non-repeating black-box** algorithms, which choose
each query from the costs already seen. That is `AdaptiveRule` together with the
no-revisit hypothesis `∀ c, Injective (ruleVisit r c)`, and
`nfl_adaptive_of_permInvariant` is the sufficient direction over exactly that
class. `nfl_of_permInvariant` is the fixed-schedule special case, kept because
it is the form the rest of the atlas consumes.

The bridge is `scheduleRule`, which reads a schedule as a rule ignoring its
history. It also carries the necessary direction upward for free: a probe built
from schedules is already a probe built from rules.

## Explicit non-claims

No time-varying objectives: the objective is fixed for the run. **Stochastic
algorithms are covered** — see `mixtureTrace` and `stochasticTrace` below, which
are Droste–Jansen–Wegener's own two pictures of a randomized search heuristic —
so this is no longer a non-claim, and what is left on that axis belongs to
Wolpert–Macready rather than to Igel–Toussaint or SVW. The characterization is of
the **prior** axis — what is proved about the algorithm class is that it does not
matter, not that every algorithm is covered. The loss-axis `iff`
(`homogeneous_iff_learner_indep`) is a separate, folklore result and is
untouched.

**The bridge from Theorem 4 to "this family is not closed under permutation" is
not proved here.** Theorem 4 says a non-trivial neighbourhood relation is not
permutation-invariant. It does *not* follow that a search space carrying such a
relation has no permutation-closed prior, and unqualified that is **false** —
`PermInvariant` is a predicate on `ObjectiveWeight X Y`, a neighbourhood
relation is a relation on `X`, and the uniform weight is permutation-invariant
whatever structure `X` carries. Print supplies the missing step separately, in
its Examples 2 and 3, and neither is formalized. See the non-claim beside
`exists_perm_rel_not_iff` for the detail.

**The double-exponential asymptotic of Theorem 3 is not proved.** The counts and
the printed fraction are; the claim that the fraction vanishes double
exponentially is an estimate on binomial coefficients and is graded `No`.
-/

open Classical
open Fintype Function
open AISafetyAtlas.Combinatorics

namespace AISafetyAtlas.Learning

universe uX uY

variable {X : Type uX} {Y : Type uY}

/-! ## Weighted aggregate performance -/

/--
A weighting of the objectives. Deliberately **not** required to be nonnegative
or to sum to one: every result below holds for an arbitrary real weight, and the
probability-distribution case of the printed sources is the special case.
-/
public abbrev ObjectiveWeight (X Y : Type*) := (X → Y) → ℝ

/--
Aggregate performance of a schedule under a weighting of the objectives.
`AISafetyAtlas.Learning.aggregatePerformance` is the constant-weight case.
-/
@[expose] public noncomputable def weightedPerformance [Fintype X] [Fintype Y] {m : ℕ}
    (P : ObjectiveWeight X Y) (Φ : CostPerformance m Y) (σ : Fin m ↪ X) : ℝ :=
  ∑ f : X → Y, P f * Φ (fun i => f (σ i))

/--
Aggregate performance of an **adaptive rule** under a weighting of the
objectives: the weighted total, over all objectives, of a functional of the cost
sequence the rule observes.

The schedule form `weightedPerformance` is the special case
`weightedTrace P Φ (scheduleRule σ)` — see `weightedPerformance_eq_adaptive`.
-/
@[expose] public noncomputable def weightedTrace [Fintype X] [Fintype Y] {m : ℕ}
    (P : ObjectiveWeight X Y) (Ψ : (Fin m → Y) → ℝ) (r : AdaptiveRule X Y m) : ℝ :=
  ∑ f : X → Y, P f * Ψ (observed r f)

/--
**Closed under permutation.** Relabelling the search domain does not change the
weight an objective receives. For an indicator weight this is exactly
Schumacher–Vose–Whitley's condition on a *set*; for a distribution it is
Igel–Toussaint's.
-/
@[expose] public def PermInvariant (P : ObjectiveWeight X Y) : Prop :=
  ∀ (π : Equiv.Perm X) (f : X → Y), P (f ∘ π) = P f

/-! ## Any two schedules of the same length differ by a permutation -/

/--
On a finite domain, two injective schedules of the same length are related by a
permutation of the domain. This is what makes permutation-invariance the right
condition: it is exactly the symmetry that identifies schedules.
-/
public theorem exists_perm_comp [Fintype X] {m : ℕ} (σ τ : Fin m ↪ X) :
    ∃ π : Equiv.Perm X, ∀ i, π (σ i) = τ i := by
  classical
  have hcard : card {x // x ∈ Set.range (σ : Fin m → X)}
      = card {x // x ∈ Set.range (τ : Fin m → X)} := by
    rw [card_congr σ.toEquivRange.symm, card_congr τ.toEquivRange.symm]
  let e : {x // x ∈ Set.range (σ : Fin m → X)} ≃ {x // x ∈ Set.range (τ : Fin m → X)} :=
    σ.toEquivRange.symm.trans τ.toEquivRange
  refine ⟨e.extendSubtype, fun i => ?_⟩
  have hmem : σ i ∈ Set.range (σ : Fin m → X) := Set.mem_range_self i
  rw [Equiv.extendSubtype_apply_of_mem e _ hmem]
  have : (⟨σ i, hmem⟩ : {x // x ∈ Set.range (σ : Fin m → X)}) = σ.toEquivRange i := by
    simp [Embedding.toEquivRange]
  rw [this]
  simp [e, Embedding.toEquivRange]

/-! ## Permutation invariance is sufficient -/

/--
**The sufficient direction, at every sample length.** If the weighting is
invariant under permutations of the domain, then no schedule beats any other —
for any cost-sequence performance measure and any length `m`.

Universal quantification over `m` matches print rather than exceeding it:
Igel–Toussaint's Theorem 5 already concludes for "any `m ∈ {1, …, |X|}`, and any
performance measure `c`". What this statement fixes, and print does not, is the
algorithm class — schedules here, non-repeating black-box algorithms there; the
printed class is reached by `nfl_adaptive_of_permInvariant`.
-/
public theorem nfl_of_permInvariant [Fintype X] [Fintype Y] {m : ℕ}
    {P : ObjectiveWeight X Y} (hP : PermInvariant P)
    (Φ : CostPerformance m Y) (σ τ : Fin m ↪ X) :
    weightedPerformance P Φ σ = weightedPerformance P Φ τ := by
  classical
  obtain ⟨π, hπ⟩ := exists_perm_comp σ τ
  let e : (X → Y) ≃ (X → Y) := Equiv.arrowCongr π (Equiv.refl Y)
  refine Fintype.sum_equiv e _ _ fun g => ?_
  have hcomp : (e g) = g ∘ (π.symm : X → X) := rfl
  have hval : ∀ i, (e g) (τ i) = g (σ i) := by
    intro i
    rw [hcomp]
    show g (π.symm (τ i)) = g (σ i)
    rw [← hπ i, Equiv.symm_apply_apply]
  have hweight : P (e g) = P g := by
    rw [hcomp]
    exact hP π.symm g
  rw [hweight]
  congr 1
  exact congrArg Φ (funext fun i => (hval i).symm)

/-! ## Permutation invariance is sufficient for adaptive algorithms too

Both printed sources quantify over *non-repeating black-box* algorithms, which
choose each query from the costs already seen. `nfl_of_permInvariant` above
covers only fixed schedules, so on its own it is narrower than print. This
section removes that restriction, using the adaptive model of
`AISafetyAtlas.Learning`. -/

/-! ### Permuting the algorithm, and permuting the objective

Schumacher–Vose–Whitley's duality: relabelling the search domain can be charged
either to the algorithm or to the objective, and the trace is the same. This is
the structural fact their characterization rests on, so it is proved here rather
than absorbed into the NFL argument. -/

/-- Relabel an adaptive rule by a permutation of the search domain: wherever the
rule would query `x`, the relabelled rule queries `π x`. -/
@[expose] public def permRule {m : ℕ} (π : Equiv.Perm X) (r : AdaptiveRule X Y m) :
    AdaptiveRule X Y m :=
  fun k h => π (r k h)

/--
**Duality of relabelling** — Schumacher–Vose–Whitley's corollary
`V(A, σf) = V(σA, f)`.

Running the relabelled rule on `f` sees exactly what the original rule sees on
the relabelled objective. Neither side is a special case of the other; the
content is that the two relabellings cancel.
-/
public theorem observed_permRule {m : ℕ} (π : Equiv.Perm X) (r : AdaptiveRule X Y m)
    (f : X → Y) :
    observed (permRule π r) f = observed r (f ∘ (π : X → X)) := by
  have hpre : ∀ (n : ℕ) (h : n ≤ m),
      obsPrefix (permRule π r) f n h = obsPrefix r (f ∘ (π : X → X)) n h := by
    intro n
    induction n with
    | zero => intro _; funext i; exact i.elim0
    | succ n ih =>
      intro h
      have hn := ih (Nat.le_of_succ_le h)
      have hL : obsPrefix (permRule π r) f (n + 1) h
          = Fin.snoc (obsPrefix (permRule π r) f n (Nat.le_of_succ_le h))
              (f (permRule π r ⟨n, h⟩
                (obsPrefix (permRule π r) f n (Nat.le_of_succ_le h)))) := rfl
      have hR : obsPrefix r (f ∘ (π : X → X)) (n + 1) h
          = Fin.snoc (obsPrefix r (f ∘ (π : X → X)) n (Nat.le_of_succ_le h))
              ((f ∘ (π : X → X)) (r ⟨n, h⟩
                (obsPrefix r (f ∘ (π : X → X)) n (Nat.le_of_succ_le h)))) := rfl
      rw [hL, hR, hn]
      rfl
  rw [observed, observed, hpre m le_rfl]

/--
**The point half of the trace theorem.** The relabelled rule queries the
relabelled points. Together with `observed_permRule` — the cost half — this is
Schumacher–Vose–Whitley's theorem on the full trace `⟨(x₀,y₀), …, (x_{n−1},y_{n−1})⟩`,
whose two components are the visited points and the costs read there.
-/
public theorem ruleVisit_permRule {m : ℕ} (π : Equiv.Perm X) (r : AdaptiveRule X Y m)
    (c : Fin m → Y) (k : Fin m) :
    ruleVisit (permRule π r) c k = π (ruleVisit r c k) := rfl

/-- A relabelled rule revisits exactly when the original does: `π` is injective. -/
public theorem injective_ruleVisit_permRule {m : ℕ} (π : Equiv.Perm X)
    (r : AdaptiveRule X Y m) (c : Fin m → Y) (h : Injective (ruleVisit r c)) :
    Injective (ruleVisit (permRule π r) c) := by
  intro a b hab
  exact h (π.injective hab)

/--
**Any two no-revisit rules agree on a trajectory, up to a permutation.**

The trajectory an adaptive rule unrolls from a *fixed* cost sequence `c` is a
schedule, so two rules give two schedules, and `exists_perm_comp` relates them.
The point is that the permutation depends only on `c` — not on the objective —
which is what makes it usable as a reindexing of the sum over objectives.
-/
public theorem exists_perm_ruleVisit [Fintype X] {m : ℕ}
    (r₁ r₂ : AdaptiveRule X Y m) {c : Fin m → Y}
    (h₁ : Injective (ruleVisit r₁ c)) (h₂ : Injective (ruleVisit r₂ c)) :
    ∃ π : Equiv.Perm X, ∀ k, π (ruleVisit r₂ c k) = ruleVisit r₁ c k :=
  exists_perm_comp ⟨ruleVisit r₂ c, h₂⟩ ⟨ruleVisit r₁ c, h₁⟩

/--
**A fibre of the observation map is cut out by `m` equations.** The objective `f`
observes `c` under `r` exactly when it takes the value `c k` at the `k`-th point
`r` unrolls from `c`.

The forward direction is `observed_consistent`, the backward
`observed_of_consistent`; both live in `AISafetyAtlas.Learning`. Stated together
because the fibre argument below needs the equivalence, not either half.
-/
public theorem observed_eq_iff {m : ℕ} (r : AdaptiveRule X Y m) (f : X → Y)
    (c : Fin m → Y) :
    observed r f = c ↔ ∀ k, f (ruleVisit r c k) = c k := by
  constructor
  · rintro rfl k
    exact observed_consistent r f k
  · intro hc
    exact observed_of_consistent r f c hc

/--
**The sufficient direction for adaptive algorithms.**

If the weighting is invariant under permutations of the search domain, then no
deterministic adaptive no-revisit rule beats any other, under any functional of
the observed cost sequence.

This is the algorithm class both printed sources quantify over, so with it the
sufficiency half is no longer narrower than print. The weight axis stays wider:
`P` is an arbitrary real weight, with neither nonnegativity nor normalization,
where the sources take a distribution.

The proof is a fibre-by-fibre reindexing. For a fixed cost sequence `c`, the two
rules unroll two schedules from `c`; a permutation `π` carrying one to the other
sends the fibre of `r₁` over `c` bijectively onto the fibre of `r₂` over `c`, and
permutation-invariance says it does not disturb the weights. Because `π` is built
from `c` alone, the same reindexing works for every objective in the fibre.
-/
public theorem nfl_adaptive_of_permInvariant [Fintype X] [Fintype Y] {m : ℕ}
    {P : ObjectiveWeight X Y} (hP : PermInvariant P)
    (r₁ r₂ : AdaptiveRule X Y m)
    (h₁ : ∀ c, Injective (ruleVisit r₁ c)) (h₂ : ∀ c, Injective (ruleVisit r₂ c))
    (Ψ : (Fin m → Y) → ℝ) :
    weightedTrace P Ψ r₁ = weightedTrace P Ψ r₂ := by
  classical
  show (∑ f : X → Y, P f * Ψ (observed r₁ f)) = ∑ f : X → Y, P f * Ψ (observed r₂ f)
  -- split each side over the fibres of the observation map
  have expand : ∀ r : AdaptiveRule X Y m,
      ∑ f : X → Y, P f * Ψ (observed r f)
        = ∑ c : Fin m → Y, ∑ f : X → Y,
            (if observed r f = c then P f * Ψ c else 0) := by
    intro r
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun f _ => ?_
    rw [Finset.sum_ite_eq Finset.univ (observed r f) fun c => P f * Ψ c]
    simp
  rw [expand r₁, expand r₂]
  refine Finset.sum_congr rfl fun c _ => ?_
  -- the permutation carrying `r₂`'s trajectory over `c` to `r₁`'s
  obtain ⟨π, hπ⟩ := exists_perm_ruleVisit r₁ r₂ (h₁ c) (h₂ c)
  -- reindex the sum over objectives by `f ↦ f ∘ π`
  let e : (X → Y) ≃ (X → Y) := Equiv.arrowCongr π.symm (Equiv.refl Y)
  refine Fintype.sum_equiv e _ _ fun f => ?_
  have hcomp : e f = f ∘ (π : X → X) := rfl
  -- the reindexing matches the two fibres over `c`
  have hmem : observed r₂ (e f) = c ↔ observed r₁ f = c := by
    rw [observed_eq_iff, observed_eq_iff, hcomp]
    constructor
    · intro hc k
      simpa [Function.comp_def, hπ k] using hc k
    · intro hc k
      simpa [Function.comp_def, hπ k] using hc k
  by_cases hf : observed r₁ f = c
  · rw [if_pos hf, if_pos (hmem.mpr hf), hcomp, hP π f]
  · rw [if_neg hf, if_neg fun h => hf (hmem.mp h)]

/-! ## Fixed schedules are adaptive rules

The adaptive class contains the non-adaptive one, so the necessary direction
transfers without being reproved: a probe built from schedules is already a probe
built from rules. -/

/-- A fixed schedule read as an adaptive rule — one that ignores the costs it has
seen. -/
@[expose] public def scheduleRule {m : ℕ} (σ : Fin m ↪ X) : AdaptiveRule X Y m :=
  fun k _ => σ k

/-- A schedule rule visits the schedule's points, whatever it observes. -/
public theorem ruleVisit_scheduleRule {m : ℕ} (σ : Fin m ↪ X) (c : Fin m → Y) (k : Fin m) :
    ruleVisit (Y := Y) (scheduleRule σ) c k = σ k := rfl

/-- A schedule rule never revisits, because a schedule is an embedding. -/
public theorem injective_ruleVisit_scheduleRule {m : ℕ} (σ : Fin m ↪ X) (c : Fin m → Y) :
    Injective (ruleVisit (Y := Y) (scheduleRule σ) c) := σ.injective

/-- What a schedule rule observes is the schedule's cost sequence. -/
public theorem observed_scheduleRule {m : ℕ} (σ : Fin m ↪ X) (f : X → Y) :
    observed (scheduleRule σ) f = fun k => f (σ k) :=
  observed_of_consistent _ f _ fun _ => rfl

/-- Weighted performance of a schedule, read through the adaptive machinery. -/
public theorem weightedPerformance_eq_adaptive [Fintype X] [Fintype Y] {m : ℕ}
    (P : ObjectiveWeight X Y) (Φ : CostPerformance m Y) (σ : Fin m ↪ X) :
    weightedPerformance P Φ σ = weightedTrace P Φ (scheduleRule σ) := by
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [observed_scheduleRule]

/--
**The uniform adaptive core, recovered from the weighted statement.** Taking the
constant weight gives `AISafetyAtlas.Learning.no_free_lunch_adaptive` back,
without its `m ≤ |X|` hypothesis: injectivity of the trajectories already forces
`m ≤ |X|`, so the hypothesis was redundant.
-/
public theorem no_free_lunch_adaptive_of_sharp [Fintype X] [Fintype Y] {m : ℕ}
    (r₁ r₂ : AdaptiveRule X Y m)
    (h₁ : ∀ c, Injective (ruleVisit r₁ c)) (h₂ : ∀ c, Injective (ruleVisit r₂ c))
    (Ψ : (Fin m → Y) → ℝ) :
    ∑ f : X → Y, Ψ (observed r₁ f) = ∑ f : X → Y, Ψ (observed r₂ f) := by
  have hP : PermInvariant (fun _ : X → Y => (1 : ℝ)) := fun _ _ => rfl
  simpa [weightedTrace] using nfl_adaptive_of_permInvariant hP r₁ r₂ h₁ h₂ Ψ

/-! ## Stochastic rules

Igel–Toussaint state Theorem 1 for *"any two (deterministic or stochastic,
cf. [1]) algorithms"*, citing Droste–Jansen–Wegener on randomized search
heuristics. `AdaptiveRule` is deterministic, so everything above quantifies over
a subclass of what the source does. This section removes that restriction.

**The modelling choice matters, and it is the point of the section.** A
stochastic rule is *not* modelled as an abstract weighted family of deterministic
rules. That would prove only that No Free Lunch is preserved under mixtures, and
would leave exactly the residual it is meant to close: nothing would say the
source's algorithms *are* such mixtures. Instead the randomness is where a
randomized heuristic actually puts it — the rule reads a **choice** at each step,
alongside the costs it has seen — and fixing the choice sequence yields a
deterministic rule **definitionally**, by `induced`. No representation theorem is
needed because there is nothing to represent.

An arbitrary weight on choice *sequences* is deliberate: it allows the steps'
choices to be correlated, so independent per-step randomization is a special
case, and so is the abstract mixture picture, by taking `C` to index rules.

**That residual is closed, at the primary source.** `C` is a `Fintype`, so this
covers finite choice sets only — and Droste–Jansen–Wegener's text makes that
print's own setting rather than an atlas restriction. At p. 134: *"The number of
different deterministic search strategies is finite. Let m be its number. A
randomized search strategy is a probability distribution p = (p₁, …, p_m) and
chooses the ith deterministic strategy with probability p_i."* `mixtureTrace`
below is that definition, and `surjective_induced_playChoice` records that the
choice-sequence form here reaches all of it.
-/

/--
A **stochastic** adaptive query rule: given the costs observed so far *and* a
choice drawn at this step, pick the next query point.

The deterministic `AdaptiveRule X Y m` is the case where `C` is a subsingleton.
-/
public abbrev StochasticRule (X Y C : Type*) (m : ℕ) : Type _ :=
  ∀ k : Fin m, (Fin k → Y) → C → X

/--
The deterministic rule obtained by fixing the whole choice sequence in advance.

This is a definition, not a theorem: a stochastic rule with its randomness
resolved *is* a deterministic rule, with no factorization argument in between.
-/
@[expose] public def induced {C : Type*} {m : ℕ}
    (r : StochasticRule X Y C m) (c : Fin m → C) : AdaptiveRule X Y m :=
  fun k hist => r k hist (c k)

/--
Aggregate performance of a stochastic rule: the weighted total, over choice
sequences, of the deterministic performance each sequence induces.

The weight is an arbitrary real, as everywhere in this file; a probability
distribution over the choices is the special case, and is what the sources take.
-/
@[expose] public noncomputable def stochasticTrace [Fintype X] [Fintype Y]
    {C : Type*} [Fintype C] {m : ℕ}
    (P : ObjectiveWeight X Y) (Ψ : (Fin m → Y) → ℝ)
    (w : (Fin m → C) → ℝ) (r : StochasticRule X Y C m) : ℝ :=
  ∑ c : Fin m → C, w c * weightedTrace P Ψ (induced r c)

/--
**No Free Lunch for stochastic rules.** Two stochastic non-repeating rules, over
possibly different choice alphabets, have the same aggregate performance against
a permutation-invariant weighting — provided their choice weights carry the same
total mass, which for two probability distributions is automatic.

This is the source's *"deterministic or stochastic"* quantifier. The proof is the
linearity argument the extension is usually waved through with: every induced
deterministic rule scores the same, by `nfl_adaptive_of_permInvariant`, so each
side collapses to that common score times its total mass.

`Nonempty C` is a hypothesis print does not state, and is what a randomized
algorithm having at least one realization amounts to.
-/
public theorem nfl_stochastic_of_permInvariant [Fintype X] [Fintype Y]
    {C₁ C₂ : Type*} [Fintype C₁] [Fintype C₂] [Nonempty C₁] [Nonempty C₂] {m : ℕ}
    {P : ObjectiveWeight X Y} (hP : PermInvariant P)
    {w₁ : (Fin m → C₁) → ℝ} {w₂ : (Fin m → C₂) → ℝ}
    (hw : ∑ c : Fin m → C₁, w₁ c = ∑ c : Fin m → C₂, w₂ c)
    (r₁ : StochasticRule X Y C₁ m) (r₂ : StochasticRule X Y C₂ m)
    (h₁ : ∀ c d, Injective (ruleVisit (induced r₁ c) d))
    (h₂ : ∀ c d, Injective (ruleVisit (induced r₂ c) d))
    (Ψ : (Fin m → Y) → ℝ) :
    stochasticTrace P Ψ w₁ r₁ = stochasticTrace P Ψ w₂ r₂ := by
  classical
  obtain ⟨c₀⟩ : Nonempty (Fin m → C₂) := inferInstance
  set V := weightedTrace P Ψ (induced r₂ c₀)
  have hconst₁ : ∀ c, weightedTrace P Ψ (induced r₁ c) = V := fun c =>
    nfl_adaptive_of_permInvariant hP _ _ (h₁ c) (h₂ c₀) Ψ
  have hconst₂ : ∀ c, weightedTrace P Ψ (induced r₂ c) = V := fun c =>
    nfl_adaptive_of_permInvariant hP _ _ (h₂ c) (h₂ c₀) Ψ
  simp only [stochasticTrace, hconst₁, hconst₂, ← Finset.sum_mul, hw]

/--
The uniform case, matching Igel–Toussaint's Theorem 1 as printed: two stochastic
non-repeating algorithms, each averaging over its own choices with total mass
one, agree on the sum over all objectives.
-/
public theorem no_free_lunch_stochastic_of_sharp [Fintype X] [Fintype Y]
    {C₁ C₂ : Type*} [Fintype C₁] [Fintype C₂] [Nonempty C₁] [Nonempty C₂] {m : ℕ}
    {w₁ : (Fin m → C₁) → ℝ} {w₂ : (Fin m → C₂) → ℝ}
    (hw₁ : ∑ c : Fin m → C₁, w₁ c = 1) (hw₂ : ∑ c : Fin m → C₂, w₂ c = 1)
    (r₁ : StochasticRule X Y C₁ m) (r₂ : StochasticRule X Y C₂ m)
    (h₁ : ∀ c d, Injective (ruleVisit (induced r₁ c) d))
    (h₂ : ∀ c d, Injective (ruleVisit (induced r₂ c) d))
    (Ψ : (Fin m → Y) → ℝ) :
    ∑ c : Fin m → C₁, w₁ c * ∑ f : X → Y, Ψ (observed (induced r₁ c) f)
      = ∑ c : Fin m → C₂, w₂ c * ∑ f : X → Y, Ψ (observed (induced r₂ c) f) := by
  have hP : PermInvariant (fun _ : X → Y => (1 : ℝ)) := fun _ _ => rfl
  have := nfl_stochastic_of_permInvariant (P := fun _ : X → Y => (1 : ℝ)) hP
    (w₁ := w₁) (w₂ := w₂) (hw₁.trans hw₂.symm) r₁ r₂ h₁ h₂ Ψ
  simpa [stochasticTrace, weightedTrace] using this

/-! ### The source's own definition: a distribution over deterministic behaviours

Igel's survey of these theorems states, citing Droste–Jansen–Wegener, that *"a
randomized search algorithm `a` can be described by a probability distribution
`p_a` over deterministic search behaviors"*, and writes the performance as

`E{c(Y(f,m,a))} = ∑_{a' ∈ A} p_a(a') · c(Y(f,m,a'))`,

where *"the set `A` contain[s] all deterministic search behaviors"*. So the
mixture picture is not a proxy for the source's randomized algorithms — it **is**
the source's definition of them, and `mixtureTrace` is that equation.

The same passage names the other view: *"drawing all realizations of random
variables required by a randomized search method **at once prior to the search
process** and to use these events as inputs to a deterministic algorithm"*, which
is `stochasticTrace`. So the section above and this one are the source's own two
descriptions of the same object, and `surjective_induced_playChoice` records that
the choice-sequence form reaches every behaviour the mixture form ranges over.

Both are finite objects here: `A` is a `Fintype` because `X` and `Y` are, so
nothing in this section restricts the randomness available. -/

/--
**Igel's equation (8).** The performance of a randomized algorithm as the
expectation, over all deterministic search behaviours, of their performance
weighted by the algorithm's own distribution.

The weight is an arbitrary real, as everywhere in this file; a probability
distribution over `A` is the case the source states.
-/
@[expose] public noncomputable def mixtureTrace [Fintype X] [Fintype Y]
    [DecidableEq Y] {m : ℕ}
    (P : ObjectiveWeight X Y) (Ψ : (Fin m → Y) → ℝ)
    (p : AdaptiveRule X Y m → ℝ) : ℝ :=
  ∑ a : AdaptiveRule X Y m, p a * weightedTrace P Ψ a

/--
**The deterministic algorithms are the degenerate distributions.** Igel's words:
*"we view the deterministic algorithms as a subset of the randomized algorithms
having degenerated probability distributions"*. At a point mass on `a`,
equation (8) is just `a`'s own performance.
-/
public theorem mixtureTrace_pointMass [Fintype X] [Fintype Y] [DecidableEq Y]
    {m : ℕ} (P : ObjectiveWeight X Y) (Ψ : (Fin m → Y) → ℝ)
    (a : AdaptiveRule X Y m) :
    mixtureTrace P Ψ (fun a' => if a' = a then (1 : ℝ) else 0)
      = weightedTrace P Ψ a := by
  simp [mixtureTrace]

/--
A mixture collapses: against a permutation-invariant weighting, every behaviour
in the support scores the same, so the whole expectation is that common score
times the distribution's total mass.

`a₀` is any non-repeating reference behaviour; the statement is independent of
which one, which is the content.
-/
public theorem mixtureTrace_eq_sum_mul [Fintype X] [Fintype Y] [DecidableEq Y]
    {m : ℕ} {P : ObjectiveWeight X Y} (hP : PermInvariant P)
    (p : AdaptiveRule X Y m → ℝ)
    (hp : ∀ a, p a ≠ 0 → ∀ c, Injective (ruleVisit a c))
    {a₀ : AdaptiveRule X Y m} (ha₀ : ∀ c, Injective (ruleVisit a₀ c))
    (Ψ : (Fin m → Y) → ℝ) :
    mixtureTrace P Ψ p = (∑ a : AdaptiveRule X Y m, p a) * weightedTrace P Ψ a₀ := by
  classical
  rw [mixtureTrace, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases ha : p a = 0
  · simp [ha]
  · rw [nfl_adaptive_of_permInvariant hP a a₀ (hp a ha) ha₀ Ψ]

/--
**No Free Lunch at the source's own definition of a randomized algorithm.** Two
distributions over deterministic non-repeating behaviours, with the same total
mass — for two probability distributions, automatic — give the same expected
performance against a permutation-invariant weighting.

This is Igel–Toussaint's *"deterministic or stochastic"* quantifier, with the
second word unfolded the way the source unfolds it.
-/
public theorem nfl_mixture_of_permInvariant [Fintype X] [Fintype Y] [DecidableEq Y]
    {m : ℕ} {P : ObjectiveWeight X Y} (hP : PermInvariant P)
    (p q : AdaptiveRule X Y m → ℝ)
    (hpq : ∑ a : AdaptiveRule X Y m, p a = ∑ a : AdaptiveRule X Y m, q a)
    (hp : ∀ a, p a ≠ 0 → ∀ c, Injective (ruleVisit a c))
    (hq : ∀ a, q a ≠ 0 → ∀ c, Injective (ruleVisit a c))
    (Ψ : (Fin m → Y) → ℝ) :
    mixtureTrace P Ψ p = mixtureTrace P Ψ q := by
  classical
  by_cases h : ∃ a, p a ≠ 0 ∨ q a ≠ 0
  · obtain ⟨a₀, ha₀⟩ := h
    have hnr : ∀ c, Injective (ruleVisit a₀ c) := ha₀.elim (hp a₀) (hq a₀)
    rw [mixtureTrace_eq_sum_mul hP p hp hnr Ψ,
      mixtureTrace_eq_sum_mul hP q hq hnr Ψ, hpq]
  · push Not at h
    have hp0 : ∀ a, p a = 0 := fun a => (h a).1
    have hq0 : ∀ a, q a = 0 := fun a => (h a).2
    simp [mixtureTrace, hp0, hq0]

/--
The stochastic rule that simply plays the behaviour it is handed: with the choice
alphabet taken to be the deterministic behaviours themselves, drawing a choice
*is* drawing an algorithm.
-/
@[expose] public def playChoice {m : ℕ} :
    StochasticRule X Y (AdaptiveRule X Y m) m :=
  fun k hist a => a k hist

/-- Handing `playChoice` the constant sequence at `a` recovers `a`. -/
public theorem induced_playChoice {m : ℕ} (a : AdaptiveRule X Y m) :
    induced (playChoice (X := X) (Y := Y) (m := m)) (fun _ => a) = a := rfl

/--
**The choice alphabet loses nothing.** Every deterministic behaviour whatsoever
is a realization of `playChoice`, so quantifying over choice sequences into a
finite alphabet reaches the source's whole set `A` of search behaviours.

This is what makes `Fintype` on the choice alphabet costless rather than a
restriction: the source's own `A` is finite here too, because `X` and `Y` are.
It is also the sentence *"an alternative way to see this is to think of drawing
all realizations … at once prior to the search process"* — the drawn choice is
the behaviour.
-/
public theorem surjective_induced_playChoice {m : ℕ} :
    Function.Surjective
      (fun c : Fin m → AdaptiveRule X Y m => induced playChoice c) :=
  fun a => ⟨fun _ => a, rfl⟩

/-! ### Schumacher–Vose–Whitley's equivalent formulations

Their NFL1–NFL4 are four readings of the same fact. NFL1 (equal performance under
any overall measure) is `no_free_lunch_adaptive_of_sharp`; NFL4 is the weighted
form the source declines and `nfl_adaptive_iff_permInvariant` supplies. The other
two are one lemma each, and are here so the group is not left uncovered. -/

/--
**NFL2.** For any two no-revisit rules and any objective, there is an objective on
which the second rule reads exactly what the first read on the original.

The witness is explicit: relabel by the permutation carrying one trajectory to the
other. No averaging and no invariance hypothesis is involved — this is a statement
about single objectives.
-/
public theorem exists_observed_eq [Fintype X] {m : ℕ}
    (r₁ r₂ : AdaptiveRule X Y m)
    (h₁ : ∀ c, Injective (ruleVisit r₁ c)) (h₂ : ∀ c, Injective (ruleVisit r₂ c))
    (f : X → Y) :
    ∃ g : X → Y, observed r₂ g = observed r₁ f := by
  classical
  set c := observed r₁ f with hc
  obtain ⟨π, hπ⟩ := exists_perm_ruleVisit r₁ r₂ (h₁ c) (h₂ c)
  refine ⟨f ∘ (π : X → X), ?_⟩
  rw [observed_eq_iff]
  intro k
  have hf : f (ruleVisit r₁ c k) = c k := (observed_eq_iff r₁ f c).mp hc.symm k
  simpa [Function.comp_def, hπ k] using hf

/--
**NFL3.** Every no-revisit rule produces the same *collection* of cost sequences
as every other, when all objectives are considered — with multiplicity.

The multiset form is the sharp one: equal counts per sequence, not merely equal
supports. `exists_observed_eq` gives the support statement; this gives the
histogram, which is what an "overall measure" of NFL1 is computed from.
-/
public theorem card_observed_eq [Fintype X] [Fintype Y] {m : ℕ}
    (r₁ r₂ : AdaptiveRule X Y m)
    (h₁ : ∀ c, Injective (ruleVisit r₁ c)) (h₂ : ∀ c, Injective (ruleVisit r₂ c))
    (c : Fin m → Y) :
    (Finset.univ.filter fun f : X → Y => observed r₁ f = c).card
      = (Finset.univ.filter fun f : X → Y => observed r₂ f = c).card := by
  classical
  have hkey := no_free_lunch_adaptive_of_sharp r₁ r₂ h₁ h₂
    (fun d => if d = c then (1 : ℝ) else 0)
  have hcast : ∀ r : AdaptiveRule X Y m,
      (∑ f : X → Y, if observed r f = c then (1 : ℝ) else 0)
        = ((Finset.univ.filter fun f : X → Y => observed r f = c).card : ℝ) := by
    intro r
    rw [Finset.sum_boole]
  rw [hcast r₁, hcast r₂] at hkey
  exact_mod_cast hkey

/-! ## Permutation invariance is necessary -/

/--
Under a full-length bijective schedule, an indicator performance measure reads
off a single weight. This is the probe that forces invariance.
-/
public theorem weightedPerformance_indicator [Fintype X] [Fintype Y]
    (P : ObjectiveWeight X Y) (e : Fin (card X) ≃ X) (c : Fin (card X) → Y) :
    weightedPerformance P (fun d => if d = c then (1 : ℝ) else 0) e.toEmbedding
      = P (fun x => c (e.symm x)) := by
  classical
  show (∑ f : X → Y, P f * (if (fun i => f (e i)) = c then (1 : ℝ) else 0))
      = P (fun x => c (e.symm x))
  rw [Finset.sum_eq_single_of_mem (fun x => c (e.symm x)) (Finset.mem_univ _)]
  · simp
  · intro g _ hne
    have hgc : (fun i => g (e i)) ≠ c := by
      intro hcontra
      refine hne (funext fun x => ?_)
      have := congrFun hcontra (e.symm x)
      simpa using this
    simp [hgc]

/--
Under a weight concentrated on one objective, aggregate performance is just that
objective's performance. This is the probe that shows the characterization has
content: a point mass is not permutation-invariant unless the objective is
constant, and then schedules genuinely differ.
-/
public theorem weightedPerformance_pointMass [Fintype X] [Fintype Y]
    [DecidableEq (X → Y)] {m : ℕ}
    (f₀ : X → Y) (Φ : CostPerformance m Y) (σ : Fin m ↪ X) :
    weightedPerformance (fun f => if f = f₀ then (1 : ℝ) else 0) Φ σ
      = Φ (fun i => f₀ (σ i)) := by
  classical
  show (∑ f : X → Y, (if f = f₀ then (1 : ℝ) else 0) * Φ (fun i => f (σ i)))
      = Φ (fun i => f₀ (σ i))
  rw [Finset.sum_eq_single_of_mem f₀ (Finset.mem_univ _)]
  · simp
  · intro g _ hne
    simp [hne]

/--
**The necessary direction, from a single sample length and indicator measures
only.** If no schedule of length `|X|` beats any other at the *indicator* of a
cost sequence, then the weighting is permutation-invariant.

Three ways this hypothesis is weaker than the sources'. They assume NFL across
the whole algorithm class; only full-length schedules appear here. They assume it
at every sample length; one length is used. And Igel–Toussaint's `δ(k, c(Y))`
form is recovered exactly by the indicator measures, so no linearity bridge from
indicators to arbitrary functionals is needed — a weaker hypothesis gives the
same conclusion.
-/
public theorem permInvariant_of_nfl [Fintype X] [Fintype Y]
    {P : ObjectiveWeight X Y}
    (h : ∀ (c : Fin (card X) → Y) (σ τ : Fin (card X) ↪ X),
      weightedPerformance P (fun d => if d = c then (1 : ℝ) else 0) σ
        = weightedPerformance P (fun d => if d = c then (1 : ℝ) else 0) τ) :
    PermInvariant P := by
  classical
  intro π f
  let e₀ : Fin (card X) ≃ X := (equivFin X).symm
  let e₁ : Fin (card X) ≃ X := e₀.trans π.symm
  let c : Fin (card X) → Y := fun i => f (e₀ i)
  have h₀ := weightedPerformance_indicator P e₀ c
  have h₁ := weightedPerformance_indicator P e₁ c
  have hmain := h c e₁.toEmbedding e₀.toEmbedding
  rw [h₀, h₁] at hmain
  have hlhs : (fun x => c (e₁.symm x)) = f ∘ π := by
    funext x
    show f (e₀ (e₁.symm x)) = f (π x)
    congr 1
    show e₀ (e₁.symm x) = π x
    have : e₁.symm x = e₀.symm (π x) := by simp [e₁]
    rw [this, Equiv.apply_symm_apply]
  have hrhs : (fun x => c (e₀.symm x)) = f := by
    funext x
    show f (e₀ (e₀.symm x)) = f x
    rw [Equiv.apply_symm_apply]
  rw [hlhs, hrhs] at hmain
  exact hmain

/--
**The sharp No Free Lunch theorem** (Igel–Toussaint 2004, Schumacher–Vose–Whitley
2001). A weighting of the objectives makes every schedule equally good exactly
when it is invariant under permutations of the search domain.

Both halves are stated more sharply on their own: `nfl_of_permInvariant` gives
the conclusion at every length, and `permInvariant_of_nfl` needs the hypothesis
at only one.
-/
public theorem nfl_iff_permInvariant [Fintype X] [Fintype Y]
    (P : ObjectiveWeight X Y) :
    (∀ (m : ℕ) (Φ : CostPerformance m Y) (σ τ : Fin m ↪ X),
        weightedPerformance P Φ σ = weightedPerformance P Φ τ)
      ↔ PermInvariant P := by
  constructor
  · intro h
    exact permInvariant_of_nfl fun c => h (card X) _
  · intro hP m Φ σ τ
    exact nfl_of_permInvariant hP Φ σ τ

/--
**The sharp No Free Lunch theorem over the printed algorithm class.**

Igel–Toussaint's Theorem 5 and Schumacher–Vose–Whitley's characterization,
quantified over the algorithms they quantify over: deterministic adaptive
non-repeating rules. A weighting makes every such rule equally good exactly when
it is invariant under permutations of the search domain.

Two axes stay wider than print. The weight is an arbitrary real function, not a
distribution; and the necessary direction needs the hypothesis only for the
*schedule* rules of a single length `|X|`, which is a strictly smaller family
than the sources assume it for.
-/
public theorem nfl_adaptive_iff_permInvariant [Fintype X] [Fintype Y]
    (P : ObjectiveWeight X Y) :
    (∀ (m : ℕ) (Ψ : (Fin m → Y) → ℝ) (r₁ r₂ : AdaptiveRule X Y m),
        (∀ c, Injective (ruleVisit r₁ c)) → (∀ c, Injective (ruleVisit r₂ c)) →
        weightedTrace P Ψ r₁ = weightedTrace P Ψ r₂)
      ↔ PermInvariant P := by
  constructor
  · intro h
    refine permInvariant_of_nfl fun c σ τ => ?_
    rw [weightedPerformance_eq_adaptive, weightedPerformance_eq_adaptive]
    exact h _ _ _ _ (injective_ruleVisit_scheduleRule σ) (injective_ruleVisit_scheduleRule τ)
  · intro hP m Ψ r₁ r₂ h₁ h₂
    exact nfl_adaptive_of_permInvariant hP r₁ r₂ h₁ h₂ Ψ

/-! ## The printed special cases

Both earlier formulations are instances of the weighted statement, recovered by
choosing the weight. Neither is reproved. -/

/-- A permutation-closed set is exactly the union of the orbits it meets. -/
public theorem eq_iUnion_permOrbit {F : Set (X → Y)} (hF : ClosedUnderPermutation F) :
    F = ⋃ f ∈ F, permOrbit f := by
  apply Set.eq_of_subset_of_subset
  · intro f hf
    exact Set.mem_biUnion hf (mem_permOrbit_self f)
  · intro g hg
    obtain ⟨f, hf, hgf⟩ := Set.mem_iUnion₂.mp hg
    exact closedUnderPermutation_iff_permOrbit_subset.mp hF f hf hgf

/-- The indicator of a permutation-closed set is a permutation-invariant weight. -/
public theorem permInvariant_of_closedUnderPermutation {F : Set (X → Y)}
    [DecidablePred (· ∈ F)] (hF : ClosedUnderPermutation F) :
    PermInvariant (fun f => if f ∈ F then (1 : ℝ) else 0) := by
  classical
  intro π f
  have hiff : f ∘ π ∈ F ↔ f ∈ F := by
    constructor
    · intro hmem
      have := hF π⁻¹ _ hmem
      simpa [Function.comp_assoc] using this
    · exact hF π f
  simp [hiff]

/--
**Schumacher–Vose–Whitley's set form, over their algorithm class.** A set of
objectives closed under permutation of the domain admits no algorithm that beats
another on it — for deterministic adaptive non-repeating rules, which is the
class the paper states it for.
-/
public theorem nfl_adaptive_of_closedUnderPermutation [Fintype X] [Fintype Y] {m : ℕ}
    {F : Set (X → Y)} [DecidablePred (· ∈ F)] (hF : ClosedUnderPermutation F)
    (r₁ r₂ : AdaptiveRule X Y m)
    (h₁ : ∀ c, Injective (ruleVisit r₁ c)) (h₂ : ∀ c, Injective (ruleVisit r₂ c))
    (Ψ : (Fin m → Y) → ℝ) :
    ∑ f ∈ Finset.univ.filter (· ∈ F), Ψ (observed r₁ f)
      = ∑ f ∈ Finset.univ.filter (· ∈ F), Ψ (observed r₂ f) := by
  classical
  have hP := permInvariant_of_closedUnderPermutation hF
  have hkey := nfl_adaptive_of_permInvariant hP r₁ r₂ h₁ h₂ Ψ
  simpa [weightedTrace, Finset.sum_filter, ite_mul, zero_mul, one_mul] using hkey

/--
**A permutation-invariant indicator comes from a permutation-closed set** — the
converse of `permInvariant_of_closedUnderPermutation`, and the step that turns
`permInvariant_of_nfl` into Schumacher–Vose–Whitley's Lemma 2, whose conclusion
is about a *set* rather than a weight.
-/
public theorem closedUnderPermutation_of_permInvariant {F : Set (X → Y)}
    [DecidablePred (· ∈ F)]
    (hP : PermInvariant (fun f => if f ∈ F then (1 : ℝ) else 0)) :
    ClosedUnderPermutation F := by
  intro π f hf
  have h : (if f ∘ (π : X → X) ∈ F then (1 : ℝ) else 0) = if f ∈ F then 1 else 0 := hP π f
  by_contra hmem
  rw [if_neg hmem, if_pos hf] at h
  exact one_ne_zero h.symm

/--
**Schumacher–Vose–Whitley's Lemma 2 verbatim.** If no schedule of length `|X|`
beats any other over `F`, then `F` is closed under permutation. The hypothesis is
weaker than the source's — schedules at one length, rather than the whole
algorithm class — so the statement is stronger.
-/
public theorem closedUnderPermutation_of_nfl [Fintype X] [Fintype Y] {F : Set (X → Y)}
    [DecidablePred (· ∈ F)]
    (h : ∀ (c : Fin (card X) → Y) (σ τ : Fin (card X) ↪ X),
      weightedPerformance (fun f => if f ∈ F then (1 : ℝ) else 0)
          (fun d => if d = c then (1 : ℝ) else 0) σ
        = weightedPerformance (fun f => if f ∈ F then (1 : ℝ) else 0)
          (fun d => if d = c then (1 : ℝ) else 0) τ) :
    ClosedUnderPermutation F :=
  closedUnderPermutation_of_permInvariant (permInvariant_of_nfl h)

/--
**The uniform core is the constant-weight case.** `no_free_lunch_embedding` in
`AISafetyAtlas.Learning` follows from the sharp theorem, because the constant
weight is permutation-invariant for trivial reasons. Recorded to show the
subsumption; the original proof is independent and stays.
-/
public theorem no_free_lunch_embedding_of_sharp [Fintype X] [Fintype Y] {m : ℕ}
    (Φ : CostPerformance m Y) (σ τ : Fin m ↪ X) :
    ∑ f : X → Y, Φ (fun i => f (σ i)) = ∑ f : X → Y, Φ (fun i => f (τ i)) := by
  have hP : PermInvariant (fun _ : X → Y => (1 : ℝ)) := fun _ _ => rfl
  have := nfl_of_permInvariant hP Φ σ τ
  simpa [weightedPerformance] using this

/-! ## How many objective sets satisfy the condition

The `iff` above says NFL holds exactly on the permutation-closed sets. Igel and
Toussaint's Theorem 3 asks how many of those there are, and answers that almost
none of them are: the count is `2 ^ C(|X| + |Y| − 1, |X|) − 1`, against
`2 ^ (|Y| ^ |X|) − 1` subsets in all.

The argument is short once Lemma 1 is in hand. A permutation-closed set is a
union of orbits, an orbit is a basis class, and a basis class is fixed by the
multiset of cost values an objective takes — so the orbits are exactly the
multisets of size `|X|` drawn from `Y`, of which there are `C(|X| + |Y| − 1,
|X|)`, and a permutation-closed set is any set of them.

`spectrum` is that multiset, as an element of Mathlib's `Sym`, which is what
turns the counting into `Sym.card_sym_eq_choose`.
-/

/-! ## Neighbourhood structure breaks the symmetry

Theorem 3 says permutation-closed priors are rare by count. Theorem 4 is the
first step of print's argument that the structures search actually uses are
never among them — **only the first step**, and the rest is not formalized here;
see the non-claim at the end of this section.

Igel–Toussaint's *neighbourhood relation* on the search space is a **symmetric**
`n : X × X → {0,1}`, non-trivial when some pair of distinct points neighbours
and some pair does not, and their theorem is that no such relation survives
every relabelling of the space.

Nothing about that is specific to search — or, as it turns out, to symmetry.
The content is a fact about the action of `Equiv.Perm X` on binary relations:
**a relation invariant under every permutation of `X` is constant off the
diagonal, and constant on it.** No such relation distinguishes any point from
any other, so "invariant under every relabelling" is not a condition a relation
can meet while carrying structure.

**Explicit non-claim: the bridge to No Free Lunch is not proved here.** It is
tempting to write that a space with a non-trivial neighbourhood structure
therefore has no permutation-closed prior, so that
`nfl_adaptive_iff_permInvariant` never applies to it. That does not follow, and
unqualified it is **false**: `PermInvariant` is a predicate on
`ObjectiveWeight X Y`, a neighbourhood relation is a relation on `X`, and the
uniform weight is permutation-invariant no matter what structure `X` carries.

Getting from Theorem 4 to *"`F` is not closed under permutation"* takes a
further argument about a family whose membership condition reads the relation,
and print supplies it separately in its Examples 2 and 3 — steepness, and a
bound on the number of local minima. Example 2's argument is not a corollary of
Theorem 4: it turns on *"for every f ∈ F there exists a permutation that maps a
global minimum and a global maximum of f to neighboring points"*, which is a
claim about where permutations can send extrema. **Neither example is
formalized**, and both are graded `No` in the coverage audit.
-/

end AISafetyAtlas.Learning
