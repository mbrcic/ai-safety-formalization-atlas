module

public import AISafetyAtlas.Sovereignty.Evidence
public import Mathlib.Probability.Distributions.Uniform

/-!
# The counting bound is met, and no evidence is no better than chance

`uniform_success` is print's symmetric construction for `C7`: `k` contexts,
one correct action each, and a controller that spreads its mass evenly. Every
context succeeds with probability exactly `1 / k`, so the bound of
`exists_measure_le_inv_of_disjoint` is attained and cannot be improved.

`blind_success` is the degenerate case of `C8`: two contexts whose observation
laws agree give an event gap of zero, so the two success probabilities sum to
at most one -- whatever is gained in one context is lost in the other.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Evidence

open AISafetyAtlas.Sovereignty
open MeasureTheory
open scoped ENNReal

/-! ## `C7`: the bound is attained -/

/-- The controller that spreads its mass evenly over `k` actions. -/
@[expose] public noncomputable def uniform (k : ℕ) [NeZero k] : Measure (Fin k) :=
  (PMF.uniformOfFintype (Fin k)).toMeasure

/-- It is a probability measure. -/
public instance uniform_isProbability (k : ℕ) [NeZero k] :
    IsProbabilityMeasure (uniform k) := by
  unfold uniform
  infer_instance

/-- **Every context succeeds with probability exactly `1 / k`.** The one action
that is correct in context `i` has exactly the mass the counting bound allows,
so `C7` cannot be improved. -/
public theorem uniform_success (k : ℕ) [NeZero k] (i : Fin k) :
    uniform k {i} = 1 / k := by
  rw [uniform, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i),
    PMF.uniformOfFintype_apply, Fintype.card_fin, one_div]

/-- The correct actions are pairwise disjoint, one per context. -/
public theorem uniform_disjoint (k : ℕ) :
    Pairwise (Function.onFun Disjoint (fun i : Fin k => ({i} : Set (Fin k)))) := by
  intro i j hij
  exact Set.disjoint_singleton.mpr hij

/-! ### `C7` at print's own quantifiers

`uniform_success` computes one measure. `exists_success_le_inv` is the printed
statement, with the contexts, the observation laws and the controller still
present as binders, and nothing had run it -- so the binders had never been
filled and an unsatisfiable combination of them would have looked the same.

The filling is the blind controller: every context yields the same observation
(there is only one to yield), so `actionLaw_congr`'s hypothesis holds for a
reason rather than by fiat, and the correct actions are one per context.

The bound is then **attained**, by `uniform_success`: the context the theorem
produces has success probability exactly `1 / k`, so `C7` is the best bound of
its shape and not a slack one.
-/

/-- The blind observation: every context looks the same, which is print's
*"its action distribution is the same in all contexts"*. -/
@[expose] public noncomputable def blindObs (k : ℕ) : Fin k → Measure Unit :=
  fun _ => Measure.dirac ()

/-- The controller ignores the observation and spreads its mass. -/
@[expose] public noncomputable def spreadAct (k : ℕ) [NeZero k] :
    Unit → Measure (Fin k) :=
  fun _ => uniform k

/-- Under a blind observation the action law is the controller itself. -/
public theorem actionLaw_blind (k : ℕ) [NeZero k] (i : Fin k) :
    actionLaw (blindObs k i) (spreadAct k) = uniform k := by
  unfold actionLaw blindObs spreadAct
  simp

public instance actionLaw_blind_isProbability (k : ℕ) [NeZero k] (i : Fin k) :
    IsProbabilityMeasure (actionLaw (blindObs k i) (spreadAct k)) := by
  rw [actionLaw_blind k i]
  infer_instance

/-- **`C7` at the witness**: some context succeeds with probability at most
`1 / k`. -/
public theorem blind_exists_success_le_inv (k : ℕ) [NeZero k] :
    ∃ i : Fin k, actionLaw (blindObs k i) (spreadAct k) ({i} : Set (Fin k)) ≤ 1 / k :=
  exists_success_le_inv (NeZero.ne k) (blindObs k) (fun _ _ => rfl) (spreadAct k)
    (fun i => ({i} : Set (Fin k))) (fun i => measurableSet_singleton i)
    (uniform_disjoint k)

/-- **And the bound is attained**, so it cannot be improved: *every* context
succeeds with probability exactly `1 / k`, not merely at most. -/
public theorem blind_success_eq_inv (k : ℕ) [NeZero k] (i : Fin k) :
    actionLaw (blindObs k i) (spreadAct k) ({i} : Set (Fin k)) = 1 / k := by
  rw [actionLaw_blind k i]
  exact uniform_success k i

/-! ## `C8`: with no evidence, the two successes trade off exactly -/

/-- **Identical observation laws leave nothing to decide on.** The gap is zero,
so the probability of deciding `0` correctly and the probability of deciding
`1` correctly sum to at most one, whatever region the rule uses. -/
public theorem blind_success {O : Type*} [MeasurableSpace O] (P : Measure O)
    [IsProbabilityMeasure P] {A : Set O} (hA : MeasurableSet A) :
    P Aᶜ + P A ≤ 1 := by
  have hgap : eventGap P P = 0 := (eventGap_eq_zero_iff P P).mpr fun _ _ => rfl
  have := success_add_le_one_add_eventGap P P hA
  rwa [hgap, add_zero] at this

/-! ## `C8` averaged: a blind rule cannot beat a coin -/

/-- **The averaged form of `blind_success`.** The same law in both contexts
gives a zero gap, so the average of the two success probabilities is at most a
half -- the scale print states `C8` on. -/
public theorem blind_avgSuccess_le_half {O : Type*} [MeasurableSpace O]
    (P : Measure O) [IsProbabilityMeasure P] {A : Set O} (hA : MeasurableSet A) :
    (P Aᶜ + P A) / 2 ≤ 1 / 2 := by
  have hgap : eventGap P P = 0 := (eventGap_eq_zero_iff P P).mpr fun _ _ => rfl
  have h := avgSuccess_le_one_add_eventGap P P hA
  rwa [hgap, add_zero] at h

/-- **And no guarantee exceeds a half on identical evidence.** Whatever `c` the
rule guarantees in both contexts satisfies `2 * c ≤ 1`. This is
`eventGap_ge_of_success` at a zero gap, and read the other way it is print's
point: a guarantee above a half *forces* the two laws apart, so it is evidence
about the experiment and not about the rule. -/
public theorem blind_no_guarantee_above_half {O : Type*} [MeasurableSpace O]
    (P : Measure O) [IsProbabilityMeasure P] {A : Set O} (hA : MeasurableSet A)
    {c : ℝ≥0∞} (h₀ : c ≤ P Aᶜ) (h₁ : c ≤ P A) :
    2 * c ≤ 1 := by
  have hgap : eventGap P P = 0 := (eventGap_eq_zero_iff P P).mpr fun _ _ => rfl
  have h := eventGap_ge_of_success P P hA h₀ h₁
  rwa [hgap, add_zero] at h

end AISafetyAtlas.Examples.Sovereignty.Evidence
