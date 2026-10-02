module

public import AISafetyAtlas.Sovereignty.Influence
public import Mathlib.MeasureTheory.Measure.GiryMonad

/-!
# How much a decision can succeed on the evidence it has

Two bounds from the proposal's §7, both of the same shape: a decision that
cannot see the context cannot beat what the observations distinguish, and
randomizing does not help.

`C7` is the counting bound. If `k` contexts induce the same observation law
then the controller's action law is one measure -- `actionLaw_congr` is that
step, and it is the whole force of print's "its action distribution is the same
in all contexts". The success sets are pairwise disjoint, so their probabilities
sum to at most one and one of them is at most `1 / k`:
`exists_measure_le_inv_of_disjoint` is that counting content and
`exists_success_le_inv` is the statement at print's own quantifiers, with the
contexts, the observation laws and the controller still present as binders.

`C8` is the binary bound. A decision rule is its decision-one region `A`, and
its equal-prior average success is `(P₀ Aᶜ + P₁ A) / 2`. Print maximizes over
`A` by hand; here `eventGap` already is that maximum, so
`avgSuccess_le_one_add_eventGap` is the bound at every region at once.
`eventGap_ge_of_success` is print's contrapositive: worst-case success near
one forces the laws apart.

## Scope

Print says "any randomized controller" and "any decision rule". A controller
here is an action law and a decision rule is a measurable region, which is what
those quantifiers range over once the observation is integrated out; the
integration itself is `Measure.bind` and is not otherwise used. Abstention is
print's caveat and is outside both statements: a rule that may decline is not a
region, and print says as much.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

open MeasureTheory
open scoped ENNReal

/-! ## `C7`: randomizing does not beat the counting bound -/

section C7

variable {O A : Type*} [MeasurableSpace O] [MeasurableSpace A]

/--
**The action law of a randomized controller.** The observation is drawn and the
controller answers it with a distribution over actions.
-/
@[expose] public noncomputable def actionLaw (obs : Measure O) (act : O → Measure A) :
    Measure A :=
  obs.bind act

/--
**Identical observation laws give identical action laws.**

This is print's "its action distribution is the same in all contexts", and it
is the only place the identical-observation hypothesis of `C7` is used.
-/
public theorem actionLaw_congr {obs obs' : Measure O} (h : obs = obs')
    (act : O → Measure A) : actionLaw obs act = actionLaw obs' act := by
  rw [h]

/--
**`C7`: one of `k` disjoint success sets has probability at most `1 / k`.**

The bound does not depend on the controller being deterministic, and it is
attained by the symmetric construction print describes, where the `k` sets
partition the actions into singletons of equal mass.
-/
public theorem exists_measure_le_inv_of_disjoint {k : ℕ} (hk : k ≠ 0)
    (π : Measure A) [IsProbabilityMeasure π] (G : Fin k → Set A)
    (hm : ∀ i, MeasurableSet (G i)) (hd : Pairwise (Function.onFun Disjoint G)) :
    ∃ i, π (G i) ≤ 1 / k := by
  have : Nonempty (Fin k) := ⟨⟨0, Nat.pos_of_ne_zero hk⟩⟩
  have hne : (Finset.univ : Finset (Fin k)).Nonempty := Finset.univ_nonempty
  obtain ⟨i₀, -, hmin⟩ := Finset.exists_min_image Finset.univ (fun i => π (G i)) hne
  refine ⟨i₀, ?_⟩
  have hsum : ∑ i, π (G i) = π (⋃ i, G i) := by
    rw [measure_iUnion hd hm, tsum_fintype]
  have hcard : (k : ℝ≥0∞) * π (G i₀) ≤ ∑ i, π (G i) := by
    have := Finset.card_nsmul_le_sum (Finset.univ : Finset (Fin k))
      (fun i => π (G i)) (π (G i₀)) fun i _ => hmin i (Finset.mem_univ i)
    rwa [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  rw [ENNReal.le_div_iff_mul_le (Or.inl (by exact_mod_cast hk))
    (Or.inl (by simp)), mul_comm]
  exact hcard.trans (hsum ▸ prob_le_one)

/--
**`C7` at print's quantifiers.** `k` contexts with the same observation law,
one randomized controller, pairwise disjoint success sets: some context
succeeds with probability at most `1 / k`.

`exists_measure_le_inv_of_disjoint` is the counting content and this is the
statement print makes, with the observation and the controller still present as
binders rather than folded into one law by prose.
-/
public theorem exists_success_le_inv {k : ℕ} (hk : k ≠ 0) (obs : Fin k → Measure O)
    (hobs : ∀ i j, obs i = obs j) (act : O → Measure A)
    [∀ i, IsProbabilityMeasure (actionLaw (obs i) act)] (G : Fin k → Set A)
    (hm : ∀ i, MeasurableSet (G i)) (hd : Pairwise (Function.onFun Disjoint G)) :
    ∃ i, actionLaw (obs i) act (G i) ≤ 1 / k := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  obtain ⟨i₀, hi₀⟩ := exists_measure_le_inv_of_disjoint hk
    (actionLaw (obs ⟨0, hk0⟩) act) G hm hd
  exact ⟨i₀, by rwa [actionLaw_congr (hobs i₀ ⟨0, hk0⟩) act]⟩

end C7

/-! ## `C8`: the binary bound, and what it costs to beat it -/

section C8

variable {O : Type*} [MeasurableSpace O]

/--
**`C8`, undivided: the two success probabilities sum to at most `1 + TV`.**

The halving in print's statement is a prior, and it is the only thing the
factor of two is. This form carries the content and has no division.
-/
public theorem success_add_le_one_add_eventGap (P₀ P₁ : Measure O)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] {A : Set O}
    (hA : MeasurableSet A) : P₀ Aᶜ + P₁ A ≤ 1 + eventGap P₀ P₁ := by
  have hgap : P₁ A - P₀ A ≤ eventGap P₀ P₁ :=
    le_iSup_of_le A (le_iSup_of_le hA le_sup_right)
  have hstep : P₀ Aᶜ + P₁ A ≤ 1 + (P₁ A - P₀ A) := by
    rw [prob_compl_eq_one_sub hA]
    rcases le_total (P₀ A) (P₁ A) with h | h
    · have e1 : (1 : ℝ≥0∞) - P₀ A + P₀ A = 1 := tsub_add_cancel_of_le prob_le_one
      have e2 : P₁ A - P₀ A + P₀ A = P₁ A := tsub_add_cancel_of_le h
      calc 1 - P₀ A + P₁ A = 1 - P₀ A + (P₁ A - P₀ A + P₀ A) := by rw [e2]
        _ = 1 - P₀ A + P₀ A + (P₁ A - P₀ A) := by ac_rfl
        _ = 1 + (P₁ A - P₀ A) := by rw [e1]
        _ ≤ 1 + (P₁ A - P₀ A) := le_rfl
    · calc 1 - P₀ A + P₁ A ≤ 1 - P₁ A + P₁ A := by gcongr
        _ = 1 := tsub_add_cancel_of_le prob_le_one
        _ ≤ 1 + (P₁ A - P₀ A) := le_self_add
  exact hstep.trans (by gcongr)

/--
**`C8`: equal-prior average success is at most `(1 + TV) / 2`.**

Print picks the decision-one region and maximizes the success by hand; here the
maximum is `eventGap`, so the bound holds at every measurable region without a
maximization step.
-/
public theorem avgSuccess_le_one_add_eventGap (P₀ P₁ : Measure O)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] {A : Set O}
    (hA : MeasurableSet A) :
    (P₀ Aᶜ + P₁ A) / 2 ≤ (1 + eventGap P₀ P₁) / 2 :=
  ENNReal.div_le_div_right (success_add_le_one_add_eventGap P₀ P₁ hA) 2

/--
**`C8`, contrapositive: near-certain success forces the laws apart.**

Print writes it as `TV ≥ 1 - 2ε`; in `ℝ≥0∞` the same content is that twice the
guaranteed success is at most one plus the gap, with no subtraction to truncate.
-/
public theorem eventGap_ge_of_success (P₀ P₁ : Measure O)
    [IsProbabilityMeasure P₀] [IsProbabilityMeasure P₁] {A : Set O}
    (hA : MeasurableSet A) {c : ℝ≥0∞} (h₀ : c ≤ P₀ Aᶜ) (h₁ : c ≤ P₁ A) :
    2 * c ≤ 1 + eventGap P₀ P₁ := by
  refine le_trans ?_ (success_add_le_one_add_eventGap P₀ P₁ hA)
  rw [two_mul]
  exact add_le_add h₀ h₁

end C8

end AISafetyAtlas.Sovereignty
