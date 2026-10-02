module

public import AISafetyAtlas.Sovereignty.Value

/-!
# Influence, and why it is not power

The proposal's §4.2 measures how much one party's intervention can move the
distribution of a matter, holding the other party's policy fixed. That number
is not a guarantee and not an entitlement, and §4.3 spends three results saying
so.

## The measure

`eventGap` is the largest difference two laws assign to a measurable event. It
is the total-variation distance written directly, and it is written directly
rather than imported because that is the form print's arguments use: `Q7` is
"the gap vanishes exactly on equality", `Q8` is "every event downstairs is a
preimage".

`influenceCapacity` is §4.2's capacity for causal influence: the largest gap the
complement can open at a fixed coalition commitment. Print is emphatic that
this is a **capacity**, so it cannot be called zero because the other party
currently abstains -- and the definition makes that visible, since the
supremum is over all its commitments and not over a deployed one.

## The three results

`eventGap_eq_zero_iff` is `Q7`: zero capacity is interventional independence,
distribution by distribution, and not counterfactual equality under some
coupling.

`eventGap_map_le` is `Q8`: coarsening cannot increase the gap, so agreement at
a coarse resolution establishes nothing at a fine one. This is the reason an
audit that looks only at summary statistics cannot certify non-influence.

`Q9` -- influence and full option sovereignty coexist -- is in
`AISafetyAtlas.Examples.Sovereignty.Influence`.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

open MeasureTheory
open scoped ENNReal

universe u v w

variable {N : Type u} {X : Type v} [MeasurableSpace X]

/-- **The largest difference two laws assign to a measurable event.** -/
@[expose] public noncomputable def eventGap (μ ν : Measure X) : ℝ≥0∞ :=
  ⨆ (Φ : Set X) (_ : MeasurableSet Φ), (μ Φ - ν Φ) ⊔ (ν Φ - μ Φ)

/-- The gap is symmetric. -/
public theorem eventGap_comm (μ ν : Measure X) : eventGap μ ν = eventGap ν μ := by
  simp only [eventGap]
  exact iSup_congr fun _ => iSup_congr fun _ => sup_comm _ _

/-- **`Q7`: the gap vanishes exactly on equality of every event's probability.**

Print's statement is that zero influence capacity is distributional
interventional independence. It is not individual-counterfactual equality under
every coupling, and nothing here says it is: the right-hand side quantifies over
events, not over outcomes.
-/
public theorem eventGap_eq_zero_iff (μ ν : Measure X) :
    eventGap μ ν = 0 ↔ ∀ Φ : Set X, MeasurableSet Φ → μ Φ = ν Φ := by
  constructor
  · intro h Φ hΦ
    have hle : (μ Φ - ν Φ) ⊔ (ν Φ - μ Φ) ≤ 0 := by
      rw [← h]
      exact le_iSup_of_le Φ (le_iSup_of_le hΦ le_rfl)
    rw [sup_le_iff] at hle
    have h1 : μ Φ ≤ ν Φ := tsub_eq_zero_iff_le.mp (le_antisymm hle.1 bot_le)
    have h2 : ν Φ ≤ μ Φ := tsub_eq_zero_iff_le.mp (le_antisymm hle.2 bot_le)
    exact le_antisymm h1 h2
  · intro h
    refine le_antisymm (iSup_le fun Φ => iSup_le fun hΦ => ?_) bot_le
    simp [h Φ hΦ]

/-- And therefore the two laws are equal. -/
public theorem eq_of_eventGap_eq_zero {μ ν : Measure X} (h : eventGap μ ν = 0) :
    μ = ν :=
  Measure.ext fun Φ hΦ => (eventGap_eq_zero_iff μ ν).mp h Φ hΦ

/--
**`Q8`: coarsening cannot increase the gap.**

Every measurable event downstairs is the pushforward image of its preimage
upstairs, and the supremum downstairs therefore ranges over fewer tests.
Equality at a coarse resolution is not evidence of causal independence at a
fine one.
-/
public theorem eventGap_map_le {Y : Type*} [MeasurableSpace Y] (f : X → Y)
    (hf : Measurable f) (μ ν : Measure X) :
    eventGap (μ.map f) (ν.map f) ≤ eventGap μ ν := by
  refine iSup_le fun B => iSup_le fun hB => ?_
  rw [Measure.map_apply hf hB, Measure.map_apply hf hB]
  exact le_iSup_of_le (f ⁻¹' B) (le_iSup_of_le (hf hB) le_rfl)

/-- The gap between two probability laws is at most one. -/
public theorem eventGap_le_one (μ ν : Measure X) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : eventGap μ ν ≤ 1 :=
  iSup_le fun _ => iSup_le fun _ =>
    sup_le (le_trans tsub_le_self prob_le_one) (le_trans tsub_le_self prob_le_one)

/-! ## Influence as a capacity -/

variable {G : GameForm.{u, v, w} N X}

/--
**The capacity for causal influence**, at a fixed coalition commitment: the
largest gap the complement can open between two of its own commitments.

A supremum over the complement's commitments, never over a deployed one. Print
insists on that and the definition carries it: a party that currently abstains
has exactly the capacity it would have if it did not.
-/
@[expose] public noncomputable def influenceCapacity (K : OutcomeLaw G) (C : Set N)
    (sC : ∀ i : C, G.strategy i) : ℝ≥0∞ :=
  ⨆ sD : ∀ i : (Cᶜ : Set N), G.strategy i, ⨆ sD' : ∀ i : (Cᶜ : Set N), G.strategy i,
    eventGap (K.law (spliceProfile C sC sD)) (K.law (spliceProfile C sC sD'))

/--
**Support-based sure effectivity.** The targets a coalition can force the law
onto almost surely: some commitment leaves the complement no way to give the
target's complement positive mass.

This is the qualitative reading of a stochastic system that print's `P12`
compares against the value -- effectivity read off the *support* rather than
off a deterministic outcome map.
-/
@[expose] public noncomputable def supportEffectivity (K : OutcomeLaw G) (C : Set N) :
    Set (Set X) :=
  {Φ | ∃ sC : ∀ i : C, G.strategy i,
    ∀ sD : ∀ i : (Cᶜ : Set N), G.strategy i, K.law (spliceProfile C sC sD) Φᶜ = 0}

/-- **Two laws with the same null sets have the same support-based
effectivity.** -/
public theorem supportEffectivity_congr {K K' : OutcomeLaw G} (C : Set N)
    (h : ∀ s Φ, K.law s Φ = 0 ↔ K'.law s Φ = 0) :
    supportEffectivity K C = supportEffectivity K' C := by
  ext Φ
  constructor
  · rintro ⟨sC, hsC⟩
    exact ⟨sC, fun sD => (h _ _).mp (hsC sD)⟩
  · rintro ⟨sC, hsC⟩
    exact ⟨sC, fun sD => (h _ _).mpr (hsC sD)⟩

/-- **Zero capacity is interventional independence**: every pair of complement
commitments induces the same law. This is `Q7` at the game form. -/
public theorem influenceCapacity_eq_zero_iff (K : OutcomeLaw G) (C : Set N)
    (sC : ∀ i : C, G.strategy i) :
    influenceCapacity K C sC = 0 ↔
      ∀ sD sD' : ∀ i : (Cᶜ : Set N), G.strategy i,
        K.law (spliceProfile C sC sD) = K.law (spliceProfile C sC sD') := by
  constructor
  · intro h sD sD'
    refine eq_of_eventGap_eq_zero (le_antisymm ?_ bot_le)
    rw [← h]
    exact le_iSup_of_le sD (le_iSup_of_le sD' le_rfl)
  · intro h
    refine le_antisymm (iSup_le fun sD => iSup_le fun sD' => ?_) bot_le
    rw [h sD sD', (eventGap_eq_zero_iff _ _).mpr fun _ _ => rfl]

end AISafetyAtlas.Sovereignty
