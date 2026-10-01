module

public import PFR.ForMathlib.Entropy.Basic
public import AISafetyAtlas.InformationTheory.ChannelCapacity

/-!
# Empowerment of a deterministic channel is the capacity of its range

The proposal's `B2`: for a finite deterministic channel `Z = f(A)`, the
empowerment `max_{P_A} I(A ; Z)` equals `log |range f|`.

`empowerment` is the supremum of the mutual information between the input and
its image, taken over all input laws. The bound is print's two-step argument --
a deterministic output has no conditional entropy, so the mutual information is
the output entropy, and an entropy is at most the log of the size of a set the
variable lives in. The attaining law is print's too: one input per reachable
output, uniformly weighted, which is `uniformOn (Set.range (Set.rangeSplitting f))`.

`empowerment_eq_channelCapacity_range` reads the answer back as the atlas's own
`AISafetyAtlas.InformationTheory.channelCapacity` of the reachable outputs. The
two definitions were written for different purposes and agree here, which is
the point: a deterministic actuator's empowerment is the noiseless capacity of
what it can actually reach, and nothing about the input alphabet beyond that
survives.

## Scope

Print's caveat is carried as a caveat and not as a hypothesis, because it is
about statements that are *not* made: with a stochastic channel, an adversary,
or constraints on the allowable input distributions, the reachable-output count
alone is insufficient. The supremum here is over *all* input laws, so the
constrained case is outside it; `mutualInfo_le_log_card_range` still holds law
by law and is the part that survives a restriction.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

open MeasureTheory ProbabilityTheory Real

section Section

variable {A Z : Type*} (f : A → Z)

/-- **One input per reachable output.** -/
@[expose] public noncomputable def section' : Set A :=
  Set.range (Set.rangeSplitting f)

/-- It is nonempty. -/
public theorem section'_nonempty [Nonempty A] : (section' f).Nonempty :=
  ⟨Set.rangeSplitting f ⟨f (Classical.arbitrary A), Set.mem_range_self _⟩,
    Set.mem_range_self _⟩

/-- The inputs of the section that hit a given reachable output are exactly one. -/
public theorem section'_inter_preimage (z : Z) (hz : z ∈ Set.range f) :
    section' f ∩ f ⁻¹' {z} = {Set.rangeSplitting f ⟨z, hz⟩} := by
  ext a
  constructor
  · rintro ⟨⟨w, rfl⟩, hfa⟩
    have hw : (w : Z) = z := by
      rw [← Set.apply_rangeSplitting f w]
      exact hfa
    subst hw
    rfl
  · rintro rfl
    exact ⟨Set.mem_range_self _, Set.apply_rangeSplitting f ⟨z, hz⟩⟩

end Section

variable {A Z : Type*} [Fintype A] [Nonempty A] [MeasurableSpace A]
  [DiscreteMeasurableSpace A] [MeasurableSingletonClass A] [Fintype Z]
  [MeasurableSpace Z] [DiscreteMeasurableSpace Z] (f : A → Z)

omit [Nonempty A] in
/-- **A deterministic output carries no conditional entropy.** -/
public theorem condEntropy_comp_id_eq_zero (μ : Measure A) [IsProbabilityMeasure μ] :
    H[f | (id : A → A) ; μ] = 0 := by
  have hpair : H[⟨(id : A → A), f⟩ ; μ] = H[(id : A → A) ; μ] :=
    entropy_prod_comp measurable_id μ f
  rw [chain_rule'' μ (Measurable.of_discrete (f := f)) measurable_id,
    entropy_comm (Measurable.of_discrete (f := f)) measurable_id, hpair, sub_self]

omit [Nonempty A] in
/-- **So the mutual information is the entropy of the output.** -/
public theorem mutualInfo_id_eq_entropy (μ : Measure A) [IsProbabilityMeasure μ] :
    I[(id : A → A) : f ; μ] = H[f ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy' measurable_id
    (Measurable.of_discrete (f := f)) μ, condEntropy_comp_id_eq_zero f μ, sub_zero]

omit [Nonempty A] in
/-- **`B2`, the bound.** At every input law the mutual information is at most
the log of the number of reachable outputs. -/
public theorem mutualInfo_le_log_card_range (μ : Measure A) [IsProbabilityMeasure μ] :
    I[(id : A → A) : f ; μ] ≤ log ((Set.range f).ncard) := by
  rw [mutualInfo_id_eq_entropy f μ]
  have h := entropy_le_log_card_of_mem_finite (Set.finite_range f)
    (Measurable.of_discrete (f := f)) (μ := μ)
    (Filter.Eventually.of_forall fun a => Set.mem_range_self a)
  rwa [Nat.card_coe_set_eq] at h

omit [Fintype A] [Nonempty A] [Fintype Z] [MeasurableSpace Z]
  [DiscreteMeasurableSpace Z] in
/-- **The uniform law on the section makes the output uniform on the range.** -/
public theorem isUniform_section : IsUniform (Set.range f) f (uniformOn (section' f)) := by
  have hmeas : ∀ s : Set A, MeasurableSet s := fun _ => MeasurableSet.of_discrete
  constructor
  · intro z hz z' hz'
    rw [uniformOn, cond_apply (hmeas _), cond_apply (hmeas _),
      section'_inter_preimage f z hz, section'_inter_preimage f z' hz',
      Measure.count_singleton, Measure.count_singleton]
  · have : f ⁻¹' (Set.range f)ᶜ = (∅ : Set A) := by
      ext a
      simp
    rw [this, measure_empty]

omit [DiscreteMeasurableSpace A] [Fintype Z] [MeasurableSpace Z]
  [DiscreteMeasurableSpace Z] in
/-- The uniform law on the section is a probability measure. -/
public theorem isProbabilityMeasure_section :
    IsProbabilityMeasure (uniformOn (section' f)) :=
  isProbabilityMeasure_uniformOn (Set.toFinite _) (section'_nonempty f)

/-- **`B2`, attainment.** -/
public theorem mutualInfo_section_eq :
    I[(id : A → A) : f ; uniformOn (section' f)] = log ((Set.range f).ncard) := by
  have := isProbabilityMeasure_section f
  rw [mutualInfo_id_eq_entropy f, IsUniform.entropy_eq' (Set.finite_range f)
    (isUniform_section f) (Measurable.of_discrete (f := f))]

/--
**Empowerment of a channel**: the largest mutual information between the input
and the output over all input laws.
-/
@[expose] public noncomputable def empowerment : ℝ :=
  sSup {i : ℝ | ∃ μ : Measure A, ∃ _ : IsProbabilityMeasure μ,
    I[(id : A → A) : f ; μ] = i}

/-- **`B2`: it is the log of the number of reachable outputs.** -/
public theorem empowerment_eq_log_card_range :
    empowerment f = log ((Set.range f).ncard) := by
  have hprob := isProbabilityMeasure_section f
  refine IsLUB.csSup_eq ⟨?_, ?_⟩ ⟨_, uniformOn (section' f), hprob,
    mutualInfo_section_eq f⟩
  · rintro i ⟨μ, hμ, rfl⟩
    exact mutualInfo_le_log_card_range f μ
  · intro b hb
    exact hb ⟨uniformOn (section' f), hprob, mutualInfo_section_eq f⟩

/-- **And that is the noiseless capacity of the reachable outputs**, in the
atlas's own sense. The two definitions were written for different purposes:
`channelCapacity` counts signals a channel can carry, `empowerment` maximizes
an information over input laws. They agree here, and nothing about the input
alphabet beyond the reachable count survives. -/
public theorem empowerment_eq_channelCapacity_range [Fintype (Set.range f)] :
    empowerment f = InformationTheory.channelCapacity (Set.range f) := by
  rw [empowerment_eq_log_card_range, InformationTheory.channelCapacity,
    ← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]

end AISafetyAtlas.Sovereignty
