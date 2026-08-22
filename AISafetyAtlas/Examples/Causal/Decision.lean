module

public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Examples.Causal.BehavioralCollision

/-!
# A non-vacuous decision example

The behavioral-collision example supplies two models whose transforms agree.
This companion supplies the opposite check required by the decision layer:
the identified-set relation is not universal. A second edgeless model has
`P(X=1) = P(Y=1) = 4/5`, so its no-intervention transform has the opposite
sign from the original model's. At zero regret no common policy can serve
both models.
-/

namespace AISafetyAtlas.Examples.Causal

open AISafetyAtlas.Causal

local notation:max "Model" C:arg =>
  AISafetyAtlas.Causal.Model C (binaryDim C) ℚ
local notation:max "InterventionProfile" C:arg =>
  AISafetyAtlas.Causal.InterventionProfile C (binaryDim C)
local notation:max "Mixture" C:arg =>
  AISafetyAtlas.Causal.Mixture C (binaryDim C) ℚ
local notation:max "ProbMixture" C:arg =>
  AISafetyAtlas.Causal.ProbMixture C (binaryDim C) ℚ

/-! ## Transform equality gives shared optimal behavior -/

/-- The collision supplies one policy family that is optimal in both models.

This is the machine-checked forward bridge from the numerical transform collision
to the optimal-policy-oracle reading used by MAIS A2. -/
public theorem margin_class_not_identifiable_shared_optimal :
    Skeleton.ValidMargin lam ∧ ∃ M M' : Model (Fin 2),
      M.parents ≠ M'.parents ∧ M ≠ M' ∧ InIdentifiedSet skel lam 0 M M' := by
  rcases margin_class_not_identifiable with
    ⟨hlam, M, M', hM, hM', hparents, hne, hEq⟩
  exact ⟨hlam, M, M', hparents, hne,
    inIdentifiedSet_zero_of_behaviorEq skel lam hM hM' hEq⟩

/-! ## Fibre-indexing regression

At `C = Fin 2` and `visible = ∅` there is one visible fibre. Summing `Δmask`
over all four assignments would count it four times; the representative image
must stay a singleton.
-/

/-- With nothing visible, `fibreRep` collapses every assignment to one point. -/
public theorem card_fibreRep_empty :
    (Finset.univ.image (fibreRep edgeless (∅ : Finset (Fin 2)))).card = 1 := by
  decide

/-! ## A second margin-class model -/

/-- The edgeless high-corner model, with both marginal probabilities `4/5`. -/
@[expose] public def high : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun _ => ∅
  acyclic := ⟨fun _ => 0, by intro c p hp; simp at hp⟩
  cpt := fun _ a _ ↦ bernoulli (4/5) a
  cpt_parents := by intro c a v w _; rfl
  cpt_nonneg := by intro c a v; fin_cases a <;> norm_num [bernoulli]
  cpt_sum := by intro c v; rw [Fin.sum_univ_two]; norm_num [bernoulli]

/-- `high` satisfies the margin conditions at the construction's margin. -/
public theorem high_mem : skel.MarginClass high lam := by
  refine ⟨lam_valid, ?_, skel_M2, skel_M3, ?_, skel_M5 _, skel_M6⟩
  · intro c a v
    fin_cases a <;> constructor <;> norm_num [high, bernoulli, lam]
  · intro c p hp
    simp [high] at hp

/-! ## A point-mass probability mixture -/

/-- The intervention profile that leaves both variables untouched. -/
@[expose] public def identityProfile : InterventionProfile (Fin 2) :=
  fun _ => LocalIntervention.identity

/-- A probability mixture concentrated on `identityProfile`. -/
@[expose] public def identityMixture : Mixture (Fin 2) :=
  fun σ => if σ = identityProfile then 1 else 0

/-- The point mass on the identity profile is a probability mixture. -/
public theorem identityMixture_isProbability : IsProbabilityMixture identityMixture := by
  classical
  constructor
  · intro σ
    simp only [identityMixture]
    split_ifs <;> norm_num
  · simp only [identityMixture]
    rw [Finset.sum_ite_eq']
    simp

/-- The point-mass mixture packaged for the decision layer. -/
@[expose] public def identityProbMixture : ProbMixture (Fin 2) :=
  ⟨identityMixture, identityMixture_isProbability⟩

/-! ## Opposite signs -/

/-- The high-corner model's identity transform is negative. -/
public theorem transform_identity_high :
    high.Δ g identityProfile = -(7/50) := by
  rw [Δ_eq_half_sub_joint]
  unfold Model.jointProb Model.factor
  simp [Fin.prod_univ_two, identityProfile, LocalIntervention.identity,
    identityIntervention, high, bernoulli, asg]
  norm_num

/-- The original model's masked transform at the identity mixture is positive. -/
public theorem masked_identity_edgeless :
    edgeless.Δmask skel.gap ∅ (asg false false) identityProbMixture = 1/10 := by
  rw [Model.Δmask_empty, skel_gap, Model.Δmix_eq_sum]
  simp only [identityProbMixture, identityMixture]
  have hpick : ∀ f : InterventionProfile (Fin 2) → ℚ,
      (∑ σ, (if σ = identityProfile then (1 : ℚ) else 0) * f σ) =
        f identityProfile := by
    intro f
    rw [Finset.sum_eq_single identityProfile]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hp
      simp at hp
  rw [hpick]
  change edgeless.Δ g (fun _ => LocalIntervention.identity) = 1/10
  exact transform_identity_edgeless

/-- The high model's masked transform at the identity mixture is negative. -/
public theorem masked_identity_high :
    high.Δmask skel.gap ∅ (asg false false) identityProbMixture = -(7/50) := by
  rw [Model.Δmask_empty, skel_gap, Model.Δmix_eq_sum]
  simp only [identityProbMixture, identityMixture]
  have hpick : ∀ f : InterventionProfile (Fin 2) → ℚ,
      (∑ σ, (if σ = identityProfile then (1 : ℚ) else 0) * f σ) =
        f identityProfile := by
    intro f
    rw [Finset.sum_eq_single identityProfile]
    · simp
    · intro b _ hb
      simp [hb]
    · intro hp
      simp at hp
  rw [hpick, transform_identity_high]

/-- Two margin-class models can fail to share a zero-regret policy family. -/
public theorem not_inIdentifiedSet_high :
    ¬InIdentifiedSet skel lam 0 edgeless high := by
  apply not_inIdentifiedSet_of_opposite_sign skel lam edgeless high ∅
    (by simp [skel]) identityProbMixture (asg false false)
  · rw [masked_identity_edgeless]
    norm_num
  · rw [masked_identity_high]
    norm_num

/-! ## Normalization outside the binary case

`realizable_iff` is a two-point statement and cannot say anything about a task
with three or more decisions. `realizable_iff_general` can, and this is a worked
instance in exactly that region: a three-decision family on the collision's
chart, whose fibrewise spread is `3/4` and which is therefore realized by a
normalized utility. RE24 Appendix A.2 equation (2) normalizes at this arity; the
binary lemma has no statement here at all. -/

/-- A three-decision family on the two-variable chart. -/
@[expose] public def ternaryGap : Fin 3 → Assignment (Fin 2) (binaryDim (Fin 2)) → ℚ :=
  fun d _ ↦ ![0, 1/2, 3/4] d

/-- The three-decision family is realized by a normalized utility, which is a
conclusion `realizable_iff` cannot state. -/
public theorem ternaryGap_realizable :
    ∃ u : Fin 3 → Assignment (Fin 2) (binaryDim (Fin 2)) → ℚ,
      (∀ d v, 0 ≤ u d v ∧ u d v ≤ 1) ∧
      (∀ d v w, (∀ z ∈ (∅ : Finset (Fin 2)), v z = w z) → u d v = u d w) ∧
      (∀ d d' v, u d v - u d' v = ternaryGap d v - ternaryGap d' v) := by
  refine (Skeleton.realizable_iff_general (dim := binaryDim (Fin 2)) ∅ ternaryGap
    (fun d v w _ ↦ rfl)).mp (fun v ↦ ?_)
  have hsup : Finset.univ.sup' Finset.univ_nonempty (fun d ↦ ternaryGap d v) ≤ 3/4 :=
    Finset.sup'_le _ _ (fun d _ ↦ by fin_cases d <;> norm_num [ternaryGap])
  have hinf : (0 : ℚ) ≤ Finset.univ.inf' Finset.univ_nonempty (fun d ↦ ternaryGap d v) :=
    Finset.le_inf' _ _ (fun d _ ↦ by fin_cases d <;> norm_num [ternaryGap])
  linarith

end AISafetyAtlas.Examples.Causal
