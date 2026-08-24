module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import AISafetyAtlas.Examples.Causal.OneNodeClass
public import AISafetyAtlas.Examples.Causal.Query
public import AISafetyAtlas.Examples.Conjectures.MAIS.Common

/-!
# MAIS-O31 — witnesses, chambers, and what the root coordinate does

The antecedent is inhabited in both chambers, and in the same-side chamber the
root coordinate is not identified. The one-node chain shows the same-side
chamber can be empty.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ## MAIS-O31: the antecedent is inhabited, chamber disjunct included

`maisO31_chainClassificationCandidate` quantifies over a chain model, a margin,
a threshold in `(0,1)` and an intervened node, and then assumes the **chamber
disjunct** — the transfer from hard-fixing `C_j` either straddles the decision
threshold or stays strictly on one side. The pieces were separately inhabited and
the disjunct was not, so nothing ruled out an antecedent that no model meets.

The witness below closes that. It is a two-node chain, and the straddling branch
is the one it lands in — the branch issue #8's first bullet is about, so the
implication whose hypothesis it is is not vacuous either. -/

/-- A two-node chain at margin `1/10`: root `2/5`, and a child whose transition
probabilities `1/5` and `7/10` sit on opposite sides of the threshold `1/2`. -/
@[expose] public noncomputable def o31Witness : O31ChainModel 1 where
  root := 2 / 5
  transition := fun _ x ↦ if x = 1 then 7 / 10 else 1 / 5

public theorem o31Witness_valid : o31Witness.Valid (1 / 10) := by
  refine ⟨by norm_num, by norm_num, ⟨by norm_num [o31Witness], by norm_num [o31Witness]⟩,
    ?_, ?_⟩
  · intro i x
    fin_cases x <;> exact ⟨by norm_num [o31Witness], by norm_num [o31Witness]⟩
  · intro i
    norm_num [o31Witness]

public theorem o31Witness_generic : o31Witness.Generic (1 / 10) := by
  refine ⟨by norm_num [o31Witness], by norm_num [o31Witness], ?_, ?_⟩
  · intro i x
    fin_cases x <;> exact ⟨by norm_num [o31Witness], by norm_num [o31Witness]⟩
  · intro i
    norm_num [o31Witness]

/-- The gap pair `(-1/2, 1/2)` meets `q:chain`'s (M2)–(M3) at this margin, in the
sign order `g₀ < 0 < g₁`. -/
public theorem o31Witness_gap : O31UtilityGap (1 / 10) (-(1 / 2)) (1 / 2) := by
  unfold O31UtilityGap
  norm_num

/-- And it induces the threshold `1/2`, by `o31Threshold`'s own formula. -/
public theorem o31Witness_threshold : o31Threshold (-(1 / 2)) (1 / 2) = 1 / 2 := by
  norm_num [o31Threshold]

/-- Hard-fixing the root to `0` transfers the child's `0`-column. -/
public theorem o31Witness_target_zero :
    o31Witness.targetProbability (o31SingleNodeProfile (Fin.last 1) (fun _ ↦ 0)) = 1 / 5 := by
  rw [O31ChainModel.targetProbability, ← Equiv.sum_comp finFunctionFinEquiv.symm]
  simp [Fin.sum_univ_four, O31ChainModel.jointProb, O31ChainModel.nodeParameter,
    o31SingleNodeProfile, o31Witness, finFunctionFinEquiv,
    AISafetyAtlas.Conjectures.BinaryPair.interventionFactor,
    AISafetyAtlas.Conjectures.BinaryPair.bernoulli]
  rw [show (0 : Fin 2) = Fin.castSucc 0 from rfl, Fin.lastCases_castSucc]

/-- And to `1` transfers the `1`-column. -/
public theorem o31Witness_target_one :
    o31Witness.targetProbability (o31SingleNodeProfile (Fin.last 1) (fun _ ↦ 1)) = 7 / 10 := by
  rw [O31ChainModel.targetProbability, ← Equiv.sum_comp finFunctionFinEquiv.symm]
  simp [Fin.sum_univ_four, O31ChainModel.jointProb, O31ChainModel.nodeParameter,
    o31SingleNodeProfile, o31Witness, finFunctionFinEquiv,
    AISafetyAtlas.Conjectures.BinaryPair.interventionFactor,
    AISafetyAtlas.Conjectures.BinaryPair.bernoulli]
  rw [show (0 : Fin 2) = Fin.castSucc 0 from rfl, Fin.lastCases_castSucc]

/-- **The chamber disjunct holds, on its straddling branch.** `1/5 < 1/2 < 7/10`,
so the transfer from hard-fixing the root crosses the decision threshold. -/
public theorem o31Witness_straddles :
    O31StraddlingChamber (1 / 2) (Fin.last 1) o31Witness := by
  unfold O31StraddlingChamber
  rw [o31Witness_target_zero, o31Witness_target_one]
  norm_num

/-- **The whole antecedent of `maisO31_chainClassificationCandidate` is
inhabited.** Threshold bounds, validity, genericity and the chamber disjunct
hold together at one model, so the statement is not vacuously true for want of a
model meeting its hypotheses. -/
public theorem o31_antecedent_inhabited :
    0 < (1 / 2 : ℝ) ∧ (1 / 2 : ℝ) < 1 ∧ o31Witness.Valid (1 / 10) ∧
      o31Witness.Generic (1 / 10) ∧
      (O31StraddlingChamber (1 / 2) (Fin.last 1) o31Witness ∨
        O31SameSideChamber (1 / 2) (Fin.last 1) o31Witness) :=
  ⟨by norm_num, by norm_num, o31Witness_valid, o31Witness_generic,
    Or.inl o31Witness_straddles⟩

/-! ## The same-side chamber

`o31_antecedent_inhabited` lands on the straddling branch. The other branch of
the chamber disjunct is settled here, and it is settled *generally* rather than
at a witness: the mixture layer can never carry the endpoint probability outside
the interval the two hard interventions span, so when that whole interval sits
on one side of the threshold no behaviour distinguishes models that share it.

The candidate's same-side content is a **negative**. `O31StraddlingChamber` and
`O31SameSideChamber` are mutually exclusive, so on the same-side branch the right
side of the candidate's equivalence is false for every coordinate, and the claim
is that no coordinate is identified. `o31_sameSide_root_not_identified` proves
that for the root at a two-node chain. The two transition coordinates, and chains
with more nodes, are not settled here.
-/

private theorem convexCombo_lt {a b x y B : ℝ} (hs : a + b = 1) (hn0 : 0 ≤ a)
    (hn1 : 0 ≤ b) (h0 : x < B) (h1 : y < B) : a * x + b * y < B := by
  rcases lt_or_ge 0 a with ha | ha
  · have p1 : a * x < a * B := mul_lt_mul_of_pos_left h0 ha
    have p2 : b * y ≤ b * B := mul_le_mul_of_nonneg_left h1.le hn1
    have hsum : a * B + b * B = B := by rw [← add_mul, hs, one_mul]
    linarith
  · have ha0 : a = 0 := le_antisymm ha hn0
    subst ha0; simp at hs ⊢; subst hs; linarith

private theorem lt_convexCombo {a b x y B : ℝ} (hs : a + b = 1) (hn0 : 0 ≤ a)
    (hn1 : 0 ≤ b) (h0 : B < x) (h1 : B < y) : B < a * x + b * y := by
  rcases lt_or_ge 0 a with ha | ha
  · have p1 : a * B < a * x := mul_lt_mul_of_pos_left h0 ha
    have p2 : b * B ≤ b * y := mul_le_mul_of_nonneg_left h1.le hn1
    have hsum : a * B + b * B = B := by rw [← add_mul, hs, one_mul]
    linarith
  · have ha0 : a = 0 := le_antisymm ha hn0
    subst ha0; simp at hs ⊢; subst hs; linarith

open AISafetyAtlas.Conjectures.BinaryPair in
/-- A local intervention redistributes the node's mass without creating any: the
weight it puts on the two realized values sums to one, whichever of the four
maps it is. -/
public theorem interventionFactor_add_eq_one (p : ℝ) (f : Fin 2 → Fin 2) :
    interventionFactor p f 0 + interventionFactor p f 1 = 1 := by
  have h : interventionFactor p f 0 + interventionFactor p f 1
      = ∑ r : Fin 2, interventionFactor p f r := by rw [Fin.sum_univ_two]
  rw [h]
  simp only [interventionFactor]
  rw [Finset.sum_comm]
  have hcol : ∀ a : Fin 2,
      ∑ r : Fin 2, (if f a = r then AISafetyAtlas.Conjectures.BinaryPair.bernoulli p a else 0) = AISafetyAtlas.Conjectures.BinaryPair.bernoulli p a := by
    intro a; simp
  rw [Finset.sum_congr rfl (fun a _ => hcol a)]
  simp [Fin.sum_univ_two, AISafetyAtlas.Conjectures.BinaryPair.bernoulli]

open AISafetyAtlas.Conjectures.BinaryPair in
/-- And it never puts negative weight there, at a parameter that is a
probability. -/
public theorem interventionFactor_nonneg {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)
    (f : Fin 2 → Fin 2) (r : Fin 2) : 0 ≤ interventionFactor p f r := by
  simp only [interventionFactor]
  apply Finset.sum_nonneg
  intro a _
  split_ifs with h
  · simp only [AISafetyAtlas.Conjectures.BinaryPair.bernoulli]; split_ifs <;> linarith
  · exact le_refl 0

open AISafetyAtlas.Conjectures.BinaryPair in
/-- **A root intervention reads the two transition columns and nothing else.**
On a two-node chain the endpoint probability under any local map at the root is
the affine combination of the two columns with the map's own weights. The root
probability enters only through those weights. -/
public theorem targetProbability_root_eq (M : O31ChainModel 1) (f : Fin 2 → Fin 2) :
    M.targetProbability (o31SingleNodeProfile (Fin.last 1) f)
      = interventionFactor M.root f 0 * M.transition 0 0
        + interventionFactor M.root f 1 * M.transition 0 1 := by
  rw [O31ChainModel.targetProbability, ← Equiv.sum_comp finFunctionFinEquiv.symm]
  simp [Fin.sum_univ_four, O31ChainModel.jointProb, O31ChainModel.nodeParameter,
    o31SingleNodeProfile, finFunctionFinEquiv, interventionFactor, AISafetyAtlas.Conjectures.BinaryPair.bernoulli,
    Fin.sum_univ_two]
  rw [show (0 : Fin 2) = Fin.castSucc 0 from rfl, show (1 : Fin 2) = Fin.last 1 from rfl]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  ring

/-- Hard-fixing the root to `0` transfers the child's `0`-column, at every model. -/
public theorem targetProbability_const_zero (M : O31ChainModel 1) :
    M.targetProbability (o31SingleNodeProfile (Fin.last 1) (fun _ => 0))
      = M.transition 0 0 := by
  rw [targetProbability_root_eq]
  simp [AISafetyAtlas.Conjectures.BinaryPair.interventionFactor, Fin.sum_univ_two,
    AISafetyAtlas.Conjectures.BinaryPair.bernoulli]

/-- And to `1` transfers the `1`-column. -/
public theorem targetProbability_const_one (M : O31ChainModel 1) :
    M.targetProbability (o31SingleNodeProfile (Fin.last 1) (fun _ => 1))
      = M.transition 0 1 := by
  rw [targetProbability_root_eq]
  simp [AISafetyAtlas.Conjectures.BinaryPair.interventionFactor, Fin.sum_univ_two,
    AISafetyAtlas.Conjectures.BinaryPair.bernoulli]

/-- **A mixture never escapes a bound every pure intervention respects.** This is
what makes the chamber a statement about the whole behaviour rather than about
the four hard interventions: `O31BehaviorEqAt` quantifies over every real
mixture, and none of them reaches past the transfer interval. -/
public theorem mixedTargetProbability_le {M : O31ChainModel 1} {B : ℝ}
    {mix : O31LocalMixture}
    (h : ∀ f, M.targetProbability (o31SingleNodeProfile (Fin.last 1) f) ≤ B) :
    M.mixedTargetProbability (Fin.last 1) mix ≤ B := by
  rw [O31ChainModel.mixedTargetProbability]
  calc ∑ f : Fin 2 → Fin 2, mix.weight f *
          M.targetProbability (o31SingleNodeProfile (Fin.last 1) f)
      ≤ ∑ f : Fin 2 → Fin 2, mix.weight f * B :=
        Finset.sum_le_sum (fun f _ => mul_le_mul_of_nonneg_left (h f) (mix.nonneg f))
    _ = B := by rw [← Finset.sum_mul, mix.sum_one, one_mul]

/-- The mirror bound, below. -/
public theorem le_mixedTargetProbability {M : O31ChainModel 1} {B : ℝ}
    {mix : O31LocalMixture}
    (h : ∀ f, B ≤ M.targetProbability (o31SingleNodeProfile (Fin.last 1) f)) :
    B ≤ M.mixedTargetProbability (Fin.last 1) mix := by
  rw [O31ChainModel.mixedTargetProbability]
  calc B = ∑ f : Fin 2 → Fin 2, mix.weight f * B := by
        rw [← Finset.sum_mul, mix.sum_one, one_mul]
    _ ≤ _ := Finset.sum_le_sum (fun f _ => mul_le_mul_of_nonneg_left (h f) (mix.nonneg f))

/-- Every root intervention stays below a bound both transition columns are
below. -/
public theorem targetProbability_lt {M : O31ChainModel 1} {B : ℝ}
    (hr0 : 0 ≤ M.root) (hr1 : M.root ≤ 1)
    (h0 : M.transition 0 0 < B) (h1 : M.transition 0 1 < B) (f : Fin 2 → Fin 2) :
    M.targetProbability (o31SingleNodeProfile (Fin.last 1) f) < B := by
  rw [targetProbability_root_eq]
  exact convexCombo_lt (interventionFactor_add_eq_one M.root f)
    (interventionFactor_nonneg hr0 hr1 f 0) (interventionFactor_nonneg hr0 hr1 f 1) h0 h1

/-- And above a bound both columns are above. -/
public theorem lt_targetProbability {M : O31ChainModel 1} {B : ℝ}
    (hr0 : 0 ≤ M.root) (hr1 : M.root ≤ 1)
    (h0 : B < M.transition 0 0) (h1 : B < M.transition 0 1) (f : Fin 2 → Fin 2) :
    B < M.targetProbability (o31SingleNodeProfile (Fin.last 1) f) := by
  rw [targetProbability_root_eq]
  exact lt_convexCombo (interventionFactor_add_eq_one M.root f)
    (interventionFactor_nonneg hr0 hr1 f 0) (interventionFactor_nonneg hr0 hr1 f 1) h0 h1

/-- **The same-side chamber identifies no root**, at a two-node chain with the
root intervened, and at every model rather than at one witness.

The mate keeps both transition columns and moves the root to the margin
endpoint. It only has to be `O31ChainModel.Valid` — the comparison class inside
`O31IdentifiesCoordinate` is the source's own closed-margin class, not the
strengthened `O31ChainModel.Generic` the chamber hypothesis uses — so the
endpoint is available and the two models differ exactly at the root.

Behavioural equality is then the convex-hull bound: both models share the
transfer interval, the interval is strictly on one side of the threshold, so
every mixture of every local map leaves both advantages with the same sign and
`ShareBinaryOptimum` holds throughout. -/
public theorem o31_sameSide_root_not_identified {lam t : ℝ} {M : O31ChainModel 1}
    (hV : M.Valid lam) (hG : M.Generic lam)
    (hss : O31SameSideChamber t (Fin.last 1) M) :
    ¬ O31IdentifiesCoordinate lam t (Fin.last 1) M .root := by
  obtain ⟨hlam, hlam2, hroot, htrans, hedge⟩ := hV
  obtain ⟨hgr0, hgr1, hgt, hge⟩ := hG
  have hr0 : (0:ℝ) ≤ M.root := by linarith [hroot.1]
  have hr1 : M.root ≤ 1 := by linarith [hroot.2]
  have hMate : (⟨lam, M.transition⟩ : O31ChainModel 1).Valid lam :=
    ⟨hlam, hlam2, ⟨le_refl lam, by linarith⟩, htrans, hedge⟩
  have hr0' : (0:ℝ) ≤ (⟨lam, M.transition⟩ : O31ChainModel 1).root := by
    show (0:ℝ) ≤ lam; linarith
  have hr1' : (⟨lam, M.transition⟩ : O31ChainModel 1).root ≤ 1 := by
    show lam ≤ (1:ℝ); linarith
  rw [O31SameSideChamber, targetProbability_const_zero, targetProbability_const_one] at hss
  intro hid
  have hne : (⟨lam, M.transition⟩ : O31ChainModel 1).coordinate .root
      ≠ M.coordinate .root := by
    show lam ≠ M.root
    exact ne_of_lt hgr0
  refine hne (hid ⟨lam, M.transition⟩ hMate ?_)
  intro mix
  rcases mul_pos_iff.mp hss with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have hA : t < M.transition 0 0 := by linarith
    have hB : t < M.transition 0 1 := by linarith
    have k1 : t ≤ M.mixedTargetProbability (Fin.last 1) mix :=
      le_mixedTargetProbability (fun f => (lt_targetProbability hr0 hr1 hA hB f).le)
    have k2 : t ≤ (⟨lam, M.transition⟩ : O31ChainModel 1).mixedTargetProbability
        (Fin.last 1) mix :=
      le_mixedTargetProbability (fun f => (lt_targetProbability hr0' hr1' hA hB f).le)
    exact Or.inl ⟨by linarith, by linarith⟩
  · have hA : M.transition 0 0 < t := by linarith
    have hB : M.transition 0 1 < t := by linarith
    have k1 : M.mixedTargetProbability (Fin.last 1) mix ≤ t :=
      mixedTargetProbability_le (fun f => (targetProbability_lt hr0 hr1 hA hB f).le)
    have k2 : (⟨lam, M.transition⟩ : O31ChainModel 1).mixedTargetProbability
        (Fin.last 1) mix ≤ t :=
      mixedTargetProbability_le (fun f => (targetProbability_lt hr0' hr1' hA hB f).le)
    exact Or.inr ⟨by linarith, by linarith⟩

/-- A gap pair whose induced threshold clears both transfer endpoints, so the
same model that witnesses the straddling branch witnesses the other one. Both
gap values sit strictly inside the margin, which the source's Scope section
excludes the boundary of. -/
public theorem o31Witness_sameSide_gap : O31UtilityGap (1 / 10) (-(4 / 5)) (1 / 5) := by
  unfold O31UtilityGap
  norm_num

/-- Its threshold is `4/5`, by `o31Threshold`'s own formula. -/
public theorem o31Witness_sameSide_threshold : o31Threshold (-(4 / 5)) (1 / 5) = 4 / 5 := by
  norm_num [o31Threshold]

/-- **The chamber disjunct holds on its same-side branch too.** Both transfer
endpoints, `1/5` and `7/10`, fall below `4/5`. -/
public theorem o31Witness_sameSide :
    O31SameSideChamber (4 / 5) (Fin.last 1) o31Witness := by
  unfold O31SameSideChamber
  rw [o31Witness_target_zero, o31Witness_target_one]
  norm_num

/-- **The same-side branch of the antecedent is inhabited.** `o31_antecedent_inhabited`
inhabits the straddling branch; this inhabits the other one, at the same model
and the same intervened node, so neither branch of the chamber disjunct is empty. -/
public theorem o31_sameSide_antecedent_inhabited :
    0 < (4 / 5 : ℝ) ∧ (4 / 5 : ℝ) < 1 ∧ o31Witness.Valid (1 / 10) ∧
      o31Witness.Generic (1 / 10) ∧
      (O31StraddlingChamber (4 / 5) (Fin.last 1) o31Witness ∨
        O31SameSideChamber (4 / 5) (Fin.last 1) o31Witness) :=
  ⟨by norm_num, by norm_num, o31Witness_valid, o31Witness_generic,
    Or.inr o31Witness_sameSide⟩

/-- The general theorem, read at that witness: the root probability is not
identified there. -/
public theorem o31Witness_root_not_identified :
    ¬ O31IdentifiesCoordinate (1 / 10) (4 / 5) (Fin.last 1) o31Witness .root :=
  o31_sameSide_root_not_identified o31Witness_valid o31Witness_generic o31Witness_sameSide

/-! ## The one-node chain, where the same-side chamber is empty

`maisO31_chainClassificationCandidate` quantifies over every `n`, and the
withdrawal of the old `0 < n` hypothesis put the one-node chain inside it. There
the intervened node *is* the guessed endpoint, so the two hard interventions pin
the transfer at `0` and `1` and straddle every threshold a utility can induce.
The same-side branch is therefore vacuous at `n = 0`, and the candidate's
same-side content says nothing there. This is a fact about the transcription's
domain, and it is why the witnesses above need a two-node chain.
-/

open AISafetyAtlas.Conjectures.BinaryPair in
/-- At a one-node chain the endpoint probability is the intervened node's own
realized mass. -/
public theorem targetProbability_oneNode (M : O31ChainModel 0) (f : Fin 2 → Fin 2) :
    M.targetProbability (o31SingleNodeProfile (Fin.last 0) f)
      = interventionFactor M.root f 1 := by
  rw [O31ChainModel.targetProbability, ← Equiv.sum_comp finFunctionFinEquiv.symm]
  simp [Fin.sum_univ_two, O31ChainModel.jointProb, O31ChainModel.nodeParameter,
    o31SingleNodeProfile, finFunctionFinEquiv, interventionFactor, AISafetyAtlas.Conjectures.BinaryPair.bernoulli]
  rw [show (0 : Fin 1) = Fin.last 0 from rfl]
  simp only [Fin.lastCases_last]

/-- So hard-fixing it to `0` drives the endpoint probability to `0`. -/
public theorem targetProbability_oneNode_zero (M : O31ChainModel 0) :
    M.targetProbability (o31SingleNodeProfile (Fin.last 0) (fun _ => 0)) = 0 := by
  rw [targetProbability_oneNode]
  simp [AISafetyAtlas.Conjectures.BinaryPair.interventionFactor]

/-- And to `1` drives it to `1`. -/
public theorem targetProbability_oneNode_one (M : O31ChainModel 0) :
    M.targetProbability (o31SingleNodeProfile (Fin.last 0) (fun _ => 1)) = 1 := by
  rw [targetProbability_oneNode]
  simp [AISafetyAtlas.Conjectures.BinaryPair.interventionFactor, Fin.sum_univ_two,
    AISafetyAtlas.Conjectures.BinaryPair.bernoulli]

/-- **The same-side chamber is empty at a one-node chain**, for every threshold
`o31Threshold_mem_Ioo` admits. -/
public theorem o31_not_sameSideChamber_oneNode {t : ℝ} (ht0 : 0 < t) (ht1 : t < 1)
    (M : O31ChainModel 0) : ¬ O31SameSideChamber t (Fin.last 0) M := by
  rw [O31SameSideChamber, targetProbability_oneNode_zero, targetProbability_oneNode_one]
  intro h
  nlinarith


end AISafetyAtlas.Examples.Conjectures.MAIS
