module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import AISafetyAtlas.Examples.Causal.OneNodeClass
public import AISafetyAtlas.Examples.Causal.Query
public import AISafetyAtlas.Examples.Conjectures.MAIS.O31

/-!
# MAIS-O31 — the positive-measure counterexample

`q:chain`'s heuristic is labelled as such by its own author and asks for a
genuine indistinguishability construction. This is one, on an explicit open box
of positive Lebesgue measure: at every point two margin-valid models share the
transfer map and an optimal policy under every real root-intervention mixture,
and disagree on the observational marginal of `C₁`.

It refutes the marginal clause of that heuristic, at `m = 2`, with the root
intervened, in the same-side chamber. The marginal is not one of the literal
table coordinates, so this is consistent with issue #8's same-side branch rather
than in tension with it.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ### What the two models do to the agenda's heuristic

`q:chain` records a heuristic and labels it as such: mixtures at `C_j` *"should
reveal the composite transfer map from `C_j` to `C_1` and the observational
marginal of `C_1`, but not the individual factors nor anything upstream of
`C_j`"*, and the agenda adds that it has proved neither half.

The mate built above shares the transfer map and differs in that marginal, so at
this model the marginal is **not** revealed. It is the positive half of the
heuristic that fails here, not the negative half the agenda expects to need an
indistinguishability construction.

**What is checked.** The pair immediately below is a *single concrete instance*
on rational literals: its type contains no open set, no neighbourhood and no
measure, and by itself it would not reach `q:chain`'s *"for almost every `θ`"*,
which forgives a null set. The section after it removes that limitation —
`o31_endpointMarginal_not_identified_onBox` reruns every clause over three free
coordinates ranging in an explicit open box, and `o31BoxSet_volume` computes that
box's Lebesgue measure to be `1/500`, so the failure set is provably not null and
the printed quantifier no longer excuses it.

The scope is otherwise one instance: a two-node chain with the root intervened.
Nothing here settles the heuristic at larger `m`, at other `j`, or in the
straddling chamber, where the agenda's expectation is untouched.
-/

/-- The mate of `o31Witness` used below: the same transition table, with the root
moved to the margin endpoint. It is the model `o31_sameSide_root_not_identified`
constructs, written down so its marginal can be computed. -/
@[expose] public noncomputable def o31WitnessMate : O31ChainModel 1 :=
  ⟨1 / 10, o31Witness.transition⟩

/-- The mate is in the comparison class `q:chain` names. -/
public theorem o31WitnessMate_valid : o31WitnessMate.Valid (1 / 10) := by
  refine ⟨by norm_num, by norm_num,
    ⟨by norm_num [o31WitnessMate], by norm_num [o31WitnessMate]⟩, ?_, ?_⟩
  · intro i x
    fin_cases x <;>
      exact ⟨by norm_num [o31WitnessMate, o31Witness],
        by norm_num [o31WitnessMate, o31Witness]⟩
  · intro i; norm_num [o31WitnessMate, o31Witness]

/-- **The transfer map is shared.** The heuristic's positive half says a mixture
at `C_j` reveals this, and it is the same object in both models by construction. -/
public theorem o31WitnessMate_transfer :
    o31WitnessMate.transition = o31Witness.transition := rfl

/-- **The observational marginal of `C₁`, at every two-node model.**

`P(C₁ = 1) = (1 - r)·θ₀ + r·θ₁`: the root's own Bernoulli mixes the two transfer
columns. Stated parametrically so the box argument below can read it off the
coordinates rather than off literals. -/
public theorem nodeMass_zero_eq (M : O31ChainModel 1) :
    M.nodeMass 0 = (1 - M.root) * M.transition 0 0 + M.root * M.transition 0 1 := by
  rw [O31ChainModel.nodeMass, ← Equiv.sum_comp finFunctionFinEquiv.symm]
  simp [Fin.sum_univ_four, O31ChainModel.jointProb, O31ChainModel.nodeParameter,
    finFunctionFinEquiv,
    AISafetyAtlas.Conjectures.BinaryPair.interventionFactor,
    AISafetyAtlas.Conjectures.BinaryPair.bernoulli]
  rw [show (0 : Fin 2) = Fin.castSucc 0 from rfl, show (1 : Fin 2) = Fin.last 1 from rfl]
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  ring

/-- The witness puts mass `2/5` on the guessed endpoint. -/
public theorem o31Witness_nodeMass_zero : o31Witness.nodeMass 0 = 2 / 5 := by
  rw [nodeMass_zero_eq]
  norm_num [o31Witness]

/-- The mate puts mass `1/4` on it. -/
public theorem o31WitnessMate_nodeMass_zero : o31WitnessMate.nodeMass 0 = 1 / 4 := by
  rw [nodeMass_zero_eq]
  norm_num [o31WitnessMate, o31Witness]

/-- **Every mixture at the root leaves the two models sharing an optimum.** Both
transfer endpoints of both models are below the threshold `4/5`, so no mixture of
the four local maps carries either advantage across it. -/
public theorem o31Witness_behaviorEq_mate :
    O31BehaviorEqAt (4 / 5) (Fin.last 1) o31Witness o31WitnessMate := by
  intro mix
  have k1 : o31Witness.mixedTargetProbability (Fin.last 1) mix ≤ 4 / 5 :=
    mixedTargetProbability_le (fun f =>
      (targetProbability_lt (by norm_num [o31Witness]) (by norm_num [o31Witness])
        (by norm_num [o31Witness]) (by norm_num [o31Witness]) f).le)
  have k2 : o31WitnessMate.mixedTargetProbability (Fin.last 1) mix ≤ 4 / 5 :=
    mixedTargetProbability_le (fun f =>
      (targetProbability_lt (by norm_num [o31WitnessMate]) (by norm_num [o31WitnessMate])
        (by norm_num [o31WitnessMate, o31Witness])
        (by norm_num [o31WitnessMate, o31Witness]) f).le)
  exact Or.inr ⟨by linarith, by linarith⟩

/--
**A same-side collision at which the observational marginal of `C₁` is not
revealed.**

Two models of `𝕄(sk, λ)` on the same chain at margin `1/10`, with the **same**
transfer map, sharing an optimal policy under **every** real mixture of the four
local interventions at the root, whose observational marginals of the guessed
endpoint differ: `2/5` against `1/4`.

The agenda's heuristic for `q:chain` expects that marginal to be recoverable from
exactly this data. At this pair it is not. The utility is the gap pair
`(-4/5, 1/5)`, whose induced threshold `4/5` clears both transfer endpoints,
placing the pair in the same-side chamber.

**This is one concrete pair, and the type says so.** There is no open set, no
neighbourhood and no measure in this statement, so on its own it does not reach
`q:chain`'s *"for almost every `θ`"*, which would forgive an isolated failure.
`o31_endpointMarginal_not_identified_onBox` below is the same result over an
explicit open box and is what carries the quantifier.

This says nothing about the straddling chamber, about longer chains, or about
intervening anywhere but the root.
-/
public theorem o31_endpointMarginal_not_identified :
    o31Witness.Valid (1 / 10) ∧ o31WitnessMate.Valid (1 / 10) ∧
      o31WitnessMate.transition = o31Witness.transition ∧
      O31BehaviorEqAt (o31Threshold (-(4 / 5)) (1 / 5)) (Fin.last 1)
        o31Witness o31WitnessMate ∧
      o31WitnessMate.nodeMass 0 ≠ o31Witness.nodeMass 0 := by
  refine ⟨o31Witness_valid, o31WitnessMate_valid, o31WitnessMate_transfer, ?_, ?_⟩
  · rw [o31Witness_sameSide_threshold]; exact o31Witness_behaviorEq_mate
  · rw [o31WitnessMate_nodeMass_zero, o31Witness_nodeMass_zero]; norm_num

/-! ### The same failure on an open box, which is what the quantifier needs

`o31_endpointMarginal_not_identified` is one point, and `q:chain` asks *"for
almost every `θ`"*, so a single model is a null set and settles nothing about the
printed quantifier. This section replaces the literals by three free coordinates
ranging over an explicit open box and reruns the whole argument there.

The measure claim is proved here rather than asserted. `O31Box` read as a subset
of `ℝ³` is a product of three open intervals, and `o31BoxSet_volume` computes its
Lebesgue measure exactly: `1/500`. Every clause is then checked to survive the
widening — margin validity, the mate's validity, the chamber, behavioural
equality at every real mixture, and the marginals staying apart —
and `o31_endpointMarginal_not_identified_positiveMeasure` states the two halves
together, so no step of the argument is left to the reader.

The box is chosen around the witness of the previous section, which sits strictly
inside it, so the concrete pair is one member rather than a separate example.
-/

/-- The open box of two-node chains this section quantifies over: the root in
`(3/10, 1/2)`, the `0`-column in `(3/20, 1/4)`, the `1`-column in `(13/20, 3/4)`.

A product of three nonempty open intervals, hence a nonempty open subset of the
chain's `ℝ³` coordinate space. -/
@[expose] public def O31Box (r θ₀ θ₁ : ℝ) : Prop :=
  (3 / 10 < r ∧ r < 1 / 2) ∧ (3 / 20 < θ₀ ∧ θ₀ < 1 / 4) ∧ (13 / 20 < θ₁ ∧ θ₁ < 3 / 4)

/-- The chain model at a point of the box. -/
@[expose] public noncomputable def o31BoxModel (r θ₀ θ₁ : ℝ) : O31ChainModel 1 where
  root := r
  transition := fun _ x ↦ if x = 1 then θ₁ else θ₀

/-- Its mate: the same transfer columns, root moved to the margin endpoint. -/
@[expose] public noncomputable def o31BoxMate (r θ₀ θ₁ : ℝ) : O31ChainModel 1 :=
  ⟨1 / 10, (o31BoxModel r θ₀ θ₁).transition⟩

/-- The box is nonempty, and the earlier witness is one of its points. -/
public theorem o31Witness_mem_box : O31Box (2 / 5) (1 / 5) (7 / 10) := by
  refine ⟨⟨by norm_num, by norm_num⟩, ⟨by norm_num, by norm_num⟩,
    ⟨by norm_num, by norm_num⟩⟩

/-- And the box model at that point *is* the earlier witness, definitionally. -/
public theorem o31BoxModel_witness : o31BoxModel (2 / 5) (1 / 5) (7 / 10) = o31Witness := rfl


/-! #### The box has positive measure, proved rather than asserted

`O31Box` is a predicate on three reals. Read as a subset of `ℝ × ℝ × ℝ` it is a
product of three open intervals, and its Lebesgue measure is computed below
exactly: `1/500`. Nothing here is left to the reader — the step from "product of
open intervals" to "positive Lebesgue measure" is the one a prose argument would
wave through, so it is discharged by the kernel instead. -/

/-- The box as a subset of the chain's `ℝ³` coordinate space. -/
@[expose] public def o31BoxSet : Set (ℝ × ℝ × ℝ) := {p | O31Box p.1 p.2.1 p.2.2}

/-- It is literally a product of three open intervals. -/
public theorem o31BoxSet_eq :
    o31BoxSet = Set.Ioo (3 / 10 : ℝ) (1 / 2) ×ˢ
      (Set.Ioo (3 / 20 : ℝ) (1 / 4) ×ˢ Set.Ioo (13 / 20 : ℝ) (3 / 4)) := by
  ext p
  simp only [o31BoxSet, Set.mem_setOf_eq, O31Box, Set.mem_prod, Set.mem_Ioo]

/-- **Its Lebesgue measure is `1/500`.** The three edge lengths are `1/5`,
`1/10` and `1/10`. -/
public theorem o31BoxSet_volume :
    MeasureTheory.volume o31BoxSet = ENNReal.ofReal (1 / 500) := by
  rw [o31BoxSet_eq, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Measure.prod_prod, MeasureTheory.Measure.volume_eq_prod,
    MeasureTheory.Measure.prod_prod, Real.volume_Ioo, Real.volume_Ioo,
    Real.volume_Ioo, ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_mul (by norm_num)]
  norm_num

/-- **So the failure set is not null**, which is exactly what `q:chain`'s
*"for almost every `θ`"* requires before a counterexample counts. -/
public theorem o31BoxSet_volume_pos : 0 < MeasureTheory.volume o31BoxSet := by
  rw [o31BoxSet_volume, ENNReal.ofReal_pos]
  norm_num

/-- The box is inhabited, as a set. -/
public theorem o31BoxSet_nonempty : o31BoxSet.Nonempty :=
  ⟨(2 / 5, 1 / 5, 7 / 10), o31Witness_mem_box⟩

/-- Every point of the box is in the comparison class `q:chain` names. -/
public theorem o31BoxModel_valid {r θ₀ θ₁ : ℝ} (h : O31Box r θ₀ θ₁) :
    (o31BoxModel r θ₀ θ₁).Valid (1 / 10) := by
  obtain ⟨⟨hr0, hr1⟩, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩ := h
  refine ⟨by norm_num, by norm_num, ⟨by simp [o31BoxModel]; linarith,
    by simp [o31BoxModel]; linarith⟩, ?_, ?_⟩
  · intro i x
    fin_cases x <;>
      exact ⟨by simp [o31BoxModel]; linarith, by simp [o31BoxModel]; linarith⟩
  · intro i
    have : (o31BoxModel r θ₀ θ₁).transition i 1 - (o31BoxModel r θ₀ θ₁).transition i 0
        = θ₁ - θ₀ := by simp [o31BoxModel]
    rw [this, abs_of_pos (by linarith)]
    linarith

/-- So is the mate, whose root sits exactly on the margin endpoint — admissible,
since `def:margin`'s interval is closed. -/
public theorem o31BoxMate_valid {r θ₀ θ₁ : ℝ} (h : O31Box r θ₀ θ₁) :
    (o31BoxMate r θ₀ θ₁).Valid (1 / 10) := by
  obtain ⟨⟨hr0, hr1⟩, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩ := h
  refine ⟨by norm_num, by norm_num, ⟨by norm_num [o31BoxMate], by norm_num [o31BoxMate]⟩,
    ?_, ?_⟩
  · intro i x
    fin_cases x <;>
      exact ⟨by simp [o31BoxMate, o31BoxModel]; linarith,
        by simp [o31BoxMate, o31BoxModel]; linarith⟩
  · intro i
    have : (o31BoxMate r θ₀ θ₁).transition i 1 - (o31BoxMate r θ₀ θ₁).transition i 0
        = θ₁ - θ₀ := by simp [o31BoxMate, o31BoxModel]
    rw [this, abs_of_pos (by linarith)]
    linarith

/-- **The whole box lies in the same-side chamber** at threshold `4/5`: both
transfer endpoints stay below it, since the `1`-column is capped at `3/4`. -/
public theorem o31BoxModel_sameSide {r θ₀ θ₁ : ℝ} (h : O31Box r θ₀ θ₁) :
    O31SameSideChamber (4 / 5) (Fin.last 1) (o31BoxModel r θ₀ θ₁) := by
  obtain ⟨_, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩ := h
  rw [O31SameSideChamber, targetProbability_const_zero, targetProbability_const_one]
  have e0 : (o31BoxModel r θ₀ θ₁).transition 0 0 = θ₀ := by simp [o31BoxModel]
  have e1 : (o31BoxModel r θ₀ θ₁).transition 0 1 = θ₁ := by simp [o31BoxModel]
  rw [e0, e1]
  nlinarith

/-- **Every point of the box shares an optimum with its mate, under every real
mixture.** Both models' four transfer endpoints stay strictly below `4/5`, so no
mixture carries either across the threshold. -/
public theorem o31BoxModel_behaviorEq {r θ₀ θ₁ : ℝ} (h : O31Box r θ₀ θ₁) :
    O31BehaviorEqAt (4 / 5) (Fin.last 1) (o31BoxModel r θ₀ θ₁) (o31BoxMate r θ₀ θ₁) := by
  obtain ⟨⟨hr0, hr1⟩, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩ := h
  intro mix
  have k1 : (o31BoxModel r θ₀ θ₁).mixedTargetProbability (Fin.last 1) mix ≤ 4 / 5 :=
    mixedTargetProbability_le (fun f =>
      (targetProbability_lt (by simp [o31BoxModel]; linarith)
        (by simp [o31BoxModel]; linarith)
        (by simp [o31BoxModel]; linarith) (by simp [o31BoxModel]; linarith) f).le)
  have k2 : (o31BoxMate r θ₀ θ₁).mixedTargetProbability (Fin.last 1) mix ≤ 4 / 5 :=
    mixedTargetProbability_le (fun f =>
      (targetProbability_lt (by norm_num [o31BoxMate])
        (by norm_num [o31BoxMate])
        (by simp [o31BoxMate, o31BoxModel]; linarith)
        (by simp [o31BoxMate, o31BoxModel]; linarith) f).le)
  exact Or.inr ⟨by linarith, by linarith⟩

/-- **And the two marginals stay apart across the whole box.** The gap is
`(r - 1/10)·(θ₁ - θ₀)`, and the box keeps both factors strictly positive. -/
public theorem o31BoxMate_nodeMass_ne {r θ₀ θ₁ : ℝ} (h : O31Box r θ₀ θ₁) :
    (o31BoxMate r θ₀ θ₁).nodeMass 0 ≠ (o31BoxModel r θ₀ θ₁).nodeMass 0 := by
  obtain ⟨⟨hr0, hr1⟩, ⟨ha0, ha1⟩, ⟨hb0, hb1⟩⟩ := h
  rw [nodeMass_zero_eq, nodeMass_zero_eq]
  have e0 : (o31BoxModel r θ₀ θ₁).transition 0 0 = θ₀ := by simp [o31BoxModel]
  have e1 : (o31BoxModel r θ₀ θ₁).transition 0 1 = θ₁ := by simp [o31BoxModel]
  have m0 : (o31BoxMate r θ₀ θ₁).transition 0 0 = θ₀ := by simp [o31BoxMate, o31BoxModel]
  have m1 : (o31BoxMate r θ₀ θ₁).transition 0 1 = θ₁ := by simp [o31BoxMate, o31BoxModel]
  have mr : (o31BoxMate r θ₀ θ₁).root = 1 / 10 := rfl
  have hr : (o31BoxModel r θ₀ θ₁).root = r := rfl
  rw [e0, e1, m0, m1, mr, hr]
  nlinarith

/--
**The heuristic fails on a nonempty open box of chain parameters, not at a
point.**

For *every* `(r, θ₀, θ₁)` in `O31Box` — a product of three open intervals, hence
a nonempty open subset of the chain's `ℝ³` coordinate space and of positive
Lebesgue measure — the model at that point and its mate are both in
`𝕄(sk, 1/10)`, carry the **same** transfer map, share an optimal policy under
**every** real mixture of the four local interventions at the root, and have
**different** observational marginals of the guessed endpoint.

`q:chain`'s heuristic says that data should reveal the marginal of `C₁`. Across
this box it does not. Because the failure set contains a nonempty open box, the
question's *"for almost every `θ`"* does not forgive it: this is the statement
`o31_endpointMarginal_not_identified` could not make, and it is now checked rather
than argued by continuity in prose.

Still one instance in the other coordinates: two nodes, root intervened,
same-side chamber. Longer chains, other `j`, and the straddling chamber are
untouched.
-/
public theorem o31_endpointMarginal_not_identified_onBox {r θ₀ θ₁ : ℝ}
    (h : O31Box r θ₀ θ₁) :
    (o31BoxModel r θ₀ θ₁).Valid (1 / 10) ∧ (o31BoxMate r θ₀ θ₁).Valid (1 / 10) ∧
      (o31BoxMate r θ₀ θ₁).transition = (o31BoxModel r θ₀ θ₁).transition ∧
      O31BehaviorEqAt (o31Threshold (-(4 / 5)) (1 / 5)) (Fin.last 1)
        (o31BoxModel r θ₀ θ₁) (o31BoxMate r θ₀ θ₁) ∧
      (o31BoxMate r θ₀ θ₁).nodeMass 0 ≠ (o31BoxModel r θ₀ θ₁).nodeMass 0 := by
  refine ⟨o31BoxModel_valid h, o31BoxMate_valid h, rfl, ?_, o31BoxMate_nodeMass_ne h⟩
  rw [o31Witness_sameSide_threshold]
  exact o31BoxModel_behaviorEq h

/-- The on-box counterexample transported end to end into the printed margin
class and the causal-kernel calculation of restricted behavior. -/
public theorem o31_endpointMarginal_not_identified_kernel_onBox {r θ₀ θ₁ : ℝ}
    (h : O31Box r θ₀ θ₁) :
    ∃ hM : (o31BoxModel r θ₀ θ₁).Valid (1 / 10),
      ∃ hM' : (o31BoxMate r θ₀ θ₁).Valid (1 / 10),
        (o31Skeleton (n := 1) o31Witness_sameSide_gap).MarginClass
            ((o31BoxModel r θ₀ θ₁).toModel
              ((o31BoxModel r θ₀ θ₁).inUnitBox_of_valid hM)) (1 / 10) ∧
        (o31Skeleton (n := 1) o31Witness_sameSide_gap).MarginClass
            ((o31BoxMate r θ₀ θ₁).toModel
              ((o31BoxMate r θ₀ θ₁).inUnitBox_of_valid hM')) (1 / 10) ∧
        O31UtilityKernelBehaviorEq o31Witness_sameSide_gap (Fin.last 1)
          (o31BoxModel r θ₀ θ₁) (o31BoxMate r θ₀ θ₁)
          ((o31BoxModel r θ₀ θ₁).inUnitBox_of_valid hM)
          ((o31BoxMate r θ₀ θ₁).inUnitBox_of_valid hM') ∧
        (o31BoxMate r θ₀ θ₁).nodeMass 0 ≠ (o31BoxModel r θ₀ θ₁).nodeMass 0 := by
  let hM := o31BoxModel_valid h
  let hM' := o31BoxMate_valid h
  refine ⟨hM, hM', ?_, ?_, ?_, o31BoxMate_nodeMass_ne h⟩
  · exact O31ChainModel.toModel_marginClass o31Witness_sameSide_gap hM
  · exact O31ChainModel.toModel_marginClass o31Witness_sameSide_gap hM'
  · apply (o31BehaviorEqAt_threshold_iff_utilityKernel
      o31Witness_sameSide_gap _ _ _ _ _).mp
    exact (o31_endpointMarginal_not_identified_onBox h).2.2.2.1

/--
**The complete statement, with nothing left to the reader.**

`q:chain`'s heuristic fails on an explicit set of chain parameters of Lebesgue
measure `1/500 > 0`. That set is the box below, which is *contained in* the
failure locus rather than equal to it; nothing here computes the measure of the
locus itself. At *every* point of the box the model and its mate are both
in `𝕄(sk, 1/10)`, share the transfer map, share an optimal policy under every
real mixture of the four local interventions at the root, and disagree on the
observational marginal of the guessed endpoint.

Every link used here is machine-checked: the measure by `o31BoxSet_volume`, the
chart behavior by `o31_endpointMarginal_not_identified_onBox`, and membership
in the printed margin class together with causal-kernel behavior by
`o31_endpointMarginal_not_identified_kernel_onBox`. `q:chain` asks its question
*"for almost every `θ`"*, and a set of measure `1/500` is not a null set, so the
printed quantifier does not excuse this.

The remaining scope is honest and unchanged: two nodes, root intervened,
same-side chamber. Longer chains, other `j`, and the straddling chamber are
untouched.
-/
public theorem o31_endpointMarginal_not_identified_positiveMeasure :
    0 < MeasureTheory.volume o31BoxSet ∧
      ∀ p ∈ o31BoxSet,
        ((o31BoxModel p.1 p.2.1 p.2.2).Valid (1 / 10) ∧
            (o31BoxMate p.1 p.2.1 p.2.2).Valid (1 / 10) ∧
            (o31BoxMate p.1 p.2.1 p.2.2).transition
              = (o31BoxModel p.1 p.2.1 p.2.2).transition ∧
            O31BehaviorEqAt (o31Threshold (-(4 / 5)) (1 / 5)) (Fin.last 1)
              (o31BoxModel p.1 p.2.1 p.2.2) (o31BoxMate p.1 p.2.1 p.2.2) ∧
            (o31BoxMate p.1 p.2.1 p.2.2).nodeMass 0
              ≠ (o31BoxModel p.1 p.2.1 p.2.2).nodeMass 0) ∧
          ∃ hM : (o31BoxModel p.1 p.2.1 p.2.2).Valid (1 / 10),
            ∃ hM' : (o31BoxMate p.1 p.2.1 p.2.2).Valid (1 / 10),
              (o31Skeleton (n := 1) o31Witness_sameSide_gap).MarginClass
                  ((o31BoxModel p.1 p.2.1 p.2.2).toModel
                    ((o31BoxModel p.1 p.2.1 p.2.2).inUnitBox_of_valid hM)) (1 / 10) ∧
              (o31Skeleton (n := 1) o31Witness_sameSide_gap).MarginClass
                  ((o31BoxMate p.1 p.2.1 p.2.2).toModel
                    ((o31BoxMate p.1 p.2.1 p.2.2).inUnitBox_of_valid hM')) (1 / 10) ∧
              O31UtilityKernelBehaviorEq o31Witness_sameSide_gap (Fin.last 1)
                (o31BoxModel p.1 p.2.1 p.2.2) (o31BoxMate p.1 p.2.1 p.2.2)
                ((o31BoxModel p.1 p.2.1 p.2.2).inUnitBox_of_valid hM)
                ((o31BoxMate p.1 p.2.1 p.2.2).inUnitBox_of_valid hM') ∧
              (o31BoxMate p.1 p.2.1 p.2.2).nodeMass 0
                ≠ (o31BoxModel p.1 p.2.1 p.2.2).nodeMass 0 :=
  ⟨o31BoxSet_volume_pos, fun _ hp ↦
    ⟨o31_endpointMarginal_not_identified_onBox hp,
      o31_endpointMarginal_not_identified_kernel_onBox hp⟩⟩


end AISafetyAtlas.Examples.Conjectures.MAIS
