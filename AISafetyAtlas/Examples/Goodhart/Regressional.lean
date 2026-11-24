module

public import AISafetyAtlas.Goodhart.Regressional

/-!
# A worked model for Regressional Goodhart

The library statement quantifies over probability measures. This file inhabits
its hypotheses at the smallest pair on which nothing degenerates: the goal and
the noise are both fair coin flips on `{0, 1}`, and both sides of the inequality
are exact rationals.

With `twoPoint` for both the goal law and the noise law, and the threshold at
`1/2`, the four states `(0,0), (0,1), (1,0), (1,1)` carry mass `1/4` each and
three of them are selected. Then

* the selected mass is `3/4`;
* the unconditional expected gap is `1/2`, so the left-hand side is `3/8`;
* the selected gap mass is `1/2`, so the conditional expected gap is `2/3`.

`3/8 < 1/2` is the inequality, strictly, and `2/3 > 1/2` is what it says about
the conditional expectation: selecting on the proxy raised the expected gap.

The cut set that makes it strict is `{0}`, not everything. At goal value `1`
the state is selected whatever the noise does, so no noise is filtered there;
the strictness comes from the goal values where the threshold actually bites.
That is why `gap_selection_gt` asks for a set of goal values on which the
selected noise mass is a proper fraction rather than asking only that the noise
be non-degenerate.
-/

namespace AISafetyAtlas.Examples.Goodhart.Regressional

open MeasureTheory Set AISafetyAtlas.Goodhart
open scoped NNReal ENNReal

/-- Fair two-point law on `{0, 1}`. -/
@[expose] public noncomputable def twoPoint : Measure ℝ :=
  (2⁻¹ : ℝ≥0∞) • (Measure.dirac 0 + Measure.dirac 1)

public instance : IsProbabilityMeasure twoPoint := by
  constructor
  simp only [twoPoint, Measure.smul_apply, Measure.coe_add, Pi.add_apply, measure_univ,
    smul_eq_mul]
  rw [show ((1:ℝ≥0∞) + 1) = 2 by norm_num]
  exact ENNReal.inv_mul_cancel (by norm_num) (by norm_num)

/-- Every real function is integrable against a two-point law. -/
private theorem integrable_twoPoint (f : ℝ → ℝ) : Integrable f twoPoint := by
  have h0 : Integrable f (Measure.dirac (0:ℝ)) := integrable_dirac (by finiteness)
  have h1 : Integrable f (Measure.dirac (1:ℝ)) := integrable_dirac (by finiteness)
  exact (integrable_add_measure.2 ⟨h0, h1⟩).smul_measure (by simp)

/-- Integration against `twoPoint` is the average of the two values. -/
private theorem integral_twoPoint (f : ℝ → ℝ) :
    ∫ x, f x ∂twoPoint = (f 0 + f 1) / 2 := by
  have h0 : Integrable f (Measure.dirac (0:ℝ)) := integrable_dirac (by finiteness)
  have h1 : Integrable f (Measure.dirac (1:ℝ)) := integrable_dirac (by finiteness)
  rw [twoPoint, integral_smul_measure, integral_add_measure h0 h1,
    integral_dirac, integral_dirac]
  simp
  ring

/-- The mass `twoPoint` gives a measurable set counts which of `0` and `1` it holds. -/
private theorem twoPoint_real (s : Set ℝ) (hs : MeasurableSet s) :
    twoPoint.real s
      = (s.indicator (fun _ => (1:ℝ)) 0 + s.indicator (fun _ => (1:ℝ)) 1) / 2 := by
  have h : twoPoint.real s = ∫ x, s.indicator (fun _ => (1:ℝ)) x ∂twoPoint := by
    rw [integral_indicator hs, setIntegral_const]
    simp
  rw [h, integral_twoPoint]

/-- The tail integral of the identity against `twoPoint`. -/
private theorem integral_twoPoint_Ioi (t : ℝ) :
    (∫ n in Ioi t, n ∂twoPoint) = (if (1:ℝ) ∈ Ioi t then 1 else 0) / 2 := by
  rw [← integral_indicator measurableSet_Ioi, integral_twoPoint]
  simp [Set.indicator_apply]

/-- The unconditional expected gap is `1/2`. -/
private theorem integral_id_twoPoint : ∫ x, x ∂twoPoint = 2⁻¹ := by
  rw [integral_twoPoint]
  norm_num

/-- Goal value `0` carries positive mass: the cut set of `gap_selection_gt` is inhabited. -/
private theorem twoPoint_singleton_zero : twoPoint {(0:ℝ)} ≠ 0 := by
  simp [twoPoint]

/-- Three of the four states are selected. -/
public theorem measureReal_selected_twoPoint :
    (twoPoint.prod twoPoint).real (selected (2⁻¹ : ℝ)) = 3/4 := by
  rw [measureReal_selected twoPoint twoPoint (2⁻¹ : ℝ), integral_twoPoint,
    twoPoint_real _ measurableSet_Ioi, twoPoint_real _ measurableSet_Ioi]
  norm_num [Set.indicator_apply]

/-- The gap mass carried by the selected states is `1/2`. -/
public theorem integral_gap_selected_twoPoint :
    (∫ p in selected (2⁻¹ : ℝ), gap p ∂(twoPoint.prod twoPoint)) = 2⁻¹ := by
  rw [integral_gap_selected twoPoint twoPoint (integrable_twoPoint _) (2⁻¹ : ℝ),
    integral_twoPoint, integral_twoPoint_Ioi, integral_twoPoint_Ioi]
  norm_num

/-- **The hypotheses of the strict statement are satisfiable.** The witness cuts
at goal value `0`, where the selected noise mass is `1/2`. -/
public theorem gap_selection_twoPoint :
    (∫ x, x ∂twoPoint) * (twoPoint.prod twoPoint).real (selected (2⁻¹ : ℝ))
      < ∫ p in selected (2⁻¹ : ℝ), gap p ∂(twoPoint.prod twoPoint) := by
  refine gap_selection_gt twoPoint twoPoint (integrable_twoPoint _) (2⁻¹ : ℝ)
    (A := {(0:ℝ)}) twoPoint_singleton_zero ?_
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  rw [twoPoint_real _ measurableSet_Ioi]
  norm_num [Set.indicator_apply]

/-- **Both sides are exact rationals**, so the inequality is `3/8 < 1/2` and the
conditional expected gap is `(1/2)/(3/4) = 2/3` against an unconditional `1/2`. -/
public theorem gap_selection_twoPoint_values :
    (∫ x, x ∂twoPoint) * (twoPoint.prod twoPoint).real (selected (2⁻¹ : ℝ)) = 3/8
      ∧ (∫ p in selected (2⁻¹ : ℝ), gap p ∂(twoPoint.prod twoPoint)) = 1/2 := by
  refine ⟨?_, ?_⟩
  · rw [integral_id_twoPoint, measureReal_selected_twoPoint]
    norm_num
  · rw [integral_gap_selected_twoPoint]
    norm_num

/-- **Print's Gaussian instance is inhabited too**, and there the strictness needs
no cut set: at any variance `v ≠ 0` every threshold splits the noise. -/
public theorem gap_selection_standard_normal (c : ℝ) :
    (0:ℝ) * (twoPoint.prod (ProbabilityTheory.gaussianReal 0 1)).real (selected c)
      < ∫ p in selected c, gap p ∂(twoPoint.prod (ProbabilityTheory.gaussianReal 0 1)) :=
  gap_selection_gaussianReal_gt twoPoint 0 (v := 1) (by norm_num) c

/-- **The non-strict bound, at the two-point noise.** The strict version above
needs the noise to be split by every threshold; the general inequality does not,
and holds at the discrete noise where strictness can fail. Having both at the
same selection is what shows the strictness hypothesis is doing work rather than
tidying the statement. -/
public theorem gap_selection_ge_twoPoint (c : ℝ) :
    (∫ x, x ∂twoPoint) * (twoPoint.prod twoPoint).real (selected c)
      ≤ ∫ p in selected c, gap p ∂(twoPoint.prod twoPoint) :=
  gap_selection_ge twoPoint twoPoint (integrable_twoPoint _) c

/-! ## The goal component: selection raises the goal

The carrier is symmetric, so the two-point model witnesses the goal statements
at the same threshold `1/2`: the cut is at noise value `0`, where the selected
goal mass is `1/2`. -/

/-- **The goal mirror, strictly, at the two-point model.** -/
public theorem goal_selection_twoPoint :
    (∫ x, x ∂twoPoint) * (twoPoint.prod twoPoint).real (selected (2⁻¹ : ℝ))
      < ∫ p in selected (2⁻¹ : ℝ), goal p ∂(twoPoint.prod twoPoint) := by
  refine goal_selection_gt twoPoint twoPoint (integrable_twoPoint _) (2⁻¹ : ℝ)
    (B := {(0:ℝ)}) twoPoint_singleton_zero ?_
  intro n hn
  rw [Set.mem_singleton_iff] at hn
  subst hn
  rw [twoPoint_real _ measurableSet_Ioi]
  norm_num [Set.indicator_apply]

/-- The non-strict goal bound, at the two-point model and every threshold. -/
public theorem goal_selection_ge_twoPoint (c : ℝ) :
    (∫ x, x ∂twoPoint) * (twoPoint.prod twoPoint).real (selected c)
      ≤ ∫ p in selected c, goal p ∂(twoPoint.prod twoPoint) :=
  goal_selection_ge twoPoint twoPoint (integrable_twoPoint _) c

/-- **Print's "higher than otherwise", strictly, at the two-point model.** -/
public theorem goal_selected_compl_twoPoint :
    (∫ p in (selected (2⁻¹ : ℝ))ᶜ, goal p ∂(twoPoint.prod twoPoint)) *
        (twoPoint.prod twoPoint).real (selected (2⁻¹ : ℝ))
      < (∫ p in selected (2⁻¹ : ℝ), goal p ∂(twoPoint.prod twoPoint)) *
        (twoPoint.prod twoPoint).real (selected (2⁻¹ : ℝ))ᶜ := by
  refine goal_selected_compl_lt twoPoint twoPoint (integrable_twoPoint _) (2⁻¹ : ℝ)
    (B := {(0:ℝ)}) twoPoint_singleton_zero ?_
  intro n hn
  rw [Set.mem_singleton_iff] at hn
  subst hn
  rw [twoPoint_real _ measurableSet_Ioi]
  norm_num [Set.indicator_apply]

/-- The non-strict "than otherwise" form, at every threshold. -/
public theorem goal_selected_compl_le_twoPoint (c : ℝ) :
    (∫ p in (selected c)ᶜ, goal p ∂(twoPoint.prod twoPoint)) *
        (twoPoint.prod twoPoint).real (selected c)
      ≤ (∫ p in selected c, goal p ∂(twoPoint.prod twoPoint)) *
        (twoPoint.prod twoPoint).real (selected c)ᶜ :=
  goal_selected_compl_le twoPoint twoPoint (integrable_twoPoint _) c

/-- The two-point law is not a point mass: it gives `{0}` mass `1/2`, a Dirac
measure gives every singleton mass `0` or `1`. -/
public theorem twoPoint_ne_dirac (a : ℝ) : twoPoint ≠ Measure.dirac a := by
  intro h
  have h0 : twoPoint {(0:ℝ)} = 2⁻¹ := by
    simp [twoPoint]
  rw [h] at h0
  by_cases ha : a ∈ ({(0:ℝ)} : Set ℝ)
  · rw [Measure.dirac_apply_of_mem ha, eq_comm, ENNReal.inv_eq_one] at h0
    norm_num at h0
  · rw [Measure.dirac_apply' _ (measurableSet_singleton _), Set.indicator_of_notMem ha] at h0
    exact absurd h0.symm (by norm_num)

/-- **Print's "higher than otherwise", strictly, at a non-degenerate goal and print's
Gaussian noise**, at every threshold (Manheim and Garrabrant, PDF p. 2: *"for large
values of `c` the values of `G` when `M > c` is expected to be higher than
otherwise"*, with `M = G + normal(μ, σ²)` of equation (1)). The goal is the fair
coin on `{0, 1}`, which is not a point mass, and the noise is standard normal; no
cut set is supplied by hand. -/
public theorem goal_selected_compl_twoPoint_standard_normal (c : ℝ) :
    (∫ p in (selected c)ᶜ, goal p ∂(twoPoint.prod (ProbabilityTheory.gaussianReal 0 1))) *
        (twoPoint.prod (ProbabilityTheory.gaussianReal 0 1)).real (selected c)
      < (∫ p in selected c, goal p ∂(twoPoint.prod (ProbabilityTheory.gaussianReal 0 1))) *
        (twoPoint.prod (ProbabilityTheory.gaussianReal 0 1)).real (selected c)ᶜ :=
  AISafetyAtlas.Goodhart.goal_selected_compl_gaussianReal_lt twoPoint
    (integrable_twoPoint _) twoPoint_ne_dirac 0 (v := 1) (by norm_num) c

/-- **The goal mirror at a standard normal goal**, with the two-point noise. -/
public theorem goal_selection_standard_normal (c : ℝ) :
    (0:ℝ) * ((ProbabilityTheory.gaussianReal 0 1).prod twoPoint).real (selected c)
      < ∫ p in selected c, goal p ∂((ProbabilityTheory.gaussianReal 0 1).prod twoPoint) :=
  goal_selection_gaussianReal_gt twoPoint 0 (v := 1) (by norm_num) c

/-! ## The non-strict selection event, where the atom matters

At threshold `1` the proxy of the two-point model has an atom: the states
`(0,1)` and `(1,0)` have proxy exactly `1`. Print's setup inequality `M ≥ c`
selects three states and the strict one selects one, so the two events differ
in mass; the gap inequality holds strictly at both. -/

/-- At threshold `1`, the non-strict event carries mass `3/4`. -/
public theorem measureReal_selectedGe_twoPoint :
    (twoPoint.prod twoPoint).real (selectedGe 1) = 3/4 := by
  rw [measureReal_selectedGe twoPoint twoPoint 1, integral_twoPoint,
    twoPoint_real _ measurableSet_Ici, twoPoint_real _ measurableSet_Ici]
  norm_num [Set.indicator_apply]

/-- …while the strict event carries mass `1/4`: the atom at the threshold. -/
public theorem measureReal_selected_one_twoPoint :
    (twoPoint.prod twoPoint).real (selected 1) = 1/4 := by
  rw [measureReal_selected twoPoint twoPoint 1, integral_twoPoint,
    twoPoint_real _ measurableSet_Ioi, twoPoint_real _ measurableSet_Ioi]
  norm_num [Set.indicator_apply]

/-- **The strict gap inequality at print's setup event**, at threshold `1`, cut
at goal value `0`. -/
public theorem gap_selectionGe_twoPoint :
    (∫ x, x ∂twoPoint) * (twoPoint.prod twoPoint).real (selectedGe 1)
      < ∫ p in selectedGe 1, gap p ∂(twoPoint.prod twoPoint) := by
  refine gap_selectionGe_gt twoPoint twoPoint (integrable_twoPoint _) 1
    (A := {(0:ℝ)}) twoPoint_singleton_zero ?_
  intro g hg
  rw [Set.mem_singleton_iff] at hg
  subst hg
  rw [twoPoint_real _ measurableSet_Ici]
  norm_num [Set.indicator_apply]

/-- The non-strict gap bound at print's setup event, at every threshold. -/
public theorem gap_selectionGe_ge_twoPoint (c : ℝ) :
    (∫ x, x ∂twoPoint) * (twoPoint.prod twoPoint).real (selectedGe c)
      ≤ ∫ p in selectedGe c, gap p ∂(twoPoint.prod twoPoint) :=
  gap_selectionGe_ge twoPoint twoPoint (integrable_twoPoint _) c

/-- The gap mass on print's setup event, reduced, at the two-point model. -/
example : (∫ p in selectedGe 1, gap p ∂(twoPoint.prod twoPoint)) =
    ∫ g, (∫ n in Ici (1 - g), n ∂twoPoint) ∂twoPoint :=
  integral_gap_selectedGe twoPoint twoPoint (integrable_twoPoint _) 1

/-- **Print's Gaussian instance at print's setup event.** -/
public theorem gap_selectionGe_standard_normal (c : ℝ) :
    (0:ℝ) * (twoPoint.prod (ProbabilityTheory.gaussianReal 0 1)).real (selectedGe c)
      < ∫ p in selectedGe c, gap p ∂(twoPoint.prod (ProbabilityTheory.gaussianReal 0 1)) :=
  gap_selectionGe_gaussianReal_gt twoPoint 0 (v := 1) (by norm_num) c

/-- The closed-ray core, strictly, at the two-point law and threshold `1`. -/
example : (∫ x, x ∂twoPoint) * twoPoint.real (Ici 1) < ∫ x in Ici 1, x ∂twoPoint := by
  refine tail_integral_gt_Ici twoPoint (integrable_twoPoint _) 1 ?_ ?_ <;>
    · rw [twoPoint_real _ measurableSet_Ici]; norm_num [Set.indicator_apply]

/-- **A two-state system outside the carrier**, read into it: states `Bool`,
goal `0` at `false` and `1` at `true`, proxy `1` at both, threshold `1`. Print's
region `A = {s | M s ≥ 1}` is every state, and it is the pullback of
`selectedGe 1`; the difference `M − G` is `1` at `false` and `0` at `true`. -/
public theorem twoState_selectedAt :
    (fun s : Bool => ((fun b : Bool => if b then (1 : ℝ) else 0) s,
        (fun _ : Bool => (1 : ℝ)) s - (fun b : Bool => if b then (1 : ℝ) else 0) s)) ⁻¹'
        selectedGe 1 = Set.univ := by
  rw [preimage_selectedGe]
  ext s
  simp

/-- The carrier's gap is print's difference at that system. -/
example : gap ∘ (fun s : Bool => ((fun b : Bool => if b then (1 : ℝ) else 0) s,
    (fun _ : Bool => (1 : ℝ)) s - (fun b : Bool => if b then (1 : ℝ) else 0) s)) =
      (fun _ : Bool => (1 : ℝ)) - fun b : Bool => if b then (1 : ℝ) else 0 :=
  (goalGap_comp Bool _ _).2.1

end AISafetyAtlas.Examples.Goodhart.Regressional
