module

public import AISafetyAtlas.SingularLearning.LocalPair
public import Mathlib.MeasureTheory.Function.Jacobian

/-!
# The Jacobian sandwich: a `C¹` injection moves volume by a bounded factor

Print's **Lemma 6.4(i)** says the local pair is invariant under an analytic diffeomorphism.
`PairTransfer.lean` proves 6.2 (comparability) and 6.4(ii) (free coordinates); this module is the
measure-theoretic heart of 6.4(i), separated out because it is a statement about `C¹` injections
and nothing else — no germ, no sublevel set, no pair.

## Why the O70 chain needs it

Theorem 5.1 compares `2K(w)` with `‖u‖² + ‖Y₀S_Z‖²_F` evaluated at `Ψ(w)`, a germ on the
*parameter* space. The residual-germ theorem gives the pair of that germ at the *origin of the
chart space*. `Ψ` is not affine — it contains `A₁₁⁻¹` — so passing between the two is a genuine
nonlinear change of variables, and only a Jacobian argument recovers the pair.

## What is proved

For `φ` injective and differentiable on a measurable `s`, with `|det Dφ|` bounded on `s`,

    m · vol(s) ≤ vol(φ '' s) ≤ M · vol(s) .

Mathlib's `lintegral_abs_det_fderiv_eq_addHaar_image` supplies the equality
`vol(φ '' s) = ∫⁻_s |det Dφ|`; the two bounds are then monotonicity of the integral against a
constant. Nothing here is specific to the elimination chart, and nothing here is asymptotic.

## What is not proved here

The rest of Lemma 6.4(i): that a `C¹` diffeomorphism carries balls to comparable balls, so that
the sublevel volumes at the two base points can be compared at *some* radius. That is a
Lipschitz estimate on `φ` and on `φ⁻¹`, and it is the other half of the lemma.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Set

variable {D : ℕ}

/-- **The upper half of the sandwich.** A `C¹` injection with `|det Dφ| ≤ M` cannot expand
volume by more than `M`. -/
public theorem measure_image_le_of_abs_det_le
    {φ : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)}
    {φ' : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D)}
    {s : Set (EuclideanSpace ℝ (Fin D))} (hs : MeasurableSet s)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) (hinj : Set.InjOn φ s)
    {M : ℝ} (hM : ∀ x ∈ s, |(φ' x).det| ≤ M) :
    volume (φ '' s) ≤ ENNReal.ofReal M * volume s := by
  rw [← MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image volume hs hφ' hinj]
  calc ∫⁻ x in s, ENNReal.ofReal |(φ' x).det|
      ≤ ∫⁻ _x in s, ENNReal.ofReal M :=
        MeasureTheory.setLIntegral_mono' hs fun x hx => ENNReal.ofReal_le_ofReal (hM x hx)
    _ = ENNReal.ofReal M * volume s := by rw [MeasureTheory.setLIntegral_const]

/-- **The lower half.** A `C¹` injection with `m ≤ |det Dφ|` cannot contract volume by more
than `m`. -/
public theorem le_measure_image_of_le_abs_det
    {φ : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)}
    {φ' : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D)}
    {s : Set (EuclideanSpace ℝ (Fin D))} (hs : MeasurableSet s)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) (hinj : Set.InjOn φ s)
    {m : ℝ} (hm : ∀ x ∈ s, m ≤ |(φ' x).det|) :
    ENNReal.ofReal m * volume s ≤ volume (φ '' s) := by
  rw [← MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image volume hs hφ' hinj]
  calc ENNReal.ofReal m * volume s
      = ∫⁻ _x in s, ENNReal.ofReal m := by rw [MeasureTheory.setLIntegral_const]
    _ ≤ ∫⁻ x in s, ENNReal.ofReal |(φ' x).det| :=
        MeasureTheory.setLIntegral_mono' hs fun x hx => ENNReal.ofReal_le_ofReal (hm x hx)

/-- The two halves together, in real form. The finiteness hypothesis is what lets the bound be
read in `ℝ` rather than in `ℝ≥0∞`; a sublevel set inside a ball satisfies it. -/
public theorem measureReal_image_sandwich
    {φ : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)}
    {φ' : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D) →L[ℝ] EuclideanSpace ℝ (Fin D)}
    {s : Set (EuclideanSpace ℝ (Fin D))} (hs : MeasurableSet s) (hfin : volume s ≠ ⊤)
    (hφ' : ∀ x ∈ s, HasFDerivWithinAt φ (φ' x) s x) (hinj : Set.InjOn φ s)
    {m M : ℝ} (hm0 : 0 ≤ m) (hm : ∀ x ∈ s, m ≤ |(φ' x).det|) (hM : ∀ x ∈ s, |(φ' x).det| ≤ M) :
    m * (volume s).toReal ≤ (volume (φ '' s)).toReal ∧
      (volume (φ '' s)).toReal ≤ M * (volume s).toReal := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp
  have hM0 : (0:ℝ) ≤ M := le_trans (abs_nonneg _) (hM x₀ hx₀)
  have hupper := measure_image_le_of_abs_det_le hs hφ' hinj hM
  have hlower := le_measure_image_of_le_abs_det hs hφ' hinj hm
  have hfin' : volume (φ '' s) ≠ ⊤ :=
    ne_top_of_le_ne_top (by
      refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hupper
  constructor
  · have h := ENNReal.toReal_mono hfin' hlower
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hm0] at h
  · have h := ENNReal.toReal_mono
      (by exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hupper
    rwa [ENNReal.toReal_mul, ENNReal.toReal_ofReal hM0] at h

end AISafetyAtlas.SingularLearning
