module

public import AISafetyAtlas.SingularLearning.CriticalFiber

/-!
# A worked model for the critical fibre and the splitting along it

`AISafetyAtlas.SingularLearning.CriticalFiber` is a chain of existence statements under
hypotheses, and the hypotheses of the last one — smoothness, a critical point at the origin, and
an invertible `W`-block Hessian — could in principle be jointly unsatisfiable in a way no other
check in this repository would notice. They are witnessed here at `W = V = ℝ` on

    f (η, ζ) = η ^ 2 - ζ ^ 4,

for which the origin is critical, the `W`-block Hessian is doubling and hence invertible, and the
germ left on the fibre is genuinely quartic.

The model is chosen so that the germ is **not constant**. That is the difference between this
splitting and a strict Morse–Bott one, and a witness whose germ vanished would not test it. The
example does not merely assert non-constancy: it derives it. The conclusion of
`exists_gromoll_meyer_splitting` returns the critical fibre `c` together with the statement that
`∂_W f (c ζ, ζ) = 0`; for this `f` that reads `2 * c ζ = 0`, so the fibre is forced to be the zero
section, `g ζ = f (0, ζ) - f 0 = -ζ ^ 4`, and any point of the produced neighbourhood with nonzero
second coordinate separates `g` from `g 0`. Such a point exists because the neighbourhood is open
and contains the origin.

All derivative computations go through one generic pair of continuous linear functionals: for
`c d : X →L[ℝ] ℝ`, the function `y ↦ c y * c y - d y ^ 4` has first derivative
`(2 * c x) • c - (4 * d x ^ 3) • d`, and — at a point where `d` vanishes — constant second
derivative `((2 : ℝ) • c).smulRight c`, the quartic contributing nothing to the Hessian at the
origin. Instantiating that at `c = ContinuousLinearMap.fst`, `d = ContinuousLinearMap.snd` on
`ℝ × ℝ` is what makes the model cheap.
-/

noncomputable section

open scoped ContDiff

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

section Model

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

private theorem hasFDerivAt_model (c d : X →L[ℝ] ℝ) (x : X) :
    HasFDerivAt (fun y : X ↦ c y * c y - d y ^ 4)
      ((2 * c x) • c - ((4 : ℝ) * d x ^ 3) • d) x := by
  have h1 : HasFDerivAt (fun y : X ↦ c y * c y) ((2 * c x) • c) x := by
    have hsmul : (2 * c x) • c = c x • (c : X →L[ℝ] ℝ) + c x • c := by
      rw [two_mul, add_smul]
    rw [hsmul]
    exact c.hasFDerivAt.mul c.hasFDerivAt
  have h2 : HasFDerivAt (fun y : X ↦ d y ^ 4) (((4 : ℝ) * d x ^ 3) • d) x := by
    simpa using d.hasFDerivAt.pow 4
  exact h1.sub h2

private theorem fderiv_model (c d : X →L[ℝ] ℝ) :
    fderiv ℝ (fun y : X ↦ c y * c y - d y ^ 4)
      = fun x ↦ (2 * c x) • c - ((4 : ℝ) * d x ^ 3) • d :=
  funext fun x ↦ (hasFDerivAt_model c d x).fderiv

private theorem contDiff_model (c d : X →L[ℝ] ℝ) :
    ContDiff ℝ ∞ fun y : X ↦ c y * c y - d y ^ 4 :=
  (c.contDiff.mul c.contDiff).sub (d.contDiff.pow 4)

private theorem fderiv_fderiv_model (c d : X →L[ℝ] ℝ) (hd0 : d 0 = 0) :
    fderiv ℝ (fderiv ℝ fun y : X ↦ c y * c y - d y ^ 4) 0 = ((2 : ℝ) • c).smulRight c := by
  rw [fderiv_model]
  refine HasFDerivAt.fderiv ?_
  have h1 : HasFDerivAt (fun x : X ↦ (2 * c x) • (c : X →L[ℝ] ℝ))
      (((2 : ℝ) • c).smulRight c) 0 := by
    simpa using (((2 : ℝ) • c).hasFDerivAt).smul_const (c : X →L[ℝ] ℝ)
  have hp : HasFDerivAt (fun x : X ↦ (4 : ℝ) * d x ^ 3) (0 : X →L[ℝ] ℝ) 0 := by
    have hp0 := ((d.hasFDerivAt (x := (0 : X))).pow 3).const_mul (4 : ℝ)
    rw [hd0] at hp0
    simpa using hp0
  have h2 : HasFDerivAt (fun x : X ↦ ((4 : ℝ) * d x ^ 3) • (d : X →L[ℝ] ℝ))
      (0 : X →L[ℝ] (X →L[ℝ] ℝ)) 0 := by
    simpa using hp.smul_const (d : X →L[ℝ] ℝ)
  have h3 := h1.sub h2
  rw [sub_zero] at h3
  exact h3

end Model

/-- The model loss on `ℝ × ℝ`: `f (η, ζ) = η ^ 2 - ζ ^ 4`. -/
private def quarticGerm (p : ℝ × ℝ) : ℝ :=
  ContinuousLinearMap.fst ℝ ℝ ℝ p * ContinuousLinearMap.fst ℝ ℝ ℝ p
    - ContinuousLinearMap.snd ℝ ℝ ℝ p ^ 4

private theorem quarticGerm_def : quarticGerm = fun y : ℝ × ℝ ↦
    ContinuousLinearMap.fst ℝ ℝ ℝ y * ContinuousLinearMap.fst ℝ ℝ ℝ y
      - ContinuousLinearMap.snd ℝ ℝ ℝ y ^ 4 := rfl

private theorem quarticGerm_apply (p : ℝ × ℝ) : quarticGerm p = p.1 * p.1 - p.2 ^ 4 := rfl

private theorem contDiff_quarticGerm : ContDiff ℝ ∞ quarticGerm := contDiff_model _ _

/-- Doubled multiplication on `ℝ`, as an equivalence onto the dual: the `W`-block Hessian of the
model at the origin. -/
private def qTwo : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ) :=
  ContinuousLinearEquiv.equivOfInverse ((2 : ℝ) • ContinuousLinearMap.mul ℝ ℝ)
    ((2⁻¹ : ℝ) • ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) (fun _ ↦ by simp)
    (fun _ ↦ by ext; simp [mul_comm])

private theorem coe_qTwo :
    (qTwo : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) = (2 : ℝ) • ContinuousLinearMap.mul ℝ ℝ := rfl

private theorem quarticGerm_crit : fderiv ℝ quarticGerm 0 = 0 := by
  rw [quarticGerm_def, fderiv_model]
  simp

private theorem quarticGerm_hessian :
    (qTwo : ℝ →L[ℝ] ℝ →L[ℝ] ℝ) = blockW ℝ ℝ (fderiv ℝ (fderiv ℝ quarticGerm) 0) := by
  refine ContinuousLinearMap.ext fun w ↦ ContinuousLinearMap.ext fun w' ↦ ?_
  rw [blockW_apply, quarticGerm_def, fderiv_fderiv_model _ _ (by simp), coe_qTwo]
  simp
  ring

/-- **The Gromoll–Meyer splitting fires on a model with a genuinely non-constant germ.** -/
example : ∃ (Θ : ℝ × ℝ → ℝ × ℝ) (c : ℝ → ℝ) (g : ℝ → ℝ) (U : Set (ℝ × ℝ))
      (e : (ℝ × ℝ) ≃L[ℝ] (ℝ × ℝ)),
    IsOpen U ∧ (0 : ℝ × ℝ) ∈ U ∧ Θ 0 = 0 ∧ ContDiffOn ℝ ∞ Θ U ∧
      HasFDerivAt Θ (e : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ)) 0 ∧ (∀ q ∈ U, (Θ q).2 = q.2) ∧
      ContDiff ℝ ∞ c ∧ c 0 = 0 ∧
      (∀ q ∈ U, ∀ η : ℝ, fderiv ℝ quarticGerm (c q.2, q.2) (η, 0) = 0) ∧
      (∀ ζ : ℝ, g ζ = quarticGerm (c ζ, ζ) - quarticGerm 0) ∧ g 0 = 0 ∧ ContDiff ℝ ∞ g ∧
      (∀ q ∈ U, quarticGerm q - quarticGerm 0
        = (2 : ℝ)⁻¹ * qTwo (Θ q).1 (Θ q).1 + g q.2) ∧
      ∃ ζ : ℝ, g ζ ≠ g 0 := by
  obtain ⟨Θ, c, g, U, e, hUopen, h0U, hΘ0, hΘcd, hΘd, hΘ2, hc, hc0, hccrit, hgdef, hg0, hgcd,
    hsplit⟩ := exists_gromoll_meyer_splitting contDiff_quarticGerm quarticGerm_crit qTwo
      quarticGerm_hessian
  refine ⟨Θ, c, g, U, e, hUopen, h0U, hΘ0, hΘcd, hΘd, hΘ2, hc, hc0, hccrit, hgdef, hg0, hgcd,
    hsplit, ?_⟩
  -- the fibre is forced to be the zero section, so the germ is the quartic
  have hcz : ∀ q ∈ U, c q.2 = 0 := by
    intro q hq
    have h := hccrit q hq 1
    rw [quarticGerm_def, fderiv_model] at h
    simp at h
    exact h
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hUopen 0 h0U
  have hmem : ((0 : ℝ), ε / 2) ∈ U := by
    refine hball ?_
    rw [Metric.mem_ball, dist_zero_right, Prod.norm_def]
    refine max_lt (by simpa using hε) ?_
    rw [Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  refine ⟨ε / 2, ?_⟩
  have hpos : (0 : ℝ) < (ε / 2) ^ 4 := by positivity
  rw [hgdef, hg0, hcz ((0 : ℝ), ε / 2) hmem, quarticGerm_apply, quarticGerm_apply]
  simp only [Prod.fst_zero, Prod.snd_zero]
  intro hcon
  linarith

end AISafetyAtlas.Examples.SingularLearning

end
