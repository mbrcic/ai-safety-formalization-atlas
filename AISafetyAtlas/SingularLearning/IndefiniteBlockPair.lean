module

public import AISafetyAtlas.SingularLearning.CriticalFiber
public import AISafetyAtlas.SingularLearning.GermPair
public import AISafetyAtlas.SingularLearning.DiffeoTransfer
public import AISafetyAtlas.SingularLearning.TwoSidedBand

/-!
# An indefinite Hessian block forces the two-sided pair `(1,1)`

Three modules each hold one link of the chain print's Stage 3 argument runs, and none of them
joins to the next without work.

* `exists_gromoll_meyer_splitting` (`CriticalFiber`) flattens a smooth `f` on `W × V` near a
  critical point onto `2⁻¹ Q₀ (Θ q).1 (Θ q).1 + g q.2`, provided the `W`-block of the Hessian is
  handed over as an **isomorphism onto the dual**.
* `hasLocalVolumeOrder_abs_matrixQuadForm_add_germ` (`GermPair`) computes the band order of
  `|Q(ξ) + g(ζ)|` for a nondegenerate indefinite **matrix** form in at least three variables plus
  an arbitrary continuous germ on the complement.
* `hasLocalVolumeOrder_comp_of_lipschitz` (`DiffeoTransfer`) moves a local volume order through a
  chart that is bi-Lipschitz near the point, which a `C^∞` chart with invertible derivative is.

The gaps are three. The splitting speaks of a dual isomorphism and the band estimate of a
matrix; the splitting lives on a product `W × V` and the band estimate on a single Euclidean
space; and the splitting's chart is produced with no inverse, while the transport needs one on
both sides. This module closes all three and states the consequence.

## What is proved

`hasLocalVolumeOrder_centeredBandGerm_of_indefinite_block`: if a smooth `L` on
`EuclideanSpace ℝ (Fin D)` has a critical point at `w₀` and, in some linear chart splitting the
space as `ℝ^m × ℝ^d` with `m ≥ 3`, the `ℝ^m` block of the Hessian is a symmetric matrix `K` with
`det K ≠ 0` taking both signs, then the two-sided band `|L x − L w₀| ≤ ε` has volume `Θ(ε)` in
every small ball around `w₀`.

**Nothing is assumed about the Hessian off the block.** The complementary germ the splitting
produces is carried by the band estimate as an arbitrary continuous function vanishing at the
origin, so the `ℝ^d` directions may be as degenerate as they like. That is the point of the
statement, and `Examples/SingularLearning/IndefiniteBlockPair.lean` witnesses it on a model
whose Hessian is identically zero off the block.

## The normalisation, and where the factor two goes

`K` is the **Hessian block itself**: the hypothesis reads

    `blockW _ _ (fderiv ℝ (fderiv ℝ (fun p => L (w₀ + Ξ p))) 0) x y = matrixQuadPolar K x y`,

so `hsymm`, `hdet`, `hpos` and `hneg` are conditions on the second derivative and not on some
rescaling of it. The splitting delivers `2⁻¹ * Q₀ η η`, so the matrix handed to the band estimate
is `(2 : ℝ)⁻¹ • K`, and its symmetry, nondegeneracy and indefiniteness are **re-derived** for
that matrix rather than inherited: `isSymm_smul`, `det_smul_ne_zero` and `matrixQuadForm_smul`
do exactly that. A scalar multiple changes none of the three, but the proof says so rather than
assuming it, because a sign or a factor lost here would produce a theorem about a different
form that every other check in this repository would pass.

On the model `x ↦ x²` this reads `K = 2`, not `K = 1`. A caller who holds the coefficient matrix
of the quadratic part of the Taylor expansion must therefore double it before calling.

## The pieces built here

* `matrixPolarEquiv` turns `det K ≠ 0` into the isomorphism `W ≃L[ℝ] (W →L[ℝ] ℝ)` the splitting
  demands. Injectivity is the substance — a functional annihilating the image of `K` annihilates
  everything, because `K` is onto — and equality of dimensions upgrades it to a bijection.
* `splitCLE` is the coordinate split as a continuous linear equivalence, the same function as
  `splitLE` and as `euclideanProdEquiv`.
* `exists_lipschitzOnWith_ball_of_contDiffAt` is the `ContDiffAt` form of the Lipschitz-ball
  extraction that `exists_lipschitzOnWith_ball` performs for analytic maps.
* `HasLocalVolumeOrder.congr_of_eventuallyEq` records that the order is a property of the germ.
  The chart identity holds only on the neighbourhood the splitting produces, so the transported
  order has to be moved onto the germ the statement names.

The local inverse of the chart comes from `ContDiffAt.to_localInverse`; the two sets on which
the chart and its inverse invert each other are taken to be exactly the sets where they do, which
is all the transport lemma asks for and avoids constructing a homeomorphism.
-/

noncomputable section

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology

open scoped ContDiff Matrix

/-! ## The polar form of a matrix -/

/-- The polarisation of `matrixQuadForm`: the bilinear form of `K`. -/
@[expose] public noncomputable def matrixQuadPolar {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) : ℝ :=
  (fun i => x i) ⬝ᵥ (K *ᵥ (fun i => y i))

/-- On the diagonal the polar form is the quadratic form. -/
public theorem matrixQuadPolar_self {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (x : EuclideanSpace ℝ (Fin n)) : matrixQuadPolar K x x = matrixQuadForm K x := rfl

/-- The polar form as a bilinear map. -/
@[expose] public noncomputable def matrixPolarBilin {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ :=
  (Matrix.toLinearMap₂' ℝ K).compl₁₂
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap
    (WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).toLinearMap

public theorem matrixPolarBilin_apply {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    matrixPolarBilin K x y = matrixQuadPolar K x y := by
  rw [matrixPolarBilin, LinearMap.compl₁₂_apply, Matrix.toLinearMap₂'_apply']
  rfl

/-- The polar form read as a map into the continuous dual. -/
@[expose] public noncomputable def matrixPolarDual {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ) :
    EuclideanSpace ℝ (Fin n) →ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  (LinearMap.toContinuousLinearMap :
      (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).toLinearMap.comp
    (matrixPolarBilin K)

public theorem matrixPolarDual_apply {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (x y : EuclideanSpace ℝ (Fin n)) :
    matrixPolarDual K x y = matrixQuadPolar K x y := by
  rw [matrixPolarDual]
  simp [matrixPolarBilin_apply]

public theorem injective_matrixPolarDual {n : ℕ} {K : Matrix (Fin n) (Fin n) ℝ}
    (hdet : K.det ≠ 0) : Function.Injective (matrixPolarDual K) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  have hall : ∀ v : Fin n → ℝ, (fun i => x i) ⬝ᵥ v = 0 := by
    intro v
    have hy := congrArg (fun φ : EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ =>
      φ ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm (K⁻¹ *ᵥ v))) hx
    simp only [zero_apply] at hy
    rw [matrixPolarDual_apply] at hy
    have hKv : K *ᵥ (K⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv K (Ne.isUnit hdet), Matrix.one_mulVec]
    rw [matrixQuadPolar] at hy
    rwa [show (fun i => ((WithLp.linearEquiv 2 ℝ (Fin n → ℝ)).symm (K⁻¹ *ᵥ v)) i)
      = K⁻¹ *ᵥ v from rfl, hKv] at hy
  ext i
  have hi := hall (Pi.single i 1)
  simpa using hi

/-- The continuous dual of a Euclidean space has the dimension of the space. -/
public theorem finrank_euclidean_dual (n : ℕ) :
    Module.finrank ℝ (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)
      = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
  rw [← (LinearMap.toContinuousLinearMap :
    (EuclideanSpace ℝ (Fin n) →ₗ[ℝ] ℝ) ≃ₗ[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).finrank_eq]
  exact Subspace.dual_finrank_eq

/-- **A matrix with nonvanishing determinant polarises to an isomorphism onto the dual.** -/
@[expose] public noncomputable def matrixPolarEquiv {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hdet : K.det ≠ 0) :
    EuclideanSpace ℝ (Fin n) ≃L[ℝ] (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
  (LinearMap.linearEquivOfInjective (matrixPolarDual K) (injective_matrixPolarDual hdet)
    (finrank_euclidean_dual n).symm).toContinuousLinearEquiv

public theorem matrixPolarEquiv_apply {n : ℕ} (K : Matrix (Fin n) (Fin n) ℝ)
    (hdet : K.det ≠ 0) (x y : EuclideanSpace ℝ (Fin n)) :
    matrixPolarEquiv K hdet x y = matrixQuadPolar K x y := by
  rw [matrixPolarEquiv]
  rw [show ((LinearMap.linearEquivOfInjective (matrixPolarDual K)
      (injective_matrixPolarDual hdet)
      (finrank_euclidean_dual n).symm).toContinuousLinearEquiv x)
    = matrixPolarDual K x from rfl]
  exact matrixPolarDual_apply K x y

/-! ## Rescaling a matrix rescales its form -/

public theorem matrixQuadForm_smul {n : ℕ} (c : ℝ) (K : Matrix (Fin n) (Fin n) ℝ)
    (z : EuclideanSpace ℝ (Fin n)) :
    matrixQuadForm (c • K) z = c * matrixQuadForm K z := by
  simp [matrixQuadForm, Matrix.smul_mulVec]

public theorem isSymm_smul {n : ℕ} (c : ℝ) {K : Matrix (Fin n) (Fin n) ℝ} (hsymm : K.IsSymm) :
    (c • K).IsSymm := by
  show (c • K)ᵀ = c • K
  rw [Matrix.transpose_smul, hsymm.eq]

public theorem det_smul_ne_zero {n : ℕ} {c : ℝ} (hc : c ≠ 0) {K : Matrix (Fin n) (Fin n) ℝ}
    (hdet : K.det ≠ 0) : (c • K).det ≠ 0 := by
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) hdet

/-! ## A local volume order only sees the germ -/

/-- **The order is a property of the germ.**  Two functions agreeing on a
neighbourhood of `w` have the same local volume order at `w`. -/
public theorem HasLocalVolumeOrder.congr_of_eventuallyEq {n : ℕ}
    {F G : EuclideanSpace ℝ (Fin n) → ℝ} {w : EuclideanSpace ℝ (Fin n)} {lam : ℝ} {m : ℕ}
    (h : HasLocalVolumeOrder F w lam m) (heq : ∀ᶠ x in nhds w, F x = G x) :
    HasLocalVolumeOrder G w lam m := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.1 heq
  rcases h with ⟨hz, hl, hm⟩ | ⟨hlam, hm, δ₀, hδ₀, hb⟩
  · exact Or.inl ⟨(heq.and hz).mono fun _ hx => hx.1 ▸ hx.2, hl, hm⟩
  refine Or.inr ⟨hlam, hm, min δ₀ r, lt_min hδ₀ hr, fun δ hδ => ?_⟩
  obtain ⟨cL, cU, hcL, hcLU, hbd⟩ := hb δ ⟨hδ.1, lt_of_lt_of_le hδ.2 (min_le_left _ _)⟩
  have hsub : Metric.ball w δ ⊆ Metric.ball w r :=
    Metric.ball_subset_ball (le_of_lt (lt_of_lt_of_le hδ.2 (min_le_right _ _)))
  have hset : ∀ ε : ℝ, sublevelVolume G w δ ε = sublevelVolume F w δ ε := by
    intro ε
    have hs : {x ∈ Metric.ball w δ | G x ≤ ε} = {x ∈ Metric.ball w δ | F x ≤ ε} := by
      ext x
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hx1, hx2⟩
        exact ⟨hx1, by rw [hball (hsub hx1)]; exact hx2⟩
      · rintro ⟨hx1, hx2⟩
        exact ⟨hx1, by rw [← hball (hsub hx1)]; exact hx2⟩
    rw [sublevelVolume, sublevelVolume, hs]
  exact ⟨cL, cU, hcL, hcLU, by simpa only [hset] using hbd⟩

/-! ## The coordinate split as a continuous linear equivalence -/

/-- `splitLE` packaged as a continuous linear equivalence.  Finite dimensionality makes the
packaging free, and it is what a transport lemma stated for continuous maps consumes. -/
@[expose] public noncomputable def splitCLE (p q : ℕ) :
    (EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin (p + q)) :=
  (splitLE p q).toContinuousLinearEquiv

public theorem coe_splitCLE (p q : ℕ) : ⇑(splitCLE p q) = ⇑(euclideanProdEquiv p q) :=
  coe_splitLE p q

public theorem coe_splitCLE_symm (p q : ℕ) : ⇑(splitCLE p q).symm = ⇑(splitLE p q).symm := rfl

public theorem euclideanProdEquiv_symm_splitCLE (p q : ℕ)
    (x : EuclideanSpace ℝ (Fin p) × EuclideanSpace ℝ (Fin q)) :
    (euclideanProdEquiv p q).symm (splitCLE p q x) = x := by
  rw [show (splitCLE p q) x = euclideanProdEquiv p q x from congrFun (coe_splitCLE p q) x]
  exact (euclideanProdEquiv p q).symm_apply_apply x

/-! ## Lipschitz balls from a `C¹` germ -/

/-- The `ContDiffAt` analogue of `exists_lipschitzOnWith_ball`: around a point where `φ` is
`C¹` there is a ball, inside any prescribed neighbourhood, on which `φ` is Lipschitz with a
positive constant. -/
public theorem exists_lipschitzOnWith_ball_of_contDiffAt {D : ℕ}
    {φ : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)}
    {w : EuclideanSpace ℝ (Fin D)} (hφ : ContDiffAt ℝ 1 φ w)
    {U : Set (EuclideanSpace ℝ (Fin D))} (hU : U ∈ nhds w) :
    ∃ ρ > 0, ∃ K : NNReal, 0 < K ∧ Metric.ball w ρ ⊆ U ∧
      LipschitzOnWith K φ (Metric.ball w ρ) := by
  obtain ⟨K, t, ht, hlip⟩ := hφ.exists_lipschitzOnWith
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht hU)
  exact ⟨ρ, hρ, max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x hx => (hsub hx).2, (hlip.mono fun x hx => (hsub hx).1).weaken (le_max_left _ _)⟩

/-! ## The band pair in split coordinates -/

/-- **The two-sided band pair at a critical point with an indefinite Hessian block, read in
split coordinates at the origin.** -/
public theorem hasLocalVolumeOrder_abs_sub_of_indefinite_block {m d : ℕ} (h3 : 3 ≤ m)
    {f : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f)
    (hcrit : fderiv ℝ f 0 = 0)
    (K : Matrix (Fin m) (Fin m) ℝ) (hsymm : K.IsSymm) (hdet : K.det ≠ 0)
    (hpos : ∃ z, 0 < matrixQuadForm K z) (hneg : ∃ z, matrixQuadForm K z < 0)
    (hQ : ∀ x y : EuclideanSpace ℝ (Fin m),
      blockW _ _ (fderiv ℝ (fderiv ℝ f) 0) x y = matrixQuadPolar K x y) :
    HasLocalVolumeOrder
      (fun y : EuclideanSpace ℝ (Fin (m + d)) => |f ((splitLE m d).symm y) - f 0|) 0 1 1 := by
  classical
  have hQ₀ : ((matrixPolarEquiv K hdet :
        EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) →L[ℝ] ℝ))
      = blockW (EuclideanSpace ℝ (Fin m)) (EuclideanSpace ℝ (Fin d))
        (fderiv ℝ (fderiv ℝ f) 0) := by
    refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
    rw [hQ x y]
    exact matrixPolarEquiv_apply K hdet x y
  obtain ⟨Θ, c, g, Usp, e, hUopen, h0U, hΘ0, hΘcd, hΘd, hΘ2, -, -, -, -, hg0, hgcd,
    hspl⟩ := exists_gromoll_meyer_splitting hf hcrit (matrixPolarEquiv K hdet) hQ₀
  -- the band estimate, at the halved matrix the splitting's factor `2⁻¹` produces
  have hK'symm : ((2 : ℝ)⁻¹ • K).IsSymm := isSymm_smul _ hsymm
  have hK'det : ((2 : ℝ)⁻¹ • K).det ≠ 0 := det_smul_ne_zero (by norm_num) hdet
  have hK'form : ∀ z, matrixQuadForm ((2 : ℝ)⁻¹ • K) z = (2 : ℝ)⁻¹ * matrixQuadForm K z :=
    fun z => matrixQuadForm_smul _ _ _
  have hK'pos : ∃ z, 0 < matrixQuadForm ((2 : ℝ)⁻¹ • K) z := by
    obtain ⟨z, hz⟩ := hpos
    exact ⟨z, by rw [hK'form]; linarith⟩
  have hK'neg : ∃ z, matrixQuadForm ((2 : ℝ)⁻¹ • K) z < 0 := by
    obtain ⟨z, hz⟩ := hneg
    exact ⟨z, by rw [hK'form]; linarith⟩
  have hband := hasLocalVolumeOrder_abs_matrixQuadForm_add_germ (s := d) h3 ((2 : ℝ)⁻¹ • K)
    hK'symm hK'det hK'pos hK'neg g hgcd.continuous hg0
  -- the local inverse of the chart
  have hΘcda : ContDiffAt ℝ ∞ Θ 0 := hΘcd.contDiffAt (hUopen.mem_nhds h0U)
  have hn : (∞ : WithTop ℕ∞) ≠ 0 := by decide
  have hstrict : HasStrictFDerivAt Θ
      (e : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) →L[ℝ]
        (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d))) 0 :=
    hΘcda.hasStrictFDerivAt' hΘd hn
  set Ψ : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) →
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) :=
    hstrict.localInverse Θ e 0 with hΨdef
  have hΨcd : ContDiffAt ℝ ∞ Ψ 0 := by
    have h := hΘcda.to_localInverse (f' := e) hΘd hn
    rw [hΘ0] at h
    exact h
  have hΨ0 : Ψ 0 = 0 := by
    have h := hstrict.localInverse_apply_image
    rw [hΘ0] at h
    exact h
  have hleft : ∀ᶠ x in nhds (0 : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)),
      Ψ (Θ x) = x := hstrict.eventually_left_inverse
  have hright : ∀ᶠ y in nhds (0 : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)),
      Θ (Ψ y) = y := by
    have h := hstrict.eventually_right_inverse
    rwa [hΘ0] at h
  -- the chart conjugated into the single Euclidean space
  have hSLcd : ContDiff ℝ ∞ (splitCLE m d : (EuclideanSpace ℝ (Fin m) ×
      EuclideanSpace ℝ (Fin d)) → EuclideanSpace ℝ (Fin (m + d))) := (splitCLE m d).contDiff
  have hSLscd : ContDiff ℝ ∞ ((splitCLE m d).symm : EuclideanSpace ℝ (Fin (m + d)) →
      (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d))) := (splitCLE m d).symm.contDiff
  have hSLs0 : (splitCLE m d).symm 0 = 0 := map_zero _
  set Θ' : EuclideanSpace ℝ (Fin (m + d)) → EuclideanSpace ℝ (Fin (m + d)) :=
    fun y => splitCLE m d (Θ ((splitCLE m d).symm y)) with hΘ'def
  set Ψ' : EuclideanSpace ℝ (Fin (m + d)) → EuclideanSpace ℝ (Fin (m + d)) :=
    fun y => splitCLE m d (Ψ ((splitCLE m d).symm y)) with hΨ'def
  have hΘ'0 : Θ' 0 = 0 := by rw [hΘ'def]; simp only [hSLs0, hΘ0, map_zero]
  have hΨ'0 : Ψ' 0 = 0 := by rw [hΨ'def]; simp only [hSLs0, hΨ0, map_zero]
  have hΘ'cd : ContDiffAt ℝ ∞ Θ' 0 := by
    rw [hΘ'def]
    refine hSLcd.contDiffAt.comp 0 ?_
    have h1 : ContDiffAt ℝ ∞ Θ ((splitCLE m d).symm 0) := by rw [hSLs0]; exact hΘcda
    exact h1.comp 0 hSLscd.contDiffAt
  have hΨ'cd : ContDiffAt ℝ ∞ Ψ' 0 := by
    rw [hΨ'def]
    refine hSLcd.contDiffAt.comp 0 ?_
    have h1 : ContDiffAt ℝ ∞ Ψ ((splitCLE m d).symm 0) := by rw [hSLs0]; exact hΨcd
    exact h1.comp 0 hSLscd.contDiffAt
  -- the two sets on which the conjugated chart and its inverse invert each other
  have hUnhds : {x : EuclideanSpace ℝ (Fin (m + d)) | Ψ' (Θ' x) = x}
      ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + d))) := by
    have hpre : ((fun y => (splitCLE m d).symm y) ⁻¹'
        {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) | Ψ (Θ q) = q})
        ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + d))) := by
      refine ContinuousAt.preimage_mem_nhds ((splitCLE m d).symm.continuous.continuousAt) ?_
      rw [hSLs0]; exact hleft
    refine Filter.mem_of_superset hpre fun x hx => ?_
    show Ψ' (Θ' x) = x
    simp only [hΨ'def, hΘ'def, ContinuousLinearEquiv.symm_apply_apply]
    rw [show Ψ (Θ ((splitCLE m d).symm x)) = (splitCLE m d).symm x from hx]
    exact (splitCLE m d).apply_symm_apply x
  have hVnhds : {y : EuclideanSpace ℝ (Fin (m + d)) | Θ' (Ψ' y) = y}
      ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + d))) := by
    have hpre : ((fun y => (splitCLE m d).symm y) ⁻¹'
        {q : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d) | Θ (Ψ q) = q})
        ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + d))) := by
      refine ContinuousAt.preimage_mem_nhds ((splitCLE m d).symm.continuous.continuousAt) ?_
      rw [hSLs0]; exact hright
    refine Filter.mem_of_superset hpre fun x hx => ?_
    show Θ' (Ψ' x) = x
    simp only [hΨ'def, hΘ'def, ContinuousLinearEquiv.symm_apply_apply]
    rw [show Θ (Ψ ((splitCLE m d).symm x)) = (splitCLE m d).symm x from hx]
    exact (splitCLE m d).apply_symm_apply x
  have h1le : (1 : WithTop ℕ∞) ≤ (∞ : WithTop ℕ∞) := by exact_mod_cast le_top
  have hmain : HasLocalVolumeOrder ((fun w : EuclideanSpace ℝ (Fin (m + d)) =>
      |matrixQuadForm ((2 : ℝ)⁻¹ • K) ((euclideanProdEquiv m d).symm w).1
        + g (((euclideanProdEquiv m d).symm w).2)|) ∘ Θ') 0 1 1 := by
    refine hasLocalVolumeOrder_comp_of_lipschitz (U := {x | Ψ' (Θ' x) = x})
      (V := {y | Θ' (Ψ' y) = y}) (w := 0) ?_ ⟨fun x hx => hx, fun y hy => hy⟩
      hΘ'cd.continuousAt ?_ ?_ ?_
    · show Ψ' (Θ' 0) = 0
      rw [hΘ'0, hΨ'0]
    · exact exists_lipschitzOnWith_ball_of_contDiffAt (hΘ'cd.of_le h1le) hUnhds
    · rw [hΘ'0]
      exact exists_lipschitzOnWith_ball_of_contDiffAt (hΨ'cd.of_le h1le) hVnhds
    · rw [hΘ'0]; exact hband
  -- on a neighbourhood of the origin the transported germ is the band of `f`
  refine hmain.congr_of_eventuallyEq ?_
  have hstep : ∀ z : EuclideanSpace ℝ (Fin m),
      matrixQuadForm K z = (matrixPolarEquiv K hdet) z z := by
    intro z
    rw [matrixPolarEquiv_apply K hdet z z, matrixQuadPolar_self]
  have hnb : ((fun y => (splitCLE m d).symm y) ⁻¹' Usp)
      ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + d))) := by
    refine ContinuousAt.preimage_mem_nhds ((splitCLE m d).symm.continuous.continuousAt) ?_
    rw [hSLs0]; exact hUopen.mem_nhds h0U
  filter_upwards [hnb] with y hy
  have hy' : (splitCLE m d).symm y ∈ Usp := hy
  have hQeq : (euclideanProdEquiv m d).symm (Θ' y) = Θ ((splitCLE m d).symm y) := by
    simp only [hΘ'def]
    exact euclideanProdEquiv_symm_splitCLE m d _
  have hqq : (splitLE m d).symm y = (splitCLE m d).symm y := rfl
  rw [hqq, Function.comp_apply, hQeq, hK'form, hΘ2 _ hy', hstep, ← hspl _ hy']

/-! ## The theorem -/

/-- **A critical point whose Hessian is nondegenerate and indefinite on some
block of dimension at least three has two-sided band pair `(1,1)`**, whatever the
Hessian does off that block. -/
public theorem hasLocalVolumeOrder_centeredBandGerm_of_indefinite_block
    {D m d : ℕ} (hD : m + d = D) (h3 : 3 ≤ m)
    {L : EuclideanSpace ℝ (Fin D) → ℝ} (hL : ContDiff ℝ ∞ L)
    (w₀ : EuclideanSpace ℝ (Fin D))
    (Ξ : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) ≃L[ℝ]
      EuclideanSpace ℝ (Fin D))
    (K : Matrix (Fin m) (Fin m) ℝ) (hsymm : K.IsSymm) (hdet : K.det ≠ 0)
    (hpos : ∃ z, 0 < matrixQuadForm K z) (hneg : ∃ z, matrixQuadForm K z < 0)
    (hcrit : fderiv ℝ (fun p => L (w₀ + Ξ p)) 0 = 0)
    (hQ : ∀ x y : EuclideanSpace ℝ (Fin m),
      blockW _ _ (fderiv ℝ (fderiv ℝ (fun p => L (w₀ + Ξ p))) 0) x y
        = matrixQuadPolar K x y) :
    HasLocalVolumeOrder (centeredBandGerm L w₀) w₀ 1 1 := by
  subst hD
  set f : (EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin d)) → ℝ :=
    fun p => L (w₀ + Ξ p) with hfdef
  have hf : ContDiff ℝ ∞ f := hL.comp (contDiff_const.add Ξ.contDiff)
  have hbase := hasLocalVolumeOrder_abs_sub_of_indefinite_block h3 hf hcrit K hsymm hdet
    hpos hneg hQ
  set T : EuclideanSpace ℝ (Fin (m + d)) ≃L[ℝ] EuclideanSpace ℝ (Fin (m + d)) :=
    (splitCLE m d).symm.trans Ξ with hTdef
  set G₁ : EuclideanSpace ℝ (Fin (m + d)) → ℝ :=
    fun x => centeredBandGerm L w₀ (x + w₀) with hG₁def
  have hcomp : (fun y : EuclideanSpace ℝ (Fin (m + d)) => |f ((splitLE m d).symm y) - f 0|)
      = G₁ ∘ T := by
    funext y
    simp only [hG₁def, hTdef, Function.comp_apply, centeredBandGerm, hfdef,
      ContinuousLinearEquiv.trans_apply, map_zero, add_zero]
    rw [show (splitLE m d).symm y = (splitCLE m d).symm y from rfl, add_comm (Ξ _) w₀]
  rw [hcomp] at hbase
  have hG₁ : HasLocalVolumeOrder G₁ 0 1 1 := by
    have h := hasLocalVolumeOrder_comp_continuousLinearEquiv (g := G₁ ∘ T) T.symm
      (w := 0) (by rw [map_zero]; exact hbase)
    have hfun : (G₁ ∘ T) ∘ (T.symm : EuclideanSpace ℝ (Fin (m + d)) →
        EuclideanSpace ℝ (Fin (m + d))) = G₁ := by
      funext x
      simp only [Function.comp_apply, ContinuousLinearEquiv.apply_symm_apply]
    rwa [hfun] at h
  have hshift := hasLocalVolumeOrder_comp_add_const (g := G₁) (-w₀) w₀
    (by rw [add_neg_cancel]; exact hG₁)
  have hfun2 : (fun x : EuclideanSpace ℝ (Fin (m + d)) => G₁ (x + -w₀))
      = centeredBandGerm L w₀ := by
    funext x
    simp only [hG₁def, neg_add_cancel_right]
  rwa [hfun2] at hshift

end AISafetyAtlas.SingularLearning

end
