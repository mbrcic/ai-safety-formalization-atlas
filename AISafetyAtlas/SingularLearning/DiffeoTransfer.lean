module

public import AISafetyAtlas.SingularLearning.LocalPair
public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.MeasureTheory.Measure.Haar.Unique
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.FDeriv.Analytic
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist

/-!
# Lemma 6.4(i): the local pair is invariant under an analytic change of coordinates

`PairTransfer.lean` proves print's Lemma 6.2 (comparable germs share a pair) and Lemma 6.4(ii)
(free coordinates are free). The third transfer rule print uses, and the one the reduced-rank
chain cannot do without, is

> **Lemma 6.4(i).** The local pair is invariant under an analytic diffeomorphism.

Theorem 5.1 compares `2K(w)` with a germ evaluated at `Ψ(w)`, on the *parameter* space; Theorem
8.1 gives the pair of that germ at the *origin of the chart space*. `Ψ` is not affine — it
contains `A₁₁⁻¹` — so passing between the two is a genuine nonlinear change of variables.

## The proof, and why it needs no determinant

The obvious route is the Jacobian formula, and `JacobianSandwich.lean` carries that route's
measure-theoretic core. It is not the route taken here, because it costs three hypotheses this
argument does not need: measurability of every sublevel set, injectivity on it, and a *lower*
bound on `|det Dφ|`.

What is used instead is that a `K`-Lipschitz map multiplies `D`-dimensional Hausdorff measure by
at most `K ^ D` (`LipschitzOnWith.hausdorffMeasure_image_le`), together with the fact that
`μH[D]` and `volume` are both additive Haar measures on `EuclideanSpace ℝ (Fin D)` and hence
proportional. The resulting bound `volume (φ '' s) ≤ K ^ D * volume s` holds for *every* set `s`,
measurable or not, since both sides are values of measures. Applying it to `φ` and to `φ⁻¹`
sandwiches the volume from both sides, and a `C¹` map is locally Lipschitz, so only
`ContDiffAt.exists_lipschitzOnWith` is needed — no derivative bound is computed anywhere.

## Shape of the statement

The hypotheses are the ones a chart supplies: two open sets, two analytic maps inverse to each
other between them, and the germ's pair known at the image point. The conclusion is the pair of
the pulled-back germ at the source point. Nothing is assumed about the germ beyond that.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

variable {D : ℕ}

/-! ## A Lipschitz map moves Lebesgue measure by a bounded factor -/

/-- `μH[D]` is a positive multiple of Lebesgue measure on `EuclideanSpace ℝ (Fin D)`: both are
additive Haar measures, and Haar measure is unique up to a positive scalar. -/
public theorem exists_hausdorffMeasure_eq_smul_volume (D : ℕ) :
    ∃ c : ℝ≥0, 0 < c ∧
      (μH[(D : ℝ)] : Measure (EuclideanSpace ℝ (Fin D))) = c • volume := by
  have hfr : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin D)) : ℕ) : ℝ) = (D : ℝ) := by
    rw [finrank_euclideanSpace_fin]
  have : (μH[(D : ℝ)] : Measure (EuclideanSpace ℝ (Fin D))).IsAddHaarMeasure := by
    rw [← hfr]; infer_instance
  exact ⟨Measure.addHaarScalarFactor (μH[(D : ℝ)]) volume,
    Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure .., Measure.isAddLeftInvariant_eq_smul ..⟩

/-- **The volume bound.** A `K`-Lipschitz map on `s` sends `s` to a set of volume at most
`K ^ D * volume s`. No measurability and no injectivity: both sides are measures of sets, and
the Hausdorff bound `LipschitzOnWith.hausdorffMeasure_image_le` is itself unrestricted. -/
public theorem measure_image_le_of_lipschitzOnWith
    {φ : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)}
    {s : Set (EuclideanSpace ℝ (Fin D))} {K : ℝ≥0} (h : LipschitzOnWith K φ s) :
    volume (φ '' s) ≤ (K : ℝ≥0∞) ^ D * volume s := by
  obtain ⟨c, hc, hsmul⟩ := exists_hausdorffMeasure_eq_smul_volume D
  have hle := h.hausdorffMeasure_image_le (d := (D : ℝ)) (by positivity)
  rw [hsmul] at hle
  simp only [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.rpow_natCast] at hle
  have hc0 : (c : ℝ≥0∞) ≠ 0 := by simpa using hc.ne'
  rw [← ENNReal.mul_le_mul_iff_right hc0 ENNReal.coe_ne_top]
  calc (c : ℝ≥0∞) * volume (φ '' s) ≤ (K : ℝ≥0∞) ^ D * ((c : ℝ≥0∞) * volume s) := hle
    _ = (c : ℝ≥0∞) * ((K : ℝ≥0∞) ^ D * volume s) := by ring

/-! ## A map analytic on an open set is Lipschitz on a ball -/

/-- Around any point of an open set on which `φ` is analytic there is a ball, inside that set, on
which `φ` is Lipschitz with a *positive* constant. Positivity is free (weaken to `max K 1`) and is
what lets the constant be divided by later. -/
public theorem exists_lipschitzOnWith_ball
    {φ : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)}
    {U : Set (EuclideanSpace ℝ (Fin D))} (hU : IsOpen U) (hφ : AnalyticOnNhd ℝ φ U)
    {w : EuclideanSpace ℝ (Fin D)} (hw : w ∈ U) :
    ∃ ρ > 0, ∃ K : ℝ≥0, 0 < K ∧ Metric.ball w ρ ⊆ U ∧ LipschitzOnWith K φ (Metric.ball w ρ) := by
  obtain ⟨K, t, ht, hlip⟩ := (hφ w hw).contDiffAt.exists_lipschitzOnWith (𝕂 := ℝ)
  obtain ⟨ρ, hρ, hsub⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem ht (hU.mem_nhds hw))
  refine ⟨ρ, hρ, max K 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _),
    fun x hx => (hsub hx).2, ?_⟩
  exact (hlip.mono fun x hx => (hsub hx).1).weaken (le_max_left _ _)

/-! ## Lemma 6.4(i) -/

/-- **Print's Lemma 6.4(i), order form.** If `φ` and `ψ` are mutually inverse analytic maps
between open sets `U ∋ w` and `V ∋ φ w`, then the germ `g ∘ φ` has at `w` the same local pair
that `g` has at `φ w`.

The two radii the proof uses are `K * δ` on the target side (the image of the `δ`-ball is inside
it) and `δ / L` (that ball is inside the image). `HasLocalVolumeOrder` quantifies over all
sufficiently small radii, so both are available, and the mismatch between them is absorbed into
the two constants — the same bookkeeping Lemma 8.6's factor of two already needed. -/
public theorem hasLocalVolumeOrder_comp_of_analytic
    {g : EuclideanSpace ℝ (Fin D) → ℝ}
    {φ ψ : EuclideanSpace ℝ (Fin D) → EuclideanSpace ℝ (Fin D)}
    {U V : Set (EuclideanSpace ℝ (Fin D))} {w : EuclideanSpace ℝ (Fin D)}
    (hU : IsOpen U) (hV : IsOpen V) (hw : w ∈ U)
    (hmaps : Set.MapsTo φ U V) (hinv : Set.InvOn ψ φ U V)
    (hφ : AnalyticOnNhd ℝ φ U) (hψ : AnalyticOnNhd ℝ ψ V)
    {lam : ℝ} {m : ℕ} (h : HasLocalVolumeOrder g (φ w) lam m) :
    HasLocalVolumeOrder (g ∘ φ) w lam m := by
  rcases h with ⟨hzero, hlam, hm⟩ | ⟨hlam, hm, δ₀, hδ₀, hbound⟩
  · exact Or.inl ⟨(hφ w hw).continuousAt.eventually hzero, hlam, hm⟩
  refine Or.inr ⟨hlam, hm, ?_⟩
  obtain ⟨ρ, hρ, K, hK, hρU, hlipφ⟩ := exists_lipschitzOnWith_ball hU hφ hw
  obtain ⟨σ, hσ, L, hL, hσV, hlipψ⟩ := exists_lipschitzOnWith_ball hV hψ (hmaps hw)
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK
  have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  set τ : ℝ := min σ δ₀ with hτdef
  have hτ : 0 < τ := lt_min hσ hδ₀
  refine ⟨min ρ (min (τ / K) (L * τ)), by positivity, fun δ hδ => ?_⟩
  obtain ⟨hδ0, hδlt⟩ := hδ
  have hδρ : δ < ρ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδτ : δ < τ / K := lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_left _ _))
  have hδτ' : δ < L * τ := lt_of_lt_of_le hδlt ((min_le_right _ _).trans (min_le_right _ _))
  have hKδ : (K : ℝ) * δ < τ := by
    rw [← lt_div_iff₀' hKR]; exact hδτ
  have hδL : δ / L < τ := by
    rw [div_lt_iff₀ hLR, mul_comm]; exact hδτ'
  -- the two radii on the target side, both admissible for the hypothesis
  obtain ⟨c₂, C₂, hc₂, hcC₂, hb₂⟩ :=
    hbound (δ / L) ⟨by positivity, lt_of_lt_of_le hδL (min_le_right _ _)⟩
  obtain ⟨c₁, C₁, hc₁, hcC₁, hb₁⟩ :=
    hbound ((K : ℝ) * δ) ⟨by positivity, lt_of_lt_of_le hKδ (min_le_right _ _)⟩
  refine ⟨c₂ / (K : ℝ) ^ D, max (c₂ / (K : ℝ) ^ D) ((L : ℝ) ^ D * C₁), by positivity,
    le_max_left _ _, ?_⟩
  filter_upwards [hb₁, hb₂, Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε h1 h2 hε
  have hvs : 0 ≤ volumeScale lam m ε := by
    have h1' : 0 < ε ^ lam := Real.rpow_pos_of_pos hε.1 lam
    have h2' : (0 : ℝ) < Real.log (1 / ε) :=
      Real.log_pos (by rw [lt_div_iff₀ hε.1]; linarith [hε.2])
    exact le_of_lt (mul_pos h1' (pow_pos h2' _))
  -- the three sets
  set S : Set (EuclideanSpace ℝ (Fin D)) := {x ∈ Metric.ball w δ | (g ∘ φ) x ≤ ε} with hSdef
  set T : Set (EuclideanSpace ℝ (Fin D)) := φ '' S with hTdef
  have hSball : S ⊆ Metric.ball w δ := fun _ hx => hx.1
  have hSρ : S ⊆ Metric.ball w ρ := fun _ hx => Metric.ball_subset_ball hδρ.le hx.1
  -- the image of the small ball lands in the ball of radius `K * δ`
  have hT1 : T ⊆ {y ∈ Metric.ball (φ w) ((K : ℝ) * δ) | g y ≤ ε} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨?_, hx.2⟩
    have := hlipφ.dist_le_mul x (hSρ hx) w (Metric.mem_ball_self hρ)
    have hlt : (K : ℝ) * dist x w < (K : ℝ) * δ :=
      (mul_lt_mul_of_pos_left (Metric.mem_ball.1 hx.1) hKR)
    exact Metric.mem_ball.2 (lt_of_le_of_lt this hlt)
  -- the ball of radius `δ / L` is inside the image
  have hT2 : {y ∈ Metric.ball (φ w) (δ / L) | g y ≤ ε} ⊆ T := by
    rintro y ⟨hy, hgy⟩
    have hyσ : y ∈ Metric.ball (φ w) σ :=
      Metric.ball_subset_ball (le_of_lt (lt_of_lt_of_le hδL (min_le_left _ _))) hy
    have hyV : y ∈ V := hσV hyσ
    have hψy : dist (ψ y) w < δ := by
      have hbase : ψ (φ w) = w := hinv.1 hw
      have := hlipψ.dist_le_mul y hyσ (φ w) (Metric.mem_ball_self hσ)
      rw [hbase] at this
      refine lt_of_le_of_lt this ?_
      have : dist y (φ w) < δ / L := Metric.mem_ball.1 hy
      calc (L : ℝ) * dist y (φ w) < (L : ℝ) * (δ / L) :=
            mul_lt_mul_of_pos_left this hLR
        _ = δ := by field_simp
    have hφψ : φ (ψ y) = y := hinv.2 hyV
    exact ⟨ψ y, ⟨Metric.mem_ball.2 hψy, by simpa [Function.comp_apply, hφψ] using hgy⟩, hφψ⟩
  -- the two Lipschitz volume bounds
  have h3 : volume T ≤ (K : ℝ≥0∞) ^ D * volume S :=
    measure_image_le_of_lipschitzOnWith (hlipφ.mono hSρ)
  have h4 : volume S ≤ (L : ℝ≥0∞) ^ D * volume T := by
    have hTσ : T ⊆ Metric.ball (φ w) σ := fun y hy =>
      Metric.ball_subset_ball (le_of_lt (lt_of_lt_of_le hKδ (min_le_left _ _))) (hT1 hy).1
    have himg : ψ '' T = S := hinv.1.image_image' (hSρ.trans hρU)
    calc volume S = volume (ψ '' T) := by rw [himg]
      _ ≤ (L : ℝ≥0∞) ^ D * volume T := measure_image_le_of_lipschitzOnWith (hlipψ.mono hTσ)
  -- transport to the real-valued interface
  have hSfin : volume S ≠ ⊤ := sublevelVolume_ne_top (g ∘ φ) w δ ε
  have hupper : sublevelVolume (g ∘ φ) w δ ε
      ≤ (L : ℝ) ^ D * sublevelVolume g (φ w) ((K : ℝ) * δ) ε := by
    have hchain : volume S ≤ (L : ℝ≥0∞) ^ D
        * volume {y ∈ Metric.ball (φ w) ((K : ℝ) * δ) | g y ≤ ε} :=
      h4.trans (by gcongr)
    have hfin : (L : ℝ≥0∞) ^ D * volume {y ∈ Metric.ball (φ w) ((K : ℝ) * δ) | g y ≤ ε} ≠ ⊤ :=
      ENNReal.mul_ne_top (by finiteness) (sublevelVolume_ne_top g (φ w) _ ε)
    have hmono := ENNReal.toReal_mono hfin hchain
    rw [hSdef] at hmono
    simpa [sublevelVolume, ENNReal.toReal_mul, ENNReal.toReal_pow] using hmono
  have hlower : sublevelVolume g (φ w) (δ / L) ε
      ≤ (K : ℝ) ^ D * sublevelVolume (g ∘ φ) w δ ε := by
    have hchain : volume {y ∈ Metric.ball (φ w) (δ / L) | g y ≤ ε} ≤ (K : ℝ≥0∞) ^ D * volume S :=
      (measure_mono hT2).trans h3
    have hfin : (K : ℝ≥0∞) ^ D * volume S ≠ ⊤ := ENNReal.mul_ne_top (by finiteness) hSfin
    have hmono := ENNReal.toReal_mono hfin hchain
    rw [hSdef] at hmono
    simpa [sublevelVolume, ENNReal.toReal_mul, ENNReal.toReal_pow] using hmono
  have hKD : (0 : ℝ) < (K : ℝ) ^ D := pow_pos hKR D
  constructor
  · have hstep : c₂ * volumeScale lam m ε ≤ (K : ℝ) ^ D * sublevelVolume (g ∘ φ) w δ ε :=
      h2.1.trans hlower
    have hrw : c₂ / (K : ℝ) ^ D * volumeScale lam m ε
        = c₂ * volumeScale lam m ε / (K : ℝ) ^ D := by ring
    rw [hrw, div_le_iff₀ hKD, mul_comm (sublevelVolume (g ∘ φ) w δ ε)]
    exact hstep
  · refine hupper.trans ?_
    calc (L : ℝ) ^ D * sublevelVolume g (φ w) ((K : ℝ) * δ) ε
        ≤ (L : ℝ) ^ D * (C₁ * volumeScale lam m ε) := by
          exact mul_le_mul_of_nonneg_left h1.2 (by positivity)
      _ = ((L : ℝ) ^ D * C₁) * volumeScale lam m ε := by ring
      _ ≤ max (c₂ / (K : ℝ) ^ D) ((L : ℝ) ^ D * C₁) * volumeScale lam m ε :=
          mul_le_mul_of_nonneg_right (le_max_right _ _) hvs

/-- **The same statement between two spaces of equal dimension.** The chart's source and target
are counted differently — `HN + MH` on the parameter side, `q + (hn + ph) + g` on the chart side
— and they are equal only propositionally. Substituting the equality is the whole proof. -/
public theorem hasLocalVolumeOrder_comp_of_analytic' {D₁ D₂ : ℕ} (hD : D₁ = D₂)
    {g : EuclideanSpace ℝ (Fin D₂) → ℝ}
    {φ : EuclideanSpace ℝ (Fin D₁) → EuclideanSpace ℝ (Fin D₂)}
    {ψ : EuclideanSpace ℝ (Fin D₂) → EuclideanSpace ℝ (Fin D₁)}
    {U : Set (EuclideanSpace ℝ (Fin D₁))} {V : Set (EuclideanSpace ℝ (Fin D₂))}
    {w : EuclideanSpace ℝ (Fin D₁)} {lam : ℝ} {m : ℕ}
    (hU : IsOpen U) (hV : IsOpen V) (hw : w ∈ U)
    (hmaps : Set.MapsTo φ U V) (hinv : Set.InvOn ψ φ U V)
    (hφ : AnalyticOnNhd ℝ φ U) (hψ : AnalyticOnNhd ℝ ψ V)
    (h : HasLocalVolumeOrder g (φ w) lam m) :
    HasLocalVolumeOrder (g ∘ φ) w lam m := by
  subst hD
  exact hasLocalVolumeOrder_comp_of_analytic hU hV hw hmaps hinv hφ hψ h

/-! ## Two corollaries the assembly uses -/

/-- **The orbit transfer.** A continuous linear equivalence is entire, and so is its inverse, so
Lemma 6.4(i) applies with `U = V = univ`. Print's step 1 — carrying an arbitrary factorization to
its normal form by the linear group action of Lemma 3.2 — is exactly this case, and needs no
second development. -/
public theorem hasLocalVolumeOrder_comp_continuousLinearEquiv
    {g : EuclideanSpace ℝ (Fin D) → ℝ}
    (e : EuclideanSpace ℝ (Fin D) ≃L[ℝ] EuclideanSpace ℝ (Fin D))
    {w : EuclideanSpace ℝ (Fin D)} {lam : ℝ} {m : ℕ}
    (h : HasLocalVolumeOrder g (e w) lam m) :
    HasLocalVolumeOrder (g ∘ e) w lam m :=
  hasLocalVolumeOrder_comp_of_analytic isOpen_univ isOpen_univ (Set.mem_univ w)
    (Set.mapsTo_univ _ _) ⟨fun x _ => e.symm_apply_apply x, fun y _ => e.apply_symm_apply y⟩
    (fun x _ => (e.toContinuousLinearMap.analyticAt x))
    (fun y _ => (e.symm.toContinuousLinearMap.analyticAt y)) h

/-- **Moving the base point.** Theorem 8.1 states a pair at the origin, while the chart's base
point is not the origin. Translation is entire, and its inverse is translation by `-b`. -/
public theorem hasLocalVolumeOrder_comp_add_const
    {g : EuclideanSpace ℝ (Fin D) → ℝ} (b w : EuclideanSpace ℝ (Fin D)) {lam : ℝ} {m : ℕ}
    (h : HasLocalVolumeOrder g (w + b) lam m) :
    HasLocalVolumeOrder (fun x => g (x + b)) w lam m :=
  hasLocalVolumeOrder_comp_of_analytic (ψ := fun y => y - b) isOpen_univ isOpen_univ
    (Set.mem_univ w) (Set.mapsTo_univ _ _)
    ⟨fun x _ => by simp, fun y _ => by simp⟩
    (analyticOnNhd_id.add analyticOnNhd_const) (analyticOnNhd_id.sub analyticOnNhd_const) h

end AISafetyAtlas.SingularLearning
