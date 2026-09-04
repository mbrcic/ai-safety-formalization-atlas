module

public import AISafetyAtlas.SingularLearning.ChartAnalytic

/-!
# Worked models for the chart's analyticity

`AISafetyAtlas/SingularLearning/ChartAnalytic.lean` proves that every ingredient of Step 5's
`Ψ` is analytic, and that all nine of its coordinate blocks are analytic at every point of
`ElimChartDomain`. The examples below exercise the toolkit and then the conclusion.

## What the toolkit is for

`MatrixAnalytic.lean` already had entries, determinants, adjugates and inverses. What the chart
needs on top is closure under the *block* algebra it is written in: multiplication,
`fromBlocks`, `fromCols`, `fromRows`, and the projections. Each is linear or bilinear in the
entries, so each reduces to `analyticAt_matrix_of_entries` over a finite sum of products.

## The shape of the conclusion

Print says the chart is "analytic with analytic inverse on
`{det A₁₁ ≠ 0} ∩ {det P_{top}(D) ≠ 0}`", and its reason is that all the identities are rational
functions whose only denominators are those two determinants. The formalization matches that
exactly: `analyticAt_elimPsi_blocks` takes precisely two hypotheses, one per determinant, and
every other ingredient is analytic unconditionally.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-! ## The toolkit -/

/-- **Matrix multiplication preserves analyticity** — the bilinear case, and the one the chart
uses most. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m n k : Type*} [Fintype m]
    [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n]
    {f : E → Matrix m k ℝ} {g : E → Matrix k n ℝ} {x : E}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => f y * g y) x :=
  AnalyticAt.matrix_mul hf hg

/-- **`fromBlocks` preserves analyticity** — the shape `L(A)`, `R(D)` and their inverses are
written in. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m₁ m₂ n₁ n₂ : Type*}
    [Fintype m₁] [Fintype m₂] [Fintype n₁] [Fintype n₂] [DecidableEq m₁] [DecidableEq m₂]
    [DecidableEq n₁] [DecidableEq n₂] {f₁₁ : E → Matrix m₁ n₁ ℝ} {f₁₂ : E → Matrix m₁ n₂ ℝ}
    {f₂₁ : E → Matrix m₂ n₁ ℝ} {f₂₂ : E → Matrix m₂ n₂ ℝ} {x : E}
    (h₁₁ : AnalyticAt ℝ f₁₁ x) (h₁₂ : AnalyticAt ℝ f₁₂ x) (h₂₁ : AnalyticAt ℝ f₂₁ x)
    (h₂₂ : AnalyticAt ℝ f₂₂ x) :
    AnalyticAt ℝ (fun y => Matrix.fromBlocks (f₁₁ y) (f₁₂ y) (f₂₁ y) (f₂₂ y)) x :=
  AnalyticAt.fromBlocks h₁₁ h₁₂ h₂₁ h₂₂

/-- The column and row constructions, and one projection, on the same footing. -/
example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m n k : Type*} [Fintype m]
    [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq n] [DecidableEq k]
    {f : E → Matrix m n ℝ} {g : E → Matrix m k ℝ} {x : E}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => Matrix.fromCols (f y) (g y)) x ∧
      AnalyticAt ℝ (fun y => (Matrix.fromCols (f y) (g y)).toCols₁) x :=
  ⟨AnalyticAt.fromCols hf hg, AnalyticAt.toCols₁ (AnalyticAt.fromCols hf hg)⟩

/-! ## The chart's two nonlinear ingredients

Everything in `Ψ` is polynomial except `A₁₁⁻¹` and `P_{top}⁻¹`. These are the only places a
hypothesis is needed, and they are print's two denominators. -/

/-- `A₁₁⁻¹` is analytic exactly where print says: `det A₁₁ ≠ 0`. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] {x : PairSpace ρ σ τ η ν π}
    (h : (x.1.toBlocks₁₁).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (w.1.toBlocks₁₁)⁻¹) x :=
  analyticAt_A11_inv h

/-- Print's `X = A₁₁⁻¹A₁₂`, analytic on the same locus. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq ν]
    {x : PairSpace ρ σ τ η ν π} (h : (x.1.toBlocks₁₁).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂) x :=
  analyticAt_elimX h

/-- Print's `R(D)`, analytic where `det P_{top}(D) ≠ 0`. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq π] {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ} {x : PairSpace ρ σ τ η ν π}
    (h : (elimPtop J (elimDOf x.1 x.2)).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      elimR (elimPtop J (elimDOf w.1 w.2)) (elimPbot J (elimDOf w.1 w.2))) x :=
  analyticAt_elimR h

/-- **Print's gauge `L(A)⁻¹` is analytic everywhere** — it is polynomial in the entries, with
no denominator at all. Print's `L(A)` itself is the one with the `A₁₁⁻¹`. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      elimLinv w.1.toBlocks₁₁ w.1.toBlocks₂₁) x :=
  analyticAt_elimLinv x

/-! ## The conclusion -/

/-- **All nine blocks of `Ψ` are analytic on the chart domain.** The statement takes exactly
one hypothesis — membership in `ElimChartDomain` — which is print's two determinant conditions
and nothing more. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {x : PairSpace ρ σ τ η ν π} (hx : x ∈ ElimChartDomain ρ σ τ η ν π J) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).U) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).Tp) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).Y0) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).SZ) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).A11) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).A21) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).XP) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).D) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).Y1) x :=
  analyticAt_elimPsi_blocks J hx

/-- **`T′` is the only block that mixes the two hypotheses**, because it is the only one built
from both `A₁₁⁻¹` (through `X` and `S`) and `P_{top}⁻¹` (through `Y₁`). That is print's shear,
and it is where the gauge and residual data meet. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ}
    {x : PairSpace ρ σ τ η ν π} (hA : (x.1.toBlocks₁₁).det ≠ 0)
    (hP : (elimPtop J (elimDOf x.1 x.2)).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).Tp) x :=
  analyticAt_psi_Tp hA hP

/-! ## The domain is open, and `Ψ` is analytic on it as one map -/

/-- **Print's open set is open.** This is `HasEliminationChartAt`'s `IsOpen O` clause, before
transport: the intersection of the nonvanishing loci of the chart's two denominators. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    IsOpen (ElimChartDomain ρ σ τ η ν π J) :=
  isOpen_ElimChartDomain J

/-- Both denominators are continuous, which is what openness rests on — and they are
continuous *because* they are analytic, so no separate estimate is needed. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Continuous (fun w : PairSpace ρ σ τ η ν π => (w.1.toBlocks₁₁).det) ∧
      Continuous (fun w : PairSpace ρ σ τ η ν π => (elimPtop J (elimDOf w.1 w.2)).det) :=
  ⟨continuous_A11_det, continuous_Ptop_det J⟩

/-- **`Ψ` is analytic on the chart domain, as a single map into a normed space.** Together with
openness this is the `AnalyticOnNhd ℝ Ψ O` clause, before transport into `ChartSpace`. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    AnalyticOnNhd ℝ (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2)
      (ElimChartDomain ρ σ τ η ν π J) :=
  analyticOnNhd_elimPsiProd J

/-- The product form is the same data as the structure, so Step 5's round trips carry over
without restating them. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype π]
    [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq π]
    (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (A : Matrix ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ((ρ ⊕ σ) ⊕ ν) ℝ)
    (B : Matrix ((ρ ⊕ τ) ⊕ π) ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ℝ) :
    elimCoordsEquivProd.symm (elimPsiProd J A B) = elimPsi J A B :=
  elimPsiProd_eq J A B


/-! ## `Φ` is analytic, and on a larger set than `Ψ`

Print states the chart as "analytic with analytic inverse on
`{det A₁₁ ≠ 0} ∩ {det P_{top}(D) ≠ 0}`". That is true, but not sharp for the inverse: print's
`R(D)⁻¹ = (P_{top} 0 ; P_{bot} I)` is polynomial, so `Φ` never divides by `det P_{top}`. Its only
denominator is the `A₁₁⁻¹` inside `L(A)`. -/

/-- **`Φ` is analytic on the whole of `{det A₁₁ ≠ 0}`** — one of print's two conditions, not
both. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    AnalyticOnNhd ℝ (elimPhiProd J)
      {c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} :=
  analyticOnNhd_elimPhiProd J

/-- **`Φ`'s first component needs no hypothesis at all.** Print's `A` is polynomial in the
chart coordinates: the `A₁₁` in `A₁₂ = A₁₁X` is a coordinate, not an inverse. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (c : ElimCoordsProd ρ σ τ η ν π) :
    AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => (elimPhiProd J d).1) c :=
  analyticAt_elimPhiProd_fst J c

/-- The nine projections of the product form are analytic, which is what makes the two
components above composites of the toolkit. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] (c : ElimCoordsProd ρ σ τ η ν π) :
    AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => d.2.2.2.2.1) c :=
  (analyticAt_coords c).2.2.2.2.1

/-- `Φ` on the product form agrees with `Φ` on the structure, so Step 5's round trips apply to
it unchanged. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype π]
    [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq π]
    (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) (c : ElimCoords ρ σ τ η ν π) :
    elimPhiProd J (elimCoordsEquivProd c) = elimPhi J c :=
  elimPhiProd_apply J c


/-! ## The image is open, and the chart is a bijection of open sets -/

/-- **`O'` is open.** Not from invariance of domain: the second round trip `Ψ ∘ Φ = id` holds
on an explicitly open coordinate set, so `O'` is an intersection of open sets. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    IsOpen (ElimChartImage ρ σ τ η ν π J) :=
  isOpen_ElimChartImage J

/-- And it really is the image of `O`, so the two descriptions of `O'` agree. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2) ''
        ElimChartDomain ρ σ τ η ν π J = ElimChartImage ρ σ τ η ν π J :=
  elimPsiProd_image J

/-- **The chart is a bijection between two open sets**, `Ψ : O ⟶ O'`. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Set.BijOn (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2)
      (ElimChartDomain ρ σ τ η ν π J) (ElimChartImage ρ σ τ η ν π J) :=
  bijOn_elimPsiProd J

/-- **Every topological and analytic clause of `HasEliminationChartAt`, in one place**, in the
`Sum`-indexed setting: both sets open, `Ψ` a bijection between them, and `Ψ`, `Φ` analytic on
their domains. What is not here is the transport into `ParamSpace`/`ChartSpace`, print's
base-point normalization, and the identification of `rrrLoss` with Step 6's Frobenius
expression. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    IsOpen (ElimChartDomain ρ σ τ η ν π J) ∧
      IsOpen (ElimChartImage ρ σ τ η ν π J) ∧
      Set.BijOn (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2)
        (ElimChartDomain ρ σ τ η ν π J) (ElimChartImage ρ σ τ η ν π J) ∧
      AnalyticOnNhd ℝ (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2)
        (ElimChartDomain ρ σ τ η ν π J) ∧
      AnalyticOnNhd ℝ (elimPhiProd J)
        {c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} :=
  ⟨isOpen_ElimChartDomain J, isOpen_ElimChartImage J, bijOn_elimPsiProd J,
    analyticOnNhd_elimPsiProd J, analyticOnNhd_elimPhiProd J⟩


/-! ## Normalizing at the base point

`HasEliminationChartAt` asks for `Ψ (A*, B*) = 0`. Print gets it by carrying `A₁₁ − I_a` and
`D − D*`; here the chart carries `A₁₁` and `D`, and the difference is a translation. -/

/-- **Translation costs nothing**, so the normalization is available at any base point without
computing `Ψ` there first. -/
example {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
    [NormedSpace ℝ F] {f : E → F} {s : Set E} {t : Set F} (w₀ : E) (hw₀ : w₀ ∈ s)
    (hs : IsOpen s) (ht : IsOpen t) (hbij : Set.BijOn f s t) (hf : AnalyticOnNhd ℝ f s) :
    IsOpen s ∧ IsOpen ((fun y => y - f w₀) '' t) ∧ w₀ ∈ s ∧
      Set.BijOn (fun x => f x - f w₀) s ((fun y => y - f w₀) '' t) ∧
      AnalyticOnNhd ℝ (fun x => f x - f w₀) s ∧ (fun x => f x - f w₀) w₀ = 0 :=
  normalized_chart w₀ hw₀ hs ht hbij hf

/-- **The elimination chart, normalized.** Open domain, open image, bijection, analytic, base
point to `0`. The one clause of `HasEliminationChartAt` still outside this list is the
comparability with `2K`, which is Steps 6 and 7 — both proved — stated over `rrrLoss` in
`Fin`-indexed coordinates rather than over `frobeniusSq` in these. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {w₀ : PairSpace ρ σ τ η ν π} (hw₀ : w₀ ∈ ElimChartDomain ρ σ τ η ν π J) :
    (elimPsiProd J w₀.1 w₀.2 - elimPsiProd J w₀.1 w₀.2 : ElimCoordsProd ρ σ τ η ν π) = 0 :=
  (normalized_elimChart J hw₀).2.2.2.2.2

/-- And the normalized chart is still a bijection between two open sets. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {w₀ : PairSpace ρ σ τ η ν π} (hw₀ : w₀ ∈ ElimChartDomain ρ σ τ η ν π J) :
    Set.BijOn (fun w : PairSpace ρ σ τ η ν π =>
        elimPsiProd J w.1 w.2 - elimPsiProd J w₀.1 w₀.2)
      (ElimChartDomain ρ σ τ η ν π J)
      ((fun y => y - elimPsiProd J w₀.1 w₀.2) '' ElimChartImage ρ σ τ η ν π J) :=
  (normalized_elimChart J hw₀).2.2.2.1


/-! ## Transport

Everything above lives over `Sum` index types; `HasEliminationChartAt` quantifies over
`ParamSpace`/`ChartSpace`. A chart survives conjugation by continuous linear equivalences, so
the remaining work is the construction of the two equivalences and nothing else. -/

/-- **A chart survives transport**: every clause is preserved by conjugating with continuous
linear equivalences on the source and target. -/
example {E E' F F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F']
    [NormedSpace ℝ F'] (e : E ≃L[ℝ] E') (g : F ≃L[ℝ] F') {O : Set E} {O' : Set F}
    {Ψ : E → F} {Φ : F → E} {w₀ : E} (hO : IsOpen O) (hO' : IsOpen O') (hw₀ : w₀ ∈ O)
    (hbij : Set.BijOn Ψ O O') (hinv : Set.InvOn Φ Ψ O O')
    (hΨ : AnalyticOnNhd ℝ Ψ O) (hΦ : AnalyticOnNhd ℝ Φ O') (hzero : Ψ w₀ = 0) :
    IsOpen (e '' O) ∧ IsOpen (g '' O') ∧ e w₀ ∈ e '' O ∧
      Set.BijOn (fun x => g (Ψ (e.symm x))) (e '' O) (g '' O') ∧
      Set.InvOn (fun y => e (Φ (g.symm y))) (fun x => g (Ψ (e.symm x))) (e '' O) (g '' O') ∧
      AnalyticOnNhd ℝ (fun x => g (Ψ (e.symm x))) (e '' O) ∧
      AnalyticOnNhd ℝ (fun y => e (Φ (g.symm y))) (g '' O') ∧
      (fun x => g (Ψ (e.symm x))) (e w₀) = 0 :=
  chart_transport e g hO hO' hw₀ hbij hinv hΨ hΦ hzero

/-- The two ingredients transport needs on their own: openness is preserved because a
continuous linear equivalence is a homeomorphism, analyticity because it is analytic with
analytic inverse. -/
example {E E' F F' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F']
    [NormedSpace ℝ F'] (e : E ≃L[ℝ] E') (g : F ≃L[ℝ] F') {O : Set E} {Ψ : E → F}
    (hO : IsOpen O) (hΨ : AnalyticOnNhd ℝ Ψ O) :
    IsOpen (e '' O) ∧ AnalyticOnNhd ℝ (fun x => g (Ψ (e.symm x))) (e '' O) :=
  ⟨isOpen_image_clm e hO, analyticOnNhd_conj e g hΨ⟩


/-! ## The coordinate equivalence

The second of the two equivalences `chart_transport` consumes, at the witness stratum
`(M, N, H, r, a, b) = (3, 3, 4, 1, 2, 2)`, where `q = 8` and `g = 14`. -/

/-- **`ElimCoordsProd` is `ChartSpace q p h n g`.** Nine blocks reindexed, regrouped into
`ChartSpace`'s four components, and packed — all as one continuous linear equivalence. -/
noncomputable example :
    ElimCoordsProd (Fin 1) (Fin (2 - 1)) (Fin (2 - 1)) (Fin (elimH 4 1 2 2))
        (Fin (elimN 3 2)) (Fin (elimP 3 2)) ≃L[ℝ]
      ChartSpace (elimQ 3 3 2 2) (elimP 3 2) (elimH 4 1 2 2) (elimN 3 2)
        (elimGauge 3 3 4 1 2 2) :=
  elimCoordEquiv (M := 3) (N := 3) (H := 4) (r := 1) (a := 2) (b := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- The target really is `ChartSpace 8 1 1 1 14`, so the equivalence lands where
`HasEliminationChartAt` quantifies. -/
example : ChartSpace (elimQ 3 3 2 2) (elimP 3 2) (elimH 4 1 2 2) (elimN 3 2)
      (elimGauge 3 3 4 1 2 2) =
    (EuclideanSpace ℝ (Fin 8) × Matrix (Fin 1) (Fin 1) ℝ × Matrix (Fin 1) (Fin 1) ℝ ×
      EuclideanSpace ℝ (Fin 14)) := rfl

/-- Being a continuous linear equivalence, it is analytic — which is what `chart_transport`
needs of it. -/
example (s : Set (ElimCoordsProd (Fin 1) (Fin (2 - 1)) (Fin (2 - 1)) (Fin (elimH 4 1 2 2))
      (Fin (elimN 3 2)) (Fin (elimP 3 2)))) :
    AnalyticOnNhd ℝ (elimCoordEquiv (M := 3) (N := 3) (H := 4) (r := 1) (a := 2) (b := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) s :=
  analyticOnNhd_elimCoordEquiv (M := 3) (N := 3) (H := 4) (r := 1) (a := 2) (b := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) s

/-- **`g` as the right-associated sum of the five gauge blocks**, the form the packing needs:
`a² + ((H−a)a + ((a−r)n + (M(b−r) + bh)))`. -/
example (M N H r a b : ℕ) :
    elimGauge M N H r a b =
      a * a + ((H - a) * a + ((a - r) * elimN N a + (M * (b - r) + b * elimH H r a b))) :=
  elimGauge_eq_add' M N H r a b

/-- **Both equivalences, at the same stratum.** With these two, `chart_transport` carries every
clause proved over `Sum` index types to `ParamSpace 3 3 4` and `ChartSpace 8 1 1 1 14`. -/
noncomputable example :
    ((Matrix ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) ℝ ×
        Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) ℝ) ≃L[ℝ]
      ParamSpace 3 3 4) ×
    (ElimCoordsProd (Fin 1) (Fin (2 - 1)) (Fin (2 - 1)) (Fin (elimH 4 1 2 2))
        (Fin (elimN 3 2)) (Fin (elimP 3 2)) ≃L[ℝ]
      ChartSpace (elimQ 3 3 2 2) (elimP 3 2) (elimH 4 1 2 2) (elimN 3 2)
        (elimGauge 3 3 4 1 2 2)) :=
  ⟨elimParamEquiv (M := 3) (N := 3) (H := 4) (r := 1) (a := 2) (b := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num),
    elimCoordEquiv (M := 3) (N := 3) (H := 4) (r := 1) (a := 2) (b := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)⟩


/-! ## Print's `N₀`, as an open condition

Step 7 says "take `O` to be the preimage under `Ψ` of a small open box inside `N₀`", so what is
needed is an open set *inside* the operator-norm region, not that the region itself be open in
a norm this development does not instantiate. The Frobenius ball is such a set. -/

/-- **Frobenius dominates the operator norm**, by Cauchy–Schwarz row by row. -/
example {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℝ) :
    IsOpNormSqBound A (frobeniusSq A) :=
  isOpNormSqBound_frobeniusSq A

/-- And the Frobenius ball is open, because `frobeniusSq` is a polynomial in the entries. -/
example {ι κ : Type*} [Fintype ι] [Fintype κ] (c : ℝ) :
    IsOpen {A : Matrix ι κ ℝ | frobeniusSq A < c} :=
  isOpen_frobeniusSq_lt c

/-- **Print's neighborhood is open.** -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    IsOpen (ElimChartNbhd ρ σ τ η ν π J) :=
  isOpen_ElimChartNbhd J

/-- **Step 7's three hypotheses hold there**, each a Frobenius bound promoted to an
operator-norm bound. No operator norm is ever computed. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {w : PairSpace ρ σ τ η ν π} (hw : w ∈ ElimChartNbhd ρ σ τ η ν π J) :
    IsOpNormSqBound (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂) (1 / 4) ∧
      IsOpNormSqBound (elimPtop J (elimDOf w.1 w.2) - 1) (1 / 4) ∧
      IsOpNormSqBound (elimPbot J (elimDOf w.1 w.2)) (1 / 4) :=
  opNormSqBounds_of_mem_ElimChartNbhd J hw

/-- **Lemma 5.4 applies there**, with print's two constants on print's two matrices — the last
input Step 7 needs beyond Lemma 5.2. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν]
    [Fintype π] [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η]
    [DecidableEq ν] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {w : PairSpace ρ σ τ η ν π} (hw : w ∈ ElimChartNbhd ρ σ τ η ν π J) :
    IsOpNormSqBound (elimR (elimPtop J (elimDOf w.1 w.2))
        (elimPbot J (elimDOf w.1 w.2))) 6 ∧
      IsOpNormSqBound (elimRinv (elimPtop J (elimDOf w.1 w.2))
        (elimPbot J (elimDOf w.1 w.2))) 3 :=
  elim_opNormSqBounds_on_nbhd J hw


end AISafetyAtlas.Examples.SingularLearning
