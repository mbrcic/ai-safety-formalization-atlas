module

public import AISafetyAtlas.SingularLearning.EliminationChart
public import AISafetyAtlas.SingularLearning.ChartTransport
public import AISafetyAtlas.SingularLearning.MatrixAnalytic

/-!
# Analyticity of the elimination chart's ingredients

`HasEliminationChartAt` asks for four things beyond the algebra: that `Ψ` and `Φ` be
bijections between open sets, and that both be `AnalyticOnNhd`. Steps 1–7 supply the algebra
(`EliminationChart.lean`) and `ChartTransport.lean` supplies the reindexing. This module
supplies the analyticity.

## The toolkit

`MatrixAnalytic.lean` proves that entries, determinants, adjugates and inverses are analytic,
and that a matrix-valued map with analytic entries is analytic. What Step 5 additionally needs
is closure of analyticity under the *block* constructions it is written in — multiplication,
`fromBlocks`, `fromCols`, `fromRows`, and the corresponding projections — and that is what is
built here. Every one of them is either linear or bilinear in the entries, so each proof is
`analyticAt_matrix_of_entries` applied to a finite sum of products of entries.

Once these exist, each of the nine blocks of `elimPsi` is a composite of them and of the two
matrix inverses, so its analyticity on `ElimChartDomain` is mechanical. The two inverses are
the only genuinely nonlinear ingredients in the whole chart, exactly as print's "identities of
rational functions whose only denominators are `det A₁₁` and `det P_{top}`" says.

## Why the `Prod` projections appear

`Ψ` is a function of the pair `(A, B)`, so every ingredient below is stated as a function on
`Matrix … × Matrix …`. The two projections are continuous linear, hence analytic, and
composing with them is how a statement about `A` alone becomes a statement about `w`.

## What is *not* here

The analyticity of `Ψ` **as a map into `ChartSpace`** is not stated, because `ElimCoords` is a
plain structure with no normed-space instance and `ChartSpace` is reached only through
`ChartTransport`'s packings. What is proved is that each of the nine coordinate blocks is
analytic on the chart domain, which is what any such assembly consumes. The assembly itself
is `ChartAssembly.lean`, where `isEliminationChart_of_feasible` inhabits `IsEliminationChart`
at every feasible stratum.
-/

namespace AISafetyAtlas.SingularLearning

open scoped Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

section Toolkit

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {m n k : Type*} [Fintype m] [Fintype n] [Fintype k]

/-- **Matrix multiplication preserves analyticity.** Entry `(i, j)` of `f y * g y` is the
finite sum `∑ l, f y i l * g y l j`, a sum of products of analytic scalars. -/
public theorem AnalyticAt.matrix_mul [DecidableEq m] [DecidableEq n]
    {f : E → Matrix m k ℝ} {g : E → Matrix k n ℝ} {x : E}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => f y * g y) x := by
  refine analyticAt_matrix_of_entries fun i j => ?_
  have h : (fun y => (f y * g y) i j) = fun y => ∑ l, f y i l * g y l j := by
    funext y
    rw [Matrix.mul_apply]
  rw [h]
  exact Finset.analyticAt_fun_sum _ fun l _ =>
    (analyticAt_entry_comp hf i l).mul (analyticAt_entry_comp hg l j)

/-- Matrix multiplication preserves analyticity on a set. -/
public theorem AnalyticOnNhd.matrix_mul [DecidableEq m] [DecidableEq n]
    {f : E → Matrix m k ℝ} {g : E → Matrix k n ℝ} {s : Set E}
    (hf : AnalyticOnNhd ℝ f s) (hg : AnalyticOnNhd ℝ g s) :
    AnalyticOnNhd ℝ (fun y => f y * g y) s :=
  fun x hx => AnalyticAt.matrix_mul (hf x hx) (hg x hx)

/-- **`Matrix.fromCols` preserves analyticity.** Each entry of the result is an entry of one of
the two arguments. -/
public theorem AnalyticAt.fromCols [DecidableEq m] [DecidableEq n] [DecidableEq k]
    {f : E → Matrix m n ℝ} {g : E → Matrix m k ℝ} {x : E}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => Matrix.fromCols (f y) (g y)) x := by
  refine analyticAt_matrix_of_entries fun i j => ?_
  rcases j with j | j
  · simpa using analyticAt_entry_comp hf i j
  · simpa using analyticAt_entry_comp hg i j

/-- **`Matrix.fromRows` preserves analyticity.** -/
public theorem AnalyticAt.fromRows [DecidableEq m] [DecidableEq n] [DecidableEq k]
    {f : E → Matrix m k ℝ} {g : E → Matrix n k ℝ} {x : E}
    (hf : AnalyticAt ℝ f x) (hg : AnalyticAt ℝ g x) :
    AnalyticAt ℝ (fun y => Matrix.fromRows (f y) (g y)) x := by
  refine analyticAt_matrix_of_entries fun i j => ?_
  rcases i with i | i
  · simpa using analyticAt_entry_comp hf i j
  · simpa using analyticAt_entry_comp hg i j

/-- **`Matrix.fromBlocks` preserves analyticity**, the shape `elimL`, `elimR` and their
inverses are written in. -/
public theorem AnalyticAt.fromBlocks {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂]
    [Fintype n₁] [Fintype n₂] [DecidableEq m₁] [DecidableEq m₂] [DecidableEq n₁]
    [DecidableEq n₂] {f₁₁ : E → Matrix m₁ n₁ ℝ} {f₁₂ : E → Matrix m₁ n₂ ℝ}
    {f₂₁ : E → Matrix m₂ n₁ ℝ} {f₂₂ : E → Matrix m₂ n₂ ℝ} {x : E}
    (h₁₁ : AnalyticAt ℝ f₁₁ x) (h₁₂ : AnalyticAt ℝ f₁₂ x) (h₂₁ : AnalyticAt ℝ f₂₁ x)
    (h₂₂ : AnalyticAt ℝ f₂₂ x) :
    AnalyticAt ℝ (fun y => Matrix.fromBlocks (f₁₁ y) (f₁₂ y) (f₂₁ y) (f₂₂ y)) x := by
  refine analyticAt_matrix_of_entries fun i j => ?_
  rcases i with i | i <;> rcases j with j | j
  · simpa using analyticAt_entry_comp h₁₁ i j
  · simpa using analyticAt_entry_comp h₁₂ i j
  · simpa using analyticAt_entry_comp h₂₁ i j
  · simpa using analyticAt_entry_comp h₂₂ i j

/-- **The row and column projections preserve analyticity.** `toRows₁` is a submatrix, hence
entrywise a coordinate of the argument. -/
public theorem AnalyticAt.toRows₁ [DecidableEq m] [DecidableEq n] [DecidableEq k]
    {f : E → Matrix (m ⊕ n) k ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).toRows₁) x :=
  analyticAt_matrix_of_entries fun i j => analyticAt_entry_comp hf (Sum.inl i) j

public theorem AnalyticAt.toRows₂ [DecidableEq m] [DecidableEq n] [DecidableEq k]
    {f : E → Matrix (m ⊕ n) k ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).toRows₂) x :=
  analyticAt_matrix_of_entries fun i j => analyticAt_entry_comp hf (Sum.inr i) j

public theorem AnalyticAt.toCols₁ [DecidableEq m] [DecidableEq n] [DecidableEq k]
    {f : E → Matrix k (m ⊕ n) ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).toCols₁) x :=
  analyticAt_matrix_of_entries fun i j => analyticAt_entry_comp hf i (Sum.inl j)

public theorem AnalyticAt.toCols₂ [DecidableEq m] [DecidableEq n] [DecidableEq k]
    {f : E → Matrix k (m ⊕ n) ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).toCols₂) x :=
  analyticAt_matrix_of_entries fun i j => analyticAt_entry_comp hf i (Sum.inr j)

/-- The four block projections of a `Sum`-by-`Sum` matrix preserve analyticity. -/
public theorem AnalyticAt.toBlocks₁₁ {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂]
    [Fintype n₁] [Fintype n₂] [DecidableEq m₁] [DecidableEq n₁]
    {f : E → Matrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).toBlocks₁₁) x :=
  analyticAt_matrix_of_entries fun i j => analyticAt_entry_comp hf (Sum.inl i) (Sum.inl j)

public theorem AnalyticAt.toBlocks₁₂ {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂]
    [Fintype n₁] [Fintype n₂] [DecidableEq m₁] [DecidableEq n₂]
    {f : E → Matrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).toBlocks₁₂) x :=
  analyticAt_matrix_of_entries fun i j => analyticAt_entry_comp hf (Sum.inl i) (Sum.inr j)

public theorem AnalyticAt.toBlocks₂₁ {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂]
    [Fintype n₁] [Fintype n₂] [DecidableEq m₂] [DecidableEq n₁]
    {f : E → Matrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).toBlocks₂₁) x :=
  analyticAt_matrix_of_entries fun i j => analyticAt_entry_comp hf (Sum.inr i) (Sum.inl j)

public theorem AnalyticAt.toBlocks₂₂ {m₁ m₂ n₁ n₂ : Type*} [Fintype m₁] [Fintype m₂]
    [Fintype n₁] [Fintype n₂] [DecidableEq m₂] [DecidableEq n₂]
    {f : E → Matrix (m₁ ⊕ m₂) (n₁ ⊕ n₂) ℝ} {x : E} (hf : AnalyticAt ℝ f x) :
    AnalyticAt ℝ (fun y => (f y).toBlocks₂₂) x :=
  analyticAt_matrix_of_entries fun i j => analyticAt_entry_comp hf (Sum.inr i) (Sum.inr j)

end Toolkit

/-! ## The chart's ingredients are analytic

The two projections `w ↦ w.1` and `w ↦ w.2` are continuous linear, hence analytic, and
everything else is a composite of the toolkit above with the two matrix inverses. -/

section Ingredients

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]

/-- The parameter pair, as the domain of every ingredient below. -/
public abbrev PairSpace (ρ σ τ η ν π : Type*) : Type _ :=
  Matrix ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ((ρ ⊕ σ) ⊕ ν) ℝ ×
    Matrix ((ρ ⊕ τ) ⊕ π) ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ℝ

public theorem analyticAt_fst (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => w.1) x :=
  (ContinuousLinearMap.fst ℝ _ _).analyticAt x

public theorem analyticAt_snd (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => w.2) x :=
  (ContinuousLinearMap.snd ℝ _ _).analyticAt x

variable [DecidableEq ρ] [DecidableEq σ]

/-- `A₁₁` is analytic in the pair. -/
public theorem analyticAt_A11 (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => w.1.toBlocks₁₁) x :=
  AnalyticAt.toBlocks₁₁ (analyticAt_fst x)

/-- `A₁₁⁻¹` is analytic wherever `det A₁₁ ≠ 0` — one of the chart's two denominators. -/
public theorem analyticAt_A11_inv {x : PairSpace ρ σ τ η ν π}
    (h : (x.1.toBlocks₁₁).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (w.1.toBlocks₁₁)⁻¹) x :=
  analyticAt_inv_comp (analyticAt_A11 x) h

variable [DecidableEq τ] [DecidableEq η]

/-- `A₂₁` is analytic in the pair. -/
public theorem analyticAt_A21 (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => w.1.toBlocks₂₁) x :=
  AnalyticAt.toBlocks₂₁ (analyticAt_fst x)

/-- **Print's `L(A)⁻¹ = (A₁₁ 0 ; A₂₁ I)` is analytic** — it is polynomial, so everywhere. -/
public theorem analyticAt_elimLinv (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => elimLinv w.1.toBlocks₁₁ w.1.toBlocks₂₁) x :=
  AnalyticAt.fromBlocks (analyticAt_A11 x) analyticAt_const (analyticAt_A21 x)
    analyticAt_const

variable [DecidableEq ν]

omit [DecidableEq τ] [DecidableEq η] in
/-- **Print's `X = A₁₁⁻¹A₁₂` is analytic** on the nonvanishing locus of `det A₁₁`. -/
public theorem analyticAt_elimX {x : PairSpace ρ σ τ η ν π}
    (h : (x.1.toBlocks₁₁).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂) x :=
  AnalyticAt.matrix_mul (analyticAt_A11_inv h)
    (AnalyticAt.toBlocks₁₂ (analyticAt_fst x))

/-- **Print's Schur complement `S = A₂₂ − A₂₁A₁₁⁻¹A₁₂` is analytic.** -/
public theorem analyticAt_elimSchur {x : PairSpace ρ σ τ η ν π}
    (h : (x.1.toBlocks₁₁).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      elimSchur w.1.toBlocks₁₁ w.1.toBlocks₁₂ w.1.toBlocks₂₁ w.1.toBlocks₂₂) x := by
  have h1 : AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => w.1.toBlocks₂₂) x :=
    AnalyticAt.toBlocks₂₂ (analyticAt_fst x)
  have h2 : AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      w.1.toBlocks₂₁ * (w.1.toBlocks₁₁)⁻¹ * w.1.toBlocks₁₂) x :=
    AnalyticAt.matrix_mul
      (AnalyticAt.matrix_mul (analyticAt_A21 x) (analyticAt_A11_inv h))
      (AnalyticAt.toBlocks₁₂ (analyticAt_fst x))
  exact AnalyticAt.sub h1 h2

variable [DecidableEq π]

omit [DecidableEq ν] in
/-- **Print's gauged `B̄ = BL(A)⁻¹` is analytic.** -/
public theorem analyticAt_elimBbarOf (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => elimBbarOf w.1 w.2) x :=
  AnalyticAt.matrix_mul (analyticAt_snd x) (analyticAt_elimLinv x)

omit [DecidableEq ν] in
/-- Print's `D`, the second column block of `B̄`, is analytic. -/
public theorem analyticAt_elimDOf (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => elimDOf w.1 w.2) x :=
  AnalyticAt.toCols₁ (AnalyticAt.toCols₂ (analyticAt_elimBbarOf x))

omit [DecidableEq ν] in
/-- Print's `Y`, the third column block of `B̄`, is analytic. -/
public theorem analyticAt_elimYOf (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => elimYOf w.1 w.2) x :=
  AnalyticAt.toCols₂ (AnalyticAt.toCols₂ (analyticAt_elimBbarOf x))

omit [DecidableEq ν] in
/-- `P_{top}(D)` is analytic, being a row projection of `(J | D)`. -/
public theorem analyticAt_elimPtop (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => elimPtop J (elimDOf w.1 w.2)) x :=
  AnalyticAt.toRows₁ (AnalyticAt.fromCols analyticAt_const (analyticAt_elimDOf x))

omit [DecidableEq ν] in
/-- `P_{bot}(D)` is analytic. -/
public theorem analyticAt_elimPbot (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => elimPbot J (elimDOf w.1 w.2)) x :=
  AnalyticAt.toRows₂ (AnalyticAt.fromCols analyticAt_const (analyticAt_elimDOf x))

omit [DecidableEq ν] in
/-- **Print's `R(D) = (P_{top}⁻¹ 0 ; −P_{bot} P_{top}⁻¹ I)` is analytic** on the nonvanishing locus
of `det P_{top}` — the chart's second and last denominator. -/
public theorem analyticAt_elimR {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ} {x : PairSpace ρ σ τ η ν π}
    (h : (elimPtop J (elimDOf x.1 x.2)).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      elimR (elimPtop J (elimDOf w.1 w.2)) (elimPbot J (elimDOf w.1 w.2))) x := by
  have hinv : AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      (elimPtop J (elimDOf w.1 w.2))⁻¹) x :=
    analyticAt_inv_comp (analyticAt_elimPtop J x) h
  exact AnalyticAt.fromBlocks hinv analyticAt_const
    (AnalyticAt.neg (AnalyticAt.matrix_mul (analyticAt_elimPbot J x) hinv)) analyticAt_const

omit [DecidableEq ν] in
/-- **Print's `R(D)Y`, whose two row blocks are `Y₁` and `Y₀`, is analytic.** -/
public theorem analyticAt_elimRYOf {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ} {x : PairSpace ρ σ τ η ν π}
    (h : (elimPtop J (elimDOf x.1 x.2)).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => elimRYOf J w.1 w.2) x :=
  AnalyticAt.matrix_mul (analyticAt_elimR h) (analyticAt_elimYOf x)

/-! ### The nine blocks of `Ψ`

Each is now a composite of the ingredients above. Print's `Ψ` is analytic on
`ElimChartDomain` block by block, and the only hypotheses used are the two determinants. -/

omit [DecidableEq ν] in
/-- Print's `U = B_I − C_I`. -/
public theorem analyticAt_psi_U (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) (x : PairSpace ρ σ τ η ν π) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      (elimBbarOf w.1 w.2).toCols₁ - elimCI J σ) x :=
  AnalyticAt.sub (AnalyticAt.toCols₁ (analyticAt_elimBbarOf x)) analyticAt_const

omit [DecidableEq ν] in
/-- Print's `Y₀`. -/
public theorem analyticAt_psi_Y0 {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ} {x : PairSpace ρ σ τ η ν π}
    (h : (elimPtop J (elimDOf x.1 x.2)).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimRYOf J w.1 w.2).toRows₂) x :=
  AnalyticAt.toRows₂ (analyticAt_elimRYOf h)

omit [DecidableEq ν] in
/-- Print's `Y₁`. -/
public theorem analyticAt_psi_Y1 {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ} {x : PairSpace ρ σ τ η ν π}
    (h : (elimPtop J (elimDOf x.1 x.2)).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimRYOf J w.1 w.2).toRows₁) x :=
  AnalyticAt.toRows₁ (analyticAt_elimRYOf h)

omit [DecidableEq π] in
/-- Print's `S_Z`. -/
public theorem analyticAt_psi_SZ {x : PairSpace ρ σ τ η ν π} (h : (x.1.toBlocks₁₁).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      (elimSchur w.1.toBlocks₁₁ w.1.toBlocks₁₂ w.1.toBlocks₂₁ w.1.toBlocks₂₂).toRows₂) x :=
  AnalyticAt.toRows₂ (analyticAt_elimSchur h)

omit [DecidableEq τ] [DecidableEq η] [DecidableEq π] in
/-- Print's `X_P`. -/
public theorem analyticAt_psi_XP {x : PairSpace ρ σ τ η ν π} (h : (x.1.toBlocks₁₁).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂).toRows₂) x :=
  AnalyticAt.toRows₂ (analyticAt_elimX h)

/-- Print's `T′ = T + Y₁ S_Z`, the one block that mixes the gauge and residual data. -/
public theorem analyticAt_psi_Tp {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ} {x : PairSpace ρ σ τ η ν π}
    (hA : (x.1.toBlocks₁₁).det ≠ 0) (hP : (elimPtop J (elimDOf x.1 x.2)).det ≠ 0) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      elimShear (elimRYOf J w.1 w.2).toRows₁
        (elimSchur w.1.toBlocks₁₁ w.1.toBlocks₁₂ w.1.toBlocks₂₁ w.1.toBlocks₂₂).toRows₂
        (elimT (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂).toRows₁
          (elimSchur w.1.toBlocks₁₁ w.1.toBlocks₁₂ w.1.toBlocks₂₁ w.1.toBlocks₂₂).toRows₁))
      x := by
  have hT : AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π =>
      elimT (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂).toRows₁
        (elimSchur w.1.toBlocks₁₁ w.1.toBlocks₁₂ w.1.toBlocks₂₁ w.1.toBlocks₂₂).toRows₁) x :=
    AnalyticAt.fromRows (AnalyticAt.toRows₁ (analyticAt_elimX hA))
      (AnalyticAt.toRows₁ (analyticAt_elimSchur hA))
  exact AnalyticAt.add hT
    (AnalyticAt.matrix_mul (analyticAt_psi_Y1 hP) (analyticAt_psi_SZ hA))

/-- **All nine blocks of `Ψ` are analytic at every point of the chart domain.** The only
hypotheses used are print's two determinants. -/
public theorem analyticAt_elimPsi_blocks (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {x : PairSpace ρ σ τ η ν π} (hx : x ∈ ElimChartDomain ρ σ τ η ν π J) :
    AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).U) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).Tp) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).Y0) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).SZ) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).A11) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).A21) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).XP) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).D) x ∧
      AnalyticAt ℝ (fun w : PairSpace ρ σ τ η ν π => (elimPsi J w.1 w.2).Y1) x := by
  obtain ⟨hA, hP⟩ := hx
  exact ⟨analyticAt_psi_U J x, analyticAt_psi_Tp (IsUnit.ne_zero hA) (IsUnit.ne_zero hP),
    analyticAt_psi_Y0 (IsUnit.ne_zero hP), analyticAt_psi_SZ (IsUnit.ne_zero hA),
    analyticAt_A11 x, analyticAt_A21 x,
    analyticAt_psi_XP (IsUnit.ne_zero hA), analyticAt_elimDOf x,
    analyticAt_psi_Y1 (IsUnit.ne_zero hP)⟩

end Ingredients

/-! ## The chart domain is open, and `Ψ` is analytic on it as a single map

Two things stand between the nine block-analyticity statements above and the `AnalyticOnNhd`
clause of `HasEliminationChartAt`. The domain must be open, and `Ψ` must be a single map into
a space that has a normed structure — `ElimCoords` is a plain structure, so it has none.

Both are handled here. Openness is immediate from analyticity: the two determinants are
analytic, hence continuous, and the domain is the intersection of their nonvanishing loci.
For the second, `elimPsiProd` is `Ψ` written into the nine-fold product of matrix spaces,
which does carry a normed structure, and `elimCoordsEquivProd` identifies it with
`ElimCoords`. Analyticity of `Ψ` as one map is then `AnalyticAt.prod` applied eight times to
the nine blocks. -/

section Domain

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]
variable [DecidableEq ρ] [DecidableEq σ]

/-- `det A₁₁` is continuous in the pair — it is analytic, and analytic maps are continuous. -/
public theorem continuous_A11_det :
    Continuous (fun w : PairSpace ρ σ τ η ν π => (w.1.toBlocks₁₁).det) :=
  continuous_iff_continuousAt.2 fun x =>
    (analyticAt_det_comp (analyticAt_A11 x)).continuousAt

variable [DecidableEq τ] [DecidableEq η] [DecidableEq π]

/-- `det P_{top}(D)` is continuous in the pair. -/
public theorem continuous_Ptop_det (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Continuous (fun w : PairSpace ρ σ τ η ν π =>
      (elimPtop J (elimDOf w.1 w.2)).det) :=
  continuous_iff_continuousAt.2 fun x =>
    (analyticAt_det_comp (analyticAt_elimPtop J x)).continuousAt

/-- **Print's open set really is open.** `ElimChartDomain` is the intersection of the
nonvanishing loci of the chart's two denominators, each the preimage of `{0}ᶜ` under a
continuous map. This is the `IsOpen O` clause of `HasEliminationChartAt`, before transport. -/
public theorem isOpen_ElimChartDomain (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    IsOpen (ElimChartDomain ρ σ τ η ν π J) := by
  have h : ElimChartDomain ρ σ τ η ν π J =
      (fun w : PairSpace ρ σ τ η ν π => (w.1.toBlocks₁₁).det) ⁻¹' {(0 : ℝ)}ᶜ ∩
        (fun w : PairSpace ρ σ τ η ν π => (elimPtop J (elimDOf w.1 w.2)).det) ⁻¹' {(0 : ℝ)}ᶜ := by
    ext w
    simp only [ElimChartDomain, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff, isUnit_iff_ne_zero]
  rw [h]
  exact (isOpen_compl_singleton.preimage continuous_A11_det).inter
    (isOpen_compl_singleton.preimage (continuous_Ptop_det J))

end Domain

section ProdForm

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]
variable [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq ν]
variable [DecidableEq π]

/-- The nine coordinate blocks as a nested product, in print's order. Unlike `ElimCoords` this
carries a `NormedAddCommGroup` and a `NormedSpace ℝ`, so `AnalyticAt` can be *stated* for a map
into it. -/
public abbrev ElimCoordsProd (ρ σ τ η ν π : Type*) : Type _ :=
  Matrix ((ρ ⊕ τ) ⊕ π) (ρ ⊕ σ) ℝ × Matrix (ρ ⊕ τ) ν ℝ × Matrix π η ℝ × Matrix η ν ℝ ×
    Matrix (ρ ⊕ σ) (ρ ⊕ σ) ℝ × Matrix (τ ⊕ η) (ρ ⊕ σ) ℝ × Matrix σ ν ℝ ×
      Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ × Matrix (ρ ⊕ τ) η ℝ

/-- The nine blocks of `ElimCoords`, read into the product. An equivalence, so nothing is lost
or added: the two presentations are the same data. -/
@[expose] public def elimCoordsEquivProd :
    ElimCoords ρ σ τ η ν π ≃ ElimCoordsProd ρ σ τ η ν π where
  toFun c := (c.U, c.Tp, c.Y0, c.SZ, c.A11, c.A21, c.XP, c.D, c.Y1)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2.1, p.2.2.2.2.1, p.2.2.2.2.2.1,
    p.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.1, p.2.2.2.2.2.2.2.2⟩
  left_inv c := by cases c; rfl
  right_inv p := by rfl

/-- **Print's `Ψ`, as a single map into a normed space.** -/
@[expose] public noncomputable def elimPsiProd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (A : Matrix ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ((ρ ⊕ σ) ⊕ ν) ℝ)
    (B : Matrix ((ρ ⊕ τ) ⊕ π) ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ℝ) : ElimCoordsProd ρ σ τ η ν π :=
  elimCoordsEquivProd (elimPsi J A B)

omit [Fintype ν] [DecidableEq ν] in
/-- The product form carries exactly the same information as the structure: the round trips of
Step 5 transfer verbatim. -/
public theorem elimPsiProd_eq (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (A : Matrix ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ((ρ ⊕ σ) ⊕ ν) ℝ)
    (B : Matrix ((ρ ⊕ τ) ⊕ π) ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ℝ) :
    elimCoordsEquivProd.symm (elimPsiProd J A B) = elimPsi J A B := by
  rw [elimPsiProd, Equiv.symm_apply_apply]

/-- **`Ψ` is analytic on the chart domain, as a single map.** `AnalyticAt.prod` applied eight
times to the nine blocks of `analyticAt_elimPsi_blocks`. Together with
`isOpen_ElimChartDomain` this is the `AnalyticOnNhd ℝ Ψ O` clause of
`HasEliminationChartAt`, before transport into `ChartSpace`. -/
public theorem analyticOnNhd_elimPsiProd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    AnalyticOnNhd ℝ (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2)
      (ElimChartDomain ρ σ τ η ν π J) := by
  intro x hx
  obtain ⟨hU, hTp, hY0, hSZ, hA11, hA21, hXP, hD, hY1⟩ := analyticAt_elimPsi_blocks J hx
  exact AnalyticAt.prod hU (AnalyticAt.prod hTp (AnalyticAt.prod hY0 (AnalyticAt.prod hSZ
    (AnalyticAt.prod hA11 (AnalyticAt.prod hA21 (AnalyticAt.prod hXP
      (AnalyticAt.prod hD hY1)))))))

end ProdForm


/-! ## `Φ` is analytic too, and on a *larger* set than `Ψ`

Print says the chart is "analytic with analytic inverse on
`{det A₁₁ ≠ 0} ∩ {det P_{top}(D) ≠ 0}`". That is correct but not sharp for the inverse, and the
reason is visible once Lemma 5.4's labels are read correctly: print's `R(D)⁻¹ = (P_{top} 0 ;
P_{bot} I)` is *polynomial*, while print's `R(D) = (P_{top}⁻¹ 0 ; −P_{bot} P_{top}⁻¹ I)` is the one
carrying an inverse. `Ψ` applies `R(D)`, so it needs both denominators; `Φ` applies `R(D)⁻¹`,
so it needs only `det A₁₁ ≠ 0`, through `L(A)`.

So `Φ` is analytic on the whole of `{det A₁₁ ≠ 0}`, of which the chart domain is a proper
subset in general. Nothing downstream needs the larger set — the chart is used on
`ElimChartDomain` — but stating the sharp hypothesis is free, and it records which of print's
two conditions each direction actually consumes. -/

section PhiAnalytic

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]
variable [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq ν]
variable [DecidableEq π]

private theorem an_fst {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (x : A × B) :
    AnalyticAt ℝ (fun p : A × B => p.1) x :=
  (ContinuousLinearMap.fst ℝ A B).analyticAt x

private theorem an_snd {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (x : A × B) :
    AnalyticAt ℝ (fun p : A × B => p.2) x :=
  (ContinuousLinearMap.snd ℝ A B).analyticAt x

/-- `Φ` as a map out of the product form, so that its analyticity can be stated. -/
@[expose] public noncomputable def elimPhiProd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (c : ElimCoordsProd ρ σ τ η ν π) : PairSpace ρ σ τ η ν π :=
  elimPhi J (elimCoordsEquivProd.symm c)

omit [Fintype ν] [DecidableEq ν] in
public theorem elimPhiProd_apply (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (c : ElimCoords ρ σ τ η ν π) :
    elimPhiProd J (elimCoordsEquivProd c) = elimPhi J c := by
  rw [elimPhiProd, Equiv.symm_apply_apply]

omit [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq ν]
  [DecidableEq π] in
/-- **The nine projections of the product form are analytic.** Each is a composite of
`ContinuousLinearMap.fst`/`snd`, hence continuous linear, hence analytic. The composites are
written out rather than chained through `AnalyticAt.comp`, whose `g ∘ f` conclusion does not
eta-reduce to a projection. -/
public theorem analyticAt_coords (c : ElimCoordsProd ρ σ τ η ν π) :
    AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => d.1) c ∧
      AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => d.2.1) c ∧
      AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => d.2.2.1) c ∧
      AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => d.2.2.2.1) c ∧
      AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => d.2.2.2.2.1) c ∧
      AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => d.2.2.2.2.2.1) c ∧
      AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => d.2.2.2.2.2.2.1) c ∧
      AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => d.2.2.2.2.2.2.2.1) c ∧
      AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => d.2.2.2.2.2.2.2.2) c := by
  refine ⟨(ContinuousLinearMap.fst ℝ _ _).analyticAt c,
    ((ContinuousLinearMap.fst ℝ _ _).comp (ContinuousLinearMap.snd ℝ _ _)).analyticAt c,
    ((ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      (ContinuousLinearMap.snd ℝ _ _))).analyticAt c,
    ((ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp
        (ContinuousLinearMap.snd ℝ _ _)))).analyticAt c,
    ((ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        (ContinuousLinearMap.snd ℝ _ _))))).analyticAt c,
    ((ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp
          (ContinuousLinearMap.snd ℝ _ _)))))).analyticAt c,
    ((ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
          (ContinuousLinearMap.snd ℝ _ _))))))).analyticAt c,
    ((ContinuousLinearMap.fst ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
          ((ContinuousLinearMap.snd ℝ _ _).comp
            (ContinuousLinearMap.snd ℝ _ _)))))))).analyticAt c,
    ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
      ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
        ((ContinuousLinearMap.snd ℝ _ _).comp ((ContinuousLinearMap.snd ℝ _ _).comp
          ((ContinuousLinearMap.snd ℝ _ _).comp
            (ContinuousLinearMap.snd ℝ _ _)))))))).analyticAt c⟩

/-- **`Φ`'s first component, print's `A`, is analytic** wherever `det A₁₁ ≠ 0`. Every
ingredient — the inverse shear, `X`, `S`, and the two products — is polynomial in the
coordinates; the `A₁₁` appearing in `A₁₂ = A₁₁X` and `A₂₂ = S + A₂₁X` is a coordinate, not an
inverse. So in fact this component needs no hypothesis at all. -/
public theorem analyticAt_elimPhiProd_fst (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (c : ElimCoordsProd ρ σ τ η ν π) :
    AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => (elimPhiProd J d).1) c := by
  have hT : AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π =>
      elimShearInv d.2.2.2.2.2.2.2.2 d.2.2.2.1 d.2.1) c :=
    AnalyticAt.sub ((analyticAt_coords c).2.1)
      (AnalyticAt.matrix_mul ((analyticAt_coords c).2.2.2.2.2.2.2.2) ((analyticAt_coords c).2.2.2.1))
  have hX : AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π =>
      Matrix.fromRows (elimShearInv d.2.2.2.2.2.2.2.2 d.2.2.2.1 d.2.1).toRows₁
        d.2.2.2.2.2.2.1) c :=
    AnalyticAt.fromRows (AnalyticAt.toRows₁ hT) ((analyticAt_coords c).2.2.2.2.2.2.1)
  have hS : AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π =>
      Matrix.fromRows (elimShearInv d.2.2.2.2.2.2.2.2 d.2.2.2.1 d.2.1).toRows₂
        d.2.2.2.1) c :=
    AnalyticAt.fromRows (AnalyticAt.toRows₂ hT) ((analyticAt_coords c).2.2.2.1)
  exact AnalyticAt.fromBlocks ((analyticAt_coords c).2.2.2.2.1)
    (AnalyticAt.matrix_mul ((analyticAt_coords c).2.2.2.2.1) hX) ((analyticAt_coords c).2.2.2.2.2.1)
    (AnalyticAt.add hS (AnalyticAt.matrix_mul ((analyticAt_coords c).2.2.2.2.2.1) hX))

omit [DecidableEq ν] in
/-- **`Φ`'s second component, print's `B`, is analytic** wherever `det A₁₁ ≠ 0`. This is the
only hypothesis `Φ` needs: `R(D)⁻¹ = (P_{top} 0 ; P_{bot} I)` is polynomial, so `det P_{top}` never
appears, and the sole inverse is the `A₁₁⁻¹` inside `L(A)`. -/
public theorem analyticAt_elimPhiProd_snd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {c : ElimCoordsProd ρ σ τ η ν π} (h : (c.2.2.2.2.1).det ≠ 0) :
    AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => (elimPhiProd J d).2) c := by
  have hPtop : AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π =>
      elimPtop J d.2.2.2.2.2.2.2.1) c :=
    AnalyticAt.toRows₁ (AnalyticAt.fromCols analyticAt_const ((analyticAt_coords c).2.2.2.2.2.2.2.1))
  have hPbot : AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π =>
      elimPbot J d.2.2.2.2.2.2.2.1) c :=
    AnalyticAt.toRows₂ (AnalyticAt.fromCols analyticAt_const ((analyticAt_coords c).2.2.2.2.2.2.2.1))
  -- print's `R(D)⁻¹` is polynomial: no denominator here
  have hRinv : AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π =>
      elimRinv (elimPtop J d.2.2.2.2.2.2.2.1) (elimPbot J d.2.2.2.2.2.2.2.1)) c :=
    AnalyticAt.fromBlocks hPtop analyticAt_const hPbot analyticAt_const
  have hY : AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π =>
      elimRinv (elimPtop J d.2.2.2.2.2.2.2.1) (elimPbot J d.2.2.2.2.2.2.2.1) *
        Matrix.fromRows d.2.2.2.2.2.2.2.2 d.2.2.1) c :=
    AnalyticAt.matrix_mul hRinv
      (AnalyticAt.fromRows ((analyticAt_coords c).2.2.2.2.2.2.2.2) ((analyticAt_coords c).2.2.1))
  have hBbar : AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π =>
      Matrix.fromCols (d.1 + elimCI J σ)
        (Matrix.fromCols d.2.2.2.2.2.2.2.1
          (elimRinv (elimPtop J d.2.2.2.2.2.2.2.1) (elimPbot J d.2.2.2.2.2.2.2.1) *
            Matrix.fromRows d.2.2.2.2.2.2.2.2 d.2.2.1))) c :=
    AnalyticAt.fromCols (AnalyticAt.add ((analyticAt_coords c).1) analyticAt_const)
      (AnalyticAt.fromCols ((analyticAt_coords c).2.2.2.2.2.2.2.1) hY)
  -- the only inverse in `Φ`
  have hinv : AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π => (d.2.2.2.2.1)⁻¹) c :=
    analyticAt_inv_comp ((analyticAt_coords c).2.2.2.2.1) h
  have hL : AnalyticAt ℝ (fun d : ElimCoordsProd ρ σ τ η ν π =>
      elimL d.2.2.2.2.1 d.2.2.2.2.2.1) c :=
    AnalyticAt.fromBlocks hinv analyticAt_const
      (AnalyticAt.neg (AnalyticAt.matrix_mul ((analyticAt_coords c).2.2.2.2.2.1) hinv)) analyticAt_const
  exact AnalyticAt.matrix_mul hBbar hL

/-- **`Φ` is analytic on `{det A₁₁ ≠ 0}`**, the sharp hypothesis: only one of print's two
denominators is consumed by the inverse direction. -/
public theorem analyticOnNhd_elimPhiProd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    AnalyticOnNhd ℝ (elimPhiProd J)
      {c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} := by
  intro c hc
  exact AnalyticAt.prod (analyticAt_elimPhiProd_fst J c) (analyticAt_elimPhiProd_snd J hc)

end PhiAnalytic


/-! ## The image is open, and `Ψ` is a bijection of open sets

The last topological clause of `HasEliminationChartAt` in the `Sum`-indexed setting. Proving
`Ψ '' O` open is not immediate from `Ψ` being an injective analytic map — that would need
invariance of domain. What makes it elementary here is that the *second* round trip,
`Ψ ∘ Φ = id`, holds on an explicitly open set of coordinates: `elimPsi_elimPhi` asks only that
`det A₁₁` and `det P_{top}(D)` be units, and both are open conditions on the coordinate side too.

So write `O'` as `ElimCoordDomain ∩ Φ⁻¹(O)`. It is open because `Φ` is continuous on the open
set where its own denominator survives, and it *is* the image because the two round trips
identify the two descriptions. -/

section Image

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]
variable [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq ν]
variable [DecidableEq π]

/-- The coordinate-side counterpart of `ElimChartDomain`: where both of print's determinants,
read off the chart coordinates rather than the parameters, are units. This is exactly where
`elimPsi_elimPhi` applies. -/
@[expose] public noncomputable def ElimCoordDomain (ρ σ τ η ν π : Type*) [Fintype ρ]
    [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π] [DecidableEq ρ] [DecidableEq σ]
    [DecidableEq τ] [DecidableEq η] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Set (ElimCoordsProd ρ σ τ η ν π) :=
  {c | IsUnit (c.2.2.2.2.1).det ∧ IsUnit (elimPtop J c.2.2.2.2.2.2.2.1).det}

omit [DecidableEq τ] [DecidableEq η] [DecidableEq ν] [DecidableEq π] in
/-- `det A₁₁` is continuous on the coordinate side. -/
public theorem continuous_coord_A11_det :
    Continuous (fun c : ElimCoordsProd ρ σ τ η ν π => (c.2.2.2.2.1).det) :=
  continuous_iff_continuousAt.2 fun c =>
    (analyticAt_det_comp (analyticAt_coords c).2.2.2.2.1).continuousAt

omit [DecidableEq σ] [DecidableEq η] [DecidableEq ν] in
/-- `det P_{top}(D)` is continuous on the coordinate side. -/
public theorem continuous_coord_Ptop_det (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Continuous (fun c : ElimCoordsProd ρ σ τ η ν π =>
      (elimPtop J c.2.2.2.2.2.2.2.1).det) :=
  continuous_iff_continuousAt.2 fun c =>
    (analyticAt_det_comp (AnalyticAt.toRows₁ (AnalyticAt.fromCols analyticAt_const
      (analyticAt_coords c).2.2.2.2.2.2.2.1))).continuousAt

omit [DecidableEq ν] in
/-- The coordinate-side domain is open, for the same reason `ElimChartDomain` is. -/
public theorem isOpen_ElimCoordDomain (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    IsOpen (ElimCoordDomain ρ σ τ η ν π J) := by
  have h : ElimCoordDomain ρ σ τ η ν π J =
      (fun c : ElimCoordsProd ρ σ τ η ν π => (c.2.2.2.2.1).det) ⁻¹' {(0 : ℝ)}ᶜ ∩
        (fun c : ElimCoordsProd ρ σ τ η ν π =>
          (elimPtop J c.2.2.2.2.2.2.2.1).det) ⁻¹' {(0 : ℝ)}ᶜ := by
    ext c
    simp only [ElimCoordDomain, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_compl_iff, Set.mem_singleton_iff, isUnit_iff_ne_zero]
  rw [h]
  exact (isOpen_compl_singleton.preimage continuous_coord_A11_det).inter
    (isOpen_compl_singleton.preimage (continuous_coord_Ptop_det J))

/-- Print's `O'`: the coordinate-side domain, cut down to those coordinates whose `Φ`-image
lies in `O`. -/
@[expose] public noncomputable def ElimChartImage (ρ σ τ η ν π : Type*) [Fintype ρ]
    [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π] [DecidableEq ρ] [DecidableEq σ]
    [DecidableEq τ] [DecidableEq η] [DecidableEq ν] [DecidableEq π]
    (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) : Set (ElimCoordsProd ρ σ τ η ν π) :=
  ElimCoordDomain ρ σ τ η ν π J ∩ elimPhiProd J ⁻¹' ElimChartDomain ρ σ τ η ν π J

/-- **`O'` is open.** `Φ` is continuous on the open set where its own denominator survives, and
`ElimCoordDomain` sits inside that set. -/
public theorem isOpen_ElimChartImage (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    IsOpen (ElimChartImage ρ σ τ η ν π J) := by
  have hs : IsOpen {c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} :=
    isOpen_compl_singleton.preimage continuous_coord_A11_det
  have hcont : ContinuousOn (elimPhiProd J)
      {c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} :=
    (analyticOnNhd_elimPhiProd J).continuousOn
  have hpre : IsOpen ({c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} ∩
      elimPhiProd J ⁻¹' ElimChartDomain ρ σ τ η ν π J) :=
    hcont.isOpen_inter_preimage hs (isOpen_ElimChartDomain J)
  have hsub : ElimChartImage ρ σ τ η ν π J =
      ElimCoordDomain ρ σ τ η ν π J ∩
        ({c : ElimCoordsProd ρ σ τ η ν π | (c.2.2.2.2.1).det ≠ 0} ∩
          elimPhiProd J ⁻¹' ElimChartDomain ρ σ τ η ν π J) := by
    ext c
    simp only [ElimChartImage, ElimCoordDomain, Set.mem_inter_iff, Set.mem_ofPred_eq,
      Set.mem_preimage, isUnit_iff_ne_zero]
    tauto
  rw [hsub]
  exact (isOpen_ElimCoordDomain J).inter hpre

/-- **`O'` really is the image of `O`.** The two round trips of Step 5 identify the two
descriptions: `Ψ` lands in `O'` because it preserves both determinants, and every point of `O'`
is `Ψ` of its own `Φ`-image. -/
public theorem elimPsiProd_image (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2) '' ElimChartDomain ρ σ τ η ν π J
      = ElimChartImage ρ σ τ η ν π J := by
  ext c
  constructor
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨hw.1, hw.2⟩, ?_⟩
    show elimPhiProd J (elimPsiProd J w.1 w.2) ∈ ElimChartDomain ρ σ τ η ν π J
    rw [elimPhiProd, elimPsiProd, Equiv.symm_apply_apply, elimPhi_elimPsi J hw.1 hw.2]
    exact hw
  · rintro ⟨hc, hΦ⟩
    refine ⟨elimPhiProd J c, hΦ, ?_⟩
    have h := elimPsi_elimPhi (J := J) (c := elimCoordsEquivProd.symm c) hc.1 hc.2
    show elimPsiProd J (elimPhiProd J c).1 (elimPhiProd J c).2 = c
    rw [elimPsiProd, elimPhiProd, h, Equiv.apply_symm_apply]

/-- **`Ψ` is a bijection of `O` onto the open set `O'`.** With `isOpen_ElimChartDomain`,
`isOpen_ElimChartImage`, `analyticOnNhd_elimPsiProd` and `analyticOnNhd_elimPhiProd`, every
topological and analytic clause of `HasEliminationChartAt` now holds in the `Sum`-indexed
setting. What remains is the transport into `ParamSpace`/`ChartSpace`, print's base-point
normalization, and the identification of `rrrLoss` with Step 6's Frobenius expression. -/
public theorem bijOn_elimPsiProd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Set.BijOn (fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2)
      (ElimChartDomain ρ σ τ η ν π J) (ElimChartImage ρ σ τ η ν π J) := by
  rw [← elimPsiProd_image J]
  refine ⟨Set.mapsTo_image _ _, ?_, Set.surjOn_image _ _⟩
  intro w hw w' hw' hEq
  have h1 : elimPhiProd J (elimPsiProd J w.1 w.2) = w := by
    rw [elimPhiProd, elimPsiProd, Equiv.symm_apply_apply, elimPhi_elimPsi J hw.1 hw.2]
  have h2 : elimPhiProd J (elimPsiProd J w'.1 w'.2) = w' := by
    rw [elimPhiProd, elimPsiProd, Equiv.symm_apply_apply, elimPhi_elimPsi J hw'.1 hw'.2]
  rw [← h1, ← h2]
  exact congrArg (elimPhiProd J) hEq

end Image


/-! ## Normalizing the chart at its base point

`HasEliminationChartAt` asks for `Ψ (A*, B*) = 0`. Print gets this by carrying `A₁₁ − I_a` and
`D − D*` as coordinates rather than `A₁₁` and `D`; the chart here carries the latter, so it
does not send the base point to `0`.

The gap is a translation, and translation costs nothing: subtracting a constant preserves
analyticity, carries open sets to open sets and bijections to bijections, and by construction
sends the chosen base point to `0`. So the normalization is available for *any* base point in
the domain, without computing `Ψ` at the canonical representative — which is what print's
explicit `A₁₁ − I_a`, `D − D*` amounts to once the value there is known.

The lemmas are stated for arbitrary normed spaces, since nothing about the chart is used. -/

section Normalize

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Subtracting a constant preserves analyticity. -/
public theorem AnalyticOnNhd.sub_const {f : E → F} {s : Set E} (h : AnalyticOnNhd ℝ f s)
    (a : F) : AnalyticOnNhd ℝ (fun x => f x - a) s :=
  fun x hx => (h x hx).sub analyticAt_const

omit [NormedSpace ℝ F] in
/-- Translating a set is a homeomorphism, so it preserves openness. -/
public theorem isOpen_image_sub_const {t : Set F} (h : IsOpen t) (a : F) :
    IsOpen ((fun y => y - a) '' t) := by
  have himg : (fun y : F => y - a) '' t = (fun y : F => y + a) ⁻¹' t := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa using hz
    · intro hy
      exact ⟨y + a, hy, by abel_nf⟩
  rw [himg]
  exact h.preimage (continuous_id.add continuous_const)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] in
/-- Translating the target carries a bijection to a bijection. -/
public theorem Set.BijOn.sub_const {f : E → F} {s : Set E} {t : Set F} (h : Set.BijOn f s t)
    (a : F) : Set.BijOn (fun x => f x - a) s ((fun y => y - a) '' t) := by
  refine ⟨fun x hx => ⟨f x, h.mapsTo hx, rfl⟩, ?_, ?_⟩
  · intro x hx x' hx' hEq
    exact h.injOn hx hx' (by simpa using sub_left_injective hEq)
  · rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, hx, rfl⟩ := h.surjOn hz
    exact ⟨x, hx, rfl⟩

/-- **The normalized chart.** Every clause survives translation, and the base point goes to
`0` by construction. This is print's `A₁₁ − I_a`, `D − D*` normalization, in the form that does
not require knowing the base value first. -/
public theorem normalized_chart {f : E → F} {s : Set E} {t : Set F} (w₀ : E) (hw₀ : w₀ ∈ s)
    (hs : IsOpen s) (ht : IsOpen t) (hbij : Set.BijOn f s t) (hf : AnalyticOnNhd ℝ f s) :
    IsOpen s ∧ IsOpen ((fun y => y - f w₀) '' t) ∧ w₀ ∈ s ∧
      Set.BijOn (fun x => f x - f w₀) s ((fun y => y - f w₀) '' t) ∧
      AnalyticOnNhd ℝ (fun x => f x - f w₀) s ∧ (fun x => f x - f w₀) w₀ = 0 :=
  ⟨hs, isOpen_image_sub_const ht _, hw₀, Set.BijOn.sub_const hbij _,
    AnalyticOnNhd.sub_const hf _, sub_self _⟩

end Normalize

/-! ### The elimination chart, normalized

Applying the above to the chart itself. Every clause of `HasEliminationChartAt` except the
transport into `ParamSpace`/`ChartSpace` and the identification of `rrrLoss` with Step 6's
Frobenius expression now holds, at any base point of the chart domain. -/

section NormalizedChart

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]
variable [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq ν]
variable [DecidableEq π]

/-- **The chart, normalized at a base point.** Open domain, open image, bijection between them,
analytic, and sending the base point to `0`.

The one clause of `HasEliminationChartAt` still absent from this list is the two-sided
comparability with `2K`, which is Step 6 plus Step 7 — both proved — but stated over `rrrLoss`
in `Fin`-indexed coordinates rather than over `frobeniusSq` in these. That identification, and
the transport, are what remain. -/
public theorem normalized_elimChart (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {w₀ : PairSpace ρ σ τ η ν π} (hw₀ : w₀ ∈ ElimChartDomain ρ σ τ η ν π J) :
    IsOpen (ElimChartDomain ρ σ τ η ν π J) ∧
      IsOpen ((fun y => y - elimPsiProd J w₀.1 w₀.2) '' ElimChartImage ρ σ τ η ν π J) ∧
      w₀ ∈ ElimChartDomain ρ σ τ η ν π J ∧
      Set.BijOn (fun w : PairSpace ρ σ τ η ν π =>
          elimPsiProd J w.1 w.2 - elimPsiProd J w₀.1 w₀.2)
        (ElimChartDomain ρ σ τ η ν π J)
        ((fun y => y - elimPsiProd J w₀.1 w₀.2) '' ElimChartImage ρ σ τ η ν π J) ∧
      AnalyticOnNhd ℝ (fun w : PairSpace ρ σ τ η ν π =>
          elimPsiProd J w.1 w.2 - elimPsiProd J w₀.1 w₀.2)
        (ElimChartDomain ρ σ τ η ν π J) ∧
      (elimPsiProd J w₀.1 w₀.2 - elimPsiProd J w₀.1 w₀.2 : ElimCoordsProd ρ σ τ η ν π) = 0 :=
  normalized_chart (f := fun w : PairSpace ρ σ τ η ν π => elimPsiProd J w.1 w.2) w₀ hw₀
    (isOpen_ElimChartDomain J) (isOpen_ElimChartImage J) (bijOn_elimPsiProd J)
    (analyticOnNhd_elimPsiProd J)

end NormalizedChart


/-! ## Transporting a chart along continuous linear equivalences

Everything proved above lives over `Sum` index types, while `HasEliminationChartAt` quantifies
over `ParamSpace M N H` and `ChartSpace q p h n g`. `ChartTransport.lean` supplies the
equivalences; what is needed to use them is that a chart *survives* transport, and that is
what this section says.

The statement is general because nothing about the elimination chart enters: given continuous
linear equivalences on the source and target, conjugating a chart by them preserves openness of
both sets, bijectivity, the two-sided inverse, analyticity of both directions, and the
normalization at the base point. Each clause is one line, because a continuous linear
equivalence is a homeomorphism (openness), a bijection (bijectivity), analytic with analytic
inverse (analyticity), and linear (the base point).

So the remaining work for `IsEliminationChart` is exactly the construction of the two
equivalences — `PairSpace ≃L ParamSpace M N H` and `ElimCoordsProd ≃L ChartSpace q p h n g` —
and that is index bookkeeping over `ChartTransport`'s pieces, requiring the counts
`q = Ma + bn` (`elimQ_eq_add`) and `g` as the five gauge blocks (`elimGauge_eq_add`). It is
not done here. -/

section Transport

variable {E E' F F' : Type*}
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup E'] [NormedSpace ℝ E']
variable [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup F'] [NormedSpace ℝ F']

/-- A continuous linear equivalence carries open sets to open sets. -/
public theorem isOpen_image_clm (e : E ≃L[ℝ] E') {O : Set E} (h : IsOpen O) :
    IsOpen (e '' O) :=
  e.toHomeomorph.isOpenMap O h

/-- Composing an analytic map with a continuous linear equivalence on either side preserves
analyticity, and the domain moves by the same equivalence. -/
public theorem analyticOnNhd_conj (e : E ≃L[ℝ] E') (g : F ≃L[ℝ] F') {Ψ : E → F} {O : Set E}
    (h : AnalyticOnNhd ℝ Ψ O) :
    AnalyticOnNhd ℝ (fun x => g (Ψ (e.symm x))) (e '' O) := by
  rintro x ⟨w, hw, rfl⟩
  have hsym : AnalyticAt ℝ (e.symm : E' → E) (e w) :=
    (e.symm : E' →L[ℝ] E).analyticAt (e w)
  have hmid : AnalyticAt ℝ Ψ (e.symm (e w)) := by
    rw [e.symm_apply_apply]; exact h w hw
  have hout : AnalyticAt ℝ (g : F → F') (Ψ (e.symm (e w))) :=
    (g : F →L[ℝ] F').analyticAt _
  have h1 : AnalyticAt ℝ (Ψ ∘ (e.symm : E' → E)) (e w) :=
    AnalyticAt.comp (g := Ψ) (f := (e.symm : E' → E)) hmid hsym
  have h2 : AnalyticAt ℝ ((g : F → F') ∘ (Ψ ∘ (e.symm : E' → E))) (e w) :=
    AnalyticAt.comp (g := (g : F → F')) (f := Ψ ∘ (e.symm : E' → E)) hout h1
  exact h2

/-- **A chart survives transport.** Conjugating by continuous linear equivalences preserves
every clause of `HasEliminationChartAt`. -/
public theorem chart_transport (e : E ≃L[ℝ] E') (g : F ≃L[ℝ] F')
    {O : Set E} {O' : Set F} {Ψ : E → F} {Φ : F → E} {w₀ : E}
    (hO : IsOpen O) (hO' : IsOpen O') (hw₀ : w₀ ∈ O)
    (hbij : Set.BijOn Ψ O O') (hinv : Set.InvOn Φ Ψ O O')
    (hΨ : AnalyticOnNhd ℝ Ψ O) (hΦ : AnalyticOnNhd ℝ Φ O') (hzero : Ψ w₀ = 0) :
    IsOpen (e '' O) ∧ IsOpen (g '' O') ∧ e w₀ ∈ e '' O ∧
      Set.BijOn (fun x => g (Ψ (e.symm x))) (e '' O) (g '' O') ∧
      Set.InvOn (fun y => e (Φ (g.symm y))) (fun x => g (Ψ (e.symm x))) (e '' O) (g '' O') ∧
      AnalyticOnNhd ℝ (fun x => g (Ψ (e.symm x))) (e '' O) ∧
      AnalyticOnNhd ℝ (fun y => e (Φ (g.symm y))) (g '' O') ∧
      (fun x => g (Ψ (e.symm x))) (e w₀) = 0 := by
  refine ⟨isOpen_image_clm e hO, isOpen_image_clm g hO', ⟨w₀, hw₀, rfl⟩, ?_, ?_,
    analyticOnNhd_conj e g hΨ, analyticOnNhd_conj g e hΦ, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · rintro x ⟨w, hw, rfl⟩
      refine ⟨Ψ w, hbij.mapsTo hw, ?_⟩
      show g (Ψ w) = g (Ψ (e.symm (e w)))
      rw [e.symm_apply_apply]
    · rintro x ⟨w, hw, rfl⟩ x' ⟨w', hw', rfl⟩ hEq
      have hEq' : g (Ψ (e.symm (e w))) = g (Ψ (e.symm (e w'))) := hEq
      rw [e.symm_apply_apply, e.symm_apply_apply] at hEq'
      rw [hbij.injOn hw hw' (g.injective hEq')]
    · rintro y ⟨z, hz, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hbij.surjOn hz
      refine ⟨e w, ⟨w, hw, rfl⟩, ?_⟩
      show g (Ψ (e.symm (e w))) = g (Ψ w)
      rw [e.symm_apply_apply]

  · refine ⟨?_, ?_⟩
    · rintro x ⟨w, hw, rfl⟩
      show e (Φ (g.symm (g (Ψ (e.symm (e w)))))) = e w
      rw [e.symm_apply_apply, g.symm_apply_apply, hinv.1 hw]
    · rintro y ⟨z, hz, rfl⟩
      show g (Ψ (e.symm (e (Φ (g.symm (g z)))))) = g z
      rw [g.symm_apply_apply, e.symm_apply_apply, hinv.2 hz]
  · show g (Ψ (e.symm (e w₀))) = 0
    rw [e.symm_apply_apply, hzero, map_zero]

end Transport


/-! ## The coordinate equivalence

The second of the two equivalences `chart_transport` consumes. `ChartTransport.lean` supplies
the index splittings and the packings; this is their composition into
`ElimCoordsProd ≃L ChartSpace q p h n g`. -/

section CoordEquiv

variable {M N H r a b : ℕ}

/-- **The coordinate equivalence.** `ElimCoordsProd` at the six `Fin` index types is
`ChartSpace q p h n g`, as a continuous linear equivalence.

Three stages, in order: reindex each of the nine blocks to `Fin`-shaped matrices; regroup the
nine-fold product into `ChartSpace`'s four components; pack the first two blocks and the last
five into their Euclidean coordinates, transporting the dimensions by `elimQ_eq_add` and
`elimGauge_eq_add'`.

With `elimParamEquiv`, this is the second of the two equivalences `chart_transport` needs. -/
@[expose] public noncomputable def elimCoordEquiv (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M) :
    ElimCoordsProd (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
        (Fin (elimN N a)) (Fin (elimP M b)) ≃L[ℝ]
      ChartSpace (elimQ M N a b) (elimP M b) (elimH H r a b) (elimN N a)
        (elimGauge M N H r a b) :=
  -- stage 1: reindex the nine blocks
  (((matrixReindexEquiv (elimOutputIdx hbM hrb) (elimAIdx hra)).prodCongr
    ((matrixReindexEquiv (elimBIdx hrb) (Equiv.refl (Fin (elimN N a)))).prodCongr
      ((ContinuousLinearEquiv.refl ℝ
          (Matrix (Fin (elimP M b)) (Fin (elimH H r a b)) ℝ)).prodCongr
        ((ContinuousLinearEquiv.refl ℝ
            (Matrix (Fin (elimH H r a b)) (Fin (elimN N a)) ℝ)).prodCongr
          ((matrixReindexEquiv (elimAIdx hra) (elimAIdx hra)).prodCongr
            ((matrixReindexEquiv (elimHTailIdx haH hrb hab) (elimAIdx hra)).prodCongr
              ((ContinuousLinearEquiv.refl ℝ
                  (Matrix (Fin (a - r)) (Fin (elimN N a)) ℝ)).prodCongr
                ((matrixReindexEquiv (elimOutputIdx hbM hrb)
                    (Equiv.refl (Fin (b - r)))).prodCongr
                  (matrixReindexEquiv (elimBIdx hrb)
                    (Equiv.refl (Fin (elimH H r a b))))))))))))).trans <|
  -- stage 2: regroup into `ChartSpace`'s four components
  (prodRegroup9 (Matrix (Fin M) (Fin a) ℝ) (Matrix (Fin b) (Fin (elimN N a)) ℝ)
    (Matrix (Fin (elimP M b)) (Fin (elimH H r a b)) ℝ)
    (Matrix (Fin (elimH H r a b)) (Fin (elimN N a)) ℝ) (Matrix (Fin a) (Fin a) ℝ)
    (Matrix (Fin (H - a)) (Fin a) ℝ) (Matrix (Fin (a - r)) (Fin (elimN N a)) ℝ)
    (Matrix (Fin M) (Fin (b - r)) ℝ) (Matrix (Fin b) (Fin (elimH H r a b)) ℝ)).trans <|
  -- stage 3: pack the `u`-block and the gauge block
  ((matrixPairEucl M a b (elimN N a)).trans
      (euclCongr (elimQ_eq_add hbM haN).symm)).prodCongr
    ((ContinuousLinearEquiv.refl ℝ
        (Matrix (Fin (elimP M b)) (Fin (elimH H r a b)) ℝ)).prodCongr
      ((ContinuousLinearEquiv.refl ℝ
          (Matrix (Fin (elimH H r a b)) (Fin (elimN N a)) ℝ)).prodCongr
        ((matrixQuintEucl a a (H - a) a (a - r) (elimN N a) M (b - r) b
            (elimH H r a b)).trans
          (euclCongr (elimGauge_eq_add' M N H r a b).symm))))

public theorem analyticOnNhd_elimCoordEquiv (haH : a ≤ H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M)
    (s : Set (ElimCoordsProd (Fin r) (Fin (a - r)) (Fin (b - r)) (Fin (elimH H r a b))
      (Fin (elimN N a)) (Fin (elimP M b)))) :
    AnalyticOnNhd ℝ (elimCoordEquiv haH hra hrb hab haN hbM) s :=
  fun x _ => (elimCoordEquiv haH hra hrb hab haN hbM).toContinuousLinearMap.analyticAt x


end CoordEquiv


/-! ## Print's `N₀`, as a manifestly open condition

Step 7 works on `N₀ = {‖X‖₂ < ½, ‖P_{top} − I_b‖₂ < ½, ‖P_{bot}‖₂ < ½}`, and says "take `O` to be
the preimage under `Ψ` of a small open box inside `N₀`". So what is needed is not that `N₀`
itself be open in the operator norm — it is that *some* open set inside it be exhibited. The
Frobenius ball is one, by `isOpNormSqBound_of_frobeniusSq_le`, and it is open because
`frobeniusSq` is a polynomial in the entries.

`ElimChartNbhd` is that set, intersected with the chart domain. It is open, and on it all three
of Step 7's operator-norm hypotheses hold — so `elim_opNormSqBound_elimR`,
`elim_opNormSqBound_elimRinv` and Lemma 5.2 all apply. No norm instance on matrices is used. -/

section Nbhd

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]
variable [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq ν]
variable [DecidableEq π]

/-- The Frobenius form of print's `N₀`. -/
@[expose] public noncomputable def ElimN0 (ρ σ τ η ν π : Type*) [Fintype ρ] [Fintype σ]
    [Fintype τ] [Fintype η] [Fintype ν] [Fintype π] [DecidableEq ρ] [DecidableEq σ]
    [DecidableEq τ] [DecidableEq η] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Set (PairSpace ρ σ τ η ν π) :=
  {w | frobeniusSq (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂) < 1 / 4 ∧
    frobeniusSq (elimPtop J (elimDOf w.1 w.2) - 1) < 1 / 4 ∧
    frobeniusSq (elimPbot J (elimDOf w.1 w.2)) < 1 / 4}

/-- Print's neighborhood: the chart domain cut down by the Frobenius form of `N₀`. -/
@[expose] public noncomputable def ElimChartNbhd (ρ σ τ η ν π : Type*) [Fintype ρ] [Fintype σ]
    [Fintype τ] [Fintype η] [Fintype ν] [Fintype π] [DecidableEq ρ] [DecidableEq σ]
    [DecidableEq τ] [DecidableEq η] [DecidableEq ν] [DecidableEq π]
    (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) : Set (PairSpace ρ σ τ η ν π) :=
  ElimChartDomain ρ σ τ η ν π J ∩ ElimN0 ρ σ τ η ν π J

/-- `‖X‖²_F` is continuous on the chart domain — `X` involves `A₁₁⁻¹`, so only there. -/
public theorem continuousOn_frobeniusSq_elimX (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    ContinuousOn (fun w : PairSpace ρ σ τ η ν π =>
      frobeniusSq (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂)) (ElimChartDomain ρ σ τ η ν π J) :=
  fun _w hw => (continuous_frobeniusSq.continuousAt.comp
    (analyticAt_elimX (IsUnit.ne_zero hw.1)).continuousAt).continuousWithinAt

omit [DecidableEq ν] in
/-- `‖P_{top} − I‖²_F` is continuous everywhere: `P_{top}` is polynomial in the parameter. -/
public theorem continuous_frobeniusSq_elimPtop_sub_one (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Continuous (fun w : PairSpace ρ σ τ η ν π =>
      frobeniusSq (elimPtop J (elimDOf w.1 w.2) - 1)) :=
  continuous_iff_continuousAt.2 fun w =>
    continuous_frobeniusSq.continuousAt.comp
      ((analyticAt_elimPtop J w).sub analyticAt_const).continuousAt

omit [DecidableEq ν] in
/-- `‖P_{bot}‖²_F` is continuous everywhere. -/
public theorem continuous_frobeniusSq_elimPbot (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Continuous (fun w : PairSpace ρ σ τ η ν π =>
      frobeniusSq (elimPbot J (elimDOf w.1 w.2))) :=
  continuous_iff_continuousAt.2 fun w =>
    continuous_frobeniusSq.continuousAt.comp (analyticAt_elimPbot J w).continuousAt

/-- **Print's neighborhood is open.** Each of the three conditions is a strict inequality
between continuous functions, and the first is continuous exactly on the chart domain, which is
where it is imposed. -/
public theorem isOpen_ElimChartNbhd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    IsOpen (ElimChartNbhd ρ σ τ η ν π J) := by
  have h1 : IsOpen (ElimChartDomain ρ σ τ η ν π J ∩
      {w : PairSpace ρ σ τ η ν π |
        frobeniusSq (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂) < 1 / 4}) :=
    (continuousOn_frobeniusSq_elimX J).isOpen_inter_preimage (isOpen_ElimChartDomain J)
      isOpen_Iio
  have h2 : IsOpen {w : PairSpace ρ σ τ η ν π |
      frobeniusSq (elimPtop J (elimDOf w.1 w.2) - 1) < 1 / 4} :=
    isOpen_lt (continuous_frobeniusSq_elimPtop_sub_one J) continuous_const
  have h3 : IsOpen {w : PairSpace ρ σ τ η ν π |
      frobeniusSq (elimPbot J (elimDOf w.1 w.2)) < 1 / 4} :=
    isOpen_lt (continuous_frobeniusSq_elimPbot J) continuous_const
  have heq : ElimChartNbhd ρ σ τ η ν π J =
      (ElimChartDomain ρ σ τ η ν π J ∩
        {w : PairSpace ρ σ τ η ν π |
          frobeniusSq (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂) < 1 / 4}) ∩
        ({w : PairSpace ρ σ τ η ν π |
            frobeniusSq (elimPtop J (elimDOf w.1 w.2) - 1) < 1 / 4} ∩
          {w : PairSpace ρ σ τ η ν π |
            frobeniusSq (elimPbot J (elimDOf w.1 w.2)) < 1 / 4}) := by
    ext w
    simp only [ElimChartNbhd, ElimN0, Set.mem_inter_iff, Set.mem_ofPred_eq]
    tauto
  rw [heq]
  exact h1.inter (h2.inter h3)

/-- **Step 7's three operator-norm hypotheses hold on `ElimChartNbhd`.** Each is a Frobenius
bound promoted by `isOpNormSqBound_of_frobeniusSq_le`; no operator norm is ever computed. -/
public theorem opNormSqBounds_of_mem_ElimChartNbhd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {w : PairSpace ρ σ τ η ν π} (hw : w ∈ ElimChartNbhd ρ σ τ η ν π J) :
    IsOpNormSqBound (elimX w.1.toBlocks₁₁ w.1.toBlocks₁₂) (1 / 4) ∧
      IsOpNormSqBound (elimPtop J (elimDOf w.1 w.2) - 1) (1 / 4) ∧
      IsOpNormSqBound (elimPbot J (elimDOf w.1 w.2)) (1 / 4) :=
  ⟨isOpNormSqBound_of_frobeniusSq_le hw.2.1.le,
    isOpNormSqBound_of_frobeniusSq_le hw.2.2.1.le,
    isOpNormSqBound_of_frobeniusSq_le hw.2.2.2.le⟩

/-- **Lemma 5.4 applies on `ElimChartNbhd`**, with print's two constants on print's two
matrices. This is the last input Step 7 needs beyond Lemma 5.2. -/
public theorem elim_opNormSqBounds_on_nbhd (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {w : PairSpace ρ σ τ η ν π} (hw : w ∈ ElimChartNbhd ρ σ τ η ν π J) :
    IsOpNormSqBound (elimR (elimPtop J (elimDOf w.1 w.2))
        (elimPbot J (elimDOf w.1 w.2))) 6 ∧
      IsOpNormSqBound (elimRinv (elimPtop J (elimDOf w.1 w.2))
        (elimPbot J (elimDOf w.1 w.2))) 3 := by
  obtain ⟨-, hT, hB⟩ := opNormSqBounds_of_mem_ElimChartNbhd J hw
  exact ⟨elim_opNormSqBound_elimR hT hB, elim_opNormSqBound_elimRinv hT hB⟩

end Nbhd


end AISafetyAtlas.SingularLearning
