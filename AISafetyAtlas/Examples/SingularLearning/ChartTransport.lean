module

public import AISafetyAtlas.SingularLearning.ChartTransport

/-!
# Worked models for the chart's coordinate transport

`AISafetyAtlas/SingularLearning/ChartTransport.lean` supplies the bridge between Step 5's
`Sum`-indexed identities and the `Fin`-indexed `ParamSpace`/`ChartSpace` that Theorem 5.1's
statement quantifies over. Both halves of the bridge are exercised here.

## The witness stratum

`(M, N, H, r, a, b) = (3, 3, 4, 1, 2, 2)` is the smallest stratum on which **every** one of
print's six index types is nonempty:

    r = 1,  a − r = 1,  b − r = 1,  h = H + r − a − b = 1,  n = N − a = 1,  p = M − b = 1

so `ρ = σ = τ = η = ν = π = Fin 1`, and the three splittings read

    Fin 4 ≃ (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1),
    Fin 3 ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin 1,
    Fin 3 ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin 1.

This is the same shape the Step 5 round-trip examples use, which is the point: the transport
below lands exactly on the index types at which `elimPhi_elimPsi` and `elimPsi_elimPhi` are
already proved. At this stratum `q = 8` and `g = 14`, and the dimension identity reads
`8 + 1·1 + 1·1 + 14 = 24 = 4·3 + 3·4`.

A smaller-looking choice like `H = 3` is *not* usable: it forces `h = 0`, so the residual
hidden block is empty and the germ `‖Y₀S_Z‖²_F` is identically zero. The witness has to have
`h ≥ 1` for the chart to be testing anything.

## What these examples do and do not certify

They certify that the splittings elaborate at a genuine stratum, that the two counts agree
there, and that the packings are continuous linear equivalences with analytic inverses. They do
**not** certify that `Ψ` has been driven across the bridge — `IsEliminationChart` is still
unproved for this stratum, as for every stratum but the degenerate one.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-! ## The witness stratum's dimensions -/

example : elimP 3 2 = 1 := rfl
example : elimN 3 2 = 1 := rfl
example : elimH 4 1 2 2 = 1 := rfl
example : elimQ 3 3 2 2 = 8 := rfl
example : elimGauge 3 3 4 1 2 2 = 14 := rfl

/-- The dimension identity at the witness stratum: `q + ph + hn + g = HN + MH`. -/
example : elimQ 3 3 2 2 + elimP 3 2 * elimH 4 1 2 2 + elimH 4 1 2 2 * elimN 3 2
      + elimGauge 3 3 4 1 2 2 = 4 * 3 + 3 * 4 :=
  elim_dimension_split (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **`q = Ma + bn`**, the form the `u`-block is packed in, against `elimQ`'s `a(M−b) + bN`. -/
example : elimQ 3 3 2 2 = 3 * 2 + 2 * elimN 3 2 :=
  elimQ_eq_add (by norm_num) (by norm_num)

/-! ## The three index splittings, at the witness stratum

Each is an `Equiv` between a `Fin` and a nest of `Sum`s of `Fin`s, so its existence is the
whole content: `Fin 4` really does decompose as print says. -/

/-- Print's hidden splitting `ℝ^H = (ℝ^r ⊕ ℝ^{a−r}) ⊕ (ℝ^{b−r} ⊕ ℝ^h)`. -/
example : Fin 4 ≃ (Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1) :=
  elimHiddenEquiv (H := 4) (r := 1) (a := 2) (b := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- Print's input splitting `ℝ^N = (ℝ^r ⊕ ℝ^{a−r}) ⊕ ℝ^n`. -/
example : Fin 3 ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin 1 :=
  elimInputEquiv (N := 3) (r := 1) (a := 2) (by norm_num) (by norm_num)

/-- Print's output splitting `ℝ^M = (ℝ^r ⊕ ℝ^{b−r}) ⊕ ℝ^p`. -/
example : Fin 3 ≃ (Fin 1 ⊕ Fin 1) ⊕ Fin 1 :=
  elimOutputEquiv (M := 3) (r := 1) (b := 2) (by norm_num) (by norm_num)

/-- `finSplit` is the one construction all three are built from, and it is exact: the summand
`n − k` is a type index, not a term appearing in an identity. -/
example {k n : ℕ} (h : k ≤ n) : Fin n ≃ Fin k ⊕ Fin (n - k) := finSplit h

/-- At `k = n` the second summand is empty, and at `k = 0` the first is: the two degenerate
ends of `finSplit` behave. -/
example : Fin 3 ≃ Fin 3 ⊕ Fin 0 := finSplit (le_refl 3)
example : Fin 3 ≃ Fin 0 ⊕ Fin 3 := finSplit (Nat.zero_le 3)

/-! ## The coordinate packings -/

/-- **The matrix packing** at the `u`-block's first half: `U` is `M × a = 3 × 2`, so it packs
into `EuclideanSpace ℝ (Fin 6)`. -/
noncomputable example : EuclideanSpace ℝ (Fin (3 * 2)) ≃L[ℝ] Matrix (Fin 3) (Fin 2) ℝ :=
  matrixEuclEquiv 3 2

/-- **The block packing** splitting `q = 8` into `Ma = 6` and `bn = 2`. -/
noncomputable example : EuclideanSpace ℝ (Fin (6 + 2)) ≃L[ℝ]
    EuclideanSpace ℝ (Fin 6) × EuclideanSpace ℝ (Fin 2) :=
  euclSplitEquiv 6 2

/-- The two composed: the `u`-block coordinate `ℝ^q` is the pair `(U, T′)`. This is the
identification the chart's first block needs, and it is a continuous linear equivalence, so it
contributes nothing to the analyticity obligation beyond
`ContinuousLinearMap.analyticAt`. -/
noncomputable example : EuclideanSpace ℝ (Fin (3 * 2 + 2 * 1)) ≃L[ℝ]
    Matrix (Fin 3) (Fin 2) ℝ × Matrix (Fin 2) (Fin 1) ℝ :=
  (euclSplitEquiv (3 * 2) (2 * 1)).trans
    ((matrixEuclEquiv 3 2).prodCongr (matrixEuclEquiv 2 1))

/-- **Reindexing a matrix along the splittings.** A hidden-by-input matrix over `Sum` index
types becomes an honest `Matrix (Fin 4) (Fin 3) ℝ`, which is what `ParamSpace 3 3 4` holds. -/
noncomputable example :
    Matrix ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) ℝ ≃L[ℝ]
      Matrix (Fin 4) (Fin 3) ℝ :=
  matrixReindexEquiv
    (elimHiddenEquiv (H := 4) (r := 1) (a := 2) (b := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)).symm
    (elimInputEquiv (N := 3) (r := 1) (a := 2) (by norm_num) (by norm_num)).symm

/-! ## Analyticity, for free

Every packing above is a continuous linear equivalence, so both it and its inverse are analytic
on any set. These are the lemmas the assembly of `Ψ` consumes. -/

example (s : Set (EuclideanSpace ℝ (Fin (3 * 2)))) :
    AnalyticOnNhd ℝ (matrixEuclEquiv 3 2) s :=
  analyticOnNhd_matrixEuclEquiv 3 2 s

example (s : Set (Matrix (Fin 3) (Fin 2) ℝ)) :
    AnalyticOnNhd ℝ (matrixEuclEquiv 3 2).symm s :=
  analyticOnNhd_matrixEuclEquiv_symm 3 2 s

example (s : Set (EuclideanSpace ℝ (Fin (6 + 2)))) :
    AnalyticOnNhd ℝ (euclSplitEquiv 6 2) s :=
  analyticOnNhd_euclSplitEquiv 6 2 s

example (s : Set (EuclideanSpace ℝ (Fin 6) × EuclideanSpace ℝ (Fin 2))) :
    AnalyticOnNhd ℝ (euclSplitEquiv 6 2).symm s :=
  analyticOnNhd_euclSplitEquiv_symm 6 2 s

/-- The matrix packing is a bijection of `univ` onto `univ`, the shape
`HasEliminationChartAt`'s `Set.BijOn` clause asks for. -/
example : Set.BijOn (matrixEuclEquiv 3 2) Set.univ Set.univ :=
  bijOn_matrixEuclEquiv 3 2

/-! ## The parameter-space equivalence

The first of the two equivalences `chart_transport` consumes, at the witness stratum. -/

/-- **`PairSpace` at the six `Fin` index types is `ParamSpace M N H`.** At
`(M, N, H, r, a, b) = (3, 3, 4, 1, 2, 2)` every index type is `Fin 1` and the target is
`ParamSpace 3 3 4 = Matrix (Fin 4) (Fin 3) ℝ × Matrix (Fin 3) (Fin 4) ℝ`. -/
noncomputable example :
    (Matrix ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) ℝ ×
      Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) ℝ) ≃L[ℝ]
      (Matrix (Fin 4) (Fin 3) ℝ × Matrix (Fin 3) (Fin 4) ℝ) :=
  elimParamEquiv (M := 3) (N := 3) (H := 4) (r := 1) (a := 2) (b := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- And the target really is `ParamSpace 3 3 4`, so the equivalence lands where
`HasEliminationChartAt` quantifies. -/
example : ParamSpace 3 3 4 = (Matrix (Fin 4) (Fin 3) ℝ × Matrix (Fin 3) (Fin 4) ℝ) := rfl

/-- Being a continuous linear equivalence, it and its inverse are analytic — which is what
`chart_transport` needs of it. -/
example (s : Set (Matrix ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) ℝ ×
      Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) ℝ)) :
    AnalyticOnNhd ℝ (elimParamEquiv (M := 3) (N := 3) (H := 4) (r := 1) (a := 2) (b := 2)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)) s :=
  analyticOnNhd_elimParamEquiv (M := 3) (N := 3) (H := 4) (r := 1) (a := 2) (b := 2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) s

/-- **Dimension transport.** `EuclideanSpace ℝ (Fin k)` moves along an equality of dimensions,
which is what lets the `u`-block's `Ma + bn` be read as `q` and the gauge blocks' sum as `g`. -/
noncomputable example : EuclideanSpace ℝ (Fin (3 * 2 + 2 * 1)) ≃L[ℝ]
    EuclideanSpace ℝ (Fin (elimQ 3 3 2 2)) :=
  euclCongr (by rw [elimQ_eq_add (by norm_num : (2:ℕ) ≤ 3) (by norm_num : (2:ℕ) ≤ 3)]; rfl)


/-! ## The packings are isometries

`comparisonGerm` is `‖u‖² + ‖Y₀S_Z‖²_F` with `u` the *packed* `u`-block, while Step 7's `NF`
is `‖U‖²_F + ‖T′‖²_F + ‖Y₀S_Z‖²_F`. They agree only because the packing preserves the sum of
squares — which is not automatic from its being a linear equivalence. -/

/-- **The matrix packing preserves the sum of squares.** -/
example (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) :
    ‖(matrixEuclEquiv m n).symm A‖ ^ 2 = frobeniusSq A :=
  norm_sq_matrixEuclEquiv_symm m n A

/-- **The `u`-block packing is an isometry**: `‖u‖² = ‖U‖²_F + ‖T′‖²_F`, the first two terms of
print's `NF`. -/
example (m₁ n₁ m₂ n₂ : ℕ) (A : Matrix (Fin m₁) (Fin n₁) ℝ) (B : Matrix (Fin m₂) (Fin n₂) ℝ) :
    ‖matrixPairEucl m₁ n₁ m₂ n₂ (A, B)‖ ^ 2 = frobeniusSq A + frobeniusSq B :=
  norm_sq_matrixPairEucl m₁ n₁ m₂ n₂ A B

/-- Splitting a Euclidean coordinate adds the squared norms. -/
example (k₁ k₂ : ℕ) (x : EuclideanSpace ℝ (Fin k₁)) (y : EuclideanSpace ℝ (Fin k₂)) :
    ‖(euclSplitEquiv k₁ k₂).symm (x, y)‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 :=
  norm_sq_euclSplitEquiv_symm k₁ k₂ x y

/-- And transporting the dimension does not move the germ. -/
example {k k' : ℕ} (h : k = k') (x : EuclideanSpace ℝ (Fin k)) :
    ‖euclCongr h x‖ ^ 2 = ‖x‖ ^ 2 :=
  norm_sq_euclCongr h x

/-- **The `u`-block of `comparisonGerm` is print's first two `NF` terms**, at the witness
stratum: `U` of shape `3 × 2` and `T′` of shape `2 × 1`. -/
example (A : Matrix (Fin 3) (Fin 2) ℝ) (B : Matrix (Fin 2) (Fin 1) ℝ) :
    ‖matrixPairEucl 3 2 2 1 (A, B)‖ ^ 2 = frobeniusSq A + frobeniusSq B :=
  norm_sq_matrixPairEucl 3 2 2 1 A B


end AISafetyAtlas.Examples.SingularLearning
