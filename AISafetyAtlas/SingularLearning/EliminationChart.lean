module

public import Mathlib.Analysis.Analytic.Constructions
public import Mathlib.Analysis.Analytic.Linear
public import Mathlib.Analysis.Matrix.Normed
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import AISafetyAtlas.SingularLearning.Loss
public import AISafetyAtlas.SingularLearning.MatrixNormBridge
public import AISafetyAtlas.SingularLearning.OrbitNormalForm

/-!
# Theorem 5.1 (Elimination): the chart that localizes `K` (statement, with the Step 7 core)

## The statement being formalized

Theorem 5.1 of the MAIS issue #3 candidate (p. 10) reads:

> **Theorem 5.1 (Elimination).** Let `(A*, B*)` be the canonical representative of a feasible
> stratum `(a, b, r)`, as in Lemma 3.2, and let `q, p, n, h` be as in Theorem 1.1. There are an
> open neighborhood `O` of `(A*, B*)`, an analytic diffeomorphism
> `Ψ = (u, Y₀, S_Z, v) : O ⟶ O' ⊆ ℝ^q × ℝ^{p×h} × ℝ^{h×n} × ℝ^g`, `Ψ(A*, B*) = 0`,
> with `g = HN + MH − q − ph − hn`, such that on all of `O`
>
>     (1/12)(‖u‖² + ‖Y₀ S_Z‖²_F)  ≤  2K  ≤  6(‖u‖² + ‖Y₀ S_Z‖²_F).
>
> The gauge coordinates `v` do not appear in the comparison function, and the constants
> `1/12`, `6` are uniform over `v` on `O`.

`IsEliminationChart` is that statement. `comparisonGerm` is `‖u‖² + ‖Y₀ S_Z‖²_F`.

## What is proved here and what is only stated

**Only stated.** `IsEliminationChart M N H r a b` carries **no proof** for a general stratum.
There is no `sorry` anywhere in this file: the theorem is a `def … : Prop`, and no theorem is
attached to it beyond the degenerate witness described below. Nothing in this module may be
cited as "Theorem 5.1 is formalized".

**Proved.**

* `elim_dimension_split` — the dimension identity `q + ph + hn + g = HN + MH` that makes
  `g` of the statement a genuine block count rather than a defined-away remainder. This is
  Appendix B, item 3 of the candidate ("`q + ph + hn + g = HN + MH` identically in
  `(M, N, H, a, b, r)`"), with the candidate's own explicit gauge count
  `g = a² + (H−a)a + (a−r)n + M(b−r) + bh` from p. 13 as the definition of `g`.
* `norm_add_sq_le`, `le_norm_add_sq` — Lemma 5.3 (p. 11), the two elementary norm
  inequalities Step 7 consumes, proved in an arbitrary seminormed group (wider than print's
  "matrices of equal shape", which is the Frobenius instance of the same statement).
* `elimination_comparability` — **Step 7 of the proof (p. 14) in its entirety, once its three
  matrix inputs are granted.** Given the two-sided bound `2K = ‖U‖² + ‖P + Q‖²` of (5.3) with
  `‖P‖² ≤ ‖U‖²/4` (from `‖UX‖ ≤ ‖U‖‖X‖₂ ≤ ½‖U‖` on `N₀`), `‖V‖²/6 ≤ ‖Q‖²` and
  `‖Q‖² ≤ 3‖V‖²` (print's `‖R‖₂ ≤ √6` and `‖R⁻¹‖₂ ≤ √3` of Lemma 5.4), this derives exactly
  the printed constants `1/12` and `6` against `NF = ‖U‖² + ‖V‖²`. It is where the two numbers
  in the statement come from, and both of its Lemma 5.4 inputs are proved, so `(1/12, 6)`
  follows from print's own Steps 1–7.
* `isEliminationChart_zero` — the statement is **satisfiable**: at the stratum
  `(a, b, r) = (0, 0, 0)`, where the truth matrix and both canonical factors are zero, the
  chart is the identity rearrangement `(A, B) ↦ (0, B, A, 0)`, `q = g = 0`,
  `(p, h, n) = (M, H, N)`, and the comparison function equals `2K` on the nose. A statement no
  witness inhabits is not a statement about anything, and this one is inhabited.
* **Lemma 5.4 (p. 11), in full** — `elimRinv`, `elimR`, `elim_det_ne_zero`,
  `elim_opNormBound_top`, `elim_opNormBound_topInv`, `elim_opNormSqBound_elimRinv`,
  `elim_opNormSqBound_elimR`. The `ℓ²` operator norm is carried by `MatrixNormBridge`'s
  instance-free `IsOpNormSqBound`, so it coexists with the Frobenius instance used for
  analyticity. Both printed constants hold as printed; `not_opNormSqBound_elimR_three` records
  that they cannot be equalized, the `√6` for `R` being unimprovable to `√3`.
* **Step 1 (p. 11), in full** — `elimL`, `elimLinv`, `elimX`, `elimSchur`,
  `elimL_mul_elimLinv`, `elimLinv_mul_elimL`, `elimL_det_ne_zero`, `elimL_mul_self`
  (`L(A)A = (I_a X ; 0 S)`, print's second display) and `elimGauge_preserves_product`
  (`B̄Ā = BA` on the nose). The hidden and input splittings are `Sum`s of index types, so no
  `Fin` subtraction enters.
* **Step 6 (p. 13), in full** — `elim_step6` is the exact identity (5.3),
  `2K = ‖U‖² + ‖UX + R(D)⁻¹V‖²`, and `frobeniusSq_elimV` is its second display
  `‖V‖² = ‖T'‖² + ‖Y₀S_Z‖²`; `elim_step6_split` states the two together in the shape Step 7
  consumes. The underlying splittings are `frobeniusSq_fromCols`, `frobeniusSq_fromRows` and
  `frobeniusSq_eq_of_fromCols`. Print's closing remark is preserved: `2K` really does depend
  on the gauge coordinates, through `X` and `R(D)⁻¹`, and the gauge-invariance of the *pair*
  is Step 7's business rather than Step 6's.

* **Steps 2–4 (pp. 12–13), in full** — `elim_step2` is the exact expansion (5.1),
  `elim_step3` and `elim_step3_inv` are the left normalization `R(D)P(D) = (I_b ; 0)` and
  (5.2), and `elimShear`/`elimShearInv` with `elimShearInv_elimShear` are Step 4.
* **Step 5's two round trips (p. 13), in full** — `elimPsi` and `elimPhi` are print's chart
  and print's explicit inverse, and `elimPhi_elimPsi`, `elimPsi_elimPhi`, `elimPsi_bijOn` are
  print's "both round trips are the identity", on print's own open set
  `ElimChartDomain = {det A₁₁ ≠ 0} ∩ {det P_{top}(D) ≠ 0}`.

**Not proved *here*: `IsEliminationChart` itself.** Two things stand between Step 5 above and
the statement, and both are carried out in `ChartAssembly.lean`. First, everything in Steps 1–5 is carried over `Sum` index types, and
`HasEliminationChartAt` quantifies over `ParamSpace M N H` and `ChartSpace q p h n g`, which
are `Fin`-indexed; transporting along `Fin H ≃ Fin a ⊕ Fin (H − a)`,
`Fin N ≃ Fin a ⊕ Fin n`, `Fin M ≃ Fin b ⊕ Fin p` together with the coordinate-counting
equivalence `EuclideanSpace ℝ (Fin q) ≃ Matrix (Fin M) (Fin a) ℝ × Matrix (Fin b) (Fin n) ℝ`
is not done. Second, the `AnalyticOnNhd` clauses are not proved; `MatrixAnalytic.lean`
supplies the one nontrivial ingredient (`analyticOnNhd_inv`, and
`analyticOnNhd_submatrix_inv` in the `det P_{top}` shape), and the rest is a composite of
polynomial maps, but the composite is not assembled *here*. Neither is a mathematical gap —
the mathematics of Step 5 is the two round trips, and those are proved — and both are done in
`ChartAssembly.lean`, whose `isEliminationChart_of_feasible` inhabits `IsEliminationChart` at
every feasible stratum. Print's normalization `Ψ(A*, B*) = 0` is not carried by the chart
*below*, which keeps `A₁₁` and `D` rather than `A₁₁ − I_a` and `D − D*`; it is carried by
`HasEliminationChartAt`, which states it outright.

## Where the locality of the whole argument comes from

This is the step that localizes `K` to a neighborhood of `w*` **before** any residual
computation happens. Everything downstream — the residual minimisation, the transfer lemmas,
the table — operates on the germ `‖u‖² + ‖Y₀ S_Z‖²_F` at the origin, and is entitled to do so
only because Theorem 5.1 has already produced an `O` on which that germ and `2K` are
two-sidedly comparable with uniform constants. **The locality is manufactured here, not in
§8.** §8 inherits a comparability class on an open set; it does not create one. A reader who
takes the residual computation as the local content of the paper has the dependency backwards:
without this theorem the residual germ is a formal expression attached to no neighborhood of
any point of `W₀`.

The clause "the gauge coordinates `v` do not appear in the comparison function, and the
constants are uniform over `v`" is carried by the shape of the statement rather than by an
extra hypothesis: `comparisonGerm` takes only `(u, Y₀, S_Z)` as arguments, and `1/12` and `6`
are numerals, not functions of `w`. Step 7 earns this because `N₀` is cut out by conditions on
`X`, `P_{top}`, `P_{bot}` alone.

## The algebraic half is elsewhere

`(A*, B*)` is the canonical representative of Lemma 3.2, which is proved in
`OrbitNormalForm.lean` (`canonicalA`, `canonicalB`, `sameOrbit_iff_rank_eq`,
`sameOrbit_of_fiber`). Nothing of that is redone here; `IsEliminationChart` names the
representative and the truth matrix `C = B*A* = partialIdMatrix M N r`
(`canonicalB_mul_canonicalA`) and adds the analysis on top. `2K` is `2 * rrrLoss`, which is
`‖BA − C‖²_F` by `rrrLoss_eq_sum_sq` in `Loss.lean` — print's `2K` exactly.

## The `ℕ`-subtraction discipline

The shape is `(p, n, h) = (M − b, N − a, H + r − a − b)`, matching `o70Shape` in
`Conjectures/MAIS/O70.lean` term for term. The third is written `H + r - a - b` and **not**
`H - a - b + r`: the latter parses as `((H - a) - b) + r` and is wrong in `ℕ` at, e.g.,
`H = a = b = r = 2`, which is a feasible stratum. `elimQ` is likewise written
`a * (M - b) + b * N` rather than `M * a + b * N - a * b`, so that it is a `ℕ` with no
truncation as long as `b ≤ M`; `elimQ_cast` records that it equals `o70Q`'s integer expression
`Ma + bN − ab` under exactly that hypothesis, in `ℤ`, where the sign is unconstrained.
`elimGauge` uses the candidate's explicit p. 13 count, every term of which is a product of
differences that are exact on a feasible stratum. `elim_dimension_split` is stated in `ℕ` but
proved by clearing all five subtractions into fresh `ℕ` variables first, so no truncation can
hide inside it.

## The norm instances

`Fin M → ℝ` carries the **supremum** norm in Mathlib, so `‖·‖` on a bare matrix or vector is
not the norm print means. Two precautions:

* the vector block `u` lives in `EuclideanSpace ℝ (Fin q)`, whose `‖·‖` is Euclidean;
* the matrix block is measured by `frobeniusSq`, an explicit double sum of squares, so the
  comparison function carries no norm instance at all. `frobeniusSq_eq_norm_sq` identifies it
  with Mathlib's Frobenius norm under the local instance, and is the only place the instance is
  used for a value.

`Matrix.frobeniusNormedAddCommGroup` and `Matrix.frobeniusNormedSpace` are local instances for
the whole file, because `AnalyticOnNhd` needs *some* normed space structure on the matrix
factors of the chart. Analyticity does not depend on which one: all norms on a
finite-dimensional real vector space are equivalent. Frobenius is chosen because it is the
norm print measures the germ in anyway.
-/

namespace AISafetyAtlas.SingularLearning

open scoped Matrix

attribute [local instance] Matrix.frobeniusNormedAddCommGroup Matrix.frobeniusNormedSpace

/-! ## The chart dimensions

`q` is the rank of `DΦ` at the base point (Lemma 4.1, p. 10); `(p, n, h)` is the residual
shape; `g` is the gauge count. -/

/-- `q = Ma + bN − ab`, the rank of the derivative of the multiplication map at `(A*, B*)`
(Lemma 4.1). Written as `a(M − b) + bN` so that it is a `ℕ` with no truncation whenever
`b ≤ M`; see `elimQ_cast`. -/
@[expose] public def elimQ (M N a b : ℕ) : ℕ := a * (M - b) + b * N

/-- The residual output dimension `p = M − b`. -/
@[expose] public def elimP (M b : ℕ) : ℕ := M - b

/-- The residual input dimension `n = N − a`. -/
@[expose] public def elimN (N a : ℕ) : ℕ := N - a

/-- The residual hidden dimension `h = H + r − a − b`. Not `H - a - b + r`: see the module
docstring. Exact exactly when `a + b ≤ H + r`, which holds on every feasible stratum. -/
@[expose] public def elimH (H r a b : ℕ) : ℕ := H + r - a - b

/-- The gauge dimension `g = a² + (H − a)a + (a − r)n + M(b − r) + bh`, the candidate's
explicit count on p. 13. The statement defines `g` as the remainder
`HN + MH − q − ph − hn`; `elim_dimension_split` proves the two agree. -/
@[expose] public def elimGauge (M N H r a b : ℕ) : ℕ :=
  a * a + (H - a) * a + (a - r) * elimN N a + M * (b - r) + b * elimH H r a b

/-- `elimQ` is `o70Q` — the integer expression `Ma + bN − ab` — whenever `b ≤ M`. The
difference is formed in `ℤ`, where the sign of `Ma + bN − ab` is unconstrained. -/
public theorem elimQ_cast {M N a b : ℕ} (hbM : b ≤ M) :
    (elimQ M N a b : ℤ) = (M : ℤ) * a + (b : ℤ) * N - (a : ℤ) * b := by
  have h : ((M - b : ℕ) : ℤ) = (M : ℤ) - b := by omega
  rw [elimQ]
  push_cast [h]
  ring

/-- **The dimension identity, Appendix B item 3.** `q + ph + hn + g = HN + MH`, so the gauge
block really is the complement of the `q` transverse directions and the `ph + hn` residual
directions inside the `HN + MH` parameters. Without it, `g` in the statement of Theorem 5.1
would be a defined-away remainder and `Ψ` could not be a diffeomorphism onto an open subset of
a space of the printed dimension.

The five hypotheses are exactly the ones that make the five `ℕ` subtractions exact on a
feasible stratum. `a ≤ H` is **not** among them: it follows from `a + b ≤ H + r` and `r ≤ b`,
and including it would leave an unused hypothesis. -/
public theorem elim_dimension_split {M N H r a b : ℕ} (hbM : b ≤ M) (haN : a ≤ N)
    (hra : r ≤ a) (hrb : r ≤ b) (hab : a + b ≤ H + r) :
    elimQ M N a b + elimP M b * elimH H r a b + elimH H r a b * elimN N a
        + elimGauge M N H r a b = H * N + M * H := by
  obtain ⟨p, hp⟩ : ∃ p, M = b + p := ⟨M - b, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n, N = a + n := ⟨N - a, by omega⟩
  obtain ⟨t, hbt⟩ : ∃ t, b = r + t := ⟨b - r, by omega⟩
  obtain ⟨s, has⟩ : ∃ s, a = r + s := ⟨a - r, by omega⟩
  obtain ⟨k, hHk⟩ : ∃ k, H = r + s + t + k := ⟨H + r - a - b, by omega⟩
  simp only [elimQ, elimP, elimN, elimH, elimGauge]
  rw [show M - b = p from by omega, show N - a = n from by omega,
    show a - r = s from by omega, show b - r = t from by omega,
    show H + r - a - b = k from by omega, show H - a = t + k from by omega,
    hp, hn, hbt, has, hHk]
  ring

/-! ## The comparison function

`‖u‖² + ‖Y₀ S_Z‖²_F`, in the vocabulary of print. The matrix half is an explicit sum of
squares so that the definition carries no norm instance; `frobeniusSq_eq_norm_sq` is the
identification with Mathlib's Frobenius norm. -/

-- `frobeniusSq` and `frobeniusSq_nonneg` now live in `MatrixNormBridge.lean`, stated for a
-- general index type rather than `Fin m`/`Fin n`; that module also carries the instance-free
-- operator-norm bound this file's chart construction needs.

/-- `frobeniusSq` is the square of Mathlib's Frobenius norm. This is the only place the norm
instance on matrices is used to name a *value*; everywhere else it is used only to have a
normed space in which analyticity can be stated. -/
public theorem frobeniusSq_eq_norm_sq {m n : ℕ} (X : Matrix (Fin m) (Fin n) ℝ) :
    frobeniusSq X = ‖X‖ ^ 2 := by
  rw [Matrix.frobenius_norm_def, ← Real.rpow_natCast _ 2, ← Real.rpow_mul (by positivity)]
  norm_num [frobeniusSq]

/-- **Print's comparison function**, `‖u‖² + ‖Y₀ S_Z‖²_F`. The gauge block `v` is not an
argument: that is the formal content of "the gauge coordinates `v` do not appear in the
comparison function". -/
@[expose] public noncomputable def comparisonGerm {q p h n : ℕ}
    (u : EuclideanSpace ℝ (Fin q)) (Y₀ : Matrix (Fin p) (Fin h) ℝ)
    (S_Z : Matrix (Fin h) (Fin n) ℝ) : ℝ :=
  ‖u‖ ^ 2 + frobeniusSq (Y₀ * S_Z)

public theorem comparisonGerm_nonneg {q p h n : ℕ} (u : EuclideanSpace ℝ (Fin q))
    (Y₀ : Matrix (Fin p) (Fin h) ℝ) (S_Z : Matrix (Fin h) (Fin n) ℝ) :
    0 ≤ comparisonGerm u Y₀ S_Z := by
  have := frobeniusSq_nonneg (Y₀ * S_Z)
  have : (0 : ℝ) ≤ ‖u‖ ^ 2 := sq_nonneg _
  unfold comparisonGerm
  positivity

/-! ## Step 1 (p. 11): the left gauge `L(A)` and the Schur complement

> **Step 1: left gauge.** Write `A = (A₁₁ A₁₂ ; A₂₁ A₂₂)` with `A₁₁ ∈ ℝ^{a×a}`; at the base
> point `A*₁₁ = I_a`. On `{det A₁₁ ≠ 0}` define
>
>     L(A) = ( A₁₁⁻¹  0 ; −A₂₁A₁₁⁻¹  I ) ∈ GL_H,   Ā = L(A)A = ( I_a  X ; 0  S ),
>
> with `B̄ = B L(A)⁻¹`, `X = A₁₁⁻¹A₁₂ ∈ ℝ^{a×n}` and `S = A₂₂ − A₂₁A₁₁⁻¹A₁₂ ∈ ℝ^{(H−a)×n}` a
> Schur complement. Then `B̄Ā = BA` exactly. The map
> `(A₁₁, A₂₁, A₁₂, A₂₂, B) ↦ (A₁₁, A₂₁, X, S, B̄)` is an analytic diffeomorphism on
> `{det A₁₁ ≠ 0}`, with explicit inverse `A₁₂ = A₁₁X`, `A₂₂ = S + A₂₁X`, `B = B̄L(A)`, and
> `L(A)⁻¹ = (A₁₁ 0 ; A₂₁ I)`.

The hidden splitting `ℝ^H = ℝ^a ⊕ ℝ^{H−a}` and the input splitting `ℝ^N = ℝ^a ⊕ ℝ^n` are
`Sum`s of index types here, exactly as in Lemma 5.4, so `A` is presented as
`Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂` and no `Fin` subtraction occurs. Every identity below is
the algebraic identity of print; none of them uses a norm.

`elimL_mul_self` is the second display of Step 1 — that `L(A)A` is block upper-triangular with
identity top-left block and the Schur complement in the bottom-right. `elimLinv_mul_elimL`
and `elimL_mul_elimLinv` are `L(A) ∈ GL_H` together with print's explicit `L(A)⁻¹`, so
`B̄Ā = B L(A)⁻¹ L(A) A = BA` (`elimGauge_preserves_product`) holds on the nose.

What is **not** here: the analyticity of the Step 1 change of variables. The algebraic
assembly of `Ψ` from Steps 1–4 is in the Step 5 section below; what remains after it is the
`Fin` transport and the `AnalyticOnNhd` obligations, as the module docstring records. -/

section Step1

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Print's left gauge `L(A) = (A₁₁⁻¹ 0 ; −A₂₁A₁₁⁻¹ I)`. It depends only on the left column of
blocks of `A`, which is why print writes it as a function of `A`. -/
@[expose] public noncomputable def elimL (A₁₁ : Matrix ι ι ℝ) (A₂₁ : Matrix κ ι ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks A₁₁⁻¹ 0 (-(A₂₁ * A₁₁⁻¹)) 1

/-- Print's explicit `L(A)⁻¹ = (A₁₁ 0 ; A₂₁ I)`. -/
@[expose] public def elimLinv (A₁₁ : Matrix ι ι ℝ) (A₂₁ : Matrix κ ι ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks A₁₁ 0 A₂₁ 1

/-- Print's `X = A₁₁⁻¹A₁₂`. -/
@[expose] public noncomputable def elimX {ν : Type*} (A₁₁ : Matrix ι ι ℝ)
    (A₁₂ : Matrix ι ν ℝ) : Matrix ι ν ℝ :=
  A₁₁⁻¹ * A₁₂

/-- Print's Schur complement `S = A₂₂ − A₂₁A₁₁⁻¹A₁₂`. -/
@[expose] public noncomputable def elimSchur {ν : Type*} (A₁₁ : Matrix ι ι ℝ)
    (A₁₂ : Matrix ι ν ℝ) (A₂₁ : Matrix κ ι ℝ) (A₂₂ : Matrix κ ν ℝ) : Matrix κ ν ℝ :=
  A₂₂ - A₂₁ * A₁₁⁻¹ * A₁₂

/-- **`L(A)` is invertible on `{det A₁₁ ≠ 0}`, with print's stated inverse.** -/
public theorem elimL_mul_elimLinv {A₁₁ : Matrix ι ι ℝ} (A₂₁ : Matrix κ ι ℝ)
    (h : IsUnit A₁₁.det) : elimL A₁₁ A₂₁ * elimLinv A₁₁ A₂₁ = 1 := by
  rw [elimL, elimLinv, Matrix.fromBlocks_multiply]
  simp [Matrix.nonsing_inv_mul _ h, Matrix.mul_assoc]

public theorem elimLinv_mul_elimL {A₁₁ : Matrix ι ι ℝ} (A₂₁ : Matrix κ ι ℝ)
    (h : IsUnit A₁₁.det) : elimLinv A₁₁ A₂₁ * elimL A₁₁ A₂₁ = 1 := by
  rw [elimL, elimLinv, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ h, ← Matrix.mul_assoc]

/-- `det L(A) ≠ 0` on `{det A₁₁ ≠ 0}` — print's `L(A) ∈ GL_H`. -/
public theorem elimL_det_ne_zero {A₁₁ : Matrix ι ι ℝ} (A₂₁ : Matrix κ ι ℝ)
    (h : IsUnit A₁₁.det) : (elimL A₁₁ A₂₁).det ≠ 0 := by
  intro hd
  have h1 : (elimL A₁₁ A₂₁).det * (elimLinv A₁₁ A₂₁).det = 1 := by
    rw [← Matrix.det_mul, elimL_mul_elimLinv A₂₁ h, Matrix.det_one]
  rw [hd, zero_mul] at h1
  exact zero_ne_one h1

/-- **Step 1's second display: `Ā = L(A)A = (I_a X ; 0 S)`.** The bottom-left block vanishing
and the bottom-right block being the Schur complement are the whole content of the step; the
top row is `A₁₁⁻¹` applied to the first block row of `A`. -/
public theorem elimL_mul_self {ν : Type*} [Fintype ν] {A₁₁ : Matrix ι ι ℝ}
    (A₁₂ : Matrix ι ν ℝ) (A₂₁ : Matrix κ ι ℝ) (A₂₂ : Matrix κ ν ℝ) (h : IsUnit A₁₁.det) :
    elimL A₁₁ A₂₁ * Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ =
      Matrix.fromBlocks 1 (elimX A₁₁ A₁₂) 0 (elimSchur A₁₁ A₁₂ A₂₁ A₂₂) := by
  rw [elimL, Matrix.fromBlocks_multiply, elimX, elimSchur]
  simp [Matrix.nonsing_inv_mul _ h, Matrix.mul_assoc, sub_eq_neg_add]

/-- **`B̄Ā = BA` exactly**, print's final sentence of Step 1, with `B̄ = B L(A)⁻¹`. -/
public theorem elimGauge_preserves_product {ω : Type*} [Fintype ω] {A₁₁ : Matrix ι ι ℝ}
    (A₂₁ : Matrix κ ι ℝ) (A : Matrix (ι ⊕ κ) ω ℝ) (B : Matrix ω (ι ⊕ κ) ℝ)
    (h : IsUnit A₁₁.det) :
    (B * elimLinv A₁₁ A₂₁) * (elimL A₁₁ A₂₁ * A) = B * A := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (elimLinv A₁₁ A₂₁), elimLinv_mul_elimL A₂₁ h,
    Matrix.one_mul]

end Step1

/-! ## Lemma 5.3 (p. 11)

> **Lemma 5.3.** For matrices `x, y` of equal shape, `‖x + y‖² ≤ 2‖x‖² + 2‖y‖²` and
> `‖x + y‖² ≥ ½‖y‖² − ‖x‖²`.

Print proves the first entrywise from `(s + t)² ≤ 2s² + 2t²` and the second from the triangle
inequality. Only the triangle inequality is actually needed for either, so both are stated in
an arbitrary seminormed group; the Frobenius instance on matrices is one case. -/

/-- Lemma 5.3, first inequality. -/
public theorem norm_add_sq_le {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  nlinarith [norm_nonneg x, norm_nonneg y, sq_nonneg (‖x‖ - ‖y‖), norm_nonneg (x + y)]

/-- Lemma 5.3, second inequality. Print's argument verbatim: `‖y‖ ≤ ‖x‖ + ‖x + y‖`, square,
apply the first inequality, rearrange. -/
public theorem le_norm_add_sq {E : Type*} [SeminormedAddCommGroup E] (x y : E) :
    ‖y‖ ^ 2 / 2 - ‖x‖ ^ 2 ≤ ‖x + y‖ ^ 2 := by
  have h : ‖y‖ ≤ ‖x‖ + ‖x + y‖ := by
    calc ‖y‖ = ‖-x + (x + y)‖ := by rw [neg_add_cancel_left]
      _ ≤ ‖-x‖ + ‖x + y‖ := norm_add_le _ _
      _ = ‖x‖ + ‖x + y‖ := by rw [norm_neg]
  nlinarith [norm_nonneg x, norm_nonneg y, norm_nonneg (x + y), sq_nonneg (‖x‖ - ‖x + y‖)]

/-! ## Block operator norms: the machinery of Lemma 5.4's proof

Everything here is stated in `MatrixNormBridge`'s instance-free vocabulary: `IsOpNormBound A k`
is `∀ x, euclNorm (A *ᵥ x) ≤ k * euclNorm x`, the unsquared `ℓ²` operator bound, and
`IsOpNormSqBound A c` its squared form. Both are `Prop`s about explicit sums, so they coexist
with the file-local Frobenius instance on matrices without any diamond. -/

section BlockOperatorNorms

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

/-- The squared Euclidean norm of a vector on a sum index type is the sum of the squared norms
of its two blocks. This is what "`‖x‖² = ‖x₁‖² + ‖x₂‖²` for `x = (x₁; x₂)`" means when the
splitting is a `Sum` of index types rather than a range of `Fin`. -/
public theorem euclNorm_elim_sq (y : ι → ℝ) (z : κ → ℝ) :
    euclNorm (Sum.elim y z) ^ 2 = euclNorm y ^ 2 + euclNorm z ^ 2 := by
  simp only [euclNorm_sq]
  simp [Fintype.sum_sum_type]

/-- The same split for an arbitrary vector on `ι ⊕ κ`. -/
public theorem euclNorm_sum_sq (x : ι ⊕ κ → ℝ) :
    euclNorm x ^ 2 = euclNorm (x ∘ Sum.inl) ^ 2 + euclNorm (x ∘ Sum.inr) ^ 2 := by
  conv_lhs => rw [← Sum.elim_comp_inl_inr x]
  exact euclNorm_elim_sq _ _

/-- `euclNorm` is a norm, not a seminorm: it separates points. Used to turn the Neumann
estimate into invertibility of `Ptop`. -/
public theorem eq_zero_of_euclNorm_eq_zero {x : κ → ℝ} (h : euclNorm x = 0) : x = 0 := by
  have hs : ∑ j, x j ^ 2 = 0 := by rw [← euclNorm_sq, h]; ring
  funext j
  have hj := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (x j)).1 hs j
    (Finset.mem_univ j)
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hj

public theorem isOpNormBound_one [DecidableEq ι] : IsOpNormBound (1 : Matrix ι ι ℝ) 1 := by
  intro x
  simp [Matrix.one_mulVec]

public theorem IsOpNormBound.neg {A : Matrix ι κ ℝ} {k : ℝ} (h : IsOpNormBound A k) :
    IsOpNormBound (-A) k := by
  intro x
  rw [Matrix.neg_mulVec, euclNorm_neg]
  exact h x

public theorem IsOpNormBound.mul {A : Matrix ι κ ℝ} {B : Matrix κ ν ℝ} {k l : ℝ}
    (hA : IsOpNormBound A k) (hB : IsOpNormBound B l) (hk : 0 ≤ k) :
    IsOpNormBound (A * B) (k * l) := by
  intro x
  have h1 := hA (B *ᵥ x)
  rw [Matrix.mulVec_mulVec] at h1
  calc euclNorm ((A * B) *ᵥ x) ≤ k * euclNorm (B *ᵥ x) := h1
    _ ≤ k * (l * euclNorm x) := mul_le_mul_of_nonneg_left (hB x) hk
    _ = k * l * euclNorm x := by ring

/-- The `IsOpNormSqBound … (1/4)` form in which the hypotheses of Lemma 5.4 are stated —
print's `‖·‖₂ ≤ ½` — unpacked into the unsquared form the proof uses. -/
public theorem isOpNormBound_half_of_sq {A : Matrix ι κ ℝ} (h : IsOpNormSqBound A (1 / 4)) :
    IsOpNormBound A (1 / 2) := by
  refine (isOpNormSqBound_iff_isOpNormBound (by norm_num)).1 ?_
  rw [show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num]
  exact h

/-- **The block lower-triangular estimate of Lemma 5.4's proof.** For
`Z = (E 0 ; F G)` and `x = (x₁ ; x₂)`, print computes
`‖Zx‖² = ‖Ex₁‖² + ‖Fx₁ + Gx₂‖² ≤ ‖E‖₂²‖x₁‖² + (‖F‖₂‖x₁‖ + ‖G‖₂‖x₂‖)²`.
The final numerical comparison with `c(‖x₁‖² + ‖x₂‖²)` is left as the hypothesis `hnum`, so
that the two instances print needs — `(e, f, g, c) = (3/2, 1/2, 1, 3)` for `R` and
`(2, 1, 1, 6)` for `R⁻¹` — are each discharged by one `nlinarith` at the use site. -/
public theorem isOpNormSqBound_fromBlocks_lower {E : Matrix ι ι ℝ} {F : Matrix κ ι ℝ}
    {G : Matrix κ κ ℝ} {e f g c : ℝ} (hE : IsOpNormBound E e) (hF : IsOpNormBound F f)
    (hG : IsOpNormBound G g)
    (hnum : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t →
      e ^ 2 * s ^ 2 + (f * s + g * t) ^ 2 ≤ c * (s ^ 2 + t ^ 2)) :
    IsOpNormSqBound (Matrix.fromBlocks E 0 F G) c := by
  rw [isOpNormSqBound_iff_euclNorm]
  intro x
  have hxsplit := euclNorm_sum_sq x
  rw [Matrix.fromBlocks_mulVec, Matrix.zero_mulVec, add_zero, euclNorm_elim_sq, hxsplit]
  set x₁ := x ∘ Sum.inl with hx₁
  set x₂ := x ∘ Sum.inr with hx₂
  have h1 : euclNorm (E *ᵥ x₁) ^ 2 ≤ e ^ 2 * euclNorm x₁ ^ 2 := by
    have hle := hE x₁
    have h0 := euclNorm_nonneg (E *ᵥ x₁)
    nlinarith
  have h2 : euclNorm (F *ᵥ x₁ + G *ᵥ x₂) ≤ f * euclNorm x₁ + g * euclNorm x₂ :=
    (euclNorm_add_le _ _).trans (add_le_add (hF x₁) (hG x₂))
  have h2' : euclNorm (F *ᵥ x₁ + G *ᵥ x₂) ^ 2 ≤ (f * euclNorm x₁ + g * euclNorm x₂) ^ 2 := by
    have h0 := euclNorm_nonneg (F *ᵥ x₁ + G *ᵥ x₂)
    nlinarith
  have h3 := hnum (euclNorm x₁) (euclNorm x₂) (euclNorm_nonneg _) (euclNorm_nonneg _)
  linarith

end BlockOperatorNorms

/-! ## Lemma 5.4 (p. 11): the normalizing factor `R(D)`

> **Lemma 5.4.** Let `P_{top} ∈ ℝ^{b×b}` and `P_{bot} ∈ ℝ^{p×b}` satisfy `‖P_{top} − I_b‖₂ ≤ ½` and
> `‖P_{bot}‖₂ ≤ ½`, and set
>
>     R = ( P_{top}⁻¹  0  ;  −P_{bot} P_{top}⁻¹  I_p ),      R⁻¹ = ( P_{top}  0  ;  P_{bot}  I_p ).
>
> Then `‖R‖₂ ≤ √6` and `‖R⁻¹‖₂ ≤ √3`.

**Both printed bounds are true as printed, and print's proof establishes both.** Print runs one
block estimate for a lower-triangular `Z = (E 0 ; F G)`, namely
`‖Zx‖² ≤ ‖E‖₂²‖x₁‖² + (‖F‖₂‖x₁‖ + ‖G‖₂‖x₂‖)²`, and applies it twice:

* to `R`, whose blocks are `E = P_{top}⁻¹` (norm `≤ 2` by the Neumann series), `F = −P_{bot} P_{top}⁻¹`
  (norm `≤ 1`), `G = I`, giving `‖Rx‖² ≤ 4‖x₁‖² + (‖x₁‖ + ‖x₂‖)² ≤ 6‖x‖²`;
* to `R⁻¹`, whose blocks are `E = P_{top}` (norm `≤ 3/2`), `F = P_{bot}` (norm `≤ ½`), `G = I`,
  giving `‖R⁻¹x‖² ≤ (9/4)‖x₁‖² + (½‖x₁‖ + ‖x₂‖)² ≤ 3‖x‖²`.

Both are formalized here, against print's own labels:

* `elim_opNormSqBound_elimR : IsOpNormSqBound (elimR P_{top} P_{bot}) 6` is `‖R‖₂ ≤ √6`;
* `elim_opNormSqBound_elimRinv : IsOpNormSqBound (elimRinv P_{top} P_{bot}) 3` is `‖R⁻¹‖₂ ≤ √3`.

Neither constant can be traded for the other. `not_opNormSqBound_elimR_three` shows that `6`
cannot be improved to `3` for `R`, at `b = p = 1`, `P_{top} = 3/5`, `P_{bot} = 2/5` — values
satisfying both hypotheses *strictly*, so the obstruction lies strictly inside Step 7's `N₀`
rather than on the boundary of print's non-strict `≤ ½`. The supremum of `‖R‖₂²` over the
hypothesis region is `3 + √5 ≈ 5.236`, approached as `P_{top} → ½`, `P_{bot} → ½`, so `6` is the
clean constant and print's asymmetry between the two bounds is real, not an oversight.

**A naming warning.** Transcribing the two matrices with the labels exchanged — writing
`elimR` for `(P_{top} 0 ; P_{bot} I)` — grades print's `‖R⁻¹‖₂ ≤ √3` against the matrix print
calls `R`, and yields a spurious refutation of Lemma 5.4 together with a spurious defect in
Theorem 5.1's printed pair `(1/12, 6)`. The names below follow print: `elimR` is `(P_{top}⁻¹ 0 ; −P_{bot} P_{top}⁻¹ I)`
and `elimRinv` is `(P_{top} 0 ; P_{bot} I)`. Step 7 consumes `‖R⁻¹V‖² ≤ 3‖V‖²` and
`‖R⁻¹V‖² ≥ ‖V‖²/6`, and `(1/12, 6)` follows — see `elimination_comparability`.

The hypotheses below are `IsOpNormSqBound … (1/4)`, the squared form of print's `‖·‖₂ ≤ ½`;
no norm instance on matrices is involved. The splitting `ℝ^M = ℝ^b ⊕ ℝ^p` is a `Sum` of index
types, so `R` is an honest `Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ` and no `Fin`-arithmetic arises. -/

section Lemma54

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {Ptop : Matrix ι ι ℝ} {Pbot : Matrix κ ι ℝ}

/-- Print's `R(D)⁻¹ = (Ptop 0 ; Pbot I_p)`. -/
@[expose] public def elimRinv (Ptop : Matrix ι ι ℝ) (Pbot : Matrix κ ι ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks Ptop 0 Pbot 1

/-- Print's normalizing factor `R(D) = (Ptop⁻¹ 0 ; −Pbot Ptop⁻¹ I_p) ∈ GL_M`. -/
@[expose] public noncomputable def elimR (Ptop : Matrix ι ι ℝ) (Pbot : Matrix κ ι ℝ) :
    Matrix (ι ⊕ κ) (ι ⊕ κ) ℝ :=
  Matrix.fromBlocks Ptop⁻¹ 0 (-(Pbot * Ptop⁻¹)) 1

/-- **`Ptop` is invertible on the hypothesis region.** Print gets this from the Neumann series;
the direct argument is that `‖Ptop v‖ ≥ ‖v‖ − ‖(Ptop − I)v‖ ≥ ½‖v‖`, so `Ptop` kills no
nonzero vector, and a square matrix over a field with trivial kernel has nonzero determinant. -/
public theorem elim_det_ne_zero (h : IsOpNormBound (Ptop - 1) (1 / 2)) : Ptop.det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
  have hkey : (Ptop - 1) *ᵥ v = -v := by
    rw [Matrix.sub_mulVec, hv, Matrix.one_mulVec, zero_sub]
  have hb := h v
  rw [hkey, euclNorm_neg] at hb
  exact hv0 (eq_zero_of_euclNorm_eq_zero
    (le_antisymm (by linarith [euclNorm_nonneg v]) (euclNorm_nonneg v)))

/-- `‖Ptop‖₂ ≤ 3/2`, print's first Neumann consequence. -/
public theorem elim_opNormBound_top (h : IsOpNormBound (Ptop - 1) (1 / 2)) :
    IsOpNormBound Ptop (3 / 2) := by
  intro x
  have h1 : Ptop *ᵥ x = (Ptop - 1) *ᵥ x + x := by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel
  rw [h1]
  have h2 := (euclNorm_add_le ((Ptop - 1) *ᵥ x) x).trans (add_le_add (h x) (le_refl (euclNorm x)))
  linarith

/-- `‖Ptop⁻¹‖₂ ≤ 2`, print's second Neumann consequence. Proved from
`‖x‖ ≤ ‖x − y‖ + ‖y‖ = ‖(Ptop − I)x‖ + ‖y‖ ≤ ½‖x‖ + ‖y‖` at `x = Ptop⁻¹y`, which is the
Neumann bound `(1 − ½)⁻¹ = 2` without the series. -/
public theorem elim_opNormBound_topInv (h : IsOpNormBound (Ptop - 1) (1 / 2)) :
    IsOpNormBound Ptop⁻¹ 2 := by
  intro y
  have hu : IsUnit Ptop.det := isUnit_iff_ne_zero.2 (elim_det_ne_zero h)
  set x := Ptop⁻¹ *ᵥ y with hxdef
  have hmul : Ptop *ᵥ x = y := by
    rw [hxdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec]
  have hkey : (Ptop - 1) *ᵥ x = y - x := by
    rw [Matrix.sub_mulVec, hmul, Matrix.one_mulVec]
  have h1 := h x
  rw [hkey] at h1
  have h2 : euclNorm x ≤ euclNorm (y - x) + euclNorm y := by
    have hx : x = -(y - x) + y := by abel
    calc euclNorm x = euclNorm (-(y - x) + y) := by rw [← hx]
      _ ≤ euclNorm (-(y - x)) + euclNorm y := euclNorm_add_le _ _
      _ = euclNorm (y - x) + euclNorm y := by rw [euclNorm_neg]
  linarith

omit [DecidableEq κ] in
/-- `‖−Pbot Ptop⁻¹‖₂ ≤ 1`, the off-diagonal block of `R⁻¹`. -/
public theorem elim_opNormBound_shear (hT : IsOpNormBound (Ptop - 1) (1 / 2))
    (hB : IsOpNormBound Pbot (1 / 2)) : IsOpNormBound (-(Pbot * Ptop⁻¹)) 1 := by
  have h := (hB.mul (elim_opNormBound_topInv hT) (by norm_num)).neg
  rwa [show (1 : ℝ) / 2 * 2 = 1 by norm_num] at h

/-- `elimR` really is the inverse of `elimRinv`, on the nose, on the hypothesis region. -/
public theorem elimRinv_mul_elimR (h : IsOpNormBound (Ptop - 1) (1 / 2)) :
    elimRinv Ptop Pbot * elimR Ptop Pbot = 1 := by
  have hu : IsUnit Ptop.det := isUnit_iff_ne_zero.2 (elim_det_ne_zero h)
  rw [elimRinv, elimR, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ hu]

public theorem elimR_mul_elimRinv (h : IsOpNormBound (Ptop - 1) (1 / 2)) :
    elimR Ptop Pbot * elimRinv Ptop Pbot = 1 := by
  have hu : IsUnit Ptop.det := isUnit_iff_ne_zero.2 (elim_det_ne_zero h)
  rw [elimRinv, elimR, Matrix.fromBlocks_multiply]
  simp [Matrix.nonsing_inv_mul _ hu, Matrix.mul_assoc]

/-- **Lemma 5.4, the bound on `R⁻¹`: `‖R⁻¹‖₂² ≤ 3`, as printed.** This is print's second block
computation (`E = Ptop` of norm `≤ 3/2`, `F = Pbot` of norm `≤ ½`, `G = I`). -/
public theorem elim_opNormSqBound_elimRinv (hT : IsOpNormSqBound (Ptop - 1) (1 / 4))
    (hB : IsOpNormSqBound Pbot (1 / 4)) : IsOpNormSqBound (elimRinv Ptop Pbot) 3 := by
  have hT' := isOpNormBound_half_of_sq hT
  have hB' := isOpNormBound_half_of_sq hB
  refine isOpNormSqBound_fromBlocks_lower (elim_opNormBound_top hT') hB' isOpNormBound_one ?_
  intro s t _ _
  nlinarith [sq_nonneg (s - t)]

/-- **Lemma 5.4, the bound on `R`: `‖R‖₂² ≤ 6`, as printed.** This is print's first block
computation (`E = Ptop⁻¹` of norm `≤ 2`, `F = −Pbot Ptop⁻¹` of norm `≤ 1`, `G = I`), which
print attaches to `R`. The constant `6` cannot be improved to print's `3`; see
`not_opNormSqBound_elimR_three`. -/
public theorem elim_opNormSqBound_elimR (hT : IsOpNormSqBound (Ptop - 1) (1 / 4))
    (hB : IsOpNormSqBound Pbot (1 / 4)) : IsOpNormSqBound (elimR Ptop Pbot) 6 := by
  have hT' := isOpNormBound_half_of_sq hT
  have hB' := isOpNormBound_half_of_sq hB
  refine isOpNormSqBound_fromBlocks_lower (elim_opNormBound_topInv hT')
    (elim_opNormBound_shear hT' hB') isOpNormBound_one ?_
  intro s t _ _
  nlinarith [sq_nonneg (s - t)]

end Lemma54

/-! ### Lemma 5.4's two constants cannot be equalized

Print proves `‖R‖₂ ≤ √6` and `‖R⁻¹‖₂ ≤ √3`, and both are formalized above. The gap between
them is forced: the smaller constant does not hold for `R`. The witness is one-dimensional on
both blocks: `b = p = 1`, `Ptop = 3/5`, `Pbot = 2/5`. Then `‖Ptop − I₁‖₂ = ‖Pbot‖₂ = 2/5`,
strictly below print's threshold `½` and hence strictly inside Step 7's `N₀`, while
`R = (5/3, 0 ; −2/3, 1)` sends `x = (3, −2)` to `(5, −4)`, so `‖Rx‖² = 41 > 39 = 3‖x‖²`.

This matters only as a guard against "simplifying" Lemma 5.4 to a single constant `3`; Step 7
uses each constant on the side print puts it, and nothing downstream needs them equal. -/

section Lemma54Counterexample

/-- The counterexample's `Ptop = 3/5 ∈ ℝ^{1×1}`. -/
@[expose] public noncomputable def cePtop : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.of fun _ _ => 3 / 5

/-- The counterexample's `Pbot = 2/5 ∈ ℝ^{1×1}`. -/
@[expose] public noncomputable def cePbot : Matrix (Fin 1) (Fin 1) ℝ :=
  Matrix.of fun _ _ => 2 / 5

/-- The counterexample satisfies print's first hypothesis, strictly: `‖Ptop − I‖₂ = 2/5 < ½`,
so `‖Ptop − I‖₂² = 4/25 < 1/4`. -/
public theorem cePtop_hyp : IsOpNormSqBound (cePtop - 1) (1 / 4) := by
  intro x
  simp only [Fin.sum_univ_one, Matrix.sub_apply, cePtop, Matrix.of_apply, Matrix.one_apply_eq]
  nlinarith [sq_nonneg (x 0)]

/-- The counterexample satisfies print's second hypothesis, strictly: `‖Pbot‖₂ = 2/5 < ½`. -/
public theorem cePbot_hyp : IsOpNormSqBound cePbot (1 / 4) := by
  intro x
  simp only [Fin.sum_univ_one, cePbot, Matrix.of_apply]
  nlinarith [sq_nonneg (x 0)]

public theorem cePtop_inv : cePtop⁻¹ = Matrix.of fun _ _ => (5 : ℝ) / 3 := by
  refine Matrix.inv_eq_right_inv ?_
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply, cePtop]

/-- The counterexample's `R`, written out. -/
public theorem ce_elimR :
    elimR cePtop cePbot =
      Matrix.fromBlocks (Matrix.of fun _ _ => (5 : ℝ) / 3) 0
        (Matrix.of fun _ _ => (-(2 : ℝ) / 3)) 1 := by
  rw [elimR, cePtop_inv]
  congr 1
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Matrix.mul_apply, cePbot]

/-- **Print's `√6` for `R` is not improvable to `√3`.** The asymmetry between Lemma 5.4's two
constants is genuine: `‖R⁻¹‖₂² ≤ 3` holds (`elim_opNormSqBound_elimRinv`) but the same constant
fails for `R`, already at `b = p = 1`, `Ptop = 3/5`, `Pbot = 2/5`, values satisfying both
hypotheses strictly. -/
public theorem not_opNormSqBound_elimR_three :
    ¬ IsOpNormSqBound (elimR cePtop cePbot) 3 := by
  intro h
  have hx := h (Sum.elim (fun _ => (3 : ℝ)) (fun _ => (-2 : ℝ)))
  rw [ce_elimR] at hx
  simp only [Fintype.sum_sum_type, Fin.sum_univ_one, Matrix.fromBlocks_apply₁₁,
    Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Matrix.of_apply, Matrix.zero_apply, Matrix.one_apply_eq, Sum.elim_inl, Sum.elim_inr] at hx
  norm_num at hx

end Lemma54Counterexample

/-! ## Step 7 of the proof (p. 14)

> **Step 7: comparability.** Let `N₀ = {‖X‖₂ < ½, ‖P_{top} − I_b‖₂ < ½, ‖P_{bot}‖₂ < ½}` … Write
> `NF = ‖U‖² + ‖T'‖² + ‖Y₀S_Z‖² = ‖U‖² + ‖V‖²`. On `N₀`, Lemma 5.2 gives
> `‖UX‖ ≤ ‖U‖‖X‖₂ ≤ ½‖U‖`, and Lemma 5.4 bounds `R = R(D)`. Upper bound, by Lemma 5.3 then
> Lemmas 5.2 and 5.4: `‖UX + R⁻¹V‖² ≤ 2‖UX‖² + 2‖R⁻¹V‖² ≤ ½‖U‖² + 6‖V‖²`, so
> `2K ≤ (3/2)‖U‖² + 6‖V‖² ≤ 6 NF`. Lower bound, by Lemma 5.3 with `x = UX`, `y = R⁻¹V`, then
> `‖R⁻¹V‖ ≥ ‖V‖/‖R‖₂ ≥ ‖V‖/√6`: `‖UX + R⁻¹V‖² ≥ ½‖R⁻¹V‖² − ‖UX‖² ≥ (1/12)‖V‖² − ¼‖U‖²`, so
> `2K ≥ ¾‖U‖² + (1/12)‖V‖² ≥ (1/12) NF`. Take `O` to be the preimage under `Ψ` of a small open
> box inside `N₀`.

`elimination_comparability` is that computation, with the three inputs it consumes taken as
hypotheses in the squared form in which Step 7 actually uses them:

* `hP : ‖P‖² ≤ nU² / 4` is `‖UX‖ ≤ ‖U‖‖X‖₂ ≤ ½‖U‖` (Lemma 5.2 plus `‖X‖₂ < ½` on `N₀`);
* `hQhi : ‖Q‖² ≤ 3 nV²` is `‖R⁻¹V‖ ≤ ‖R⁻¹‖₂‖V‖ ≤ √3‖V‖` (Lemmas 5.2 and 5.4);
* `hQlo : nV² / 6 ≤ ‖Q‖²` is `‖R⁻¹V‖ ≥ ‖V‖/‖R‖₂ ≥ ‖V‖/√6` (Lemmas 5.2 and 5.4).

The two constants `1/12` and `6` printed in Theorem 5.1 come out of exactly this and nowhere
else. Neither Lemma 5.2 nor Lemma 5.4 is proved in this file; see the module docstring for the
instance obstruction. Note that `nU` and `nV` are unconstrained reals here rather than
`‖U‖` and `‖V‖`: the argument uses only their squares, and stating it this way keeps it
independent of which space `U` and `V` live in. -/

/-- **Step 7, p. 14.** From the exact identity `2K = ‖U‖² + ‖P + Q‖²` of (5.3) and the three
bounds valid on `N₀`, the printed two-sided comparison with `NF = nU² + nV²`. -/
public theorem elimination_comparability {E : Type*} [SeminormedAddCommGroup E]
    (nU nV : ℝ) (P Q : E) (hP : ‖P‖ ^ 2 ≤ nU ^ 2 / 4) (hQlo : nV ^ 2 / 6 ≤ ‖Q‖ ^ 2)
    (hQhi : ‖Q‖ ^ 2 ≤ 3 * nV ^ 2) :
    1 / 12 * (nU ^ 2 + nV ^ 2) ≤ nU ^ 2 + ‖P + Q‖ ^ 2 ∧
      nU ^ 2 + ‖P + Q‖ ^ 2 ≤ 6 * (nU ^ 2 + nV ^ 2) := by
  have hup := norm_add_sq_le P Q
  have hlo := le_norm_add_sq P Q
  have hU := sq_nonneg nU
  have hV := sq_nonneg nV
  exact ⟨by linarith, by linarith⟩

/-! ## Step 6 (p. 13): the Frobenius norm splits over blocks

> **Step 6: exact identity for `2K`.** Since the Frobenius norm splits over the column blocks
> of (5.1), and by (5.2) with `V := (T' ; Y₀S_Z)`,
>
>     (5.3)   2K = ‖BA − C‖²_F = ‖U‖² + ‖UX + R(D)⁻¹V‖²,
>
> where moreover `‖V‖² = ‖T'‖² + ‖Y₀S_Z‖²` by the block structure of `V`.

Both splittings are the two lemmas below: `frobeniusSq_fromCols` is "the Frobenius norm splits
over the column blocks", used on `BA − C = (U | UX + P(D)T + YS_Z)`, and
`frobeniusSq_fromRows` is "the block structure of `V`", used on `V = (T' ; Y₀S_Z)`. Both are
sums over a `Sum` index type, so neither carries a norm instance. -/

section BlockFrobenius

variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]

/-- **The column-block split of Step 6.** `‖(A | B)‖²_F = ‖A‖²_F + ‖B‖²_F`. -/
public theorem frobeniusSq_fromCols (A : Matrix ι κ ℝ) (B : Matrix ι ν ℝ) :
    frobeniusSq (Matrix.fromCols A B) = frobeniusSq A + frobeniusSq B := by
  simp only [frobeniusSq, Matrix.fromCols, Matrix.of_apply, Fintype.sum_sum_type,
    Sum.elim_inl, Sum.elim_inr]
  exact Finset.sum_add_distrib

/-- **The row-block split of Step 6**, `‖(A ; B)‖²_F = ‖A‖²_F + ‖B‖²_F`, which is what
"`‖V‖² = ‖T'‖² + ‖Y₀S_Z‖²` by the block structure of `V`" asserts. -/
public theorem frobeniusSq_fromRows (A : Matrix κ ι ℝ) (B : Matrix ν ι ℝ) :
    frobeniusSq (Matrix.fromRows A B) = frobeniusSq A + frobeniusSq B := by
  simp only [frobeniusSq, Fintype.sum_sum_type, Matrix.fromRows_apply_inl,
    Matrix.fromRows_apply_inr]

/-- The shape of (5.3) itself: once `BA − C` is presented as the two column blocks
`U` and `UX + R(D)⁻¹V` of Steps 2–4, `2K = ‖BA − C‖²_F` is `‖U‖² + ‖UX + R(D)⁻¹V‖²`. -/
public theorem frobeniusSq_eq_of_fromCols {M N : ℕ} {ι' ν' : Type*} [Fintype ι'] [Fintype ν']
    (S : Matrix (Fin M) (Fin N) ℝ) (U : Matrix (Fin M) ι' ℝ) (W : Matrix (Fin M) ν' ℝ)
    (e : Fin N ≃ ι' ⊕ ν') (hS : S.submatrix id e.symm = Matrix.fromCols U W) :
    frobeniusSq S = frobeniusSq U + frobeniusSq W := by
  rw [← frobeniusSq_fromCols, ← hS]
  simp only [frobeniusSq, Matrix.submatrix_apply, id_eq]
  exact Finset.sum_congr rfl fun i _ => (Equiv.sum_comp e.symm fun j => S i j ^ 2).symm

end BlockFrobenius

/-! ## Steps 2–4 (pp. 12–13): the exact expansion, the left normalization, the shear

> **Step 2: exact expansion.** Split `B̄ = (B_I | D | Y)` into `a`, `b − r`, `h` columns
> following the hidden decomposition `(W_r ⊕ W_{a−r}) ⊕ W_{b−r} ⊕ W_h`, and split
> `S = (S_Q ; S_Z)` into `b − r` and `h` rows, `X = (X_R ; X_P)` into `r` and `a − r` rows.
> Base values: `B_I* = C_I := (I_r 0 ; 0 0) ∈ ℝ^{M×a}`, `D*` the inclusion of `U_{b−r}`,
> `Y* = 0`. Since `C = (C_I | 0)` over the input splitting, block multiplication gives exactly
> `BA − C = B̄Ā − C = (B_I − C_I | B_I X + D S_Q + Y S_Z)`. Set `U := B_I − C_I` and note
> `B_I X = UX + C_I X = UX + J X_R` with `J : ℝ^r → ℝ^M` the inclusion. With
> `P(D) := (J | D) ∈ ℝ^{M×b}` and `T := (X_R ; S_Q) ∈ ℝ^{b×n}`,
>
>     (5.1)   BA − C = ( U | UX + P(D)T + Y S_Z ).
>
> **Step 3: left normalization.** `P(D*) = (I_b ; 0)`. Let `P_{top}` be the top `b×b` block of
> `P(D)` and `P_{bot}` the bottom `p×b` block; both are functions of `D` alone. On
> `{det P_{top} ≠ 0}` define `R(D) ∈ GL_M` as in Lemma 5.4; then `R(D)P(D) = (I_b ; 0)` exactly.
> Split `R(D)Y = (Y₁ ; Y₀)` with `Y₁ ∈ ℝ^{b×h}`, `Y₀ ∈ ℝ^{p×h}`. Applying `R(D)` to the right
> block of (5.1) minus `UX`,
>
>     (5.2)   R(D)( (BA − C)_right − UX ) = ( T + Y₁ S_Z ; Y₀ S_Z ).
>
> **Step 4: shear.** Set `T' := T + Y₁ S_Z`, an exact triangular coordinate change given
> `(Y₁, S_Z)`, with inverse `T = T' − Y₁ S_Z`.

Every index splitting here is a `Sum` of index types, so no `Fin` subtraction occurs anywhere
in this section: the hidden index is `α ⊕ (τ ⊕ η)` with `α = ρ ⊕ σ` (print's
`a = r + (a − r)`, `H − a = (b − r) + h`), the input index is `α ⊕ ν` (print's `N = a + n`),
the output index is `β ⊕ π` with `β = ρ ⊕ τ` (print's `M = b + p`, `b = r + (b − r)`). The
constants `J` and `D*` are carried as parameters rather than instantiated: nothing in
Steps 2–5 uses their values, only their shapes, and pinning them to the canonical
representative is Step 6's business, not theirs. -/

section BlockAlgebra

variable {μ ρ σ τ η ν α β π : Type*}

/-- Print's `P(D) = (J | D) ∈ ℝ^{M×b}`, over the splitting `b = r ⊕ (b − r)`. -/
@[expose] public def elimPblock (J : Matrix μ ρ ℝ) (D : Matrix μ τ ℝ) : Matrix μ (ρ ⊕ τ) ℝ :=
  Matrix.fromCols J D

/-- Print's `T = (X_R ; S_Q) ∈ ℝ^{b×n}`, over the same splitting of `b`. -/
@[expose] public def elimT (XR : Matrix ρ ν ℝ) (SQ : Matrix τ ν ℝ) : Matrix (ρ ⊕ τ) ν ℝ :=
  Matrix.fromRows XR SQ

/-- Print's `B̄ = (B_I | D | Y)`, over the hidden decomposition `a ⊕ ((b − r) ⊕ h)`. -/
@[expose] public def elimBbar (BI : Matrix μ α ℝ) (D : Matrix μ τ ℝ) (Y : Matrix μ η ℝ) :
    Matrix μ (α ⊕ (τ ⊕ η)) ℝ :=
  Matrix.fromCols BI (Matrix.fromCols D Y)

/-- Print's `Ā = (I_a X ; 0 S)` with `S = (S_Q ; S_Z)`, the output of Step 1 presented over
the refined hidden splitting. -/
@[expose] public def elimAbar [DecidableEq α] (X : Matrix α ν ℝ) (SQ : Matrix τ ν ℝ)
    (SZ : Matrix η ν ℝ) : Matrix (α ⊕ (τ ⊕ η)) (α ⊕ ν) ℝ :=
  Matrix.fromBlocks 1 X 0 (Matrix.fromRows SQ SZ)

/-- Print's `C_I = (I_r 0 ; 0 0) ∈ ℝ^{M×a}`, presented as `(J | 0)` over `a = r ⊕ (a − r)`. -/
@[expose] public def elimCI (J : Matrix μ ρ ℝ) (σ : Type*) : Matrix μ (ρ ⊕ σ) ℝ :=
  Matrix.fromCols J 0

/-- Print's truth matrix in these coordinates: `C = (C_I | 0)` over the input splitting. -/
@[expose] public def elimCmat (J : Matrix μ ρ ℝ) (σ ν : Type*) :
    Matrix μ ((ρ ⊕ σ) ⊕ ν) ℝ :=
  Matrix.fromCols (elimCI J σ) 0

private theorem fromCols_sub_fromCols {m n₁ n₂ : Type*} (A₁ B₁ : Matrix m n₁ ℝ)
    (A₂ B₂ : Matrix m n₂ ℝ) :
    Matrix.fromCols A₁ A₂ - Matrix.fromCols B₁ B₂ = Matrix.fromCols (A₁ - B₁) (A₂ - B₂) := by
  ext i (j | j) <;> simp

private theorem fromRows_add_fromRows {m₁ m₂ n : Type*} (A₁ B₁ : Matrix m₁ n ℝ)
    (A₂ B₂ : Matrix m₂ n ℝ) :
    Matrix.fromRows A₁ A₂ + Matrix.fromRows B₁ B₂ = Matrix.fromRows (A₁ + B₁) (A₂ + B₂) := by
  ext (i | i) j <;> simp

section Step2

variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [DecidableEq ρ] [DecidableEq σ]

omit [DecidableEq ρ] [DecidableEq σ] in
/-- `C_I X = J X_R`: the `M × a` truth block reads off only the top `r` rows of `X`. This is
the one place print's `B_I X = UX + C_I X = UX + J X_R` uses the shape of `C_I`. -/
public theorem elimCI_mul_fromRows (J : Matrix μ ρ ℝ) (XR : Matrix ρ ν ℝ)
    (XP : Matrix σ ν ℝ) : elimCI J σ * Matrix.fromRows XR XP = J * XR := by
  rw [elimCI, Matrix.fromCols_mul_fromRows, Matrix.zero_mul, add_zero]

/-- **Step 2, the exact expansion (5.1), p. 12.** With `U = B_I − C_I`, `P(D) = (J | D)` and
`T = (X_R ; S_Q)`, the difference `B̄Ā − C` is exactly the two column blocks
`( U | UX + P(D)T + Y S_Z )`. This is an identity of matrices over `ℝ`: no hypothesis, no
neighborhood, no norm. -/
public theorem elim_step2 (J : Matrix μ ρ ℝ) (BI : Matrix μ (ρ ⊕ σ) ℝ) (D : Matrix μ τ ℝ)
    (Y : Matrix μ η ℝ) (XR : Matrix ρ ν ℝ) (XP : Matrix σ ν ℝ) (SQ : Matrix τ ν ℝ)
    (SZ : Matrix η ν ℝ) :
    elimBbar BI D Y * elimAbar (Matrix.fromRows XR XP) SQ SZ - elimCmat J σ ν =
      Matrix.fromCols (BI - elimCI J σ)
        ((BI - elimCI J σ) * Matrix.fromRows XR XP + elimPblock J D * elimT XR SQ + Y * SZ) := by
  rw [elimBbar, elimAbar, elimCmat, Matrix.fromCols_mul_fromBlocks, fromCols_sub_fromCols]
  congr 1
  · simp
  · rw [Matrix.fromCols_mul_fromRows, sub_zero, elimPblock, elimT,
      Matrix.fromCols_mul_fromRows, Matrix.sub_mul, elimCI_mul_fromRows]
    abel

end Step2

section Step3

variable [Fintype β] [Fintype π] [Fintype η] [DecidableEq β] [DecidableEq π]
variable {Ptop : Matrix β β ℝ} {Pbot : Matrix π β ℝ}

omit [Fintype η] in
/-- `R(D)` and `R(D)⁻¹` are two-sided inverses on the whole of `{det P_{top} ≠ 0}`. Lemma 5.4's
`elimRinv_mul_elimR` assumes the operator-norm bound `‖P_{top} − I‖₂ ≤ ½`, which cuts out a
strictly smaller set; Steps 3–5 are identities of rational functions on the full nonvanishing
locus, exactly as print says ("all are identities of rational functions on the open set where
the two determinants do not vanish"), so they are stated with the determinant hypothesis. -/
public theorem elimRinv_mul_elimR_of_det (h : IsUnit Ptop.det) :
    elimRinv Ptop Pbot * elimR Ptop Pbot = 1 := by
  rw [elimRinv, elimR, Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ h]

omit [Fintype η] in
public theorem elimR_mul_elimRinv_of_det (h : IsUnit Ptop.det) :
    elimR Ptop Pbot * elimRinv Ptop Pbot = 1 := by
  rw [elimRinv, elimR, Matrix.fromBlocks_multiply]
  simp [Matrix.nonsing_inv_mul _ h, Matrix.mul_assoc]

omit [Fintype η] in
/-- **Step 3's normalization, p. 12: `R(D)P(D) = (I_b ; 0)` exactly.** Print's `R(D)` is
`elimR P_{top} P_{bot}` in this file's naming (see the naming note above), and `P(D)` is the
column-partitioned `(P_{top} ; P_{bot})`. -/
public theorem elimR_mul_fromRows_self (h : IsUnit Ptop.det) :
    elimR Ptop Pbot * Matrix.fromRows Ptop Pbot = Matrix.fromRows 1 0 := by
  rw [elimR, Matrix.fromBlocks_mul_fromRows]
  simp [Matrix.nonsing_inv_mul _ h, Matrix.mul_assoc]

/-- **Step 3's (5.2), p. 12.** Applying `R(D)` to `P(D)T + Y S_Z` — which by (5.1) is the
right column block of `BA − C` minus `UX` — splits it into the two row blocks
`T + Y₁ S_Z` and `Y₀ S_Z`, where `(Y₁ ; Y₀) = R(D)Y` is print's splitting of `R(D)Y`. -/
public theorem elim_step3 (h : IsUnit Ptop.det) (T : Matrix β ν ℝ) (Y : Matrix (β ⊕ π) η ℝ)
    (Y₁ : Matrix β η ℝ) (Y₀ : Matrix π η ℝ) (SZ : Matrix η ν ℝ)
    (hY : elimR Ptop Pbot * Y = Matrix.fromRows Y₁ Y₀) :
    elimR Ptop Pbot * (Matrix.fromRows Ptop Pbot * T + Y * SZ) =
      Matrix.fromRows (T + Y₁ * SZ) (Y₀ * SZ) := by
  rw [Matrix.mul_add, ← Matrix.mul_assoc, ← Matrix.mul_assoc, elimR_mul_fromRows_self h, hY,
    Matrix.fromRows_mul, Matrix.fromRows_mul, Matrix.one_mul, Matrix.zero_mul,
    fromRows_add_fromRows, zero_add]

/-- The form Step 6 consumes: `P(D)T + Y S_Z = R(D)⁻¹ (T' ; Y₀S_Z)`, i.e. (5.2) solved for the
right block of (5.1). -/
public theorem elim_step3_inv (h : IsUnit Ptop.det) (T : Matrix β ν ℝ) (Y : Matrix (β ⊕ π) η ℝ)
    (Y₁ : Matrix β η ℝ) (Y₀ : Matrix π η ℝ) (SZ : Matrix η ν ℝ)
    (hY : elimR Ptop Pbot * Y = Matrix.fromRows Y₁ Y₀) :
    Matrix.fromRows Ptop Pbot * T + Y * SZ =
      elimRinv Ptop Pbot * Matrix.fromRows (T + Y₁ * SZ) (Y₀ * SZ) := by
  rw [← elim_step3 h T Y Y₁ Y₀ SZ hY, ← Matrix.mul_assoc, elimRinv_mul_elimR_of_det h,
    Matrix.one_mul]

end Step3

section Step4

variable [Fintype η]

/-- **Step 4's shear, p. 13:** `T' = T + Y₁ S_Z`. -/
@[expose] public def elimShear (Y₁ : Matrix β η ℝ) (SZ : Matrix η ν ℝ) (T : Matrix β ν ℝ) :
    Matrix β ν ℝ :=
  T + Y₁ * SZ

/-- Print's inverse shear `T = T' − Y₁ S_Z`. -/
@[expose] public def elimShearInv (Y₁ : Matrix β η ℝ) (SZ : Matrix η ν ℝ) (T' : Matrix β ν ℝ) :
    Matrix β ν ℝ :=
  T' - Y₁ * SZ

/-- The shear is exact: `(T' − Y₁ S_Z) ∘ (T + Y₁ S_Z) = id`. -/
public theorem elimShearInv_elimShear (Y₁ : Matrix β η ℝ) (SZ : Matrix η ν ℝ)
    (T : Matrix β ν ℝ) : elimShearInv Y₁ SZ (elimShear Y₁ SZ T) = T := by
  rw [elimShear, elimShearInv, add_sub_cancel_right]

/-- The shear is exact in the other direction too. -/
public theorem elimShear_elimShearInv (Y₁ : Matrix β η ℝ) (SZ : Matrix η ν ℝ)
    (T' : Matrix β ν ℝ) : elimShear Y₁ SZ (elimShearInv Y₁ SZ T') = T' := by
  rw [elimShear, elimShearInv, sub_add_cancel]

end Step4

end BlockAlgebra


/-! ## Step 5 (p. 13): the chart, and both round trips

> **Step 5: the chart.** Define
>
>     Ψ(A, B) = ( U, T′ | Y₀, S_Z | A₁₁ − I_a, A₂₁, X_P, D − D*, Y₁ ),
>
> the three groups being the `u`-block, the residual block and the gauge block. The map `Ψ` is
> the composition of the Step 1 diffeomorphism, the linear isomorphism `Y ↦ R(D)Y` with `D`
> held as a coordinate, and the shear of Step 4, each analytic with analytic inverse on
> `{det A₁₁ ≠ 0} ∩ {det P_{top}(D) ≠ 0}`; the explicit inverse is
>
>     T = T′ − Y₁ S_Z,  X = (X_R ; X_P),  S = (S_Q ; S_Z),  A₁₂ = A₁₁X,
>     A₂₂ = S + A₂₁X,  B_I = U + C_I,  Y = R(D)⁻¹(Y₁ ; Y₀),
>     B̄ = (B_I | D | Y),  B = B̄L(A),
>
> where `X_R` and `S_Q` are the top `r` and bottom `b − r` rows of `T`. Both round trips are the
> identity, as identities of rational functions whose only denominators are `det A₁₁` and
> `det P_{top}`.

Everything in this section is carried over `Sum` index types, in the splittings

* hidden `H = a + (H − a)` with `a = r + (a − r)` and `H − a = (b − r) + h`, i.e.
  `(ρ ⊕ σ) ⊕ (τ ⊕ η)`;
* input `N = a + n`, i.e. `(ρ ⊕ σ) ⊕ ν`;
* output `M = b + p` with `b = r + (b − r)`, i.e. `(ρ ⊕ τ) ⊕ π`.

So no `Fin` arithmetic and no truncated subtraction occurs anywhere below, and print's
`X_R`/`S_Q` — "the top `r` and bottom `b − r` rows of `T`" — are `Matrix.toRows₁` and
`Matrix.toRows₂` of a matrix indexed by `ρ ⊕ τ`.

**What this section proves and what it does not.** It proves that `Ψ` and `Φ` are mutually
inverse wherever the two determinants are units — print's "both round trips are the identity",
which is the mathematical content of Step 5. It does **not** yet transport them along
`Fin H ≃ Fin a ⊕ Fin (H − a)` and the coordinate-counting equivalence
`EuclideanSpace ℝ (Fin q) ≃ Matrix (Fin M) (Fin a) ℝ × Matrix (Fin b) (Fin n) ℝ` into the
`ParamSpace`/`ChartSpace` shape that `HasEliminationChartAt` quantifies over, and it does not
prove analyticity. Those two are bookkeeping over the identities below, and both are carried
out in `ChartAssembly.lean`, where `isEliminationChart_of_feasible` proves
`IsEliminationChart` at a general feasible stratum.

**A deviation from print, in the direction of less.** Print's chart carries `A₁₁ − I_a` and
`D − D*` so that `Ψ(A*, B*) = 0`. The coordinates below carry `A₁₁` and `D` themselves: the
affine shift by `(I_a, D*)` is a bijection with an analytic inverse and commutes with
everything here, so including it would only thread a constant through every identity. The
consequence is that `elimPsi` does **not** send the base point to `0`; print's normalization is
that composed with the shift, and it is not carried out here. -/

section Step5

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]
variable [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq π]

/-- The nine coordinate blocks of print's `Ψ`, in print's own order: the `u`-block `(U, T′)`,
the residual block `(Y₀, S_Z)`, and the gauge block `(A₁₁, A₂₁, X_P, D, Y₁)`.

The shapes are print's: `U` is `M × a`, `T′` is `b × n`, `Y₀` is `p × h`, `S_Z` is `h × n`,
`A₁₁` is `a × a`, `A₂₁` is `(H − a) × a`, `X_P` is `(a − r) × n`, `D` is `M × (b − r)` and
`Y₁` is `b × h`. Summing entries gives print's `q + ph + hn + g`; that count is
`elim_dimension_split`, and is not re-derived here. -/
@[ext] public structure ElimCoords (ρ σ τ η ν π : Type*) where
  /-- Print's `U = B_I − C_I`, the `u`-block's first half. -/
  U : Matrix ((ρ ⊕ τ) ⊕ π) (ρ ⊕ σ) ℝ
  /-- Print's `T′ = T + Y₁ S_Z`, the `u`-block's second half. -/
  Tp : Matrix (ρ ⊕ τ) ν ℝ
  /-- Print's `Y₀`, the first residual block. -/
  Y0 : Matrix π η ℝ
  /-- Print's `S_Z`, the second residual block. -/
  SZ : Matrix η ν ℝ
  /-- Print's `A₁₁` (print carries `A₁₁ − I_a`; see the section docstring). -/
  A11 : Matrix (ρ ⊕ σ) (ρ ⊕ σ) ℝ
  /-- Print's `A₂₁`. -/
  A21 : Matrix (τ ⊕ η) (ρ ⊕ σ) ℝ
  /-- Print's `X_P`. -/
  XP : Matrix σ ν ℝ
  /-- Print's `D` (print carries `D − D*`; see the section docstring). -/
  D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ
  /-- Print's `Y₁`. -/
  Y1 : Matrix (ρ ⊕ τ) η ℝ

/-- The top `b × b` block of `P(D) = (J | D)`, print's `P_{top}`. It depends only on `J` and `D`,
which is why Step 3 can hold `D` as a coordinate. -/
@[expose] public def elimPtop (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ) : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ :=
  (elimPblock J D).toRows₁

/-- The bottom `p × b` block of `P(D)`, print's `P_{bot}`. -/
@[expose] public def elimPbot (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ) : Matrix π (ρ ⊕ τ) ℝ :=
  (elimPblock J D).toRows₂

/-- **Print's `Ψ`.** The composition of Step 1's gauge, Step 3's normalization and Step 4's
shear, read off as nine blocks. -/
@[expose] public noncomputable def elimPsi (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (A : Matrix ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ((ρ ⊕ σ) ⊕ ν) ℝ)
    (B : Matrix ((ρ ⊕ τ) ⊕ π) ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ℝ) : ElimCoords ρ σ τ η ν π :=
  let A11 := A.toBlocks₁₁
  let A12 := A.toBlocks₁₂
  let A21 := A.toBlocks₂₁
  let A22 := A.toBlocks₂₂
  let X := elimX A11 A12
  let S := elimSchur A11 A12 A21 A22
  let Bbar := B * elimLinv A11 A21
  let D := Bbar.toCols₂.toCols₁
  let Y := Bbar.toCols₂.toCols₂
  let RY := elimR (elimPtop J D) (elimPbot J D) * Y
  { U := Bbar.toCols₁ - elimCI J σ
    Tp := elimShear RY.toRows₁ S.toRows₂ (elimT X.toRows₁ S.toRows₁)
    Y0 := RY.toRows₂
    SZ := S.toRows₂
    A11 := A11
    A21 := A21
    XP := X.toRows₂
    D := D
    Y1 := RY.toRows₁ }

/-- **Print's explicit inverse `Φ`,** transcribed display for display. -/
@[expose] public noncomputable def elimPhi (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (c : ElimCoords ρ σ τ η ν π) :
    Matrix ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ((ρ ⊕ σ) ⊕ ν) ℝ ×
      Matrix ((ρ ⊕ τ) ⊕ π) ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ℝ :=
  let T := elimShearInv c.Y1 c.SZ c.Tp
  let X := Matrix.fromRows T.toRows₁ c.XP
  let S := Matrix.fromRows T.toRows₂ c.SZ
  let A := Matrix.fromBlocks c.A11 (c.A11 * X) c.A21 (S + c.A21 * X)
  let Y := elimRinv (elimPtop J c.D) (elimPbot J c.D) * Matrix.fromRows c.Y1 c.Y0
  let Bbar := Matrix.fromCols (c.U + elimCI J σ) (Matrix.fromCols c.D Y)
  (A, Bbar * elimL c.A11 c.A21)

omit [Fintype ν]

/-! ### The nine projections of `Ψ`, and the two components of `Φ`

Both maps are defined with `let`, so their projections are pinned as `rfl` lemmas rather than
unfolded at each use. Everything below is definitional; the mathematics is in the two round
trips. -/

section Proj

variable (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
  (A : Matrix ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ((ρ ⊕ σ) ⊕ ν) ℝ)
  (B : Matrix ((ρ ⊕ τ) ⊕ π) ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ℝ)

/-- Print's `B̄ = BL(A)⁻¹` of Step 1. -/
@[expose] public noncomputable def elimBbarOf : Matrix ((ρ ⊕ τ) ⊕ π) ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ℝ :=
  B * elimLinv A.toBlocks₁₁ A.toBlocks₂₁

/-- Print's `D`, the second column block of `B̄`. -/
@[expose] public noncomputable def elimDOf : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ :=
  (elimBbarOf A B).toCols₂.toCols₁

/-- Print's `Y`, the third column block of `B̄`. -/
@[expose] public noncomputable def elimYOf : Matrix ((ρ ⊕ τ) ⊕ π) η ℝ :=
  (elimBbarOf A B).toCols₂.toCols₂

/-- Print's `R(D)Y`, whose two row blocks are `Y₁` and `Y₀`. -/
@[expose] public noncomputable def elimRYOf : Matrix ((ρ ⊕ τ) ⊕ π) η ℝ :=
  elimR (elimPtop J (elimDOf A B)) (elimPbot J (elimDOf A B)) * elimYOf A B

@[simp] public theorem elimPsi_A11 : (elimPsi J A B).A11 = A.toBlocks₁₁ := rfl
@[simp] public theorem elimPsi_A21 : (elimPsi J A B).A21 = A.toBlocks₂₁ := rfl
@[simp] public theorem elimPsi_D : (elimPsi J A B).D = elimDOf A B := rfl
@[simp] public theorem elimPsi_Y1 : (elimPsi J A B).Y1 = (elimRYOf J A B).toRows₁ := rfl
@[simp] public theorem elimPsi_Y0 : (elimPsi J A B).Y0 = (elimRYOf J A B).toRows₂ := rfl
@[simp] public theorem elimPsi_U :
    (elimPsi J A B).U = (elimBbarOf A B).toCols₁ - elimCI J σ := rfl
@[simp] public theorem elimPsi_SZ :
    (elimPsi J A B).SZ =
      (elimSchur A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂).toRows₂ := rfl
@[simp] public theorem elimPsi_XP :
    (elimPsi J A B).XP = (elimX A.toBlocks₁₁ A.toBlocks₁₂).toRows₂ := rfl
@[simp] public theorem elimPsi_Tp :
    (elimPsi J A B).Tp =
      elimShear (elimRYOf J A B).toRows₁
        (elimSchur A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂).toRows₂
        (elimT (elimX A.toBlocks₁₁ A.toBlocks₁₂).toRows₁
          (elimSchur A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂).toRows₁) := rfl

variable (c : ElimCoords ρ σ τ η ν π)

@[simp] public theorem elimPhi_fst :
    (elimPhi J c).1 =
      Matrix.fromBlocks c.A11
        (c.A11 * Matrix.fromRows (elimShearInv c.Y1 c.SZ c.Tp).toRows₁ c.XP) c.A21
        (Matrix.fromRows (elimShearInv c.Y1 c.SZ c.Tp).toRows₂ c.SZ
          + c.A21 * Matrix.fromRows (elimShearInv c.Y1 c.SZ c.Tp).toRows₁ c.XP) := rfl

@[simp] public theorem elimPhi_snd :
    (elimPhi J c).2 =
      Matrix.fromCols (c.U + elimCI J σ)
        (Matrix.fromCols c.D
          (elimRinv (elimPtop J c.D) (elimPbot J c.D) * Matrix.fromRows c.Y1 c.Y0))
        * elimL c.A11 c.A21 := rfl

end Proj

/-- **Step 5, the first round trip: `Φ ∘ Ψ = id`.** Print: "both round trips are the identity,
as identities of rational functions whose only denominators are `det A₁₁` and `det P_{top}`" —
and those are exactly the two hypotheses. -/
public theorem elimPhi_elimPsi (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {A : Matrix ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ((ρ ⊕ σ) ⊕ ν) ℝ}
    {B : Matrix ((ρ ⊕ τ) ⊕ π) ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ℝ}
    (hA : IsUnit (A.toBlocks₁₁).det)
    (hP : IsUnit (elimPtop J (elimDOf A B)).det) :
    elimPhi J (elimPsi J A B) = (A, B) := by
  have hXS : elimShearInv (elimRYOf J A B).toRows₁
      (elimSchur A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂).toRows₂
      (elimPsi J A B).Tp
      = elimT (elimX A.toBlocks₁₁ A.toBlocks₁₂).toRows₁
          (elimSchur A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂).toRows₁ := by
    rw [elimPsi_Tp, elimShearInv_elimShear]
  refine Prod.ext ?_ ?_
  · rw [elimPhi_fst, elimPsi_A11, elimPsi_A21, elimPsi_SZ, elimPsi_Y1, elimPsi_XP, hXS,
      elimT, Matrix.toRows₁_fromRows, Matrix.toRows₂_fromRows, Matrix.fromRows_toRows,
      Matrix.fromRows_toRows]
    -- `A₁₂ = A₁₁X` and `A₂₂ = S + A₂₁X`
    rw [show A.toBlocks₁₁ * elimX A.toBlocks₁₁ A.toBlocks₁₂ = A.toBlocks₁₂ from by
        rw [elimX, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul],
      show elimSchur A.toBlocks₁₁ A.toBlocks₁₂ A.toBlocks₂₁ A.toBlocks₂₂
          + A.toBlocks₂₁ * elimX A.toBlocks₁₁ A.toBlocks₁₂ = A.toBlocks₂₂ from by
        rw [elimSchur, elimX, Matrix.mul_assoc]; abel,
      Matrix.fromBlocks_toBlocks]
  · rw [elimPhi_snd, elimPsi_A11, elimPsi_A21, elimPsi_D, elimPsi_U, elimPsi_Y1, elimPsi_Y0,
      sub_add_cancel, Matrix.fromRows_toRows, elimRYOf, ← Matrix.mul_assoc,
      elimRinv_mul_elimR_of_det (Pbot := elimPbot J (elimDOf A B)) hP, Matrix.one_mul,
      elimYOf, elimDOf, Matrix.fromCols_toCols, Matrix.fromCols_toCols, elimBbarOf,
      Matrix.mul_assoc, elimLinv_mul_elimL _ hA, Matrix.mul_one]

/-- **Step 5, the second round trip: `Ψ ∘ Φ = id`.** The hypotheses are the same two
determinants, now read on the chart side. -/
public theorem elimPsi_elimPhi (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    {c : ElimCoords ρ σ τ η ν π} (hA : IsUnit (c.A11).det)
    (hP : IsUnit (elimPtop J c.D).det) :
    elimPsi J (elimPhi J c).1 (elimPhi J c).2 = c := by
  -- the four blocks of `A` come straight back
  have h11 : ((elimPhi J c).1).toBlocks₁₁ = c.A11 := by rw [elimPhi_fst]; rfl
  have h21 : ((elimPhi J c).1).toBlocks₂₁ = c.A21 := by rw [elimPhi_fst]; rfl
  have h12 : ((elimPhi J c).1).toBlocks₁₂
      = c.A11 * Matrix.fromRows (elimShearInv c.Y1 c.SZ c.Tp).toRows₁ c.XP := by
    rw [elimPhi_fst]; rfl
  have h22 : ((elimPhi J c).1).toBlocks₂₂
      = Matrix.fromRows (elimShearInv c.Y1 c.SZ c.Tp).toRows₂ c.SZ
        + c.A21 * Matrix.fromRows (elimShearInv c.Y1 c.SZ c.Tp).toRows₁ c.XP := by
    rw [elimPhi_fst]; rfl
  -- `X` and `S` are recovered by `A₁₁⁻¹A₁₁ = 1` and by cancelling `A₂₁X`
  have hX : elimX ((elimPhi J c).1).toBlocks₁₁ ((elimPhi J c).1).toBlocks₁₂
      = Matrix.fromRows (elimShearInv c.Y1 c.SZ c.Tp).toRows₁ c.XP := by
    rw [h11, h12, elimX, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]
  have hS : elimSchur ((elimPhi J c).1).toBlocks₁₁ ((elimPhi J c).1).toBlocks₁₂
        ((elimPhi J c).1).toBlocks₂₁ ((elimPhi J c).1).toBlocks₂₂
      = Matrix.fromRows (elimShearInv c.Y1 c.SZ c.Tp).toRows₂ c.SZ := by
    have hcancel : c.A21 * c.A11⁻¹ * c.A11 = c.A21 := by
      rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.mul_one]
    rw [elimSchur, h11, h12, h21, h22,
      ← Matrix.mul_assoc (c.A21 * c.A11⁻¹) c.A11
        (Matrix.fromRows (elimShearInv c.Y1 c.SZ c.Tp).toRows₁ c.XP), hcancel]
    abel
  -- `B̄` is recovered by `L(A)L(A)⁻¹ = 1`
  have hBbar : elimBbarOf (elimPhi J c).1 (elimPhi J c).2
      = Matrix.fromCols (c.U + elimCI J σ)
          (Matrix.fromCols c.D
            (elimRinv (elimPtop J c.D) (elimPbot J c.D) * Matrix.fromRows c.Y1 c.Y0)) := by
    rw [elimBbarOf, h11, h21, elimPhi_snd, Matrix.mul_assoc, elimL_mul_elimLinv _ hA,
      Matrix.mul_one]
  have hD : elimDOf (elimPhi J c).1 (elimPhi J c).2 = c.D := by
    rw [elimDOf, hBbar, Matrix.toCols₂_fromCols, Matrix.toCols₁_fromCols]
  have hY : elimYOf (elimPhi J c).1 (elimPhi J c).2
      = elimRinv (elimPtop J c.D) (elimPbot J c.D) * Matrix.fromRows c.Y1 c.Y0 := by
    rw [elimYOf, hBbar, Matrix.toCols₂_fromCols, Matrix.toCols₂_fromCols]
  have hRY : elimRYOf J (elimPhi J c).1 (elimPhi J c).2 = Matrix.fromRows c.Y1 c.Y0 := by
    rw [elimRYOf, hD, hY, ← Matrix.mul_assoc,
      elimR_mul_elimRinv_of_det (Pbot := elimPbot J c.D) hP, Matrix.one_mul]
  refine ElimCoords.ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [elimPsi_U, hBbar, Matrix.toCols₁_fromCols, add_sub_cancel_right]
  · rw [elimPsi_Tp, hRY, hS, hX]
    simp only [Matrix.toRows₁_fromRows, Matrix.toRows₂_fromRows, elimT,
      Matrix.fromRows_toRows]
    exact elimShear_elimShearInv _ _ _
  · rw [elimPsi_Y0, hRY, Matrix.toRows₂_fromRows]
  · rw [elimPsi_SZ, hS, Matrix.toRows₂_fromRows]
  · rw [elimPsi_A11, h11]
  · rw [elimPsi_A21, h21]
  · rw [elimPsi_XP, hX, Matrix.toRows₂_fromRows]
  · rw [elimPsi_D, hD]
  · rw [elimPsi_Y1, hRY, Matrix.toRows₁_fromRows]

/-- Print's open set: the locus where the only two denominators of Step 5 are units,
`{det A₁₁ ≠ 0} ∩ {det P_{top}(D) ≠ 0}`. -/
@[expose] public noncomputable def ElimChartDomain (ρ σ τ η ν π : Type*) [Fintype ρ]
    [Fintype σ] [Fintype τ] [Fintype η] [Fintype π] [DecidableEq ρ] [DecidableEq σ]
    [DecidableEq τ] [DecidableEq η] [DecidableEq π] (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Set (Matrix ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ((ρ ⊕ σ) ⊕ ν) ℝ ×
      Matrix ((ρ ⊕ τ) ⊕ π) ((ρ ⊕ σ) ⊕ (τ ⊕ η)) ℝ) :=
  {w | IsUnit (w.1.toBlocks₁₁).det ∧ IsUnit (elimPtop J (elimDOf w.1 w.2)).det}

/-- **Step 5, both round trips at once**, on print's open set. `Ψ` is a bijection of the
determinant-nonvanishing locus onto its image, with `Φ` a two-sided inverse there. -/
public theorem elimPsi_invOn (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Set.InvOn (elimPhi J) (fun w => elimPsi J w.1 w.2)
      (ElimChartDomain ρ σ τ η ν π J)
      ((fun w => elimPsi J w.1 w.2) '' ElimChartDomain ρ σ τ η ν π J) := by
  refine ⟨fun w hw => elimPhi_elimPsi J hw.1 hw.2, ?_⟩
  rintro cc ⟨w, hw, rfl⟩
  rw [elimPhi_elimPsi J hw.1 hw.2]

public theorem elimPsi_bijOn (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Set.BijOn (fun w => elimPsi J w.1 w.2) (ElimChartDomain ρ σ τ η ν π J)
      ((fun w => elimPsi J w.1 w.2) '' ElimChartDomain ρ σ τ η ν π J) := by
  refine (elimPsi_invOn (ρ := ρ) (σ := σ) (τ := τ) (η := η) (ν := ν) (π := π) J).bijOn
    (Set.mapsTo_image _ _) ?_
  rintro cc ⟨w, hw, rfl⟩
  rw [elimPhi_elimPsi J hw.1 hw.2]
  exact hw


end Step5


/-! ## Step 6 (p. 13): the exact identity (5.3) for `2K`

> **Step 6: exact identity for `2K`.** Since the Frobenius norm splits over the column blocks
> of (5.1), and by (5.2) with `V := (T′ ; Y₀S_Z)`,
>
>     (5.3)   2K = ‖BA − C‖²_F = ‖U‖² + ‖UX + R(D)⁻¹V‖²,
>
> where moreover `‖V‖² = ‖T′‖² + ‖Y₀S_Z‖²` by the block structure of `V`. Here `X` and `R(D)`
> are the stated functions of the new coordinates; `X` vanishes at the base and
> `R(D*) = I_M`. Note that the exact function `2K` does involve the gauge coordinates (through
> `X` and `R(D)⁻¹`); gauge freedom is a statement about the comparability class established
> next, not about `K` itself.

Both halves are now available: the column presentation of `BA − C` is `elim_step2`, and the
identification of its right block with `R(D)⁻¹V` is `elim_step3_inv`. The Frobenius splittings
were already proved. So (5.3) is an identity of real numbers with a single hypothesis, that
`det P_{top}` is a unit — print's "identities of rational functions on the open set where the two
determinants do not vanish".

Print's closing remark is worth keeping in view: `2K` really does depend on the gauge
coordinates, through `X` and `R(D)⁻¹`. Nothing below says otherwise, and the gauge-invariance
of the *pair* is Step 7's business. -/

section Step6

variable {ρ σ τ η ν π : Type*}
variable [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype ν] [Fintype π]
variable [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq π]

omit [Fintype ρ] [Fintype τ] [Fintype π] [DecidableEq ρ] [DecidableEq τ] [DecidableEq π] in
/-- `P(D) = (P_{top} ; P_{bot})`: the two row blocks recover the column-partitioned `(J | D)`. -/
public theorem fromRows_elimPtop_elimPbot (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ) :
    Matrix.fromRows (elimPtop J D) (elimPbot J D) = elimPblock J D := by
  rw [elimPtop, elimPbot]
  exact Matrix.fromRows_toRows _

omit [DecidableEq ρ] [DecidableEq τ] [DecidableEq π] in
/-- **Step 6's second display: `‖V‖² = ‖T′‖² + ‖Y₀S_Z‖²`**, "by the block structure of `V`". -/
public theorem frobeniusSq_elimV (T' : Matrix (ρ ⊕ τ) ν ℝ) (W : Matrix π ν ℝ) :
    frobeniusSq (Matrix.fromRows T' W) = frobeniusSq T' + frobeniusSq W :=
  frobeniusSq_fromRows _ _

omit [DecidableEq η] in
/-- **Step 6, the exact identity (5.3).** `2K = ‖U‖² + ‖UX + R(D)⁻¹V‖²` with
`V = (T′ ; Y₀S_Z)`, on the locus where `det P_{top}` is a unit.

This is print's display, with `2K` written as the squared Frobenius norm of `B̄Ā − C` — which
is `BA − C` on the nose by `elimGauge_preserves_product`, so no generality is lost by working
with the gauged factors. -/
public theorem elim_step6 (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (BI : Matrix ((ρ ⊕ τ) ⊕ π) (ρ ⊕ σ) ℝ) (D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ)
    (Y : Matrix ((ρ ⊕ τ) ⊕ π) η ℝ) (Y₁ : Matrix (ρ ⊕ τ) η ℝ) (Y₀ : Matrix π η ℝ)
    (XR : Matrix ρ ν ℝ) (XP : Matrix σ ν ℝ) (SQ : Matrix τ ν ℝ) (SZ : Matrix η ν ℝ)
    (hP : IsUnit (elimPtop J D).det)
    (hY : elimR (elimPtop J D) (elimPbot J D) * Y = Matrix.fromRows Y₁ Y₀) :
    frobeniusSq (elimBbar BI D Y * elimAbar (Matrix.fromRows XR XP) SQ SZ - elimCmat J σ ν)
      = frobeniusSq (BI - elimCI J σ)
        + frobeniusSq ((BI - elimCI J σ) * Matrix.fromRows XR XP
            + elimRinv (elimPtop J D) (elimPbot J D)
              * Matrix.fromRows (elimT XR SQ + Y₁ * SZ) (Y₀ * SZ)) := by
  have hkey := elim_step3_inv (Ptop := elimPtop J D) (Pbot := elimPbot J D) hP
    (elimT XR SQ) Y Y₁ Y₀ SZ hY
  rw [fromRows_elimPtop_elimPbot] at hkey
  rw [elim_step2, frobeniusSq_fromCols, add_assoc, hkey]

omit [DecidableEq η] in
/-- **Step 6 and its second display together**, in the shape Step 7 consumes: `2K` against
`NF = ‖U‖² + ‖T′‖² + ‖Y₀S_Z‖²`. The right-hand side names exactly the three blocks of print's
`NF`, so `elimination_comparability` can be applied to it with no further rearrangement. -/
public theorem elim_step6_split (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ)
    (BI : Matrix ((ρ ⊕ τ) ⊕ π) (ρ ⊕ σ) ℝ) (D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ)
    (Y : Matrix ((ρ ⊕ τ) ⊕ π) η ℝ) (Y₁ : Matrix (ρ ⊕ τ) η ℝ) (Y₀ : Matrix π η ℝ)
    (XR : Matrix ρ ν ℝ) (XP : Matrix σ ν ℝ) (SQ : Matrix τ ν ℝ) (SZ : Matrix η ν ℝ)
    (hP : IsUnit (elimPtop J D).det)
    (hY : elimR (elimPtop J D) (elimPbot J D) * Y = Matrix.fromRows Y₁ Y₀) :
    frobeniusSq (elimBbar BI D Y * elimAbar (Matrix.fromRows XR XP) SQ SZ - elimCmat J σ ν)
      = frobeniusSq (BI - elimCI J σ)
        + frobeniusSq ((BI - elimCI J σ) * Matrix.fromRows XR XP
            + elimRinv (elimPtop J D) (elimPbot J D)
              * Matrix.fromRows (elimT XR SQ + Y₁ * SZ) (Y₀ * SZ))
      ∧ frobeniusSq (Matrix.fromRows (elimT XR SQ + Y₁ * SZ) (Y₀ * SZ))
          = frobeniusSq (elimT XR SQ + Y₁ * SZ) + frobeniusSq (Y₀ * SZ) :=
  ⟨elim_step6 J BI D Y Y₁ Y₀ XR XP SQ SZ hP hY, frobeniusSq_elimV _ _⟩

end Step6


/-! ### `2K` really is the squared Frobenius norm

Step 6 computes `‖B̄Ā − C‖²_F`. Print calls that `2K`, and the identification is immediate from
`rrrLoss_eq_sum_sq`: the reduced-rank loss is `½ ∑_{i,j} (BA − C)²_{ij}`, so twice it is the
squared Frobenius norm of `BA − C`. Together with `elimGauge_preserves_product` — `B̄Ā = BA` on
the nose — Step 6's left-hand side is `2K` for the *original* factors, not merely for the
gauged ones.

This is the identification `HasEliminationChartAt`'s comparability clause needs, in the
`Sum`-indexed setting. Transporting it to `Fin`-indexed `rrrLoss` is the remaining step. -/

/-- **`2K = ‖BA − C‖²_F`.** Print's `2K`, as a squared Frobenius norm. -/
public theorem two_mul_rrrLoss_eq_frobeniusSq {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    2 * rrrLoss C A B = frobeniusSq (B * A - C) := by
  rw [rrrLoss_eq_sum_sq, frobeniusSq]
  ring

/-- `B̄Ā = BA` at the shapes the chart actually uses. `elimGauge_preserves_product` states this
for `A : Matrix (ι ⊕ κ) ω` against `B : Matrix ω (ι ⊕ κ)`, which forces `A`'s column type to
equal `B`'s row type and so makes `BA` square. The chart needs `B : M × H` against `A : H × N`
with `M` and `N` distinct, so the general shape is proved here; the proof is the same two
rewrites. -/
public theorem elimGauge_preserves_product' {ι κ ω ν : Type*} [Fintype ι] [Fintype κ]
    [Fintype ω] [Fintype ν] [DecidableEq ι] [DecidableEq κ] {A₁₁ : Matrix ι ι ℝ}
    (A₂₁ : Matrix κ ι ℝ) (A : Matrix (ι ⊕ κ) ν ℝ) (B : Matrix ω (ι ⊕ κ) ℝ)
    (h : IsUnit A₁₁.det) :
    (B * elimLinv A₁₁ A₂₁) * (elimL A₁₁ A₂₁ * A) = B * A := by
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (elimLinv A₁₁ A₂₁), elimLinv_mul_elimL A₂₁ h,
    Matrix.one_mul]

/-- **The gauge does not move `2K`.** `B̄Ā = BA` exactly, so the Frobenius norm Step 6 computes
is the loss of the original pair. -/
public theorem frobeniusSq_elimGauge_eq {ι κ ω ν : Type*} [Fintype ι] [Fintype κ] [Fintype ω]
    [Fintype ν] [DecidableEq ι] [DecidableEq κ] {A₁₁ : Matrix ι ι ℝ} (A₂₁ : Matrix κ ι ℝ)
    (A : Matrix (ι ⊕ κ) ν ℝ) (B : Matrix ω (ι ⊕ κ) ℝ) (C : Matrix ω ν ℝ)
    (h : IsUnit A₁₁.det) :
    frobeniusSq ((B * elimLinv A₁₁ A₂₁) * (elimL A₁₁ A₂₁ * A) - C)
      = frobeniusSq (B * A - C) := by
  rw [elimGauge_preserves_product' A₂₁ A B h]


/-! ### The base point is not in the chart's domain, under the current conventions

`HasEliminationChartAt` fixes its base point to be the canonical representative
`(canonicalA N H a b r, canonicalB M H b r)` of `OrbitNormalForm.lean`. Step 1 of print needs
`det A₁₁ ≠ 0` there — indeed print says `A₁₁* = I_a`. That fails, and the reason is a clash of
index conventions rather than an error in either module.

Print's hidden decomposition is `(W_r ⊕ W_{a−r}) ⊕ (W_{b−r} ⊕ W_h)`: the `a` coordinates that
`A` lands on come **first**, so `A₁₁` is the identity. `OrbitNormalForm`'s `canonicalA` instead
places the image of `A` at hidden coordinates `[b−r, b−r+a)`, because its ordering is
`W_{b−r}` first, then `W_r`, then `W_{a−r}`, then `W_h` — the ordering in which `canonicalB`'s
description is simplest. The two are related by a permutation of the hidden coordinates, and
the chart is stated in print's while the base point is given in the other.

The consequence is concrete rather than cosmetic: whenever `b > r`, the `a × a` block of
`canonicalA` on the *first* `a` hidden coordinates is strictly below the diagonal and singular.
`det_canonicalA_toBlocks₁₁_eq_zero` exhibits this at the smallest stratum where every index
type is nonempty.

So the final assembly of `IsEliminationChart` cannot simply compose the pieces: it needs either
a permutation of the hidden coordinates inserted between `OrbitNormalForm` and the chart, or
`canonicalA`/`canonicalB` restated in print's ordering. Recording it here so that it is not
rediscovered as a mysterious failure of `elimPhi_elimPsi`'s hypothesis.

`ChartAssembly.lean` takes the first option: `elimHiddenIdxNF` is the hidden index composed
with `elimReorderEquiv`, and `canonicalA_reindex` shows that with it `A₁₁* = I_a` at every
feasible stratum. `OrbitNormalForm` is untouched. -/

/-- At the stratum `(M, N, H, r, a, b) = (3, 3, 4, 1, 2, 2)` — the smallest on which all six of
print's index types are nonempty — the `a × a` block of `canonicalA` on the first `a` hidden
and input coordinates is `(0 0 ; 1 0)`, whose determinant is `0`.

Hence the canonical representative is **not** in `ElimChartDomain` at this stratum, and
Theorem 5.1's chart, as constructed, does not apply at its own stated base point without an
intervening permutation. -/
public theorem det_canonicalA_toBlocks₁₁_eq_zero :
    ((canonicalA 3 4 2 2 1).submatrix
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4)) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3))).det
      = 0 := by
  rw [Matrix.det_fin_two]
  norm_num [canonicalA, selCols, Matrix.submatrix, Fin.castLE]

/-- The offending block, written out: `canonicalA` sends input `0` to hidden `1` and input `1`
to hidden `2`, so on hidden coordinates `{0, 1}` it is strictly subdiagonal. -/
public theorem canonicalA_toBlocks₁₁_entries :
    (canonicalA 3 4 2 2 1
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4) 0) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 0) = 0)
      ∧ (canonicalA 3 4 2 2 1
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4) 1) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 0) = 1)
      ∧ (canonicalA 3 4 2 2 1
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4) 0) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 1) = 0)
      ∧ (canonicalA 3 4 2 2 1
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4) 1) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 1) = 0) :=
  ⟨by norm_num [canonicalA, selCols, Fin.castLE], by norm_num [canonicalA, selCols, Fin.castLE],
    by norm_num [canonicalA, selCols, Fin.castLE],
    by norm_num [canonicalA, selCols, Fin.castLE]⟩


/-! ### The permutation that reconciles the two orderings

The clash above is repairable without touching `OrbitNormalForm`. `elimReorder` sends print's
hidden position to `OrbitNormalForm`'s:

    p < r          ↦ (b − r) + p     (print's `W_r`      is OrbitNormalForm's `[b−r, b)`)
    r ≤ p < a      ↦ b + (p − r)     (print's `W_{a−r}`  is `[b, b−r+a)`)
    a ≤ p < a+b−r  ↦ p − a           (print's `W_{b−r}`  is `[0, b−r)`)
    otherwise      ↦ p               (`W_h` is already last in both)

Reindexing the rows of `canonicalA` by it puts the identity back in the top-left `a × a` block,
which is print's `A₁₁* = I_a`. The content is one arithmetic equivalence,
`elimReorder_hits_iff`: for `p, j < a` the reordered row `elimReorder p` is the row
`canonicalA` fills for column `j` exactly when `p = j`.

This is stated rather than wired in, because *which* of the two orderings the atlas should
carry is a choice with consequences beyond this file — `OrbitNormalForm`'s is the one in which
`canonicalB` reads simplest, and Lemma 3.2 is proved against it. Both options are now costed:
either compose with `elimReorder` here, or restate the canonical pair in print's ordering and
re-prove Lemma 3.2's descriptions. -/

/-- The permutation from print's hidden ordering to `OrbitNormalForm`'s. -/
@[expose] public def elimReorder (a b r : ℕ) : ℕ → ℕ := fun p =>
  if p < r then (b - r) + p
  else if p < a then b + (p - r)
  else if p < a + (b - r) then p - a
  else p

/-- **The arithmetic content of the reordering.** For `p, j < a`, the reordered row is the one
`canonicalA` fills for column `j` exactly when `p = j`. Both branches of `elimReorder` in range
`p < a` collapse to this, the first because `(b−r) + p = j + (b−r) ↔ p = j` and the second
because `b + (p − r) = j + (b − r) ↔ p = j` once `r ≤ b`. -/
public theorem elimReorder_hits_iff {a b r : ℕ} (hrb : r ≤ b) {p j : ℕ} (hp : p < a) :
    elimReorder a b r p = j + (b - r) ↔ p = j := by
  unfold elimReorder
  split_ifs <;> omega

/-- **The reordering restores print's `A₁₁* = I_a`.** At the witness stratum
`(M, N, H, r, a, b) = (3, 3, 4, 1, 2, 2)`, reindexing the rows of `canonicalA` by `elimReorder`
makes the top-left `2 × 2` block the identity — compare
`det_canonicalA_toBlocks₁₁_eq_zero`, which is the same block before reordering. -/
public theorem det_canonicalA_reordered_eq_one :
    ((canonicalA 3 4 2 2 1).submatrix
        (fun p : Fin 2 => (⟨elimReorder 2 2 1 (p : ℕ), by fin_cases p <;> simp [elimReorder]⟩
          : Fin 4))
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3))).det = 1 := by
  rw [Matrix.det_fin_two]
  norm_num [canonicalA, selCols, Matrix.submatrix, elimReorder, Fin.castLE]

/-- The reordered block, entry by entry: the identity. -/
public theorem canonicalA_reordered_entries :
    (canonicalA 3 4 2 2 1 ⟨elimReorder 2 2 1 0, by simp [elimReorder]⟩
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 0) = 1)
      ∧ (canonicalA 3 4 2 2 1 ⟨elimReorder 2 2 1 0, by simp [elimReorder]⟩
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 1) = 0)
      ∧ (canonicalA 3 4 2 2 1 ⟨elimReorder 2 2 1 1, by simp [elimReorder]⟩
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 0) = 0)
      ∧ (canonicalA 3 4 2 2 1 ⟨elimReorder 2 2 1 1, by simp [elimReorder]⟩
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 1) = 1) :=
  ⟨by norm_num [canonicalA, selCols, elimReorder, Fin.castLE],
    by norm_num [canonicalA, selCols, elimReorder, Fin.castLE],
    by norm_num [canonicalA, selCols, elimReorder, Fin.castLE],
    by norm_num [canonicalA, selCols, elimReorder, Fin.castLE]⟩


/-! ### The reordering is a bijection, so it can simply be composed in

The choice of which ordering the *atlas* should present is a real one, and it is left open. But
it does not block the chart: `elimReorder` is a bijection of `Fin H`, so composing the chart
with the induced permutation of the hidden coordinates moves the base point into the domain
without touching `OrbitNormalForm` at all. That composition is additive and reversible, and it
is what `chart_transport` is for.

The inverse sends `OrbitNormalForm`'s hidden position back to print's, by reading the four
ranges the other way. Both round trips are pure arithmetic on the four branches. -/

/-- The inverse of `elimReorder`: `OrbitNormalForm`'s hidden position back to print's. -/
@[expose] public def elimReorderInv (a b r : ℕ) : ℕ → ℕ := fun q =>
  if q < b - r then a + q
  else if q < b then q - (b - r)
  else if q < a + (b - r) then r + (q - b)
  else q

public theorem elimReorderInv_elimReorder {a b r : ℕ} (hra : r ≤ a) (hrb : r ≤ b) (p : ℕ) :
    elimReorderInv a b r (elimReorder a b r p) = p := by
  unfold elimReorder elimReorderInv
  split_ifs <;> omega

public theorem elimReorder_elimReorderInv {a b r : ℕ} (hra : r ≤ a) (hrb : r ≤ b) (q : ℕ) :
    elimReorder a b r (elimReorderInv a b r q) = q := by
  unfold elimReorder elimReorderInv
  split_ifs <;> omega

public theorem elimReorder_lt {a b r H : ℕ} (hra : r ≤ a) (hrb : r ≤ b)
    (hH : a + (b - r) ≤ H) {p : ℕ} (hp : p < H) : elimReorder a b r p < H := by
  unfold elimReorder
  split_ifs <;> omega

public theorem elimReorderInv_lt {a b r H : ℕ} (hrb : r ≤ b) (hH : a + (b - r) ≤ H)
    {q : ℕ} (hq : q < H) : elimReorderInv a b r q < H := by
  unfold elimReorderInv
  split_ifs <;> omega

/-- **The reordering, as a permutation of the hidden coordinates.** With this the chart can be
composed with a relabelling of `Fin H` and applied at `OrbitNormalForm`'s canonical
representative, leaving that module untouched. -/
@[expose] public def elimReorderEquiv {a b r H : ℕ} (hra : r ≤ a) (hrb : r ≤ b)
    (hH : a + (b - r) ≤ H) : Fin H ≃ Fin H where
  toFun p := ⟨elimReorder a b r (p : ℕ), elimReorder_lt hra hrb hH p.isLt⟩
  invFun q := ⟨elimReorderInv a b r (q : ℕ), elimReorderInv_lt hrb hH q.isLt⟩
  left_inv p := by
    ext
    exact elimReorderInv_elimReorder hra hrb (p : ℕ)
  right_inv q := by
    ext
    exact elimReorder_elimReorderInv hra hrb (q : ℕ)

/-- The permutation acts on `canonicalA` exactly as intended: for `p, j < a`, the reordered row
carries a `1` at column `j` precisely when `p = j`, so the top-left `a × a` block becomes the
identity. This is `elimReorder_hits_iff` transported to the `Fin` level. -/
public theorem canonicalA_reorderEquiv_entry {N H a b r : ℕ} (hra : r ≤ a) (hrb : r ≤ b)
    (hH : a + (b - r) ≤ H) (p : Fin H) (j : Fin N) (hp : (p : ℕ) < a) (hj : (j : ℕ) < a) :
    canonicalA N H a b r (elimReorderEquiv hra hrb hH p) j =
      if (p : ℕ) = (j : ℕ) then 1 else 0 := by
  show (if (elimReorder a b r (p : ℕ)) = (if (j : ℕ) < a then (j : ℕ) + (b - r) else H)
    then (1:ℝ) else 0) = _
  rw [if_pos hj]
  by_cases h : (p : ℕ) = (j : ℕ)
  · rw [if_pos ((elimReorder_hits_iff hrb hp).2 h), if_pos h]
  · rw [if_neg (fun hc => h ((elimReorder_hits_iff hrb hp).1 hc)), if_neg h]


/-! ### The chart's ingredients at the base point

Print: "`X` vanishes at the base and `R(D*) = I_M`", and Step 1's `A₁₁* = I_a`. The first two
of those are computations about `canonicalA` in print's ordering, and they are done here.

`canonicalA` is a column-selection matrix that fills a row only for input columns `j < a`, and
after reordering it fills exactly the rows `p < a`. So both off-diagonal blocks vanish:
`A₁₂ = 0` because the columns `j ≥ a` are empty, and `A₂₁ = 0` because the rows `p ≥ a` are.
Hence `X = A₁₁⁻¹A₁₂ = 0` and `L(A)⁻¹ = (A₁₁ 0 ; A₂₁ I) = I`, so `B̄ = B` at the base point —
print's gauge is trivial there, which is what makes `D* = D` and `P_{top}(D*) = I_b`. -/

/-- `canonicalA` has no entries in the columns `j ≥ a`: those inputs are sent to the
out-of-range row `H`. -/
public theorem canonicalA_col_zero_of_ge {N H a b r : ℕ} (i : Fin H) (j : Fin N)
    (hj : a ≤ (j : ℕ)) : canonicalA N H a b r i j = 0 := by
  show (if (i : ℕ) = (if (j : ℕ) < a then (j : ℕ) + (b - r) else H) then (1:ℝ) else 0) = 0
  rw [if_neg (show ¬ ((j : ℕ) < a) by omega),
    if_neg (show (i : ℕ) ≠ H by have := i.isLt; omega)]

/-- After reordering, `canonicalA` has no entries in the rows `p ≥ a`: the four branches of
`elimReorder` send `p ≥ a` outside the range `[b−r, b−r+a)` that `canonicalA` fills. -/
public theorem canonicalA_reorderEquiv_row_zero {N H a b r : ℕ} (hra : r ≤ a) (hrb : r ≤ b)
    (hH : a + (b - r) ≤ H) (p : Fin H) (hp : a ≤ (p : ℕ)) (j : Fin N) :
    canonicalA N H a b r (elimReorderEquiv hra hrb hH p) j = 0 := by
  by_cases hj : a ≤ (j : ℕ)
  · exact canonicalA_col_zero_of_ge _ j hj
  · have hinner : (if (j : ℕ) < a then (j : ℕ) + (b - r) else H) = (j : ℕ) + (b - r) :=
      if_pos (by omega)
    have hne : elimReorder a b r (p : ℕ) ≠ (j : ℕ) + (b - r) := by
      unfold elimReorder
      split_ifs <;> omega
    show (if elimReorder a b r (p : ℕ) = (if (j : ℕ) < a then (j : ℕ) + (b - r) else H)
      then (1:ℝ) else 0) = 0
    rw [hinner, if_neg hne]

/-- **`A₁₂ = 0` at the base point**: the reordered `canonicalA` is zero on the input columns
`j ≥ a`, so print's `X = A₁₁⁻¹A₁₂` vanishes there. -/
public theorem canonicalA_A12_zero {N H a b r : ℕ} (hra : r ≤ a) (hrb : r ≤ b)
    (hH : a + (b - r) ≤ H) (p : Fin H) (j : Fin N) (hj : a ≤ (j : ℕ)) :
    canonicalA N H a b r (elimReorderEquiv hra hrb hH p) j = 0 :=
  canonicalA_col_zero_of_ge _ j hj

/-- **`A₂₁ = 0` at the base point**, so print's `L(A)⁻¹ = (A₁₁ 0 ; A₂₁ I)` is the identity
there and the gauge is trivial: `B̄ = B`. -/
public theorem canonicalA_A21_zero {N H a b r : ℕ} (hra : r ≤ a) (hrb : r ≤ b)
    (hH : a + (b - r) ≤ H) (p : Fin H) (hp : a ≤ (p : ℕ)) (j : Fin N) :
    canonicalA N H a b r (elimReorderEquiv hra hrb hH p) j = 0 :=
  canonicalA_reorderEquiv_row_zero hra hrb hH p hp j

/-- The three facts together, at the witness stratum: the reordered `canonicalA` is the
`a × a` identity in the top-left and zero in both off-diagonal blocks. `A₁₂` is empty of
entries because `N − a = 1` column is unused; `A₂₁` because `H − a = 2` rows are. -/
public theorem canonicalA_reordered_block_structure :
    (canonicalA 3 4 2 2 1 ⟨elimReorder 2 2 1 0, by simp [elimReorder]⟩
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 0) = 1)
      ∧ (canonicalA 3 4 2 2 1 ⟨elimReorder 2 2 1 1, by simp [elimReorder]⟩
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 1) = 1)
      ∧ (∀ i : Fin 4, canonicalA 3 4 2 2 1 i ⟨2, by norm_num⟩ = 0)
      ∧ (∀ j : Fin 3, canonicalA 3 4 2 2 1 ⟨elimReorder 2 2 1 2, by simp [elimReorder]⟩ j = 0) :=
  ⟨by norm_num [canonicalA, selCols, elimReorder, Fin.castLE],
    by norm_num [canonicalA, selCols, elimReorder, Fin.castLE],
    fun i => canonicalA_col_zero_of_ge i ⟨2, by norm_num⟩ (by norm_num),
    fun j => canonicalA_reorderEquiv_row_zero (a := 2) (b := 2) (r := 1) (H := 4)
      (by norm_num) (by norm_num) (by norm_num) ⟨2, by norm_num⟩ (by norm_num) j⟩


/-! ### `P(D*) = (I_b ; 0)`, and what it gives

Print's Step 3 states the base-point value outright: "`P(D*) = (I_b ; 0)`". Everything the
chart needs at the base point follows from that one equation, and the derivation is short
enough to be worth having separately from the computation of `D*` itself.

From `P(D) = (I_b ; 0)`: `P_{top} = I_b`, so `det P_{top} = 1` is a unit — the second of the
chart's two denominators survives. And `P_{bot} = 0`. Both Frobenius conditions of
`ElimChartNbhd` are then `0 < 1/4`, so the base point lies in print's `N₀` as well as in the
determinant locus.

Print's remark that `R(D*) = I_M` is the same fact read through `elimR`: with `P_{top} = I` and
`P_{bot} = 0`, `elimR = (I⁻¹ 0 ; −0·I⁻¹ I) = I`. -/

section BasePoint

variable {ρ τ π : Type*} [Fintype ρ] [Fintype τ] [Fintype π]
variable [DecidableEq ρ] [DecidableEq τ] [DecidableEq π]

omit [Fintype ρ] [Fintype τ] [Fintype π] [DecidableEq π] in
/-- From print's `P(D*) = (I_b ; 0)`, the top block is the identity. -/
public theorem elimPtop_eq_one_of_pblock {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ}
    {D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ}
    (h : elimPblock J D = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0) :
    elimPtop J D = 1 := by
  rw [elimPtop, h, Matrix.toRows₁_fromRows]

omit [Fintype ρ] [Fintype τ] [Fintype π] [DecidableEq π] in
/-- And the bottom block vanishes. -/
public theorem elimPbot_eq_zero_of_pblock {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ}
    {D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ}
    (h : elimPblock J D = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0) :
    elimPbot J D = 0 := by
  rw [elimPbot, h, Matrix.toRows₂_fromRows]

omit [Fintype π] [DecidableEq π] in
/-- **The second denominator survives at the base point**: `det P_{top}(D*) = 1`. -/
public theorem isUnit_det_elimPtop_of_pblock {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ}
    {D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ}
    (h : elimPblock J D = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0) :
    IsUnit (elimPtop J D).det := by
  rw [elimPtop_eq_one_of_pblock h, Matrix.det_one]
  exact isUnit_one

omit [DecidableEq π] in
/-- **Both of print's `N₀` conditions on `P` hold at the base point, with room to spare**: the
two Frobenius quantities are `0`. -/
public theorem frobeniusSq_elimP_zero_of_pblock {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ}
    {D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ}
    (h : elimPblock J D = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0) :
    frobeniusSq (elimPtop J D - 1) = 0 ∧ frobeniusSq (elimPbot J D) = 0 := by
  refine ⟨?_, ?_⟩
  · rw [elimPtop_eq_one_of_pblock h, sub_self, frobeniusSq_zero]
  · rw [elimPbot_eq_zero_of_pblock h, frobeniusSq_zero]

omit [Fintype π] in
/-- **Print's `R(D*) = I_M`**, the same fact read through `elimR`: with `P_{top} = I` and
`P_{bot} = 0` the normalizing factor is the identity, so Step 3 does nothing at the base
point. -/
public theorem elimR_eq_one_of_pblock {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ}
    {D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ}
    (h : elimPblock J D = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0) :
    elimR (elimPtop J D) (elimPbot J D) = 1 := by
  rw [elimR, elimPtop_eq_one_of_pblock h, elimPbot_eq_zero_of_pblock h]
  simp [Matrix.fromBlocks_one]

omit [Fintype ρ] [Fintype τ] [Fintype π] [DecidableEq π] in
/-- `P(D) = (I_b ; 0)` is equivalent to its two blocks being `I_b` and `0`, so the hypothesis
above is exactly print's display and nothing stronger. -/
public theorem pblock_eq_iff {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ}
    {D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ} :
    elimPblock J D = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0 ↔
      (elimPtop J D = 1 ∧ elimPbot J D = 0) := by
  constructor
  · intro h
    exact ⟨elimPtop_eq_one_of_pblock h, elimPbot_eq_zero_of_pblock h⟩
  · rintro ⟨h1, h2⟩
    rw [elimPtop] at h1
    rw [elimPbot] at h2
    rw [← Matrix.fromRows_toRows (elimPblock J D), h1, h2]

end BasePoint


/-! ### `D*` from `canonicalB`

The last base-point computation. At the base point the gauge is trivial (`A₂₁ = 0`, so
`L(A)⁻¹ = I` and `B̄ = B`), so `D*` is read straight off `canonicalB`: it is the block of
columns over `τ`, which in print's ordering is the range `[a, a+(b−r))`, and `elimReorder`
sends `a + t` there to `OrbitNormalForm`'s hidden position `t`.

`canonicalB` carries hidden `t < b − r` — that is `W_{b−r}` — to output `t + r`. So `D*` has a
single `1` in each column, at row `t + r`, and together with `J`'s inclusion of `W_r` at rows
`[0, r)` the pair `(J | D*)` is the identity on the first `b` output rows and zero below. That
is print's `P(D*) = (I_b ; 0)`, whose consequences are already derived. -/

/-- `elimReorder` sends print's `τ` block `[a, a+(b−r))` to `OrbitNormalForm`'s `[0, b−r)`,
which is where `canonicalB` keeps `W_{b−r}`. -/
public theorem elimReorder_tau {a b r t : ℕ} (hra : r ≤ a) (ht : t < b - r) :
    elimReorder a b r (a + t) = t := by
  unfold elimReorder
  split_ifs <;> omega

/-- **`canonicalB` on the `W_{b−r}` block.** Hidden position `q < b − r` is carried to output
`q + r`, so the column has a single `1` there. -/
public theorem canonicalB_col_lt {M H b r : ℕ} (i : Fin M) (q : Fin H)
    (hq : (q : ℕ) < b - r) :
    canonicalB M H b r i q = if (i : ℕ) = (q : ℕ) + r then 1 else 0 := by
  show (if (i : ℕ) = (if (q : ℕ) < b - r then (q : ℕ) + r
    else if (q : ℕ) < b then (q : ℕ) - (b - r) else M) then (1:ℝ) else 0) = _
  rw [if_pos hq]

/-- **`canonicalB` on the `W_r` block.** Hidden position `q ∈ [b−r, b)` is carried to output
`q − (b−r)`, which lies in `[0, r)`. Together with the previous lemma this is the whole of
`canonicalB` on the `b` hidden coordinates it does not kill. -/
public theorem canonicalB_col_mid {M H b r : ℕ} (i : Fin M) (q : Fin H)
    (hq₁ : b - r ≤ (q : ℕ)) (hq₂ : (q : ℕ) < b) :
    canonicalB M H b r i q = if (i : ℕ) = (q : ℕ) - (b - r) then 1 else 0 := by
  have hg : (if (q : ℕ) < b - r then (q : ℕ) + r
      else if (q : ℕ) < b then (q : ℕ) - (b - r) else M) = (q : ℕ) - (b - r) := by
    rw [if_neg (show ¬ ((q : ℕ) < b - r) by omega), if_pos hq₂]
  show (if (i : ℕ) = (if (q : ℕ) < b - r then (q : ℕ) + r
    else if (q : ℕ) < b then (q : ℕ) - (b - r) else M) then (1:ℝ) else 0) = _
  rw [hg]

/-- **`canonicalB` kills everything above `b`** — that is `W_{a−r} ⊕ W_h ⊆ ker B`, print's
description. -/
public theorem canonicalB_col_zero_of_ge {M H b r : ℕ} (i : Fin M) (q : Fin H)
    (hq : b ≤ (q : ℕ)) : canonicalB M H b r i q = 0 := by
  have hg : (if (q : ℕ) < b - r then (q : ℕ) + r
      else if (q : ℕ) < b then (q : ℕ) - (b - r) else M) = M := by
    rw [if_neg (show ¬ ((q : ℕ) < b - r) by omega), if_neg (show ¬ ((q : ℕ) < b) by omega)]
  show (if (i : ℕ) = (if (q : ℕ) < b - r then (q : ℕ) + r
    else if (q : ℕ) < b then (q : ℕ) - (b - r) else M) then (1:ℝ) else 0) = 0
  rw [hg, if_neg (show (i : ℕ) ≠ M by have := i.isLt; omega)]

/-- **`P(D*) = (I_b ; 0)` at the witness stratum.** The three output rows against the two
columns of `(J | D*)`: `J`'s column puts a `1` at row `0`, `D*`'s at row `0 + r = 1`, and row
`2` — the `π` block — is empty. So the top `2 × 2` block is the identity and the bottom row
vanishes, which is print's display. -/
public theorem pblock_base_witness :
    (∀ i : Fin 3, (if (i : ℕ) = 0 then (1:ℝ) else 0) =
        if (i : ℕ) = 0 then (1:ℝ) else 0)
      ∧ canonicalB 3 4 2 1 ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 1
      ∧ canonicalB 3 4 2 1 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 0
      ∧ canonicalB 3 4 2 1 ⟨2, by norm_num⟩ ⟨0, by norm_num⟩ = 0 :=
  ⟨fun _ => rfl,
    by rw [canonicalB_col_lt _ _ (by norm_num)]; norm_num,
    by rw [canonicalB_col_lt _ _ (by norm_num)]; norm_num,
    by rw [canonicalB_col_lt _ _ (by norm_num)]; norm_num⟩

/-! ## The statement of Theorem 5.1 -/

/-- The parameter space of the reduced-rank model: a pair `(A, B)` of shapes `H × N` and
`M × H`, of total dimension `HN + MH`. -/
public abbrev ParamSpace (M N H : ℕ) : Type :=
  Matrix (Fin H) (Fin N) ℝ × Matrix (Fin M) (Fin H) ℝ

/-- The target of the chart: `ℝ^q × ℝ^{p×h} × ℝ^{h×n} × ℝ^g`, the four blocks
`(u, Y₀, S_Z, v)` of `Ψ`. -/
public abbrev ChartSpace (q p h n g : ℕ) : Type :=
  EuclideanSpace ℝ (Fin q) × Matrix (Fin p) (Fin h) ℝ × Matrix (Fin h) (Fin n) ℝ ×
    EuclideanSpace ℝ (Fin g)

/-- **The body of Theorem 5.1's conclusion**, at an explicit base point, truth matrix and
tuple of chart dimensions. Split out from `IsEliminationChart` so that the dimensions can be
computed before the statement is instantiated.

"Analytic diffeomorphism `Ψ : O ⟶ O'`" is read as: `O` and `O'` open, `Ψ` a bijection of `O`
onto `O'` with a two-sided inverse `Φ` on those sets, and both `Ψ` and `Φ` analytic on a
neighborhood of each point of their domains. -/
@[expose] public noncomputable def HasEliminationChartAt {M N H : ℕ}
    (C : Matrix (Fin M) (Fin N) ℝ) (Astar : Matrix (Fin H) (Fin N) ℝ)
    (Bstar : Matrix (Fin M) (Fin H) ℝ) (q p h n g : ℕ) : Prop :=
  ∃ (O : Set (ParamSpace M N H)) (O' : Set (ChartSpace q p h n g))
    (Ψ : ParamSpace M N H → ChartSpace q p h n g)
    (Φ : ChartSpace q p h n g → ParamSpace M N H),
    IsOpen O ∧ IsOpen O' ∧ (Astar, Bstar) ∈ O ∧
      Set.BijOn Ψ O O' ∧ Set.InvOn Φ Ψ O O' ∧
      AnalyticOnNhd ℝ Ψ O ∧ AnalyticOnNhd ℝ Φ O' ∧ Ψ (Astar, Bstar) = 0 ∧
      ∀ w ∈ O,
        1 / 12 * comparisonGerm (Ψ w).1 (Ψ w).2.1 (Ψ w).2.2.1 ≤ 2 * rrrLoss C w.1 w.2 ∧
          2 * rrrLoss C w.1 w.2 ≤ 6 * comparisonGerm (Ψ w).1 (Ψ w).2.1 (Ψ w).2.2.1

/-- **Theorem 5.1 (Elimination), p. 10.** At the canonical representative `(A*, B*)` of the
stratum `(a, b, r)` — `canonicalA`/`canonicalB` of `OrbitNormalForm.lean`, over the truth
matrix `C = B*A* = partialIdMatrix M N r` supplied by `canonicalB_mul_canonicalA` — there is
an open neighborhood carrying an analytic chart in which `2K` is two-sidedly comparable to
`‖u‖² + ‖Y₀S_Z‖²_F` with the uniform constants `1/12` and `6`.

Nothing in *this file* proves it for a general stratum: `isEliminationChart_zero` below is the
only instance established here, and it is degenerate. The general theorem is
`isEliminationChart_of_feasible` in `ChartAssembly.lean`, which needs the base point of
`OrbitNormalForm` and so cannot be stated before that module's contents are available. -/
@[expose] public noncomputable def IsEliminationChart (M N H r a b : ℕ) : Prop :=
  HasEliminationChartAt (partialIdMatrix M N r) (canonicalA N H a b r) (canonicalB M H b r)
    (elimQ M N a b) (elimP M b) (elimH H r a b) (elimN N a) (elimGauge M N H r a b)

/-! ## A witness: the statement is inhabited

At `(a, b, r) = (0, 0, 0)` the truth matrix and both canonical factors vanish, the transverse
and gauge blocks are empty, and the residual shape is the whole of `(M, H, N)`. The chart is
then the identity rearrangement `(A, B) ↦ (0, B, A, 0)`, and print's comparison function is
`‖B A‖²_F = 2K` on the nose, so the two-sided bound holds with constant `1` — comfortably
inside `[1/12, 6]`.

This proves nothing about the general theorem, which is `isEliminationChart_of_feasible` in
`ChartAssembly.lean`. It is kept because it is independent of that assembly: it certifies that
`IsEliminationChart` elaborates and that its dimension bookkeeping is consistent, by a chart
written out by hand rather than transported, so a defect in the transport cannot hide here. -/

private theorem eq_zero_of_fin_zero (x : EuclideanSpace ℝ (Fin 0)) : x = 0 := by
  ext i
  exact absurd i.isLt (by omega)

public theorem canonicalA_zero (N H : ℕ) : canonicalA N H 0 0 0 = 0 := by
  ext i j
  simp only [canonicalA, selCols, Matrix.of_apply, Matrix.zero_apply]
  rw [if_neg (by have := i.isLt; simp only [Nat.not_lt_zero, if_false]; omega)]

public theorem canonicalB_zero (M H : ℕ) : canonicalB M H 0 0 = 0 := by
  ext i j
  simp only [canonicalB, selCols, Matrix.of_apply, Matrix.zero_apply]
  rw [if_neg (by have := i.isLt; simp only [Nat.sub_self, Nat.not_lt_zero, if_false]; omega)]

public theorem partialIdMatrix_zero (M N : ℕ) : partialIdMatrix M N 0 = 0 := by
  ext i j
  simp [partialIdMatrix]

/-- **The statement is satisfiable.** Theorem 5.1 holds at the degenerate stratum
`(a, b, r) = (0, 0, 0)`, with `Ψ` the identity rearrangement and comparison constant `1`. -/
public theorem isEliminationChart_zero (M N H : ℕ) : IsEliminationChart M N H 0 0 0 := by
  rw [IsEliminationChart, canonicalA_zero, canonicalB_zero, partialIdMatrix_zero,
    show elimQ M N 0 0 = 0 from by simp [elimQ], show elimP M 0 = M from rfl,
    show elimH H 0 0 0 = H from by simp [elimH], show elimN N 0 = N from rfl,
    show elimGauge M N H 0 0 0 = 0 from by simp [elimGauge, elimN, elimH]]
  classical
  set F1 := Matrix (Fin M) (Fin H) ℝ with hF1
  set F2 := Matrix (Fin H) (Fin N) ℝ with hF2
  set F3 := EuclideanSpace ℝ (Fin 0) with hF3
  refine ⟨Set.univ, Set.univ, fun w => ((0 : F3), w.2, w.1, (0 : F3)),
    fun z => (z.2.2.1, z.2.1), isOpen_univ, isOpen_univ, Set.mem_univ _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨Set.mapsTo_univ _ _, fun x _ y _ hxy => ?_, fun z _ => ⟨(z.2.2.1, z.2.1),
      Set.mem_univ _, ?_⟩⟩
    · have h1 : x.2 = y.2 := congrArg (fun t => t.2.1) hxy
      have h2 : x.1 = y.1 := congrArg (fun t => t.2.2.1) hxy
      exact Prod.ext h2 h1
    · refine Prod.ext (eq_zero_of_fin_zero z.1).symm (Prod.ext rfl (Prod.ext rfl ?_))
      exact (eq_zero_of_fin_zero z.2.2.2).symm
  · exact ⟨fun _ _ => rfl, fun z _ => Prod.ext (eq_zero_of_fin_zero z.1).symm
      (Prod.ext rfl (Prod.ext rfl (eq_zero_of_fin_zero z.2.2.2).symm))⟩
  · refine AnalyticOnNhd.prod analyticOnNhd_const (AnalyticOnNhd.prod ?_
      (AnalyticOnNhd.prod ?_ analyticOnNhd_const))
    · exact (ContinuousLinearMap.snd ℝ F2 F1).analyticOnNhd _
    · exact (ContinuousLinearMap.fst ℝ F2 F1).analyticOnNhd _
  · refine AnalyticOnNhd.prod ?_ ?_
    · exact ((ContinuousLinearMap.fst ℝ F2 F3).comp
        ((ContinuousLinearMap.snd ℝ F1 (F2 × F3)).comp
          (ContinuousLinearMap.snd ℝ F3 (F1 × F2 × F3)))).analyticOnNhd _
    · exact ((ContinuousLinearMap.fst ℝ F1 (F2 × F3)).comp
        (ContinuousLinearMap.snd ℝ F3 (F1 × F2 × F3))).analyticOnNhd _
  · rfl
  · rintro ⟨A, B⟩ -
    have hK : 2 * rrrLoss (0 : Matrix (Fin M) (Fin N) ℝ) A B = frobeniusSq (B * A) := by
      rw [rrrLoss_eq_sum_sq, sub_zero]
      simp [frobeniusSq]
    have hG : comparisonGerm (0 : F3) B A = frobeniusSq (B * A) := by
      simp [comparisonGerm]
    have hnn : 0 ≤ frobeniusSq (B * A) := frobeniusSq_nonneg _
    rw [hK, hG]
    constructor <;> linarith

end AISafetyAtlas.SingularLearning
