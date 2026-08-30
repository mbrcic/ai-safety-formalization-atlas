module

public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Set.Card
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.Permutation
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# MAIS-O38 — polynomially many samples for growing sparsity

`prob:samples`, MAIS-A3 Problem 4.8. Print asks whether a *polynomial* number of
`k`-sparse codes can pin a generic dictionary once the sparsity `k` grows with
the number of features `m`.

This module is the statement layer only. It defines print's *uniquely coded*
relation, print's spark condition of order `k`, and the printed question.
Defining a proposition asserts nothing about its truth; everything proved about
these definitions lives in `AISafetyAtlas/Examples/Conjectures/MAIS/O38.lean`.

Unlike every other `MAIS/*` module here, the source is agenda **A3**, not A2, and
none of this module's vocabulary is shared with the causal layer. Both agendas
are pinned in `docs/provenance/mais-source-pin.md`.

## The one place print leaves a quantifier unwritten

Print writes *"Let `k = k(m) → ∞` … and `n ≥ 2k`"* and *"`N` bounded by a
polynomial in `m`"*, and then never quantifies `m` itself. Both surrounding
clauses are asymptotic — a polynomial bound is a statement about growth, and
`k(m) → ∞` is a statement about large `m` — so `maisO38_polynomialSamplesSuffice`
reads the missing quantifier as *"for all sufficiently large `m`"*.

That reading is not free and it is the one interpretive choice in this module, so
here is what turns on it. Under the strictest alternative — a design at *every*
`m` — the printed sentence is **false**, and for a reason that is about small `m`
rather than about sparse coding: `maisO38_everyDimensionReading` is refuted by
`not_maisO38_everyDimensionReading`, at `m = 1`, where the sparsity is zero, every
code is the zero vector and the dataset is `{0}`. Print's own named family
`k = ⌈log m⌉` has `k 1 = 0`, so the strict reading is not one print's examples
survive either. On the eventual reading print's own hypothesis does the work
instead: `eventually_one_le_sparsity` derives `1 ≤ k m` for large `m` from
`k(m) → ∞`, so no atlas-supplied condition on `k` appears anywhere below.

## The second unwritten quantifier: what `k` ranges over

Print says `k = k(m) → ∞` and never says `k(m) < m`. Read without that, the
printed sentence is **false for a reason with no sparse-coding content**: at
`k(m) = m` every vector in `ℝᵐ` is `k`-sparse, a transvection reproduces any
dataset with rescaled codes, and no design of any size works at any dictionary —
`not_maisO38_unboundedSparsityReading`. Worse, that witness is forced into
`m < n` by print's own `n ≥ 2k` (`rows_gt_cols_of_full_sparsity_spark`), an
undercomplete dictionary, where §2 of the agenda places superposition at `m > n`.

So the domain is read as eventually `k m < m`, and the wider reading is carried
beside it, refuted, exactly as `maisO38_everyDimensionReading` is.

**`maisO38_polynomialSamplesSuffice` is true**, and
`AISafetyAtlas.Examples.Conjectures.MAIS.maisO38_polynomialSamplesSuffice_holds`
proves it — by way of the candidate submitted as MAIS issue #30, whose
construction and argument are not the atlas's. Print's named families
`k = ⌈m^α⌉` and `k = ⌈log m⌉` are instances of the universal, so they are
answered too. The two refuted readings above stay where they are: they are
findings about quantifiers print leaves unwritten, and neither is an answer.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open Matrix MeasureTheory

/-! ## Print's vocabulary -/

/-- Print: *"a vector is `k`-sparse if at most `k` of its entries are nonzero"*.

`Function.support v` is `{j | v j ≠ 0}` and `Set.ncard` counts it, so this is the
printed sentence and not a proxy for it. `isKSparse_zero_iff` and
`isKSparse_of_card_le` pin the two boundary readings. -/
@[expose] public noncomputable def IsKSparse (k : ℕ) {m : ℕ} (v : Fin m → ℝ) : Prop :=
  (Function.support v).ncard ≤ k

/-- Print's **spark condition of order `k`**: *"every set of at most `2k` columns
linearly independent"*, with print's own parenthetical that it *"applies verbatim
to matrices with non-unit columns"* — nothing here normalizes a column.

`A.col j` is Mathlib's `j`-th column of `A`, so the family being tested is a set
of columns indexed by a set of column indices, which is the standard spark
condition `spark(A) > 2k`. -/
@[expose] public def SparkCondition (k : ℕ) {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : Prop :=
  ∀ S : Finset (Fin m), S.card ≤ 2 * k → LinearIndependent ℝ fun j : S => A.col (j : Fin m)

/-- Print's *"permutation matrix `P`"*.

`Equiv.Perm.permMatrix` is onto the permutation matrices by definition — a
permutation matrix *is* one of that form — so this is a transcription and not a
chart standing in for a larger class. -/
@[expose] public def IsPermutationMatrix {m : ℕ} (P : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∃ σ : Equiv.Perm (Fin m), P = σ.permMatrix ℝ

/-- Print's *"invertible diagonal matrix `D`"*.

A diagonal matrix over a field is invertible exactly when no diagonal entry
vanishes, so the nonvanishing clause is the printed adjective rather than an
extra demand; `IsInvertibleDiagonal.isUnit` records the direction that is used. -/
@[expose] public def IsInvertibleDiagonal {m : ℕ} (D : Matrix (Fin m) (Fin m) ℝ) : Prop :=
  ∃ d : Fin m → ℝ, (∀ j, d j ≠ 0) ∧ D = Matrix.diagonal d

/--
**Print's *uniquely coded*, verbatim.**

*"Call a dataset `Y = {A x₁, …, A x_N} ⊆ ℝⁿ`, generated by a matrix
`A ∈ ℝ^{n×m}` and `k`-sparse codes `xᵢ ∈ ℝᵐ`, uniquely coded if for every
`B ∈ ℝ^{n×m}` and `k`-sparse `x̄₁, …, x̄_N` with `B x̄ᵢ = A xᵢ` for all `i`, there
are a permutation matrix `P` and invertible diagonal matrix `D` with `B = APD`
and `x̄ᵢ = D⁻¹P⁻¹xᵢ`."*

**Family, not set.** Print writes `Y` with set braces and then states the
condition index by index — `B x̄ᵢ = A xᵢ` *for all `i`*, and `x̄ᵢ = D⁻¹P⁻¹xᵢ` at
the matching index. An indexed family is what carries that; a `Set` would drop
the pairing the printed condition relies on, and would also silently collapse
repeated codes.

**The inverses are genuine.** `Matrix.inv` returns `0` on a singular matrix, so a
statement mentioning `D⁻¹` has a junk branch in general. Here it has none:
`IsInvertibleDiagonal D` and `IsPermutationMatrix P` make both factors units
(`IsInvertibleDiagonal.isUnit`, `IsPermutationMatrix.isUnit`), so `D⁻¹` and
`P⁻¹` are the true inverses at every point where this proposition is used. -/
@[expose] public noncomputable def UniquelyCoded (k : ℕ) {n m N : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin N → (Fin m → ℝ)) : Prop :=
  ∀ (B : Matrix (Fin n) (Fin m) ℝ) (x' : Fin N → (Fin m → ℝ)),
    (∀ i, IsKSparse k (x' i)) → (∀ i, B *ᵥ x' i = A *ᵥ x i) →
      ∃ P D : Matrix (Fin m) (Fin m) ℝ,
        IsPermutationMatrix P ∧ IsInvertibleDiagonal D ∧
          B = A * P * D ∧ ∀ i, x' i = (D⁻¹ * P⁻¹) *ᵥ x i

/--
A design of `N` `k`-sparse codes in `ℝᵐ` that works *"for almost every `A`
satisfying the spark condition of order `k`"*.

The measure is print's own: *"almost every refers to Lebesgue measure on
`ℝ^{n×m}`"*. Mathlib at the pinned revision carries no
`MeasureTheory.MeasureSpace` instance on `Matrix`, so the quantifier runs over
the function type `Fin n → Fin m → ℝ`,
whose `volume` is the `n·m`-fold product of Lebesgue measure, and `Matrix.of` —
the identity equivalence — presents each sample as a matrix. Naming a different
measure here would change the theorem, so it is named rather than left implicit.

*"almost every `A` satisfying the spark condition"* is read as the a.e.
implication rather than as an a.e. statement for the restricted measure; the two
agree wherever the spark set is measurable, and the implication needs no such
side condition. -/
@[expose] public noncomputable def GenericallyUniquelyCoding (k n m N : ℕ)
    (x : Fin N → (Fin m → ℝ)) : Prop :=
  (∀ i, IsKSparse k (x i)) ∧
    ∀ᵐ A : Fin n → Fin m → ℝ,
      SparkCondition k (Matrix.of A) → UniquelyCoded k (Matrix.of A) x

/-! ## The printed question -/

/--
The affirmative branch of `prob:samples` at one growth law `k` and one ambient
dimension law `n`: *"Do there exist `N` bounded by a polynomial in `m` and
`k`-sparse `x₁, …, x_N` such that for almost every `A` satisfying the spark
condition of order `k`, the dataset `Y` is uniquely coded?"*

*"bounded by a polynomial in `m`"* is a single `p : Polynomial ℕ` dominating `N`
at every `m`; the polynomial is chosen before `m`, which is what makes the bound
a growth statement rather than a tautology. Coefficients in `ℕ` cost nothing: a
real polynomial dominating a `ℕ`-valued function is itself dominated on `ℕ` by
one with natural coefficients. The bound is required at every `m` and not merely
eventually, which is the stronger of the two and so makes this affirmative branch
harder rather than easier.

The design requirement is at `Filter.atTop` — see this module's header for the
one printed quantifier that is unwritten and why it is read this way. -/
@[expose] public noncomputable def O38PolynomialSampleAnswer (k n : ℕ → ℕ) : Prop :=
  ∃ (N : ℕ → ℕ) (p : Polynomial ℕ),
    (∀ m, N m ≤ p.eval m) ∧
      ∀ᶠ m in Filter.atTop,
        ∃ x : Fin (N m) → (Fin m → ℝ), GenericallyUniquelyCoding (k m) (n m) m (N m) x

/--
**MAIS-O38, affirmative branch.** The open question.

*"Let `k = k(m) → ∞` … and `n ≥ 2k`"* is the universal quantifier over both
growth laws; `Filter.Tendsto k Filter.atTop Filter.atTop` is *"`k(m) → ∞`"* and
`2 * k m ≤ n m` is *"`n ≥ 2k`"*, both at print's own strength and with no
condition on `k` beyond the printed one.

Print's two named families, `k = ⌈m^α⌉` with `α ∈ (0,1)` and `k = ⌈log m⌉`, are
instances of this universal rather than the whole of it. Print says the question
is open *"even at `k = ⌈log m⌉`"*, so a negative answer at some other admissible
growth law would not settle those instances.

**`k m < m` is print's unwritten domain for `k`, not an atlas hypothesis.** Print
says what `k` *tends to* and never says what it ranges over, and two of its own
phrases presuppose the answer: *"`k`-sparse codes `xᵢ ∈ ℝᵐ`"* is no condition at
all once `m ≤ k`, and *"the spark condition of order `k`"* — every set of at most
`2k` columns independent — is a condition on a dictionary in `U_{n,m}`, where §2
of the agenda places superposition at `m > n`, so `2k ≤ n < m` already. Reading
the domain as eventually `k m < m` is therefore of the same kind as reading the
`m`-quantifier at `Filter.atTop`, and it is recorded the same way: the wider
reading is `maisO38_unboundedSparsityReading`, it is **false**, and
`not_maisO38_unboundedSparsityReading` proves it. The condition is *eventual*
rather than at every `m` because print's own `k = ⌈m^α⌉` has `k 1 = 1 = m`, so a
demand at every `m` would exclude a family print names. -/
@[expose] public noncomputable def maisO38_polynomialSamplesSuffice : Prop :=
  ∀ k n : ℕ → ℕ, Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ m, 2 * k m ≤ n m) → (∀ᶠ m in Filter.atTop, k m < m) →
      O38PolynomialSampleAnswer k n

/--
**MAIS-O38 with `k` unbounded by the number of features**, the reading in which
print's *"`k`-sparse"* is allowed to constrain nothing.

This is **false** — `not_maisO38_unboundedSparsityReading` — and the refutation
is a triviality about `k m = m`, where every vector in `ℝᵐ` is `k`-sparse, a
transvection reproduces the data, and no design of any size can work at any
dictionary. It is **not** an answer to `prob:samples`, and it is carried for the
same reason `maisO38_everyDimensionReading` is: so that the domain read for `k`
in `maisO38_polynomialSamplesSuffice` is a recorded finding about the printed
sentence rather than an unexplained preference. -/
@[expose] public noncomputable def maisO38_unboundedSparsityReading : Prop :=
  ∀ k n : ℕ → ℕ, Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ m, 2 * k m ≤ n m) → O38PolynomialSampleAnswer k n

/-! ## The submitted candidate -/

/--
**The candidate answer submitted as MAIS issue #30**, transcribed as a `Prop`.

*"Let `m ≥ 2` and `1 ≤ k < m`, and put `N = m³ + 2m`. There are `k`-sparse
vectors `x₁, …, x_N ∈ ℝᵐ`, depending only on `m` and `k`, such that for every
integer `n ≥ 2k` and for Lebesgue-almost every `A ∈ ℝ^{n×m}` satisfying the spark
condition of order `k`, the dataset `{Ax₁, …, Ax_N}` is uniquely coded."*

**Defining this asserts nothing.** It is not proved here, and no grade in this
repository depends on it being true. What it is for is
`maisO38_polynomialSamplesSuffice_of_candidate`, which discharges the one
question a reader of the issue should ask before spending any effort on it: does
this claim, if correct, actually answer the row?

Two places where the candidate is **stronger** than
`maisO38_polynomialSamplesSuffice` needs, both of them print's quantifier order
rather than the issue's. Print fixes `k` and `n` before asking for codes, so the
codes may depend on `n`; the candidate's depend only on `m` and `k`, and it
supplies one list good at every `n ≥ 2k` at once. And print asks only for a
design at sufficiently large `m`, where the candidate delivers one at every
`m ≥ 2`. Neither difference is repaired away: the `Prop` below is the issue's own
statement, and the implication absorbs the slack. -/
@[expose] public noncomputable def o38PolynomialSampleCandidate : Prop :=
  ∀ m k : ℕ, 2 ≤ m → 1 ≤ k → k < m →
    ∃ x : Fin (m ^ 3 + 2 * m) → (Fin m → ℝ),
      (∀ i, IsKSparse k (x i)) ∧
        ∀ n : ℕ, 2 * k ≤ n →
          ∀ᵐ A : Fin n → Fin m → ℝ,
            SparkCondition k (Matrix.of A) → UniquelyCoded k (Matrix.of A) x

/--
**MAIS-O38 with the design demanded at every `m`**, the strictest reading of the
quantifier print leaves unwritten.

This is **false** — `not_maisO38_everyDimensionReading` — and the refutation is a
statement about `m = 1` and not an answer to `prob:samples`. It is carried so
that the choice of `Filter.atTop` in `O38PolynomialSampleAnswer` is a recorded
finding about the printed sentence rather than an unexplained preference. -/
@[expose] public noncomputable def maisO38_everyDimensionReading : Prop :=
  ∀ k n : ℕ → ℕ, Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ m, 2 * k m ≤ n m) →
      ∃ (N : ℕ → ℕ) (p : Polynomial ℕ),
        (∀ m, N m ≤ p.eval m) ∧
          ∀ m, ∃ x : Fin (N m) → (Fin m → ℝ),
            GenericallyUniquelyCoding (k m) (n m) m (N m) x

/-! ## Observability of the transcribed vocabulary -/

/-- At sparsity zero the only `0`-sparse vector is `0`. -/
@[simp]
public theorem isKSparse_zero_iff {m : ℕ} {v : Fin m → ℝ} :
    IsKSparse 0 v ↔ v = 0 := by
  rw [IsKSparse, Nat.le_zero, Set.ncard_eq_zero (Set.toFinite _), Function.support_eq_empty_iff]

/-- At sparsity `m` and above nothing in `ℝᵐ` is constrained. -/
public theorem isKSparse_of_card_le {k m : ℕ} (h : m ≤ k) (v : Fin m → ℝ) : IsKSparse k v :=
  le_trans (le_trans (Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _))
    (by simp [Set.ncard_univ])) h

/-- Print's own hypothesis `k(m) → ∞` already rules out the zero-sparsity
degeneracy at large `m`, which is why `O38PolynomialSampleAnswer` needs no
condition on `k` of the atlas's own. -/
public theorem eventually_one_le_sparsity {k : ℕ → ℕ}
    (hk : Filter.Tendsto k Filter.atTop Filter.atTop) : ∀ᶠ m in Filter.atTop, 1 ≤ k m :=
  hk.eventually_ge_atTop 1

/-- A permutation matrix is invertible, so `P⁻¹` in `UniquelyCoded` is the true
inverse. -/
public theorem IsPermutationMatrix.isUnit {m : ℕ} {P : Matrix (Fin m) (Fin m) ℝ}
    (hP : IsPermutationMatrix P) : IsUnit P := by
  obtain ⟨σ, rfl⟩ := hP
  simp [Matrix.isUnit_iff_isUnit_det, Matrix.det_permutation]

/-- An invertible diagonal matrix is invertible, so `D⁻¹` in `UniquelyCoded` is
the true inverse. -/
public theorem IsInvertibleDiagonal.isUnit {m : ℕ} {D : Matrix (Fin m) (Fin m) ℝ}
    (hD : IsInvertibleDiagonal D) : IsUnit D := by
  obtain ⟨d, hd, rfl⟩ := hD
  rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal, isUnit_iff_ne_zero]
  exact Finset.prod_ne_zero_iff.2 fun j _ => hd j

/-- Once `m ≤ 2k` the spark condition reaches the full column set, so it is the
statement that `A` has independent columns. -/
public theorem SparkCondition.linearIndependent_col {k n m : ℕ}
    {A : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A) (hm : m ≤ 2 * k) :
    LinearIndependent ℝ A.col :=
  (linearIndependent_equiv (Equiv.subtypeUnivEquiv Finset.mem_univ)).1
    (hA Finset.univ (by simpa using hm))

/--
Print's `n ≥ 2k` is load-bearing rather than scene-setting: a matrix with `n` rows
carries at most `n` independent columns, so once `m` is large enough to name `2k`
of them the spark condition of order `k` forces `2k ≤ n`.

Without the hypothesis, `SparkCondition` is unsatisfiable in that regime and
`GenericallyUniquelyCoding` holds **vacuously for every design**, which would
make the affirmative branch of the printed question free. This is the
anti-vacuity check for `maisO38_polynomialSamplesSuffice`'s second binder. -/
public theorem SparkCondition.two_mul_le_rows {k n m : ℕ}
    {A : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A) (hm : 2 * k ≤ m) :
    2 * k ≤ n := by
  have huniv : 2 * k ≤ (Finset.univ : Finset (Fin m)).card := by simpa using hm
  obtain ⟨S, -, hcard⟩ := Finset.exists_subset_card_eq huniv
  have h := (hA S hcard.le).fintype_card_le_finrank
  simpa [hcard, Module.finrank_pi] using h

/-- The same fact as a statement about the map `A` induces. -/
public theorem SparkCondition.mulVec_injective {k n m : ℕ}
    {A : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A) (hm : m ≤ 2 * k) :
    Function.Injective A.mulVec :=
  Matrix.mulVec_injective_iff.2 (hA.linearIndependent_col hm)

end AISafetyAtlas.Conjectures.MAIS
