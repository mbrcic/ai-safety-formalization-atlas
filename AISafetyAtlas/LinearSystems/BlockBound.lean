module

public import AISafetyAtlas.LinearSystems.Hautus
public import Mathlib.LinearAlgebra.Eigenspace.Zero
public import Mathlib.LinearAlgebra.Eigenspace.Minpoly
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Minpoly

/-!
# Klamka's counting step, and the antecedent it belongs to

`AISafetyAtlas.LinearSystems.Hautus` carries Klamka's Theorem 1 and its three
corollaries **at the eigenspace dimension**, which is a strictly weaker
hypothesis than print's and therefore a strictly stronger theorem. What it did
not carry was **print's own antecedent**, which is stated in the multiplicities
of the characteristic and minimal polynomials and reaches the eigenspace through
a counting argument over the Jordan form.

This module supplies the counting step, without a Jordan form.

## The step

Print's equation (2) reads `αᵢ ≥ int[nᵢ/νᵢ]`, where `nᵢ` is the multiplicity of
`λᵢ` in the characteristic polynomial, `νᵢ` is its index, and `αᵢ` is the number
of Jordan blocks carrying `λᵢ` — which is the dimension of the eigenspace. Print
derives it from equation (1), `βᵢⱼ ≤ νᵢ`, by observing that `nᵢ` blocks of size
at most `νᵢ` need at least `nᵢ/νᵢ` of them.

`finrank_ker_pow_le` is the same count with no blocks in it: **the kernel of a
`k`-th power is at most `k` times the kernel**. It follows from
`finrank_ker_comp_le`, which is the two-map case, by induction. Neither is in
Mathlib at the pinned revision, and neither mentions eigenvalues.

`finrank_maxGenEigenspace_le_index_mul` is that applied at `f - μ`, and
`rootMultiplicity_le_mul_finrank_eigenspace` reads it through Mathlib's
`LinearMap.finrank_maxGenEigenspace_eq` — so the left side is literally print's
`nᵢ` and the right is `νᵢ * αᵢ`.

## Print's index

**Print's `νᵢ` is the multiplicity of `λᵢ` in the minimal polynomial**, while
Mathlib's `Module.End.maxGenEigenspaceIndex` is the stage at which the
generalized eigenspace chain stops growing. Print states the two are equal and
does not prove it, citing Zadeh and Desoer.

`maxGenEigenspaceIndex_eq_rootMultiplicity_minpoly` proves it, in the two halves
print's own wording asks for: the chain has stopped at that multiplicity
(`maxGenEigenspace_eq_genEigenspace_rootMultiplicity_minpoly`), and no smaller
exponent stops it (`rootMultiplicity_minpoly_le_of_stabilizes`). Neither half
needs a Jordan form, an algebraically closed field or a split minimal
polynomial: factor `ψ = (X - λ)^ν · q`, and Bézout between `q` and a power of
`X - λ` gives the first while `minpoly.dvd` gives the second.

Everything above is stated at an *arbitrary* stabilizing exponent, so print's
`νᵢ` is one of the exponents they admit. `minpoly_mulVecLin` carries that back
to the matrix, and the statements whose names carry `minpoly` are print's
numbered results with nothing left for the caller to choose.

## What is not claimed

**No Jordan form.** Nothing here mentions blocks, and `αᵢ` never appears as a
block count — only as `finrank` of the eigenspace, which is what print's argument
uses it for.
-/

namespace AISafetyAtlas.LinearSystems

open Module

section Kernels

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/--
**The kernel of a composite is no larger than the two kernels together.**

Everything in `LinearMap.ker (f ∘ₗ g)` is carried by `g` into `LinearMap.ker f`,
and what that carrying loses is exactly `LinearMap.ker g`.
-/
public theorem finrank_ker_comp_le (f g : V →ₗ[K] V) :
    finrank K (LinearMap.ker (f ∘ₗ g)) ≤
      finrank K (LinearMap.ker g) + finrank K (LinearMap.ker f) := by
  have hle : LinearMap.ker g ≤ LinearMap.ker (f ∘ₗ g) := by
    intro x hx
    simp [LinearMap.mem_ker.mp hx]
  set S := LinearMap.ker (f ∘ₗ g) with hSdef
  set φ : S →ₗ[K] V := g.domRestrict S with hφ
  have hrange : LinearMap.range φ ≤ LinearMap.ker f := by
    rintro _ ⟨x, rfl⟩
    have hx := LinearMap.mem_ker.mp x.2
    rw [LinearMap.comp_apply] at hx
    simpa [hφ, LinearMap.domRestrict_apply] using hx
  have hkerφ : LinearMap.ker φ = Submodule.comap S.subtype (LinearMap.ker g) := by
    ext x
    simp [hφ, LinearMap.mem_ker]
  have h1 : finrank K (LinearMap.ker φ) = finrank K (LinearMap.ker g) := by
    rw [hkerφ]
    exact ((Submodule.comapSubtypeEquivOfLe hle).finrank_eq)
  have h2 := LinearMap.finrank_range_add_finrank_ker φ
  have h3 : finrank K (LinearMap.range φ) ≤ finrank K (LinearMap.ker f) :=
    Submodule.finrank_mono hrange
  omega

/--
**Print's counting step, with no blocks in it.** The kernel of a `k`-th power is
at most `k` times the kernel.
-/
public theorem finrank_ker_pow_le (g : V →ₗ[K] V) (k : ℕ) :
    finrank K (LinearMap.ker (g ^ k)) ≤ k * finrank K (LinearMap.ker g) := by
  induction k with
  | zero => simp [Module.End.one_eq_id]
  | succ n ih =>
      have hpow : (g ^ (n + 1)) = (g ^ n) ∘ₗ g := by
        rw [pow_succ]
        rfl
      rw [hpow]
      have := finrank_ker_comp_le (g ^ n) g
      have hmul : (n + 1) * finrank K (LinearMap.ker g)
          = finrank K (LinearMap.ker g) + n * finrank K (LinearMap.ker g) := by
        ring
      omega

end Kernels

section Eigen

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/--
**The generalized eigenspace is at most `k` times the eigenspace**, at any
exponent `k` at which the generalized eigenspace chain has already reached its
limit. Print's equations (1) and (2) together.

Stated at an arbitrary stabilizing exponent rather than at the least one,
because that is what the counting argument needs and because a caller who has
*some* stabilizing exponent — which is what an eigenvalue's index is — can use
it without computing the least.
-/
public theorem finrank_maxGenEigenspace_le_mul_of_stabilizes
    (f : Module.End K V) (μ : K) {k : ℕ}
    (hk : f.maxGenEigenspace μ = f.genEigenspace μ (k : ℕ∞)) :
    finrank K (f.maxGenEigenspace μ) ≤ k * finrank K (f.eigenspace μ) := by
  rw [hk, Module.End.genEigenspace_nat]
  have h := finrank_ker_pow_le (f - μ • (1 : Module.End K V)) k
  have he : f.eigenspace μ = LinearMap.ker (f - μ • (1 : Module.End K V)) :=
    Module.End.genEigenspace_one
  rw [he]
  exact h

/-- The same at Mathlib's own index, where the stabilization hypothesis is a
theorem. -/
public theorem finrank_maxGenEigenspace_le_index_mul (f : Module.End K V) (μ : K) :
    finrank K (f.maxGenEigenspace μ)
      ≤ f.maxGenEigenspaceIndex μ * finrank K (f.eigenspace μ) :=
  finrank_maxGenEigenspace_le_mul_of_stabilizes f μ (Module.End.maxGenEigenspace_eq f μ)

/--
**Print's equation (2).** The multiplicity of `μ` in the characteristic
polynomial is at most `k` times the dimension of the eigenspace — so the
eigenspace is at least `nᵢ / k`, which is what print's Theorem 1 tests.
-/
public theorem rootMultiplicity_le_mul_finrank_eigenspace
    (f : Module.End K V) (μ : K) {k : ℕ}
    (hk : f.maxGenEigenspace μ = f.genEigenspace μ (k : ℕ∞)) :
    (LinearMap.charpoly f).rootMultiplicity μ ≤ k * finrank K (f.eigenspace μ) := by
  rw [← LinearMap.finrank_maxGenEigenspace_eq]
  exact finrank_maxGenEigenspace_le_mul_of_stabilizes f μ hk

/--
**Print's equation (5), as a lower bound on the eigenspace.** The ceiling of
`nᵢ / k` — which print writes `int[(nᵢ + νᵢ - 1)/νᵢ]` — does not exceed the
dimension of the eigenspace.

The positivity hypothesis is print's `νᵢ ≠ 0` in equation (1).
-/
public theorem ceil_div_le_finrank_eigenspace
    (f : Module.End K V) (μ : K) {k : ℕ} (hkpos : 0 < k)
    (hk : f.maxGenEigenspace μ = f.genEigenspace μ (k : ℕ∞)) :
    ((LinearMap.charpoly f).rootMultiplicity μ + k - 1) / k
      ≤ finrank K (f.eigenspace μ) := by
  have h := rootMultiplicity_le_mul_finrank_eigenspace f μ hk
  rw [Nat.div_le_iff_le_mul_add_pred hkpos]
  omega

end Eigen

section Index

open Polynomial

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

omit [FiniteDimensional K V] in
/-- `aeval` at the linear factor print writes `A - λᵢ I`. -/
private theorem aeval_X_sub_C_eq (f : Module.End K V) (μ : K) :
    Polynomial.aeval f (X - C μ) = f - μ • (1 : Module.End K V) := by
  simp [Algebra.algebraMap_eq_smul_one]

omit [FiniteDimensional K V] in
/-- `aeval` at a power of that factor, which is the map whose kernel is the
`k`-th generalized eigenspace. -/
private theorem aeval_X_sub_C_pow (f : Module.End K V) (μ : K) (k : ℕ) :
    Polynomial.aeval f ((X - C μ) ^ k) = (f - μ • (1 : Module.End K V)) ^ k := by
  rw [map_pow, aeval_X_sub_C_eq]

/--
**Print's index is a stabilizing exponent.** The generalized eigenspace chain of
`μ` has already reached its limit at the multiplicity of `μ` in the minimal
polynomial.

This is the half of print's `νᵢ` that the counting step consumes: it lets
`finrank_maxGenEigenspace_le_mul_of_stabilizes` and everything below it be fired
at print's own quantity.
-/
public theorem maxGenEigenspace_eq_genEigenspace_rootMultiplicity_minpoly
    (f : Module.End K V) (μ : K) :
    f.maxGenEigenspace μ
      = f.genEigenspace μ (((minpoly K f).rootMultiplicity μ : ℕ) : ℕ∞) := by
  have hne : minpoly K f ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := K) f)
  obtain ⟨q, hq, hqd⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly K f) hne μ
  set ν := (minpoly K f).rootMultiplicity μ with hν
  set g := f - μ • (1 : Module.End K V) with hg
  have hcop : IsCoprime q (X - C μ) :=
    ((Polynomial.irreducible_X_sub_C μ).coprime_iff_not_dvd.mpr hqd).symm
  -- the minimal polynomial, read as a map, is `aeval f q` after `g ^ ν`
  have hzero : ∀ x : V, (Polynomial.aeval f q) ((g ^ ν) x) = 0 := by
    intro x
    have : (Polynomial.aeval f (minpoly K f)) x = 0 := by
      rw [minpoly.aeval]; rfl
    rw [hq, mul_comm, map_mul, aeval_X_sub_C_pow] at this
    simpa [Module.End.mul_apply] using this
  refine le_antisymm ?_ (Module.End.genEigenspace_le_maximal f μ _)
  intro x hx
  obtain ⟨m, hm⟩ := (Module.End.mem_maxGenEigenspace f μ x).mp hx
  rw [Module.End.genEigenspace_nat, LinearMap.mem_ker]
  rcases le_or_gt m ν with hmν | hmν
  · have : g ^ ν = g ^ (ν - m) * g ^ m := by
      rw [← pow_add]; congr 1; omega
    rw [this, Module.End.mul_apply, hm, map_zero]
  · -- `g ^ ν x` is killed by `aeval f q` and by `g ^ (m - ν)`, which are coprime
    set y := (g ^ ν) x with hy
    have h1 : (Polynomial.aeval f q) y = 0 := hzero x
    have h2 : (g ^ (m - ν)) y = 0 := by
      rw [hy, ← Module.End.mul_apply, ← pow_add]
      have : m - ν + ν = m := by omega
      rw [this, hm]
    obtain ⟨a, b, hab⟩ := hcop.pow_right (n := m - ν)
    have := congrArg (fun p : K[X] => (Polynomial.aeval f p) y) hab
    simp only [map_add, map_mul, map_one, aeval_X_sub_C_pow] at this
    rw [LinearMap.add_apply, Module.End.mul_apply, Module.End.mul_apply, h1, h2,
      map_zero, map_zero, add_zero, Module.End.one_apply] at this
    exact this.symm

/--
**Print's index is the least stabilizing exponent.** Any exponent at which the
generalized eigenspace chain of `μ` has stopped growing is at least the
multiplicity of `μ` in the minimal polynomial.

Together with the statement above, this is print's own definition of `νᵢ` — *the
least `w` for which the kernel chain is stationary* — identified with the
multiplicity print actually computes with. Print does not prove this, citing
Zadeh and Desoer for it.
-/
public theorem rootMultiplicity_minpoly_le_of_stabilizes
    (f : Module.End K V) (μ : K) {k : ℕ}
    (hk : f.maxGenEigenspace μ = f.genEigenspace μ (k : ℕ∞)) :
    (minpoly K f).rootMultiplicity μ ≤ k := by
  have hne : minpoly K f ≠ 0 := minpoly.ne_zero (Algebra.IsIntegral.isIntegral (R := K) f)
  obtain ⟨q, hq, _⟩ :=
    Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd (minpoly K f) hne μ
  set ν := (minpoly K f).rootMultiplicity μ with hν
  set g := f - μ • (1 : Module.End K V) with hg
  have hqne : q ≠ 0 := by
    intro h; rw [h, mul_zero] at hq; exact hne hq
  -- `(X - C μ) ^ k * q` annihilates `f`, so the minimal polynomial divides it
  have hann : Polynomial.aeval f ((X - C μ) ^ k * q) = 0 := by
    ext x
    have hmem : (Polynomial.aeval f q) x ∈ f.maxGenEigenspace μ := by
      rw [maxGenEigenspace_eq_genEigenspace_rootMultiplicity_minpoly,
        Module.End.genEigenspace_nat, LinearMap.mem_ker]
      have : (Polynomial.aeval f (minpoly K f)) x = 0 := by
        rw [minpoly.aeval]; rfl
      rw [hq, map_mul, aeval_X_sub_C_pow] at this
      simpa [Module.End.mul_apply] using this
    rw [hk, Module.End.genEigenspace_nat, LinearMap.mem_ker] at hmem
    simpa [map_mul, aeval_X_sub_C_pow, Module.End.mul_apply] using hmem
  have hdvd : minpoly K f ∣ (X - C μ) ^ k * q := minpoly.dvd K f hann
  rw [hq] at hdvd
  have hxne : (X - C μ : K[X]) ≠ 0 := Polynomial.X_sub_C_ne_zero μ
  have hxnu : ¬ IsUnit (X - C μ : K[X]) := (Polynomial.irreducible_X_sub_C μ).not_isUnit
  exact (pow_dvd_pow_iff hxne hxnu).mp ((mul_dvd_mul_iff_right hqne).mp hdvd)

/--
**Print's `νᵢ`, in the atlas's vocabulary.** The stage at which the generalized
eigenspace chain of `μ` stops growing is the multiplicity of `μ` in the minimal
polynomial.

This is the identification print cites rather than proves. With it, every
statement in this module stated at a stabilizing exponent is a statement at
print's own index.
-/
public theorem maxGenEigenspaceIndex_eq_rootMultiplicity_minpoly
    (f : Module.End K V) (μ : K) :
    f.maxGenEigenspaceIndex μ = (minpoly K f).rootMultiplicity μ :=
  by
  refine le_antisymm (Nat.sInf_le ?_)
    (rootMultiplicity_minpoly_le_of_stabilizes f μ (Module.End.maxGenEigenspace_eq f μ))
  intro m hm
  show f.genEigenspace μ (((minpoly K f).rootMultiplicity μ : ℕ) : ℕ∞)
      = f.genEigenspace μ ((m : ℕ) : ℕ∞)
  refine le_antisymm ((f.genEigenspace μ).monotone (by exact_mod_cast hm)) ?_
  rw [← maxGenEigenspace_eq_genEigenspace_rootMultiplicity_minpoly]
  exact Module.End.genEigenspace_le_maximal f μ _

end Index

section Matrices

open Polynomial

variable {n m p : ℕ}

/-- The eigenspace of the map a matrix induces is the kernel the Hautus layer
already tests. -/
public theorem eigenspace_mulVecLin_eq_ker (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.End.eigenspace A.mulVecLin μ
      = LinearMap.ker (μ • (1 : Matrix (Fin n) (Fin n) ℂ) - A).mulVecLin := by
  ext x
  rw [Module.End.mem_eigenspace_iff, LinearMap.mem_ker]
  simp [sub_eq_zero, eq_comm]

/-- The characteristic polynomial of that map is the matrix's own. -/
public theorem charpoly_mulVecLin (A : Matrix (Fin n) (Fin n) ℂ) :
    LinearMap.charpoly A.mulVecLin = A.charpoly := by
  rw [← LinearMap.charpoly_toMatrix A.mulVecLin (Pi.basisFun ℂ (Fin n))]
  congr 1
  rw [LinearMap.toMatrix_eq_toMatrix']
  exact LinearMap.toMatrix'_toLin' A

/--
**Klamka's Theorem 1, at print's own antecedent.**

If the multiplicity of `μ` in the characteristic polynomial, divided by a
stabilizing exponent and rounded up, exceeds the rank of the input matrix, the
system is uncontrollable. Print's test: it never needs the value of `μ` beyond
the two multiplicities, and never needs the transformation matrix.
-/
public theorem not_isControllable_of_ceil_div_gt_rank
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) {k : ℕ}
    (hkpos : 0 < k)
    (hk : Module.End.maxGenEigenspace A.mulVecLin μ
      = Module.End.genEigenspace A.mulVecLin μ (k : ℕ∞))
    (h : B.rank < (A.charpoly.rootMultiplicity μ + k - 1) / k) :
    ¬ IsControllable A B := by
  refine not_isControllable_of_finrank_ker_gt_rank A B μ ?_
  have hb := ceil_div_le_finrank_eigenspace A.mulVecLin μ hkpos hk
  rw [charpoly_mulVecLin, eigenspace_mulVecLin_eq_ker] at hb
  omega

/--
**Klamka's Corollary 1, at print's own antecedent**: the input dimension bounds
the rank of the input matrix, so the same test against it suffices.
-/
public theorem not_isControllable_of_ceil_div_gt_width
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ) {k : ℕ}
    (hkpos : 0 < k)
    (hk : Module.End.maxGenEigenspace A.mulVecLin μ
      = Module.End.genEigenspace A.mulVecLin μ (k : ℕ∞))
    (h : m < (A.charpoly.rootMultiplicity μ + k - 1) / k) :
    ¬ IsControllable A B := by
  refine not_isControllable_of_ceil_div_gt_rank A B μ hkpos hk ?_
  have hB := B.rank_le_card_width
  rw [Fintype.card_fin] at hB
  omega

/--
**Klamka's Theorem 2, at print's own antecedent**, by print's own route: *"It
follows by duality."*
-/
public theorem not_isObservable_of_ceil_div_gt_rank
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ) {k : ℕ}
    (hkpos : 0 < k)
    (hk : Module.End.maxGenEigenspace (Matrix.mulVecLin A.transpose) μ
      = Module.End.genEigenspace (Matrix.mulVecLin A.transpose) μ (k : ℕ∞))
    (h : C.rank < ((Matrix.charpoly A.transpose).rootMultiplicity μ + k - 1) / k) :
    ¬ IsObservable A C := by
  refine not_isObservable_of_finrank_ker_gt_rank A C μ ?_
  have hb := ceil_div_le_finrank_eigenspace (Matrix.mulVecLin A.transpose) μ hkpos hk
  rw [charpoly_mulVecLin, eigenspace_mulVecLin_eq_ker] at hb
  omega

/--
**Klamka's Corollary 2, at print's own antecedent**: the output dimension in
place of the rank of the output matrix.
-/
public theorem not_isObservable_of_ceil_div_gt_height
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ) {k : ℕ}
    (hkpos : 0 < k)
    (hk : Module.End.maxGenEigenspace (Matrix.mulVecLin A.transpose) μ
      = Module.End.genEigenspace (Matrix.mulVecLin A.transpose) μ (k : ℕ∞))
    (h : p < ((Matrix.charpoly A.transpose).rootMultiplicity μ + k - 1) / k) :
    ¬ IsObservable A C := by
  refine not_isObservable_of_ceil_div_gt_rank A C μ hkpos hk ?_
  have hC := C.rank_le_card_height
  rw [Fintype.card_fin] at hC
  omega

/-- The minimal polynomial of the map a matrix induces is the matrix's own, so
print's `νᵢ` may be read off `A` directly. -/
public theorem minpoly_mulVecLin (A : Matrix (Fin n) (Fin n) ℂ) :
    minpoly ℂ A.mulVecLin = minpoly ℂ A := by
  rw [← Matrix.toLin'_apply']
  exact Matrix.minpoly_toLin' A

/-- The generalized eigenspace chain of a matrix has stabilized at the
multiplicity of `μ` in the matrix's own minimal polynomial — print's `νᵢ`. -/
public theorem maxGenEigenspace_mulVecLin_eq_rootMultiplicity_minpoly
    (A : Matrix (Fin n) (Fin n) ℂ) (μ : ℂ) :
    Module.End.maxGenEigenspace A.mulVecLin μ
      = Module.End.genEigenspace A.mulVecLin μ
          ((((minpoly ℂ A).rootMultiplicity μ : ℕ)) : ℕ∞) := by
  rw [maxGenEigenspace_eq_genEigenspace_rootMultiplicity_minpoly, minpoly_mulVecLin]

/--
**Klamka's Theorem 1, in print's own vocabulary.**

`νᵢ` is the multiplicity of `μ` in the **minimal** polynomial, `nᵢ` its
multiplicity in the characteristic polynomial, and the test is print's
`int[(nᵢ + νᵢ - 1)/νᵢ] > r`. Nothing here is an exponent chosen by the caller:
both quantities are computed from `A`.
-/
public theorem not_isControllable_of_ceil_div_minpoly_gt_rank
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ)
    (hν : 0 < (minpoly ℂ A).rootMultiplicity μ)
    (h : B.rank < (A.charpoly.rootMultiplicity μ + (minpoly ℂ A).rootMultiplicity μ - 1)
      / (minpoly ℂ A).rootMultiplicity μ) :
    ¬ IsControllable A B :=
  not_isControllable_of_ceil_div_gt_rank A B μ hν
    (maxGenEigenspace_mulVecLin_eq_rootMultiplicity_minpoly A μ) h

/-- **Klamka's Corollary 1, in print's own vocabulary**: the input dimension in
place of the rank of `B`. -/
public theorem not_isControllable_of_ceil_div_minpoly_gt_width
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ) (μ : ℂ)
    (hν : 0 < (minpoly ℂ A).rootMultiplicity μ)
    (h : m < (A.charpoly.rootMultiplicity μ + (minpoly ℂ A).rootMultiplicity μ - 1)
      / (minpoly ℂ A).rootMultiplicity μ) :
    ¬ IsControllable A B :=
  not_isControllable_of_ceil_div_gt_width A B μ hν
    (maxGenEigenspace_mulVecLin_eq_rootMultiplicity_minpoly A μ) h

/-- **Klamka's Theorem 2, in print's own vocabulary**, at the transposed system
print's duality sentence sends it to. -/
public theorem not_isObservable_of_ceil_div_minpoly_gt_rank
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ)
    (hν : 0 < (minpoly ℂ A.transpose).rootMultiplicity μ)
    (h : C.rank < ((Matrix.charpoly A.transpose).rootMultiplicity μ
      + (minpoly ℂ A.transpose).rootMultiplicity μ - 1)
      / (minpoly ℂ A.transpose).rootMultiplicity μ) :
    ¬ IsObservable A C :=
  not_isObservable_of_ceil_div_gt_rank A C μ hν
    (maxGenEigenspace_mulVecLin_eq_rootMultiplicity_minpoly A.transpose μ) h

/-- **Klamka's Corollary 2, in print's own vocabulary**: the output dimension in
place of the rank of `C`. -/
public theorem not_isObservable_of_ceil_div_minpoly_gt_height
    (A : Matrix (Fin n) (Fin n) ℂ) (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ)
    (hν : 0 < (minpoly ℂ A.transpose).rootMultiplicity μ)
    (h : p < ((Matrix.charpoly A.transpose).rootMultiplicity μ
      + (minpoly ℂ A.transpose).rootMultiplicity μ - 1)
      / (minpoly ℂ A.transpose).rootMultiplicity μ) :
    ¬ IsObservable A C :=
  not_isObservable_of_ceil_div_gt_height A C μ hν
    (maxGenEigenspace_mulVecLin_eq_rootMultiplicity_minpoly A.transpose μ) h

/--
**Klamka's Corollary 3, at print's own antecedent.**

The conjunction against the two ranks. It needs a stabilizing exponent for `A`
alone and none for `Aᵀ`, because the conjunction lemma it calls already carries
`finrank_ker_transpose_eq` — the eigenspace has the same dimension for a matrix
and its transpose, so there is only ever one count to bound.
-/
public theorem not_isControllable_and_not_isObservable_of_ceil_div_gt_ranks
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ) {k : ℕ} (hkpos : 0 < k)
    (hk : Module.End.maxGenEigenspace A.mulVecLin μ
      = Module.End.genEigenspace A.mulVecLin μ (k : ℕ∞))
    (h : max B.rank C.rank < (A.charpoly.rootMultiplicity μ + k - 1) / k) :
    ¬ IsControllable A B ∧ ¬ IsObservable A C := by
  refine not_isControllable_and_not_isObservable_of_finrank_ker_gt_ranks A B C μ ?_
  have hb := ceil_div_le_finrank_eigenspace A.mulVecLin μ hkpos hk
  rw [charpoly_mulVecLin, eigenspace_mulVecLin_eq_ker] at hb
  omega

/-- **Klamka's Corollary 4, at print's own antecedent**: the two dimensions in
place of the two ranks. -/
public theorem not_isControllable_and_not_isObservable_of_ceil_div_gt_dims
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ) {k : ℕ} (hkpos : 0 < k)
    (hk : Module.End.maxGenEigenspace A.mulVecLin μ
      = Module.End.genEigenspace A.mulVecLin μ (k : ℕ∞))
    (h : max m p < (A.charpoly.rootMultiplicity μ + k - 1) / k) :
    ¬ IsControllable A B ∧ ¬ IsObservable A C := by
  refine not_isControllable_and_not_isObservable_of_ceil_div_gt_ranks A B C μ hkpos hk ?_
  have hB := B.rank_le_card_width
  have hC := C.rank_le_card_height
  rw [Fintype.card_fin] at hB hC
  have h1 : max B.rank C.rank ≤ max m p := max_le_max hB hC
  omega

/-- **Klamka's Corollary 3, in print's own vocabulary**: both multiplicities read
off `A`. -/
public theorem not_isControllable_and_not_isObservable_of_ceil_div_minpoly_gt_ranks
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ)
    (hν : 0 < (minpoly ℂ A).rootMultiplicity μ)
    (h : max B.rank C.rank
      < (A.charpoly.rootMultiplicity μ + (minpoly ℂ A).rootMultiplicity μ - 1)
        / (minpoly ℂ A).rootMultiplicity μ) :
    ¬ IsControllable A B ∧ ¬ IsObservable A C :=
  not_isControllable_and_not_isObservable_of_ceil_div_gt_ranks A B C μ hν
    (maxGenEigenspace_mulVecLin_eq_rootMultiplicity_minpoly A μ) h

/-- **Klamka's Corollary 4, in print's own vocabulary.** -/
public theorem not_isControllable_and_not_isObservable_of_ceil_div_minpoly_gt_dims
    (A : Matrix (Fin n) (Fin n) ℂ) (B : Matrix (Fin n) (Fin m) ℂ)
    (C : Matrix (Fin p) (Fin n) ℂ) (μ : ℂ)
    (hν : 0 < (minpoly ℂ A).rootMultiplicity μ)
    (h : max m p
      < (A.charpoly.rootMultiplicity μ + (minpoly ℂ A).rootMultiplicity μ - 1)
        / (minpoly ℂ A).rootMultiplicity μ) :
    ¬ IsControllable A B ∧ ¬ IsObservable A C :=
  not_isControllable_and_not_isObservable_of_ceil_div_gt_dims A B C μ hν
    (maxGenEigenspace_mulVecLin_eq_rootMultiplicity_minpoly A μ) h

end Matrices

end AISafetyAtlas.LinearSystems
