module

public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import AISafetyAtlas.SingularLearning.RankRealization

/-!
# The orbit of a factorization is determined by its three ranks (Lemma 3.2)

`RankRealization.lean` settles which rank pairs `(a, b)` occur on the zero fiber

    W₀ = {(A, B) : A ∈ ℝ^{H×N}, B ∈ ℝ^{M×H}, B * A = C} .

This module settles the next question: *how much of the position of a fiber point matters
beyond its ranks?* The answer is nothing, and that is what makes a table indexed by
`(rank A, rank B)` complete rather than a table of sampled examples.

## The statement being formalized

Lemma 3.2 of the candidate (p. 9) reads:

> **Lemma 3.2 (Canonical form).** Let `(G_M, G_H, G_N) ∈ GL_M × GL_H × GL_N` act on parameter
> space by `A ↦ G_H A G_N⁻¹`, `B ↦ G_M B G_H⁻¹`. The orbit of a pair `(A*, B*)` is determined by
> `(a, b, r) = (rank A*, rank B*, rank B*A*)`. A canonical representative is built from
> decompositions `ℝ^N = V_r ⊕ V_{a-r} ⊕ V_n`, `ℝ^H = W_r ⊕ W_{a-r} ⊕ W_{b-r} ⊕ W_h`,
> `ℝ^M = U_r ⊕ U_{b-r} ⊕ U_p` … on which `A*` is the identity `V_r → W_r` and
> `V_{a-r} → W_{a-r}` and zero otherwise, `B*` is the identity `W_r → U_r` and
> `W_{b-r} → U_{b-r}` and zero otherwise, and `C = B*A*` is the identity `V_r → U_r` and zero
> otherwise.

`SameOrbit` is that action, `canonicalA`/`canonicalB` are that representative (written in the
`selCols` vocabulary of `RankRealization.lean`, with the four hidden blocks laid out in the
order `W_{b-r}, W_r, W_{a-r}, W_h`; a permutation of the hidden coordinates is itself an
element of `GL_H`, so the choice of layout is not a choice of orbit), and
`sameOrbit_iff_rank_eq` is the classification. Both halves are proved:
`SameOrbit.rank_eq` is the invariance, `exists_units_to_canonical` the reduction to the
representative, and `sameOrbit_of_rank_eq` the completeness that follows from them.

The construction lives in `exists_adapted_bases`, which is the candidate's proof: `W_{a-r}` is
`im A ∩ ker B`, of dimension `a - r` by rank–nullity applied to `B` restricted to `im A`
(equation (3.1) on p. 8); `W_r` and `W_h` are complements of it inside `im A` and `ker B`, cut
out of one complement `q` of `im A ∩ ker B` by the modular law; and `W_{b-r}` is a complement
of `im A + ker B`. The three bases are then obtained from spanning plus a dimension count, so
no independence has to be checked by hand. The single `G_H` shared by the two factors is what
makes this a statement about pairs rather than two statements about matrices.

## Why the candidate needs it

Section 10, Step 1 uses Lemma 3.2 to move the local analysis at an *arbitrary* `w* ∈ W₀` to
the canonical representative of its stratum: a fixed linear change of basis `(G_M, G_H, G_N)`
carries `w*` there, so a statement proved at the representative is a statement about every
point of the stratum. Without it, Theorem 5.1's chart would describe one point per stratum and
the elimination table would not be a table about `W₀`.

## What this module is not

**This is the algebraic prerequisite of Theorem 5.1 and contains none of its analysis.** There
is no neighborhood here, no comparability constant, no diffeomorphism, and no norm. The
candidate is explicit about the hygiene (p. 9): the group action is a linear diffeomorphism of
parameter space but does *not* preserve the Frobenius norm, so the local pair transfers
"through comparability plus diffeomorphism invariance, never through an isometry". Nothing in
this file may be read as transporting a metric quantity.
-/

namespace AISafetyAtlas.SingularLearning

/-! ## The action of `GL(M) × GL(H) × GL(N)` -/

/-- The action sends `B * A` to `P (B * A) Q⁻¹`: the hidden-layer factor `S` cancels between
the two factors, which is why the product — and hence the fiber `{(A, B) : B * A = C}` up to
the induced action on `C` — is carried along by the action on the pair. -/
public theorem mul_congr_of_units {M N H : ℕ}
    (P : Matrix (Fin M) (Fin M) ℝ) (S : Matrix (Fin H) (Fin H) ℝ)
    (Q : Matrix (Fin N) (Fin N) ℝ) (hS : IsUnit S.det)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    (P * B * S⁻¹) * (S * A * Q⁻¹) = P * (B * A) * Q⁻¹ := by
  rw [Matrix.mul_assoc S A Q⁻¹, Matrix.mul_assoc (P * B) S⁻¹, ← Matrix.mul_assoc S⁻¹ S (A * Q⁻¹),
    Matrix.nonsing_inv_mul S hS, Matrix.one_mul, ← Matrix.mul_assoc, Matrix.mul_assoc P B A]

/-- Multiplying on the left by an invertible matrix and on the right by the inverse of an
invertible matrix leaves the rank alone. -/
public theorem rank_mul_mul_inv {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (X : Matrix (Fin m) (Fin n) ℝ) : (P * X * Q⁻¹).rank = X.rank := by
  rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_nonsing_inv_det Q hQ),
    Matrix.rank_mul_eq_right_of_isUnit_det P X hP]

/-! ## The orbit relation -/

/-- Two pairs lie in the same orbit of `GL(M) × GL(H) × GL(N)` acting by
`A ↦ S A Q⁻¹`, `B ↦ P B S⁻¹`. The single `S` is shared: that coupling is the whole difficulty
of Lemma 3.2, since it forces one basis of `ℝ^H` to be adapted to `im A` and `ker B` at once. -/
@[expose] public def SameOrbit {M N H : ℕ} (A₁ A₂ : Matrix (Fin H) (Fin N) ℝ)
    (B₁ B₂ : Matrix (Fin M) (Fin H) ℝ) : Prop :=
  ∃ (P : Matrix (Fin M) (Fin M) ℝ) (S : Matrix (Fin H) (Fin H) ℝ) (Q : Matrix (Fin N) (Fin N) ℝ),
    IsUnit P.det ∧ IsUnit S.det ∧ IsUnit Q.det ∧ S * A₁ * Q⁻¹ = A₂ ∧ P * B₁ * S⁻¹ = B₂

public theorem SameOrbit.refl {M N H : ℕ} (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) : SameOrbit A A B B :=
  ⟨1, 1, 1, by simp, by simp, by simp, by simp, by simp⟩

/-- Undoing the action: the inverse triple sends the image back to the source. -/
public theorem act_inv_act {m n : ℕ} (P : Matrix (Fin m) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (hP : IsUnit P.det) (hQ : IsUnit Q.det)
    (X : Matrix (Fin m) (Fin n) ℝ) : P⁻¹ * (P * X * Q⁻¹) * Q⁻¹⁻¹ = X := by
  rw [Matrix.nonsing_inv_nonsing_inv Q hQ, Matrix.mul_assoc P X Q⁻¹,
    Matrix.nonsing_inv_mul_cancel_left P _ hP, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul Q hQ, Matrix.mul_one]

public theorem SameOrbit.symm {M N H : ℕ} {A₁ A₂ : Matrix (Fin H) (Fin N) ℝ}
    {B₁ B₂ : Matrix (Fin M) (Fin H) ℝ} (h : SameOrbit A₁ A₂ B₁ B₂) : SameOrbit A₂ A₁ B₂ B₁ := by
  obtain ⟨P, S, Q, hP, hS, hQ, hA, hB⟩ := h
  exact ⟨P⁻¹, S⁻¹, Q⁻¹, Matrix.isUnit_nonsing_inv_det P hP, Matrix.isUnit_nonsing_inv_det S hS,
    Matrix.isUnit_nonsing_inv_det Q hQ, by rw [← hA]; exact act_inv_act S Q hS hQ A₁,
    by rw [← hB]; exact act_inv_act P S hP hS B₁⟩

public theorem SameOrbit.trans {M N H : ℕ} {A₁ A₂ A₃ : Matrix (Fin H) (Fin N) ℝ}
    {B₁ B₂ B₃ : Matrix (Fin M) (Fin H) ℝ} (h₁ : SameOrbit A₁ A₂ B₁ B₂)
    (h₂ : SameOrbit A₂ A₃ B₂ B₃) : SameOrbit A₁ A₃ B₁ B₃ := by
  obtain ⟨P, S, Q, hP, hS, hQ, hA, hB⟩ := h₁
  obtain ⟨P', S', Q', hP', hS', hQ', hA', hB'⟩ := h₂
  refine ⟨P' * P, S' * S, Q' * Q, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_mul]; exact hP'.mul hP
  · rw [Matrix.det_mul]; exact hS'.mul hS
  · rw [Matrix.det_mul]; exact hQ'.mul hQ
  · rw [Matrix.mul_inv_rev, ← hA', ← hA, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_assoc]
  · rw [Matrix.mul_inv_rev, ← hB', ← hB, Matrix.mul_assoc, Matrix.mul_assoc, Matrix.mul_assoc,
      Matrix.mul_assoc, Matrix.mul_assoc]

/-! ## The canonical representative -/

/-- The canonical `A` of the stratum `(a, b, r)`: the identity from the first `a` input
coordinates onto the hidden coordinates `[b - r, b - r + a)`, and zero elsewhere. The hidden
block it lands on is `W_r ⊕ W_{a-r}` in the notation of Lemma 3.2. -/
@[expose] public def canonicalA (N H a b r : ℕ) : Matrix (Fin H) (Fin N) ℝ :=
  selCols H N (fun j => if j < a then j + (b - r) else H)

/-- The canonical `B` of the stratum `(a, b, r)`: it carries the hidden coordinates
`[b - r, b)` — that is `W_r`, the part of `im A` on which `B` is injective — onto the first `r`
output coordinates, carries the hidden coordinates `[0, b - r)` — that is `W_{b-r}` — onto the
output coordinates `[r, b)`, and kills the rest, namely `W_{a-r} ⊕ W_h ⊆ ker B`. -/
@[expose] public def canonicalB (M H b r : ℕ) : Matrix (Fin M) (Fin H) ℝ :=
  selCols M H (fun j => if j < b - r then j + r else if j < b then j - (b - r) else M)

public theorem rank_partialIdMatrix {M N r : ℕ} (hM : r ≤ M) (hN : r ≤ N) :
    (partialIdMatrix M N r).rank = r := by
  rw [partialIdMatrix_eq_selCols]
  refine rank_selCols _ r hN (fun j => ?_) (fun j j' hj hjj => ?_)
  · split_ifs <;> omega
  · split_ifs at hj hjj <;> omega

public theorem rank_canonicalA {N H a b r : ℕ} (haN : a ≤ N) (hH : a + (b - r) ≤ H) :
    (canonicalA N H a b r).rank = a := by
  refine rank_selCols _ a haN (fun j => ?_) (fun j j' hj hjj => ?_)
  · split_ifs <;> omega
  · split_ifs at hj hjj <;> omega

public theorem rank_canonicalB {M H b r : ℕ} (hrb : r ≤ b) (hbM : b ≤ M) (hbH : b ≤ H) :
    (canonicalB M H b r).rank = b := by
  refine rank_selCols _ b hbH (fun j => ?_) (fun j j' hj hjj => ?_)
  · split_ifs <;> omega
  · split_ifs at hj hjj <;> omega

/-- The canonical pair multiplies to the canonical rank-`r` matrix: only the `r` hidden
coordinates `[b - r, b)` are both hit by `canonicalA` and kept by `canonicalB`. -/
public theorem canonicalB_mul_canonicalA {M N H a b r : ℕ} (hra : r ≤ a) (hrb : r ≤ b)
    (hH : a + (b - r) ≤ H) :
    canonicalB M H b r * canonicalA N H a b r = partialIdMatrix M N r := by
  rw [canonicalA, canonicalB, selCols_mul_selCols, partialIdMatrix_eq_selCols]
  refine selCols_ext (fun j => ?_)
  split_ifs <;> omega

/-! ## From adapted bases to the group element -/

/-- The span of a basis of a submodule, read in the ambient space, is that submodule. -/
public theorem span_range_coe_basis {V : Type*} [AddCommGroup V] [Module ℝ V]
    (p : Submodule ℝ V) {ι : Type*} (d : Module.Basis ι ℝ p) :
    Submodule.span ℝ (Set.range fun i => (d i : V)) = p := by
  have h : (Set.range fun i => (d i : V)) = p.subtype '' Set.range (⇑d) := by
    rw [← Set.range_comp]; rfl
  rw [h, ← Submodule.map_span, d.span_eq, Submodule.map_subtype_top]

/-- A submodule is contained in any span that swallows one of its bases. This is the only way
the four hidden blocks enter the spanning argument below. -/
public theorem le_span_of_basis_mem {V : Type*} [AddCommGroup V] [Module ℝ V]
    {p : Submodule ℝ V} {ι : Type*} (d : Module.Basis ι ℝ p) {S : Set V}
    (h : ∀ i, (d i : V) ∈ Submodule.span ℝ S) : p ≤ Submodule.span ℝ S := by
  rw [← span_range_coe_basis p d, Submodule.span_le]
  rintro _ ⟨i, rfl⟩
  exact h i

/-- Reading a factorization `X = P' * Y * Q` as an action `P * X * Q⁻¹ = Y`. -/
public theorem act_of_factor {m n : ℕ} {P P' : Matrix (Fin m) (Fin m) ℝ}
    {Q : Matrix (Fin n) (Fin n) ℝ} (hP : P * P' = 1) (hQ : IsUnit Q.det)
    {X Y : Matrix (Fin m) (Fin n) ℝ} (h : P' * Y * Q = X) : P * X * Q⁻¹ = Y := by
  rw [← h, ← Matrix.mul_assoc P (P' * Y) Q, ← Matrix.mul_assoc P P' Y, hP, Matrix.one_mul,
    Matrix.mul_assoc Y Q Q⁻¹, Matrix.mul_nonsing_inv Q hQ, Matrix.mul_one]

/-- Bases in which `A` and `B` have prescribed matrices exhibit the group element carrying the
pair to those matrices: `(P, S, Q)` are the three changes of basis. -/
public theorem sameOrbit_of_toMatrix {M N H : ℕ} {A A₀ : Matrix (Fin H) (Fin N) ℝ}
    {B B₀ : Matrix (Fin M) (Fin H) ℝ} (bN : Module.Basis (Fin N) ℝ (Fin N → ℝ))
    (bH : Module.Basis (Fin H) ℝ (Fin H → ℝ)) (bM : Module.Basis (Fin M) ℝ (Fin M → ℝ))
    (hA : LinearMap.toMatrix bN bH
      (Matrix.toLin (Pi.basisFun ℝ (Fin N)) (Pi.basisFun ℝ (Fin H)) A) = A₀)
    (hB : LinearMap.toMatrix bH bM
      (Matrix.toLin (Pi.basisFun ℝ (Fin H)) (Pi.basisFun ℝ (Fin M)) B) = B₀) :
    SameOrbit A A₀ B B₀ := by
  set eN := Pi.basisFun ℝ (Fin N)
  set eH := Pi.basisFun ℝ (Fin H)
  set eM := Pi.basisFun ℝ (Fin M)
  have hunit : ∀ {k : ℕ} (b c : Module.Basis (Fin k) ℝ (Fin k → ℝ)), IsUnit (b.toMatrix c).det := by
    intro k b c
    have : Invertible (b.toMatrix c) := Module.Basis.invertibleToMatrix b c
    exact Matrix.isUnit_det_of_invertible _
  have hfacA : eH.toMatrix bH * A₀ * bN.toMatrix eN = A := by
    rw [← hA, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix, LinearMap.toMatrix_toLin]
  have hfacB : eM.toMatrix bM * B₀ * bH.toMatrix eH = B := by
    rw [← hB, basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix, LinearMap.toMatrix_toLin]
  exact ⟨bM.toMatrix eM, bH.toMatrix eH, bN.toMatrix eN, hunit _ _, hunit _ _, hunit _ _,
    act_of_factor (Module.Basis.toMatrix_mul_toMatrix_flip bH eH) (hunit bN eN) hfacA,
    act_of_factor (Module.Basis.toMatrix_mul_toMatrix_flip bM eM) (hunit bH eH) hfacB⟩

/-! ## The adapted bases -/

open Module (finrank)

/-- **The adapted bases of Lemma 3.2.** -/
public theorem exists_adapted_bases {M N H : ℕ} (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) :
    ∃ (bN : Module.Basis (Fin N) ℝ (Fin N → ℝ)) (bH : Module.Basis (Fin H) ℝ (Fin H → ℝ))
      (bM : Module.Basis (Fin M) ℝ (Fin M → ℝ)),
      LinearMap.toMatrix bN bH (Matrix.toLin (Pi.basisFun ℝ (Fin N)) (Pi.basisFun ℝ (Fin H)) A)
          = canonicalA N H A.rank B.rank (B * A).rank ∧
      LinearMap.toMatrix bH bM (Matrix.toLin (Pi.basisFun ℝ (Fin H)) (Pi.basisFun ℝ (Fin M)) B)
          = canonicalB M H B.rank (B * A).rank := by
  classical
  set eN := Pi.basisFun ℝ (Fin N) with heN
  set eH := Pi.basisFun ℝ (Fin H) with heH
  set eM := Pi.basisFun ℝ (Fin M) with heM
  set f := Matrix.toLin eN eH A with hf
  set g := Matrix.toLin eH eM B with hg
  set a := A.rank with ha
  set b := B.rank with hb
  set r := (B * A).rank with hr
  set U := LinearMap.range f with hUdef
  set K := LinearMap.ker g with hKdef
  set I := U ⊓ K with hIdef
  have hdimH : finrank ℝ (Fin H → ℝ) = H := by simp
  have hdimN : finrank ℝ (Fin N → ℝ) = N := by simp
  have hdimM : finrank ℝ (Fin M → ℝ) = M := by simp
  have hdimU : finrank ℝ U = a := (Matrix.rank_eq_finrank_range_toLin A eH eN).symm
  have hdimRg : finrank ℝ (LinearMap.range g) = b :=
    (Matrix.rank_eq_finrank_range_toLin B eM eH).symm
  have hdimBA : finrank ℝ (LinearMap.range (g ∘ₗ f)) = r := by
    rw [← Matrix.toLin_mul eN eH eM B A]
    exact (Matrix.rank_eq_finrank_range_toLin (B * A) eM eN).symm
  -- Rank–nullity for `g` restricted to `U = im A`: `dim (im A ∩ ker B) + r = a`, which is
  -- equation (3.1) of the candidate.
  have hgU : LinearMap.range (g ∘ₗ U.subtype) = LinearMap.range (g ∘ₗ f) := by
    rw [LinearMap.range_comp, Submodule.range_subtype, LinearMap.range_comp]
  have hkerU : finrank ℝ (LinearMap.ker (g ∘ₗ U.subtype)) = finrank ℝ I := by
    rw [← Submodule.finrank_map_subtype_eq U (LinearMap.ker (g ∘ₗ U.subtype)),
      LinearMap.ker_comp, Submodule.map_comap_subtype]
  have hIa : finrank ℝ I + r = a := by
    have h := LinearMap.finrank_range_add_finrank_ker (g ∘ₗ U.subtype)
    rw [hgU, hdimBA, hkerU, hdimU] at h
    omega
  have hKb : b + finrank ℝ K = H := by
    have h := LinearMap.finrank_range_add_finrank_ker g
    rw [hdimRg, hdimH] at h
    omega
  have hrb : r ≤ b := Matrix.rank_mul_le_left B A
  -- The four hidden blocks.
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl I
  obtain ⟨W3, hW3⟩ := Submodule.exists_isCompl (U ⊔ K)
  have hIU : I ≤ U := inf_le_left
  have hIK : I ≤ K := inf_le_right
  have hsup1 : I ⊔ q ⊓ U = U := by
    rw [← sup_inf_assoc_of_le q hIU, hq.sup_eq_top, top_inf_eq]
  have hsup4 : I ⊔ q ⊓ K = K := by
    rw [← sup_inf_assoc_of_le q hIK, hq.sup_eq_top, top_inf_eq]
  have hinf1 : I ⊓ (q ⊓ U) = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf_left I inf_le_left) hq.inf_eq_bot.le)
  have hinf4 : I ⊓ (q ⊓ K) = ⊥ :=
    le_bot_iff.mp (le_trans (inf_le_inf_left I inf_le_left) hq.inf_eq_bot.le)
  have hdim1 : finrank ℝ (q ⊓ U : Submodule ℝ (Fin H → ℝ)) = r := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq I (q ⊓ U)
    rw [hsup1, hinf1, hdimU, finrank_bot] at h
    omega
  have hdim4 : finrank ℝ I + finrank ℝ (q ⊓ K : Submodule ℝ (Fin H → ℝ)) = finrank ℝ K := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq I (q ⊓ K)
    rw [hsup4, hinf4, finrank_bot] at h
    omega
  have hdimUK : finrank ℝ (U ⊔ K : Submodule ℝ (Fin H → ℝ)) + finrank ℝ I = a + finrank ℝ K := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq U K
    rw [hdimU] at h
    exact h
  have hdim3 : finrank ℝ (U ⊔ K : Submodule ℝ (Fin H → ℝ)) + finrank ℝ W3 = H := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (U ⊔ K) W3
    rw [hW3.sup_eq_top, hW3.inf_eq_bot, finrank_top, finrank_bot, hdimH] at h
    omega
  -- Block sizes.  `c = b - r`, and the four blocks are laid out as
  -- `W_{b-r} | W_r | W_{a-r} | W_h` along the hidden coordinates.
  set c := b - r with hc
  set W1 := (q ⊓ U : Submodule ℝ (Fin H → ℝ)) with hW1def
  set W4 := (q ⊓ K : Submodule ℝ (Fin H → ℝ)) with hW4def
  set n4 := finrank ℝ W4 with hn4
  have hW1U : W1 ≤ U := by rw [hW1def]; exact inf_le_right
  have hW4K : W4 ≤ K := by rw [hW4def]; exact inf_le_right
  have hra : r ≤ a := by omega
  have hn2 : finrank ℝ I = a - r := by omega
  have hn3 : finrank ℝ W3 = c := by omega
  have hsum : c + r + (a - r) + n4 = H := by omega
  have hbH : b ≤ H := by omega
  set d3 := Module.finBasisOfFinrankEq ℝ W3 hn3 with hd3def
  set d1 := Module.finBasisOfFinrankEq ℝ W1 hdim1 with hd1def
  set d2 := Module.finBasisOfFinrankEq ℝ I hn2 with hd2def
  set d4 := Module.finBasisOfFinrankEq ℝ W4 hn4.symm with hd4def
  set e3 : ℕ → (Fin H → ℝ) := fun k => if h : k < c then (d3 ⟨k, h⟩ : Fin H → ℝ) else 0 with he3
  set e1 : ℕ → (Fin H → ℝ) := fun k => if h : k < r then (d1 ⟨k, h⟩ : Fin H → ℝ) else 0 with he1
  set e2 : ℕ → (Fin H → ℝ) :=
    fun k => if h : k < a - r then (d2 ⟨k, h⟩ : Fin H → ℝ) else 0 with he2
  set e4 : ℕ → (Fin H → ℝ) := fun k => if h : k < n4 then (d4 ⟨k, h⟩ : Fin H → ℝ) else 0 with he4
  have he3mem : ∀ k, e3 k ∈ W3 := by
    intro k; rw [he3]; dsimp only; split
    exacts [Submodule.coe_mem _, W3.zero_mem]
  have he1mem : ∀ k, e1 k ∈ W1 := by
    intro k; rw [he1]; dsimp only; split
    exacts [Submodule.coe_mem _, W1.zero_mem]
  have he2mem : ∀ k, e2 k ∈ I := by
    intro k; rw [he2]; dsimp only; split
    exacts [Submodule.coe_mem _, I.zero_mem]
  have he4mem : ∀ k, e4 k ∈ W4 := by
    intro k; rw [he4]; dsimp only; split
    exacts [Submodule.coe_mem _, W4.zero_mem]
  set wH : ℕ → (Fin H → ℝ) := fun k =>
    if k < c then e3 k else if k < b then e1 (k - c)
      else if k < b + (a - r) then e2 (k - b) else e4 (k - b - (a - r)) with hwH
  set vH : Fin H → (Fin H → ℝ) := fun j => wH (j : ℕ) with hvH
  -- The four blocks are read off `wH`.
  have hb3 : ∀ i : Fin c, wH (i : ℕ) = (d3 i : Fin H → ℝ) := by
    intro i
    rw [hwH]; dsimp only
    rw [if_pos i.isLt, he3]
    simp [i.isLt]
  have hb1 : ∀ i : Fin r, wH (c + (i : ℕ)) = (d1 i : Fin H → ℝ) := by
    intro i
    have hi := i.isLt
    rw [hwH]; dsimp only
    rw [if_neg (by omega), if_pos (by omega), he1]
    simp [hi]
  have hb2 : ∀ i : Fin (a - r), wH (b + (i : ℕ)) = (d2 i : Fin H → ℝ) := by
    intro i
    have hi := i.isLt
    rw [hwH]; dsimp only
    rw [if_neg (by omega), if_neg (by omega), if_pos (by omega), he2]
    simp
  have hb4 : ∀ i : Fin n4, wH (b + (a - r) + (i : ℕ)) = (d4 i : Fin H → ℝ) := by
    intro i
    have hi := i.isLt
    rw [hwH]; dsimp only
    rw [if_neg (by omega), if_neg (by omega), if_neg (by omega), he4,
      show b + (a - r) + (i : ℕ) - b - (a - r) = (i : ℕ) from by omega]
    simp
  -- Membership statements used by both derived bases.
  have hmemU : ∀ k, k < a → wH (k + c) ∈ U := by
    intro k hk
    rw [hwH]; dsimp only
    rw [if_neg (by omega)]
    by_cases h : k + c < b
    · rw [if_pos h]
      exact hW1U (he1mem _)
    · rw [if_neg h, if_pos (by omega)]
      exact hIU (he2mem _)
  have hmemK : ∀ k, b ≤ k → wH k ∈ K := by
    intro k hk
    rw [hwH]; dsimp only
    rw [if_neg (by omega), if_neg (by omega)]
    by_cases h : k < b + (a - r)
    · rw [if_pos h]
      exact hIK (he2mem _)
    · rw [if_neg h]
      exact hW4K (he4mem _)
  -- `vH` spans, hence is a basis.
  have hsubH : ∀ k, k < H → wH k ∈ Submodule.span ℝ (Set.range vH) := by
    intro k hk
    exact Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  have hspanH : ⊤ ≤ Submodule.span ℝ (Set.range vH) := by
    have h3 : W3 ≤ Submodule.span ℝ (Set.range vH) :=
      le_span_of_basis_mem d3 (fun i => by
        rw [← hb3 i]; exact hsubH _ (by have := i.isLt; omega))
    have h1 : W1 ≤ Submodule.span ℝ (Set.range vH) :=
      le_span_of_basis_mem d1 (fun i => by
        rw [← hb1 i]; exact hsubH _ (by have := i.isLt; omega))
    have h2 : I ≤ Submodule.span ℝ (Set.range vH) :=
      le_span_of_basis_mem d2 (fun i => by
        rw [← hb2 i]; exact hsubH _ (by have := i.isLt; omega))
    have h4 : W4 ≤ Submodule.span ℝ (Set.range vH) :=
      le_span_of_basis_mem d4 (fun i => by
        rw [← hb4 i]; exact hsubH _ (by have := i.isLt; omega))
    rw [← hW3.sup_eq_top]
    refine sup_le (sup_le ?_ ?_) h3
    · rw [← hsup1]; exact sup_le h2 h1
    · rw [← hsup4]; exact sup_le h2 h4
  set bH := basisOfTopLeSpanOfCardEqFinrank vH hspanH (by simp) with hbHdef
  have hbHc : ⇑bH = vH := coe_basisOfTopLeSpanOfCardEqFinrank _ _ _
  -- The input basis: preimages of the first `a` hidden basis vectors, then a basis of `ker A`.
  have hkerf : a + finrank ℝ (LinearMap.ker f) = N := by
    have h := LinearMap.finrank_range_add_finrank_ker f
    rw [← hUdef, hdimU, hdimN] at h
    omega
  have haN : a ≤ N := by omega
  have hnk : finrank ℝ (LinearMap.ker f) = N - a := by omega
  set dk := Module.finBasisOfFinrankEq ℝ (LinearMap.ker f) hnk with hdkdef
  set ek : ℕ → (Fin N → ℝ) :=
    fun k => if h : k < N - a then (dk ⟨k, h⟩ : Fin N → ℝ) else 0 with hek
  have hekmem : ∀ k, ek k ∈ LinearMap.ker f := by
    intro k; rw [hek]; dsimp only; split
    exacts [Submodule.coe_mem _, (LinearMap.ker f).zero_mem]
  have hex : ∀ k : ℕ, ∃ x : Fin N → ℝ, k < a → f x = wH (k + c) := by
    intro k
    by_cases hk : k < a
    · have hmem : wH (k + c) ∈ LinearMap.range f := by rw [← hUdef]; exact hmemU k hk
      obtain ⟨x, hx⟩ := hmem
      exact ⟨x, fun _ => hx⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose xv hxv using hex
  set wN : ℕ → (Fin N → ℝ) := fun k => if k < a then xv k else ek (k - a) with hwN
  set vN : Fin N → (Fin N → ℝ) := fun j => wN (j : ℕ) with hvN
  have hfwN : ∀ k, k < a → f (wN k) = wH (k + c) := by
    intro k hk
    rw [hwN]; dsimp only; rw [if_pos hk]
    exact hxv k hk
  have hkwN : ∀ k, a ≤ k → wN k ∈ LinearMap.ker f := by
    intro k hk
    rw [hwN]; dsimp only; rw [if_neg (by omega)]
    exact hekmem _
  have hsubN : ∀ k, k < N → wN k ∈ Submodule.span ℝ (Set.range vN) := fun k hk =>
    Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  have hspanN : ⊤ ≤ Submodule.span ℝ (Set.range vN) := by
    have hUle : U ≤ Submodule.map f (Submodule.span ℝ (Set.range vN)) := by
      rw [Submodule.map_span, ← hsup1]
      refine sup_le ?_ ?_
      · refine le_span_of_basis_mem d2 (fun i => ?_)
        have hi := i.isLt
        have hk : r + (i : ℕ) < a := by omega
        have hval : (d2 i : Fin H → ℝ) = f (wN (r + (i : ℕ))) := by
          rw [hfwN _ hk, show r + (i : ℕ) + c = b + (i : ℕ) from by omega, hb2 i]
        rw [hval]
        exact Submodule.subset_span ⟨wN (r + (i : ℕ)), ⟨⟨r + (i : ℕ), by omega⟩, rfl⟩, rfl⟩
      · refine le_span_of_basis_mem d1 (fun i => ?_)
        have hi := i.isLt
        have hk : (i : ℕ) < a := by omega
        have hval : (d1 i : Fin H → ℝ) = f (wN (i : ℕ)) := by
          rw [hfwN _ hk, show (i : ℕ) + c = c + (i : ℕ) from by omega, hb1 i]
        rw [hval]
        exact Submodule.subset_span ⟨wN (i : ℕ), ⟨⟨(i : ℕ), by omega⟩, rfl⟩, rfl⟩
    have hkle : LinearMap.ker f ≤ Submodule.span ℝ (Set.range vN) := by
      refine le_span_of_basis_mem dk (fun i => ?_)
      have hi := i.isLt
      have hval : (dk i : Fin N → ℝ) = wN (a + (i : ℕ)) := by
        rw [hwN]; dsimp only
        rw [if_neg (by omega), show a + (i : ℕ) - a = (i : ℕ) from by omega, hek]
        simp
      rw [hval]
      exact hsubN _ (by omega)
    intro y _
    obtain ⟨z, hz, hfz⟩ := hUle (show f y ∈ U by rw [hUdef]; exact ⟨y, rfl⟩)
    have hyz : y - z ∈ LinearMap.ker f := by
      simp only [LinearMap.mem_ker, map_sub, hfz, sub_self]
    have hmem : y - z + z ∈ Submodule.span ℝ (Set.range vN) := add_mem (hkle hyz) hz
    simpa using hmem
  set bN := basisOfTopLeSpanOfCardEqFinrank vN hspanN (by simp) with hbNdef
  have hbNc : ⇑bN = vN := coe_basisOfTopLeSpanOfCardEqFinrank _ _ _
  -- The output basis: the images of the `W_r` and `W_{b-r}` blocks, then a complement of `im B`.
  obtain ⟨Pc, hPc⟩ := Submodule.exists_isCompl (LinearMap.range g)
  have hnP : b + finrank ℝ Pc = M := by
    have h := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range g) Pc
    rw [hPc.sup_eq_top, hPc.inf_eq_bot, finrank_top, finrank_bot, hdimM, hdimRg] at h
    omega
  have hbM : b ≤ M := by omega
  have hnP' : finrank ℝ Pc = M - b := by omega
  set dP := Module.finBasisOfFinrankEq ℝ Pc hnP' with hdPdef
  set eP : ℕ → (Fin M → ℝ) :=
    fun k => if h : k < M - b then (dP ⟨k, h⟩ : Fin M → ℝ) else 0 with heP
  set wM : ℕ → (Fin M → ℝ) := fun k =>
    if k < r then g (wH (k + c)) else if k < b then g (wH (k - r)) else eP (k - b) with hwM
  set vM : Fin M → (Fin M → ℝ) := fun j => wM (j : ℕ) with hvM
  have hgwH1 : ∀ k, k < c → g (wH k) = wM (k + r) := by
    intro k hk
    rw [hwM]; dsimp only
    rw [if_neg (by omega), if_pos (by omega), show k + r - r = k from by omega]
  have hgwH2 : ∀ k, c ≤ k → k < b → g (wH k) = wM (k - c) := by
    intro k hk hk'
    rw [hwM]; dsimp only
    rw [if_pos (by omega), show k - c + c = k from by omega]
  have hgwH3 : ∀ k, b ≤ k → g (wH k) = 0 := by
    intro k hk
    have h := hmemK k hk
    rw [hKdef, LinearMap.mem_ker] at h
    exact h
  have hsubM : ∀ k, k < M → wM k ∈ Submodule.span ℝ (Set.range vM) := fun k hk =>
    Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩
  have hspanM : ⊤ ≤ Submodule.span ℝ (Set.range vM) := by
    have hgle : LinearMap.range g ≤ Submodule.span ℝ (Set.range vM) := by
      have hHtop : Submodule.span ℝ (Set.range vH) = ⊤ := le_antisymm le_top hspanH
      have hrg : LinearMap.range g = Submodule.map g (Submodule.span ℝ (Set.range vH)) := by
        rw [hHtop, Submodule.map_top]
      rw [hrg, Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
      have hj := j.isLt
      rcases lt_or_ge (j : ℕ) c with h1 | h1
      · rw [hvH]
        dsimp only
        rw [hgwH1 _ h1]
        exact hsubM _ (by omega)
      · rcases lt_or_ge (j : ℕ) b with h2 | h2
        · rw [hvH]
          dsimp only
          rw [hgwH2 _ h1 h2]
          exact hsubM _ (by omega)
        · rw [hvH]
          dsimp only
          rw [hgwH3 _ h2]
          exact Submodule.zero_mem _
    have hPle : Pc ≤ Submodule.span ℝ (Set.range vM) := by
      refine le_span_of_basis_mem dP (fun i => ?_)
      have hi := i.isLt
      have hval : (dP i : Fin M → ℝ) = wM (b + (i : ℕ)) := by
        rw [hwM]; dsimp only
        rw [if_neg (by omega), if_neg (by omega), show b + (i : ℕ) - b = (i : ℕ) from by omega,
          heP]
        simp
      rw [hval]
      exact hsubM _ (by omega)
    rw [← hPc.sup_eq_top]
    exact sup_le hgle hPle
  set bM := basisOfTopLeSpanOfCardEqFinrank vM hspanM (by simp) with hbMdef
  have hbMc : ⇑bM = vM := coe_basisOfTopLeSpanOfCardEqFinrank _ _ _
  -- The two matrices in the adapted bases.
  refine ⟨bN, bH, bM, ?_, ?_⟩
  · ext i j
    have hi := i.isLt
    have hj := j.isLt
    rw [LinearMap.toMatrix_apply, hbNc]
    simp only [canonicalA, selCols, Matrix.of_apply, ← hc]
    by_cases hja : (j : ℕ) < a
    · rw [if_pos hja]
      have hidx : (j : ℕ) + c < H := by omega
      have h1 : f (vN j) = bH ⟨(j : ℕ) + c, hidx⟩ := by
        rw [hvN]; dsimp only
        rw [hfwN _ hja, hbHc]
      rw [h1, bH.repr_self, Finsupp.single_apply]
      by_cases hij : (i : ℕ) = (j : ℕ) + c
      · rw [if_pos hij, if_pos (Fin.ext hij.symm)]
      · rw [if_neg hij, if_neg (fun h => hij (by rw [← h]))]
    · rw [if_neg hja]
      have h0 : f (vN j) = 0 := by
        have h := hkwN (j : ℕ) (by omega)
        rw [LinearMap.mem_ker] at h
        rw [hvN]
        exact h
      rw [h0, map_zero, if_neg (by omega)]
      simp
  · ext i j
    have hi := i.isLt
    have hj := j.isLt
    rw [LinearMap.toMatrix_apply, hbHc]
    simp only [canonicalB, selCols, Matrix.of_apply, ← hc]
    rcases lt_or_ge (j : ℕ) c with h1 | h1
    · rw [if_pos h1]
      have hidx : (j : ℕ) + r < M := by omega
      have h2 : g (vH j) = bM ⟨(j : ℕ) + r, hidx⟩ := by
        rw [hvH]; dsimp only
        rw [hgwH1 _ h1, hbMc]
      rw [h2, bM.repr_self, Finsupp.single_apply]
      by_cases hij : (i : ℕ) = (j : ℕ) + r
      · rw [if_pos hij, if_pos (Fin.ext hij.symm)]
      · rw [if_neg hij, if_neg (fun h => hij (by rw [← h]))]
    · rw [if_neg (show ¬((j : ℕ) < c) by omega)]
      rcases lt_or_ge (j : ℕ) b with h2 | h2
      · rw [if_pos h2]
        have hidx : (j : ℕ) - c < M := by omega
        have h3 : g (vH j) = bM ⟨(j : ℕ) - c, hidx⟩ := by
          rw [hvH]; dsimp only
          rw [hgwH2 _ h1 h2, hbMc]
        rw [h3, bM.repr_self, Finsupp.single_apply]
        by_cases hij : (i : ℕ) = (j : ℕ) - c
        · rw [if_pos hij, if_pos (Fin.ext hij.symm)]
        · rw [if_neg hij, if_neg (fun h => hij (by rw [← h]))]
      · rw [if_neg (show ¬((j : ℕ) < b) by omega)]
        have h0 : g (vH j) = 0 := by
          rw [hvH]
          exact hgwH3 _ h2
        rw [h0, map_zero, if_neg (show ¬((i : ℕ) = M) by omega)]
        simp

/-! ## Lemma 3.2 -/

/-- **The three ranks are invariants of the action.** Each factor is multiplied by fixed
invertible matrices, and the shared `S` cancels in the product. -/
public theorem SameOrbit.rank_eq {M N H : ℕ} {A₁ A₂ : Matrix (Fin H) (Fin N) ℝ}
    {B₁ B₂ : Matrix (Fin M) (Fin H) ℝ} (h : SameOrbit A₁ A₂ B₁ B₂) :
    A₁.rank = A₂.rank ∧ B₁.rank = B₂.rank ∧ (B₁ * A₁).rank = (B₂ * A₂).rank := by
  obtain ⟨P, S, Q, hP, hS, hQ, hA, hB⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · rw [← hA, rank_mul_mul_inv S Q hS hQ]
  · rw [← hB, rank_mul_mul_inv P S hP hS]
  · rw [← hA, ← hB, mul_congr_of_units P S Q hS, rank_mul_mul_inv P Q hP hQ]

/-- **Every pair reaches the canonical representative of its stratum.** This is the direction of
Lemma 3.2 that §10 Step 1 uses: a fixed linear change of basis `(G_M, G_H, G_N)` carries an
arbitrary `w* ∈ W₀` to the representative indexed by `(rank A, rank B, rank (B * A))`. -/
public theorem exists_units_to_canonical {M N H : ℕ} (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) :
    SameOrbit A (canonicalA N H A.rank B.rank (B * A).rank)
      B (canonicalB M H B.rank (B * A).rank) := by
  obtain ⟨bN, bH, bM, hA, hB⟩ := exists_adapted_bases A B
  exact sameOrbit_of_toMatrix bN bH bM hA hB

/-- The canonical representative really carries the three ranks it is indexed by. No feasibility
hypothesis is needed here: the triple came from an actual pair. -/
public theorem rank_canonical_of_pair {M N H : ℕ} (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) :
    (canonicalA N H A.rank B.rank (B * A).rank).rank = A.rank ∧
      (canonicalB M H B.rank (B * A).rank).rank = B.rank ∧
      (canonicalB M H B.rank (B * A).rank * canonicalA N H A.rank B.rank (B * A).rank).rank
        = (B * A).rank := by
  obtain ⟨h1, h2, h3⟩ := (exists_units_to_canonical A B).rank_eq
  exact ⟨h1.symm, h2.symm, h3.symm⟩

/-- **Completeness of the invariant.** Two pairs with the same three ranks lie in the same
orbit: both reach the same canonical representative, and the relation is an equivalence. -/
public theorem sameOrbit_of_rank_eq {M N H : ℕ} {A₁ A₂ : Matrix (Fin H) (Fin N) ℝ}
    {B₁ B₂ : Matrix (Fin M) (Fin H) ℝ} (hA : A₁.rank = A₂.rank) (hB : B₁.rank = B₂.rank)
    (hC : (B₁ * A₁).rank = (B₂ * A₂).rank) : SameOrbit A₁ A₂ B₁ B₂ := by
  have h₁ := exists_units_to_canonical A₁ B₁
  have h₂ := exists_units_to_canonical A₂ B₂
  rw [hA, hB, hC] at h₁
  exact h₁.trans h₂.symm

/-- **Lemma 3.2 (Canonical form), p. 9.** The orbit of a pair `(A*, B*)` under
`GL_M × GL_H × GL_N` is determined by, and determines, the triple
`(a, b, r) = (rank A*, rank B*, rank B*A*)`. -/
public theorem sameOrbit_iff_rank_eq {M N H : ℕ} {A₁ A₂ : Matrix (Fin H) (Fin N) ℝ}
    {B₁ B₂ : Matrix (Fin M) (Fin H) ℝ} :
    SameOrbit A₁ A₂ B₁ B₂ ↔
      A₁.rank = A₂.rank ∧ B₁.rank = B₂.rank ∧ (B₁ * A₁).rank = (B₂ * A₂).rank :=
  ⟨SameOrbit.rank_eq, fun h => sameOrbit_of_rank_eq h.1 h.2.1 h.2.2⟩

/-- The form in which the fiber `W₀ = {(A, B) : B * A = C}` sees Lemma 3.2: over one fixed
truth matrix, the rank pair `(a, b)` alone determines the point up to the action, since the
third invariant is `rank C` for every point of the fiber. Together with
`exists_factorization_iff_feasible` (`RankRealization.lean`) this says that the strata of `W₀`
are exactly the orbits, so a table indexed by `(rank A, rank B)` is complete. -/
public theorem sameOrbit_of_fiber {M N H : ℕ} {C : Matrix (Fin M) (Fin N) ℝ}
    {A₁ A₂ : Matrix (Fin H) (Fin N) ℝ} {B₁ B₂ : Matrix (Fin M) (Fin H) ℝ}
    (h₁ : B₁ * A₁ = C) (h₂ : B₂ * A₂ = C) (hA : A₁.rank = A₂.rank) (hB : B₁.rank = B₂.rank) :
    SameOrbit A₁ A₂ B₁ B₂ :=
  sameOrbit_of_rank_eq hA hB (by rw [h₁, h₂])

end AISafetyAtlas.SingularLearning
