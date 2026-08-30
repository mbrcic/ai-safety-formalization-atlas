module

public import AISafetyAtlas.Analysis.PolynomialGenericity
public import AISafetyAtlas.Conjectures.MAIS.O38
public import Mathlib.LinearAlgebra.Matrix.Transvection

/-!
# MAIS-O38: what is settled about the transcription

`prob:samples` is **answered affirmatively** — by
`AISafetyAtlas.Examples.Conjectures.MAIS.maisO38_polynomialSamplesSuffice_holds`,
in the sibling module `O38Candidate.lean`, and by way of the candidate submitted
as MAIS issue #30 rather than by anything of the atlas's own. What *this* module
supplies is three things a reader would otherwise have to take on trust about
`AISafetyAtlas/Conjectures/MAIS/O38.lean`, and **two warnings** about quantifiers
print leaves unwritten — each a refuted reading, neither of them the answer.

**The predicate is satisfiable.** `uniquelyCoded_two` proves that two one-sparse
coordinate probes pin every dictionary with independent columns at `m = 2`, so
`genericallyUniquelyCoding_two` exhibits a design meeting print's demand at the
smallest interesting `(m, k)`. Without this the whole row could have been an
elaborate definition of a predicate nothing satisfies, and the printed question
would have had a negative answer for that reason rather than for its own.

**Zero sparsity is dead.** `not_uniquelyCoded_of_sparsity_zero` proves that at
`k = 0` no design of any size works, at any nonzero dictionary, and
`not_genericallyUniquelyCoding_of_sparsity_zero` carries that to print's *almost
every* quantifier. This is why `maisO38_polynomialSamplesSuffice` reads print's
unwritten quantifier over `m` at `Filter.atTop`: print's own `k(m) → ∞` then
excludes the case, and no atlas-supplied condition on `k` is needed. The
statement module's `eventually_one_le_sparsity` is that step.

**The every-`m` reading is false.** `not_maisO38_everyDimensionReading` refutes
`maisO38_everyDimensionReading` outright. This is emphatically *not* an answer to
MAIS-O38: the witness is `k 1 = 0`, a degeneracy at one small `m` that print's own
example family `k = ⌈log m⌉` also has. It is recorded because the choice of
reading has to be a finding rather than a preference, and this is the finding.

**The unbounded-sparsity reading is false — the second warning.** Print says
`k(m) → ∞` and never says `k(m) < m`. Read without that,
`maisO38_unboundedSparsityReading` is refuted by
`not_maisO38_unboundedSparsityReading` at `k(m) = m`, `n(m) = 2m`.
`not_uniquelyCoded_of_full_sparsity` proves no design works once `m ≤ k`, and
`not_uniquelyCoded_of_full_sparsity_spark` says this at every dictionary print's
spark condition admits; `ae_sparkCondition` closes the last escape, since a null
spark set would satisfy print's *almost every* vacuously.

**Why that is a warning and not a result.** The argument has no sparse-coding
content: at `k = m` nothing in `ℝᵐ` is constrained and a single transvection
does all the work. `rows_gt_cols_of_full_sparsity_spark` shows print's own
`n ≥ 2k` then forces `m < n` — an undercomplete dictionary, where agenda A3's
subject is `m > n`. Print's named families `k = ⌈m^α⌉` and `k = ⌈log m⌉` are
both `o(m)`, so nothing here touches the question print asks; print says it is
open *"even at `k = ⌈log m⌉`"* and it stays open. MAIS issue #30 states its
claim for `1 ≤ k < m`, which is the same domain read here — and on that domain
its theorem is true, which is what resolves the row. So the graded
`maisO38_polynomialSamplesSuffice` carries that domain and is **proved**, and
this refutation is carried beside it to make the reading a finding rather than a
preference. `exists_admissibleGrowthLaw` checks the narrowed universal is not
empty, so the row is not true by vacuity of its antecedent.

`ae_sparkCondition` is worth more than the warning it serves: it needs a
genericity fact Mathlib does not carry — a nonzero real polynomial in several
variables vanishes only on a null set — which is why
`AISafetyAtlas/Analysis/PolynomialGenericity.lean` exists, and it discharges the
non-nullity obligation the affirmative answer needs as well, since that answer's
own *almost every* clause would otherwise be satisfiable by an empty spark set.
`docs/provenance/mais-o38-transcription.md` records the searches.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open Matrix MeasureTheory
open AISafetyAtlas.Conjectures.MAIS

/-! ## Matrix plumbing -/

private theorem permMatrix_mul_diagonal_apply {m : ℕ} (σ : Equiv.Perm (Fin m)) (d : Fin m → ℝ)
    (a b : Fin m) : (σ.permMatrix ℝ * Matrix.diagonal d) a b = if σ a = b then d b else 0 := by
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Equiv.Perm.permMatrix,
    PEquiv.toMatrix_apply, Equiv.toPEquiv_apply, Finset.sum_ite_eq']

private theorem mul_permMatrix_diagonal_apply {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (σ : Equiv.Perm (Fin m)) (d : Fin m → ℝ) (i : Fin n) (b : Fin m) :
    (A * σ.permMatrix ℝ * Matrix.diagonal d) i b = A i (σ.symm b) * d b := by
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  simp only [permMatrix_mul_diagonal_apply, Equiv.apply_eq_iff_eq_symm_apply,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]

private theorem mulVec_single' {n m : ℕ} (B : Matrix (Fin n) (Fin m) ℝ) (q : Fin m) (c : ℝ) :
    B *ᵥ Pi.single q c = c • B.col q := by
  ext i; simp [Matrix.mulVec_single, Matrix.col, mul_comm]

private theorem inv_diagonal' {m : ℕ} (d : Fin m → ℝ) (hd : ∀ j, d j ≠ 0) :
    (Matrix.diagonal d)⁻¹ = Matrix.diagonal (fun j => (d j)⁻¹) := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  exact congrArg _ (funext fun j => mul_inv_cancel₀ (hd j))

private theorem inv_permMatrix {m : ℕ} (σ : Equiv.Perm (Fin m)) :
    (σ.permMatrix ℝ)⁻¹ = (σ⁻¹).permMatrix ℝ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [← Matrix.permMatrix_mul]; simp

private theorem mul_left_cancel_of_mulVec_inj {n m : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    (hA : Function.Injective A.mulVec) {X Y : Matrix (Fin m) (Fin m) ℝ}
    (h : A * X = A * Y) : X = Y := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm; ext i; exact absurd i.2 (by omega)
  · haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
    exact Matrix.mul_right_injective_iff_mulVec_injective.2 hA h

/-! ## The degeneracy at zero sparsity -/

/--
At `k = 0` every code is the zero vector, so the dataset is `{0}` and every `B`
reproduces it with the zero codes. No design determines a nonzero dictionary.

The hypothesis is `A ≠ 0` rather than a dimension bound because a matrix with no
rows or no columns *is* zero, so `A ≠ 0` already forces `0 < n` and `0 < m`. -/
public theorem not_uniquelyCoded_of_sparsity_zero {n m N : ℕ} {A : Matrix (Fin n) (Fin m) ℝ}
    (hA : A ≠ 0) {x : Fin N → (Fin m → ℝ)} (hx : ∀ i, IsKSparse 0 (x i)) :
    ¬ UniquelyCoded 0 A x := by
  intro h
  obtain ⟨P, D, hP, hD, hB, -⟩ :=
    h 0 (fun _ => 0) (fun _ => isKSparse_zero_iff.2 rfl)
      (fun i => by rw [isKSparse_zero_iff.1 (hx i)]; simp)
  have hU : IsUnit (P * D) := hP.isUnit.mul hD.isUnit
  have hdet : IsUnit (P * D).det := (Matrix.isUnit_iff_isUnit_det _).1 hU
  refine hA ?_
  calc A = A * ((P * D) * (P * D)⁻¹) := by rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    _ = A * P * D * (P * D)⁻¹ := by rw [← Matrix.mul_assoc, Matrix.mul_assoc A P D]
    _ = 0 := by rw [← hB, Matrix.zero_mul]

/-- The spark condition of order `0` tests only the empty set of columns, so it
holds of every matrix and screens nothing out. -/
public theorem sparkCondition_of_sparsity_zero {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) :
    SparkCondition 0 A := by
  intro T hT
  have he : T = ∅ := Finset.card_eq_zero.1 (Nat.le_zero.1 (by simpa using hT))
  subst he
  exact linearIndependent_empty_type

/-- The zero-sparsity degeneracy at print's own *almost every* quantifier: the
failure set is the complement of a single point, hence conull. -/
public theorem not_genericallyUniquelyCoding_of_sparsity_zero {n m N : ℕ}
    (hn : 0 < n) (hm : 0 < m) (x : Fin N → (Fin m → ℝ)) :
    ¬ GenericallyUniquelyCoding 0 n m N x := by
  rintro ⟨hsp, hae⟩
  haveI : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  haveI : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
  have hne : ∀ᵐ A : Fin n → Fin m → ℝ, A ≠ 0 := by refine ae_iff.2 ?_; simp
  have hfalse : ∀ᵐ _A : Fin n → Fin m → ℝ, False := by
    filter_upwards [hae, hne] with A h1 h2
    exact not_uniquelyCoded_of_sparsity_zero h2 hsp (h1 (sparkCondition_of_sparsity_zero _))
  simp [MeasureTheory.ae_iff] at hfalse

/-! ## The degeneracy at full sparsity -/

/--
At `m ≤ k` nothing in `ℝᵐ` is sparse, so `GL(m)` acts on the factorization and no
design of any size determines the dictionary: for a transvection `M`, the pair
`(A M, M⁻¹ x)` reproduces the data and `M` is not a permutation times a diagonal.

The witness is the transvection at the first two coordinates, which is why the
statement needs `2 ≤ m`; at `m = 1` every invertible matrix *is* a diagonal one
and this obstruction genuinely is absent. -/
public theorem not_uniquelyCoded_of_full_sparsity {k n m N : ℕ} (hm : 2 ≤ m) (hk : m ≤ k)
    {A : Matrix (Fin n) (Fin m) ℝ} (hA : Function.Injective A.mulVec)
    (x : Fin N → (Fin m → ℝ)) : ¬ UniquelyCoded k A x := by
  intro h
  set i : Fin m := ⟨0, by omega⟩ with hi
  set j : Fin m := ⟨1, by omega⟩ with hj
  have hij : i ≠ j := by simp [hi, hj, Fin.ext_iff]
  have hMM' : Matrix.transvection i j (1:ℝ) * Matrix.transvection i j (-1:ℝ) = 1 := by
    rw [Matrix.transvection_mul_transvection_same i j hij]; simp
  obtain ⟨P, D, ⟨σ, rfl⟩, ⟨d, hd, rfl⟩, hB, -⟩ :=
    h (A * Matrix.transvection i j (1:ℝ)) (fun t => Matrix.transvection i j (-1:ℝ) *ᵥ x t)
      (fun t => isKSparse_of_card_le hk _)
      (fun t => by rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, hMM', Matrix.mul_one])
  have hMe : Matrix.transvection i j (1:ℝ) = σ.permMatrix ℝ * Matrix.diagonal d :=
    mul_left_cancel_of_mulVec_inj hA (by rw [hB, Matrix.mul_assoc])
  have h1 : (Matrix.transvection i j (1:ℝ)) i i = 1 := by
    simp [Matrix.transvection, Ne.symm hij]
  have h2 : (Matrix.transvection i j (1:ℝ)) i j = 1 := by
    simp [Matrix.transvection, hij]
  rw [hMe, permMatrix_mul_diagonal_apply] at h1 h2
  have e1 : σ i = i := by by_contra hc; rw [if_neg hc] at h1; norm_num at h1
  have e2 : σ i = j := by by_contra hc; rw [if_neg hc] at h2; norm_num at h2
  exact hij (e1.symm.trans e2)

/-- The same degeneracy stated against print's own hypothesis on `A`: once
`m ≤ k`, the spark condition of order `k` reaches every column, so it *implies*
the injectivity the previous theorem assumes. -/
public theorem not_uniquelyCoded_of_full_sparsity_spark {k n m N : ℕ} (hm : 2 ≤ m) (hk : m ≤ k)
    {A : Matrix (Fin n) (Fin m) ℝ} (hA : SparkCondition k A) (x : Fin N → (Fin m → ℝ)) :
    ¬ UniquelyCoded k A x :=
  not_uniquelyCoded_of_full_sparsity hm hk (hA.mulVec_injective (by omega)) x

/-! ## The every-`m` reading is false -/

/--
`maisO38_everyDimensionReading` — print's question read to demand a design at
*every* `m` — is refuted by `k = fun m => m - 1` at `m = 1`, where the sparsity is
zero.

**This is not an answer to MAIS-O38.** It says only that the strictest reading of
a quantifier print never writes is false at one small `m`, and print's own example
family `k = ⌈log m⌉` has the same `k 1 = 0`. -/
public theorem not_maisO38_everyDimensionReading : ¬ maisO38_everyDimensionReading := by
  intro h
  obtain ⟨N, p, -, hdesign⟩ :=
    h (fun m => m - 1) (fun m => 2 * m)
      (Filter.tendsto_atTop_atTop.2 fun b => ⟨b + 1, fun a ha => by omega⟩)
      (fun m => by omega)
  obtain ⟨x, hx⟩ := hdesign 1
  exact not_genericallyUniquelyCoding_of_sparsity_zero (n := 2) (m := 1)
    (by norm_num) (by norm_num) x (by simpa using hx)

/-! ## The predicate is satisfiable: two probes at `m = 2` -/

private theorem sparse_one_repr {v : Fin 2 → ℝ} (h : IsKSparse 1 v) :
    ∃ q : Fin 2, v = Pi.single q (v q) := by
  have h' : (Function.support v).ncard ≤ 1 := h
  by_cases h0 : v 0 = 0
  · exact ⟨1, by ext l; fin_cases l <;> simp [h0]⟩
  · refine ⟨0, ?_⟩
    have h1 : v 1 = 0 := by
      by_contra h1
      have hsub : ({0, 1} : Set (Fin 2)) ⊆ Function.support v := by
        intro z hz
        rcases hz with rfl | rfl
        · simpa [Function.mem_support] using h0
        · simpa [Function.mem_support] using h1
      have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
      rw [Set.ncard_pair (by decide : (0:Fin 2) ≠ 1)] at h2
      omega
    ext l; fin_cases l <;> simp [h1]

/--
**Print's demand is met at `m = 2`, `k = 1`, with `N = 2`.**

The two one-sparse coordinate probes `e₁, e₂` make every dictionary with
independent columns uniquely coded, for *every* rival `B` and every one-sparse
rewriting of the codes.

The argument is the classical one and it uses both halves of the sparsity: a
one-sparse rival code writes each datum as a multiple of a single column of `B`,
independence of `A`'s columns forces the two columns used to be distinct, and the
resulting index bijection is the permutation while the two scale factors are the
diagonal. -/
public theorem uniquelyCoded_two {n : ℕ} {A : Matrix (Fin n) (Fin 2) ℝ}
    (hA : LinearIndependent ℝ A.col) :
    UniquelyCoded 1 A (fun t : Fin 2 => Pi.single t (1:ℝ)) := by
  intro B x' hsp heq
  choose q hq using fun t => sparse_one_repr (hsp t)
  set c : Fin 2 → ℝ := fun t => x' t (q t) with hcdef
  have key : ∀ t, c t • B.col (q t) = A.col t := by
    intro t
    have h := heq t
    rw [hq t, mulVec_single', mulVec_single', one_smul] at h
    exact h
  have hc : ∀ t, c t ≠ 0 := by
    intro t ht
    have h := key t
    rw [ht, zero_smul] at h
    exact hA.ne_zero t h.symm
  have hq01 : q 0 ≠ q 1 := by
    intro hqe
    have h0 := key 0
    have h1 := key 1
    rw [← hqe] at h1
    have hzero : (c 1) • A.col 0 + (-(c 0)) • A.col 1 = 0 := by
      rw [← h0, ← h1]; module
    have hgz := Fintype.linearIndependent_iff.1 hA ![c 1, -(c 0)] (by
      simpa [Fin.sum_univ_two] using hzero) 0
    exact hc 1 (by simpa using hgz)
  have hqinj : Function.Injective q := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exact absurd hab hq01
    · exact absurd hab.symm hq01
    · rfl
  set σ : Equiv.Perm (Fin 2) := Equiv.ofBijective q (Finite.injective_iff_bijective.1 hqinj)
    with hσdef
  have hσ : ∀ t, σ t = q t := fun _ => rfl
  set d : Fin 2 → ℝ := fun j => (c (σ.symm j))⁻¹ with hddef
  have hd : ∀ j, d j ≠ 0 := fun j => inv_ne_zero (hc _)
  refine ⟨σ.permMatrix ℝ, Matrix.diagonal d, ⟨σ, rfl⟩, ⟨d, hd, rfl⟩, ?_, ?_⟩
  · ext i b
    rw [mul_permMatrix_diagonal_apply]
    set t := σ.symm b with ht
    have hb : q t = b := by rw [← hσ t, ht, Equiv.apply_symm_apply]
    have hcol : c t * B i b = A i t := by
      have h := congrFun (key t) i
      simpa [Matrix.col_apply, hb] using h
    have hdb : d b = (c t)⁻¹ := rfl
    rw [hdb, ← hcol, mul_comm (c t) (B i b), mul_assoc, mul_inv_cancel₀ (hc t), mul_one]
  · intro t
    have hsym : σ.symm (q t) = t := by rw [← hσ t, Equiv.symm_apply_apply]
    rw [inv_diagonal' d hd, inv_permMatrix]
    have hstep : ((σ⁻¹).permMatrix ℝ) *ᵥ (Pi.single t (1:ℝ)) = Pi.single (σ t) (1:ℝ) := by
      rw [Matrix.permMatrix_mulVec]
      ext l
      simp [Pi.single_apply, Equiv.eq_symm_apply, eq_comm]
    rw [← Matrix.mulVec_mulVec, hstep, hσ t]
    ext l
    rw [hq t]
    simp only [Matrix.mulVec, Matrix.diagonal, dotProduct, Matrix.of_apply, Pi.single_apply]
    by_cases hl : l = q t
    · simp [hl, hsym, hddef, hcdef]
    · simp [hl]

/--
The design of `uniquelyCoded_two` meets print's *almost every* demand at
`m = 2`, `k = 1`, for every ambient dimension `n` — and it does so pointwise, so
no null set is discarded.

This inhabits `GenericallyUniquelyCoding` at the smallest parameters at which
neither degeneracy bites, which is the non-vacuity obligation for
`O38PolynomialSampleAnswer`'s inner existential. It settles nothing about the
question, whose content is entirely in how `N` grows. -/
public theorem genericallyUniquelyCoding_two (n : ℕ) :
    GenericallyUniquelyCoding 1 n 2 2 (fun t : Fin 2 => Pi.single t (1:ℝ)) := by
  refine ⟨fun i => ?_, Filter.Eventually.of_forall fun A hA =>
    uniquelyCoded_two (hA.linearIndependent_col (by omega))⟩
  have hsub : Function.support (Pi.single i (1:ℝ)) ⊆ ({i} : Set (Fin 2)) := by
    intro l hl
    by_contra hne
    exact hl (Pi.single_eq_of_ne (by simpa using hne) 1)
  calc (Function.support (Pi.single i (1:ℝ))).ncard
      ≤ ({i} : Set (Fin 2)).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = 1 := Set.ncard_singleton i

/-! ## The submitted candidate would answer the row -/

/--
**If MAIS issue #30's theorem is correct, CONJ-025 is resolved affirmatively.**

Nothing here checks the candidate. This discharges the prior question — whether
the claim, if true, is even about this row — and the answer is yes, with slack in
the atlas's favour on two axes. The candidate fixes its codes before `n` where
print allows them to depend on it, and delivers a design at every `m ≥ 2` where
`O38PolynomialSampleAnswer` asks only for sufficiently large `m`; the proof
spends both.

The polynomial witness is `X³ + 2X`, which `O38PolynomialSampleAnswer` requires to
dominate `N` at **every** `m`, not merely eventually. It does so with equality,
so the candidate's bound is exactly a polynomial bound in print's sense. -/
public theorem maisO38_polynomialSamplesSuffice_of_candidate
    (h : o38PolynomialSampleCandidate) : maisO38_polynomialSamplesSuffice := by
  intro k n hk hn hlt
  refine ⟨fun m => m ^ 3 + 2 * m, Polynomial.X ^ 3 + 2 * Polynomial.X, fun m => by simp, ?_⟩
  filter_upwards [hlt, eventually_one_le_sparsity hk, Filter.eventually_ge_atTop 2]
    with m hlt' hone htwo
  obtain ⟨x, hsparse, hae⟩ := h m (k m) htwo hone hlt'
  exact ⟨x, hsparse, hae (n m) (hn m)⟩

/-! ## The spark-condition set is not null, and the printed question is false -/

open AISafetyAtlas.Analysis MvPolynomial in
/-- For a fixed column set `S` no larger than the number of rows, almost every
matrix has those columns linearly independent.

The witness is the `S × S` minor on any injection `S ↪ Fin n`, which exists
because `S.card ≤ n`. Its determinant is a polynomial in the entries, nonzero
because the minor is the identity at one point, so `ae_eval_ne_zero_uncurry`
makes it nonzero almost everywhere; restricting to the chosen rows is linear, so
independence of the minor's columns pulls back. -/
public theorem ae_linearIndependent_col {n m : ℕ} (S : Finset (Fin m)) (hS : S.card ≤ n) :
    ∀ᵐ A : Fin n → Fin m → ℝ,
      LinearIndependent ℝ fun j : S => (Matrix.of A).col (j : Fin m) := by
  classical
  obtain ⟨f⟩ : Nonempty (S ↪ Fin n) :=
    Function.Embedding.nonempty_iff_card_le.2 (by simpa using hS)
  set P : MvPolynomial (Fin n × Fin m) ℝ :=
    (Matrix.of fun a b : S => (X (f a, (b : Fin m)) : MvPolynomial (Fin n × Fin m) ℝ)).det
    with hP
  have hkey : ∀ y : Fin n × Fin m → ℝ,
      MvPolynomial.eval y P = (Matrix.of fun a b : S => y (f a, (b : Fin m))).det := by
    intro y
    rw [hP, RingHom.map_det]
    congr 1
    ext a b
    simp
  have hPne : P ≠ 0 := by
    intro h0
    set y₀ : Fin n × Fin m → ℝ :=
      fun q => if ∃ a : S, f a = q.1 ∧ (a : Fin m) = q.2 then 1 else 0 with hy₀
    have hone : (Matrix.of fun a b : S => y₀ (f a, (b : Fin m))) = 1 := by
      ext a b
      by_cases hab : a = b
      · subst hab; simp [hy₀]
      · simp [hy₀, hab, Ne.symm hab]
    have hev := hkey y₀
    rw [h0, hone] at hev
    simp at hev
  filter_upwards [ae_eval_ne_zero_uncurry hPne] with A hA
  rw [hkey] at hA
  have hdet : (Matrix.of fun a b : S => A (f a) (b : Fin m)).det ≠ 0 := by
    simpa [Function.uncurry] using hA
  have hcols : LinearIndependent ℝ (Matrix.of fun a b : S => A (f a) (b : Fin m)).col :=
    Matrix.linearIndependent_cols_of_isUnit
      ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  rw [Fintype.linearIndependent_iff] at hcols ⊢
  intro g hg
  refine hcols g (funext fun a => ?_)
  have h1 := congrFun hg (f a)
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.col, Matrix.transpose_apply,
    Matrix.of_apply, Pi.zero_apply] at h1 ⊢
  exact h1

/--
**Print's spark condition holds almost everywhere**, whenever print's own
`n ≥ 2k` holds.

This is the statement CONJ-025's refutation field named as missing:
without it the *almost every* quantifier in `GenericallyUniquelyCoding` could be
satisfied vacuously by a null spark set, and the full-sparsity findings would
settle nothing. -/
public theorem ae_sparkCondition {k n m : ℕ} (h : 2 * k ≤ n) :
    ∀ᵐ A : Fin n → Fin m → ℝ, SparkCondition k (Matrix.of A) := by
  refine MeasureTheory.ae_all_iff.2 fun S => ?_
  by_cases hS : S.card ≤ 2 * k
  · filter_upwards [ae_linearIndependent_col S (hS.trans h)] with A hA using fun _ => hA
  · filter_upwards with A hc using absurd hc hS

open AISafetyAtlas.Analysis in
/-- The same fact as the non-nullity CONJ-025's refutation field asked for. -/
public theorem measure_setOf_sparkCondition_ne_zero {k n m : ℕ} (h : 2 * k ≤ n) :
    MeasureTheory.volume {A : Fin n → Fin m → ℝ | SparkCondition k (Matrix.of A)} ≠ 0 := by
  intro h0
  refine volume_ne_zero_pi_pi (Fin n) (Fin m) (MeasureTheory.Measure.measure_univ_eq_zero.1 ?_)
  have hco : MeasureTheory.volume {A : Fin n → Fin m → ℝ | ¬ SparkCondition k (Matrix.of A)} = 0 := by
    have hae := ae_sparkCondition (k := k) (n := n) (m := m) h
    rwa [MeasureTheory.ae_iff] at hae
  refine measure_mono_null (fun A _ => ?_) (measure_union_null h0 hco)
  by_cases hA : SparkCondition k (Matrix.of A) <;> simp [hA]

/--
**The full-sparsity route forces an undercomplete dictionary.** `m ≤ k` is what
`not_uniquelyCoded_of_full_sparsity` needs and `2k ≤ n` is print's own
hypothesis, so together they put strictly more rows than columns in `A`.

This is recorded as a theorem rather than a remark because it is the one thing a
reader should carry away about how far the refutation reaches. Agenda A3 is
about superposition, which its §2 places in the regime `m > n`; the refuting
instance is on the other side of that line. Print does not impose `m > n` on
`prob:samples` — it states that hypothesis explicitly where it wants it, in
`conj:independent` and in the toy-model problem, and states it here neither for
`n` nor as `k < m` — so this is not a defect in the transcription. It is a fact
about the witness. -/
public theorem rows_gt_cols_of_full_sparsity_spark {k n m : ℕ} (hm : 1 ≤ m) (hk : m ≤ k)
    (hn : 2 * k ≤ n) : m < n := by omega

/--
**The admissible growth laws are not empty.** `k m = m / 2` with `n m = m` meets
all three binders of `maisO38_polynomialSamplesSuffice`, so narrowing the domain
of `k` to eventually `k m < m` has not emptied the universal and made the row
true for that reason. Print's own `k = ⌈log m⌉` is another. -/
public theorem exists_admissibleGrowthLaw :
    ∃ k n : ℕ → ℕ, Filter.Tendsto k Filter.atTop Filter.atTop ∧
      (∀ m, 2 * k m ≤ n m) ∧ (∀ᶠ m in Filter.atTop, k m < m) := by
  refine ⟨fun m => m / 2, fun m => m, ?_, fun m => by dsimp only; omega, ?_⟩
  · exact Filter.tendsto_atTop_atTop.2 fun b => ⟨2 * b + 1, fun a ha => by omega⟩
  · filter_upwards [Filter.eventually_ge_atTop 1] with m hm using by omega

open AISafetyAtlas.Analysis in
/--
**The unbounded-sparsity reading is false**, and this is a warning about a
quantifier print leaves unwritten rather than a result about sparse coding.

The witness is the growth law `k(m) = m` with `n(m) = 2m`. It is inside
`maisO38_unboundedSparsityReading`: `k(m) = m → ∞` is print's hypothesis on `k`,
and `n = 2k` is the boundary case of print's `n ≥ 2k`. At it,
`not_uniquelyCoded_of_full_sparsity_spark` says no design of any size is
uniquely coded at *any* dictionary the spark condition admits, and
`ae_sparkCondition` says almost every dictionary is one — so the design an
affirmative answer supplies would have to fail almost everywhere while holding
almost everywhere.

**This is not an answer to MAIS-O38, and is not graded as one.** The refuted
proposition is the *unbounded-sparsity reading*, not
`maisO38_polynomialSamplesSuffice`, whose domain for `k` is eventually
`k m < m`. Three things make the witness degenerate rather than informative.
`k(m) = m` makes every vector in `ℝᵐ` `k`-sparse, so the dictionary is pinned by
nothing and the argument uses no sparse-coding content — a transvection is the
whole of it. By `rows_gt_cols_of_full_sparsity_spark` print's own `n ≥ 2k` then
forces `m < n`, an undercomplete dictionary, where agenda A3's subject is the
regime `m > n`. And print's two named families `k = ⌈m^α⌉` and `k = ⌈log m⌉` are
both `o(m)`, so neither is touched; print says the question is open *"even at
`k = ⌈log m⌉`"*, and it stays open there. Nor does this bear on MAIS issue #30,
whose claim is stated for `1 ≤ k < m` and so never reaches this growth law —
that reading of the domain is the same one taken here.

**No conflict with the bounds print quotes.** At `k = m` the classical counts
print names — `(k+1)·binom(m,k)`, `k·binom(m,k)²`, `m(k-1)·binom(m,k)+m` —
collapse to polynomials in `m`, which could look like a contradiction. It is
not one: those theorems are uniqueness results for a sparsity that constrains,
and none of them is transcribed, checked, or asserted anywhere in this
repository. -/
public theorem not_maisO38_unboundedSparsityReading : ¬ maisO38_unboundedSparsityReading := by
  intro h
  obtain ⟨N, -, -, hev⟩ := h (fun m => m) (fun m => 2 * m) Filter.tendsto_id fun _ => le_rfl
  obtain ⟨m, ⟨x, hx⟩, hm2⟩ := (hev.and (Filter.eventually_ge_atTop 2)).exists
  have hfalse : ∀ᵐ _A : Fin (2 * m) → Fin m → ℝ, False := by
    filter_upwards [ae_sparkCondition (k := m) (n := 2 * m) (m := m) le_rfl, hx.2] with A hA hAU
    exact not_uniquelyCoded_of_full_sparsity_spark hm2 le_rfl hA x (hAU hA)
  rw [Filter.eventually_false_iff_eq_bot, MeasureTheory.ae_eq_bot] at hfalse
  exact volume_ne_zero_pi_pi (Fin (2 * m)) (Fin m) hfalse

end AISafetyAtlas.Examples.Conjectures.MAIS
