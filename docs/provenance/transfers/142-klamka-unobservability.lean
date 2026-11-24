import AISafetyAtlas.LinearSystems.BlockBound

/-!
J. Klamka, *Uncontrollability and Unobservability of Multivariable Systems* (1972),
Theorem 2, p. 726. A complex system is unobservable if some eigenvalue has
`⌊(nᵢ + νᵢ - 1) / νᵢ⌋ > rank C`, where `nᵢ` is its characteristic multiplicity
and `νᵢ` its minimal-polynomial multiplicity.

The cited routes are `not_isObservable_of_finrank_ker_gt_rank`,
`not_isObservable_of_ceil_div_gt_rank`, and `not_isObservable_of_ceil_div_minpoly_gt_rank`.
The map sends `(A, C, μ)` to the zero dynamics with output matrix `[μI - A; C]`
and eigenvalue zero. The rank comparison uses `finrank_ker_transpose_eq`.

Checked: `lake env lean docs/provenance/transfers/142-klamka-unobservability.lean`
-/

namespace Transfer142

open AISafetyAtlas.LinearSystems
open Matrix Module Polynomial

abbrev StateMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℂ
abbrev OutputMatrix (n p : ℕ) := Matrix (Fin p) (Fin n) ℂ

noncomputable def multiplicityBound {n : ℕ} (A : StateMatrix n) (μ : ℂ) (k : ℕ) : ℕ :=
  (A.charpoly.rootMultiplicity μ + k - 1) / k

def PrintHyp {n p : ℕ} (A : StateMatrix n) (C : OutputMatrix n p) : Prop :=
  ∃ μ, A.charpoly.IsRoot μ ∧
    let k := (minpoly ℂ A).rootMultiplicity μ
    0 < k ∧ C.rank < multiplicityBound A μ k

def PrintStatement : Prop :=
  ∀ {n m p : ℕ} (A : StateMatrix n) (_B : Matrix (Fin n) (Fin m) ℂ) (C : OutputMatrix n p),
    PrintHyp A C → ¬ IsObservable A C

def KernelHyp {n p : ℕ} (A : StateMatrix n) (C : OutputMatrix n p) (μ : ℂ) : Prop :=
  C.rank < finrank ℂ (LinearMap.ker (μ • (1 : StateMatrix n) - Aᵀ).mulVecLin)

def KernelStatement : Prop :=
  ∀ {n p} (A : StateMatrix n) (C : OutputMatrix n p) (μ : ℂ),
    KernelHyp A C μ → ¬ IsObservable A C

def CeilStatement : Prop :=
  ∀ {n p} (A : StateMatrix n) (C : OutputMatrix n p) (μ : ℂ) {k : ℕ}, 0 < k →
    Module.End.maxGenEigenspace Aᵀ.mulVecLin μ =
      Module.End.genEigenspace Aᵀ.mulVecLin μ (k : ℕ∞) →
    C.rank < multiplicityBound Aᵀ μ k → ¬ IsObservable A C

def MinpolyStatement : Prop :=
  ∀ {n p} (A : StateMatrix n) (C : OutputMatrix n p) (μ : ℂ),
    let k := (minpoly ℂ Aᵀ).rootMultiplicity μ
    0 < k → C.rank < multiplicityBound Aᵀ μ k → ¬ IsObservable A C

def LeanStatement : Prop := KernelStatement ∧ CeilStatement ∧ MinpolyStatement

noncomputable def phi {n p : ℕ} (A : StateMatrix n) (C : OutputMatrix n p) (μ : ℂ) :
    StateMatrix n × OutputMatrix n (n + p) :=
  (0, reindex finSumFinEquiv (Equiv.refl (Fin n)) (hautusObservabilityMatrix A C μ))

theorem print_hyp {n p : ℕ} {A : StateMatrix n} {C : OutputMatrix n p} {μ : ℂ}
    (h : KernelHyp A C μ) : PrintHyp (phi A C μ).1 (phi A C μ).2 := by
  unfold KernelHyp at h
  rw [finrank_ker_transpose_eq] at h
  have hnull := finrank_ker_add_rank_eq (μ • (1 : StateMatrix n) - A)
  have hrank := MatrixLemmas.rank_fromRows_le (μ • (1 : StateMatrix n) - A) C
  have hlt : (phi A C μ).2.rank < n := by
    change (reindex _ _ (hautusObservabilityMatrix A C μ)).rank < n
    rw [rank_reindex, hautusObservabilityMatrix]
    omega
  have hn : 0 < n := by omega
  have hmin : minpoly ℂ (0 : StateMatrix n) = X := by
    have hinj : Function.Injective (algebraMap ℂ (StateMatrix n)) := by
      intro x y hxy
      have i : Fin n := ⟨0, hn⟩
      simpa [Matrix.algebraMap_eq_diagonal] using congrFun (congrFun hxy i) i
    simpa using minpoly.eq_X_sub_C_of_algebraMap_inj (0 : ℂ) hinj
  have hchar : (0 : StateMatrix n).charpoly = X ^ n := by simp [Matrix.charpoly_zero]
  have hroot (k : ℕ) : (X ^ k : ℂ[X]).rootMultiplicity 0 = k := by
    simpa using rootMultiplicity_X_sub_C_pow (0 : ℂ) k
  refine ⟨0, ?_, ?_⟩
  · change (0 : StateMatrix n).charpoly.IsRoot 0
    simp [hchar, Polynomial.IsRoot, Nat.ne_of_gt hn]
  · change 0 < (minpoly ℂ (0 : StateMatrix n)).rootMultiplicity 0 ∧
      (phi A C μ).2.rank < multiplicityBound 0 0 ((minpoly ℂ (0 : StateMatrix n)).rootMultiplicity 0)
    have hx : (X : ℂ[X]).rootMultiplicity 0 = 1 := by simpa using hroot 1
    simpa [hmin, hx, multiplicityBound, hchar, hroot] using hlt

theorem lean_concl {n p : ℕ} {A : StateMatrix n} {C : OutputMatrix n p} {μ : ℂ}
    (h : ¬ IsObservable (phi A C μ).1 (phi A C μ).2) : ¬ IsObservable A C := by
  unfold IsObservable at h
  push Not at h
  obtain ⟨x, hx, hne⟩ := h
  have hn : 0 < n := by
    by_contra hzero
    exact hne (funext fun i ↦ (Nat.not_lt_zero i.val (by omega)).elim)
  have hzero := hx ⟨0, hn⟩
  change (((phi A C μ).2) * (0 : StateMatrix n) ^ (0 : ℕ)) *ᵥ x = 0 at hzero
  rw [pow_zero, Matrix.mul_one] at hzero
  apply hautus_failure_implies_not_isObservable A C μ x hne
  funext i
  simpa [phi, Matrix.mulVec, Matrix.reindex_apply] using congrFun hzero (finSumFinEquiv i)

private theorem bound_le_kernel {n : ℕ} (A : StateMatrix n) (μ : ℂ) {k : ℕ}
    (hk : 0 < k)
    (hstable : Module.End.maxGenEigenspace A.mulVecLin μ =
      Module.End.genEigenspace A.mulVecLin μ (k : ℕ∞)) :
    multiplicityBound A μ k ≤ finrank ℂ (LinearMap.ker (μ • (1 : StateMatrix n) - A).mulVecLin) := by
  rw [← eigenspace_mulVecLin_eq_ker, multiplicityBound, ← charpoly_mulVecLin]
  exact ceil_div_le_finrank_eigenspace A.mulVecLin μ hk hstable

theorem lean_of_print : PrintStatement → LeanStatement := by
  intro h
  have hker : KernelStatement := fun A C μ hh ↦
    lean_concl (h (phi A C μ).1 (0 : Matrix _ (Fin 0) ℂ) (phi A C μ).2 (print_hyp hh))
  have hceil : CeilStatement := fun A C μ _ hk hstable hb ↦
    hker A C μ (hb.trans_le (bound_le_kernel Aᵀ μ hk hstable))
  exact ⟨hker, hceil, fun A C μ hk hb ↦ hceil A C μ hk
    (maxGenEigenspace_mulVecLin_eq_rootMultiplicity_minpoly Aᵀ μ) hb⟩

theorem print_of_lean : LeanStatement → PrintStatement := by
  intro h n m p A B C hprint
  obtain ⟨μ, _, hk, hb⟩ := hprint
  refine h.1 A C μ ?_
  unfold KernelHyp
  rw [finrank_ker_transpose_eq]
  exact hb.trans_le (bound_le_kernel A μ hk
    (maxGenEigenspace_mulVecLin_eq_rootMultiplicity_minpoly A μ))

end Transfer142
