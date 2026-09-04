module

public import AISafetyAtlas.SingularLearning.EliminationChart

/-!
# Worked models for the elimination chart

Theorem 5.1 of the MAIS issue #3 candidate (p. 10) is **where the locality of the
whole argument comes from**. It produces an analytic diffeomorphism on an open
neighborhood `O` of a factorization, on which

    (1/12)(‖u‖² + ‖Y₀ S_Z‖²_F) ≤ 2K ≤ 6(‖u‖² + ‖Y₀ S_Z‖²_F)

uniformly. Nothing in §8 localizes anything; §8 already works with the residual
germ this chart produces.

## What is proved here, and what is not

**Proved:** the statement `IsEliminationChart`, at the Lemma 3.2 canonical
representative; the dimension split `q + ph + hn + g = HN + MH`; Lemma 5.3's
norm inequalities, in an arbitrary seminormed group rather than print's matrices
of equal shape; **Step 7 in full** — the derivation of the constants `1/12` and
`6` from its three matrix inputs; and `isEliminationChart_zero`, which exhibits
the statement as satisfiable.

**Not proved:** the chart itself. Steps 1–6 construct `Ψ`, which
`IsEliminationChart` quantifies existentially. The obstruction is bookkeeping
rather than mathematics — Lemmas 5.2 and 5.4 need the ℓ² operator norm and the
Frobenius norm on `Matrix` simultaneously, and those are two incompatible
`NormedAddCommGroup` instances on one type, so the mixed inequality must be
written with at least one norm spelled out by hand.

Satisfiability matters here for the usual reason: without
`isEliminationChart_zero` the statement could be an empty relation, and every
theorem quantified over it would be vacuously true.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- **The statement is not vacuous.** At `(a, b, r) = (0, 0, 0)` the chart is
`(A, B) ↦ (0, B, A, 0)`, the gauge and `u` blocks are empty, and the comparison
function is `2K` on the nose. -/
example (M N H : ℕ) : IsEliminationChart M N H 0 0 0 :=
  isEliminationChart_zero M N H

/-- The chart's four blocks account for exactly the ambient dimension
`d = H·N + M·H` — Appendix B item 3. -/
example {M N H r a b : ℕ} (hbM : b ≤ M) (haN : a ≤ N)
    (hra : r ≤ a) (hrb : r ≤ b) (hab : a + b ≤ H + r) :
    elimQ M N a b + elimP M b * elimH H r a b + elimH H r a b * elimN N a
      + elimGauge M N H r a b = H * N + M * H :=
  elim_dimension_split hbM haN hra hrb hab

/-! ## Steps 2–5, and the two round trips

The chart is exercised at the smallest index types that keep every block present: one index
in each of `ρ, σ, τ, η, ν, π`, so `r = 1`, `a = 2`, `b = 2`, `h = 1`, `n = 1`, `p = 1`,
`H = 3`, `N = 3`, `M = 3`. All nine coordinate blocks are then nonempty, which is what makes
the round trips a real test rather than a vacuous one. -/

/-- **Step 2, the exact expansion (5.1).** An identity of matrices, with no hypothesis. -/
example {μ ρ σ τ η ν : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η]
    [DecidableEq ρ] [DecidableEq σ]
    (J : Matrix μ ρ ℝ) (BI : Matrix μ (ρ ⊕ σ) ℝ) (D : Matrix μ τ ℝ) (Y : Matrix μ η ℝ)
    (XR : Matrix ρ ν ℝ) (XP : Matrix σ ν ℝ) (SQ : Matrix τ ν ℝ) (SZ : Matrix η ν ℝ) :
    elimBbar BI D Y * elimAbar (Matrix.fromRows XR XP) SQ SZ - elimCmat J σ ν =
      Matrix.fromCols (BI - elimCI J σ)
        ((BI - elimCI J σ) * Matrix.fromRows XR XP + elimPblock J D * elimT XR SQ + Y * SZ) :=
  elim_step2 J BI D Y XR XP SQ SZ

/-- **Step 3's normalization.** `R(D)P(D) = (I_b ; 0)` exactly, on the whole nonvanishing
locus of `det P_{top}` — not only where Lemma 5.4's norm hypotheses hold. -/
example {β π : Type*} [Fintype β] [Fintype π] [DecidableEq β] [DecidableEq π]
    {Ptop : Matrix β β ℝ} {Pbot : Matrix π β ℝ} (h : IsUnit Ptop.det) :
    elimR Ptop Pbot * Matrix.fromRows Ptop Pbot = Matrix.fromRows 1 0 :=
  elimR_mul_fromRows_self h

/-- **Step 4's shear is exact in both directions.** -/
example {β η ν : Type*} [Fintype η] (Y₁ : Matrix β η ℝ) (SZ : Matrix η ν ℝ)
    (T : Matrix β ν ℝ) :
    elimShearInv Y₁ SZ (elimShear Y₁ SZ T) = T ∧
      elimShear Y₁ SZ (elimShearInv Y₁ SZ T) = T :=
  ⟨elimShearInv_elimShear Y₁ SZ T, elimShear_elimShearInv Y₁ SZ T⟩

/-- **Step 5, `Φ ∘ Ψ = id`**, at the smallest fully nondegenerate index types. -/
example (J : Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) (Fin 1) ℝ)
    {A : Matrix ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) ℝ}
    {B : Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) ((Fin 1 ⊕ Fin 1) ⊕ (Fin 1 ⊕ Fin 1)) ℝ}
    (hA : IsUnit (A.toBlocks₁₁).det)
    (hP : IsUnit (elimPtop J (elimDOf A B)).det) :
    elimPhi J (elimPsi J A B) = (A, B) :=
  elimPhi_elimPsi J hA hP

/-- **Step 5, `Ψ ∘ Φ = id`**, at the same index types. -/
example (J : Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) (Fin 1) ℝ)
    {c : ElimCoords (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1) (Fin 1)}
    (hA : IsUnit (c.A11).det) (hP : IsUnit (elimPtop J c.D).det) :
    elimPsi J (elimPhi J c).1 (elimPhi J c).2 = c :=
  elimPsi_elimPhi J hA hP

/-- **Step 5, the bijection.** `Ψ` is a bijection of print's open set onto its image. -/
example {ρ σ τ η ν π : Type*} [Fintype ρ] [Fintype σ] [Fintype τ] [Fintype η] [Fintype π]
    [DecidableEq ρ] [DecidableEq σ] [DecidableEq τ] [DecidableEq η] [DecidableEq π]
    (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) :
    Set.BijOn (fun w => elimPsi J w.1 w.2) (ElimChartDomain ρ σ τ η ν π J)
      ((fun w => elimPsi J w.1 w.2) '' ElimChartDomain ρ σ τ η ν π J) :=
  elimPsi_bijOn J

/-- **Lemma 5.4's two constants, both as printed**, and the fact that they cannot be
equalized. The `√6` belongs to `R = (P_{top}⁻¹ 0 ; −P_{bot} P_{top}⁻¹ I)` and the `√3` to
`R⁻¹ = (P_{top} 0 ; P_{bot} I)`; swapping them grades print's `√3` against the matrix
print calls `R`, and yields a spurious refutation of Lemma 5.4. -/
example {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    {Ptop : Matrix ι ι ℝ} {Pbot : Matrix κ ι ℝ}
    (hT : IsOpNormSqBound (Ptop - 1) (1 / 4)) (hB : IsOpNormSqBound Pbot (1 / 4)) :
    IsOpNormSqBound (elimR Ptop Pbot) 6 ∧ IsOpNormSqBound (elimRinv Ptop Pbot) 3 :=
  ⟨elim_opNormSqBound_elimR hT hB, elim_opNormSqBound_elimRinv hT hB⟩

example : ¬ IsOpNormSqBound (elimR cePtop cePbot) 3 :=
  not_opNormSqBound_elimR_three


/-! ## Step 6, the exact identity for `2K` -/

/-- **Step 6's (5.3).** `2K = ‖U‖² + ‖UX + R(D)⁻¹V‖²`, at the smallest fully nondegenerate
index types. The only hypotheses are `det P_{top}` a unit and the splitting of `R(D)Y`. -/
example (J : Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) (Fin 1) ℝ)
    (BI : Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) (Fin 1 ⊕ Fin 1) ℝ)
    (D : Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) (Fin 1) ℝ)
    (Y : Matrix ((Fin 1 ⊕ Fin 1) ⊕ Fin 1) (Fin 1) ℝ)
    (Y₁ : Matrix (Fin 1 ⊕ Fin 1) (Fin 1) ℝ) (Y₀ : Matrix (Fin 1) (Fin 1) ℝ)
    (XR XP SQ SZ : Matrix (Fin 1) (Fin 1) ℝ)
    (hP : IsUnit (elimPtop J D).det)
    (hY : elimR (elimPtop J D) (elimPbot J D) * Y = Matrix.fromRows Y₁ Y₀) :
    frobeniusSq (elimBbar BI D Y * elimAbar (Matrix.fromRows XR XP) SQ SZ
        - elimCmat J (Fin 1) (Fin 1))
      = frobeniusSq (BI - elimCI J (Fin 1))
        + frobeniusSq ((BI - elimCI J (Fin 1)) * Matrix.fromRows XR XP
            + elimRinv (elimPtop J D) (elimPbot J D)
              * Matrix.fromRows (elimT XR SQ + Y₁ * SZ) (Y₀ * SZ)) :=
  elim_step6 J BI D Y Y₁ Y₀ XR XP SQ SZ hP hY

/-- **Step 6's second display.** `‖V‖² = ‖T′‖² + ‖Y₀S_Z‖²`, the row-block structure of `V`.
This is the split that makes print's `NF = ‖U‖² + ‖T′‖² + ‖Y₀S_Z‖²` the same number as
`‖U‖² + ‖V‖²`. -/
example {ρ τ ν π : Type*} [Fintype ρ] [Fintype τ] [Fintype ν] [Fintype π]
    (T' : Matrix (ρ ⊕ τ) ν ℝ) (W : Matrix π ν ℝ) :
    frobeniusSq (Matrix.fromRows T' W) = frobeniusSq T' + frobeniusSq W :=
  frobeniusSq_elimV T' W

/-- `P(D)` is recovered from its two row blocks, which is what lets Step 3's normalization be
substituted into Step 2's expansion. -/
example {ρ τ π : Type*} (J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ) (D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ) :
    Matrix.fromRows (elimPtop J D) (elimPbot J D) = elimPblock J D :=
  fromRows_elimPtop_elimPbot J D

/-- **Step 7 applied to Step 6's own shape.** With the three inputs print's Step 7 consumes,
the printed constants `1/12` and `6` come out against `NF = ‖U‖² + ‖V‖²`. Steps 6 and 7 are
both proved, and the `Fin` transport and the analyticity clauses that stood between them and
`IsEliminationChart` are done in `ChartAssembly.lean`. -/
example {E : Type*} [SeminormedAddCommGroup E] (nU nV : ℝ) (P Q : E)
    (hP : ‖P‖ ^ 2 ≤ nU ^ 2 / 4) (hQlo : nV ^ 2 / 6 ≤ ‖Q‖ ^ 2)
    (hQhi : ‖Q‖ ^ 2 ≤ 3 * nV ^ 2) :
    1 / 12 * (nU ^ 2 + nV ^ 2) ≤ nU ^ 2 + ‖P + Q‖ ^ 2 ∧
      nU ^ 2 + ‖P + Q‖ ^ 2 ≤ 6 * (nU ^ 2 + nV ^ 2) :=
  elimination_comparability nU nV P Q hP hQlo hQhi


/-! ## `2K` is the squared Frobenius norm -/

/-- **Print's `2K = ‖BA − C‖²_F`**, the identification Step 6's left-hand side needs. Immediate
from `rrrLoss_eq_sum_sq`: the loss is `½ ∑ (BA − C)²`. -/
example {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) :
    2 * rrrLoss C A B = frobeniusSq (B * A - C) :=
  two_mul_rrrLoss_eq_frobeniusSq C A B

/-- **The gauge does not move `2K`.** `B̄Ā = BA` on the nose, at the rectangular shapes the
chart actually uses — `B : M × H` against `A : H × N`, which the original
`elimGauge_preserves_product` could not express. -/
example {ι κ ω ν : Type*} [Fintype ι] [Fintype κ] [Fintype ω] [Fintype ν] [DecidableEq ι]
    [DecidableEq κ] {A₁₁ : Matrix ι ι ℝ} (A₂₁ : Matrix κ ι ℝ) (A : Matrix (ι ⊕ κ) ν ℝ)
    (B : Matrix ω (ι ⊕ κ) ℝ) (C : Matrix ω ν ℝ) (h : IsUnit A₁₁.det) :
    frobeniusSq ((B * elimLinv A₁₁ A₂₁) * (elimL A₁₁ A₂₁ * A) - C)
      = frobeniusSq (B * A - C) :=
  frobeniusSq_elimGauge_eq A₂₁ A B C h

/-- The two together: the loss of a pair equals the loss of its gauged form, which is what
Step 6 decomposes. At the shapes of the reduced-rank model. -/
example {M H N : ℕ} (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) :
    2 * rrrLoss C A B = frobeniusSq (B * A - C) :=
  two_mul_rrrLoss_eq_frobeniusSq C A B


/-! ## The base point is not in the chart's domain

A convention clash, not an error in either module: print's hidden decomposition puts the `a`
coordinates `A` lands on first, so `A₁₁ = I_a`; `OrbitNormalForm`'s `canonicalA` puts them at
`[b−r, b−r+a)`, the ordering in which `canonicalB` is simplest. The chart is stated in print's
ordering and the base point in the other. -/

/-- **At the witness stratum the chart's `A₁₁` block is singular at the base point.** So
Theorem 5.1's chart does not apply at its own stated base point without a permutation of the
hidden coordinates. -/
example :
    ((canonicalA 3 4 2 2 1).submatrix
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4)) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3))).det
      = 0 :=
  det_canonicalA_toBlocks₁₁_eq_zero

/-- The block, entry by entry: `(0 0 ; 1 0)`. `canonicalA` sends input `0` to hidden `1` and
input `1` to hidden `2`, so on hidden `{0,1}` it is strictly subdiagonal. -/
example :
    (canonicalA 3 4 2 2 1
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4) 0) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 0) = 0)
      ∧ (canonicalA 3 4 2 2 1
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4) 1) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 0) = 1)
      ∧ (canonicalA 3 4 2 2 1
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4) 0) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 1) = 0)
      ∧ (canonicalA 3 4 2 2 1
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4) 1) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 1) = 0) :=
  canonicalA_toBlocks₁₁_entries


/-! ## The permutation that repairs it -/

/-- **`elimReorder` restores print's `A₁₁* = I_a`.** Compare the block before reordering,
which is singular. -/
example :
    ((canonicalA 3 4 2 2 1).submatrix
        (fun p : Fin 2 => (⟨elimReorder 2 2 1 (p : ℕ), by fin_cases p <;> simp [elimReorder]⟩
          : Fin 4))
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3))).det = 1 :=
  det_canonicalA_reordered_eq_one

/-- The two determinants side by side: `0` in `OrbitNormalForm`'s ordering, `1` in print's. The
chart applies in the second and not the first. -/
example :
    ((canonicalA 3 4 2 2 1).submatrix
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 4)) (Fin.castLE (by norm_num : (2:ℕ) ≤ 3))).det = 0
      ∧ ((canonicalA 3 4 2 2 1).submatrix
        (fun p : Fin 2 => (⟨elimReorder 2 2 1 (p : ℕ), by fin_cases p <;> simp [elimReorder]⟩
          : Fin 4))
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3))).det = 1 :=
  ⟨det_canonicalA_toBlocks₁₁_eq_zero, det_canonicalA_reordered_eq_one⟩

/-- **The arithmetic content**, general in the stratum: for `p, j < a` the reordered row is the
one `canonicalA` fills for column `j` exactly when `p = j`. -/
example {a b r : ℕ} (hrb : r ≤ b) {p j : ℕ} (hp : p < a) :
    elimReorder a b r p = j + (b - r) ↔ p = j :=
  elimReorder_hits_iff hrb hp


/-! ## The reordering is a permutation, so it composes in

Which ordering the atlas should present is still open. But it does not block the chart: the
reordering is a bijection of `Fin H`, so it can be composed in without touching
`OrbitNormalForm`. -/

/-- **`elimReorder` is a permutation of the hidden coordinates.** -/
example {a b r H : ℕ} (hra : r ≤ a) (hrb : r ≤ b) (hH : a + (b - r) ≤ H) :
    Fin H ≃ Fin H :=
  elimReorderEquiv hra hrb hH

/-- Both round trips, as pure arithmetic on the four branches. -/
example {a b r : ℕ} (hra : r ≤ a) (hrb : r ≤ b) (p : ℕ) :
    elimReorderInv a b r (elimReorder a b r p) = p ∧
      elimReorder a b r (elimReorderInv a b r p) = p :=
  ⟨elimReorderInv_elimReorder hra hrb p, elimReorder_elimReorderInv hra hrb p⟩

/-- At the witness stratum the permutation sends print's positions `0, 1` to
`OrbitNormalForm`'s `1, 2` — the rows `canonicalA` actually fills. -/
example : elimReorder 2 2 1 0 = 1 ∧ elimReorder 2 2 1 1 = 2 := by
  constructor <;> norm_num [elimReorder]

/-- **The permutation restores print's `A₁₁* = I_a`**, entrywise and in general: for
`p, j < a` the reordered row carries a `1` at column `j` exactly when `p = j`. -/
example {N H a b r : ℕ} (hra : r ≤ a) (hrb : r ≤ b) (hH : a + (b - r) ≤ H)
    (p : Fin H) (j : Fin N) (hp : (p : ℕ) < a) (hj : (j : ℕ) < a) :
    canonicalA N H a b r (elimReorderEquiv hra hrb hH p) j =
      if (p : ℕ) = (j : ℕ) then 1 else 0 :=
  canonicalA_reorderEquiv_entry hra hrb hH p j hp hj


/-! ## The chart's ingredients at the base point

Print: "`X` vanishes at the base", and Step 1's `A₁₁* = I_a`. Both are computations about
`canonicalA` in print's ordering. -/

/-- **`A₁₂ = 0`**: `canonicalA` fills no column `j ≥ a`, so print's `X = A₁₁⁻¹A₁₂` vanishes at
the base point. -/
example {N H a b r : ℕ} (i : Fin H) (j : Fin N) (hj : a ≤ (j : ℕ)) :
    canonicalA N H a b r i j = 0 :=
  canonicalA_col_zero_of_ge i j hj

/-- **`A₂₁ = 0`**: after reordering, `canonicalA` fills no row `p ≥ a`, so print's
`L(A)⁻¹ = (A₁₁ 0 ; A₂₁ I)` is the identity there and the gauge is trivial, `B̄ = B`. -/
example {N H a b r : ℕ} (hra : r ≤ a) (hrb : r ≤ b) (hH : a + (b - r) ≤ H)
    (p : Fin H) (hp : a ≤ (p : ℕ)) (j : Fin N) :
    canonicalA N H a b r (elimReorderEquiv hra hrb hH p) j = 0 :=
  canonicalA_A21_zero hra hrb hH p hp j

/-- The block structure at the witness stratum: identity on the diagonal of the `2 × 2` block,
zero in the unused column and the unused rows. -/
example :
    (canonicalA 3 4 2 2 1 ⟨elimReorder 2 2 1 0, by simp [elimReorder]⟩
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 0) = 1)
      ∧ (canonicalA 3 4 2 2 1 ⟨elimReorder 2 2 1 1, by simp [elimReorder]⟩
        (Fin.castLE (by norm_num : (2:ℕ) ≤ 3) 1) = 1)
      ∧ (∀ i : Fin 4, canonicalA 3 4 2 2 1 i ⟨2, by norm_num⟩ = 0)
      ∧ (∀ j : Fin 3, canonicalA 3 4 2 2 1 ⟨elimReorder 2 2 1 2, by simp [elimReorder]⟩ j = 0) :=
  canonicalA_reordered_block_structure


/-! ## `P(D*) = (I_b ; 0)` and its consequences

Print's Step 3 states the base-point value outright. Everything the chart needs there follows
from that one equation. -/

/-- **The second denominator survives at the base point**: `det P_{top}(D*) = 1`. -/
example {ρ τ π : Type*} [Fintype ρ] [Fintype τ] [Fintype π] [DecidableEq ρ] [DecidableEq τ]
    [DecidableEq π] {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ} {D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ}
    (h : elimPblock J D = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0) :
    IsUnit (elimPtop J D).det :=
  isUnit_det_elimPtop_of_pblock h

/-- **Both `N₀` conditions on `P` hold there with room to spare**: the two Frobenius
quantities are `0`, comfortably below `1/4`. -/
example {ρ τ π : Type*} [Fintype ρ] [Fintype τ] [Fintype π] [DecidableEq ρ] [DecidableEq τ]
    [DecidableEq π] {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ} {D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ}
    (h : elimPblock J D = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0) :
    frobeniusSq (elimPtop J D - 1) < 1 / 4 ∧ frobeniusSq (elimPbot J D) < 1 / 4 := by
  obtain ⟨h1, h2⟩ := frobeniusSq_elimP_zero_of_pblock h
  rw [h1, h2]
  norm_num

/-- **Print's `R(D*) = I_M`.** Step 3 does nothing at the base point. -/
example {ρ τ π : Type*} [Fintype ρ] [Fintype τ] [Fintype π] [DecidableEq ρ] [DecidableEq τ]
    [DecidableEq π] {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ} {D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ}
    (h : elimPblock J D = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0) :
    elimR (elimPtop J D) (elimPbot J D) = 1 :=
  elimR_eq_one_of_pblock h

/-- The hypothesis is exactly print's display and nothing stronger. -/
example {ρ τ π : Type*} [Fintype ρ] [Fintype τ] [Fintype π] [DecidableEq ρ] [DecidableEq τ]
    [DecidableEq π] {J : Matrix ((ρ ⊕ τ) ⊕ π) ρ ℝ} {D : Matrix ((ρ ⊕ τ) ⊕ π) τ ℝ} :
    elimPblock J D = Matrix.fromRows (1 : Matrix (ρ ⊕ τ) (ρ ⊕ τ) ℝ) 0 ↔
      (elimPtop J D = 1 ∧ elimPbot J D = 0) :=
  pblock_eq_iff


/-! ## `D*` from `canonicalB`

At the base point the gauge is trivial, so `D*` is read straight off `canonicalB`: the columns
over `τ`, which print's ordering places at `[a, a+(b−r))`. -/

/-- `elimReorder` sends print's `τ` block to `OrbitNormalForm`'s `[0, b−r)`, where `canonicalB`
keeps `W_{b−r}`. -/
example {a b r t : ℕ} (hra : r ≤ a) (ht : t < b - r) : elimReorder a b r (a + t) = t :=
  elimReorder_tau hra ht

/-- **`canonicalB` on `W_{b−r}`**: hidden `q < b − r` goes to output `q + r`. This is `D*`. -/
example {M H b r : ℕ} (i : Fin M) (q : Fin H) (hq : (q : ℕ) < b - r) :
    canonicalB M H b r i q = if (i : ℕ) = (q : ℕ) + r then 1 else 0 :=
  canonicalB_col_lt i q hq

/-- **`canonicalB` on `W_r`**: hidden `q ∈ [b−r, b)` goes to output `q − (b−r) ∈ [0, r)`. -/
example {M H b r : ℕ} (i : Fin M) (q : Fin H) (hq₁ : b - r ≤ (q : ℕ)) (hq₂ : (q : ℕ) < b) :
    canonicalB M H b r i q = if (i : ℕ) = (q : ℕ) - (b - r) then 1 else 0 :=
  canonicalB_col_mid i q hq₁ hq₂

/-- **`W_{a−r} ⊕ W_h ⊆ ker B`**, print's description of what `canonicalB` kills. -/
example {M H b r : ℕ} (i : Fin M) (q : Fin H) (hq : b ≤ (q : ℕ)) :
    canonicalB M H b r i q = 0 :=
  canonicalB_col_zero_of_ge i q hq

/-- At the witness stratum `D*`'s single column has its `1` at output row `0 + r = 1`, and is
zero at rows `0` and `2` — so `(J | D*)` is the identity on the top two rows and zero on the
third, which is print's `P(D*) = (I_b ; 0)`. -/
example :
    canonicalB 3 4 2 1 ⟨1, by norm_num⟩ ⟨0, by norm_num⟩ = 1
      ∧ canonicalB 3 4 2 1 ⟨0, by norm_num⟩ ⟨0, by norm_num⟩ = 0
      ∧ canonicalB 3 4 2 1 ⟨2, by norm_num⟩ ⟨0, by norm_num⟩ = 0 :=
  ⟨pblock_base_witness.2.1, pblock_base_witness.2.2.1, pblock_base_witness.2.2.2⟩


end AISafetyAtlas.Examples.SingularLearning
