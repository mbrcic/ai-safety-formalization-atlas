module

public import AISafetyAtlas.SingularLearning.ChamberIntegral

/-!
# Worked models for the chamber integral

Appendix A of the MAIS issue #3 candidate supplies the two-sided order of the
chamber integral `J(T)`, which Lemma 8.5's read-off converts into the local
pair. It is self-contained — "no proof in it uses anything from the body of the
paper" — and elementary; its only measure-theoretic input is Tonelli.

**No integrality is used anywhere.** The plan recorded this material as "the
largest single risk in the project: no source packages the real-`α`, real-`ρ`
estimate, and `ρ = p/2` is a half-integer". Appendix A is stated at exactly
`k ≥ 1` integer, `α > −1` real, `ρ > 0` real, and says twice that
half-integrality is never used. Everything below is at real parameters.

## What is proved here, and what is not

**Lemma A.2 is proved in full** (`chamberA2`), with the paper's explicit
constant `κ` transcribed term for term: all three regions `(0, 1/T]`,
`(1/T, 1]`, `(1, ∞)`, their assembly, and the three-case evaluation of
`J = ∫_{1/T}^1 s^{a−b−1} ds`. The case `a = b` is the one that produces
`log T`, and hence the only way the multiplicity can exceed `1`; it is stated
separately as `chamberJ_of_eq`.

Also proved: **A.4's upper bound** — the Vandermonde majorization
`0 ≤ ∏_{i<j}(s_j − s_i) ≤ ∏_j s_j^{j−1}` on the ordered chamber, the pointwise
domination of the integrand by a product, and the Tonelli step to
`∏_i G(T; α+i, ρ)` — and **Lemma 8.15**, the `k!` symmetrization identifying the
full-orthant integral with the chamber one.

**Not proved:** Lemma A.2's *localized* bounds (i)–(iii); A.4's hazard remarks;
and Lemma A.5's explicit boxes, which supply the matching lower bound. Corollary
8.16 needs A.5, so it is not yet available.

## The exponent that did not bite

`∏_j s_j^{j−1}` is where seven previous defects in this project would have
recurred, since `j − 1` in `ℕ` truncates at `j = 0`. It is never formed:
coordinates are indexed by `Fin k`, so the paper's 1-based `s_j` is `s j` and its
`j − 1` is literally `(j : ℕ)`, arriving from `Fin.card_Iio`. Structural
avoidance, not a guarded subtraction.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- The integrand of `G(T; a, b) = ∫₀^∞ e^{−s} s^{a−1} (1 + T s)^{−b} ds`
is integrable at real `a > 0`, `b ≥ 0` — no integrality anywhere. -/
example {T a b : ℝ} (hT : 0 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    MeasureTheory.IntegrableOn (chamberIntegrand T a b) (Set.Ioi 0) :=
  integrableOn_chamberIntegrand hT ha hb

/-- **Region (0, 1/T].** Here `(1 + Ts)^{-b}` is harmless and the bound is the
plain Gamma-type tail. -/
example {T a b : ℝ} (hT : 3 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    (∫ s in Set.Ioc (0:ℝ) (1 / T), chamberIntegrand T a b s) ≤ T ^ (-a) / a :=
  chamberG0_le hT ha hb

/-- **Lemma A.2.** The two-sided order of the model integral, at real
parameters, with the paper's explicit `κ`. `Θ(T;a,b) = T^{−min(a,b)}(log T)^{1{a=b}}`. -/
example {T a b : ℝ} (hT : 3 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    (kappaA2 a b)⁻¹ * chamberTheta T a b ≤ chamberG T a b ∧
      chamberG T a b ≤ kappaA2 a b * chamberTheta T a b :=
  chamberA2 hT ha hb

/-- **Where the logarithm comes from.** `J = log T` exactly when `a = b` — the
only mechanism by which the multiplicity `N*` can exceed `1`. -/
example {T a b : ℝ} (hT : 3 ≤ T) (hab : a = b) :
    chamberJ T a b = Real.log T :=
  chamberJ_of_eq hT hab

/-- **Region (1/T, 1].** Two-sided, in terms of `J`. -/
example {T a b : ℝ} (hT : 3 ≤ T) (ha : 0 < a) (hb : 0 ≤ b) :
    Real.exp (-1) * 2 ^ (-b) * T ^ (-b) * chamberJ T a b
        ≤ ∫ s in Set.Ioc (1 / T) (1:ℝ), chamberIntegrand T a b s ∧
      (∫ s in Set.Ioc (1 / T) (1:ℝ), chamberIntegrand T a b s)
        ≤ T ^ (-b) * chamberJ T a b :=
  chamberG1_bounds hT ha hb

/-- **A.4's Vandermonde majorization.** On the ordered chamber the Vandermonde
product is dominated by `∏_j s_j^{j−1}` — with the exponent arriving as
`(j : ℕ)` from `Fin.card_Iio`, so no natural subtraction is ever formed. -/
example {k : ℕ} {s : Fin k → ℝ} (hs : s ∈ chamberDelta k) :
    chamberVandermonde s ≤ ∏ j : Fin k, s j ^ (j : ℕ) :=
  chamberVandermonde_le_prod hs

/-- **Lemma 8.15.** The integrand is permutation-invariant and the ordered
chamber is a fundamental domain, so the full-orthant integral is `k!` times the
chamber one. -/
example {k : ℕ} {T α ρ : ℝ} (hT : 0 ≤ T) (hα : -1 < α) (hρ : 0 ≤ ρ) :
    chamberJFull k T α ρ = (Nat.factorial k : ℝ) * chamberI k T α ρ :=
  chamberJFull_eq_factorial_mul_chamberI hT hα hρ

/-! ## Lemma A.5 and Corollary 8.16

The transcription anchors for the matching lower bound. Print's arithmetic at `k = 1` is
small enough to pin by `norm_num`, and pinning it means a future edit to the case split or to
the indexing convention breaks loudly instead of quietly changing a constant. -/

/-- The vertex exponents at `k = 1` are print's two: `E_0 = ρ` (the single coordinate sits on
a large box) and `E_1 = A_1 = α + 1` (it sits on a small box). -/
example (α ρ : ℝ) : chamberVertexExponent 1 α ρ 0 = ρ := by
  simp [chamberVertexExponent]

example (α ρ : ℝ) : chamberVertexExponent 1 α ρ 1 = α + 1 := by
  simp [chamberVertexExponent]

/-- Hence `E⋆ = min(α + 1, ρ)` at `k = 1`: print's Lemma A.3(iii) in the smallest case. -/
example (α ρ : ℝ) : chamberMinExponent 1 α ρ = min (α + 1) ρ := by
  rw [chamberMinExponent_eq_sum_min]
  simp

/-- **The increment identity**, print's `E_{s+1} − E_s = α + s + 1 − ρ`, at `k = 1`. -/
example (α ρ : ℝ) : chamberVertexExponent 1 α ρ 1 - chamberVertexExponent 1 α ρ 0 = α + 1 - ρ :=
  by simp [chamberVertexExponent]

/-- The exponent of print's constant `2^{-k(k-1)/2}` is `∑_j (j : ℕ)`, which takes the values
`0, 1, 6` at `k = 1, 2, 4`. Pinned so that a change of indexing convention cannot silently
move the constant. -/
example : (∑ j : Fin 1, (j : ℕ)) = 0 := by simp

example : (∑ j : Fin 2, (j : ℕ)) = 1 := by simp [Fin.sum_univ_two]

example : (∑ j : Fin 4, (j : ℕ)) = 6 := by simp [Fin.sum_univ_four]

/-- And that exponent really is `k(k-1)/2`, with no division formed in `ℕ`. -/
example (k : ℕ) : (∑ j : Fin k, (j : ℕ)) * 2 = k * (k - 1) := sum_fin_val_mul_two k

/-- **Print's threshold really does dominate the two bounds the proof consumes**, so the
print-facing form of clause (ii) is available. -/
example (k : ℕ) : 3 ≤ (16:ℝ) ^ (k + 1) ∧ 2 * (4:ℝ) ^ k ≤ (16:ℝ) ^ (k + 1) := chamberT0_le k

/-- **Lemma A.5(i).** Strong separation implies membership in the ordered chamber — strictly
stronger than the monotonicity `Δ` asks for. -/
example {k : ℕ} {s : Fin k → ℝ} (hs : chamberSeparated s) : s ∈ chamberDelta k :=
  hs.mem_chamberDelta

/-- **Lemma A.5(i), the Vandermonde lower bound**, the mirror of A.4's upper one. -/
example {k : ℕ} {s : Fin k → ℝ} (hs : chamberSeparated s) :
    chamberSepConst k * (∏ j : Fin k, s j ^ (j : ℕ)) ≤ chamberVandermonde s :=
  chamberVandermonde_ge_const_mul hs

/-- **Lemma A.5(ii).** The matching lower bound for the exponent, at print's own threshold. -/
example {k : ℕ} {T α ρ : ℝ} (hα : -1 < α) (hρ : 0 ≤ ρ) (hT : (16:ℝ) ^ (k + 1) ≤ T) :
    chamberKappa3 k α ρ * T ^ (-chamberMinExponent k α ρ) ≤ chamberI k T α ρ :=
  chamberA5_lower_of_T0 hα hρ hT

/-- **Lemma A.5(iii)'s resonance, derived rather than imported.** Two adjacent vertices carry
the same exponent exactly when the coordinate between them resonates, `A_{m+1} = ρ`. -/
example {k : ℕ} {α ρ : ℝ} {m : ℕ} (hm : m < k)
    (h : chamberVertexExponent k α ρ (m + 1) = chamberVertexExponent k α ρ m) :
    α + (m : ℝ) + 1 = ρ :=
  resonance_of_chamberVertexExponent_eq hm h

/-- **Print's `N⋆ ∈ {1, 2}`**, as `#{i : A_i = ρ} ≤ 1`. -/
example (k : ℕ) (α ρ : ℝ) : chamberResonanceCount k α ρ ≤ 1 :=
  chamberResonanceCount_le_one k α ρ

/-- At `k = 1` the multiplicity is `2` exactly in the resonant case `α + 1 = ρ`. -/
example (α ρ : ℝ) (h : α + 1 = ρ) : chamberResonanceCount 1 α ρ = 1 := by
  classical
  rw [chamberResonanceCount]
  rw [Finset.filter_true_of_mem (fun i _ => by
    have : (i : ℕ) = 0 := Nat.lt_one_iff.mp i.isLt
    simpa [this] using h)]
  simp

example (α ρ : ℝ) (h : α + 1 ≠ ρ) : chamberResonanceCount 1 α ρ = 0 := by
  classical
  rw [chamberResonanceCount]
  rw [Finset.filter_false_of_mem (fun i _ => by
    have hi : (i : ℕ) = 0 := Nat.lt_one_iff.mp i.isLt
    simpa [hi] using h)]
  simp

/-- **Lemma A.5(v).** The lower bound holds on print's full range `T ≥ 3`, at the cost of a
constant. This is what makes it comparable with `chamberA4_upper`, stated at `T ≥ 3`. -/
example {k : ℕ} {α ρ : ℝ} (hα : -1 < α) (hρ : 0 < ρ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 3 ≤ T →
      C * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ 0) ≤ chamberI k T α ρ :=
  chamberA5_matching_three hα hρ hk 0 0 (Or.inl rfl)

/-- **Corollary 8.16.** The two-sided order of `J`, on `T ≥ 3`, with both constants depending
only on `(k, α, ρ)` — and with no integrality hypothesis on either `α` or `ρ`, which is the
point print makes twice. -/
example {k : ℕ} {α ρ : ℝ} (hα : -1 < α) (hρ : 0 < ρ) (hk : 0 < k) :
    ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ T : ℝ, 3 ≤ T →
      c * (T ^ (-chamberMinExponent k α ρ) * Real.log T ^ chamberResonanceCount k α ρ)
          ≤ chamberJFull k T α ρ ∧
        chamberJFull k T α ρ
          ≤ C * (T ^ (-chamberMinExponent k α ρ)
            * Real.log T ^ chamberResonanceCount k α ρ) :=
  chamberCor816 hα hρ hk

/-- **Corollary 8.16 at a half-integral `α` and a non-integral `ρ`**, the configuration
Proposition 8.17 actually uses: `α = -1/2` (the case `h = n`) and `ρ = 3/2`. The statement is
inhabited there, so the "no integrality is assumed" claim is not vacuous. -/
example : ∃ c C : ℝ, 0 < c ∧ c ≤ C ∧ ∀ T : ℝ, 3 ≤ T →
      c * (T ^ (-chamberMinExponent 2 (-1/2) (3/2))
            * Real.log T ^ chamberResonanceCount 2 (-1/2) (3/2))
          ≤ chamberJFull 2 T (-1/2) (3/2) ∧
        chamberJFull 2 T (-1/2) (3/2)
          ≤ C * (T ^ (-chamberMinExponent 2 (-1/2) (3/2))
            * Real.log T ^ chamberResonanceCount 2 (-1/2) (3/2)) :=
  chamberCor816 (by norm_num) (by norm_num) (by norm_num)

/-- At those parameters the exponent is `min(1/2, 3/2) + min(3/2, 3/2) = 2`, and the second
coordinate resonates — so print's `N⋆` is `2` and the logarithm is genuinely present. -/
example : chamberMinExponent 2 (-1/2 : ℝ) (3/2) = 2 := by
  rw [chamberMinExponent_eq_sum_min]
  norm_num [Fin.sum_univ_two]

example : chamberResonanceCount 2 (-1/2 : ℝ) (3/2) = 1 := by
  classical
  rw [chamberResonanceCount]
  rw [show (Finset.univ.filter fun i : Fin 2 => (-1/2 : ℝ) + (i : ℕ) + 1 = 3/2)
      = {(1 : Fin 2)} from ?_]
  · simp
  · ext i
    fin_cases i <;> norm_num



/-! ### The multiplicity

`N⋆` is the number of vertices attaining `E⋆`, and it exceeds the number of resonant coordinates
by exactly one. Since at most one coordinate can resonate, `N⋆ ∈ {1, 2}` — print's Proposition
8.18, without convexity. -/

/-- **`N⋆ = #{i : A_i = ρ} + 1`.** -/
example (k : ℕ) (α ρ : ℝ) :
    (chamberMinimizers k α ρ).card = chamberResonanceCount k α ρ + 1 :=
  chamberMinimizers_card k α ρ

/-- Hence `N⋆ ∈ {1, 2}`: at most one coordinate can resonate, because `A_i = α + i + 1` is
injective. -/
example (k : ℕ) (α ρ : ℝ) : (chamberMinimizers k α ρ).card ≤ 2 := by
  rw [chamberMinimizers_card]
  have := chamberResonanceCount_le_one k α ρ
  omega

/-- And it is at least `1`: the minimum is attained. -/
example (k : ℕ) (α ρ : ℝ) : 1 ≤ (chamberMinimizers k α ρ).card := by
  rw [chamberMinimizers_card]
  omega

/-- **Two minimizers are adjacent.** The increments of `E` rise by exactly one, so a minimum
cannot be attained twice with a gap. -/
example {k : ℕ} {α ρ : ℝ} {s s' : ℕ} (hs : s ∈ chamberMinimizers k α ρ)
    (hs' : s' ∈ chamberMinimizers k α ρ) (hlt : s < s') : s' = s + 1 :=
  chamberMinimizers_adjacent hs hs' hlt

/-- **A pair of minimizers is a resonance**, print's `a_{s+1} = 0`. -/
example {k : ℕ} {α ρ : ℝ} {s : ℕ} (hs : s ∈ chamberMinimizers k α ρ)
    (hs1 : s + 1 ∈ chamberMinimizers k α ρ) : α + (s : ℝ) + 1 = ρ :=
  resonance_of_two_minimizers hs hs1

/-- **The empty chamber**: at `k = 0` there is one vertex, `s = 0`, and no coordinate to
resonate, so `N⋆ = 1`. -/
example (α ρ : ℝ) : (chamberMinimizers 0 α ρ).card = 1 := by
  rw [chamberMinimizers_card, chamberResonanceCount]
  simp

end AISafetyAtlas.Examples.SingularLearning
