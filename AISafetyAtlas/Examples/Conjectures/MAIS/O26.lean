module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import AISafetyAtlas.Examples.Causal.OneNodeClass
public import AISafetyAtlas.Examples.Causal.Query
public import AISafetyAtlas.Examples.Conjectures.MAIS.Common
public import AISafetyAtlas.Examples.Conjectures.MAIS.Rates

/-!
# MAIS-O26's empty-class refutation route

A conditional theorem, not a refutation: it needs an `O24Solution` with an empty
cut, none is exhibited in this tree, and until one is the closed `∀ sol`
statement may be vacuously true rather than false.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ## The empty-class refutation route for MAIS-O26 -/

/-- An empty class with positive chart dimension cannot satisfy MAIS-O26's
two-sided rate, for any proposed polynomial constants. -/
public theorem not_isThetaWithMarginBound_emptyClass {m K : ℕ} (hK : 0 < K)
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (lam mu L A : ℝ) (d : ℕ) :
    ¬ IsThetaWithMarginBound
      (fun ε ↦ exactMinimalBudget sk
        (∅ : Set (Model (Fin (m + 1)) (binaryDim (Fin (m + 1))) ℝ)) ε)
      (fun ε ↦ (K : ℝ) * Real.log (1 / ε)) lam mu L A d := by
  rintro ⟨c₁, c₂, ε₀, hc₁, -, hε₀, -, -, hbound⟩
  let ε : ℝ := min (ε₀ / 2) (1 / 2)
  have hε : 0 < ε := by
    dsimp [ε]
    exact lt_min (by linarith) (by norm_num)
  have hε1 : ε < 1 := (min_le_right _ _).trans_lt (by norm_num)
  have hεε₀ : ε < ε₀ := (min_le_left _ _).trans_lt (by linarith)
  obtain ⟨n, hn, hlo, -⟩ := hbound ε hε hεε₀
  change exactMinimalBudget sk ∅ ε = (n : ℕ∞) at hn
  rw [AISafetyAtlas.Examples.Causal.Query.exactMinimalBudget_emptyClass sk ε hε.le] at hn
  have hn0 : n = 0 := by simpa using hn.symm
  subst n
  simp only [Nat.cast_zero] at hlo
  change c₁ * ((K : ℝ) * Real.log (1 / ε)) ≤ 0 at hlo
  have hrecip : 1 < 1 / ε := (lt_div_iff₀ hε).2 (by simpa using hε1)
  have hlog : 0 < Real.log (1 / ε) := Real.log_pos hrecip
  have hKreal : (0 : ℝ) < K := by exact_mod_cast hK
  exact (not_lt_of_ge hlo) (mul_pos hc₁ (mul_pos hKreal hlog))

/-- The ledger's proposed O26 counterexample route, as one conditional theorem:
if an O24 solution has an empty cut at positive chart dimension and the printed
antecedent holds, then that instance of the printed rate conjecture is false. -/
public theorem not_maisO26_exactRate_for_of_empty {m K : ℕ} (hK : 0 < K)
    (sol : O24Solution)
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (lam mu L δmax A : ℝ) (d : ℕ)
    (hclass : sol.marginClass sk lam mu = ∅)
    (hassumptions : O26ClassAssumptions sol sk lam mu K L δmax) :
    ¬ maisO26_exactRate_for sol sk K lam mu L δmax A d := by
  intro hrate
  have htheta := hrate hassumptions
  rw [hclass] at htheta
  exact not_isThetaWithMarginBound_emptyClass hK sk lam mu L A d htheta


end AISafetyAtlas.Examples.Conjectures.MAIS
