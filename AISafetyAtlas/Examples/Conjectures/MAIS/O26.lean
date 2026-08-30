module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import AISafetyAtlas.Examples.Causal.O24Refutation
public import AISafetyAtlas.Examples.Causal.OneNodeClass
public import AISafetyAtlas.Examples.Causal.Query
public import AISafetyAtlas.Examples.Conjectures.MAIS.Common
public import AISafetyAtlas.Examples.Conjectures.MAIS.Rates

/-!
# MAIS-O26's empty-class refutation route, and why it can never be run

Two results that pull in opposite directions.

The conditional theorem needs an `O24Solution` with an empty cut. It can never
be supplied: `Examples.Causal.O24Refutation.isEmpty_o24Solution` proves that
`prob:effective`'s conclusions (a) and (c) are incompatible, so no `O24Solution`
exists at all.

That settles `maisO26_exactRate`, and settles it the uninteresting way. The
closed statement opens `∀ sol : O24Solution`, so an empty domain makes it true
with nothing said about any rate. `maisO26_exactRate_holds` records that, and
records it as a **fact about `conj:exact` as printed**, not as evidence for the
`Θ(K log(1/ε))` budget the conjecture is about. A repaired MAIS-O26 would have
to be stated over a class that does not come from an O24 solution.

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


/-! ## The printed conjecture is vacuous

`conj:exact` is stated *"for `𝒩 = 𝕄(sk,λ,μ)`"*, print's own convention being to
fix one list supplied by a solution to `prob:effective`. There are none, so the
universal quantifier over solutions ranges over nothing. -/

/-- **MAIS-O26 as printed is true, vacuously.** Every `O24Solution` has the
stated rate because there are no `O24Solution`s. This is not evidence about the
minimax budget; it is a defect of the printed quantifier, inherited from
MAIS-O24 being unsatisfiable. -/
public theorem maisO26_exactRate_holds : maisO26_exactRate := by
  unfold maisO26_exactRate
  intro sol
  exact (AISafetyAtlas.Examples.Causal.O24Refutation.isEmpty_o24Solution.false sol).elim


end AISafetyAtlas.Examples.Conjectures.MAIS
