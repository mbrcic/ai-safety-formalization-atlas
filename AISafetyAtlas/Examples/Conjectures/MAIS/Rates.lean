module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import AISafetyAtlas.Examples.Causal.OneNodeClass
public import AISafetyAtlas.Examples.Causal.Query
public import AISafetyAtlas.Examples.Conjectures.MAIS.Common
public import Mathlib.Analysis.Asymptotics.Theta
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# `⊤` refutes the budget bounds

An infeasible target must break a finite bound rather than satisfy one. These
are the discipline checks for the rate predicates shared by O25 and O26.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ## `⊤` refutes the budget bound

MAIS-O25 and MAIS-O26 are both stated over `Causal.exactMinimalBudget`, which is
`ℕ∞`-valued and returns `⊤` when no budget drives the minimax risk to `ε`. The
whole point of that codomain is that an infeasible target must **refute** a bound
rather than satisfy one. `IsPolyLogBudget`, `NonadaptiveWithinConstant` and
`IsThetaWithMarginBound` were all restated to make that so, and the checks below
are what a `ℕ`-valued budget with an `else 0` fallback would have got wrong:
there, `N(ε) = 0` and every upper bound holds vacuously on exactly the instances
print answers *no* for. -/

/-- A budget that is `⊤` on **every** target refutes every polynomial-log bound,
whatever the constants.

A class on which no finite budget ever achieves any positive target is exactly
the situation print's `N(ε)` does not exist on. The hypothesis is stated at every
positive `ε` rather than at one, which is what it was already doing when
`IsPolyLogBudget` carried an `ε₀` a witness could choose; the predicate now
quantifies over all of `(0,1)` and any single infeasible target in that range
refutes it. -/
public theorem not_isPolyLogBudget_of_top {f : ℝ → ℕ∞}
    (htop : ∀ ε : ℝ, 0 < ε → f ε = ⊤)
    (K : ℕ) (lam L rho A : ℝ) (d : ℕ) :
    ¬ IsPolyLogBudget f K lam L rho A d := by
  intro hbound
  obtain ⟨n, hn, -⟩ := hbound (1 / 2) (by norm_num) (by norm_num)
  rw [htop (1 / 2) (by norm_num)] at hn
  exact (ENat.top_ne_coe n) hn

/-- If adaptivity buys feasibility outright — a finite budget where the
non-adaptive analyst has none — then it has beaten non-adaptive queries by more
than any constant factor, which is the branch `prob:exact` asks to decide
against. -/
public theorem not_nonadaptiveWithinConstant_of_top {c : ℝ} {adaptive nonadaptive : ℝ → ℕ∞}
    (h : ∀ ε : ℝ, 0 < ε → ε < 1 → (∃ a : ℕ, adaptive ε = (a : ℕ∞)) ∧ nonadaptive ε = ⊤) :
    ¬ NonadaptiveWithinConstant c adaptive nonadaptive := by
  intro hbound
  obtain ⟨⟨a, ha⟩, htop⟩ := h (1 / 2) (by norm_num) (by norm_num)
  obtain ⟨b, hb, -⟩ := hbound (1 / 2) (by norm_num) (by norm_num) a ha
  rw [htop] at hb
  exact (ENat.top_ne_coe b) hb

/-- The same discipline on MAIS-O26's two-sided rate. A `Θ` claim is an upper
bound too, so a budget that is `⊤` at arbitrarily small targets must refute it.
Under the deleted `ℕ`-valued stand-in this was the reverse: that budget
returned `0` where none was feasible, and `0` sits *below* every rate, so
the lower half of the `Θ` — not the upper — was what an infeasible class broke,
at the one place print says the quantity does not exist. -/
public theorem not_isThetaWithMarginBound_of_top {f : ℝ → ℕ∞} {g : ℝ → ℝ}
    (htop : ∀ ε : ℝ, 0 < ε → f ε = ⊤) (lam mu L A : ℝ) (d : ℕ) :
    ¬ IsThetaWithMarginBound f g lam mu L A d := by
  rintro ⟨c₁, c₂, ε₀, -, -, hε₀, -, -, hbound⟩
  have hhalf : (0 : ℝ) < ε₀ / 2 := by linarith
  obtain ⟨n, hn, -, -⟩ := hbound (ε₀ / 2) hhalf (by linarith)
  rw [htop (ε₀ / 2) hhalf] at hn
  exact (ENat.top_ne_coe n) hn

/-! ## The rate predicate really is a `Θ`

`IsThetaWithMarginBound` is not Mathlib's `IsTheta`, and the reason is the
polynomial-constant clause: `conj:exact` demands the implied constants be
bounded by `A · (1 + 1/λ + 1/μ + L)^d`, and `Asymptotics.IsTheta` quantifies its
constants existentially with nothing said about their size. So the atlas
predicate cannot be replaced by the library one.

What can be checked is that it *implies* it, which is what the theorem below
does — and that direction is the whole of the claim. -/

open Filter Topology Asymptotics in
/-- The margin-bounded rate predicate implies Mathlib's two-sided `Θ` on the
punctured right neighbourhood of `0`, so `conj:exact`'s
*"`N(ε) = Θ(K log(1/ε))` as `ε → 0`"* is being asserted in the library's own
sense and not merely in a lookalike of it.

**This bridge is one-directional and must stay read that way.**
`Asymptotics.IsTheta` cannot express *"with the implied constants polynomial in
`1/λ`, `1/μ` and `L`"*, so the converse is false as a matter of expressiveness
rather than of missing proof: a budget can be `Θ(g)` with constants that blow up
as the margins shrink, and `conj:exact` denies exactly that. Reading this
implication as an equivalence would silently delete the printed clause the
predicate exists to carry.

Nonnegativity of `g` is not assumed: `0 ≤ n ≤ c₂ · g ε` with `0 < c₂` supplies
it on the interval where the bound bites, which is why both norms collapse. -/
public theorem isTheta_of_isThetaWithMarginBound {f : ℝ → ℕ∞} {g : ℝ → ℝ}
    {lam mu L A : ℝ} {d : ℕ} (h : IsThetaWithMarginBound f g lam mu L A d) :
    (fun ε => ((f ε).toNat : ℝ)) =Θ[𝓝[>] (0 : ℝ)] g := by
  obtain ⟨c₁, c₂, ε₀, hc₁, hc₂, hε₀, -, -, hb⟩ := h
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε < ε₀ := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hε₀)] with ε h1 h2
    exact ⟨h1, h2⟩
  constructor
  · rw [isBigO_iff]
    refine ⟨c₂, ?_⟩
    filter_upwards [hev] with ε hε
    obtain ⟨n, hn, hlo, hhi⟩ := hb ε hε.1 hε.2
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hg0 : 0 ≤ g ε := nonneg_of_mul_nonneg_right (le_trans hn0 hhi) hc₂
    have : ((f ε).toNat : ℝ) = (n : ℝ) := by rw [hn]; simp
    rw [this, Real.norm_of_nonneg hn0, Real.norm_of_nonneg hg0]
    exact hhi
  · rw [isBigO_iff]
    refine ⟨c₁⁻¹, ?_⟩
    filter_upwards [hev] with ε hε
    obtain ⟨n, hn, hlo, hhi⟩ := hb ε hε.1 hε.2
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hg0 : 0 ≤ g ε := nonneg_of_mul_nonneg_right (le_trans hn0 hhi) hc₂
    have : ((f ε).toNat : ℝ) = (n : ℝ) := by rw [hn]; simp
    rw [this, Real.norm_of_nonneg hn0, Real.norm_of_nonneg hg0]
    rw [inv_mul_eq_div, le_div_iff₀ hc₁]
    linarith [hlo]


end AISafetyAtlas.Examples.Conjectures.MAIS
