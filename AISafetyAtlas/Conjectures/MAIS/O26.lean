module

public import AISafetyAtlas.Conjectures.BinaryPair
public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Causal.EffectiveGenericity
public import AISafetyAtlas.Causal.ParameterChart
public import AISafetyAtlas.Causal.Query
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic
public import AISafetyAtlas.Conjectures.MAIS.Common
public import AISafetyAtlas.Conjectures.MAIS.Rates

/-!
# MAIS-O26 — the exact-query rate conjecture

`conj:exact`'s two-sided rate, plus the atlas-only well-posed variant that adds
the nonemptiness condition print does not state.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Defining a proposition asserts nothing about its truth; resolutions live in
`AISafetyAtlas/Examples/Conjectures/`.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.BinaryPair

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}

/-- **`conj:exact`'s class, and the hypotheses it inherits.**

`conj:exact` opens *"For `𝒩 = 𝕄(sk, λ, μ)` with `μ` fixed"*, which is
`prob:effective`'s cut — the margin class intersected with `|Q^G_j(θ,u)| ≥ μ` for
a solution's own polynomial list. `O24Solution.marginClass` is that set, so the
class is not supplied here: it is determined by a solution, a skeleton and the
two margins.

That is what removes the antecedents an arbitrary cut needed. Conclusion (a) —
behaviour identifies a model inside the class — is `O24Solution.identifies`, a
field of the bundle rather than an assumption, and the degeneracies a free
witness could produce (a cut that excludes nothing, a `μ` the class ignores)
cannot arise, since a solution's list must satisfy (c).

The remaining recovery hypothesis is the one `conj:exact` names through `L`: the
class satisfies conclusion (b) with modulus `ω(δ) = Lδ`. Compact
semialgebraicity and `prob:exact`'s richness condition are **not** carried into
this statement because O26 does not state them; in particular its constant bound
contains no `ρ`. Both remain on `ExactClassAssumptions`, where O25 prints them.

`IsClassChartDim` binds `K` to `def:margin`'s maximum over the margin class.
Without it `K` is a free number reaching the statement only through the rate, and
`K = 0` against `K = 1` refutes the conjecture by substitution alone. -/
public noncomputable def O26ClassAssumptions {m : ℕ} (sol : O24Solution)
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (lam mu : ℝ) (K : ℕ) (L δmax : ℝ) : Prop :=
  Skeleton.ValidMargin lam ∧ Skeleton.ValidMargin mu ∧ 0 < L ∧
    IsClassChartDim sk lam K ∧
    HasLinearRecoveryModulus sk (sol.marginClass sk lam mu) lam L δmax

/-- A solution to O24 supplies the recovery constants required by O26 whenever
the margins and the printed chart maximum are valid.

The coefficient is enlarged to at least one only to satisfy O26's explicit
positivity requirement on `L`; `O24Solution.recovery` supplies the sharper
coefficient. This theorem does not construct an `O24Solution` or a chart-maximum
witness, so it closes the recovery-compatibility gap without claiming that the
closed O26 proposition is inhabited. -/
public theorem O24Solution.exists_o26ClassAssumptions {m : ℕ} (sol : O24Solution)
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (lam mu : ℝ) (K : ℕ)
    (hlam : Skeleton.ValidMargin lam) (hmu : Skeleton.ValidMargin mu)
    (hK : IsClassChartDim sk lam K) :
    ∃ L δmax : ℝ, O26ClassAssumptions sol sk lam mu K L δmax := by
  let coeff : ℝ :=
    ((K : ℝ) / (lam * mu)) ^
      (sol.constants.a (m + 1) (o24ClassSize sk.utilityParents K))
  let L : ℝ := max coeff 1
  let δmax : ℝ := (sol.thresholds (m + 1)).bound sk lam mu
  refine ⟨L, δmax, hlam, hmu, ?_, hK, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right coeff 1)
  · refine ⟨(sol.thresholds (m + 1)).bound_pos sk lam mu, ?_⟩
    intro δ hδ hδmax M hM M' hidentified
    have hrec :=
      sol.recovery (m + 1) inferInstance sk lam mu hlam hmu K hK δ hδ hδmax
        M hM M' hidentified
    have hcoeff :
        ((K : ℝ) / (lam * mu)) ^
            (sol.constants.a (Fintype.card (Fin (m + 1)))
              (o24ClassSize sk.utilityParents K)) ≤ L := by
      simp [coeff, L]
    exact hrec.trans (mul_le_mul_of_nonneg_right hcoeff hδ)

/--
**MAIS-O26, statement only.**

All side conditions occur to the left of an implication, so universally
quantified invalid margins do not make the proposition false and arbitrary model
classes are not silently claimed to satisfy the rate.

**The class is print's.** `conj:exact` is stated over `𝕄(sk, λ, μ)`, cut by
MAIS-O24's *specific* polynomial list. Cutting instead by an arbitrary supplied
genericity witness admits classes print does not reach, and a rational stand-in
query layer whose analyst was deterministic where `subsec:queries` takes an
infimum over **randomized** strategies. Both are gone: the class is
`O24Solution.marginClass` and `N(ε)` is `Causal.exactMinimalBudget`, the same
`ℕ∞`-valued infimum MAIS-O25 uses.

Two atlas sharpenings went with them. The properness and tightness clauses
were antecedents *stronger* than print's, added because an
arbitrary witness could cut nothing or could decouple `μ` from the class. A
solution's list can do neither, so print needs no such clause and neither does
this.

**Print's sentence continues after a colon, and this transcribes the half before
it.** `conj:exact` reads *"… independent of `m` otherwise: bisection along the
segments of `prop:equiv` achieves the information-theoretic floor of
`rem:packing` up to constants."* The `Prop` above is the rate clause. The colon
clause is a claim about a **mechanism**: `rem:packing` supplies the lower bound
`N = Ω(K(G) log(1/ε))` by a packing-plus-Fano argument, and bisection along
`prop:equiv`'s segments is asserted to attain it from above, which together
would *give* the `Θ`.

Read as a gloss it says how print expects the rate to be proved, and the
transcription loses nothing. Read as a conjunct it is a second assertion — that
this particular algorithm is optimal up to constants — and then the `Prop` is
**narrower than the printed sentence**, because a proof of the rate need not
proceed by bisection. The atlas takes the gloss reading, on the grounds that the
colon introduces a mechanism rather than a second demand and that a conjecture
environment states one thing; this paragraph records that
choice rather than leaving it to be inferred from the `Prop`.

Closing it the other way is costed rather than hard: it needs bisection as a
query strategy over `Causal.ShiftedQuery` and `rem:packing`'s floor as a theorem,
neither of which exists here. `rem:packing` also reaches past this row — its
corrupted-channel variant divides by `1 - H(ζ)` and belongs to `prob:noisy`.

**Quantifying over solutions is print's own convention**, not a widening:
`prob:effective` closes by fixing one solution's list and reading every later
`𝕄(sk,λ,μ)` against it, and nothing distinguishes one solution's list from
another's.

`Fin (m + 1)` ranges over the nonempty chance sets `𝐂 = {C₁, …, C_m}` as `m`
ranges over `ℕ` — the `+1` is what forces `𝐂` nonempty, not a count of print's
variables, and it indexes O23 and O29(a) the same way. `O24Solution`'s lists are
indexed the same way, so no transport is owed.

**The estimator's output law is not a widening**, and this is the one axis this
statement shares with MAIS-O25 rather than owning. `Causal.RandomizedEstimator`
returns a `PMF`, hence a countably supported law, where `subsec:queries`
constrains the analyst's output not at all and the model space is uncountable.
Restricting the output laws shrinks the set the infimum ranges over, so
`exactMinimalBudget` could only rise and a finite two-sided rate on it would be
**stronger** than print's. It does not rise:
`Causal.measureMinimalBudget_eq_exactMinimalBudget` proves `N(ε)` is the same
number either way, and `Examples.Conjectures.MAIS.o26_minimalBudget_eq_measure`
instantiates that at this `Prop`'s own quantifier rather than leaving it as a
claim about typeclass resolution. The argument itself is written out at
`maisO25_exactQueryRate`, which owns it.
-/
@[expose] public noncomputable def maisO26_exactRate_for {m : ℕ} (sol : O24Solution)
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (K : ℕ) (lam mu L δmax A : ℝ) (d : ℕ) : Prop :=
  O26ClassAssumptions sol sk lam mu K L δmax →
    IsThetaWithMarginBound
      (fun ε ↦ exactMinimalBudget sk (sol.marginClass sk lam mu) ε)
      (fun ε ↦ (K : ℝ) * Real.log (1 / ε))
      lam mu L A d

/-- Closed O26 proposition recorded in the conjecture ledger.

`A` and `d` are chosen **before the diagram and after the solution**, and both
halves of that are print's.

*Before the diagram* is `conj:exact`'s *"independent of `m` otherwise"*: one
polynomial in `(1/λ, 1/μ, L)` for every skeleton, not one per instance.

*After the solution* is `prob:effective`'s closing convention, *"Fix one list
supplied by a solution; every occurrence of `𝕄(sk,λ,μ)` below refers to that
list"*. Print states `conj:exact` about that one fixed list, so its constants may
depend on it; `conj:exact` says the constants are independent of `m`, and says
nothing about independence of the list. **Until 2026-08-21 the `∃ A, ∃ d` sat
outside `∀ sol`**, demanding one pair of constants uniform over every solution.
That is strictly stronger than print, so the row was `Wider` on an axis nothing
recorded. Moving the existentials inside `∀ sol` is what print asks for. -/
public noncomputable def maisO26_exactRate : Prop :=
  ∀ sol : O24Solution, ∃ A : ℝ, ∃ d : ℕ, 0 ≤ A ∧
    ∀ (m : ℕ)
      (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ) (K : ℕ)
      (lam mu L δmax : ℝ),
      maisO26_exactRate_for sol sk K lam mu L δmax A d

/-! ### The well-posed variant, which is the atlas's question and not print's -/

/-- `O26ClassAssumptions` together with the class being **nonempty**.

`conj:exact` states no such condition. It is added here rather than to
`O26ClassAssumptions` because the two are different questions:
`maisO26_exactRate` is print's, at print's quantifiers, and this one is an
unregistered atlas variant.

**Why the distinction is not pedantry.** The conditional empty-class route is
machine-checked by
`Examples.Conjectures.MAIS.not_maisO26_exactRate_for_of_empty`: at positive
chart dimension the actual randomized minimax budget is zero and cannot satisfy
the lower half of the printed rate. What is not available is an `O24Solution`
whose cut realizes that antecedent. No such solution is exhibited in this tree,
so `maisO26_exactRate` may instead be vacuously true. The theorem certifies the
route; it does not supply the missing instance. -/
@[expose] public noncomputable def O26ClassAssumptionsWellPosed {m : ℕ}
    (sol : O24Solution)
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (lam mu : ℝ) (K : ℕ) (L δmax : ℝ) : Prop :=
  O26ClassAssumptions sol sk lam mu K L δmax ∧
    (sol.marginClass sk lam mu).Nonempty

/-- The well-posed antecedent implies the printed one, by projection.

**Implication only.** This does not show the inclusion is *strict*: strictness
needs an instance satisfying `O26ClassAssumptions` and failing
`O26ClassAssumptionsWellPosed`, hence an `O24Solution` with an empty cut, and no
`O24Solution` is exhibited. Whether this variant really asks about fewer
instances is therefore open, not established. -/
public theorem o26ClassAssumptions_of_wellPosed {m : ℕ} {sol : O24Solution}
    {sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ}
    {lam mu : ℝ} {K : ℕ} {L δmax : ℝ}
    (h : O26ClassAssumptionsWellPosed sol sk lam mu K L δmax) :
    O26ClassAssumptions sol sk lam mu K L δmax := h.1

/-- One instance of the well-posed rate question. -/
@[expose] public noncomputable def maisO26_exactRateWellPosed_for {m : ℕ}
    (sol : O24Solution)
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (K : ℕ) (lam mu L δmax A : ℝ) (d : ℕ) : Prop :=
  O26ClassAssumptionsWellPosed sol sk lam mu K L δmax →
    IsThetaWithMarginBound
      (fun ε ↦ exactMinimalBudget sk (sol.marginClass sk lam mu) ε)
      (fun ε ↦ (K : ℝ) * Real.log (1 / ε))
      lam mu L A d

/-- **The atlas's well-posed reading of MAIS-O26.**

Print's `conj:exact` with one hypothesis added: the class is nonempty. This is
**not** MAIS-O26 and is not graded against it; `maisO26_exactRate` is. It is
recorded because deleting the empty-class refutation from print's statement
leaves a question that is still open and still the interesting one -- whether the
`Θ(K log(1/ε))` rate holds where the rate has content.

This closed proposition still starts with `∀ sol : O24Solution`. No such solution
is exhibited in this tree, so adding nonemptiness to the per-instance antecedent
does not make the closed proposition inhabited: it may be vacuously true for the
same missing-solution reason as `maisO26_exactRate`. -/
public noncomputable def maisO26_exactRateWellPosed : Prop :=
  ∀ sol : O24Solution, ∃ A : ℝ, ∃ d : ℕ, 0 ≤ A ∧
    ∀ (m : ℕ)
      (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ) (K : ℕ)
      (lam mu L δmax : ℝ),
      maisO26_exactRateWellPosed_for sol sk K lam mu L δmax A d


end AISafetyAtlas.Conjectures.MAIS
