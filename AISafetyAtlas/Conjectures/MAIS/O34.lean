module

public import AISafetyAtlas.Conjectures.BinaryPair
public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Causal.EffectiveGenericity
public import AISafetyAtlas.Causal.ParameterChart
public import AISafetyAtlas.Causal.Query
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic
public import AISafetyAtlas.Conjectures.MAIS.Common

/-!
# MAIS-O34 — the two-variable starter problem

`prob:starter-set`(a): margin sufficiency, and the explicit singleton criterion
submitted in MAIS issue #4. Part (b) is not stated here or anywhere.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Defining a proposition asserts nothing about its truth; resolutions live in
`AISafetyAtlas/Examples/Conjectures/`.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.BinaryPair

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}

/-- A two-variable model carries at least one genuine graph edge. -/
@[expose] public def HasGraphEdge (M : Model (Fin 2) (binaryDim (Fin 2)) ℝ) : Prop :=
  ∃ child parent, parent ∈ M.parents child

/--
**MAIS-O34(a), negative-answer statement.**

Even after restricting to the two one-edge graph shapes of `M₂(λ)`, a
positive margin alone does not make the global behavioral fibre a singleton.

`prob:starter-set`(a) asks to decide *"when the global fiber `{M' : 𝚫_{M'} = 𝚫_M}`
is the singleton `{M}`; in particular … whether margin `λ > 0` alone suffices"*.
The negative branch needs the fibre to be **nonsingleton** — two distinct models,
nothing more. So the separation asked for here is `M ≠ M'`.

An earlier version asked for `M.parents ≠ M'.parents` instead. That was narrower
in a way easy to miss, because the statement carried no `M ≠ M'` clause at all and
the graph clause implied one: a same-orientation collision at equal graphs answers
print's question just as well and was excluded. `def:twovar`'s own restriction is
kept — both models carry an edge, which is the family `𝕄₂(λ)` — since that
restriction is print's and not the atlas's. The witness that discharges this does
carry different graphs, which is a fact about the witness and not a demand of the
statement.
-/
@[expose] public noncomputable def maisO34_marginAloneDoesNotIdentify : Prop :=
  ∃ (sk : Skeleton (Fin 2) (binaryDim (Fin 2)) Bool ℝ) (lam : ℝ),
    sk.observed = ∅ ∧ sk.utilityParents = Finset.univ ∧
      Skeleton.ValidMargin lam ∧
      ∃ M M' : Model (Fin 2) (binaryDim (Fin 2)) ℝ,
        sk.MarginClass M lam ∧ sk.MarginClass M' lam ∧
          HasGraphEdge M ∧ HasGraphEdge M' ∧
          M ≠ M' ∧ sk.BehaviorEq M M'

/-! ## MAIS-O34(a): complete real two-variable fibre candidate -/



/-- The same-orientation singleton criterion submitted in MAIS issue #4. -/
@[expose] public def O34SameDirectionSingletonCandidate (g : Fin 2 → Fin 2 → ℝ)
    (lam : ℝ) (M : PairModel) : Prop :=
  (∀ i, childDifference M.orientation g i ≠ 0) ∨
    ∃ z, childDifference M.orientation g z = 0 ∧
      childDifference M.orientation g (other z) ≠ 0 ∧
      separatedValues lam (M.child (other z)) = {M.child z}

/-- The issue's exact criterion for the existence of an opposite-orientation mate. -/
@[expose] public def O34HasOppositeDirectionMateCandidate (g : Fin 2 → Fin 2 → ℝ)
    (lam : ℝ) (M : PairModel) : Prop :=
  ExactlyOneFlat (childDifference M.orientation g) ∧
    ExactlyOneFlat (rootDifference M.orientation g) ∧
    (separatedValues lam M.root).Nonempty

/-- The complete global-singleton criterion proposed in MAIS issue #4. -/
@[expose] public def O34GlobalSingletonCandidate (g : Fin 2 → Fin 2 → ℝ)
    (lam : ℝ) (M : PairModel) : Prop :=
  O34SameDirectionSingletonCandidate g lam M ∧
    ¬ O34HasOppositeDirectionMateCandidate g lam M

/--
**MAIS-O34(a), complete candidate statement.**

On the real two-variable chart, the global transform fibre is a singleton
exactly under the explicit row/column and companion-set criterion submitted in
MAIS issue #4. Defining this proposition does not accept the pending solution.
-/
@[expose] public noncomputable def maisO34_exactFiberCandidate : Prop :=
  ∀ (g : Fin 2 → Fin 2 → ℝ) (lam : ℝ) (M : PairModel),
    ValidGap lam g → M.Valid lam →
      (HasSingletonFibre g lam M ↔ O34GlobalSingletonCandidate g lam M)

/-! ### Non-vacuity of the new statement domains -/

private noncomputable def o34StatementWitnessGap : Fin 2 → Fin 2 → ℝ :=
  fun x y ↦ if x = 0 then (if y = 0 then -2 / 5 else 1 / 5)
    else if y = 0 then 3 / 10 else -3 / 10

private noncomputable def o34StatementWitnessModel : PairModel where
  orientation := .forward
  root := 2 / 5
  child := fun x ↦ if x = 0 then 1 / 5 else 7 / 10

private example : ValidGap (1 / 10) o34StatementWitnessGap := by
  refine ⟨?_, ⟨0, 1, ?_⟩, ⟨0, 0, ?_⟩, ⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · intro x y
    fin_cases x <;> fin_cases y <;> norm_num [o34StatementWitnessGap]
  · norm_num [o34StatementWitnessGap]
  · norm_num [o34StatementWitnessGap]
  · norm_num [o34StatementWitnessGap]
  · norm_num [o34StatementWitnessGap]

private example : o34StatementWitnessModel.Valid (1 / 10) := by
  refine ⟨by norm_num, by norm_num, ?_, ?_, by norm_num [o34StatementWitnessModel]⟩
  · norm_num [InMarginInterval, o34StatementWitnessModel]
  · intro i
    fin_cases i <;> norm_num [InMarginInterval, o34StatementWitnessModel]


end AISafetyAtlas.Conjectures.MAIS
