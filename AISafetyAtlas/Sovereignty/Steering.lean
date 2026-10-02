module

public import AISafetyAtlas.Sovereignty.Mandate
public import Mathlib.Data.Fin.Basic

/-!
# Gradual steering, and why stepwise retention is not authorship

Cognitive sovereignty in the unpublished organizational cut (HEC2026) is the
capacity to remain the author of memory, goals, judgment and action under AI
mediation. The five verbs and the Memory–Compass–Engine anatomy are
**atlas-side interpretation**; nothing here is graded against a printed
theorem. What is graded is one implication SOV-1 does not give:

> A path of games can retain the *current* mandate at every step and still
> lose the *original* mandate.

`RetainsFamily.trans` says retention is transitive at a **fixed** family.
Steering is the case where the family moves — memory coarsens what the
principal treats as acceptable — and Compass and Engine then change the game
under that coarser family. Each adjacent step looks safe. The composition is
not.

The three kinds of step, matching the keynote's three seams:

* **Memory** — the mandate family coarsens; the game does not.
* **Compass** — the outcome map reframes the original option as the substitute.
* **Engine** — the assistant names the outcome, mapped away from disaster.

Worked path: `AISafetyAtlas.Examples.Sovereignty.Steering`.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

/-- The three seams authorship can leak at. A Memory step moves the mandate
family; Compass and Engine move the game. -/
public inductive StepKind
  | memory
  | compass
  | engine

/--
**A steering path.** Games `G 0, …, G n` and mandate families `𝒜 0, …, 𝒜 n`,
with a kind for each adjacent step.

`n` is the number of *steps*, so there are `n + 1` games. The principal's
coalition is `C` throughout: this is the gradual-steering reading of SOV-1,
not a change of who occupies the slot.
-/
public structure SteeringPath (N : Type u) (X : Type v) (n : ℕ) where
  /-- The game after `i` steps. -/
  G : Fin (n + 1) → GameForm.{u, v, w} N X
  /-- The mandate family the principal currently treats as its own, after `i`
  steps. Memory steps move this; Compass and Engine need not. -/
  mandate : Fin (n + 1) → Set (Set X)
  /-- The principal's coalition, fixed along the path. -/
  C : Set N
  /-- Kind of the step from `i` to `i + 1`. -/
  kind : Fin n → StepKind

namespace SteeringPath

variable {N : Type u} {X : Type v} {n : ℕ} (P : SteeringPath.{u, v, w} N X n)

/-- The step from `i` to `i + 1` retains the **later** mandate. That is what
"looks safe" means: against what the principal now treats as its mandate, every
guarantee it had, it still has. -/
@[expose] public def StepSafe (i : Fin n) : Prop :=
  RetainsFamily (P.G i.castSucc) (P.G i.succ) P.C P.C (P.mandate i.succ)

/-- Every adjacent step looks safe. -/
@[expose] public def AdjacentSafe : Prop :=
  ∀ i : Fin n, P.StepSafe i

/-- The original mandate is not retained at the end of the path. -/
@[expose] public def OriginalLost : Prop :=
  ¬ RetainsFamily (P.G 0) (P.G (Fin.last n)) P.C P.C (P.mandate 0)

/--
**Steering.** Adjacent steps all look safe, and the original mandate is gone.

This is the theorem-shaped cut of "little by little": no single step is a
visible loss against the current mandate, and authorship of the original
mandate is not retained.
-/
@[expose] public def IsSteering : Prop :=
  P.AdjacentSafe ∧ P.OriginalLost

end SteeringPath

end AISafetyAtlas.Sovereignty
