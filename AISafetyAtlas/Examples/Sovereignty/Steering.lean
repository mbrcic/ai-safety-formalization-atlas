module

public import AISafetyAtlas.Sovereignty.Steering
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.SplitIfs
public import Mathlib.Tactic.IntervalCases

/-!
# A three-step steer: memory, compass, engine

One principal (`false`) and one assistant (`true`). Outcomes `{0, 1, 2}`:
`0` is the original goal, `1` a substitute that comes to feel acceptable, `2`
a disaster the assistant will not name.

* **Memory.** The mandate coarsens from `{0}` to `{0, 1}`. The game is
  unchanged. The principal can still force both families.
* **Compass.** Picking `0` is silently read as `1` — the original option is
  still on the button, and it no longer means what it did.
* **Engine.** The assistant names the outcome, and maps disaster to the
  substitute. Every play lands in `{0, 1}`, so the *current* mandate is kept;
  `{0}` is not.

Each adjacent step retains `{0, 1}`. The composition does not retain `{0}`.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-- The principal names the outcome. -/
@[expose, reducible] public def baseline : GameForm.{0, 0, 0} Bool (Fin 3) where
  strategy _ := Fin 3
  outcome s := s false

/-- Compass: the original option is reframed as the substitute. -/
@[expose, reducible] public def reframed : GameForm.{0, 0, 0} Bool (Fin 3) where
  strategy _ := Fin 3
  outcome s := if s false = 0 then 1 else s false

/-- Engine: the assistant names the outcome, and will not play disaster. -/
@[expose, reducible] public def executed : GameForm.{0, 0, 0} Bool (Fin 3) where
  strategy _ := Fin 3
  outcome s := if s true = 2 then 1 else s true

/-- Original mandate: the singleton of the original goal. -/
@[expose] public def original : Set (Set (Fin 3)) := {{0}}

/-- Coarsened mandate, after memory has made the substitute feel acceptable. -/
@[expose] public def coarsened : Set (Set (Fin 3)) := {{0, 1}}

/-! ## What each game can force -/

public theorem baseline_forces_original :
    Forces baseline {false} ({0} : Set (Fin 3)) := by decide

public theorem baseline_forces_coarsened :
    Forces baseline {false} ({0, 1} : Set (Fin 3)) :=
  (baseline_forces_original).mono (by intro x hx; simp at hx; simp [hx])

public theorem reframed_forces_coarsened :
    Forces reframed {false} ({0, 1} : Set (Fin 3)) := by decide

public theorem executed_forces_coarsened :
    Forces executed {false} ({0, 1} : Set (Fin 3)) := by decide

public theorem executed_not_forces_original :
    ¬ Forces executed {false} ({0} : Set (Fin 3)) := by decide

/-! ## The path -/

/-- Memory, then Compass, then Engine. -/
@[expose] public def steer : SteeringPath.{0, 0, 0} Bool (Fin 3) 3 where
  G := ![baseline, baseline, reframed, executed]
  mandate := ![original, coarsened, coarsened, coarsened]
  C := {false}
  kind := ![.memory, .compass, .engine]
  coarsens := by
    intro i A hA
    fin_cases i
    · refine ⟨{0, 1}, rfl, ?_⟩
      have : A = ({0} : Set (Fin 3)) := hA
      subst this; intro x hx; simp at hx; simp [hx]
    · exact ⟨A, hA, le_rfl⟩
    · exact ⟨A, hA, le_rfl⟩
  memory_keeps_game := by
    intro i hi
    fin_cases i
    · rfl
    · exact absurd hi (by simp)
    · exact absurd hi (by simp)
  game_keeps_mandate := by
    intro i hi
    fin_cases i
    · exact absurd rfl hi
    · rfl
    · rfl

public theorem steer_step0 :
    steer.StepSafe 0 := by
  intro A hA hA0
  have : A = ({0, 1} : Set (Fin 3)) := hA
  subst this
  exact baseline_forces_coarsened

public theorem steer_step1 :
    steer.StepSafe 1 := by
  intro A hA hA0
  have : A = ({0, 1} : Set (Fin 3)) := hA
  subst this
  exact reframed_forces_coarsened

public theorem steer_step2 :
    steer.StepSafe 2 := by
  intro A hA hA0
  have : A = ({0, 1} : Set (Fin 3)) := hA
  subst this
  exact executed_forces_coarsened

public theorem steer_adjacentSafe : steer.AdjacentSafe := by
  intro i
  fin_cases i
  · exact steer_step0
  · exact steer_step1
  · exact steer_step2

public theorem steer_originalLost : steer.OriginalLost := by
  intro h
  have : ({0} : Set (Fin 3)) ∈ effectivity executed {false} :=
    h {0} rfl baseline_forces_original
  exact executed_not_forces_original this

/--
**Steering is inhabited.** Three adjacent steps, each retaining the current
mandate; the original singleton is gone at the end. Memory coarsened the
family, Compass reframed the original option, Engine handed naming to the
assistant. No single step is a loss against `{0, 1}`. The composition is a
loss against `{0}`.
-/
public theorem steer_isSteering : steer.IsSteering :=
  ⟨steer_adjacentSafe, steer_originalLost⟩

/-- And this is not a failure of transitivity at a fixed family: on the
coarsened mandate the whole path *does* retain. The original family is the
one that moved. -/
public theorem steer_retains_coarsened :
    RetainsFamily baseline executed {false} {false} coarsened := by
  intro A hA hA0
  have : A = ({0, 1} : Set (Fin 3)) := hA
  subst this
  exact executed_forces_coarsened

end AISafetyAtlas.Examples.Sovereignty
