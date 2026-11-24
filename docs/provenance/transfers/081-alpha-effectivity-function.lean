import AISafetyAtlas.Sovereignty.ConcurrentGameFrame

/-!
Chen, Ju and Ågotnes (2026), arXiv:2607.10567v1, Definition 5, first bullet,
p. 8. At a state, a coalition's alpha effectivity family consists of the sets
that contain the outcome set of some available joint action of the coalition.
The cited definitions are `alphaEff`, `AlphaPower` and `SafeFor`.

The map keeps the state space and uses a single agent whose action type is
`Option (C → AC)`, which is nonempty through `none`. Each joint action of the
original coalition is represented by the constant action with value `some σ`.
The new grand coalition inherits the availability and outcomes of those
actions at every state; `none` is never available. The printed frame's state
set is nonempty because the evaluated state inhabits it.

Checked: `lake env lean docs/provenance/transfers/081-alpha-effectivity-function.lean`
-/

namespace Transfer081

open AISafetyAtlas.Sovereignty

def PrintStatement {AG ST AC : Type*} [Finite AG] [Nonempty AG] [_states : Nonempty ST]
    [Nonempty AC] (F : ActionFrame AG ST AC) (C : Set AG) (s : ST) (Y : Set ST) : Prop :=
  ∃ σ ∈ F.av C s, F.out C s σ ⊆ Y

def LeanStatement {AG ST AC : Type*} (F : ActionFrame AG ST AC) (C : Set AG)
    (s : ST) (Y : Set ST) : Prop :=
  Y ∈ alphaEff F C s

noncomputable def phi {AG ST AC : Type*} (F : ActionFrame AG ST AC) (C : Set AG) :
    ActionFrame Unit ST (Option (C → AC)) := by
  classical
  exact {
    av := fun D s ↦ (fun σ (_ : D) ↦ some σ) '' F.av C s
    out := fun D s τ ↦
      if h : () ∈ D then (τ ⟨(), h⟩).elim ∅ (F.out C s) else ∅ }

theorem defining_condition {AG ST AC : Type*} (F : ActionFrame AG ST AC)
    (C : Set AG) (s : ST) (Y : Set ST) :
    LeanStatement F C s Y ↔ PrintStatement (_states := ⟨s⟩) (phi F C) Set.univ s Y := by
  constructor
  · rintro ⟨σ, hσ, hY⟩
    refine ⟨fun _ ↦ some σ, ⟨σ, hσ, rfl⟩, ?_⟩
    simpa [phi, SafeFor] using hY
  · rintro ⟨_, ⟨σ, hσ, rfl⟩, hY⟩
    exact ⟨σ, hσ, by simpa [phi, SafeFor] using hY⟩

theorem lean_of_print {AG ST AC : Type*} (F : ActionFrame AG ST AC)
    (C : Set AG) (s : ST) (Y : Set ST) :
    PrintStatement (_states := ⟨s⟩) (phi F C) Set.univ s Y → LeanStatement F C s Y :=
  (defining_condition F C s Y).mpr

theorem print_of_lean {AG ST AC : Type*} [Finite AG] [Nonempty AG] [Nonempty ST] [Nonempty AC]
    (F : ActionFrame AG ST AC) (C : Set AG) (s : ST) (Y : Set ST) :
    LeanStatement F C s Y → PrintStatement F C s Y :=
  id

end Transfer081
