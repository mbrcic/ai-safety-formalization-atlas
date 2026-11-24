import AISafetyAtlas.Sovereignty.ConcurrentGameFrame

/-!
Chen, Ju and Ågotnes (2026), arXiv:2607.10567v1, Definition 5, second bullet,
p. 8. At a state, a coalition's actual effectivity family consists of the
outcome sets of its available joint actions. The cited definition is `actualEff`.

The map keeps the state space and uses a single agent whose action type is
`Option (C → AC)`. Each joint action of the original coalition is represented
by the constant action with value `some σ`. The new grand coalition inherits
the availability and outcomes of those actions at every state.

Checked: `lake env lean docs/provenance/transfers/163-actual-effectivity.lean`
-/

namespace Transfer163

open AISafetyAtlas.Sovereignty

def PrintStatement {AG ST AC : Type*} [Finite AG] [Nonempty AG] [_states : Nonempty ST]
    [Nonempty AC] (F : ActionFrame AG ST AC) (C : Set AG) (s : ST) (A : Set ST) : Prop :=
  ∃ σ ∈ F.av C s, F.out C s σ = A

def LeanStatement {AG ST AC : Type*} (F : ActionFrame AG ST AC) (C : Set AG)
    (s : ST) (A : Set ST) : Prop :=
  A ∈ actualEff F C s

noncomputable def phi {AG ST AC : Type*} (F : ActionFrame AG ST AC) (C : Set AG) :
    ActionFrame Unit ST (Option (C → AC)) := by
  classical
  exact {
    av := fun D s ↦ (fun σ (_ : D) ↦ some σ) '' F.av C s
    out := fun D s τ ↦
      if h : () ∈ D then (τ ⟨(), h⟩).elim ∅ (F.out C s) else ∅ }

theorem defining_condition {AG ST AC : Type*} (F : ActionFrame AG ST AC)
    (C : Set AG) (s : ST) (A : Set ST) :
    LeanStatement F C s A ↔ PrintStatement (_states := ⟨s⟩) (phi F C) Set.univ s A := by
  constructor
  · rintro ⟨σ, hσ, hA⟩
    refine ⟨fun _ ↦ some σ, ⟨σ, hσ, rfl⟩, ?_⟩
    simpa [phi] using hA
  · rintro ⟨_, ⟨σ, hσ, rfl⟩, hA⟩
    exact ⟨σ, hσ, by simpa [phi] using hA⟩

theorem lean_of_print {AG ST AC : Type*} (F : ActionFrame AG ST AC)
    (C : Set AG) (s : ST) (A : Set ST) :
    PrintStatement (_states := ⟨s⟩) (phi F C) Set.univ s A → LeanStatement F C s A :=
  (defining_condition F C s A).mpr

theorem print_of_lean {AG ST AC : Type*} [Finite AG] [Nonempty AG] [Nonempty ST] [Nonempty AC]
    (F : ActionFrame AG ST AC) (C : Set AG) (s : ST) (A : Set ST) :
    LeanStatement F C s A → PrintStatement F C s A :=
  id

end Transfer163
