import AISafetyAtlas.Sovereignty.Independence

/-!
List and Valentini (2016), §II, “A Simple Taxonomy”, p. 1047. The four
cases require actual or robust absence of relevant constraints, each
with or without a moralized exemption. The cited definitions are
`Setting.LiberalFree`, `Setting.MoralizedLiberalFree`,
`Setting.IndependenceFree`, and `Setting.RepublicanFree`.

The map gives each world a Boolean coordinate, uses the false copy as
actual, and pulls relevance, constraints, and permission back along the
first projection. On the adjudicated reading the true copy of the actual
world supplies the additional relevant world.

Checked: `lake env lean docs/provenance/transfers/047-four-freedom-cases.lean`
-/

namespace Transfer047

open AISafetyAtlas.Sovereignty

variable {N A W : Type*}

def PrintHyp (S : Setting N A W) : Prop :=
  ∃ w ∈ S.relevant, w ≠ S.actual

private def absence (S : Setting N A W) (moralized robust : Bool) (i : N) (a : A) : Prop :=
  match moralized, robust with
  | false, false => ¬ S.constrains S.actual i a
  | true, false => ¬ (S.constrains S.actual i a ∧ ¬ S.permitted S.actual i a)
  | false, true => ∀ w ∈ S.relevant, ¬ S.constrains w i a
  | true, true => ∀ w ∈ S.relevant, ¬ (S.constrains w i a ∧ ¬ S.permitted w i a)

def PrintStatement (S : Setting N A W) (_ : PrintHyp S) (moralized robust : Bool)
    (i : N) (a : A) : Prop :=
  absence S moralized robust i a

def LeanStatement (S : Setting N A W) (moralized robust : Bool) (i : N) (a : A) : Prop :=
  match moralized, robust with
  | false, false => S.LiberalFree i a
  | true, false => S.MoralizedLiberalFree i a
  | false, true => S.IndependenceFree i a
  | true, true => S.RepublicanFree i a

def phi (S : Setting N A W) : Setting N A (W × Bool) where
  actual := (S.actual, false)
  relevant := Prod.fst ⁻¹' S.relevant
  actual_mem := S.actual_mem
  constrains w := S.constrains w.1
  permitted w := S.permitted w.1

theorem print_hyp (S : Setting N A W) : PrintHyp (phi S) :=
  ⟨(S.actual, true), S.actual_mem, fun h ↦ Bool.noConfusion (congrArg Prod.snd h)⟩

private theorem condition_on_setting (S : Setting N A W) (moralized robust : Bool)
    (i : N) (a : A) :
    LeanStatement S moralized robust i a ↔ absence S moralized robust i a := by
  cases moralized <;> cases robust <;>
    simp [LeanStatement, absence, Setting.LiberalFree, Setting.MoralizedLiberalFree,
      Setting.IndependenceFree, Setting.RepublicanFree, Setting.Free, Setting.worlds,
      Setting.Counts]

private theorem forall_relevant_phi (S : Setting N A W) (P : W → Prop) :
    (∀ w ∈ (phi S).relevant, P w.1) ↔ (∀ w ∈ S.relevant, P w) :=
  ⟨fun h w hw ↦ h (w, false) hw, fun h w hw ↦ h w.1 hw⟩

theorem defining_condition (S : Setting N A W) (moralized robust : Bool) (i : N) (a : A) :
    LeanStatement S moralized robust i a ↔
      PrintStatement (phi S) (print_hyp S) moralized robust i a := by
  rw [condition_on_setting]
  cases moralized <;> cases robust
  · rfl
  · exact (forall_relevant_phi S (fun w ↦ ¬ S.constrains w i a)).symm
  · rfl
  · exact (forall_relevant_phi S (fun w ↦ ¬ (S.constrains w i a ∧ ¬ S.permitted w i a))).symm

theorem lean_of_print (S : Setting N A W) (moralized robust : Bool) (i : N) (a : A) :
    PrintStatement (phi S) (print_hyp S) moralized robust i a →
      LeanStatement S moralized robust i a :=
  (defining_condition S moralized robust i a).mpr

theorem print_of_lean (S : Setting N A W) (hS : PrintHyp S) (moralized robust : Bool)
    (i : N) (a : A) :
    LeanStatement S moralized robust i a → PrintStatement S hS moralized robust i a :=
  (condition_on_setting S moralized robust i a).mp

end Transfer047
