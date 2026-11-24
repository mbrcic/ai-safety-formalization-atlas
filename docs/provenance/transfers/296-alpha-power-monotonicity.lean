import AISafetyAtlas.Sovereignty.ConcurrentGameFrame

/-!
Chen, Ju and Ågotnes (2026), arXiv:2607.10567v1, remark after Definition 5,
p. 8. For every coalition and state, the alpha effectivity family is closed
under supersets. The cited theorem is `AlphaPower.mono`.

The map gives a single agent the original coalition's joint actions. At the
grand coalition, availability and outcomes are pulled back by evaluating
the singleton joint action at its sole member. The state set stays fixed.

Checked: `lake env lean docs/provenance/transfers/296-alpha-power-monotonicity.lean`
-/

namespace Transfer296

open AISafetyAtlas.Sovereignty

universe u v w

def PrintStatement : Prop :=
  ∀ (AG : Type u) (ST : Type v) (AC : Type w) [Finite AG] [Nonempty AG]
      [Nonempty ST] [Nonempty AC] (F : ActionFrame AG ST AC) (C : Set AG)
      (s : ST) (X Y : Set ST),
    X ∈ alphaEff F C s → X ⊆ Y → Y ∈ alphaEff F C s

def LeanStatement : Prop :=
  ∀ {AG : Type u} {ST : Type v} {AC : Type w} {F : ActionFrame AG ST AC}
      {C : Set AG} {s : ST} {X Y : Set ST},
    AlphaPower F C s X → X ⊆ Y → AlphaPower F C s Y

variable {AG : Type u} {ST : Type v} {AC : Type w}

open Classical in
noncomputable def phi (F : ActionFrame AG ST AC) (C : Set AG) :
    ActionFrame (ULift.{u} Unit) ST (C → AC) where
  av D t :=
    if h : ULift.up () ∈ D then {σ | σ ⟨ULift.up (), h⟩ ∈ F.av C t} else ∅
  out D t σ :=
    if h : ULift.up () ∈ D then F.out C t (σ ⟨ULift.up (), h⟩) else ∅

private theorem mem_alphaEff_phi_iff (F : ActionFrame AG ST AC) (C : Set AG)
    (s : ST) (Z : Set ST) :
    Z ∈ alphaEff (phi F C) Set.univ s ↔ AlphaPower F C s Z := by
  let agent : (Set.univ : Set (ULift.{u} Unit)) := ⟨ULift.up (), Set.mem_univ _⟩
  change (∃ σ ∈ (phi F C).av Set.univ s, (phi F C).out Set.univ s σ ⊆ Z) ↔
    (∃ σ ∈ F.av C s, F.out C s σ ⊆ Z)
  simp only [phi, Set.mem_univ, dite_true, Set.mem_ofPred_eq]
  exact ⟨fun ⟨σ, hav, hout⟩ ↦ ⟨σ agent, hav, hout⟩,
    fun ⟨σ, hav, hout⟩ ↦ ⟨fun _ ↦ σ, hav, hout⟩⟩

theorem print_hyp {F : ActionFrame AG ST AC} {C : Set AG} {s : ST} {X Y : Set ST}
    (h : AlphaPower F C s X) (hXY : X ⊆ Y) :
    Nonempty ST ∧ Nonempty (C → AC) ∧ X ∈ alphaEff (phi F C) Set.univ s ∧ X ⊆ Y :=
  ⟨⟨s⟩, h.elim fun σ _ ↦ ⟨σ⟩, (mem_alphaEff_phi_iff F C s X).mpr h, hXY⟩

theorem lean_concl {F : ActionFrame AG ST AC} {C : Set AG} {s : ST} {Y : Set ST}
    (h : Y ∈ alphaEff (phi F C) Set.univ s) : AlphaPower F C s Y :=
  (mem_alphaEff_phi_iff F C s Y).mp h

theorem lean_of_print : PrintStatement.{u, v, max u w} → LeanStatement.{u, v, w} := by
  intro hp AG ST AC F C s X Y h hXY
  obtain ⟨hST, hAC, hX, hXY'⟩ := print_hyp h hXY
  exact lean_concl (hp (ULift.{u} Unit) ST (C → AC) (phi F C) Set.univ s X Y hX hXY')

theorem print_of_lean : LeanStatement.{u, v, w} → PrintStatement.{u, v, w} := by
  intro h AG ST AC _ _ _ _ F C s X Y hX hXY
  exact h hX hXY

end Transfer296
