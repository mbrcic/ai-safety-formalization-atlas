module

public import AISafetyAtlas.Inference.PhysicalKnowledge

/-!
# Physical knowledge — an executable Wolpert 2018 certificate

The observer chooses which value of a Boolean target it is testing. Its
conclusion says whether the target equals that chosen value. Over the worlds in
which the target is true, the resulting selector satisfies every clause of
Wolpert's Definition 11 for knowing that the target is true.

This example is deliberately stronger than a bare weak-inference witness: both
the positive selected block and the alternative block meet `W`, and their
conclusions have the signs Definition 11 requires. It also exercises Lemma 17
and Corollary 19 on a non-singleton universe.
-/

namespace AISafetyAtlas.Examples.Inference.PhysicalKnowledge

open AISafetyAtlas.Inference

/-- The fact to be known is the world's second bit. -/
public abbrev target : Bool × Bool → Bool := Prod.snd

/-- The device chooses a candidate value in its first bit and reports whether
that candidate agrees with the target in the second bit. -/
public abbrev observer : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := fun u => decide (u.2 = u.1)
  concl_surjective := by
    intro b
    cases b
    · exact ⟨(false, true), rfl⟩
    · exact ⟨(false, false), rfl⟩

/-- The context in which the target is true. -/
public abbrev trueWorlds : Set (Bool × Bool) := {u | target u = true}

/-- Select the setup block whose candidate is the realized target value. -/
private def selectedBlock (g : ImageValue target) : SetupBlock observer :=
  ⟨g.1, ⟨(g.1, g.1), rfl⟩⟩

/-- All three clauses of Definition 11 hold for this concrete observer. -/
public def knowsTrueWitness :
    PhysicalKnowledgeWitness observer target true trueWorlds := by
  refine {
    target_realized := ⟨(false, true), rfl⟩
    selector := selectedBlock
    correct := ?_
    yes_nonempty := ?_
    yes_on := ?_
    no_nonempty := ?_
    no_on := ?_ }
  · intro g u hu
    cases u with
    | mk candidate actual =>
      simp only [observer, selectedBlock] at hu
      subst candidate
      cases actual <;> cases g.1 <;> decide
  · exact ⟨(true, true), rfl, rfl⟩
  · intro u huW huX
    cases u with
    | mk candidate actual =>
      simp only [trueWorlds, target, Set.mem_ofPred_eq] at huW
      simp only [observer, selectedBlock] at huX
      subst actual
      subst candidate
      rfl
  · intro g hg
    have hfalse : g.1 = false := by
      cases h : g.1
      · rfl
      · exact (hg h).elim
    exact ⟨(false, true), rfl, by simp [selectedBlock, hfalse]⟩
  · intro g hg u huW huX
    have hfalse : g.1 = false := by
      cases h : g.1
      · rfl
      · exact (hg h).elim
    cases u with
    | mk candidate actual =>
      simp only [trueWorlds, target, Set.mem_ofPred_eq] at huW
      simp only [observer, selectedBlock] at huX
      subst actual
      rw [hfalse] at huX
      subst candidate
      rfl

/-- Executable non-vacuity: this device physically knows the true target value
over the declared context. -/
public theorem observer_physicallyKnows_true :
    PhysicallyKnows observer target true trueWorlds :=
  ⟨knowsTrueWitness⟩

/-- The example context refines the target, as Corollary 19 requires. -/
public theorem trueWorlds_refines_target : RefinesOn trueWorlds target := by
  intro u v hu hv
  exact hu.trans hv.symm

/-- Corollary 19 applied to the concrete Definition 11 certificate. -/
public theorem target_true_on_trueWorlds :
    ∀ u, u ∈ trueWorlds → target u = true :=
  true_on_of_physicallyKnows_true trueWorlds_refines_target
    observer_physicallyKnows_true

end AISafetyAtlas.Examples.Inference.PhysicalKnowledge
