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

/-! ## The weakened operator, at the same witness -/

/-- **The modification is a weakening**, applied to the observer's own
Definition 11 certificate. -/
public theorem observer_weakPhysicallyKnows_true :
    WeakPhysicallyKnows observer target true trueWorlds :=
  weakPhysicallyKnows_of_physicallyKnows observer_physicallyKnows_true

/-- A concrete `WeakKnowledgeWitness`, built the same way
`weakPhysicallyKnows_of_physicallyKnows` builds one internally, but kept as a
term rather than packed into `Nonempty` — `yes_block_correct` needs the term,
not just its existence. -/
public def weakKnowsTrueWitness :
    WeakKnowledgeWitness observer target true trueWorlds where
  target_realized := knowsTrueWitness.target_realized
  selector := knowsTrueWitness.selector
  yes_correct := fun u hu htrue =>
    (knowsTrueWitness.correct ⟨true, knowsTrueWitness.target_realized⟩ u hu).mp htrue
  no_correct := fun g _hg u _huW hu hfalse hval => by
    have hval' := (knowsTrueWitness.correct g u hu).mpr hval
    rw [hval'] at hfalse
    exact Bool.noConfusion hfalse

/-- **The weakened operator still entails weak inference on the known
block**, at the concrete witness above. -/
public theorem weakKnowsTrueWitness_yes_block_correct :
    observer.concl (true, true) = true → target (true, true) = true :=
  WeakKnowledgeWitness.yes_block_correct weakKnowsTrueWitness (true, true) rfl

/-! ## The operator's own laws, at this observer

Six statements about `PhysicallyKnows` had no application anywhere until
2026-09-21, including the two that connect it to Wolpert's inference notion.
The observer above satisfies the hypothesis of every one of them.
-/

/-- **Physical knowledge entails weak inference.** The bridge from Wolpert 2018's
operator back to the 2008 device notion, which is what makes the two papers one
development rather than two. -/
public theorem observer_weaklyInfers : WeaklyInfers observer target :=
  PhysicallyKnows.weaklyInfers observer_physicallyKnows_true

/-- The same, straight from the certificate rather than from its existential
wrapper — the form a construction uses when it still holds the witness. -/
public theorem observer_weaklyInfers_from_witness : WeaklyInfers observer target :=
  PhysicalKnowledgeWitness.weaklyInfers knowsTrueWitness

/-- **Knowing a value is knowing its negation's negation.** The operator
commutes with complementing the target. -/
public theorem observer_knows_negation :
    PhysicallyKnows observer (fun u => Bool.not (target u)) (Bool.not true) trueWorlds :=
  PhysicallyKnows.negate observer_physicallyKnows_true

/-- **Proposition 18 at this observer**: knowing the target is false is knowing
the complement is true, so the two readings of a negative answer agree. -/
public theorem observer_knows_false_iff :
    PhysicallyKnows observer target false trueWorlds ↔
      PhysicallyKnows observer (fun u => Bool.not (target u)) true trueWorlds :=
  physicallyKnows_false_iff_not_true observer target trueWorlds

/-- **And it cannot know both answers.** Consistency of the operator, at a
refining block — which is the hypothesis that makes it consistency rather than
an artefact of an empty block. -/
public theorem observer_not_knows_both :
    ¬ (PhysicallyKnows observer target true trueWorlds ∧
        PhysicallyKnows observer target false trueWorlds) :=
  not_physicallyKnows_true_and_false trueWorlds_refines_target

/-- **Something is never known, whatever the block.** The observer's own
conclusion: Wolpert's Theorem 1 carried into the knowledge operator, so no
device is omniscient about itself. -/
public theorem observer_has_an_unknowable :
    ∃ Γ : Bool × Bool → Bool, ∀ (W : Set (Bool × Bool)) (γ : Bool),
      ¬ PhysicallyKnows observer Γ γ W :=
  exists_never_physicallyKnown observer

end AISafetyAtlas.Examples.Inference.PhysicalKnowledge
