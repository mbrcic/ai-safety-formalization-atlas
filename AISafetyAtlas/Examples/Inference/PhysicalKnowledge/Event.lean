module

public import AISafetyAtlas.Inference.PhysicalKnowledge.Event
public import AISafetyAtlas.Examples.Inference.PhysicalKnowledge

/-!
# Countermodel to Wolpert 2018 Corollary 25

The four-state observer from the Definition 11 example knows the event that its
target bit is true. Its unique correct selector uses both setup blocks, so the
union in equation (11) is the entire universe. Neither setup block has a
constantly-true conclusion, and therefore the observer cannot physically know
the characteristic function of that whole-universe event.

This refutes positive introspection under the natural extension to a
singleton-image target. Under the paper's standing two-valued-function
convention the universal event's characteristic is inadmissible, so Corollary
25 is not even closed under its own construction. Either reading exposes the
same proof error: the original event characteristic and the characteristic of
equation (11)'s union do not agree on the selected blocks.
-/

namespace AISafetyAtlas.Examples.Inference.PhysicalKnowledge.Event

open AISafetyAtlas.Inference
open AISafetyAtlas.Examples.Inference.PhysicalKnowledge

private theorem indicator_trueWorlds :
    eventIndicator trueWorlds = target := by
  funext u
  classical
  simp [eventIndicator, trueWorlds, target]

/-- The original source-faithful certificate, transported only across the
definitional equality between the event characteristic and the target bit. -/
public noncomputable def knowsEventWitness :
    PhysicalKnowledgeWitness observer (eventIndicator trueWorlds) true trueWorlds := by
  rw [indicator_trueWorlds]
  exact knowsTrueWitness

public theorem observer_knows_event : KnowsEvent observer trueWorlds :=
  ⟨knowsEventWitness⟩

private theorem knowsEventWitness_selector_setup
    (g : ImageValue (eventIndicator trueWorlds)) :
    (knowsEventWitness.selector g).1 = g.1 := by
  let x : Bool := (knowsEventWitness.selector g).1
  let u : Bool × Bool := (x, g.1)
  have huX : observer.setup u = (knowsEventWitness.selector g).1 := by rfl
  have hc := knowsEventWitness.correct g u huX
  have htarget : eventIndicator trueWorlds u = g.1 := by
    cases hg : g.1 <;> simp [eventIndicator, trueWorlds, target, u, hg]
  have htrue : observer.concl u = true := hc.mpr htarget
  have heq : g.1 = x := by simpa [observer, u, x] using htrue
  exact heq.symm

/-- Every world lies in a setup block selected by the knowledge certificate, so
equation (11) makes the event “the observer knows `trueWorlds`” universal. -/
public theorem observer_knowledgeEvent_eq_univ :
    KnowledgeEvent observer trueWorlds = Set.univ := by
  apply Set.eq_univ_of_forall
  rintro u
  let g : ImageValue (eventIndicator trueWorlds) :=
    ⟨u.1, by
      rw [indicator_trueWorlds]
      exact ⟨(false, u.1), rfl⟩⟩
  apply mem_knowledgeEvent_of_selected knowsEventWitness g
  exact (knowsEventWitness_selector_setup g).symm

/-- The observer has no setup block on which its conclusion is constantly true,
so it cannot physically know the constant-true characteristic of `Set.univ`. -/
public theorem observer_not_knows_univ :
    ¬ KnowsEvent observer (Set.univ : Set (Bool × Bool)) := by
  intro h
  obtain ⟨K⟩ := h
  let x : Bool := K.knownBlock.1
  let u : Bool × Bool := (x, !x)
  have huX : observer.setup u = K.knownBlock.1 := by rfl
  have hc := K.correct ⟨true, K.target_realized⟩ u huX
  have hind : eventIndicator (Set.univ : Set (Bool × Bool)) u = true := by
    simp [eventIndicator]
  have htrue : observer.concl u = true := hc.mpr hind
  change decide (Bool.not x = x) = true at htrue
  have hcontra : Bool.not x = x := of_decide_eq_true htrue
  exact Bool.not_ne_self x hcontra

/-- **Corollary 25 is false as printed.** The observer knows `E`, but does not
know the event `K(D knows E)` defined by the paper's own equation (11). -/
public theorem not_positiveIntrospection_observer :
    ¬ PositiveIntrospection observer := by
  intro h
  have hk := h trueWorlds observer_knows_event
  rw [observer_knowledgeEvent_eq_univ] at hk
  exact observer_not_knows_univ hk

end AISafetyAtlas.Examples.Inference.PhysicalKnowledge.Event
