module

public import AISafetyAtlas.Inference.PhysicalKnowledge

/-!
# Event knowledge and the Corollary 25 boundary — Wolpert 2018

Wolpert translates physical knowledge into an Aumann-style event vocabulary:

* a device knows an event `E` when it physically knows the characteristic
  function of `E` is true over `E`;
* equation (11) defines `K(D knows E)` as the union of every setup block selected
  by every certificate witnessing that knowledge.

Those definitions are mechanized literally as `KnowsEvent` and
`KnowledgeEvent`. The paper's Corollary 25 then claims positive introspection:
knowledge of `E` entails knowledge of `K(D knows E)`.

That claim is **not made as a theorem here**. The displayed proof says that the
two characteristic functions agree throughout both selected blocks. Equation
(11), however, makes the new characteristic function true throughout every such
block, while Definition 11 only makes the original characteristic function track
the device's varying conclusion there. The equality need not hold.
`AISafetyAtlas.Examples.Inference.PhysicalKnowledge.Event` gives a four-state
countermodel: the device knows `E`, equation (11) yields the whole universe, and
the device cannot know that constant event under the natural singleton-image
extension already supported by Definition 11 in Lean. Under the paper's separate
two-valued-function convention, the resulting constant characteristic is not an
admissible target at all, so the printed corollary is instead ill-typed at this
case. Thus Corollary 25 is covered by an explicit boundary/refutation rather
than silently omitted or weakened.
-/

namespace AISafetyAtlas.Inference

universe u v

variable {U : Type u}

/-- Characteristic function of an event, with the paper's `1` renamed `true`. -/
@[expose] public noncomputable def eventIndicator (E : Set U) : U → Bool := by
  classical
  exact fun u => if u ∈ E then true else false

@[simp] public theorem eventIndicator_eq_true_iff (E : Set U) (u : U) :
    eventIndicator E u = true ↔ u ∈ E := by
  classical
  simp [eventIndicator]

@[simp] public theorem eventIndicator_eq_false_iff (E : Set U) (u : U) :
    eventIndicator E u = false ↔ u ∉ E := by
  classical
  simp [eventIndicator]

/-- Event translation preceding equation (11): `C` knows `E` when it physically
knows the characteristic function of `E` is true over `E`. -/
@[expose] public noncomputable def KnowsEvent (C : InferenceDevice.{u, v} U)
    (E : Set U) : Prop :=
  PhysicallyKnows C (eventIndicator E) true E

/-- **Equation (11).** The event “`C` knows `E`”: the union of all setup blocks
that occur in the image of any selector witnessing knowledge of `E`.

The existential presentation is the pointwise form of the source's two nested
unions. `ImageValue` restricts the inner union to realized values, exactly as
Definition 11 restricts the selector's domain to `Γ(U)`. -/
@[expose] public noncomputable def KnowledgeEvent (C : InferenceDevice.{u, v} U)
    (E : Set U) : Set U :=
  {u | ∃ K : PhysicalKnowledgeWitness C (eventIndicator E) true E,
    ∃ g : ImageValue (eventIndicator E), C.setup u = (K.selector g).1}

public theorem mem_knowledgeEvent_of_selected
    {C : InferenceDevice.{u, v} U} {E : Set U}
    (K : PhysicalKnowledgeWitness C (eventIndicator E) true E)
    (g : ImageValue (eventIndicator E)) {u : U}
    (hu : C.setup u = (K.selector g).1) :
    u ∈ KnowledgeEvent C E :=
  ⟨K, g, hu⟩

/-- The positive-introspection proposition asserted by Corollary 25, interpreted
using the natural singleton-image extension of Definition 11. It is a predicate,
not a theorem: the executable model named in the module docstring refutes it. -/
@[expose] public noncomputable def PositiveIntrospection
    (C : InferenceDevice.{u, v} U) : Prop :=
  ∀ E : Set U, KnowsEvent C E → KnowsEvent C (KnowledgeEvent C E)

end AISafetyAtlas.Inference
