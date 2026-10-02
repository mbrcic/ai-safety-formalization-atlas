module

public import AISafetyAtlas.Sovereignty.Catalogue
public import AISafetyAtlas.Examples.Sovereignty.Quantifiers

/-!
# A checklist that passes and a system that cannot be run

One game, one catalogue, two readings that disagree.

`decider` is the principal naming the outcome. The catalogue asks for two
things: *the bit comes out `true`*, and *the bit comes out `false`*. Each is
forceable, so `decider_demandwise` passes the catalogue demand by demand.
`decider_not_demandwiseUniform` says no single commitment serves both, because
they are disjoint.

`decider_selector` exhibits what the weak reading actually provides, and it is
the proposal's `S2` made concrete: a function from the demand to the policy.
The policy has to be told which demand it is serving, which is exactly what an
operating system is not told in advance.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Catalogue

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Examples.Sovereignty.Quantifiers

/-- Two demands that cannot both be met: the bit comes out `true`, and the bit
comes out `false`. -/
@[expose] public def rivalBits : Set (Set Bool) :=
  {({true} : Set Bool), ({false} : Set Bool)}

/-- **Each demand is forceable**, so the catalogue passes demand by demand. -/
public theorem decider_demandwise : Demandwise decider {false} rivalBits := by
  rintro Φ (rfl | rfl)
  · exact principalDecides_forces_singleton true
  · exact principalDecides_forces_singleton false

/-- **And no single commitment serves both.** -/
public theorem decider_not_demandwiseUniform :
    ¬ DemandwiseUniform decider {false} rivalBits := by
  refine not_demandwiseUniform_of_disjoint (Φ := ({true} : Set Bool))
    (Ψ := ({false} : Set Bool)) (by simp [rivalBits]) (by simp [rivalBits]) ?_
  rw [Set.disjoint_iff_inter_eq_empty]
  ext b
  simp

/-- So the two readings of a catalogue come apart: an evaluation that scores
demands one at a time certifies something no configuration of the system
delivers. -/
public theorem demandwise_not_uniform :
    Demandwise decider {false} rivalBits ∧
      ¬ DemandwiseUniform decider {false} rivalBits :=
  ⟨decider_demandwise, decider_not_demandwiseUniform⟩

/-- **What the weak reading does provide**, as the proposal's `S2` says: a
policy for each demand, chosen knowing the demand. -/
public theorem decider_selector :
    ∃ f : rivalBits → ∀ i : ({false} : Set Bool), decider.strategy i,
      ∀ Φ : rivalBits, outcomesOf decider {false} (f Φ) ⊆ (Φ : Set Bool) :=
  demandwise_iff_exists_selector.mp decider_demandwise

/-! ## A catalogue one commitment does serve

Everything above is a refutation of the uniform reading. The rest of
`AISafetyAtlas.Sovereignty.Catalogue` is about catalogues that pass it, so a
positive witness is needed too -- otherwise those results would only ever be
read at a hypothesis nothing in the tree meets.
-/

/-- Two demands a single commitment serves: the bit comes out `true`, and the
bit comes out at all. -/
@[expose] public def agreeBits : Set (Set Bool) :=
  {({true} : Set Bool), (Set.univ : Set Bool)}

/-- **One commitment serves the whole catalogue.** Naming `true` settles both
demands at once, which is what the uniform reading asks for and what
`rivalBits` denies. -/
public theorem decider_demandwiseUniform :
    DemandwiseUniform decider {false} agreeBits := by
  refine ⟨fun _ ↦ true, ?_⟩
  rintro Φ hΦ x ⟨s, hs, rfl⟩
  have h0 : s false = true := hs ⟨false, rfl⟩
  rcases hΦ with rfl | rfl
  · show decider.outcome s ∈ ({true} : Set Bool)
    rw [Set.mem_singleton_iff]
    exact h0
  · exact Set.mem_univ _

/-- **The uniform reading implies the demandwise one**, read at the catalogue
that passes it. -/
public theorem decider_demandwise_agreeBits :
    Demandwise decider {false} agreeBits :=
  demandwise_of_demandwiseUniform decider_demandwiseUniform

/-- **A uniform catalogue is forced whole**, not demand by demand -- which is
precisely what `decider_not_demandwiseUniform` shows `rivalBits` cannot do. -/
public theorem decider_forces_sInter_agreeBits :
    Forces decider {false} (⋂₀ agreeBits) :=
  forces_sInter_of_demandwiseUniform decider_demandwiseUniform

/-- And the uniform reading is antitone in the catalogue. -/
public theorem decider_demandwiseUniform_singleton :
    DemandwiseUniform decider {false} ({({true} : Set Bool)} : Set (Set Bool)) :=
  DemandwiseUniform.mono decider_demandwiseUniform (by
    rintro Φ rfl
    simp [agreeBits])

/-- **A separating pair refutes the uniform reading**, which is
`decider_not_demandwiseUniform` again with the hypothesis stated as separation
rather than as disjointness. -/
public theorem decider_not_demandwiseUniform_of_separating :
    ¬ DemandwiseUniform decider {false} rivalBits :=
  not_demandwiseUniform_of_separating_pair (by
    show Separating ({({true} : Set Bool), ({false} : Set Bool)} : Set (Set Bool))
    unfold Separating
    ext b
    simp)

/-- **Retention is reflexive**, which with `RetainsFamily.trans` makes it a
preorder. -/
public theorem decider_retainsFamily_refl :
    RetainsFamily decider decider {false} {false} rivalBits :=
  retainsFamily_refl decider {false} rivalBits

end AISafetyAtlas.Examples.Sovereignty.Catalogue
