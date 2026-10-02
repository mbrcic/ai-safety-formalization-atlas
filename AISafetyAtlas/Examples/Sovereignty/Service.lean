module

public import AISafetyAtlas.Sovereignty.Service
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# A delegate that refuses everything, and one that does not

Three outcomes, read as the state of a memory the principal has asked to be
corrected: `0` nothing changed, `1` the authorized correction was applied, `2`
an unauthorized change happened.

The protected family is the single safety property *no unauthorized change*,
which is `{0, 1}`. The demand catalogue adds the service demand *the correction
is applied*, which is `{1}`.

`refusing` is `pinnedForm 0`: whatever anyone does, nothing changes. `serving`
is `principalDecides`, in which the principal names the outcome.

`d8` is the pair of facts D8 asserts, at these witnesses: `refusing` retains
the protected family and fails the catalogue. `serving_demandwise` is the
non-vacuity that makes the failure informative -- the catalogue is satisfiable,
so refusing it is a fact about the delegate and not about an impossible
specification.

`separating_rival` and `serving_separating` do the same for the stronger
catalogue-side condition: `{{0}, {1}}` asks for two outcomes that cannot both
happen, no refusing delegate passes it whatever its still point, and `serving`
does.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Service

open AISafetyAtlas.Sovereignty

/-- The refusing delegate: nothing anyone does changes the outcome. -/
@[expose] public def refusing : GameForm.{0, 0, 0} Bool (Fin 3) :=
  pinnedForm 0

/-- The serving delegate: the principal names the outcome. -/
@[expose] public def serving : GameForm.{0, 0, 0} Bool (Fin 3) :=
  principalDecides (Fin 3)

/-- The protected family: no unauthorized change. -/
@[expose] public def protectedFamily : Set (Set (Fin 3)) :=
  {({0, 1} : Set (Fin 3))}

/-- The demand catalogue: no unauthorized change, **and** the correction is
applied. -/
@[expose] public def catalogue : Set (Set (Fin 3)) :=
  {({0, 1} : Set (Fin 3)), ({1} : Set (Fin 3))}

/-- Everyone has a strategy in the refusing delegate. -/
public instance refusing_nonempty (i : Bool) : Nonempty (refusing.strategy i) :=
  ⟨PUnit.unit⟩

/-- The refusing delegate is inert at "nothing changed". -/
public theorem refusing_inert : Inert refusing 0 :=
  inert_pinnedForm 0

/-- Every protected set holds when nothing changes, which is what makes the
family safety-shaped. -/
public theorem zero_mem_protectedFamily :
    ∀ A ∈ protectedFamily, (0 : Fin 3) ∈ A := by
  rintro A rfl
  simp [Set.mem_insert_iff]

/-- The service demand is in the catalogue and fails at "nothing changed". -/
public theorem service_demand_mem : ({1} : Set (Fin 3)) ∈ catalogue := by
  simp [catalogue]

/--
**D8 at a witness.** One delegate retains the whole protected family and meets
no catalogue containing the service demand. Safety was preserved and nothing
was delivered.
-/
public theorem d8 :
    RetainsFamily serving refusing {false} {false} protectedFamily ∧
      ¬ Demandwise refusing {false} catalogue :=
  retainsFamily_and_not_demandwise refusing_inert zero_mem_protectedFamily
    service_demand_mem (by simp)

/-- **The catalogue is satisfiable**, so `d8` is a fact about the refusing
delegate rather than about an impossible specification. -/
public theorem serving_demandwise : Demandwise serving {false} catalogue := by
  rintro Φ (rfl | rfl)
  · exact (principalDecides_forces_singleton (1 : Fin 3)).mono (by simp)
  · exact principalDecides_forces_singleton (1 : Fin 3)

/-! ## The catalogue-side condition -/

/-- Two demands that cannot both be met: apply the correction, or leave the
memory alone. -/
@[expose] public def rival : Set (Set (Fin 3)) :=
  {({0} : Set (Fin 3)), ({1} : Set (Fin 3))}

/-- `rival` is separating: no outcome meets both demands. -/
public theorem separating_rival : Separating rival := by
  ext x
  simp only [Set.mem_sInter, rival, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_empty_iff_false, iff_false, not_forall]
  exact ⟨if x = 0 then {1} else {0}, by split <;> simp_all⟩

/-- **No refusing delegate passes `rival`**, whatever it is pinned to -- the
quantifier is over the delegate. -/
public theorem no_inert_demandwise_rival {G : GameForm.{0, 0, 0} Bool (Fin 3)}
    [∀ i, Nonempty (G.strategy i)] {x₀ : Fin 3} (h : Inert G x₀) :
    ¬ Demandwise G {false} rival :=
  separating_not_demandwise_of_inert h separating_rival

/-- And `serving` does pass it, so the condition is not unsatisfiable. -/
public theorem serving_separating : Demandwise serving {false} rival := by
  rintro Φ (rfl | rfl)
  · exact principalDecides_forces_singleton (0 : Fin 3)
  · exact principalDecides_forces_singleton (1 : Fin 3)

/-- **The protected family is vacuously retainable**, and the characterization
says exactly why: its members share the outcome `0`. -/
public theorem protectedFamily_vacuous :
    ∃ x₀ : Fin 3,
      RetainsFamily serving (pinnedForm x₀) {false} {false} protectedFamily :=
  ⟨0, d8.1⟩

/-! ## The service vocabulary read at these two delegates

Nothing new is proved below. Each general lemma of
`AISafetyAtlas.Sovereignty.Service` is applied at `refusing` or `serving`, whose
hypotheses this file has already discharged.
-/

/-- **Demandwise sovereignty is catalogue containment in the effectivity
family**, read at the delegate that passes the catalogue. -/
public theorem serving_demandwise_iff_subset :
    Demandwise serving {false} catalogue ↔ catalogue ⊆ effectivity serving {false} :=
  demandwise_iff_subset

/-- **Fewer demands are easier**: the protected family sits inside the
catalogue, so `serving` meets it too. -/
public theorem serving_demandwise_protectedFamily :
    Demandwise serving {false} protectedFamily :=
  Demandwise.mono serving_demandwise (by
    rintro Φ rfl
    simp [catalogue])

/-- **The refusing delegate meets exactly the demands that hold at "nothing
changed"**, which is why it passes the protected family and fails the
catalogue. -/
public theorem refusing_demandwise_iff {𝒬 : Set (Set (Fin 3))} :
    Demandwise refusing {false} 𝒬 ↔ ∀ Φ ∈ 𝒬, (0 : Fin 3) ∈ Φ :=
  Inert.demandwise_iff refusing_inert

/-- And so it does pass the protected family. -/
public theorem refusing_demandwise_protectedFamily :
    Demandwise refusing {false} protectedFamily :=
  refusing_demandwise_iff.mpr zero_mem_protectedFamily

/-- **The refusing delegate's effectivity family is the same at every
coalition**: the sets containing the still point. Universal-looking effectivity
here is the outcome having been settled in advance. -/
public theorem refusing_effectivity_eq (C : Set Bool) :
    effectivity refusing C = {A : Set (Fin 3) | (0 : Fin 3) ∈ A} :=
  Inert.effectivity_eq refusing_inert C

/-- **A separating catalogue is nonempty**, so `rival` is a specification and
not an empty one. -/
public theorem rival_nonempty : rival.Nonempty :=
  Separating.nonempty separating_rival

/-- **Separating survives adding demands**, so checking it on `rival` settles it
for every catalogue that contains `rival`. -/
public theorem separating_rival_union :
    Separating (rival ∪ protectedFamily) :=
  Separating.mono separating_rival Set.subset_union_left

/-- **Vacuous retainability, characterized.** The protected family is retained
by some refusing delegate exactly because its members share an outcome the
baseline could already deliver. -/
public theorem protectedFamily_vacuous_iff :
    (∃ x₀ : Fin 3,
        RetainsFamily serving (pinnedForm x₀) {false} {false} protectedFamily) ↔
      (⋂₀ (protectedFamily ∩ effectivity serving {false})).Nonempty :=
  exists_pinned_retainsFamily_iff

end AISafetyAtlas.Examples.Sovereignty.Service
