module

public import AISafetyAtlas.Oversight.VarietyBound
public import AISafetyAtlas.Oversight.VarietyCheck

/-!
# Both corners, in one place

`Oversight.VarietyBound` says coverage and control are separable capacities.
Independence is a claim about two directions, and a claim about two directions
needs two models. Here they are, as small as they go.

**Corner one — sees everything, controls nothing.** Three situations, two
interventions, and an effect table that reports the situation back whatever the
overseer does. The observation is the identity, so the overseer knows exactly
which situation it is in and any hazard decision is available to it. It still
cannot force the outcome: there are more situations than interventions.

**Corner two — sees nothing, controls perfectly.** The same three situations,
an intervention that flattens every one of them to the same outcome, and an
overseer that observes nothing at all. It forces the target, while the hazard it
would have been asked about is not decidable from what it sees.

Neither corner is subtle, which is the point. If the two capacities could be
traded against each other, neither corner would exist.
-/

namespace AISafetyAtlas.Examples.Oversight

open AISafetyAtlas.Oversight
open AISafetyAtlas.Knowledge (Knowable)

/-! ## Corner one: full observation, insufficient repertoire -/

/-- The effect table that hands the situation back: whatever the overseer does,
the outcome is the situation it was facing. Ashby's "no repeat in a column". -/
@[expose] public def revealing : Fin 3 → Fin 2 → Fin 3 := fun σ _ => σ

/-- Every hazard decision is available: the overseer sees the situation itself. -/
public theorem knowable_of_full_observation (hazard : Fin 3 → Bool) :
    Knowable (id : Fin 3 → Fin 3) hazard :=
  ⟨hazard, fun _ => rfl⟩

/-- A fixed intervention still separates situations. -/
public theorem revealing_column_injective (a : Fin 2) :
    Function.Injective fun σ => revealing σ a :=
  fun _ _ h => h

/--
**Seeing everything is not enough.** No overseer forces the outcome, however it
maps its (perfect) observations to the two interventions available.
-/
public theorem not_forces_revealing (act : Fin 3 → Fin 2) (target : Fin 3) :
    ¬ Forces revealing (id : Fin 3 → Fin 3) act target :=
  not_forces_of_card_lt revealing_column_injective (by decide) act target

/-! ## Corner two: no observation, sufficient repertoire -/

/-- The effect table with a flattening intervention: intervention `0` sends every
situation to outcome `0`. -/
@[expose] public def flattening : Fin 3 → Fin 2 → Fin 3 := fun _ _ => 0

/-- The blind overseer. -/
@[expose] public def blind : Fin 3 → Unit := fun _ => ()

/-- The hazard it would be asked about: is this the first situation? -/
@[expose] public def firstSituation : Fin 3 → Bool := fun σ => σ = 0

/-- **It cannot see.** A decision rule reading a constant returns a constant, and
the hazard is not constant. -/
public theorem not_knowable_blind : ¬ Knowable blind firstSituation := by
  rintro ⟨decide, hdec⟩
  have h0 : firstSituation 0 = decide () := hdec 0
  have h1 : firstSituation 1 = decide () := hdec 1
  rw [show firstSituation 0 = true from by decide,
    show firstSituation 1 = false from by decide] at *
  exact absurd (h0.trans h1.symm) (by decide)

/-- **And it controls anyway.** -/
public theorem forces_flattening : Forces flattening blind (fun _ => 0) 0 :=
  forces_of_constant_effect (fun _ => rfl)

/-! ## The pair -/

/--
**Independence, witnessed.** Coverage without control, and control without
coverage, in models of three situations each.
-/
public theorem coverage_and_control_are_independent :
    (∀ hazard : Fin 3 → Bool, Knowable (id : Fin 3 → Fin 3) hazard)
      ∧ (∀ (act : Fin 3 → Fin 2) (target : Fin 3),
          ¬ Forces revealing (id : Fin 3 → Fin 3) act target)
      ∧ ¬ Knowable blind firstSituation
      ∧ Forces flattening blind (fun _ => 0) 0 :=
  ⟨knowable_of_full_observation, not_forces_revealing, not_knowable_blind, forces_flattening⟩

/-! ## The same verdict, decided

`Oversight.VarietyCheck.cannotForce` is what `atlas-check` runs on a model read
from JSON. Here it is on corner one, so the executable verdict and the proved one
are visible side by side rather than only in the harness.
-/

/-- The checker agrees: the counting obstruction applies to `revealing`. -/
public theorem cannotForce_revealing : cannotForce revealing = true := by decide

/-- And it is silent on `flattening`, which is the case where the bound's
structural hypothesis fails. A `false` verdict is not a clearance. -/
public theorem not_cannotForce_flattening : cannotForce flattening = false := by decide

/-- The executable verdict carries the same conclusion as `not_forces_revealing`,
through the agreement theorem rather than through a second argument. -/
public theorem not_forces_revealing_via_checker (act : Fin 3 → Fin 2) (target : Fin 3) :
    ¬ Forces revealing (id : Fin 3 → Fin 3) act target :=
  not_forces_of_cannotForce cannotForce_revealing _ act target

/-! ## A small repertoire that collapses beats a large one that does not

`revealing` and `flattening` sit at the two ends of the counting bound, but both
have small repertoires, so neither shows the thing that makes counting the wrong
measure. These two do. `manyWeak` holds twice as many interventions as
`twoWithNuke` and cannot force anything; `twoWithNuke` holds two and forces,
because one of them lands every situation on the same outcome.
-/

/-- Blind observation on five situations: the comparison is about repertoires,
so nothing here should turn on what is seen. -/
@[expose] public def blind5 : Fin 5 → Unit := fun _ => ()

/-- **Four interventions, none of which collapses anything.** Every act leaves the
situation exactly as informative as it was. -/
@[expose] public def manyWeak : Fin 5 → Fin 4 → Fin 5 := fun σ _ => σ

/-- **Two interventions, one of which collapses everything.** Act `true` lands
every situation on `0`; act `false` changes nothing. -/
@[expose] public def twoWithNuke : Fin 5 → Bool → Fin 5 := fun σ a => if a then 0 else σ

/-- Every act of `manyWeak` preserves every distinction. -/
public theorem manyWeak_column_injective (a : Fin 4) :
    Function.Injective fun σ => manyWeak σ a := fun _ _ h => h

/-- No act of `manyWeak` is decisive, whatever target you name. -/
public theorem not_decisive_manyWeak (a : Fin 4) (target : Fin 5) :
    ¬ Decisive manyWeak a target :=
  not_decisive_of_injective (manyWeak_column_injective a) target

/-- **The larger repertoire cannot force.** Four acts against five situations,
with nothing collapsing. -/
public theorem not_forces_manyWeak (act : Unit → Fin 4) (target : Fin 5) :
    ¬ Forces manyWeak blind5 act target :=
  not_forces_of_card_lt manyWeak_column_injective (by decide) act target

/-- The nuke is decisive for `0`. -/
public theorem decisive_twoWithNuke : Decisive twoWithNuke true 0 := by
  rw [decisive_iff]; intro σ; rfl

/-- **The smaller repertoire forces.** Two acts against the same five situations,
because one of them collapses. -/
public theorem forces_twoWithNuke : Forces twoWithNuke blind5 (fun _ => true) 0 :=
  forces_of_decisive decisive_twoWithNuke

/--
**Repertoire size is not power.** Against the same five situations and the same
blind observation, four interventions cannot force and two can. What separates
them is that one of the two collapses the situation space and none of the four
does.

This refutes reading `not_forces_of_card_lt` as "more acts, more power". It is a
necessary condition that holds only under `hcol`, and `hcol` is exactly the
assumption that nobody holds a collapsing act.
-/
public theorem fewer_acts_can_force_while_more_cannot :
    (∀ act : Unit → Fin 4, ∀ target, ¬ Forces manyWeak blind5 act target) ∧
      Forces twoWithNuke blind5 (fun _ => true) 0 :=
  ⟨fun act target => not_forces_manyWeak act target, forces_twoWithNuke⟩

/-! ## Power that becomes, and does not stay

A repertoire is a snapshot. `disarmable` is a substrate with two configurations:
in `false` the collapsing act works, in `true` it has been neutralised and every
act is back to preserving distinctions. The agent's repertoire is the same size
in both. What changed is the substrate, and with it the power.
-/

/-- A substrate whose decisive act can be taken away. -/
@[expose] public def disarmable : Bool → Fin 5 → Bool → Fin 5 :=
  fun k σ a => if a && !k then 0 else σ

/-- In the armed configuration the act still forces. -/
public theorem forces_disarmable_armed :
    Forces (disarmable false) blind5 (fun _ => true) 0 :=
  forces_of_decisive (by rw [decisive_iff]; intro σ; rfl)

/-- In the disarmed configuration nothing collapses, and the same act fails. -/
public theorem not_forces_disarmable_disarmed (act : Unit → Bool) (target : Fin 5) :
    ¬ Forces (disarmable true) blind5 act target :=
  not_forces_of_card_lt (fun a _ _ h => by simpa [disarmable] using h) (by decide)
    act target

/--
**Power that becomes need not stay.** The policy forces in one configuration of
the substrate and in another it does not, so it is not robust: holding a
collapsing act is a fact about the configuration you are in, not a possession
that travels with you.
-/
public theorem disarmable_power_does_not_stay :
    Forces (disarmable false) blind5 (fun _ => true) 0 ∧
      ¬ RobustlyForces disarmable blind5 (fun _ => true) 0 :=
  ⟨forces_disarmable_armed,
    not_robustlyForces_of_exists_not true (not_forces_disarmable_disarmed _ 0)⟩


/-! ## The arena and robustness vocabulary, at these tables

`flattening` is the table where forcing succeeds and `twoWithNuke` the one with
a decisive act, so each statement below is read where its hypothesis holds.
-/

/-- **Forcing is the composite being constant**, at the table that forces. -/
public theorem forces_flattening_iff_constant :
    Forces flattening blind (fun _ ↦ 0) 0 ↔
      ∀ σ, flattening σ ((fun _ ↦ 0) (blind σ)) = 0 :=
  forces_iff_composite_constant

/-- A one-configuration substrate built from the table with a decisive act. -/
@[expose] public def nukeFamily : Unit → Fin 5 → Bool → Fin 5 := fun _ ↦ twoWithNuke

/-- **An act that stays decisive is power that stays.** The hypothesis is met by
`decisive_twoWithNuke` in every configuration, there being one. -/
public theorem robustlyForces_nukeFamily :
    RobustlyForces nukeFamily blind5 (fun _ ↦ true) 0 :=
  robustlyForces_of_decisive (fun _ ↦ decisive_twoWithNuke)

/-- And robust power is power in each configuration separately. -/
public theorem nukeFamily_forces :
    Forces (nukeFamily ()) blind5 (fun _ ↦ true) 0 :=
  RobustlyForces.forces robustlyForces_nukeFamily ()

/-- **Some act forces exactly when the arena forces the singleton**, which is
what lets the counting bound be stated on the arena. -/
public theorem exists_forces_flattening_iff_arena :
    (∃ act, Forces flattening blind act 0) ↔
      (effectArena flattening blind).Forces {0} :=
  exists_forces_iff_arena_forces

/-- The arena's collapse at a policy is the set of outcomes that policy still
admits. -/
public theorem arena_collapse_flattening :
    (effectArena flattening blind).collapse (fun _ ↦ 0)
      = Set.range fun σ ↦ flattening σ ((fun _ ↦ 0) (blind σ)) :=
  arena_collapse_eq

/-- **A constant effect forces its target even when the hazard is unknowable.**
The reading that matters for oversight: an action whose outcome does not depend
on the situation needs no information about the situation, so the variety bound
is about actions that *discriminate* and says nothing about the ones that do
not. `flattening` is constant and `blind` cannot see the hazard, and the forcing
holds anyway. -/
public theorem flattening_forces_despite_blindness :
    Forces flattening blind (fun _ => (0 : Fin 2)) 0 :=
  forces_of_constant_effect_of_not_knowable not_knowable_blind (fun _ => rfl)

end AISafetyAtlas.Examples.Oversight
