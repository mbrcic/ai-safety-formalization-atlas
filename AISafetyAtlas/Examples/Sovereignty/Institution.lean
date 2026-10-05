module

public import AISafetyAtlas.Sovereignty.Institution
public import AISafetyAtlas.Examples.Sovereignty.Deontic

/-!
# One rule, one mandate, and one cycle that installs nothing

A minimal institution over the eight acts of
`AISafetyAtlas.Examples.Sovereignty.Deontic.cube`. Two facts: a request has been
filed (`0`), and a mandate exists (`1`). One constitutive rule: an
institutionally empowered act, performed when a request is on file, creates the
mandate.

Three things are shown.

* The rule fires: an empowered act **is recognized** as creating the mandate.
* Recognition is **not** authorization — the same institution has an empowered act
  its mandate rule makes count as creating the mandate, and does not authorize it,
  because the act is not permitted.
* A pair of rules that only cite each other, with no ground facts, derives
  **nothing**. Authority does not bootstrap.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Institution

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Examples.Sovereignty.Deontic

/-! ## An institution with one rule -/

/-- Given a filed request, an empowered act creates the mandate. -/
@[expose] public def mandateRule : ConstitutiveRule (Fin 8) (Fin 2) where
  premises := [0]
  trigger := empoweredBit
  conclusion := 1

/-- The request is on file. -/
@[expose] public def filed : Fin 2 → Prop := fun f => f = 0

/-- The institution: one rule, one ground fact, and `cube`'s three axes. -/
@[expose] public def office : AISafetyAtlas.Sovereignty.Institution (Fin 8) (Fin 2) where
  rules := [mandateRule]
  facts := filed
  setting := cube

/-- **The rule fires.** Act `7` is empowered, so the office recognizes it as
creating the mandate. -/
public theorem office_recognizes_mandate : office.Recognized 7 1 := by
  refine Derives.fire mandateRule (by simp [office]) ?_ ?_
  · show empoweredBit 7
    unfold empoweredBit
    decide
  · intro p hp
    have : p = 0 := by simpa [mandateRule] using hp
    exact Derives.given (by simp [office, filed, this])

/-- **And act `7` is fully authorized**: recognized, permitted and possible. -/
public theorem office_authorizes_seven : office.Authorized 7 1 := by
  refine ⟨office_recognizes_mandate, ?_, ?_⟩
  · show permittedBit 7
    unfold permittedBit
    decide
  · show possibleBit 7
    unfold possibleBit
    decide

/--
**Recognition is not authorization.** The same office has an empowered, possible
act that its mandate rule makes count as creating the mandate, and which it does
not authorize, because the act is not permitted.
-/
public theorem office_recognized_not_authorized :
    ∃ e, office.setting.empowered e ∧ office.setting.possible e ∧
      office.Recognized e 1 ∧ ¬ office.Authorized e 1 :=
  office.exists_recognized_not_authorized (r := mandateRule) cube_separated
    (by simp [office]) (fun p hp => by simp_all [mandateRule, office, filed])
    (fun _ he => he)

/--
**Authorization is three conditions and the characterisation is what takes it
apart.** Read forwards, `office_authorizes_seven` is a single fact; read through
`authorized_iff` it is the three separate ones, and a safety argument that has
checked only some of them can see which it is missing.
-/
public theorem office_seven_three_conditions :
    office.Recognized 7 1 ∧ office.setting.norms.permitted 7 ∧ office.setting.possible 7 :=
  (Institution.authorized_iff office 7 1).mp office_authorizes_seven

/-- **And permission alone**, through the projection rather than by reaching
into the conjunction. The distinction this file exists for is that recognition
does not give permission; the converse projection is what says authorization
does. -/
public theorem office_seven_permitted : office.setting.norms.permitted 7 :=
  Institution.permitted_of_authorized office office_authorizes_seven

/-! ## Nothing bootstraps -/

/-- Two rules that cite only each other. -/
@[expose] public def loopRules : List (ConstitutiveRule (Fin 8) (Fin 2)) :=
  [ { premises := [1], trigger := fun _ => True, conclusion := 0 },
    { premises := [0], trigger := fun _ => True, conclusion := 1 } ]

/-- **An ungrounded cycle installs no authority.** With no ground facts, the two
rules derive nothing at all, however often they fire each other. -/
public theorem loop_derives_nothing (e : Fin 8) :
    ∀ f, ¬ Derives loopRules (fun _ => False) e f := by
  refine no_authority_from_ungrounded_cycles loopRules e ?_
  intro r hr
  simp only [loopRules, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨1, by simp⟩
  · exact ⟨0, by simp⟩

/-! ## The counts-as warning, at this institution -/

/-- **`RI` holds here** — every fact counts as itself — and Jones and Sergot
reject it at p. 433. -/
public theorem office_countsAs_refl (a : Fin 2) : CountsAs office.rules 7 a a :=
  countsAs_refl _ _ _

/-- **`PTR` holds here** too, and they reject it at p. 435. Together these are
why `CountsAs` must not be cited as their connective. -/
public theorem office_countsAs_trans (a b c : Fin 2)
    (hab : CountsAs office.rules 7 a b) (hbc : CountsAs office.rules 7 b c) :
    CountsAs office.rules 7 a c :=
  countsAs_trans hab hbc

/-- **Both at once, which is the actual objection.** Jones and Sergot reject
reflexivity and transitivity *of the same connective*; either alone is
unremarkable. The packaged form is what an argument citing their paper has to
confront, and it holds at this institution without any rule being chosen to make
it hold. -/
public theorem office_countsAs_validates_both :
    (∀ a : Fin 2, CountsAs office.rules 7 a a) ∧
      (∀ a b c : Fin 2, CountsAs office.rules 7 a b → CountsAs office.rules 7 b c →
        CountsAs office.rules 7 a c) :=
  countsAs_validates_refl_and_trans office.rules 7

/-! ## Widening the ground facts -/

/-- **Nothing is lost by admitting more ground facts.** What the office derives
from the filed request it still derives when everything is taken as given, which
is the monotonicity every argument about adding evidence to an institution
needs. Stated at this institution so the hypothesis is inhabited: the derivation
on the left is `office_recognizes_mandate`. -/
public theorem office_recognizes_mandate_under_wider_base :
    Derives office.rules (fun _ => True) 7 1 :=
  derives_mono_base (fun _ _ => trivial) office_recognizes_mandate

end AISafetyAtlas.Examples.Sovereignty.Institution
