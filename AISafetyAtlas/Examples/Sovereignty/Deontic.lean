module

public import AISafetyAtlas.Sovereignty.Deontic

/-!
# Eight acts that separate the three axes, and four that use all four statuses

Two finite witnesses, both checked by `decide`.

* `fourStatus` realizes **all four** norm statuses, so `Unclassified` and
  `Conflicted` are not empty and the two-annotation design is doing work rather
  than decorating a boolean.
* `cube` realizes **all eight** combinations of empowered, permitted and
  possible, which is what `Separated` asks for and therefore what Jones and
  Sergot's *"we distinguish institutionalised power from permission and
  practical possibility"* (p. 427) amounts to formally.

Both are bit patterns on an index, which is the cheapest way to make a
separation claim true by construction and checkable by evaluation.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Deontic

open AISafetyAtlas.Sovereignty

/-! ## All four statuses occur -/

/-- Bit 0 permits; bit 1 forbids. The two are independent by construction. -/
@[expose] public def fourStatus : NormSystem (Fin 4) where
  permitted := fun e => e.val % 2 = 1
  forbidden := fun e => 2 ≤ e.val

/-- Act `1` is permitted and not forbidden. -/
public theorem fourStatus_permitted : fourStatus.permitted 1 ∧ ¬ fourStatus.forbidden 1 := by
  unfold fourStatus
  decide

/-- Act `2` is forbidden and not permitted — **this is `may not`**, and it is
not the absence of permission, which act `0` has instead. -/
public theorem fourStatus_forbidden : fourStatus.forbidden 2 ∧ ¬ fourStatus.permitted 2 := by
  unfold fourStatus
  decide

/-- Act `0` is **unclassified**: the norms are silent, which is not the same as
forbidding it. -/
public theorem fourStatus_unclassified : fourStatus.Unclassified 0 := by
  unfold NormSystem.Unclassified fourStatus
  decide

/-- Act `3` is **conflicted**: the norms both permit and forbid it. -/
public theorem fourStatus_conflicted : fourStatus.Conflicted 3 := by
  unfold NormSystem.Conflicted fourStatus
  decide

/-- So this system is neither consistent nor complete, and both failures are
witnessed rather than assumed.

Each half goes **through** the library's characterisation rather than unfolding
the definition at the witness. This file did the latter until 2026-09-21, and the
cost was that `consistent_iff_no_conflicted` and `complete_iff_no_unclassified`
had no application anywhere: the two statements that say *consistency is the
absence of conflict* and *completeness is the absence of silence* were never
once used to conclude either. -/
public theorem fourStatus_neither :
    ¬ fourStatus.Consistent ∧ ¬ fourStatus.Complete :=
  ⟨fun h =>
     (NormSystem.consistent_iff_no_conflicted fourStatus).mp h 3 fourStatus_conflicted,
   fun h =>
     (NormSystem.complete_iff_no_unclassified fourStatus).mp h 0 fourStatus_unclassified⟩

/--
**The four statuses are a partition, and reading the exhaustiveness backwards is
what it is for.** An act on which the norms are neither silent nor
self-contradicting is decided one way or the other — so the two-valued reading
is available exactly there and not in general.
-/
public theorem fourStatus_decided_of_not_silent_not_conflicted {e : Fin 4}
    (hu : ¬ fourStatus.Unclassified e) (hc : ¬ fourStatus.Conflicted e) :
    (fourStatus.permitted e ∧ ¬ fourStatus.forbidden e) ∨
      (¬ fourStatus.permitted e ∧ fourStatus.forbidden e) := by
  rcases fourStatus.status_exhaustive e with h | h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact absurd h hu
  · exact absurd h hc

/-- And it is not vacuous: acts `1` and `2` satisfy the hypotheses and land in
the two different halves. The acts that do **not** satisfy them are `0` and `3`,
which are exactly the silent and the conflicted one. -/
public theorem fourStatus_decided_at_one_and_two :
    (fourStatus.permitted 1 ∧ ¬ fourStatus.forbidden 1) ∧
      (¬ fourStatus.permitted 2 ∧ fourStatus.forbidden 2) := by
  refine ⟨?_, ?_⟩
  · rcases fourStatus_decided_of_not_silent_not_conflicted (e := 1)
      (by unfold NormSystem.Unclassified fourStatus; decide)
      (by unfold NormSystem.Conflicted fourStatus; decide) with h | h
    · exact h
    · exact absurd fourStatus_permitted.1 h.1
  · rcases fourStatus_decided_of_not_silent_not_conflicted (e := 2)
      (by unfold NormSystem.Unclassified fourStatus; decide)
      (by unfold NormSystem.Conflicted fourStatus; decide) with h | h
    · exact absurd fourStatus_forbidden.1 h.2
    · exact h

/-- **The silent act is not forbidden.** The distinction the whole design
exists for, at a witness. -/
public theorem fourStatus_silence_is_not_prohibition : ¬ fourStatus.forbidden 0 :=
  fourStatus.not_forbidden_of_unclassified fourStatus_unclassified

/-! ## All eight combinations of the three axes occur -/

/-- Bit 0: institutionally empowered. -/
@[expose] public def empoweredBit (e : Fin 8) : Prop := e.val % 2 = 1

/-- Bit 1: permitted. -/
@[expose] public def permittedBit (e : Fin 8) : Prop := (e.val / 2) % 2 = 1

/-- Bit 2: practically possible. -/
@[expose] public def possibleBit (e : Fin 8) : Prop := (e.val / 4) % 2 = 1

/--
**Eight acts, one per combination.** `forbidden` is set to the complement of
`permitted` here only because this witness is about the *other* three axes;
`fourStatus` above is where the four statuses are exercised.
-/
@[expose] public def cube : InstitutionalSetting (Fin 8) where
  norms := { permitted := permittedBit, forbidden := fun e => ¬ permittedBit e }
  empowered := empoweredBit
  possible := possibleBit

/--
**Jones and Sergot's separation, witnessed.** Every combination of
institutionalised power, permission and practical possibility is realized.
-/
public theorem cube_separated : cube.Separated := by
  unfold InstitutionalSetting.Separated cube empoweredBit permittedBit possibleBit
  decide

/-- **An act can be empowered, possible, and forbidden.** The case a system that
checks only "can it be done" and "does it count" will miss. -/
public theorem cube_empowered_possible_not_permitted :
    ∃ e, cube.empowered e ∧ cube.possible e ∧ ¬ cube.norms.permitted e :=
  cube.exists_empowered_possible_not_permitted cube_separated

/-- **Ought-implies-can buys no permission**, at this witness. -/
public theorem cube_oughtImpliesCan_gives_no_permission :
    ∃ obligatory : Fin 8 → Prop,
      OughtImpliesCan obligatory cube.possible ∧
        ∃ e, obligatory e ∧ ¬ cube.norms.permitted e :=
  oughtImpliesCan_does_not_give_permission cube cube_separated

/--
**Where the classical reading is the right one, at a witness.** `cube` below sets
`forbidden` to `¬ permitted` by construction, so its norms are consistent and
complete — and the library's characterisation is what says so, rather than the
definition being unfolded. The point of having the theorem is that the collapse
is a *property* some norm systems have and `fourStatus` does not: the classical
two-valued reading is a special case here, not a rival design.
-/
public theorem cubeNorms_consistent_and_complete :
    (NormSystem.Consistent (cube.norms) ∧ NormSystem.Complete (cube.norms)) :=
  (NormSystem.forbidden_iff_not_permitted_iff cube.norms).mpr fun _ => Iff.rfl

/-- The two systems in this file sit on opposite sides of that characterisation:
one collapses to two statuses and the other uses all four. -/
public theorem collapse_is_not_automatic :
    (NormSystem.Consistent (cube.norms) ∧ NormSystem.Complete (cube.norms)) ∧
      ¬ (fourStatus.Consistent ∧ fourStatus.Complete) :=
  ⟨cubeNorms_consistent_and_complete, fun h => fourStatus_neither.1 h.1⟩

/-! ## The two implementations, at act 5 -/

/-- The acts this repository's `cube` would regiment: the unpermitted ones. -/
@[expose] public def unpermitted (e : Fin 8) : Prop := ¬ cube.norms.permitted e

/-- **Act `5` is the gap.** Empowered, possible, and not permitted — the case
`exists_empowered_possible_not_permitted` asserts abstractly. -/
public theorem five_is_the_gap :
    cube.empowered 5 ∧ cube.possible 5 ∧ ¬ cube.norms.permitted 5 := by
  unfold cube empoweredBit permittedBit possibleBit
  decide

/-- **Regimentation removes it.** Act `5` is no longer possible. -/
public theorem five_not_possible_after_regimenting :
    ¬ (cube.regiment unpermitted).possible 5 :=
  cube.not_possible_of_regimented (bad := unpermitted) five_is_the_gap.2.2

/-- **Enforcement does not.** Act `5` is still possible, and is now forbidden.

Both halves go **through** the library's axis lemmas rather than around them.
That is not style: this file proved the same conjunction by hand until
2026-09-21, unfolding `enforce` at the witness, and the effect was that
`enforce_possible` and `enforce_forbidden` had no application anywhere in the
tree — so nothing would have noticed if `enforce` had been defined to move
possibility after all. -/
public theorem five_still_possible_after_enforcing :
    (cube.enforce unpermitted).possible 5 ∧ (cube.enforce unpermitted).norms.forbidden 5 :=
  ⟨by rw [cube.enforce_possible unpermitted]; exact five_is_the_gap.2.1,
   (cube.enforce_forbidden unpermitted 5).mpr (Or.inr five_is_the_gap.2.2)⟩

/-! ## The axes the two implementations leave alone

`regiment` and `enforce` are the same prohibition through different means, and
the claim that they differ on **exactly one** axis is four `rfl` lemmas in the
library that nothing applied. Fired here at `cube`, so the claim is checked at a
setting where all three axes are genuinely independent rather than at a carrier
where the equalities could not fail. -/

/-- Neither implementation touches institutional power. -/
public theorem cube_power_untouched :
    (cube.regiment unpermitted).empowered = cube.empowered ∧
      (cube.enforce unpermitted).empowered = cube.empowered :=
  ⟨cube.regiment_empowered unpermitted, cube.enforce_empowered unpermitted⟩

/-- **Regimentation leaves the norms alone** — it removes the act instead of
recording anything about it, which is the whole objection to it. -/
public theorem cube_regiment_says_nothing :
    (cube.regiment unpermitted).norms = cube.norms :=
  cube.regiment_norms unpermitted

/-- **Enforcement leaves possibility and permission alone**, and adds a
prohibition. Grossi, Gabbay and van der Torre's printed `{R_a} = {R'_a}` is the
first of these. -/
public theorem cube_enforce_keeps_possibility_and_permission :
    (cube.enforce unpermitted).possible = cube.possible ∧
      (cube.enforce unpermitted).norms.permitted = cube.norms.permitted :=
  ⟨cube.enforce_possible unpermitted, cube.enforce_permitted unpermitted⟩

/-- **And the separation survives**, which is the axis claim: the empowered,
possible, unpermitted act is still there after enforcement, so the gap a safety
argument has to close has not been closed by fiat. -/
public theorem cube_enforce_separated : (cube.enforce unpermitted).Separated :=
  cube.enforce_separated (bad := unpermitted) cube_separated

/-- **Empowerment and permission are independent in both directions**, at this
witness: an act that counts but is not allowed, and one that is allowed but does
not count. -/
public theorem cube_power_and_permission_independent :
    (∃ e, cube.empowered e ∧ ¬ cube.norms.permitted e) ∧
      (∃ e, cube.norms.permitted e ∧ ¬ cube.empowered e) :=
  cube.exists_empowered_not_permitted cube_separated

/-- **And the separation survives enforcement and not regimentation**, at this
witness. -/
public theorem cube_regiment_vs_enforce :
    ¬ (cube.regiment (fun e => ¬ cube.norms.permitted e)).Separated ∧
      (cube.enforce (fun e => ¬ cube.norms.permitted e)).Separated :=
  cube.regiment_and_enforce_differ cube_separated

end AISafetyAtlas.Examples.Sovereignty.Deontic
