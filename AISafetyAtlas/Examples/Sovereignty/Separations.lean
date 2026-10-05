module

public import AISafetyAtlas.Sovereignty.Separations
public import AISafetyAtlas.Sovereignty.Mandate

/-!
# A worked delegation, and where each reading lands

`AISafetyAtlas.Sovereignty.Separations` proves the three readings of delegated
authority are inequivalent. That is a statement about *some* game form; this file
exhibits one, with a mandate that is a genuine proper subset of the outcomes
rather than everything or a single point.

Three outcomes and the mandate `{0, 1}` is the smallest setting in which the
readings visibly come apart: with two outcomes and a singleton mandate, "force
the mandate" and "force a specific outcome" coincide, and the distinction the
note turns on disappears.

## What each witness is for

| Witness | Shows |
|---|---|
| `retainsWith_delegated` | reading 1 holds — principal and delegate *together* keep the mandate |
| `not_retainsAgainst_delegated` | reading 2 fails — the delegate alone can leave it |
| `retainsUnder_delegated_zero` | reading 3 holds at one fixed policy |
| `not_retainsUnder_delegated_two` | and fails at another, so reading 3 is a claim about the policy, not about the principal |
| `retainsAgainst_undelegated` | the baseline: acting directly, the principal keeps the mandate outright |
| `sovereignty_lost_on_delegation` | the SOV-1 comparison instantiated — held before, not held after, under reading 2 |
| `not_retainsWith_empty` | the vacuous end: no coalition forces an empty mandate, so these witnesses are not passing for free |

The last row matters for the same reason `repeatedColumn` matters in
`Examples/Control/RegulationCheck.lean`. A file containing only successes leaves
a reader unable to tell an informative region from one where everything holds.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-- The mandate: a proper, non-empty subset of the three outcomes. -/
@[expose, reducible] public def mandate : Set (Fin 3) := {0, 1}

/-- Membership in the worked mandate is decidable, which is what lets the
readings below close by `decide` rather than by hand. -/
public instance : ∀ x : Fin 3, Decidable (x ∈ mandate) := fun x ↦ by
  unfold mandate; infer_instance

/-- The delegated game: the delegate (`true`) names the outcome. -/
@[expose, reducible] public def delegated : GameForm.{0, 0, 0} Bool (Fin 3) where
  strategy _ := Fin 3
  outcome s := s true

/-- The baseline game: the principal (`false`) names the outcome itself. -/
@[expose, reducible] public def undelegated : GameForm.{0, 0, 0} Bool (Fin 3) where
  strategy _ := Fin 3
  outcome s := s false

/-! ## The three readings on this game -/

/-- **Reading 1 holds.** With the delegate inside the coalition, the mandate is
forced — the guarantee is bought with the delegate's cooperation. -/
public theorem retainsWith_delegated :
    RetainsWith delegated false true mandate := by decide

/-- **Reading 2 fails.** The principal acting alone cannot stop the delegate
choosing `2`, which is outside the mandate. -/
public theorem not_retainsAgainst_delegated :
    ¬ RetainsAgainst delegated false mandate := by decide

/-- **Reading 3 holds at one policy.** -/
public theorem retainsUnder_delegated_zero :
    RetainsUnder delegated true (0 : Fin 3) mandate := by decide

/-- **And fails at another.** Reading 3 is a claim about which policy was fixed,
not about what the principal can do. -/
public theorem not_retainsUnder_delegated_two :
    ¬ RetainsUnder delegated true (2 : Fin 3) mandate := by decide

/-! ## The comparison SOV-1 asks for -/

/-- **The baseline.** Acting directly, the principal forces the mandate against
anything the other player does. -/
public theorem retainsAgainst_undelegated :
    RetainsAgainst undelegated false mandate := by decide

/--
**SOV-1 instantiated, and failing.**

Under reading 2 — the delegate is in the complement, so the guarantee must
survive its deviation — this principal held the mandate before delegating and
does not hold it after. The mandate is in `E₀(p)` and not in `E₁(p)`, which is
exactly the inclusion `E₀ ∩ 𝒜 ⊆ E₁ ∩ 𝒜` failing at one point.
-/
public theorem sovereignty_lost_on_delegation :
    RetainsAgainst undelegated false mandate ∧
      ¬ RetainsAgainst delegated false mandate :=
  ⟨retainsAgainst_undelegated, not_retainsAgainst_delegated⟩

/-! ## The vacuous end -/

/-- **No coalition forces an empty mandate**, so the witnesses above are not
holding for free. -/
public theorem not_retainsWith_empty :
    ¬ RetainsWith delegated false true (∅ : Set (Fin 3)) := by
  rintro ⟨sC, hsC⟩
  exact hsC (fun b => sC ⟨b, by cases b <;> simp⟩) (fun i => by
    obtain ⟨b, hb⟩ := i
    rfl)

/-! ## SOV-1, and the alignment that selects the coalition

`AISafetyAtlas.Sovereignty.SOV1` fixes the delegated coalition by the delegate's
alignment rather than by choice. On this pair of games the two settings of that
parameter give opposite verdicts, so the parameter is load-bearing and not a
relabelling of one obligation.
-/

/-- **The mandate is retained by the pair.** The antecedent of
`sov1_of_aligned`, worked at this pair of games: the mandate was in the
baseline effectivity of the principal alone, and `retainsWith_delegated` puts
it in the delegated effectivity of the principal and the delegate together. -/
public theorem retainsFamily_delegated_pair :
    RetainsFamily undelegated delegated {false} {false, true} {mandate} := by
  intro A hA _
  rw [Set.mem_singleton_iff] at hA
  subst hA
  exact retainsWith_delegated

/-- **With an aligned delegate the mandate survives delegation.**

Stated through `sov1_of_aligned` rather than by unfolding `SOV1`, which is what
makes this an instance of that lemma rather than a parallel proof of the same
fact. Unfolding proves the same thing and leaves the lemma untested: nothing
would have noticed if `principalCoalition_of_aligned` named a coalition no
mandate could be retained by. -/
public theorem sov1_aligned :
    SOV1 undelegated delegated false true True {mandate} :=
  (sov1_of_aligned trivial).mpr retainsFamily_delegated_pair

/-- **With an unaligned delegate it does not.** The coalition is the principal
alone, the mandate was in the baseline effectivity, and it is not in the
delegated one. -/
public theorem not_sov1_unaligned :
    ¬ SOV1 undelegated delegated false true False {mandate} := fun h =>
  not_retainsAgainst_delegated
    ((sov1_of_unaligned not_false).mp h mandate rfl retainsAgainst_undelegated)

/--
**So alignment is what the guarantee turns on.** The same principal, the same
mandate and the same two games: the obligation holds if the delegate acts for
the principal and fails if it does not.

This is why `sov1_of_retainsFamily_singleton` matters. Its hypothesis is the
failing side here, so anything that discharges SOV-1 without assuming alignment
discharges it under every alignment -- and on these games nothing does, which is
the honest reading of `sovereignty_lost_on_delegation`.
-/
public theorem sov1_turns_on_alignment :
    SOV1 undelegated delegated false true True {mandate} ∧
      ¬ SOV1 undelegated delegated false true False {mandate} :=
  ⟨sov1_aligned, not_sov1_unaligned⟩

/-- **Reading 3 at the family level, on the same pair.** The pinned policy `0`
lands in the mandate, so retention through a fixed delegate policy holds where
retention against the delegate fails. -/
public theorem retainsUnderFamily_delegated_zero :
    RetainsUnderFamily undelegated delegated {false} true (0 : Fin 3) {mandate} := by
  intro A hA _
  rw [Set.mem_singleton_iff] at hA
  subst hA
  exact retainsUnder_delegated_zero

/-- And fails at the policy `2`, so the family form inherits the same
policy-dependence reading 3 has at a single target. -/
public theorem not_retainsUnderFamily_delegated_two :
    ¬ RetainsUnderFamily undelegated delegated {false} true (2 : Fin 3) {mandate} := by
  intro h
  exact not_retainsUnder_delegated_two (h mandate rfl retainsAgainst_undelegated)


/-! ## Every separation lemma, applied

`AISafetyAtlas.Sovereignty.Separations` proves thirty-three results that nothing
in the tree instantiated. Each is applied once below, on the worked models the
library already builds -- `vetoGame`, `delegateDecides`, `pinnedForm`,
`principalDecides`, `dominatedForm`, `triadGame`, `matchGame` -- or on
`undelegated`/`delegated` above. Several are trivial as facts about these games;
what they establish is that the hypotheses are inhabited, which the build cannot
otherwise see.
-/

/-- The already-closed separations, named so the build depends on them. -/
public theorem separations_concrete :
    MForces matchGame {true} ∧ ¬ MForces matchGameBlind {true} ∧
      HasPowerOver vetoGame {false} {true} {true} ∧
      RetainsWith delegateDecides false true {true} ∧
      RetainsUnder delegateDecides true true {true} ∧
      ¬ RetainsUnder delegateDecides true false {true} :=
  ⟨matchGame_forces, matchGameBlind_not_forces, vetoGame_hasPowerOver,
    retainsWith_delegateDecides, retainsUnder_delegateDecides,
    not_retainsUnder_delegateDecides⟩

/-- The mediated factorization and the environment-dependence pair. -/
public theorem separations_mediated_and_env :
    (matchGameBlind.obs) = (fun _ => ()) ∘ matchGame.obs ∧
      (HasPowerOverEnv triadGame {0} {1} aligned {true} ∧
        ¬ HasPowerOverEnv triadGame {0} {1} neutral {true}) :=
  ⟨matchGameBlind_factors, power_depends_on_environment⟩

/-- `ForcesGiven` can hold vacuously, and the `Env`-indexed form collapses to it
at the trivial environment. `ForcesGivenEnv.mono_env` then weakens that
environment, which is monotone in the direction a smaller environment is easier. -/
public theorem separations_forcesGiven :
    ForcesGivenEnv vetoGame {false} (fun _ => true) {false} (fun _ => True)
      (∅ : Set Bool) ∧
    ForcesGivenEnv vetoGame {false} (fun _ => true) {false} (fun _ => False)
      (∅ : Set Bool) :=
  have h := forcesGivenEnv_true_iff.mpr forcesGiven_vacuous_of_overlap
  ⟨h, ForcesGivenEnv.mono_env h (fun _ hs => hs.elim)⟩

/-- The pinned form gives the principal exactly one outcome, so it has actual
power over the singleton and not over the pair -- and `ActualPower.forces` and
`actualPower_iff` read that fact two more ways. -/
public theorem separations_pinned :
    ActualPower (pinnedForm (0 : Fin 3)) {false} {0} ∧
      Forces (pinnedForm (0 : Fin 3)) {false} {0} ∧
      (∃ sC, outcomesOf (pinnedForm (0 : Fin 3)) {false} sC = {0}) ∧
      Forces (pinnedForm (0 : Fin 3)) {false} {0, 1} ∧
      ¬ ActualPower (pinnedForm (0 : Fin 3)) {false} {0, 1} :=
  have hp := pinned_actualPower_singleton (0 : Fin 3)
  ⟨hp, ActualPower.forces hp, actualPower_iff.mp hp,
    pinned_forces_pair (0 : Fin 3) 1,
    pinned_not_actualPower_pair (by decide : (1 : Fin 3) ≠ 0)⟩

/-- Both players' strategy sets in `dominatedForm (Fin 3)` are `Fin 3`, which is
inhabited; `forces_univ` asks for that and nothing registers it automatically. -/
public instance : ∀ i : Bool, Nonempty ((dominatedForm (Fin 3)).strategy i) :=
  fun _ => ⟨(0 : Fin 3)⟩

/-- In the dominated form the pusher forces every singleton, so the dominated
player forces only the whole space. -/
public theorem separations_dominated :
    Forces (dominatedForm (Fin 3)) {true} {0} ∧
      Forces (dominatedForm (Fin 3)) {false} Set.univ ∧
      (Set.univ : Set (Fin 3)) = Set.univ :=
  ⟨pusher_forces_singleton 0, Sovereignty.forces_univ {false},
    dominated_forces_univ (Sovereignty.forces_univ {false})⟩

/-- The principal decides, so it forces every singleton and hence -- by
`forces_of_forces_singletons` -- every nonempty target. -/
public theorem separations_principalDecides :
    Forces (principalDecides (Fin 3)) {false} {0, 1} :=
  have hall : ∀ x : Fin 3, Forces (principalDecides (Fin 3)) {false} {x} := by
    intro x
    obtain ⟨y, hy⟩ := exists_ne x
    exact (minCard_cannot_separate y x (Ne.symm hy)).2.2.2
  forces_of_forces_singletons hall ⟨0, by simp⟩

/-- Minimum cardinality does not separate the two forms. -/
public theorem separations_minCard :
    (∃ y : Fin 3, Forces (pinnedForm (0 : Fin 3)) {false} {y}) ∧
      (∃ y : Fin 3, Forces (principalDecides (Fin 3)) {false} {y}) ∧
      (¬ Forces (pinnedForm (0 : Fin 3)) {false} {1}) ∧
      Forces (principalDecides (Fin 3)) {false} {1} :=
  minCard_cannot_separate (0 : Fin 3) 1 (by decide)

/-- Structural power lives across a family and not inside any one game, and
`hasStructuralPower_iff_not_robustly` reads the same fact as a conjunction. -/
public theorem separations_structural :
    HasStructuralPower (configFamily (0 : Fin 3) 1) {false} {1} ∧
      ((∃ k, Forces (configFamily (0 : Fin 3) 1 k) {false} {1}) ∧
        ¬ RobustlyForces (configFamily (0 : Fin 3) 1) {false} {1}) :=
  have h := (structuralPower_not_within_game (by decide : (1 : Fin 3) ≠ 0)).1
  ⟨h, hasStructuralPower_iff_not_robustly.mp h⟩

/-- `HasPowerOver` over the veto game, read through the effectivity form. -/
public theorem separations_hasPowerOver_iff :
    ∃ sC sC' : ∀ i : ({false} : Set Bool), vetoGame.strategy i,
      effectivityGiven vetoGame {false} sC {true}
        ≠ effectivityGiven vetoGame {false} sC' {true} :=
  (hasPowerOver_iff_effectivityGiven_ne (by simp)).mp ⟨{true}, vetoGame_hasPowerOver⟩

/-- The baseline forcing fact, carried through the monotonicity and arena
readings, and used to refute power over the principal's own coalition. -/
public theorem separations_forces_readings :
    Forces undelegated {false} (Set.univ : Set (Fin 3)) ∧
      (gameArena undelegated {false}).Forces mandate ∧
      ¬ HasPowerOver undelegated {true} {false} mandate :=
  have h : Forces undelegated {false} mandate := retainsAgainst_undelegated
  ⟨Forces.mono h (Set.subset_univ _), forces_iff_gameArena_forces.mp h,
    not_hasPowerOver_of_forces h⟩

/-- Widening the coalition keeps the guarantee, and reading 2 implies reading 1
at any delegate. -/
public theorem separations_coalition_readings :
    Forces undelegated Set.univ mandate ∧ RetainsWith undelegated false true mandate :=
  ⟨Forces.mono_coalition retainsAgainst_undelegated (Set.subset_univ _),
    retainsAgainst_imp_retainsWith retainsAgainst_undelegated⟩

/-- A larger coalition fixes at least as much, so its outcome set is smaller. -/
public theorem separations_outcomesOf_anti :
    outcomesOf undelegated Set.univ (fun _ => (0 : Fin 3))
      ⊆ outcomesOf undelegated {false} (fun _ => (0 : Fin 3)) :=
  outcomesOf_anti_coalition (Set.subset_univ _) _ _ (fun _ => rfl)

/-- The mediated form's arena reading, on the game that does force, plus the two
readings that widen it. `mforces_of_factors` is applied at the identity
factoring: `matchGameBlind_factors` is the interesting instance of that equation
but the blind game does not force `{true}`, so it cannot supply the second
premise, and the honest instance here is the trivial one. -/
public theorem separations_mforces_arena :
    matchGame.toArena.Forces {true} ∧ MForces matchGame Set.univ ∧
      MForces ⟨matchGame.obs, matchGame.result⟩ {true} :=
  ⟨mforces_iff_toArena_forces.mp matchGame_forces,
    MForces.mono matchGame_forces (Set.subset_univ _),
    mforces_of_factors (k := id) rfl matchGame_forces⟩

/-- A family that forces robustly forces at every index; the config family does
not, which is what `separations_structural` records, so the instance here is the
constant family built from a game that forces. -/
public theorem separations_robustlyForces :
    Forces undelegated {false} mandate :=
  RobustlyForces.forces (Γ := fun _ : Bool => undelegated)
    (fun _ => retainsAgainst_undelegated) true

end AISafetyAtlas.Examples.Sovereignty
