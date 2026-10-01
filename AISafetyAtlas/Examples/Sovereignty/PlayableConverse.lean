module

public import AISafetyAtlas.Sovereignty.PlayableConverse

/-!
# Playable is strictly weaker than realizable

`PlayableConverse` states Pauly's five conditions as `Playable` and shows the
converse half of his Theorem 3.2 fails. This file runs both sides on concrete
objects, so the separation is between two inhabited classes rather than between
two predicates.

* `vetoGame` is a game, so its effectivity function is playable -- the easy
  direction, instantiated.
* `cofiniteEff` is playable and is **no game's** effectivity function. This is
  Goranko, Jamroga and Turrini's counterexample (JAAMAS 26: 288-314, 2013), not
  this atlas's; see the module header of `PlayableConverse`.

Both examples are needed. Without the first, `Playable` could be a condition
nothing satisfies; without the second, it could be one that only games satisfy.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-! ## A game, hence playable -/

/-- Both players always have a move, which is what liveness reads. -/
public instance (i : Bool) : Nonempty (vetoGame.strategy i) := ⟨true⟩

/-- The veto game's effectivity function satisfies every condition on Pauly's
page-152 list. -/
public theorem vetoGame_playable : Playable (effectivity vetoGame) :=
  playable_effectivity

example : (∅ : Set Bool) ∉ effectivity vetoGame {true} := vetoGame_playable.live _

/-- Lemma 3.1 running on it: the two players cannot both force complementary
sets. -/
example {A : Set Bool} (h : A ∈ effectivity vetoGame {true}) :
    Aᶜ ∉ effectivity vetoGame ({true} : Set Bool)ᶜ :=
  vetoGame_playable.regular h

/-- Lemma 3.1's other half: growing the coalition never loses power. -/
example : effectivity vetoGame {true} ⊆ effectivity vetoGame Set.univ :=
  vetoGame_playable.mono_coalition (Set.subset_univ _)

/-- Superadditivity over a finite family, which is what page 153's Claim needs.
The two singleton coalitions of `vetoGame` are a partition of its player set, and
whatever each forces, the grand coalition forces the intersection. -/
example (A : Bool → Set Bool) (h : ∀ b, A b ∈ effectivity vetoGame {b}) :
    (⋂ b, A b) ∈ effectivity vetoGame (⋃ b, ({b} : Set Bool)) :=
  vetoGame_playable.iInter_mem (fun b => ({b} : Set Bool)) A
    (fun _ _ hij => Set.disjoint_singleton.mpr hij) h

/-! ## Playable, and no game's

`cofiniteEff` passes every condition and still fails to be an effectivity
function of any game form, because `effectivity G ∅` always has a least element
and the cofinite filter has none. This is the counterexample to the left-to-right
direction of Theorem 3.2.
-/

example : Playable cofiniteEff := cofiniteEff_playable

example : ¬ ∃ G : GameForm.{0, 0, 0} Unit ℕ, effectivity G = cofiniteEff :=
  not_exists_gameForm_cofiniteEff

/-- The separation, in one statement: some playable effectivity function is no
game form's. -/
public theorem exists_playable_not_effectivity :
    ∃ E : Set Unit → Set (Set ℕ),
      Playable E ∧ ∀ G : GameForm.{0, 0, 0} Unit ℕ, effectivity G ≠ E :=
  ⟨cofiniteEff, cofiniteEff_playable,
    fun G hG => not_exists_gameForm_cofiniteEff ⟨G, hG⟩⟩

/-! ## The construction, run

`paulyGame` rebuilds a game from an effectivity function. Run on a game's own
effectivity function it must give back the same power structure -- and it does,
at every coalition that is neither empty nor everybody. On `vetoGame` those are
the two singletons.
-/

/-- The rebuilt veto game has exactly the veto game's power at each singleton
coalition. Both of print's side conditions are met there. -/
public theorem vetoGame_paulyGame_eq (b : Bool) :
    effectivity (paulyGame vetoGame_playable) ({b} : Set Bool)
      = effectivity vetoGame ({b} : Set Bool) :=
  vetoGame_playable.effectivity_paulyGame_eq ⟨b, rfl⟩ (by
    intro h
    have hb : (!b) ∈ ({b} : Set Bool) := by rw [h]; trivial
    exact Bool.not_ne_self b hb)

/-- Neither player can force the good outcome alone in the rebuilt game either,
which is `Separations`' `vetoGame_not_forces` transported across the
construction. -/
example : ({true} : Set Bool) ∉ effectivity (paulyGame vetoGame_playable) ({true} : Set Bool) := by
  rw [vetoGame_paulyGame_eq]
  exact vetoGame_not_forces

/-- The outcome of the rebuilt game always lies in print's `G(f)`. -/
example (σ : ∀ i, Strat (effectivity vetoGame) i) :
    (paulyGame vetoGame_playable).outcome σ ∈ outcomeSet σ :=
  paulyGame_outcome_mem vetoGame_playable σ

/-- One player can always make itself the one who picks, whatever the others
chose. Print's `t_{j₀}`. -/
example (j : Bool) (t : Bool → Bool) :
    ∃ t' : Bool → Bool, (∀ i, i ≠ j → t' i = t i) ∧ dictator t' = j :=
  exists_dictator_eq j t

/-! ## Why the witness needs only one player

`Playable.effectivity_paulyGame_eq` asks for a coalition that is neither empty
nor everybody. On one player there is no such coalition, so on `cofiniteEff` the
construction says nothing at all -- and `not_exists_gameForm_cofiniteEff` says
nothing could.
-/

public theorem no_middle_coalition_on_one_player (C : Set Unit)
    (hne : C.Nonempty) (huniv : C ≠ Set.univ) : False :=
  huniv (unit_coalition_cases C |>.resolve_left (Set.nonempty_iff_ne_empty.mp hne))

/-! ## Lemma 3.1 and the choice functions, as named results

These two run above inside anonymous `example`s, which demonstrate but do not
ground: nothing the build can point at instantiates the hypotheses. Named here
so that the veto game is on record as an actual model of each. -/

/-- **Growing the coalition never loses power**, Lemma 3.1's second half at the
veto game. -/
public theorem vetoGame_mono_coalition :
    effectivity vetoGame {true} ⊆ effectivity vetoGame Set.univ :=
  Playable.mono_coalition vetoGame_playable (Set.subset_univ _)

/-- **And every player has a choice function**, which is what the converse
construction consumes. The constant function naming the whole outcome space is
one, and safety is what makes it legitimate. -/
public theorem vetoGame_nonempty_choiceFn (i : Bool) :
    Nonempty (ChoiceFn (effectivity vetoGame) i) :=
  Playable.nonempty_choiceFn vetoGame_playable i

/-! ## Theorem 3.3 at print's own quantifier

The same witness that refutes Theorem 3.2 refutes Theorem 3.3, because print's
Theorem 3.3 quantifies over an arbitrary effectivity function and its right-hand
side asks for a game form.
-/

/-- `cofiniteEff` is individualistic in print's own sense: playable, and on one
player the union over individuals is the grand coalition's own power. -/
example : IndividualisticEff cofiniteEff := cofiniteEff_individualisticEff

/-- **The separation for Theorem 3.3**, in the shape print's sentence has: some
individualistic effectivity function is no dictatorship's, because it is no game
form's. -/
public theorem exists_individualisticEff_not_dictatorship :
    ∃ E : Set Unit → Set (Set ℕ),
      IndividualisticEff E ∧
        ∀ (G : GameForm.{0, 0, 0} Unit ℕ) (d : Unit),
          IsDictator G d → effectivity G ≠ E :=
  ⟨cofiniteEff, cofiniteEff_individualisticEff,
    fun G _ _ hG => not_exists_gameForm_cofiniteEff ⟨G, hG⟩⟩

/-- Print's Theorem 3.3, read at print's quantifier, is false. -/
example : ¬ ∀ E : Set Unit → Set (Set ℕ), IndividualisticEff E →
    ∃ (G : GameForm.{0, 0, 0} Unit ℕ) (d : Unit), IsDictator G d ∧ effectivity G = E :=
  not_forall_individualisticEff_exists_dictator

/-- And already without the word *dictatorship*: the witness is outside the
range of `effectivity`, so no reading of print's right-hand side saves it. -/
public theorem not_forall_individualisticEff_exists_gameForm_zero :
    ¬ ∀ E : Set Unit → Set (Set ℕ), IndividualisticEff E →
        ∃ G : GameForm.{0, 0, 0} Unit ℕ, effectivity G = E :=
  not_forall_individualisticEff_exists_gameForm

/-- **On a game form the two readings of *individualistic* agree**, at the veto
game: print's playability conjunct is free there. -/
public theorem vetoGame_individualisticEff_iff :
    IndividualisticEff (effectivity vetoGame) ↔ Individualistic vetoGame :=
  individualisticEff_effectivity_iff

end AISafetyAtlas.Examples.Sovereignty
