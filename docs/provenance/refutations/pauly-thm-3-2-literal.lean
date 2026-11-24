import AISafetyAtlas.Sovereignty.PlayableConverse
import AISafetyAtlas.Sovereignty.TrulyPlayableRepresentation

/-!
# Pauly's Theorem 3.2 construction as printed is false; the finite-outcome repair holds

Marc Pauly, *A Modal Logic for Coalitional Power in Games*, J. Logic Computat. 12(1),
2002, proof of Theorem 3.2, pp. 152--154 (PDF pp. 4--6; audit row S15-R06):

    [...] let E be an effectivity function satisfying the five properties.
    We shall construct a game G such that E = E_G. To simplify our
    definitions, assume that N = {1, ..., n}. [...]

(Transcribed from the page images in
`docs/provenance/printed-statements/pauly-2002-coalition-logic.yaml`, entry
`pauly-thm-3.2-construction`.) The five properties are playability (p. 152): (1)
`∅ ∉ E(C)`, (2) `S ∈ E(C)`, (3) `N`-maximality, (4) outcome-monotonicity, (5)
superadditivity; the library's `AISafetyAtlas.Sovereignty.Playable` is that list in
print's order. A strategic game (p. 150) has "a non-empty finite set of agents or
players `N`, a non-empty set of strategies or actions `Σ_i` for every player
`i ∈ N`, a non-empty set of outcome states `S`" and an outcome function. Print
states no finiteness of `S` or of the `Σ_i` anywhere in §§2--3.1 (the yaml's
`standing` paragraph records the search), and says on p. 152 it wants to be "as
general as possible regarding the notion of an effectivity function".

So `S = ℕ` is inside print's hypotheses, and there the claim is false. The witness
is the library's `cofiniteEff`: one player, outcomes `ℕ`, the empty coalition
effective for the cofinite sets and the grand coalition for the infinite sets.
It is playable (`cofiniteEff_playable`), and no game form has it as its effectivity
function (`not_exists_gameForm_cofiniteEff`): a game form's `E_G(∅)` is the family
of supersets of its set of reachable outcomes, so it has a least element, and the
cofinite filter has none.

**This is not a new refutation.** It is the counterexample of Goranko, Jamroga and
Turrini, *Strategic Games and Truly Playable Effectivity Functions*, Autonomous
Agents and Multi-Agent Systems 26: 288--314 (2013), DOI `10.1007/s10458-012-9192-y`,
the proof of their Proposition 4 ("There is a playable effectivity function `E` for
which `E ≠ E^α_G` for all strategic games `G`"), read from the pinned author
manuscript (`docs/provenance/printed-statements/goranko-2013-truly-playable.yaml`,
entry `gjt-prop-4-counterexample`): the same single player over `ℕ` with
`E({a})` the infinite sets and `E(∅)` the cofinite ones, obstructed because "there
are no minimal cofinite sets". The library records the attribution at
`AISafetyAtlas.Sovereignty.PlayableConverse`.

Not proved here: Pauly's own game `G` fails even when `S` is finite. Goranko,
Jamroga and Turrini locate a second obstruction at the grand coalition: if every
player names `S` for every coalition and all use one selector returning `x`, the
outcome is `x`, so `{x} ∈ E_G(N)` even when `{x} ∉ E(N)`. The library's
`PlayableConverse` header records this and says it is not formalized; its
`Playable.effectivity_paulyGame_eq` proves `E_G(C) = E(C)` for Pauly's
construction only at coalitions other than `∅` and `N`.

**`repaired_holds`.** The repair is the finite-`S` representation theorem (every
playable `E` over finite `S` is some game's, at every coalition including `∅` and `N`),
which Goranko, Jamroga and Turrini reach through true playability. The library proves
it as `AISafetyAtlas.Sovereignty.Playable.exists_gameForm_of_finite` (added
2026-11-21): restrict `E` to the core of `E(∅)`, represent the restriction, and carry
the game back along the inclusion. Pauly's own game is still wrong at the grand
coalition (`Examples.Sovereignty.effectivity_paulyGame_pointEff_ne`); the repair needs
a different game, not only finiteness.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/pauly-thm-3-2-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md`.
-/

open AISafetyAtlas.Sovereignty

namespace PaulyThmThreeTwoLiteral

/-- The construction's claim exactly as printed: for a non-empty finite set of
players `N` and a non-empty set of outcome states `S`, every effectivity function
`E : P(N) → P(P(S))` satisfying the five properties is `E_G` for some strategic
game `G` with non-empty strategy sets. Strategy sets are sets, so `Type`. -/
def LiteralPrint : Prop :=
  ∀ (N S : Type) [Finite N] [Nonempty N] [Nonempty S] (E : Set N → Set (Set S)),
    Playable E →
      ∃ G : GameForm.{0, 0, 0} N S, (∀ i, Nonempty (G.strategy i)) ∧ effectivity G = E

/-- **The printed claim is false.** At one player over `ℕ`, `cofiniteEff` is
playable and no game form realises it, with or without non-empty strategy sets. -/
theorem not_literalPrint : ¬ LiteralPrint := by
  intro h
  obtain ⟨G, -, hG⟩ := h Unit ℕ cofiniteEff cofiniteEff_playable
  exact not_exists_gameForm_cofiniteEff ⟨G, hG⟩

/-- **The repaired claim holds**: the printed statement with a finite set of outcome
states. -/
theorem repaired_holds :
    ∀ (N S : Type) [Finite N] [Nonempty N] [Nonempty S] [Finite S] (E : Set N → Set (Set S)),
      Playable E →
        ∃ G : GameForm.{0, 0, 0} N S, (∀ i, Nonempty (G.strategy i)) ∧ effectivity G = E :=
  fun _ _ _ _ _ _ _ hE => Playable.exists_gameForm_of_finite hE

end PaulyThmThreeTwoLiteral
