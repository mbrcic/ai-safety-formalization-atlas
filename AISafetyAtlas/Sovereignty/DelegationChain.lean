module

public import AISafetyAtlas.Sovereignty.Quantifiers

/-!
# Power over a party is not power over what that party settles

**This module is a bridge**, in the sense of
[`ledger-coverage.md`](../../docs/agent/policy/ledger-coverage.md)'s four layers:
*(1) math theorem → (2) atlas interface → **(3) AI-safety bridge** → (4)
real-system claim*. Layer 2 is `AISafetyAtlas.Sovereignty.Quantifiers` and the effectivity layer
beneath it, which are
about coalitions, strategies and effectivity and mentions no AI system. What is
added here is the reading as an **assurance chain**, and the general obstruction
behind the concrete refutation in
`AISafetyAtlas.Examples.Sovereignty.Authority`.

## The question

Assurance is delegated and re-delegated. A deployer relies on a vendor, the
vendor on a model provider, the provider on a data supplier; an accountability
framework names a responsible party who relies on someone else for the thing it
is accountable for. The move being made is: *A has power over B, B has power over
the outcome, therefore A has power over the outcome.*

## What is stated

`not_forces_of_free_coordinate` is the general obstruction. If, for **every**
commitment a coalition can make, some completion of the profile still moves a
coordinate of the outcome off a target, then the coalition does not force that
coordinate — whatever it holds elsewhere. The hypothesis is the definition of the
coordinate being free of the coalition, and it is stated as a hypothesis rather
than derived, because whether a real chain leaves a coordinate free is precisely
the contestable question.

`power_over_a_matter_does_not_compose` is the reading: power over one matter and
another party's power over a second matter need not combine into power over the
second — where every commitment of the first party leaves the second matter free,
it does not force it. Power-over is relative to a matter; dropping the matter is what makes the
composition look valid.

`AISafetyAtlas.Examples.Sovereignty.Authority`'s `split` is the witness that the
hypothesis is inhabited and the conclusion is not vacuous —
`split_opponent_forces_fst`, `split_principal_forces_snd` and
`split_opponent_not_forces_snd` are the three halves at a concrete game.

## What this does not claim

The atlas has **no contract, no vendor and no assurance artifact.** This says
nothing about whether any real chain leaves a coordinate free; it says that if
one does, no amount of power elsewhere in the chain reaches it, and that the
composition step needs its own justification each time.

A chain in which the upstream party *does* control the downstream matter — by
contract with a remedy that actually binds, by holding the key, by being able to
withdraw the input — is not an instance. That is the useful form: the property an
accountability framework must establish is control of the specific matter, not
control of the party.

Nothing here is about blame, responsibility or liability, none of which is
modelled. Identifying a coalition with any real party is layer 4 and is not done
here.
-/

namespace AISafetyAtlas.Sovereignty.DelegationChain

universe u v w y

variable {N : Type u} {X : Type v} {Y : Type y}

/--
**A coordinate no commitment of the coalition reaches is not forced by it.**

The hypothesis says: whatever the coalition commits to, the rest of the profile
can still be completed so that the second coordinate misses `w`. That is what it
means for the coordinate to be free of this coalition, and under it the coalition
does not force the coordinate however much else it controls.

Stated for a product outcome because "a matter" is a coordinate of what happens:
the same play settles several things at once, and power is held over some of them
and not others.
-/
public theorem not_forces_of_free_coordinate
    (G : GameForm.{u, max v y, w} N (X × Y)) (C : Set N) (y₀ : Y)
    (hfree : ∀ sC : ∀ i : C, G.strategy i, ∃ s : ∀ i, G.strategy i,
      (∀ i : C, s i = sC i) ∧ (G.outcome s).2 ≠ y₀) :
    ¬ Forces G C (Prod.snd ⁻¹' {y₀}) := by
  rintro ⟨sC, hsC⟩
  obtain ⟨s, hagree, hne⟩ := hfree sC
  exact hne (hsC s hagree)

/--
**Power over a matter does not compose along a chain.**

`C` settles the first matter, `D` settles the second, and `C` does not settle the
second. So from "`C` has power over what `D` does" and "`D` has power over the
outcome" nothing follows about `C` and the outcome: the two arrows are about
different matters and the composition is not available.

All three conjuncts are stated together because each alone is misleading. The
first two are what an assurance chain documents; the third is what it is taken to
establish.
-/
public theorem power_over_a_matter_does_not_compose
    (G : GameForm.{u, max v y, w} N (X × Y)) (C D : Set N) (x₀ : X) (y₀ : Y)
    (hfst : Forces G C (Prod.fst ⁻¹' {x₀}))
    (hsnd : Forces G D (Prod.snd ⁻¹' {y₀}))
    (hfree : ∀ sC : ∀ i : C, G.strategy i, ∃ s : ∀ i, G.strategy i,
      (∀ i : C, s i = sC i) ∧ (G.outcome s).2 ≠ y₀) :
    Forces G C (Prod.fst ⁻¹' {x₀}) ∧ Forces G D (Prod.snd ⁻¹' {y₀}) ∧
      ¬ Forces G C (Prod.snd ⁻¹' {y₀}) :=
  ⟨hfst, hsnd, not_forces_of_free_coordinate G C y₀ hfree⟩

/--
**The repair, stated as the hypothesis an accountability framework must
discharge — and note what it is not.**

It is not enough that each matter is separately within the coalition's reach.
`forces_inter_of_shared_footprint` needs **one** commitment whose outcomes lie in
both targets, and two separate `Forces` may be witnessed by two different
commitments that cannot be played at once. That is the same distinction
`AISafetyAtlas.Sovereignty.Conformity` draws between passing each item of a
checklist and being operable, arriving here from the delegation side.

So the missing ingredient is never more authority over the *party*; it is a
single commitment that reaches the *matter*, and exhibiting one is a claim about
the specific mechanism.
-/
public theorem forces_both_of_shared_commitment
    (G : GameForm.{u, max v y, w} N (X × Y)) (C : Set N) (x₀ : X) (y₀ : Y)
    {sC : ∀ i : C, G.strategy i}
    (hfst : outcomesOf G C sC ⊆ Prod.fst ⁻¹' {x₀})
    (hsnd : outcomesOf G C sC ⊆ Prod.snd ⁻¹' {y₀}) :
    Forces G C ((Prod.fst ⁻¹' {x₀}) ∩ (Prod.snd ⁻¹' {y₀})) :=
  forces_inter_of_shared_footprint hfst hsnd

end AISafetyAtlas.Sovereignty.DelegationChain
