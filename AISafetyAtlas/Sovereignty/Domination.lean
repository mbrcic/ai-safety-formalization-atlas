module

public import AISafetyAtlas.Sovereignty.Authority
public import AISafetyAtlas.Sovereignty.Playability

/-!
# Blocking is not dominating, and failing is not being dominated

The proposal's §5.6 separates three things that a single word usually runs
together: that a party *can* block a demand, that its capacity to do so is
insufficiently constrained, and that the demand fails at all.

`Veto` is the first. `Dominates` is the first together with the second, and the
second is carried as an explicit `Prop` -- `Uncontrolled` -- for the same
reason the authority predicate is: the proposal says an authorized, constrained
guardian is not a dominator merely because it can interfere, and nothing in a
game form decides whether a capacity is constrained.

`not_forces_of_veto` is the bite: a veto held by everyone outside the coalition
refutes the coalition's guarantee outright. `not_dominates_of_controlled` is
the other side, and it is definitional -- which is the point, since it says the
whole weight of the word sits in the second conjunct.

`S6` is in `AISafetyAtlas.Examples.Sovereignty.Authority`: the simultaneous-bit
game, where the principal has no guarantee and nobody has a veto either. A
failure of sovereignty there is attributable to the interaction and to nothing
and nobody else, which is print's warning against relabelling every failure as
domination.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

variable {N : Type u} {X : Type v} {G : GameForm.{u, v, w} N X}

/--
**A veto.** The coalition `Y` can force the outcome out of the demand's success
set.
-/
@[expose] public def Veto (G : GameForm.{u, v, w} N X) (Y : Set N) (Φ : Set X) :
    Prop :=
  Forces G Y Φᶜ

/--
**Domination, in the proposal's §5.6 shape.** A veto whose exercise is not
constrained by the constitution.

`Uncontrolled` is an input and is never defined in this repository. Print is
explicit that it must not be: an authorized, constrained guardian that can
block a prohibited action is not thereby a dominator, and which constraints
count is a question about the constitution rather than about the game.
-/
@[expose] public def Dominates (G : GameForm.{u, v, w} N X) (Y : Set N)
    (Φ : Set X) (Uncontrolled : Prop) : Prop :=
  Veto G Y Φ ∧ Uncontrolled

/-- **A veto held by the complement refutes the guarantee.** The two cannot
both hold, so a demand a coalition genuinely enforces is one the rest cannot
block. -/
public theorem not_forces_of_veto [∀ i, Nonempty (G.strategy i)] {C : Set N}
    {Φ : Set X} (h : Veto G Cᶜ Φ) : ¬ Forces G C Φ :=
  fun hf => not_forces_compl_of_forces hf h

/-- Vetoes are downward closed in the demand: blocking a weaker demand blocks
every stronger one. -/
public theorem Veto.mono {Y : Set N} {Φ Ψ : Set X} (h : Veto G Y Φ)
    (hΨΦ : Ψ ⊆ Φ) : Veto G Y Ψ :=
  Forces.mono h (Set.compl_subset_compl.mpr hΨΦ)

/-- **A constrained guardian is not a dominator**, whatever it can block. The
proof is the definition, and that is the content: the word carries no weight
that the second conjunct does not supply. -/
public theorem not_dominates_of_controlled {Y : Set N} {Φ : Set X}
    {Uncontrolled : Prop} (h : ¬ Uncontrolled) :
    ¬ Dominates G Y Φ Uncontrolled :=
  fun hd => h hd.2

/-- And domination is still a veto, so the capacity is real even when the
constraint question is left open. -/
public theorem Dominates.veto {Y : Set N} {Φ : Set X} {Uncontrolled : Prop}
    (h : Dominates G Y Φ Uncontrolled) : Veto G Y Φ :=
  h.1

end AISafetyAtlas.Sovereignty
