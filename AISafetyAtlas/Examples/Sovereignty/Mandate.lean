module

public import AISafetyAtlas.Sovereignty.Mandate
public import AISafetyAtlas.Examples.Sovereignty.Separations

/-!
# Peleg's representation condition on the delegation already in the tree

`AISafetyAtlas.Examples.Sovereignty.Separations` already separates the note's
three readings on `undelegated` against `delegated`. This file adds the one thing
that development does not say: **that delegation is not a representation in
Peleg's sense**, and the mandate family the note asks for is the family form of
the comparison it already instantiates.

Nothing is redefined here. The game forms, the mandate and the three readings are
`Separations`'.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-- The mandate, as a one-element family. -/
@[expose] public def mandateFamily : Set (Set (Fin 3)) := {mandate}

/-- **The delegation does not distribute power as the baseline does.** The
witness is the principal's own coalition -- exactly the failure
`not_retainsAgainst_delegated` records. -/
public theorem not_effectivityEq_delegation : ¬ EffectivityEq undelegated delegated := by
  intro h
  refine not_retainsAgainst_delegated ?_
  have : mandate ∈ effectivity delegated {false} := (h {false}) ▸ retainsAgainst_undelegated
  exact this

/-- **And so the delegation is not a representation**, at Peleg's Definition 3.4
proper: the constitution read off the baseline by `Constitution.ofGameForm` is
one the baseline represents by construction and the delegation does not. -/
public theorem not_represents_delegation :
    ¬ Represents delegated (Constitution.ofGameForm undelegated Unit) :=
  fun h => not_effectivityEq_delegation fun C => (h C).symm

/-- **And the mandate is not retained in the family form either**, at the
strongest reading. This is `sovereignty_lost_on_delegation` restated over a
family rather than a single set, which is the shape the obligation note's §2
item 3 asks for. -/
public theorem not_retainsFamily_delegation :
    ¬ RetainsFamily undelegated delegated {false} {false} mandateFamily := fun h =>
  not_retainsAgainst_delegated (h mandate rfl retainsAgainst_undelegated)

/-- The cooperative reading does survive, and the family form sees that too.

`mandateFamily` is `{mandate}` by definition, so this is
`retainsFamily_delegated_pair` under its family name rather than a second proof
of it. -/
public theorem retainsFamily_delegation_coop :
    RetainsFamily undelegated delegated {false} {false, true} mandateFamily :=
  retainsFamily_delegated_pair

/-! ## Instances of the mandate lemmas

Every lemma in `AISafetyAtlas.Sovereignty.Mandate` is applied below at least
once on these two games. A lemma nothing applies is unfalsifiable by the build:
its hypotheses are never instantiated, so an antecedent nothing can satisfy
would compile exactly the same. Several of the instances are deliberately
trivial -- a reflexive representation, an empty mandate -- and each says so.
What they establish is inhabitation, not depth.
-/

/-- **Reading 1 recovered from the family form.** `retainsWith_of_retainsFamily`
at the singleton mandate returns the forcing fact `retainsWith_delegated`
states directly, which is what makes the family form a generalization of the
reading rather than a different claim. -/
public theorem retainsWith_of_family_delegated :
    RetainsWith delegated false true mandate :=
  retainsWith_of_retainsFamily retainsAgainst_undelegated retainsFamily_delegated_pair

/-- **An equality of effectivity functions, so that the lemmas about one are not
vacuous.** The baseline agrees with itself; `not_effectivityEq_delegation` is
the interesting direction, and this is the trivial one that keeps
`EffectivityEq.refl` and `retainsFamily_of_effectivityEq` applied. -/
public theorem retainsFamily_undelegated_self :
    RetainsFamily undelegated undelegated {false} {false} mandateFamily :=
  retainsFamily_of_effectivityEq (EffectivityEq.refl undelegated) {false} mandateFamily

/-- **SOV-1 from the singleton coalition.** A principal that retains its
mandate on its own retains it inside any coalition the mandate lemmas build
around it, which is the monotonicity `sov1_of_retainsFamily_singleton` packages.
Trivial in depth and not in shape: the hypothesis is the reflexive instance
above, so the antecedent is inhabited and the lemma is falsifiable by the
build. -/
public theorem sov1_undelegated_self :
    SOV1 undelegated undelegated false true True mandateFamily :=
  sov1_of_retainsFamily_singleton retainsFamily_undelegated_self

/-- **Reading 2 recovered from the family form**, on the baseline where it
holds. Against `delegated` it fails, which is `not_retainsFamily_delegation`. -/
public theorem retainsAgainst_of_family_undelegated :
    RetainsAgainst undelegated false mandate :=
  retainsAgainst_of_retainsFamily retainsAgainst_undelegated
    retainsFamily_undelegated_self

/-- Symmetry, on the reflexive instance. -/
public theorem effectivityEq_undelegated_symm : EffectivityEq undelegated undelegated :=
  EffectivityEq.symm (EffectivityEq.refl undelegated)

/-- **The two extremes meet, on the reflexive instance.** Retention both ways at
every coalition and an unrestricted mandate returns equality of the two
effectivity functions. -/
public theorem effectivityEq_of_univ_undelegated : EffectivityEq undelegated undelegated :=
  effectivityEq_of_retainsFamily_univ
    (fun C => retainsFamily_of_effectivityEq (EffectivityEq.refl undelegated) C Set.univ)
    (fun C => retainsFamily_of_effectivityEq (EffectivityEq.refl undelegated) C Set.univ)

/-- **Transitivity at a fixed mandate**, composing the surviving cooperative
retention with the delegated game's reflexive retention. -/
public theorem retainsFamily_delegation_trans :
    RetainsFamily undelegated delegated {false} {false, true} mandateFamily :=
  RetainsFamily.trans retainsFamily_delegation_coop
    (retainsFamily_of_effectivityEq (EffectivityEq.refl delegated) {false, true} mandateFamily)

/-- **Monotone in the delegated coalition**: widening `{false, true}` to
everything keeps the retention. -/
public theorem retainsFamily_delegation_univ :
    RetainsFamily undelegated delegated {false} Set.univ mandateFamily :=
  RetainsFamily.mono_coalition retainsFamily_delegation_coop (Set.subset_univ _)

/-- **Monotone in the mandate.** The empty mandate is retained wherever a larger
one is; trivial as a fact about these games, and the point is that
`SOV1.mono_mandate` is applied at all. -/
public theorem sov1_aligned_empty :
    SOV1 undelegated delegated false true True (∅ : Set (Set (Fin 3))) :=
  SOV1.mono_mandate sov1_aligned (Set.empty_subset _)

/-- **Reading 3 recovered from its family form**, at the pinned policy `0`. -/
public theorem retainsUnder_of_family_zero :
    RetainsUnder delegated true (0 : Fin 3) mandate :=
  retainsUnder_of_retainsUnderFamily retainsAgainst_undelegated
    retainsUnderFamily_delegated_zero

/-- And the family form of reading 3 is monotone in the mandate too. -/
public theorem retainsUnderFamily_delegated_zero_empty :
    RetainsUnderFamily undelegated delegated {false} true (0 : Fin 3)
      (∅ : Set (Set (Fin 3))) :=
  RetainsUnderFamily.mono_mandate retainsUnderFamily_delegated_zero (Set.empty_subset _)

end AISafetyAtlas.Examples.Sovereignty
