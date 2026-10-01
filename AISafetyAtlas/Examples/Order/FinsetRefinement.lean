module

public import AISafetyAtlas.Order.FinsetRefinement

/-!
# Worked example: refinement of finite sets over a preorder

`AISafetyAtlas.Order.Refines` is stated over an arbitrary preorder, and the
reason it earns a name is that one relation carries two moves that are usually
described separately: dropping an element, and replacing an element by one below
it. This file runs both on a carrier small enough to read.

The carrier is four cards under a two-step order: `deductive` and `analogical`
each sit below `reasoning`, and `social` sits below nothing but itself. So the
order is neither discrete nor total, which is what makes the two moves visibly
different here.

The last two theorems are the degenerate case, on a separate discretely ordered
carrier: there refinement is exactly reverse inclusion, so the only move left is
dropping an element.
-/

namespace AISafetyAtlas.Examples.Order.FinsetRefinement

/-- Four cards. `social` is present so the order is not a single chain. -/
public inductive Skill where
  | deductive
  | analogical
  | reasoning
  | social
  deriving DecidableEq, Repr

open Skill

/-- The order: two specialisations below `reasoning`, and nothing else. -/
public inductive Skill.Le : Skill → Skill → Prop
  | rfl (a : Skill) : Skill.Le a a
  | deductive_reasoning : Skill.Le deductive reasoning
  | analogical_reasoning : Skill.Le analogical reasoning

public theorem Skill.Le.trans' {a b c : Skill} (h : Skill.Le a b) (h' : Skill.Le b c) :
    Skill.Le a c := by
  cases h with
  | rfl _ => exact h'
  | deductive_reasoning => cases h' with | rfl _ => exact Skill.Le.deductive_reasoning
  | analogical_reasoning => cases h' with | rfl _ => exact Skill.Le.analogical_reasoning

public instance : Preorder Skill where
  le := Skill.Le
  le_refl := Skill.Le.rfl
  le_trans _ _ _ := Skill.Le.trans'

/-- A specialisation sits below the card it specialises. -/
public theorem deductive_le_reasoning : (deductive : Skill) ≤ reasoning :=
  Skill.Le.deductive_reasoning

/-- **Dropping an element is a refinement move.** -/
public theorem pair_refines_singleton :
    AISafetyAtlas.Order.Refines ({deductive, social} : Finset Skill) {social} :=
  AISafetyAtlas.Order.refines_of_subset (by decide)

/-- **Moving down the order is the same move.** -/
public theorem deductive_refines_reasoning :
    AISafetyAtlas.Order.Refines ({deductive} : Finset Skill) {reasoning} :=
  AISafetyAtlas.Order.refines_singleton deductive_le_reasoning

/-- Both moves composed: drop `social`, then move `deductive` up to `reasoning`. -/
public theorem pair_refines_reasoning :
    AISafetyAtlas.Order.Refines ({deductive, social} : Finset Skill) {reasoning} :=
  AISafetyAtlas.Order.Refines.trans
    (AISafetyAtlas.Order.refines_of_subset (by decide))
    deductive_refines_reasoning

/-- Refinement is reflexive, on this carrier as on any. -/
public theorem refines_self (A : Finset Skill) : AISafetyAtlas.Order.Refines A A :=
  AISafetyAtlas.Order.Refines.refl A

/-- The pointwise form of the definition, taken as the way in. -/
public theorem refines_reasoning_pointwise :
    AISafetyAtlas.Order.Refines ({deductive, analogical} : Finset Skill) {reasoning} :=
  AISafetyAtlas.Order.refines_of_forall fun _ hb =>
    ⟨deductive, by decide, (Finset.mem_singleton.mp hb) ▸ deductive_le_reasoning⟩

/-- The one-element criterion, which is the decidable form. -/
public theorem refines_reasoning_of_witness :
    AISafetyAtlas.Order.Refines ({social, analogical} : Finset Skill) {reasoning} :=
  AISafetyAtlas.Order.refines_singleton_iff.mpr
    ⟨analogical, by decide, Skill.Le.analogical_reasoning⟩

/-- Everything refines the empty demand. -/
public theorem refines_empty_demand :
    AISafetyAtlas.Order.Refines ({social} : Finset Skill) (∅ : Finset Skill) :=
  AISafetyAtlas.Order.refines_empty _

/-- **Nothing refines from nothing.** The empty set refines only the empty set,
so an empty left-hand side is not a universal refiner. -/
public theorem not_empty_refines_reasoning :
    ¬AISafetyAtlas.Order.Refines (∅ : Finset Skill) {reasoning} := by
  intro h
  have : ({reasoning} : Finset Skill) = ∅ :=
    AISafetyAtlas.Order.refines_empty_iff.mp h
  exact absurd (this ▸ Finset.mem_singleton_self reasoning) (Finset.notMem_empty _)

/-- A second carrier, discretely ordered: `≤` relates a card only to itself. -/
public inductive Modality where
  | text
  | image
  deriving DecidableEq, Repr

public instance : Preorder Modality where
  le := Eq
  le_refl _ := rfl
  le_trans _ _ _ h h' := h.trans h'

/-- **On a discrete carrier, refinement is reverse inclusion.** -/
public theorem refines_modality_iff_subset (A B : Finset Modality) :
    AISafetyAtlas.Order.Refines A B ↔ B ⊆ A :=
  AISafetyAtlas.Order.refines_iff_subset_of_discrete (fun _ _ h => h) A B

end AISafetyAtlas.Examples.Order.FinsetRefinement
