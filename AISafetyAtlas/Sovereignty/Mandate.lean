module

public import AISafetyAtlas.Sovereignty.Rights

/-!
# Mandate retention under delegation, and Peleg's representation condition

`docs/provenance/cognitive-sovereignty-obligation.md` states SOV-1 and calls it a
**schema, not a statement**, because in the delegated game the principal has no
strategy slot and the note lists three repairs.

**Those three are already built.** `AISafetyAtlas.Sovereignty.Separations`
carries them as `RetainsWith`, `RetainsAgainst` and `RetainsUnder`, with the
separations in `AISafetyAtlas.Examples.Sovereignty.Separations` --
`retainsWith_delegated` holds, `not_retainsAgainst_delegated` fails, and
`retainsUnder_delegated_zero` together with `not_retainsUnder_delegated_two`
shows reading 3 is a claim about the *policy* rather than about the principal.
Nothing here restates them.

This module adds the two things that development does not have: the **published
anchor** those readings specialize, and the **mandate family**.

## The published anchor, and what is atlas-side

**`Represents` is Peleg's Definition 3.4** — Bezalel Peleg, *Effectivity
functions, game forms, games, and rights*, Social Choice and Welfare 15: 67-80,
pinned as `peleg1997.pdf`, sha256 `99039339aae01cb8e903ebab...`. Read from
rendered images of pages 72 and 73, because the manifest records that this file's
mathematics is AMS-glyph and text extraction mangles it.

Print's Definition 3.3 is α-effectivity:

> Let `Γ = ⟨N; Σ¹, …, Σⁿ; g; A⟩` be a GF, let `S ⊆ N, S ≠ ∅`, and let `B ⊆ A`.
> `S` is *α-effective* for `B` if there exists `σ₀^S ∈ Σ^S = ×_{i∈S} Σⁱ` such
> that for all `σ^{N\S} ∈ Σ^{N\S}`, `g(σ₀^S, σ^{N\S}) ∈ B`.

which is this repository's `Forces`, and `E_α(S; Γ)` is `effectivity`. Print's
Definition 3.4 is then:

> A (legal) GF `Γ` is a *representation* of the constitution `⟨ρ, α, γ⟩` if
> `E_α(·; Γ) = E(·)`, where `E` is defined by (3.1).

`Represents` is now in `AISafetyAtlas.Sovereignty.Rights`, at print's
right-hand side: the constitution `⟨ρ, α, γ⟩` is `Constitution`, the effectivity
function (3.1) induces is `Constitution.induced`, and `Represents G κ` is
print's equality. What this module carried before that was built survives there
as `EffectivityEq` — two game forms agree at every coalition — which
`effectivityEq_iff_represents_ofGameForm` identifies as representation against a
constitution read off one of them. Print's Theorem 3.5 is **not** proved here:
`Represents.superadditive` is the necessity of its condition (ii) and the
sufficiency direction is print's appendix construction.

**Three deliberate differences from Definition 3.3, none of them a
strengthening.** Print restricts to `S ≠ ∅` and sets `E_α(∅; Γ) = A` by fiat;
`effectivity` is defined at every coalition including `∅` and computes the empty
coalition's family rather than stipulating it. Print assumes `g` is **surjective
onto `A`**; nothing here does. And print writes `E_α(S; Γ) = {B ⊆ S | S is
α-effective for B}` on page 73, where `B ⊆ S` is a typo for `B ⊆ A` — `B` is a
set of social states throughout, and `S` is a coalition.

**Everything below `Represents` is atlas-side interpretation.** The mandate
family `𝒜`, the retention comparison, and the three readings of the delegated
coalition are this repository's, not Peleg's; the obligation note says the five
verbs of the operational cut are unpublished, and per that note's §8 item 1 they
are graded as interpretation rather than against a source. What Peleg supplies is
the object `𝒜` lives in and the totalized condition retention relaxes.

## SOV-1, and how far it sits below Definition 3.4

`RetainsFamily` relaxes `EffectivityEq` on three axes at once: one coalition
rather than all, inclusion rather than equality, and the mandate family `𝒜`
rather than every set. `retainsFamily_of_effectivityEq` is the specialization and
`effectivityEq_of_retainsFamily_univ` the converse at the two extremes, so the
two notions meet exactly where the note says the comparison is a partial order
and not a number. `retainsFamily_of_represents` states the same specialization
against Peleg's Definition 3.4 proper: two game forms representing one
constitution retain every mandate across the move between them.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

variable {N : Type u} {X : Type v}


/-! ## The mandate family, and the comparison across two games

The three readings above are each a single target set in a single game. The
obligation note's §2 items 2 and 3 ask for more: a **family** `𝒜` of
mandate-relevant targets, and a **comparison** between a baseline game and a
delegated one -- *"every mandate-relevant guarantee the principal had, it still
has"*, as a partial order rather than a number. That is what `RetainsFamily` is,
and it is the shape in which SOV-1 sits directly below Peleg's Definition 3.4.
-/

/--
**Mandate retention across a delegation.** Every mandate-relevant set the
coalition `C₀` could force in the baseline, the coalition `C₁` can still force in
the delegated game.

`𝒜` is the mandate family. The note is explicit that nothing in a game form
supplies it -- it comes from the mandate and is an input, not a theorem. In
Peleg's frame it is a sub-family of the constitution's `γ(C, α(C))`.
-/
@[expose] public def RetainsFamily (G₀ G₁ : GameForm.{u, v, w} N X) (C₀ C₁ : Set N)
    (𝒜 : Set (Set X)) : Prop :=
  ∀ A ∈ 𝒜, A ∈ effectivity G₀ C₀ → A ∈ effectivity G₁ C₁

/-- **Equal effectivity implies retention, at every coalition and every
mandate.** A delegated game form that distributes power exactly as the baseline
does keeps every mandate whatsoever. -/
public theorem retainsFamily_of_effectivityEq {G₀ G₁ : GameForm.{u, v, w} N X}
    (h : EffectivityEq G₀ G₁) (C : Set N) (𝒜 : Set (Set X)) :
    RetainsFamily G₀ G₁ C C 𝒜 :=
  fun _A _h𝒜 hA => (h C) ▸ hA

/-- **Representation implies retention, at every coalition and every mandate.**
The specialization that places SOV-1 below Peleg's Definition 3.4: two game
forms that represent the *same constitution* keep every mandate across the move
from one to the other. -/
public theorem retainsFamily_of_represents {R : Type*} {κ : Constitution N X R}
    {G₀ G₁ : GameForm.{u, v, w} N X} (h₀ : Represents G₀ κ) (h₁ : Represents G₁ κ)
    (C : Set N) (𝒜 : Set (Set X)) :
    RetainsFamily G₀ G₁ C C 𝒜 :=
  retainsFamily_of_effectivityEq (fun D => (h₀ D).trans (h₁ D).symm) C 𝒜

/-- **And at the two extremes they meet.** Retention at every coalition, with the
mandate family unrestricted and the inclusion holding both ways, *is* equality
of the two effectivity functions -- so SOV-1 is a genuine weakening of Peleg's
condition rather than a different notion. -/
public theorem effectivityEq_of_retainsFamily_univ {G₀ G₁ : GameForm.{u, v, w} N X}
    (h₀ : ∀ C, RetainsFamily G₀ G₁ C C (Set.univ : Set (Set X)))
    (h₁ : ∀ C, RetainsFamily G₁ G₀ C C (Set.univ : Set (Set X))) :
    EffectivityEq G₀ G₁ :=
  fun C => Set.Subset.antisymm
    (fun A hA => h₀ C A trivial hA) (fun A hA => h₁ C A trivial hA)

/-- Retention is transitive at a **fixed** mandate. If the mandate also
moves, transitivity can fail; that is the content of
`AISafetyAtlas.Sovereignty.Steering`. -/
public theorem RetainsFamily.trans {G₀ G₁ G₂ : GameForm.{u, v, w} N X}
    {C₀ C₁ C₂ : Set N} {𝒜 : Set (Set X)}
    (h₀₁ : RetainsFamily G₀ G₁ C₀ C₁ 𝒜) (h₁₂ : RetainsFamily G₁ G₂ C₁ C₂ 𝒜) :
    RetainsFamily G₀ G₂ C₀ C₂ 𝒜 :=
  fun A hA hA₀ => h₁₂ A hA (h₀₁ A hA hA₀)

/-- Retention is monotone in the mandate: a smaller mandate is easier to keep. -/
public theorem RetainsFamily.mono_mandate {G₀ G₁ : GameForm.{u, v, w} N X}
    {C₀ C₁ : Set N} {𝒜 ℬ : Set (Set X)} (h : RetainsFamily G₀ G₁ C₀ C₁ ℬ)
    (h𝒜 : 𝒜 ⊆ ℬ) : RetainsFamily G₀ G₁ C₀ C₁ 𝒜 :=
  fun A hA => h A (h𝒜 hA)

/-- And monotone in the delegated coalition, by `Forces.mono_coalition`. -/
public theorem RetainsFamily.mono_coalition {G₀ G₁ : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G₁.strategy i)] {C₀ C₁ D₁ : Set N} {𝒜 : Set (Set X)}
    (h : RetainsFamily G₀ G₁ C₀ C₁ 𝒜) (hCD : C₁ ⊆ D₁) :
    RetainsFamily G₀ G₁ C₀ D₁ 𝒜 :=
  fun A hA hA₀ => (h A hA hA₀).mono_coalition hCD

/-! ## The bridge to the three readings

Each reading is `RetainsFamily` at a singleton mandate and its own coalition, so
the family form generalizes all three rather than competing with them.
-/

/-- Reading 1, `RetainsWith`, is the family form at `C₁ = {p, d}`. -/
public theorem retainsWith_of_retainsFamily {G₀ G₁ : GameForm.{u, v, w} N X}
    {p d : N} {A : Set X} (hA : A ∈ effectivity G₀ {p})
    (h : RetainsFamily G₀ G₁ {p} {p, d} {A}) : RetainsWith G₁ p d A :=
  h A rfl hA

/-- Reading 2, `RetainsAgainst`, is the family form at `C₁ = {p}`. -/
public theorem retainsAgainst_of_retainsFamily {G₀ G₁ : GameForm.{u, v, w} N X}
    {p : N} {A : Set X} (hA : A ∈ effectivity G₀ {p})
    (h : RetainsFamily G₀ G₁ {p} {p} {A}) : RetainsAgainst G₁ p A :=
  h A rfl hA

/-! ## SOV-1, and what selects the coalition

The obligation note's §8 item 5 left exactly one thing open: in the delegated
game, which coalition acts for the principal. The maintainer's ruling, taken
2026-09-13, is that this is **not a free modelling choice**. It is fixed by the
delegate's alignment: an aligned delegate acts for the principal, so the
coalition is `{p, d}`; an unaligned one does not, so the coalition is `{p}` and
the delegate's strategies join the complement the guarantee has to survive.

`principalCoalition` carries that rule as a set-valued function of an arbitrary
alignment proposition, and `SOV1` is `RetainsFamily` at it. Nothing here decides
*whether* a given delegate is aligned, and nothing here supplies a criterion for
it; `al` is a parameter, exactly as the mandate family is.

Reading 3 is deliberately not folded in. A pinned policy is a restriction of the
delegate's strategy set and not a coalition, so it gets its own family form at
the end of this section rather than an instance of `principalCoalition`.
-/

/--
**Who acts for the principal, selected by the delegate's alignment.**

`insert p {x | x = d ∧ al}` rather than an `if`, so that no decidability
instance is needed and `al` may be any proposition -- including one nobody in
the model can evaluate, which is the case the separation below is about.
-/
@[expose] public def principalCoalition (p d : N) (al : Prop) : Set N :=
  insert p {x | x = d ∧ al}

/-- With an aligned delegate the coalition is the pair. -/
public theorem principalCoalition_of_aligned {p d : N} {al : Prop} (h : al) :
    principalCoalition p d al = {p, d} := by
  ext x
  simp [principalCoalition, h]

/-- With an unaligned delegate it is the principal alone. -/
public theorem principalCoalition_of_unaligned {p d : N} {al : Prop} (h : ¬ al) :
    principalCoalition p d al = {p} := by
  ext x
  simp [principalCoalition, h]

/-- The principal is in its own coalition at every alignment. -/
public theorem singleton_subset_principalCoalition (p d : N) (al : Prop) :
    ({p} : Set N) ⊆ principalCoalition p d al :=
  Set.singleton_subset_iff.mpr (Set.mem_insert _ _)

/--
**SOV-1.** Every mandate-relevant set the principal could force in the baseline,
the coalition that acts for it can still force in the delegated game.

This is `RetainsFamily` with the delegated coalition supplied by the alignment
rule rather than chosen. The baseline coalition is `{p}` in both cases: before
delegating there is no delegate to be aligned with.
-/
@[expose] public def SOV1 (G₀ G₁ : GameForm.{u, v, w} N X) (p d : N) (al : Prop)
    (𝒜 : Set (Set X)) : Prop :=
  RetainsFamily G₀ G₁ {p} (principalCoalition p d al) 𝒜

/-- At an aligned delegate, SOV-1 is retention by the pair -- reading 1. -/
public theorem sov1_of_aligned {G₀ G₁ : GameForm.{u, v, w} N X} {p d : N}
    {al : Prop} {𝒜 : Set (Set X)} (h : al) :
    SOV1 G₀ G₁ p d al 𝒜 ↔ RetainsFamily G₀ G₁ {p} {p, d} 𝒜 := by
  rw [SOV1, principalCoalition_of_aligned h]

/-- At an unaligned delegate, SOV-1 is retention by the principal alone --
reading 2, the one that has to survive the delegate's own deviation. -/
public theorem sov1_of_unaligned {G₀ G₁ : GameForm.{u, v, w} N X} {p d : N}
    {al : Prop} {𝒜 : Set (Set X)} (h : ¬ al) :
    SOV1 G₀ G₁ p d al 𝒜 ↔ RetainsFamily G₀ G₁ {p} {p} 𝒜 := by
  rw [SOV1, principalCoalition_of_unaligned h]

/--
**The unaligned obligation is the safe one to prove.**

Discharging SOV-1 as though the delegate were unaligned discharges it at *every*
alignment, including one the principal cannot evaluate. This is the formal
content of the ruling's asymmetry: alignment weakens what must be shown, so
assuming it is what costs something, and refusing to assume it costs nothing.
-/
public theorem sov1_of_retainsFamily_singleton {G₀ G₁ : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G₁.strategy i)] {p d : N} {al : Prop} {𝒜 : Set (Set X)}
    (h : RetainsFamily G₀ G₁ {p} {p} 𝒜) : SOV1 G₀ G₁ p d al 𝒜 :=
  h.mono_coalition (singleton_subset_principalCoalition p d al)

/-- SOV-1 inherits monotonicity in the mandate from `RetainsFamily.mono_mandate`. -/
public theorem SOV1.mono_mandate {G₀ G₁ : GameForm.{u, v, w} N X} {p d : N}
    {al : Prop} {𝒜 ℬ : Set (Set X)} (h : SOV1 G₀ G₁ p d al ℬ) (h𝒜 : 𝒜 ⊆ ℬ) :
    SOV1 G₀ G₁ p d al 𝒜 :=
  RetainsFamily.mono_mandate h h𝒜

/-! ### Reading 3 at the family level

`RetainsUnder` pins one of the delegate's strategies instead of naming a
coalition, so it is not an instance of `principalCoalition` and is stated in
parallel. Its baseline side is the same as SOV-1's.
-/

/--
**Retention through a delegate whose policy is fixed.** Every mandate-relevant
set the principal could force in the baseline, the pinned policy lands in.
-/
@[expose] public def RetainsUnderFamily (G₀ G₁ : GameForm.{u, v, w} N X)
    (C₀ : Set N) (d : N) (σd : G₁.strategy d) (𝒜 : Set (Set X)) : Prop :=
  ∀ A ∈ 𝒜, A ∈ effectivity G₀ C₀ → RetainsUnder G₁ d σd A

/-- Reading 3 is the family form at a singleton mandate. -/
public theorem retainsUnder_of_retainsUnderFamily
    {G₀ G₁ : GameForm.{u, v, w} N X} {C₀ : Set N} {d : N} {σd : G₁.strategy d}
    {A : Set X} (hA : A ∈ effectivity G₀ C₀)
    (h : RetainsUnderFamily G₀ G₁ C₀ d σd {A}) : RetainsUnder G₁ d σd A :=
  h A rfl hA

/-- And it is monotone in the mandate, like the other two. -/
public theorem RetainsUnderFamily.mono_mandate {G₀ G₁ : GameForm.{u, v, w} N X}
    {C₀ : Set N} {d : N} {σd : G₁.strategy d} {𝒜 ℬ : Set (Set X)}
    (h : RetainsUnderFamily G₀ G₁ C₀ d σd ℬ) (h𝒜 : 𝒜 ⊆ ℬ) :
    RetainsUnderFamily G₀ G₁ C₀ d σd 𝒜 :=
  fun A hA => h A (h𝒜 hA)


end AISafetyAtlas.Sovereignty
