module

public import AISafetyAtlas.Sovereignty.Playability

/-!
# Peleg's rights layer: the constitution, and what a game form represents

`AISafetyAtlas.Sovereignty.Separations` renders Peleg's section 3 game-form
layer -- `GameForm` is Definition 3.2, `Forces` is Definition 3.3's
α-effectivity, `effectivity` is its family. What it does not render is the
object Definition 3.4 compares a game form *against*: the constitution. This
module builds it.

Bezalel Peleg, *Effectivity functions, game forms, games, and rights*, Social
Choice and Welfare 15: 67-80, pinned as `peleg1997.pdf`, sha256
`99039339aae01cb8e903ebab99e210d2ffdb7945cd9e89247abcdaf02976669a`. Read from
rendered images of journal pages 69, 70, 72, 73 and 74, because the manifest
records that this file's mathematics is AMS-glyph and text extraction mangles
it.

## What a constitution is

Print's Definition 2.4: a society is `⟨N, A, ρ, α, γ⟩` and the triple
`⟨ρ, α, γ⟩` is the *constitution* -- a set of rights, an assignment `α` of
rights to coalitions, and an *access correspondence* `γ` giving, for a coalition
and a set of rights, the sets of social states that coalition may attain by
exercising them. `Constitution` is that triple: `N` and `X` are print's `N` and
`A`, and the type `R` is print's `ρ`.

**A name shared with an unrelated module.** `AISafetyAtlas.Sovereignty.Constitution`
is a module about *amendment chains* -- whether each change to a constitution was
authorized by the one in force when it was made -- over an abstract carrier with
no rights, no coalitions and no social states. It is not this object and nothing
connects them.

`Constitution.induced` is print's **(3.1)**, `E(S; α, γ) = γ(S, α(S))`: a
constitution induces an effectivity function by handing each coalition the
rights it holds.

`Constitution.Standing` is print's standing assumption on journal page 69 --
*"We always assume the following: (1) `α(∅) = ∅`, and (2)
`γ(∅, θ) = γ(S, ∅) = {A}` for all `θ ⊆ ρ` and `S ⊆ N`."*

**Print's singleton convention, stated by print itself.** Page 69 says
*"Henceforth, we shall denote a singleton `{a}` by `a`"*, which is why pages 72
and 73 write `E(∅) = A` and `E_α(∅; Γ) = A` where the family `{A}` is meant.
The standing assumption above is the one place print writes the braces, and it
is the reading taken here.

## Definition 3.4, at print's right-hand side

> A (legal) GF `Γ` is a *representation* of the constitution `⟨ρ, α, γ⟩` if
> `E_α(•; Γ) = E(•)`, where `E` is defined by (3.1).

`Represents G κ` is that equality at every coalition. Until this module,
`AISafetyAtlas.Sovereignty.Mandate` carried a stand-in that put a *second game
form's own* α-effectivity function where print puts the induced one; that
notion survives as `EffectivityEq`, and `effectivityEq_iff_represents_ofGameForm`
is the exact sense in which it was weaker -- it is representation against the
constitution `Constitution.ofGameForm`, which every game form represents by
construction.

**Three widenings, none of them a strengthening.** Print restricts Definition
3.4 to *legal* game forms -- those whose strategies contradict no assignment of
rights -- and leaves legality informal; the equality uses none of it, so it is
quantified here over every game form. Print's `ρ` is finite; nothing here needs
that. And print assumes `g` is surjective onto `A` from Definition 3.3 onward;
nothing here assumes it, because `Represents.surjective_outcome` **derives** it
from representation of a constitution satisfying the standing assumptions.

## Theorem 3.5, and the half that is free

> Let `E` be the EF which is derived by (3.1). Then there exists a GF `Γ` such
> that `E_α(S; Γ) = E(S)` for all `S ∈ 2^N` iff the following two conditions
> hold: (i) `γ` is monotonic w.r.t. the alternatives; (ii) `E` is superadditive.

Necessity of (ii) is `Represents.superadditive`, a direct transfer of
`forces_superadditive`. Sufficiency is print's appendix construction and is not
proved here.

Necessity of **(i) as printed is not available, and that is a fact about
print's quantifier rather than a gap here.** Condition (3.3) quantifies `γ` over
every `θ ∈ 2^ρ`, while a representation constrains only the diagonal
`γ(S, α(S))`; print's own page 70 says the off-diagonal values *"do not enter
the analysis of a society at a given date"*. What representation does give is
`Represents.upwardClosed`, condition (3.3) restricted to the diagonal. The gap
is exhibited rather than asserted:
`AISafetyAtlas.Examples.Sovereignty.represented_not_monotoneAlternatives`
is a represented constitution that fails (3.3).

## What is not here

Legality, Remark 2.5's equal-treatment condition, Theorem 3.5's construction,
and sections 4 and 5. Section 21 of `docs/provenance/source-coverage-audit.md`
grades each.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w r

variable {N : Type u} {X : Type v} {R : Type r}

/-! ## The constitution -/

/--
**Peleg's Definition 2.4.** A constitution is a set of rights `R`, an assignment
`assign` of rights to coalitions, and an access correspondence `access` giving
the sets of social states a coalition may attain with a given set of rights.

Print's `⟨ρ, α, γ⟩`, with `ρ` carried as the type `R` rather than as a subset of
a larger one: print's `θ ⊆ ρ` is a `Set R` here, and print's `ρ` itself is
`Set.univ`.
-/
public structure Constitution (N : Type u) (X : Type v) (R : Type r) where
  /-- Print's `α`: the rights a coalition holds. -/
  assign : Set N → Set R
  /-- Print's `γ`: the sets of social states a coalition may attain by
  exercising a given set of rights. -/
  access : Set N → Set R → Set (Set X)

namespace Constitution

variable (κ : Constitution N X R)

/--
**(3.1).** The effectivity function a constitution induces: hand each coalition
the rights it holds. Print writes `E(S; α, γ) = E(S) = γ(S, α(S))`.
-/
@[expose] public def induced (C : Set N) : Set (Set X) :=
  κ.access C (κ.assign C)

/--
**Print's standing assumptions**, journal page 69: the empty coalition is
assigned no rights, and both the empty coalition and the empty set of rights
attain the whole state space and nothing smaller.

Carried as a predicate rather than as structure fields, because Definition 3.4
needs none of them; only `surjective_outcome` and `induced_empty` do.
-/
public structure Standing : Prop where
  /-- `α(∅) = ∅`. -/
  assign_empty : κ.assign ∅ = ∅
  /-- `γ(∅, θ) = {A}` for every set of rights. -/
  access_empty_coalition : ∀ θ : Set R, κ.access ∅ θ = {Set.univ}
  /-- `γ(S, ∅) = {A}` for every coalition. -/
  access_empty_rights : ∀ C : Set N, κ.access C ∅ = {Set.univ}

/-- The empty coalition's induced family is the whole state space alone --
print's condition (i) on an effectivity function, here a consequence of the
standing assumptions rather than a stipulation. -/
public theorem induced_empty (h : κ.Standing) : κ.induced ∅ = ({Set.univ} : Set (Set X)) :=
  h.access_empty_coalition _

/-! ## Print's monotonicity conditions

Each is a property a constitution may or may not have; print says so of all four
and says outright that (3.4) *"generally does not hold"*.
-/

/-- **(3.2).** The assignment of rights is monotonic: larger groups hold at
least the rights of smaller ones. -/
@[expose] public def MonotoneAssign : Prop :=
  ∀ S T : Set N, S ⊆ T → κ.assign S ⊆ κ.assign T

/-- **(3.3).** The access correspondence is monotonic with respect to the
alternatives: a superset of an attainable set is attainable. -/
@[expose] public def MonotoneAlternatives : Prop :=
  ∀ (S : Set N) (θ : Set R) (B B' : Set X), B ∈ κ.access S θ → B ⊆ B' → B' ∈ κ.access S θ

/-- **(3.4).** The access correspondence is monotonic with respect to rights.
Print says this generally fails, because rights in its model include
obligations and more rights may *diminish* the attainable sets. -/
@[expose] public def MonotoneRights : Prop :=
  ∀ (S : Set N) (θ θ' : Set R), θ ⊆ θ' → κ.access S θ ⊆ κ.access S θ'

/-- **(3.5).** The access correspondence is monotonic with respect to
coalitions. Print says this too may fail -- the members of `S* \ S` may hold
rights conflicting with those of `S` -- and then assumes it. -/
@[expose] public def MonotoneCoalitions : Prop :=
  ∀ (S S' : Set N) (θ : Set R), S ⊆ S' → κ.access S θ ⊆ κ.access S' θ

/--
**The induced effectivity function is coalition-monotone under print's three
conditions.** Larger coalitions hold more rights by (3.2), which attain more by
(3.4), and a larger coalition attains more at fixed rights by (3.5).

This is the one place all three conditions are used at once, and it is why
print states them separately: none of the three alone gives it.
-/
public theorem induced_mono (h₂ : κ.MonotoneAssign) (h₄ : κ.MonotoneRights)
    (h₅ : κ.MonotoneCoalitions) {S T : Set N} (hST : S ⊆ T) :
    κ.induced S ⊆ κ.induced T :=
  fun _B hB => h₄ T (κ.assign S) (κ.assign T) (h₂ S T hST) (h₅ S T (κ.assign S) hST hB)

end Constitution

/-! ## Effectivity functions in the abstract

Print's two conditions in Theorem 3.5 are properties of the induced family, not
of the game form, so they are stated on a bare family of families.
-/

/-- **Definition 3.1.** An effectivity function is *superadditive* when disjoint
coalitions effective for two sets make their union effective for the
intersection. -/
@[expose] public def Superadditive (E : Set N → Set (Set X)) : Prop :=
  ∀ (S₁ S₂ : Set N) (B₁ B₂ : Set X), Disjoint S₁ S₂ → B₁ ∈ E S₁ → B₂ ∈ E S₂ →
    B₁ ∩ B₂ ∈ E (S₁ ∪ S₂)

/-- Condition (3.3) read on an effectivity function rather than on the access
correspondence: every coalition's family is closed upwards. -/
@[expose] public def UpwardClosed (E : Set N → Set (Set X)) : Prop :=
  ∀ (S : Set N) (B B' : Set X), B ∈ E S → B ⊆ B' → B' ∈ E S

/-! ## Definition 3.4 -/

variable {G G₀ G₁ : GameForm.{u, v, w} N X} {κ : Constitution N X R}

/--
**Peleg's Definition 3.4.** A game form *represents* a constitution when its
α-effectivity function is the effectivity function the constitution induces, at
every coalition.

Print restricts this to *legal* game forms; legality is an informal condition on
the relation between strategies and the assignment of rights, it is not used in
the equality, and it is not imposed here.
-/
@[expose] public def Represents (G : GameForm.{u, v, w} N X)
    (κ : Constitution N X R) : Prop :=
  ∀ C : Set N, effectivity G C = κ.induced C

/--
**A game form's own α-effectivity function, read as a constitution.** No rights
are assigned and the access correspondence ignores them.

This is the object the pre-constitution stand-in was implicitly comparing
against, and `represents_ofGameForm` is why that comparison was strictly weaker
than print's.
-/
@[expose] public def Constitution.ofGameForm (G : GameForm.{u, v, w} N X)
    (R : Type r) : Constitution N X R where
  assign := fun _ => ∅
  access := fun C _ => effectivity G C

/-- **Every game form represents its own α-effectivity function.** Print's
Definition 3.4 is a question about a constitution precisely because this one is
not a question at all. -/
public theorem represents_ofGameForm (G : GameForm.{u, v, w} N X) (R : Type r) :
    Represents G (Constitution.ofGameForm G R) :=
  fun _ => rfl

/-! ### The stand-in, and where it sits

`EffectivityEq` is what the mandate module's `Represents` was before the
constitution existed: two game forms distribute power the same way. It is
retained under a name that says so.
-/

/-- **Two game forms have the same α-effectivity function**, at every coalition.
Not Peleg's Definition 3.4, which compares one game form against a
constitution. -/
@[expose] public def EffectivityEq (G₀ G₁ : GameForm.{u, v, w} N X) : Prop :=
  ∀ C : Set N, effectivity G₀ C = effectivity G₁ C

/-- Equality of effectivity functions is reflexive. -/
public theorem EffectivityEq.refl (G : GameForm.{u, v, w} N X) : EffectivityEq G G :=
  fun _ => rfl

/-- And symmetric, because it is an equality -- unlike `Represents`, whose two
arguments have different types. -/
public theorem EffectivityEq.symm (h : EffectivityEq G₀ G₁) : EffectivityEq G₁ G₀ :=
  fun C => (h C).symm

/-- And transitive. -/
public theorem EffectivityEq.trans {G₂ : GameForm.{u, v, w} N X}
    (h₀ : EffectivityEq G₀ G₁) (h₁ : EffectivityEq G₁ G₂) : EffectivityEq G₀ G₂ :=
  fun C => (h₀ C).trans (h₁ C)

/--
**Exactly how the stand-in was weaker.** Comparing two game forms is
representation against a constitution that was read off one of them, and
`represents_ofGameForm` says every game form passes that test against itself.
-/
public theorem effectivityEq_iff_represents_ofGameForm (R : Type r) :
    EffectivityEq G₀ G₁ ↔ Represents G₀ (Constitution.ofGameForm G₁ R) :=
  Iff.rfl

/-! ## What representation gives -/

/-- **Necessity of Theorem 3.5's condition (ii).** A represented constitution
induces a superadditive effectivity function, because α-effectivity is
superadditive for every game form. -/
public theorem Represents.superadditive (h : Represents G κ) : Superadditive κ.induced := by
  intro S₁ S₂ B₁ B₂ hd h₁ h₂
  rw [← h] at h₁ h₂ ⊢
  exact forces_superadditive hd h₁ h₂

/-- **Condition (3.3) on the diagonal.** A represented constitution induces an
upward-closed effectivity function.

This is as much of Theorem 3.5's condition (i) as representation can see: print
states (3.3) at every set of rights, and a representation constrains only
`γ(S, α(S))`. -/
public theorem Represents.upwardClosed (h : Represents G κ) : UpwardClosed κ.induced := by
  intro S B B' hB hBB'
  rw [← h] at hB ⊢
  exact hB.mono hBB'

/--
**Representation forces the outcome function onto the social states.**

Print assumes surjectivity from Definition 3.3 onward and stipulates
`E_α(∅; Γ) = {A}` by fiat. Here the empty coalition's family is *computed*, so
the two meet: a game form represents a constitution obeying the standing
assumptions only if its outcome function is onto. Print's assumption is
recovered rather than imposed, and this is the check that `Represents` is
print's condition and not a weaker one.
-/
public theorem Represents.surjective_outcome (h : Represents G κ) (hs : κ.Standing) :
    Function.Surjective G.outcome := by
  have hmem : Set.range G.outcome ∈ effectivity G (∅ : Set N) :=
    range_outcome_mem_effectivity_empty
  rw [h ∅, κ.induced_empty hs, Set.mem_singleton_iff] at hmem
  exact Set.range_eq_univ.mp hmem

end AISafetyAtlas.Sovereignty
