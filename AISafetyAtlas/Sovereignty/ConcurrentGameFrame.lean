module

public import AISafetyAtlas.Sovereignty.Separations
public import Mathlib.Data.Set.Basic
public import Mathlib.Data.Set.Lattice
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Fintype.Prod

/-!
# General concurrent game frames, and the eight classes

Chen, Ju & Ågotnes, *Representation theorems for actual and alpha powers over
general concurrent game frames without assuming independence of agents*,
arXiv:2607.10567v1, held as
`chen-ju-agotnes-arxiv-v1-2026-representation-theorems-actual-alpha-powers-general-cgf.pdf`,
sha256 `c7aece726de1b7a7a106c646…`, manifest `SOURCES-2026-09-09-sovereignty.md`,
50 pp. Definitions 1, 5, 8 and 9 and Fact 1 read from rendered pages 6 to 10.
Graded in section 23 of
[`source-coverage-audit.md`](../../docs/provenance/source-coverage-audit.md).

**Two files, two papers.** The literature directory also holds
`chen-ju-agotnes-arxiv-v2-…-two-agent.pdf`. The `v1`/`v2` in those filenames are
**not** version numbers: the second file is arXiv:2603.04160v2, a different
submission over *two-agent* frames. This module renders arXiv:2607.10567 only.

## Why this carrier exists

`AISafetyAtlas.Sovereignty.Separations` has `GameForm`: one joint action, one
outcome, strategies indexed per agent. Section 23 recorded four rows as
**narrower than print** on two axes that a game form cannot express — print's
frames carry a **state set** with the available actions and the outcome function
indexed by state, and print's outcome function returns a **set** of possible
successors rather than one. Both axes are the same move, and this module is it.

`ActionFrame` is print's Definition 1 and `IsGCGF` is Definition 8. Everything
downstream — `AlphaPower`, `ActualPowerAt`, `Serial`, `Independent`,
`Deterministic`, `out_anti_coalition` — is stated at that carrier, so the four
rows are now graded on declarations that quantify over states and over
nondeterministic outcomes.

## Where the two existing carriers sit

* **`GameForm` is the SID corner.** `gameFrame` is the bridge and
  `gameFrame_isFrame_sid` places it: serial when the strategy types are
  inhabited, independent because strategies are dependent functions on disjoint
  index sets, deterministic because `GameForm.outcome` is a function.
  `alphaPower_gameFrame` and `actualPowerAt_gameFrame` identify `Forces` and
  `ActualPower` as its alpha and actual effectivity functions.

  **The state set is the outcome type, not a point.** Section 23 used to say
  `GameForm` is print's SID case *"at a single state"*, and that is wrong in a
  way the bridge fixes: with a one-point state set every alpha power is trivial,
  because a coalition's possible successors are always that point.
  `gameFrame` takes `ST` to be the outcome type `X` with **state-independent**
  dynamics — from every state the same one round is played — which is what makes
  `alphaPower_gameFrame` an equivalence with `Forces`.

* **`AISafetyAtlas.Sovereignty.AATS` is a different corner, and it is not this
  one.** Wooldridge and van der Hoek's system has states, but its availability
  is **per agent** (`AATS.precond`) and its transition is a partial *function*
  (`AATS.step`), so independence and determinism are built in there exactly as
  they are in `GameForm`. It reaches the state axis and neither of the other
  two. No bridge is built here; the taxonomy claim is prose.

## What is not here

The paper's twenty-odd remaining definitions — alpha and actual neighborhood
frames, nonmonotonic cores, representability, groundedness, liveness — and every
numbered theorem. **The representation theorems are what the paper is for**, and
this module claims nothing about representation. It supplies print's carrier and
the facts print says are used implicitly throughout, which is what the four owed
rows asked for.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

/-! ## §2.1: joint actions -/

/--
**Print's restriction.** For `C ⊆ D`, print writes the restriction of a joint
action of `D` to `C` as a subscript bar. Coalitions are sets of agents and a
joint action of `C` is a function out of the coercion of `C`, so restricting is
reindexing along the inclusion.
-/
@[expose] public def restrictJA {AG : Type u} {AC : Type w} {C D : Set AG}
    (h : C ⊆ D) (σ : D → AC) : C → AC :=
  fun i => σ ⟨i.1, h i.2⟩

/-- Restricting to the coalition you already have is doing nothing. -/
public theorem restrictJA_self {AG : Type u} {AC : Type w} {C : Set AG}
    (h : C ⊆ C) (σ : C → AC) : restrictJA h σ = σ :=
  rfl

/-- Restricting twice is restricting once. -/
public theorem restrictJA_restrictJA {AG : Type u} {AC : Type w} {C D E : Set AG}
    (h₁ : C ⊆ D) (h₂ : D ⊆ E) (σ : E → AC) :
    restrictJA h₁ (restrictJA h₂ σ) = restrictJA (h₁.trans h₂) σ :=
  rfl

open Classical in
/--
**Print's `σ_C ∪ σ_D`.** The joint action of `C ∪ D` that plays `σ_C` on `C` and
`σ_D` elsewhere. Print declares the notation for joint actions agreeing on the
overlap; on disjoint coalitions, which is where print's independence condition
uses it, that is automatic and this is the unique such joint action.
-/
@[expose] public noncomputable def jointUnion {AG : Type u} {AC : Type w} {C D : Set AG}
    (σC : C → AC) (σD : D → AC) : (C ∪ D : Set AG) → AC :=
  fun i => if h : i.1 ∈ C then σC ⟨i.1, h⟩ else σD ⟨i.1, i.2.resolve_left h⟩

/-! ## §2.1: action frames -/

/--
**Print's Definition 1, an action frame.** A state set, an action set, and for
every coalition an availability function and an outcome function.

`ST` is print's states, `AC` print's actions, and a joint action of `C` is print's
`JA_C`, a function from the coalition to the action set. `av C s` is the set of
joint actions of `C` available at `s`; `out C s σ` is the set of possible
outcome states when `C` performs `σ` at `s`.

**Wider than print on three axes, and each is a dropped hypothesis.** Print
requires the agent set finite, the state set nonempty and the action set
nonempty. None of the three is carried here: nothing below needs finiteness, and
the two nonemptiness conditions are carried as instance hypotheses on the
theorems that use them rather than built into the carrier.

Print's outcome function is **total** on joint actions, available or not, and so
is this one; print's outcome-driven availability condition in `IsGCGF` is what
ties the two together.
-/
public structure ActionFrame (AG : Type u) (ST : Type v) (AC : Type w) where
  /-- Print's *av*: the joint actions of `C` available at a state. -/
  av : (C : Set AG) → ST → Set (C → AC)
  /-- Print's *out*: the possible successor states of a joint action at a state. -/
  out : (C : Set AG) → ST → (C → AC) → Set ST

variable {AG : Type u} {ST : Type v} {AC : Type w} {F : ActionFrame AG ST AC}

/-! ## §2.2: alpha and actual powers -/

/--
**Print's *safe*.** Performing `σ` at `s` guarantees the next state lies in `X`.
-/
@[expose] public def SafeFor (F : ActionFrame AG ST AC) (C : Set AG) (s : ST)
    (σ : C → AC) (X : Set ST) : Prop :=
  F.out C s σ ⊆ X

/--
**Print's *tight*.** Every state in `X` can occur as an outcome compatible with
performing `σ` at `s`.
-/
@[expose] public def TightFor (F : ActionFrame AG ST AC) (C : Set AG) (s : ST)
    (σ : C → AC) (X : Set ST) : Prop :=
  X ⊆ F.out C s σ

/--
**Print's alpha power.** A set of states that is safe for some *available* joint
action of the coalition at the state.
-/
@[expose] public def AlphaPower (F : ActionFrame AG ST AC) (C : Set AG) (s : ST)
    (X : Set ST) : Prop :=
  ∃ σ ∈ F.av C s, SafeFor F C s σ X

/--
**Print's actual power.** A set of states that is both safe and tight for some
available joint action. `actualPowerAt_iff_out_eq` is print's own "equivalently":
the actual powers are exactly the outcome sets of available joint actions.
-/
@[expose] public def ActualPowerAt (F : ActionFrame AG ST AC) (C : Set AG) (s : ST)
    (X : Set ST) : Prop :=
  ∃ σ ∈ F.av C s, SafeFor F C s σ X ∧ TightFor F C s σ X

/-- **Print's Definition 5**, the alpha effectivity function of an action frame. -/
@[expose] public def alphaEff (F : ActionFrame AG ST AC) (C : Set AG) (s : ST) :
    Set (Set ST) :=
  {X | AlphaPower F C s X}

/-- **Print's Definition 5**, the actual effectivity function of an action frame:
the image of the available joint actions under the outcome function. -/
@[expose] public def actualEff (F : ActionFrame AG ST AC) (C : Set AG) (s : ST) :
    Set (Set ST) :=
  (fun σ => F.out C s σ) '' F.av C s

/-- Print's *"equivalently"*: safe and tight together say the outcome set **is**
the target. -/
public theorem actualPowerAt_iff_out_eq {C : Set AG} {s : ST} {X : Set ST} :
    ActualPowerAt F C s X ↔ ∃ σ ∈ F.av C s, F.out C s σ = X := by
  constructor
  · rintro ⟨σ, hσ, hsafe, htight⟩
    exact ⟨σ, hσ, Set.Subset.antisymm hsafe htight⟩
  · rintro ⟨σ, hσ, heq⟩
    exact ⟨σ, hσ, heq.le, heq.ge⟩

/-- The actual effectivity function collects exactly the actual powers. -/
public theorem mem_actualEff_iff {C : Set AG} {s : ST} {X : Set ST} :
    X ∈ actualEff F C s ↔ ActualPowerAt F C s X := by
  rw [actualPowerAt_iff_out_eq]
  exact ⟨fun ⟨σ, hσ, heq⟩ => ⟨σ, hσ, heq⟩, fun ⟨σ, hσ, heq⟩ => ⟨σ, hσ, heq⟩⟩

/-- **Print's immediate consequence of Definition 5**: each alpha neighborhood is
closed under supersets. -/
public theorem AlphaPower.mono {C : Set AG} {s : ST} {X Y : Set ST}
    (h : AlphaPower F C s X) (hXY : X ⊆ Y) : AlphaPower F C s Y := by
  obtain ⟨σ, hσ, hsafe⟩ := h
  exact ⟨σ, hσ, hsafe.trans hXY⟩

/-- Print's *"actual powers are ... both safe and tight"*: dropping tightness
leaves the alpha notion. -/
public theorem ActualPowerAt.alphaPower {C : Set AG} {s : ST} {X : Set ST}
    (h : ActualPowerAt F C s X) : AlphaPower F C s X := by
  obtain ⟨σ, hσ, hsafe, -⟩ := h
  exact ⟨σ, hσ, hsafe⟩

/-! ## §3: general concurrent game frames -/

/--
**Print's Definition 8.** An action frame is a *general concurrent game frame*
when it satisfies two conditions, both of which say that the grand coalition's
outcome function settles everything else.

* `gci`, print's **grand-coalition-induced outcome condition**: a coalition's
  outcome set is the union of the grand coalition's outcome sets over the
  extensions of its joint action.
* `oda`, print's **outcome-driven availability condition**: a joint action is
  available exactly when its outcome set is non-empty.

Print's own summary: *"under the GCI-condition and the ODA-condition, the
outcome and availability functions of every coalition are determined by the
grand coalition's outcome function."*
-/
public structure IsGCGF (F : ActionFrame AG ST AC) : Prop where
  /-- Print's GCI-condition. -/
  gci : ∀ (C : Set AG) (s : ST) (σ : C → AC),
    F.out C s σ =
      ⋃ σ' ∈ {σ' : ↥(Set.univ : Set AG) → AC | restrictJA (Set.subset_univ C) σ' = σ},
        F.out (Set.univ : Set AG) s σ'
  /-- Print's ODA-condition. -/
  oda : ∀ (C : Set AG) (s : ST), F.av C s = {σ | (F.out C s σ).Nonempty}

namespace IsGCGF

variable (hF : IsGCGF F)
include hF

/--
**The GCI-condition, pointwise.** Every statement below goes through this rather
than through the union, which is why no later proof touches `Set.iUnion` again.
-/
public theorem mem_out_iff {C : Set AG} {s : ST} {σ : C → AC} {t : ST} :
    t ∈ F.out C s σ ↔ ∃ σ' : ↥(Set.univ : Set AG) → AC,
      restrictJA (Set.subset_univ C) σ' = σ ∧ t ∈ F.out (Set.univ : Set AG) s σ' := by
  rw [hF.gci C s σ]
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]

/-- **The ODA-condition, pointwise.** -/
public theorem mem_av_iff {C : Set AG} {s : ST} {σ : C → AC} :
    σ ∈ F.av C s ↔ (F.out C s σ).Nonempty := by
  rw [hF.oda C s]; exact Iff.rfl

/--
**Print's Fact 1, item 1 — outcome monotonicity.** Extending a joint action to a
larger coalition can only shrink the set of possible outcomes.

This is the general-frame statement the SID-corner theorem
`outcomesOf_anti_coalition` was narrower than: it quantifies over states and its
outcome sets are print's nondeterministic ones.
-/
public theorem out_anti_coalition {C D : Set AG} (h : C ⊆ D) (s : ST) (σD : D → AC) :
    F.out D s σD ⊆ F.out C s (restrictJA h σD) := by
  intro t ht
  obtain ⟨σ', hσ', ht'⟩ := hF.mem_out_iff.1 ht
  refine hF.mem_out_iff.2 ⟨σ', ?_, ht'⟩
  rw [← hσ']
  rfl

/--
**Print's Fact 1, item 2 — the alternative GCI-condition.** The same union, taken
over the grand coalition's *available* actions only. Print's reason is the
ODA-condition: unavailable grand-coalition actions have empty outcome sets, so
they contribute nothing.
-/
public theorem out_eq_iUnion_av (C : Set AG) (s : ST) (σ : C → AC) :
    F.out C s σ =
      ⋃ σ' ∈ {σ' : ↥(Set.univ : Set AG) → AC |
          σ' ∈ F.av (Set.univ : Set AG) s ∧ restrictJA (Set.subset_univ C) σ' = σ},
        F.out (Set.univ : Set AG) s σ' := by
  ext t
  simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
  constructor
  · intro ht
    obtain ⟨σ', hσ', ht'⟩ := hF.mem_out_iff.1 ht
    exact ⟨σ', ⟨hF.mem_av_iff.2 ⟨t, ht'⟩, hσ'⟩, ht'⟩
  · rintro ⟨σ', ⟨-, hσ'⟩, ht'⟩
    exact hF.mem_out_iff.2 ⟨σ', hσ', ht'⟩

/--
**Every available joint action extends to an available grand-coalition action.**
Print never states this, and it is the step both results below run through: the
ODA-condition makes an available action's outcome set non-empty, and the
GCI-condition turns a point of that set into the extension.
-/
public theorem exists_av_univ_restrict {C : Set AG} {s : ST} {σ : C → AC}
    (hσ : σ ∈ F.av C s) :
    ∃ σ' ∈ F.av (Set.univ : Set AG) s, restrictJA (Set.subset_univ C) σ' = σ := by
  obtain ⟨t, ht⟩ := hF.mem_av_iff.1 hσ
  obtain ⟨σ', hσ', ht'⟩ := hF.mem_out_iff.1 ht
  exact ⟨σ', hF.mem_av_iff.2 ⟨t, ht'⟩, hσ'⟩

/--
**Enlarging a coalition cannot destroy an alpha power**, at every general
concurrent game frame.

Print names this property of alpha powers and uses it in the proof of its Fact 2.
The SID-corner theorem `Forces.mono_coalition` carries print's seriality as an
instance hypothesis; **here seriality is not needed at all.** The ODA-condition
already makes the smaller coalition's action extend to an available
grand-coalition action, and restricting that extension to the larger coalition
gives an available action whose outcome set is contained in the original one by
outcome monotonicity.
-/
public theorem alphaPower_mono_coalition {C D : Set AG} (h : C ⊆ D) {s : ST} {X : Set ST}
    (hX : AlphaPower F C s X) : AlphaPower F D s X := by
  obtain ⟨σ, hσ, hsafe⟩ := hX
  obtain ⟨σ', hσ'av, hσ'res⟩ := hF.exists_av_univ_restrict hσ
  refine ⟨restrictJA (Set.subset_univ D) σ', ?_, ?_⟩
  · refine hF.mem_av_iff.2 ?_
    obtain ⟨t, ht⟩ := hF.mem_av_iff.1 hσ'av
    exact ⟨t, hF.out_anti_coalition (Set.subset_univ D) s σ' ht⟩
  · refine (hF.out_anti_coalition h s (restrictJA (Set.subset_univ D) σ')).trans ?_
    rw [restrictJA_restrictJA, hσ'res]
    exact hsafe

/--
**No coalition is ever effective for the empty set.**

Print does not state this and it is one line from the two conditions of
Definition 8: an available joint action has a non-empty outcome set, and nothing
non-empty is contained in the empty set.

It is also why print's **superadditivity is not a theorem** of these frames.
Two disjoint coalitions with disjoint alpha powers would make their union
effective for the empty set, so at a frame where that happens superadditivity
must fail — and `AISafetyAtlas.Examples.Sovereignty.exists_gcgf_not_superadditive`
exhibits one. `forces_superadditive` is a theorem about game forms precisely
because print's independence condition holds there by construction.
-/
public theorem not_alphaPower_empty (C : Set AG) (s : ST) :
    ¬ AlphaPower F C s (∅ : Set ST) := by
  rintro ⟨σ, hσ, hsafe⟩
  obtain ⟨t, ht⟩ := hF.mem_av_iff.1 hσ
  exact hsafe ht

end IsGCGF

/-! ## Print's "determined by the grand-coalition outcome function" -/

/--
**Print's summary of Definition 8, as a construction.** *"Under the
GCI-condition and the ODA-condition, the outcome and availability functions of
every coalition are determined by the grand coalition's outcome function."*

`ActionFrame.ofGrand` is that determination: it reads both conditions as
definitions, `ofGrand_out_univ` says it leaves the grand coalition's outcome
function alone, and `ofGrand_isGCGF` says the result is a general concurrent
game frame. Print states the dependence and never builds the map.
-/
@[expose] public def ActionFrame.ofGrand
    (g : ST → (↥(Set.univ : Set AG) → AC) → Set ST) : ActionFrame AG ST AC where
  av := fun C s => {σ | ∃ x : ST, ∃ σ' : ↥(Set.univ : Set AG) → AC,
    restrictJA (Set.subset_univ C) σ' = σ ∧ x ∈ g s σ'}
  out := fun C s σ => {x | ∃ σ' : ↥(Set.univ : Set AG) → AC,
    restrictJA (Set.subset_univ C) σ' = σ ∧ x ∈ g s σ'}

/-- The construction leaves the grand coalition's outcome function unchanged. -/
public theorem ofGrand_out_univ (g : ST → (↥(Set.univ : Set AG) → AC) → Set ST)
    (s : ST) (σ : ↥(Set.univ : Set AG) → AC) :
    (ActionFrame.ofGrand g).out (Set.univ : Set AG) s σ = g s σ := by
  ext x
  constructor
  · rintro ⟨σ', hσ', hx⟩
    rw [restrictJA_self] at hσ'
    exact hσ' ▸ hx
  · intro hx
    exact ⟨σ, restrictJA_self _ σ, hx⟩

/-- Everything built this way satisfies both of print's conditions. -/
public theorem ofGrand_isGCGF (g : ST → (↥(Set.univ : Set AG) → AC) → Set ST) :
    IsGCGF (ActionFrame.ofGrand g) := by
  constructor
  · intro C s σ
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop, ofGrand_out_univ]
    exact ⟨fun ⟨σ', hσ', hx⟩ => ⟨σ', hσ', hx⟩, fun ⟨σ', hσ', hx⟩ => ⟨σ', hσ', hx⟩⟩
  · intro C s
    ext σ
    exact ⟨fun ⟨x, σ', hσ', hx⟩ => ⟨x, σ', hσ', hx⟩, fun ⟨x, σ', hσ', hx⟩ => ⟨x, σ', hσ', hx⟩⟩

/-! ## §3: Definition 9, and the eight classes -/

/-- **Print's seriality.** Every coalition has an available joint action at every
state.

This is the axis `GameForm` could not express. There, inhabitance of the strategy
types is a property of the *types*, so it cannot hold at one state and fail at
another; print's motivating case is a game that ends, where later states have
nothing available. -/
@[expose] public def Serial (F : ActionFrame AG ST AC) : Prop :=
  ∀ (C : Set AG) (s : ST), (F.av C s).Nonempty

/-- **Print's independence.** For disjoint coalitions, actions available to each
are jointly available to their union. -/
@[expose] public def Independent (F : ActionFrame AG ST AC) : Prop :=
  ∀ (s : ST) (C D : Set AG), Disjoint C D →
    ∀ σC ∈ F.av C s, ∀ σD ∈ F.av D s, jointUnion σC σD ∈ F.av (C ∪ D) s

/-- **Print's determinism.** Every available grand-coalition action has a
singleton outcome set. -/
@[expose] public def Deterministic (F : ActionFrame AG ST AC) : Prop :=
  ∀ (s : ST), ∀ σ ∈ F.av (Set.univ : Set AG) s, ∃ t : ST, F.out (Set.univ : Set AG) s σ = {t}

/--
**Print's `ES`, the eight labels.** A label records which of print's three
conditions are *imposed*.
-/
public structure FrameClass where
  /-- Whether the label imposes seriality. -/
  serial : Bool
  /-- Whether the label imposes independence. -/
  independent : Bool
  /-- Whether the label imposes determinism. -/
  deterministic : Bool
deriving DecidableEq

/-- A label is three bits: seriality, independence, determinism. -/
@[expose] public def FrameClass.equivProd : FrameClass ≃ Bool × Bool × Bool where
  toFun X := (X.serial, X.independent, X.deterministic)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

public instance : Fintype FrameClass := Fintype.ofEquiv _ FrameClass.equivProd.symm

/-- Print's *"`ES = {ε, S, I, D, SI, SD, ID, SID}`"*: there are eight labels. -/
public theorem card_frameClass : Fintype.card FrameClass = 8 := by
  rw [Fintype.card_congr FrameClass.equivProd]
  decide

/-- Print's `SID`, the label imposing all three. -/
@[expose] public def FrameClass.sid : FrameClass := ⟨true, true, true⟩

/-- Print's `ε`, the label imposing none. -/
@[expose] public def FrameClass.epsilon : FrameClass := ⟨false, false, false⟩

/-- **Print's `X`-frame.** A general concurrent game frame satisfying the
properties the label indicates — and, per print's own caution, saying nothing
about the properties it does not. -/
@[expose] public def IsFrame (X : FrameClass) (F : ActionFrame AG ST AC) : Prop :=
  IsGCGF F ∧ (X.serial → Serial F) ∧ (X.independent → Independent F) ∧
    (X.deterministic → Deterministic F)

/--
**Print's caution, as a theorem.** *"The labels in `ES` record which frame
conditions are imposed; they do not record which conditions are required to fail.
Thus the eight classes are not intended to be disjoint."*

Weakening a label cannot lose a frame, so the strongest label's frames lie in all
eight classes at once — `isFrame_of_sid` is that at `SID`. The docstring of
`forces_superadditive` used to invert this, saying superadditivity *is not
available* in the classes that drop independence; print says only that it is not
imposed.
-/
public theorem isFrame_mono {X Y : FrameClass}
    (hs : X.serial = true → Y.serial = true)
    (hi : X.independent = true → Y.independent = true)
    (hd : X.deterministic = true → Y.deterministic = true)
    (h : IsFrame Y F) : IsFrame X F :=
  ⟨h.1, fun hx => h.2.1 (hs hx), fun hx => h.2.2.1 (hi hx), fun hx => h.2.2.2 (hd hx)⟩

/-- An `SID`-frame is an `X`-frame for every one of print's eight labels. -/
public theorem isFrame_of_sid (X : FrameClass) (h : IsFrame FrameClass.sid F) :
    IsFrame X F :=
  isFrame_mono (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) h

/-- Being an `ε`-frame is being a general concurrent game frame and nothing more. -/
public theorem isFrame_epsilon_iff : IsFrame FrameClass.epsilon F ↔ IsGCGF F :=
  ⟨fun h => h.1, fun h => ⟨h, fun hx => by simp [FrameClass.epsilon] at hx,
    fun hx => by simp [FrameClass.epsilon] at hx, fun hx => by simp [FrameClass.epsilon] at hx⟩⟩

/-- Being an `SID`-frame is print's three conditions together. -/
public theorem isFrame_sid_iff :
    IsFrame FrameClass.sid F ↔ IsGCGF F ∧ Serial F ∧ Independent F ∧ Deterministic F :=
  ⟨fun h => ⟨h.1, h.2.1 rfl, h.2.2.1 rfl, h.2.2.2 rfl⟩,
    fun h => ⟨h.1, fun _ => h.2.1, fun _ => h.2.2.1, fun _ => h.2.2.2⟩⟩

/-! ## The bridge: where `GameForm` sits -/

section Bridge

variable {N : Type u} {X : Type v} {G : GameForm.{u, v, w} N X}

/-- The action set of the frame a game form induces: an agent together with one
of *its* strategies. Print's action set is shared by all agents, so a joint
action may be mistyped; `gameOut` gives every mistyped joint action the empty
outcome set, and the outcome-driven availability condition then makes it
unavailable. -/
public abbrev GameAction (G : GameForm.{u, v, w} N X) : Type (max u w) :=
  Σ i : N, G.strategy i

/-- The possible outcomes of a joint action, read as the outcomes of the complete
profiles that agree with it. Mistyped joint actions have none. -/
@[expose] public def gameOut (G : GameForm.{u, v, w} N X) (C : Set N) (_s : X)
    (σ : C → GameAction G) : Set X :=
  {x | ∃ t : ∀ i, G.strategy i,
    (∀ i : C, (⟨i.1, t i.1⟩ : GameAction G) = σ i) ∧ G.outcome t = x}

/--
**The frame a game form induces.** States are the outcomes and the dynamics are
state-independent: from every state the same single round is played.

This is what section 23 meant by *"the SID case at a single state"*, corrected.
A one-point state set would make every alpha power trivial; the outcome type is
the state set that makes `alphaPower_gameFrame` an equivalence with `Forces`.
-/
@[expose] public def gameFrame (G : GameForm.{u, v, w} N X) : ActionFrame N X (GameAction G) where
  av := fun C s => {σ | (gameOut G C s σ).Nonempty}
  out := gameOut G

/-- The outcome set of a joint action is the `Separations` outcome set of the
strategies it names. -/
public theorem gameOut_eq_outcomesOf (C : Set N) (s : X) (sC : ∀ i : C, G.strategy i) :
    gameOut G C s (fun i => ⟨i.1, sC i⟩) = outcomesOf G C sC := by
  ext x
  constructor
  · rintro ⟨t, hagree, rfl⟩
    refine ⟨t, fun i => ?_, rfl⟩
    exact eq_of_heq (Sigma.mk.inj (hagree i)).2
  · rintro ⟨t, hagree, rfl⟩
    exact ⟨t, fun i => by rw [hagree i], rfl⟩

/-- **The induced frame is a general concurrent game frame.** The
outcome-driven availability condition holds by construction, and the
grand-coalition-induced outcome condition holds because a complete profile *is* a
grand-coalition joint action. -/
public theorem gameFrame_isGCGF : IsGCGF (gameFrame G) := by
  constructor
  · intro C s σ
    ext x
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, exists_prop]
    constructor
    · rintro ⟨t, hagree, rfl⟩
      refine ⟨fun j => ⟨j.1, t j.1⟩, ?_, ⟨t, fun _ => rfl, rfl⟩⟩
      funext i
      exact hagree i
    · rintro ⟨σ', hσ', t, hagree, rfl⟩
      refine ⟨t, fun i => ?_, rfl⟩
      rw [← hσ']
      exact hagree ⟨i.1, Set.mem_univ _⟩
  · intro C s
    rfl

open Classical in
/-- A completion of a coalition's strategies to a complete profile. Print's
frames have no such notion; it is the bookkeeping that turns a joint action of a
coalition into a witness that the joint action is available. -/
private noncomputable def completion [∀ i, Nonempty (G.strategy i)] {C : Set N}
    (sC : ∀ i : C, G.strategy i) : ∀ i, G.strategy i :=
  fun i => if h : i ∈ C then sC ⟨i, h⟩ else Classical.arbitrary _

open Classical in
private theorem completion_agrees [∀ i, Nonempty (G.strategy i)] {C : Set N}
    (sC : ∀ i : C, G.strategy i) (i : C) : completion sC i.1 = sC i :=
  dif_pos i.2

private theorem gameOut_nonempty [∀ i, Nonempty (G.strategy i)] {C : Set N} (s : X)
    (sC : ∀ i : C, G.strategy i) :
    (gameOut G C s (fun i => ⟨i.1, sC i⟩)).Nonempty :=
  ⟨G.outcome (completion sC), completion sC,
    fun i => by rw [completion_agrees sC i], rfl⟩

/-- **Alpha power in the induced frame is `α`-forcing.** Print's alpha
effectivity function of the induced frame is the game form's forcing relation, at
every state. -/
public theorem alphaPower_gameFrame [∀ i, Nonempty (G.strategy i)]
    (C : Set N) (s : X) (A : Set X) :
    AlphaPower (gameFrame G) C s A ↔ Forces G C A := by
  constructor
  · rintro ⟨σ, ⟨x, t, hagree, -⟩, hsafe⟩
    refine ⟨fun i => t i.1, fun t' ht' => ?_⟩
    refine hsafe ⟨t', fun i => ?_, rfl⟩
    rw [ht' i, hagree i]
  · rintro ⟨sC, hsC⟩
    refine ⟨fun i => ⟨i.1, sC i⟩, gameOut_nonempty s sC, ?_⟩
    rintro x ⟨t, hagree, rfl⟩
    exact hsC t (fun i => eq_of_heq (Sigma.mk.inj (hagree i)).2)

/-- **The alpha effectivity function of the induced frame is the game form's
effectivity family.** -/
public theorem alphaEff_gameFrame [∀ i, Nonempty (G.strategy i)] (C : Set N) (s : X) :
    alphaEff (gameFrame G) C s = effectivity G C := by
  ext A
  exact alphaPower_gameFrame C s A

/-- **Actual power in the induced frame is the game form's actual power.** -/
public theorem actualPowerAt_gameFrame [∀ i, Nonempty (G.strategy i)]
    (C : Set N) (s : X) (A : Set X) :
    ActualPowerAt (gameFrame G) C s A ↔ ActualPower G C A := by
  rw [actualPowerAt_iff_out_eq, actualPower_iff]
  constructor
  · rintro ⟨σ, ⟨x, t, hagree, -⟩, heq⟩
    have hσ : σ = fun i => (⟨i.1, t i.1⟩ : GameAction G) := funext fun i => (hagree i).symm
    subst hσ
    exact ⟨fun i => t i.1, (gameOut_eq_outcomesOf C s (fun i => t i.1)).symm.trans heq⟩
  · rintro ⟨sC, heq⟩
    exact ⟨fun i => ⟨i.1, sC i⟩, gameOut_nonempty s sC,
      (gameOut_eq_outcomesOf C s sC).trans heq⟩

/-- The induced frame is serial when the strategy types are inhabited — print's
condition, at every state. -/
public theorem gameFrame_serial [∀ i, Nonempty (G.strategy i)] : Serial (gameFrame G) :=
  fun _C s => ⟨fun i => ⟨i.1, Classical.arbitrary _⟩, gameOut_nonempty s _⟩

/-- The induced frame is independent, and no hypothesis is needed: two joint
actions on disjoint coalitions are witnessed by one profile, because the witness
for the second is already a complete profile. -/
public theorem gameFrame_independent : Independent (gameFrame G) := by
  classical
  rintro s C D - σC ⟨x, tC, hC, -⟩ σD ⟨y, tD, hD, -⟩
  refine ⟨G.outcome (fun i => if _ : i ∈ C then tC i else tD i), _, fun i => ?_, rfl⟩
  by_cases h : i.1 ∈ C
  · rw [show (if _ : i.1 ∈ C then tC i.1 else tD i.1) = tC i.1 from dif_pos h,
      show jointUnion σC σD i = σC ⟨i.1, h⟩ from dif_pos h]
    exact hC ⟨i.1, h⟩
  · rw [show (if _ : i.1 ∈ C then tC i.1 else tD i.1) = tD i.1 from dif_neg h,
      show jointUnion σC σD i = σD ⟨i.1, i.2.resolve_left h⟩ from dif_neg h]
    exact hD ⟨i.1, i.2.resolve_left h⟩

/-- The induced frame is deterministic: a complete profile settles the outcome,
which is print's condition made structural. -/
public theorem gameFrame_deterministic : Deterministic (gameFrame G) := by
  rintro s σ ⟨x, t, hagree, rfl⟩
  refine ⟨G.outcome t, ?_⟩
  ext y
  constructor
  · rintro ⟨t', hagree', rfl⟩
    refine congrArg G.outcome (funext fun i => ?_)
    have h := (hagree' ⟨i, Set.mem_univ i⟩).trans (hagree ⟨i, Set.mem_univ i⟩).symm
    exact eq_of_heq (Sigma.mk.inj h).2
  · rintro rfl
    exact ⟨t, hagree, rfl⟩

/--
**`GameForm` is print's `SID` corner.** The three conditions of Definition 9 hold
of the induced frame, so every row section 23 graded against `GameForm` is a row
about the most restrictive of print's eight classes — which, print says, *"the
standard class of concurrent game frames corresponds to"* and is the one Pauly's
representation theorem assumes.
-/
public theorem gameFrame_isFrame_sid [∀ i, Nonempty (G.strategy i)] :
    IsFrame FrameClass.sid (gameFrame G) :=
  isFrame_sid_iff.2 ⟨gameFrame_isGCGF, gameFrame_serial, gameFrame_independent,
    gameFrame_deterministic⟩

end Bridge

end AISafetyAtlas.Sovereignty
