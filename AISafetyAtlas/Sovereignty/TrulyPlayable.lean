module

public import AISafetyAtlas.Sovereignty.PlayableConverse
public import Mathlib.Order.Filter.Finite

/-!
# Truly playable effectivity functions

`PlayableConverse` shows that Pauly's five conditions do not characterize the
effectivity functions of strategic games: the cofinite filter on `ℕ` satisfies all
five and is no game form's. This module carries the repair, and it is not this
atlas's either.

Valentin Goranko, Wojciech Jamroga and Paolo Turrini, *Strategic Games and Truly
Playable Effectivity Functions*, Autonomous Agents and Multi-Agent Systems 26:
288-314 (2013), DOI `10.1007/s10458-012-9192-y`, conference version AAMAS 2011.
Pinned in `SOURCES-2026-09-09-sovereignty.md`
as the author manuscript, the published text being subscription-only; statements
below were read from rendered images of manuscript pages 5, 6 and 13, because
text extraction drops mathematics from this file as it does from Pauly's.

## What is here

| print | here |
|---|---|
| Definition 4, nonmonotonic core, which they attribute to Pauly | `nonmonotonicCore` |
| Definition 5, complete nonmonotonic core | `CompleteCore` |
| Definition 8, truly playable | `TrulyPlayable` |
| Definition 9, crown | `IsCrown` |
| Proposition 1 (1), `E(∅)` is a filter | `Playable.emptyFilter`, `Playable.emptyFilter_neBot`; the four conditions separately as `Playable.mem_empty_univ`, `Playable.inter_mem_empty`, `Playable.upward_mem_empty`, `Playable.empty_not_mem_empty` |
| Proposition 1 (2), `E_nc(∅)` is empty or a singleton | `Playable.subsingleton_nonmonotonicCore_empty` |
| Proposition 2, an `α`-effectivity function's core at `∅` is `{Z}`, `Z` the reachable set | `nonmonotonicCore_effectivity_empty`, `trulyPlayable_effectivity` |
| Proposition 5 (1) ⇔ (2) ⇔ (3) | `Playable.trulyPlayable_iff_nonmonotonicCore_empty_nonempty`, `Playable.trulyPlayable_iff_principal`, `Playable.trulyPlayable_iff_emptyFilter_principal` |
| Proposition 6, on a finite domain playability and true playability coincide | `Playable.trulyPlayable_of_finite` |

## The one place this is wider than print

**Corrected 2026-09-10.** This section said *"Print's route to true playability
from finiteness is not stated in the paper; it is in the Lean 3 development
`kaiobendrauf/cl-lean`"*. That is false. It is **Proposition 6**, on manuscript
page 14, immediately after the proof of Proposition 5: *"We also observe that on
finite domains playability and true playability coincide. Every playable
effectivity function on a finite domain is truly playable."* Its proof is one
line -- *"by Proposition 5.3 and the fact that every filter on a finite set is
principal"* -- and `Playable.trulyPlayable_of_finite` is that proposition.
`cl-lean` is where the finite route was found in Lean, which is a different claim
and the only one this module is entitled to make.

What is genuinely wider is the hypothesis. Print and `cl-lean` both take the
outcome type finite; the argument consumes strictly less, namely that the
*family* `E ∅` has a minimal element, and finiteness of the outcome type is one
way to get one. So the general form here is

* `Playable.trulyPlayable_of_exists_minimal` -- a minimal element of `E ∅` is
  enough, with no finiteness anywhere;
* `Playable.trulyPlayable_of_finite_empty` -- at `(E ∅).Finite`;
* `Playable.trulyPlayable_of_finite` -- at `Finite X`, which is print's own
  Proposition 6 and `cl-lean`'s hypothesis alike. Since 2026-09-10 this is proved
  the way print proves it, through `Playable.emptyFilter` and Mathlib's
  every-filter-on-a-finite-set-is-principal, rather than through the minimal
  element; `Playable.trulyPlayable_of_finite_empty` likewise. The minimal-element
  route is still the general one and still carries
  `Playable.trulyPlayable_of_exists_minimal`.

`cl-lean` is a separate development under no licence and on Lean 3, so nothing
here is derived from it; it is named because it is where the finite route was
found, and because its own file header is what identifies the paper above.

The separating fact is `nonmonotonicCore_cofiniteEff_empty`: the cofinite filter's
core at the empty coalition is *empty*, which is print's own reason -- *"there are
no minimal cofinite sets"* -- and gives `not_exists_gameForm_cofiniteEff` a second
proof following print's route through Proposition 2 rather than through the least
element directly.

## What is not here

Print's Proposition 5 (4), the equivalence with `IsCrown`, is stated as
`IsCrown` and not proved. And their Section 4.2 proves the *corrected* Theorem
3.2 -- `E` is the effectivity function of a strategic game iff `E` is truly
playable -- by revising Pauly's construction. `paulyGame` in `PlayableConverse` is
that construction unrevised, so it is one step short of the corrected theorem,
which is the natural next result and is not attempted here.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

variable {N : Type u} {X : Type v} {E : Set N → Set (Set X)}

/-! ## Definitions 4, 5, 8 and 9 -/

/-- **Definition 4**, the nonmonotonic core, which Goranko, Jamroga and Turrini
attribute to Pauly: the minimal sets of `E C`.

> `E_nc(C) = {X ∈ E(C) | ¬∃Y (Y ∈ E(C) and Y ⊊ X)}` -/
@[expose] public def nonmonotonicCore (E : Set N → Set (Set X)) (C : Set N) :
    Set (Set X) :=
  {A | A ∈ E C ∧ ¬ ∃ B, B ∈ E C ∧ B ⊂ A}

/-- **Definition 5**, completeness of the nonmonotonic core.

> `E_nc(C)` is complete iff for every `X ∈ E(C)` there exists `Y ∈ E_nc(C)` such
> that `Y ⊆ X`. -/
@[expose] public def CompleteCore (E : Set N → Set (Set X)) (C : Set N) : Prop :=
  ∀ A ∈ E C, ∃ B ∈ nonmonotonicCore E C, B ⊆ A

/-- **Definition 8**, truly playable.

> An effectivity function `E` is truly playable iff it is playable and `E(∅)` has
> a complete nonmonotonic core. -/
@[expose] public def TrulyPlayable (E : Set N → Set (Set X)) : Prop :=
  Playable E ∧ CompleteCore E (∅ : Set N)

/-- **Definition 9**, a crown.

> An effectivity function `E` is a crown iff `X ∈ E(N)` implies `{x} ∈ E(N)` for
> some `x ∈ X`.

Stated for the record; print's Proposition 5 (4) makes this equivalent to
`TrulyPlayable` for a playable `E`, and that equivalence is not proved here. -/
@[expose] public def IsCrown (E : Set N → Set (Set X)) : Prop :=
  ∀ A ∈ E (Set.univ : Set N), ∃ x ∈ A, ({x} : Set X) ∈ E (Set.univ : Set N)

/-! ## Proposition 1 (1): `E ∅` is a filter

Print states this as one clause. The four conditions its footnote 2 lists for a
filter are separated here, because each is a different field of `Playable` and
nothing downstream wants them bundled. -/

/-- `E ∅` is non-empty, by safety. -/
public theorem Playable.mem_empty_univ (hE : Playable E) :
    (Set.univ : Set X) ∈ E (∅ : Set N) :=
  hE.safe ∅

/-- `E ∅` is closed under binary intersection, by superadditivity at the empty
coalition against itself -- the one coalition disjoint from itself. -/
public theorem Playable.inter_mem_empty (hE : Playable E) {A B : Set X}
    (hA : A ∈ E (∅ : Set N)) (hB : B ∈ E (∅ : Set N)) : A ∩ B ∈ E (∅ : Set N) := by
  have h := hE.superadd (∅ : Set N) (∅ : Set N) A B (disjoint_bot_left) hA hB
  simpa using h

/-- `E ∅` is closed under supersets, by outcome-monotonicity. -/
public theorem Playable.upward_mem_empty (hE : Playable E) {A B : Set X}
    (hAB : A ⊆ B) (hA : A ∈ E (∅ : Set N)) : B ∈ E (∅ : Set N) :=
  hE.mono ∅ A B hAB hA

/-- `E ∅` is proper, by liveness. -/
public theorem Playable.empty_not_mem_empty (hE : Playable E) :
    (∅ : Set X) ∉ E (∅ : Set N) :=
  hE.live ∅

/-! ### Proposition 1 (1), as the object print names

Print does not say `E ∅` has four closure properties; it says **`E(∅)` is a
filter**, and its footnote 2 spells out the four conditions -- `Ω ∈ F`, `∅ ∉ F`,
closed under finite intersection, closed under supersets -- which are Mathlib's
`Filter` plus `NeBot`. Building the object rather than restating its axioms is
what lets print's own proof of Proposition 6 be the proof here: *"every filter on
a finite set is principal"* is a Mathlib lemma, not something this module has to
argue. -/

/-- **Proposition 1 (1).** `E ∅` is a filter on the outcome type. -/
@[expose] public noncomputable def Playable.emptyFilter (hE : Playable E) : Filter X where
  sets := E (∅ : Set N)
  univ_sets := hE.mem_empty_univ
  sets_of_superset := fun hA hAB => hE.upward_mem_empty hAB hA
  inter_sets := fun hA hB => hE.inter_mem_empty hA hB

/-- Membership in the filter is membership in `E ∅`, by construction. -/
@[simp] public theorem Playable.mem_emptyFilter {hE : Playable E} {A : Set X} :
    A ∈ hE.emptyFilter ↔ A ∈ E (∅ : Set N) := Iff.rfl

/-- And it is **proper** -- print's footnote condition (2), which is what
distinguishes a filter from the improper one that is all of `2^Ω`. -/
public theorem Playable.emptyFilter_neBot (hE : Playable E) : hE.emptyFilter.NeBot :=
  Filter.neBot_iff.mpr fun h =>
    hE.empty_not_mem_empty (Playable.mem_emptyFilter.mp (Filter.empty_mem_iff_bot.mpr h))

/-! ## The general lemma, and Proposition 1 (2)

A minimal element of `E ∅` is automatically a least element. This is the whole
content of Proposition 1 (2), and it is what makes the empty coalition special:
superadditivity applies to a coalition against itself only at `∅`. -/

/-- **A minimal element of `E ∅` is least.** Print derives this inside
Proposition 1 (2); it is stated separately because everything below consumes it.

No finiteness, and no hypothesis on `X` at all. -/
public theorem Playable.subset_of_mem_nonmonotonicCore_empty (hE : Playable E)
    {A : Set X} (hA : A ∈ nonmonotonicCore E (∅ : Set N)) {B : Set X}
    (hB : B ∈ E (∅ : Set N)) : A ⊆ B := by
  have hinter : A ∩ B ∈ E (∅ : Set N) := hE.inter_mem_empty hA.1 hB
  rcases Set.eq_or_ssubset_of_subset (Set.inter_subset_left (s := A) (t := B)) with heq | hlt
  · exact Set.inter_eq_left.mp heq
  · exact absurd ⟨A ∩ B, hinter, hlt⟩ hA.2

/-- **Proposition 1 (2)**: `E_nc(∅)` is either empty or a singleton.

> Suppose `E_nc(∅)` is non-empty, and let `X, Y ∈ E_nc(∅)`. Then, coalition `∅`
> is effective for each of `X` and `Y`, hence, by superadditivity, it is effective
> for `X ∩ Y`. By the definition of `E_nc(∅)`, it follows that `X = X ∩ Y = Y`. -/
public theorem Playable.subsingleton_nonmonotonicCore_empty (hE : Playable E) :
    Set.Subsingleton (nonmonotonicCore E (∅ : Set N)) := by
  intro A hA B hB
  exact Set.Subset.antisymm (hE.subset_of_mem_nonmonotonicCore_empty hA hB.1)
    (hE.subset_of_mem_nonmonotonicCore_empty hB hA.1)

/-! ## Proposition 5, (1) ⇔ (2) ⇔ (3) -/

/-- **Proposition 5, (1) ⇔ (2)**: a playable `E` is truly playable exactly when
`E_nc(∅)` is non-empty. Print's `(1) ⇒ (2)` is *"immediate, by safety"*: the whole
outcome space is in `E ∅`, so completeness hands back a core element below it. -/
public theorem Playable.trulyPlayable_iff_nonmonotonicCore_empty_nonempty
    (hE : Playable E) :
    TrulyPlayable E ↔ (nonmonotonicCore E (∅ : Set N)).Nonempty := by
  constructor
  · rintro ⟨-, hcomplete⟩
    obtain ⟨B, hB, -⟩ := hcomplete Set.univ hE.mem_empty_univ
    exact ⟨B, hB⟩
  · rintro ⟨A, hA⟩
    exact ⟨hE, fun B hB => ⟨A, hA, hE.subset_of_mem_nonmonotonicCore_empty hA hB⟩⟩

/-- **Proposition 5, (1) ⇔ (3)**: truly playable exactly when `E ∅` is a principal
filter. Print says *"`E_nc(∅)` is a singleton and `E(∅)` is a principal filter,
generated by `E_nc(∅)`"*; the generator is the least element. -/
public theorem Playable.trulyPlayable_iff_principal (hE : Playable E) :
    TrulyPlayable E ↔ ∃ A : Set X, A ∈ E (∅ : Set N) ∧ ∀ B ∈ E (∅ : Set N), A ⊆ B := by
  rw [hE.trulyPlayable_iff_nonmonotonicCore_empty_nonempty]
  constructor
  · rintro ⟨A, hA⟩
    exact ⟨A, hA.1, fun B hB => hE.subset_of_mem_nonmonotonicCore_empty hA hB⟩
  · rintro ⟨A, hAmem, hAleast⟩
    refine ⟨A, hAmem, ?_⟩
    rintro ⟨B, hBmem, hBlt⟩
    exact absurd (hBlt.subset.antisymm (hAleast B hBmem)) hBlt.ne

/-- **Proposition 5, (1) ⇔ (3), in print's own words.** The previous lemma states
principality by exhibiting a least element; this states it as Mathlib states it,
`hE.emptyFilter = Filter.principal A`. Print writes *"`E(∅)` is a principal
filter, generated by `E_nc(∅)`"*, and with `emptyFilter` in hand that sentence is
a statement about a `Filter` rather than a paraphrase of one. -/
public theorem Playable.trulyPlayable_iff_emptyFilter_principal (hE : Playable E) :
    TrulyPlayable E ↔ ∃ A : Set X, hE.emptyFilter = Filter.principal A := by
  rw [hE.trulyPlayable_iff_principal]
  constructor
  · rintro ⟨A, hAmem, hAleast⟩
    refine ⟨A, Filter.ext fun B => ?_⟩
    simp only [Playable.mem_emptyFilter, Filter.mem_principal]
    exact ⟨fun hB => hAleast B hB, fun hAB => hE.upward_mem_empty hAB hAmem⟩
  · rintro ⟨A, hA⟩
    have hmem : ∀ B, B ∈ E (∅ : Set N) ↔ A ⊆ B := by
      intro B
      have : B ∈ hE.emptyFilter ↔ B ∈ Filter.principal A := by rw [hA]
      simpa [Filter.mem_principal] using this
    exact ⟨A, (hmem A).mpr Set.Subset.rfl, fun B hB => (hmem B).mp hB⟩

/-! ## Getting a minimal element: the generality this module adds

Print's Proposition 6 reaches true playability from a finite domain, and
`cl-lean` from a finite outcome type. The argument needs strictly less than
either. -/

/-- **A minimal element of `E ∅` suffices.** The general form: no finiteness on
`X`, and none on the family either. -/
public theorem Playable.trulyPlayable_of_exists_minimal (hE : Playable E)
    (h : ∃ A ∈ E (∅ : Set N), ∀ B ∈ E (∅ : Set N), ¬ B ⊂ A) : TrulyPlayable E := by
  obtain ⟨A, hAmem, hAmin⟩ := h
  refine hE.trulyPlayable_iff_nonmonotonicCore_empty_nonempty.mpr ⟨A, hAmem, ?_⟩
  rintro ⟨B, hBmem, hBlt⟩
  exact hAmin B hBmem hBlt

/-- **A finite family suffices**, which is weaker than a finite outcome type: it
constrains `E ∅` and says nothing about `X`. -/
public theorem Playable.trulyPlayable_of_finite_empty (hE : Playable E)
    (hfin : (E (∅ : Set N)).Finite) : TrulyPlayable E :=
  hE.trulyPlayable_iff_emptyFilter_principal.mpr
    (Filter.eq_principal_of_finite_sets (f := hE.emptyFilter) hfin)

/-- **A finite outcome type suffices.** This is print's **Proposition 6** -- *on
finite domains playability and true playability coincide* -- and it is also
`cl-lean`'s hypothesis.

**This is print's proof, not a substitute for it.** Print writes one line:
*"Straightforward, by Proposition 5.3 and the fact that every filter on a finite
set is principal."* `Playable.trulyPlayable_iff_emptyFilter_principal` is
Proposition 5(3), `Playable.emptyFilter` is the filter Proposition 1(1) says is
there, and the second half is Mathlib's -- eq_principal_of_finite in its filter
library. Nothing about minimal elements is used here. -/
public theorem Playable.trulyPlayable_of_finite [Finite X] (hE : Playable E) :
    TrulyPlayable E :=
  hE.trulyPlayable_iff_emptyFilter_principal.mpr
    (Filter.eq_principal_of_finite hE.emptyFilter)

/-! ## Proposition 2: a game form is truly playable

Print computes the core of `E_G(∅)` outright: it is the singleton whose element is
the set of reachable outcomes. `Playability` already has both halves. -/

variable {G : GameForm.{u, v, w} N X}

/-- **Proposition 2 (1)**: the nonmonotonic core of a game form's effectivity
function at the empty coalition is the singleton `{Z}`, `Z` the set of outcomes
some strategy profile actually produces. -/
public theorem nonmonotonicCore_effectivity_empty :
    nonmonotonicCore (effectivity G) (∅ : Set N) = {Set.range G.outcome} := by
  ext A
  simp only [Set.mem_singleton_iff]
  constructor
  · rintro ⟨hAmem, hAmin⟩
    rcases Set.eq_or_ssubset_of_subset
      (range_outcome_subset_of_mem_effectivity_empty hAmem) with heq | hlt
    · exact heq.symm
    · exact absurd ⟨Set.range G.outcome, range_outcome_mem_effectivity_empty, hlt⟩ hAmin
  · rintro rfl
    refine ⟨range_outcome_mem_effectivity_empty, ?_⟩
    rintro ⟨B, hBmem, hBlt⟩
    exact absurd (hBlt.subset.antisymm
      (range_outcome_subset_of_mem_effectivity_empty hBmem)) hBlt.ne

/-- **Proposition 2 (2)**: a game form's effectivity function is truly playable. -/
public theorem trulyPlayable_effectivity [∀ i, Nonempty (G.strategy i)] :
    TrulyPlayable (effectivity G) :=
  (playable_effectivity (G := G)).trulyPlayable_iff_principal.mpr
    ⟨Set.range G.outcome, range_outcome_mem_effectivity_empty,
      fun _ hB => range_outcome_subset_of_mem_effectivity_empty hB⟩

/-! ## The separating fact, in print's own terms -/

/-- **The cofinite filter's core at the empty coalition is empty** -- print's
*"there are no minimal cofinite sets"*. Deleting one point of a cofinite set
leaves a cofinite set, and a cofinite subset of `ℕ` is infinite, so there is always
a point to delete. -/
public theorem nonmonotonicCore_cofiniteEff_empty :
    nonmonotonicCore cofiniteEff (∅ : Set Unit) = ∅ := by
  ext A
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨hAmem, hAmin⟩
  have hcof : Aᶜ.Finite := mem_cofiniteEff_empty.mp hAmem
  have hinf : A.Infinite := Set.infinite_of_finite_compl hcof
  obtain ⟨a, ha⟩ := hinf.nonempty
  refine hAmin ⟨A \ {a}, mem_cofiniteEff_empty.mpr ?_, ?_⟩
  · have : (A \ {a})ᶜ = Aᶜ ∪ {a} := by
      simp [Set.compl_sdiff, Set.union_comm]
    rw [this]
    exact hcof.union (Set.finite_singleton a)
  · exact Set.sdiff_singleton_ssubset.mpr ha

/-- **The refutation again, by print's route.** `PlayableConverse` proves
`not_exists_gameForm_cofiniteEff` from the least element directly. Goranko, Jamroga
and Turrini argue it through the core: every game form's effectivity function has a
non-empty core at `∅` by their Proposition 2, and the cofinite filter's is empty. -/
public theorem not_trulyPlayable_cofiniteEff : ¬ TrulyPlayable cofiniteEff := by
  intro h
  have := cofiniteEff_playable.trulyPlayable_iff_nonmonotonicCore_empty_nonempty.mp h
  rw [nonmonotonicCore_cofiniteEff_empty] at this
  exact this.ne_empty rfl

end AISafetyAtlas.Sovereignty
