module

public import AISafetyAtlas.Sovereignty.Rights
public import AISafetyAtlas.Sovereignty.PlayableConverse

/-!
# Peleg's Theorem 3.5, the direction that builds a game form

Bezalel Peleg, *Effectivity functions, game forms, games, and rights*, Social
Choice and Welfare 15 (1998) 67-80, journal pages 72-73 of the pinned file.

> **Theorem 3.5.** Let `E : 2^N →→ 2^A` be the EF which is derived by (3.1).
> Then there exists a GF `Γ = ⟨N; Σ¹, …, Σⁿ; g; A⟩` such that
> `E_α(S; Γ) = E(S)` for all `S ∈ 2^N` iff the following two conditions hold:
> (i) `γ` is monotonic w.r.t. the alternatives; (ii) `E` is superadditive.

Print proves it in an appendix and adds *"For a proof when `A` is finite see
Moulin (1983)"*. `AISafetyAtlas.Sovereignty.Rights` carries the necessity of
(ii). This module carries the **sufficiency**, at arbitrary `A`.

## Why this is not the theorem the atlas already refuted

`AISafetyAtlas.Sovereignty.PlayableConverse` shows Pauly's corresponding
converse is **false**: `cofiniteEff` satisfies all five playability conditions
and `not_exists_gameForm_cofiniteEff` says no game form has it. So a
construction from playability alone cannot exist, and `paulyGame` is honest
about it -- `Playable.effectivity_paulyGame_eq` delivers the equality at every
coalition **except the two ends of the lattice**.

Peleg's page 72 definition of an effectivity function pins exactly those two
ends, and that is the whole content of this module:

> An *effectivity function* (EF) is a correspondence `E : 2^N →→ 2^A` that
> satisfies the following conditions: (i) `E(∅) = A`; (ii) `E(N) = 2^A \ {∅}`;
> (iii) `∅ ∉ E(S)` for all `S ⊂ N`; and (iv) `A ∈ E(S)` for all `S ⊂ N`.

`IsEffectivityFunction` is that list. Print calls (ii) *"the familiar condition
of citizen's sovereignty (or non-imposition)"*. With (i) and (ii) in hand the
empty coalition's family has a least element and the grand coalition's family is
everything non-empty, which is precisely what `cofiniteEff` violates: its empty
family is the cofinite filter, which has none. So the refutation and this
construction are the same fact read twice, and the load-bearing hypothesis is
named rather than smuggled.

## What is proved, and what print gets wrong

* `IsEffectivityFunction.playable` -- print's four conditions, superadditivity
  and (3.3) on the diagonal give Pauly's five.
* `Playable.surjective_paulyGame_outcome` -- the constructed game form's outcome
  function is onto, which is what closes the empty coalition. Print assumes
  surjectivity from Definition 3.3 onward; here it is derived for the game that
  gets built.
* `IsEffectivityFunction.effectivity_paulyGame` -- the equality at **every**
  coalition.
* `Constitution.exists_represents` -- Theorem 3.5's sufficiency, and
  `Constitution.exists_represents_iff_superadditive` is the biconditional with
  (i) standing, which is the strongest honest form.

**The form is weaker than print's `iff` in exactly one place, and that is print's
defect rather than this module's.** Print's condition (i) is a property of `γ` at
*every* set of rights, while a representation constrains only the diagonal
`γ(S, α(S))`; print's own page 70 says the off-diagonal values *"do not enter the
analysis of a society at a given date"*. `Examples…represented_not_monotoneAlternatives`
is a represented constitution that fails (3.3) off the diagonal, so the necessity
of (i) **as printed** is refuted, not merely unproved. The audit's section 21
records it.

## Non-vacuity

`AISafetyAtlas.Examples.Sovereignty.Representation` inhabits every hypothesis at
once on a two-player, two-state society whose rights are held by one member.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w r

/-! ## Print's page-72 definition -/

/--
**Peleg's effectivity function**, journal page 72, all four conditions.

Carried as a predicate on an arbitrary family rather than as a structure on a
constitution, because Theorem 3.5's hypothesis is *"let `E` be the EF which is
derived by (3.1)"* -- the four conditions are standing, and the constitution
enters only through `Constitution.induced`.

`univ` is print's *"citizen's sovereignty (or non-imposition)"*. It is stipulated
by print and it is load-bearing: `not_exists_gameForm_cofiniteEff` is what
happens without it.
-/
public structure IsEffectivityFunction {N : Type u} {X : Type v}
    (E : Set N → Set (Set X)) : Prop where
  /-- (i) `E(∅) = A`. -/
  empty : E (∅ : Set N) = ({Set.univ} : Set (Set X))
  /-- (ii) `E(N) = 2^A ∖ {∅}`. -/
  univ : E (Set.univ : Set N) = {A : Set X | A.Nonempty}
  /-- (iii) `∅ ∉ E(S)`. -/
  live : ∀ C : Set N, (∅ : Set X) ∉ E C
  /-- (iv) `A ∈ E(S)`. -/
  safe : ∀ C : Set N, (Set.univ : Set X) ∈ E C

namespace IsEffectivityFunction

variable {N : Type u} {X : Type v} {E : Set N → Set (Set X)}

/-- **The social states are not empty.** Condition (iv) puts the whole space in
every family and condition (iii) keeps the empty set out, so they differ. -/
public theorem nonempty_outcomes (h : IsEffectivityFunction E) :
    (Set.univ : Set X).Nonempty := by
  rcases Set.eq_empty_or_nonempty (Set.univ : Set X) with hEq | hne
  · exact absurd (hEq ▸ h.safe (∅ : Set N)) (h.live _)
  · exact hne

/--
**Print's four conditions, plus his Theorem 3.5's two, are Pauly's five.**

The only condition that takes an argument is `N`-maximality, and it comes from
(i) and (ii) together: the complement of `A` fails to be in `E(∅) = {A}` exactly
when `A` is non-empty, which by (ii) is exactly when `A ∈ E(N)`.
-/
public theorem playable (h : IsEffectivityFunction E)
    (hs : Superadditive E) (hu : UpwardClosed E) : Playable E where
  live := h.live
  safe := h.safe
  maximal := by
    intro A hA
    rw [h.univ]
    rw [h.empty, Set.mem_singleton_iff] at hA
    refine Set.nonempty_iff_ne_empty.mpr fun hEq => hA ?_
    rw [hEq, Set.compl_empty]
  mono := fun C A B hAB hA => hu C A B hA hAB
  superadd := fun C D A B hCD hA hB => hs C D A B hCD hA hB

end IsEffectivityFunction

/-! ## The constructed game form is onto -/

variable {N : Type u} {X : Type v} {E : Set N → Set (Set X)}

/--
**Every social state is reached.** Give every member the choice function that
names the whole space everywhere and the picker that returns `x` there. Then
`G(f)` is the whole space whatever the partition turns out to be, and whoever
the dictator is holds that picker.

Print assumes `g` onto from Definition 3.3 onward. For the game form Theorem 3.5
actually builds it is a theorem, and it is what makes the empty coalition's
family come out as print's `{A}` rather than as the supersets of a smaller
reachable set.
-/
public theorem Playable.surjective_paulyGame_outcome [Fintype N] [Nonempty N]
    (hE : Playable E) : Function.Surjective (paulyGame hE).outcome := by
  classical
  intro x
  refine ⟨fun i => (choiceFnUniv hE i, Classical.arbitrary N,
    pickerAt (Set.univ : Set X) x (Set.mem_univ x)), ?_⟩
  set σ : ∀ i, Strat E i := fun i => (choiceFnUniv hE i, Classical.arbitrary N,
    pickerAt (Set.univ : Set X) x (Set.mem_univ x)) with hσ
  have hfull : ∀ (i : N) (C : Set N), fullChoice σ i C = (Set.univ : Set X) := by
    intro i C
    by_cases h : i ∈ C
    · rw [fullChoice_of_mem σ h]; rfl
    · simp only [fullChoice]; rw [dif_neg h]
  have hblock : ∀ b, (partitionOf σ).blockChoice b = (Set.univ : Set X) := by
    intro b
    induction b using Quotient.inductionOn with
    | _ i =>
        rw [BlockChoice.blockChoice_mk]
        show fullChoice σ i _ = Set.univ
        exact hfull i _
  have hset : outcomeSet σ = (Set.univ : Set X) := by
    unfold outcomeSet
    simp [hblock]
  rw [paulyGame_outcome hE σ,
    show (⟨outcomeSet σ, hE.outcomeSet_nonempty σ⟩ : {A : Set X // A.Nonempty})
      = ⟨Set.univ, ⟨x, Set.mem_univ x⟩⟩ from Subtype.ext hset]
  exact pickerAt_self (Set.mem_univ x) _

/-! ## Theorem 3.5, sufficiency -/

/--
**The construction represents the effectivity function at every coalition.**

`Playable.effectivity_paulyGame_eq` is the middle of the lattice, and it is all
that playability can give. The two ends are print's conditions (i) and (ii),
read off the constructed game through its own surjectivity.
-/
public theorem IsEffectivityFunction.effectivity_paulyGame [Fintype N] [Nonempty N]
    (h : IsEffectivityFunction E) (hs : Superadditive E) (hu : UpwardClosed E) :
    effectivity (paulyGame (h.playable hs hu)) = E := by
  classical
  have hsurj := (h.playable hs hu).surjective_paulyGame_outcome
  funext C
  by_cases hemp : C = (∅ : Set N)
  · subst hemp
    rw [effectivity_empty_eq_singleton_univ hsurj, h.empty]
  by_cases huniv : C = (Set.univ : Set N)
  · subst huniv
    rw [effectivity_univ_eq_nonempty hsurj, h.univ]
  exact (h.playable hs hu).effectivity_paulyGame_eq
    (Set.nonempty_iff_ne_empty.mpr hemp) huniv

/-- **Existence, on a bare effectivity function.** -/
public theorem exists_gameForm_of_isEffectivityFunction [Fintype N] [Nonempty N]
    (h : IsEffectivityFunction E) (hs : Superadditive E) (hu : UpwardClosed E) :
    ∃ G : GameForm.{u, v, max u v} N X, effectivity G = E :=
  ⟨paulyGame (h.playable hs hu), h.effectivity_paulyGame hs hu⟩

namespace Constitution

variable {R : Type r} {κ : Constitution N X R}

/-- **(3.3) on the diagonal.** Print's condition (i) is stated at every set of
rights; the induced effectivity function only ever sees `γ(S, α(S))`. -/
public theorem upwardClosed_induced (h : κ.MonotoneAlternatives) :
    UpwardClosed κ.induced :=
  fun S B B' hB hBB' => h S (κ.assign S) B B' hB hBB'

/--
**Peleg's Theorem 3.5, sufficiency.** A constitution whose induced effectivity
function is one of print's EFs, whose access correspondence is monotonic with
respect to the alternatives, and whose induced effectivity function is
superadditive, is represented by a game form.

The game form is `paulyGame`, print's own construction read through
`AISafetyAtlas.Sovereignty.PlayableConverse`. `A` is arbitrary: print's appendix
proof is general and refers to Moulin (1983) only for the finite case.
-/
public theorem exists_represents [Fintype N] [Nonempty N]
    (hEF : IsEffectivityFunction κ.induced) (h₃ : κ.MonotoneAlternatives)
    (hs : Superadditive κ.induced) :
    ∃ G : GameForm.{u, v, max u v} N X, Represents G κ :=
  ⟨paulyGame (hEF.playable hs (upwardClosed_induced h₃)),
    fun C => congrFun (hEF.effectivity_paulyGame hs (upwardClosed_induced h₃)) C⟩

/--
**Theorem 3.5 as a biconditional, with condition (i) standing.**

This is the strongest form the printed statement supports. Print puts (i) on the
right of the `iff`, which makes it a *necessary* condition for representation;
that is false, and `Examples…represented_not_monotoneAlternatives` is the
witness. What is true is that under (i) the representation question is exactly
the superadditivity question, and both directions of that are here:
`Represents.superadditive` going out, `exists_represents` coming back.
-/
public theorem exists_represents_iff_superadditive [Fintype N] [Nonempty N]
    (hEF : IsEffectivityFunction κ.induced) (h₃ : κ.MonotoneAlternatives) :
    (∃ G : GameForm.{u, v, max u v} N X, Represents G κ) ↔ Superadditive κ.induced := by
  constructor
  · rintro ⟨G, hG⟩
    exact hG.superadditive
  · intro hs
    exact exists_represents hEF h₃ hs

end Constitution

end AISafetyAtlas.Sovereignty
