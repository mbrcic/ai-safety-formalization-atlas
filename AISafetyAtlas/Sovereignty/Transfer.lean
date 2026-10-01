module

public import AISafetyAtlas.Sovereignty.Quantifiers

/-!
# Resources, projections, and carrying a guarantee to an implementation

Three ways a guarantee moves, and the hypotheses each one needs.

## Resources

`ForcesWithin` is forcing with an explicit availability family: each agent may
use only the strategies in `T i`, and the coalition's witness must itself be
available. `forces_iff_forcesWithin_univ` says the unrestricted case is the
old notion.

`ForcesWithin.mono_resources` is the proposal's `P4` in one statement, both
halves at once: **more strategies for the coalition and fewer for everyone else
cannot reduce what the coalition can force.** The two directions are not
symmetric in the proof and are symmetric in the statement, because the witness
is existential and the obligation universal.

This is deliberately not a redesign of the game. Print is explicit that `P4`
says nothing about a change that also moves the dynamics, the costs, or which
actions are mandatory; here that shows up as `G` being the same game form on
both sides, with only availability moving.

## Projections

`GameForm.map` reads the outcome through `f`, and
`forces_map_iff_forces_preimage` is the proposal's `P10`: power over `B` in the
projected game is power over `f ⁻¹' B` in the original, in both directions.
Nothing is recovered that `f` erased -- the statement is an equivalence about
one target at a time, not about the two effectivity families.

## Refinement

`Simulates` is the proposal's `P11` hypothesis, and it is the direction of
refinement that preserves power: every abstract commitment by the coalition has
a concrete commitment whose projected outcomes, against **every** concrete
completion, already lie in the abstract commitment's footprint.
`forces_of_simulates` is the transfer, and `A2` -- semantic portability
preserves power under strategy simulation -- is that theorem with the migration
read as `f`.

The quantifier order is the whole content. Ordinary trace inclusion, which asks
only that the concrete outcomes be among the abstract ones, can remove every
alternative the coalition had; what is asked here is per-commitment, which is
why it is an alternating rather than a linear refinement.

### Where that notion comes from

`Simulates` is not this repository's invention and the proposal does not claim
it is. It is the **conclusion of Lemma 1 of Alur, Henzinger, Kupferman and
Vardi, *Alternating Refinement Relations*** — the lemma's *hypothesis* is that
a relation `H` is an `A`-simulation, which is their §3 definition one level
down, over moves, and which nothing here states (pinned at
`alur-henzinger-kupferman-vardi-1998-alternating-refinement-relations.pdf`,
sha256 `7fa1d527fdbb18be6c2e24d14ba73d62ba7cfed2c4390210bcb6a8d5139b15a0`, read
at its pages 167–170). Given an `A`-simulation `H` from `S` to `S'`, Lemma 1
concludes:
for every set `F_A` of strategies in `S` for the agents in `A` there is a set
`F'_A` of strategies in `S'` such that every computation the agents in `A` can
enforce with `F'_A` in `S'` is related by `H` to one they can enforce with
`F_A` in `S`.
That conclusion is what `Simulates` states, at one step and with `H` taken to
be the graph of `f`. Their §3 definition of `A`-simulation — the lemma's
hypothesis — has the same alternation over moves rather than strategies: for
every `T ∈ δ(q, A)` there is `T' ∈ δ'(q', A)` such that for every
`R' ∈ δ'(q', Ω∖A)` there is `R ∈ δ(q, Ω∖A)` with `(T ∩ R) × (T' ∩ R') ⊆ H`.
Nothing here carries that definition: with one step there is no relation to
close under a transition, so the hypothesis and the conclusion coincide.

The correspondence is exact and the differences are worth naming. `sC₀` is
their `F_A`, `sC₁` is `F'_A`, the concrete completion is their `R'`, and the
abstract completion witnessing membership in `outcomesOf` is their `R`. What
they carry and this does not: alternating transition systems with computations,
so the relation is closed under a step and the whole development is temporal;
propositions labelling states, with `π(q) = π'(q')` as the first clause. What
this carries and they do not: two different outcome types joined by `f`, where
they keep one proposition set and force equal labels.

`simulates_univ_iff` and `simulates_empty_iff` are the two extremes their
Proposition 2 singles out as the degenerate ones — at the full coalition and at
the empty coalition the alternation collapses and what is left is containment
between the outcome ranges, in one direction each. Their Proposition 2 also
records that the notion is **not** monotone in the coalition, and
`AISafetyAtlas.Examples.Sovereignty.Transfer` carries that at game forms.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w v' w'

variable {N : Type u} {X : Type v} {Y : Type v'}

/-! ## Forcing with a resource constraint -/

/--
**Forcing when only some strategies are available.** `T i` is the set of
strategies agent `i` may actually use. The coalition's commitment must lie in
it, and only available completions count against the guarantee.
-/
@[expose] public def ForcesWithin (G : GameForm.{u, v, w} N X) (C : Set N)
    (T : ∀ i, Set (G.strategy i)) (A : Set X) : Prop :=
  ∃ sC : ∀ i : C, G.strategy i, (∀ i : C, sC i ∈ T i) ∧
    ∀ s : ∀ i, G.strategy i, (∀ i : C, s i = sC i) → (∀ i, s i ∈ T i) →
      G.outcome s ∈ A

/-- With everything available, this is ordinary forcing. -/
public theorem forces_iff_forcesWithin_univ {G : GameForm.{u, v, w} N X}
    {C : Set N} {A : Set X} :
    Forces G C A ↔ ForcesWithin G C (fun _ => Set.univ) A := by
  constructor
  · rintro ⟨sC, hsC⟩
    exact ⟨sC, fun _ => trivial, fun s hs _ => hsC s hs⟩
  · rintro ⟨sC, _, hsC⟩
    exact ⟨sC, fun s hs => hsC s hs fun _ => trivial⟩

/--
**`P4`: more of your own strategies, fewer of theirs, cannot hurt.**

The coalition's availability may grow and everyone else's may shrink, and every
guarantee survives. The witness is reused unchanged: it is still available
because `C`'s sets grew, and the obligation is easier because the completions
it must survive have thinned.

Print's caveat is preserved by the shape of the statement rather than by a
side condition. `G` is one game form throughout, so a change that also moved
the dynamics, the costs, or which actions are mandatory is not an instance of
this.
-/
public theorem ForcesWithin.mono_resources {G : GameForm.{u, v, w} N X}
    {C : Set N} {T T' : ∀ i, Set (G.strategy i)} {A : Set X}
    (hown : ∀ i ∈ C, T i ⊆ T' i) (hopp : ∀ i ∉ C, T' i ⊆ T i)
    (h : ForcesWithin G C T A) : ForcesWithin G C T' A := by
  obtain ⟨sC, hmem, hforce⟩ := h
  refine ⟨sC, fun i => hown i i.2 (hmem i), fun s hs hT' => hforce s hs ?_⟩
  intro i
  by_cases hi : i ∈ C
  · exact (hs ⟨i, hi⟩) ▸ hmem ⟨i, hi⟩
  · exact hopp i hi (hT' i)

/-- Shrinking the opponents alone is the half that reads as a weaker threat
class: fewer admissible environments, no lost guarantee. This is the
qualitative form of the proposal's `A1`. -/
public theorem ForcesWithin.mono_threat {G : GameForm.{u, v, w} N X}
    {C : Set N} {T T' : ∀ i, Set (G.strategy i)} {A : Set X}
    (hC : ∀ i ∈ C, T i = T' i) (hopp : ∀ i ∉ C, T' i ⊆ T i)
    (h : ForcesWithin G C T A) : ForcesWithin G C T' A :=
  h.mono_resources (fun i hi => (hC i hi).subset) hopp

/-! ## Reading the outcome through a projection -/

/-- **The projected game form.** The same strategies, the outcome read through
`f`. -/
@[expose] public def GameForm.map (G : GameForm.{u, v, w} N X) (f : X → Y) :
    GameForm.{u, v', w} N Y where
  strategy := G.strategy
  outcome s := f (G.outcome s)

/--
**`P10`: projection is preimage.** A coalition has power over `B` in the
projected game exactly when it has power over `f ⁻¹' B` in the original.

Both directions hold and neither recovers anything `f` erased: the statement is
about one target at a time, and two originals that `f` identifies have the same
projected targets by construction.
-/
public theorem forces_map_iff_forces_preimage {G : GameForm.{u, v, w} N X}
    {f : X → Y} {C : Set N} {B : Set Y} :
    Forces (G.map f) C B ↔ Forces G C (f ⁻¹' B) :=
  Iff.rfl

/-- The effectivity families correspond target by target. -/
public theorem mem_effectivity_map_iff {G : GameForm.{u, v, w} N X}
    {f : X → Y} {C : Set N} {B : Set Y} :
    B ∈ effectivity (G.map f) C ↔ f ⁻¹' B ∈ effectivity G C :=
  Iff.rfl

/-! ## Refinement that preserves power -/

/--
**`P11`'s hypothesis: a strategy-preserving refinement.**

Every abstract commitment by `C` has a concrete commitment such that, against
**every** concrete completion, the projected outcome already lies in the
abstract commitment's footprint.

The existential is inside the universal over abstract commitments and outside
the universal over concrete completions. That order is what distinguishes this
from ordinary trace inclusion, which compares outcome sets and can silently
delete the coalition's alternatives.
-/
@[expose] public def Simulates (G₀ : GameForm.{u, v, w} N X)
    (G₁ : GameForm.{u, v', w'} N Y) (C : Set N) (f : Y → X) : Prop :=
  ∀ sC₀ : ∀ i : C, G₀.strategy i, ∃ sC₁ : ∀ i : C, G₁.strategy i,
    ∀ s₁ : ∀ i, G₁.strategy i, (∀ i : C, s₁ i = sC₁ i) →
      f (G₁.outcome s₁) ∈ outcomesOf G₀ C sC₀

/--
**At the full coalition the alternation collapses**, and what is left is that
every abstract outcome is realized by some concrete one. This is one of the two
degenerate cases Alur, Henzinger, Kupferman and Vardi's Proposition 2 names.
-/
public theorem simulates_univ_iff {G₀ : GameForm.{u, v, w} N X}
    {G₁ : GameForm.{u, v', w'} N Y} {f : Y → X} :
    Simulates G₀ G₁ Set.univ f ↔
      Set.range G₀.outcome ⊆ Set.range (f ∘ G₁.outcome) := by
  constructor
  · rintro h _ ⟨s₀, rfl⟩
    obtain ⟨sC₁, hsC₁⟩ := h fun i => s₀ i
    obtain ⟨s₀', hs₀', hout⟩ :=
      hsC₁ (fun i => sC₁ ⟨i, Set.mem_univ i⟩) fun _ => rfl
    refine ⟨fun i => sC₁ ⟨i, Set.mem_univ i⟩, ?_⟩
    have : s₀' = s₀ := funext fun i => hs₀' ⟨i, Set.mem_univ i⟩
    rw [Function.comp_apply, ← hout, this]
  · intro h sC₀
    obtain ⟨s₁, hs₁⟩ := h ⟨fun i => sC₀ ⟨i, Set.mem_univ i⟩, rfl⟩
    refine ⟨fun i => s₁ i, fun s₁' hagree => ?_⟩
    have hs : s₁' = s₁ := funext fun i => hagree ⟨i, Set.mem_univ i⟩
    exact ⟨fun i => sC₀ ⟨i, Set.mem_univ i⟩, fun _ => rfl, by rw [hs]; exact hs₁.symm⟩

/--
**At the empty coalition it collapses the other way**: every concrete outcome
must already be an abstract one. This is ordinary containment of outcome sets,
and it is the reading that can delete every alternative the coalition had.
-/
public theorem simulates_empty_iff {G₀ : GameForm.{u, v, w} N X}
    {G₁ : GameForm.{u, v', w'} N Y} {f : Y → X} :
    Simulates G₀ G₁ (∅ : Set N) f ↔
      Set.range (f ∘ G₁.outcome) ⊆ Set.range G₀.outcome := by
  constructor
  · rintro h _ ⟨s₁, rfl⟩
    obtain ⟨sC₁, hsC₁⟩ := h (fun i => i.2.elim)
    obtain ⟨s₀, -, hout⟩ := hsC₁ s₁ fun i => i.2.elim
    exact ⟨s₀, hout⟩
  · intro h _
    refine ⟨fun i => i.2.elim, fun s₁ _ => ?_⟩
    obtain ⟨s₀, hs₀⟩ := h ⟨s₁, rfl⟩
    exact ⟨s₀, fun i => i.2.elim, hs₀⟩

/-- **`P11`: every abstract guarantee transfers to the implementation.** -/
public theorem forces_of_simulates {G₀ : GameForm.{u, v, w} N X}
    {G₁ : GameForm.{u, v', w'} N Y} {C : Set N} {f : Y → X} {A : Set X}
    (hsim : Simulates G₀ G₁ C f) (hA : Forces G₀ C A) :
    Forces G₁ C (f ⁻¹' A) := by
  obtain ⟨sC₀, hsub⟩ := forces_iff_outcomesOf_subset.mp hA
  obtain ⟨sC₁, hsC₁⟩ := hsim sC₀
  exact ⟨sC₁, fun s hs => hsub (hsC₁ s hs)⟩

/-- **`A2`: semantic portability.** A migration that simulates the original
carries the whole protected catalogue, one demand at a time. -/
public theorem demandwise_of_simulates {G₀ : GameForm.{u, v, w} N X}
    {G₁ : GameForm.{u, v', w'} N Y} {C : Set N} {f : Y → X} {𝒬 : Set (Set X)}
    (hsim : Simulates G₀ G₁ C f) (h : Demandwise G₀ C 𝒬) :
    Demandwise G₁ C ((fun Φ => f ⁻¹' Φ) '' 𝒬) := by
  rintro _ ⟨Φ, hΦ, rfl⟩
  exact forces_of_simulates hsim (h Φ hΦ)

/-- Simulation composes, so a chain of migrations carries a guarantee as far as
the chain goes. -/
public theorem Simulates.comp {Z : Type*} {G₀ : GameForm.{u, v, w} N X}
    {G₁ : GameForm.{u, v', w'} N Y} {G₂ : GameForm.{u, _, _} N Z} {C : Set N}
    {f : Y → X} {g : Z → Y} (h₀ : Simulates G₀ G₁ C f)
    (h₁ : Simulates G₁ G₂ C g) : Simulates G₀ G₂ C (f ∘ g) := by
  intro sC₀
  obtain ⟨sC₁, hsC₁⟩ := h₀ sC₀
  obtain ⟨sC₂, hsC₂⟩ := h₁ sC₁
  refine ⟨sC₂, fun s₂ hs₂ => ?_⟩
  obtain ⟨s₁, hs₁, heq⟩ := hsC₂ s₂ hs₂
  have hmem := hsC₁ s₁ hs₁
  rw [heq] at hmem
  exact hmem

/-- Every game form simulates itself, which is the identity migration. -/
public theorem simulates_refl (G : GameForm.{u, v, w} N X) (C : Set N) :
    Simulates G G C id :=
  fun sC₀ => ⟨sC₀, fun s hs => ⟨s, hs, rfl⟩⟩

end AISafetyAtlas.Sovereignty
