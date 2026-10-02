module

public import AISafetyAtlas.Sovereignty.Playability

/-!
# Playability on two games, at both ends of the range

The playability conditions are stated over an arbitrary game form, so the
interesting question is what the *principal element* is -- the least set the
empty coalition forces, which `Playability` identifies as `Set.range outcome`.
That set measures how much is settled before anyone plays.

`pinnedForm` settles everything: nobody moves the outcome, so the range is a
single point and the empty coalition already forces it. `vetoGame` settles
nothing: both outcomes are reachable, so the empty coalition forces only the
whole space. The conditions hold in both cases, which is the point -- playability
is not a strength claim about any coalition.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-! ## Nothing is settled: the veto game -/

/-- Both outcomes of `vetoGame` are reachable, so the empty coalition's principal
element is everything. -/
public theorem vetoGame_range : Set.range vetoGame.outcome = (Set.univ : Set Bool) := by
  ext b
  refine ⟨fun _ => trivial, fun _ => ?_⟩
  cases b
  · exact ⟨fun _ => false, rfl⟩
  · exact ⟨fun _ => true, rfl⟩

/-- So the empty coalition forces only the whole space: nothing is unavoidable. -/
public theorem vetoGame_forces_empty_iff (A : Set Bool) :
    Forces vetoGame (∅ : Set Bool) A ↔ A = Set.univ := by
  rw [forces_empty_iff_range_subset, vetoGame_range]
  exact ⟨fun h => Set.univ_subset_iff.mp h, fun h => h ▸ subset_rfl⟩

/-- The veto game is onto, which is Peleg's standing assumption on `g`. -/
public theorem vetoGame_surjective : Function.Surjective vetoGame.outcome :=
  Set.range_eq_univ.mp vetoGame_range

/-- And so its empty-coalition family is the singleton print stipulates. -/
public theorem vetoGame_effectivity_empty :
    effectivity vetoGame (∅ : Set Bool) = {Set.univ} :=
  effectivity_empty_eq_singleton_univ vetoGame_surjective

/-- **Fact 1 on this game.** Extending `{false}`'s `true` to everybody shrinks
the possible outcomes from both bits to `{true}`. Print's inclusion, and it is
proper. -/
public theorem vetoGame_fact1 :
    outcomesOf vetoGame (Set.univ : Set Bool) (fun _ => true) ⊂
      outcomesOf vetoGame ({false} : Set Bool) (fun _ => true) :=
  vetoGame_outcomesOf_strict

/-! ## Everything is settled: the pinned form -/

/-- In `pinnedForm` the outcome never varies, so the principal element is the
single point. -/
public theorem pinnedForm_range (x₀ : Bool) :
    Set.range (pinnedForm x₀).outcome = ({x₀} : Set Bool) := by
  ext b
  exact ⟨by rintro ⟨_, rfl⟩; rfl, by rintro rfl; exact ⟨fun _ => PUnit.unit, rfl⟩⟩

/-- The empty coalition already forces the outcome: it is unavoidable, and no
coalition adds anything. -/
public theorem pinnedForm_forces_empty (x₀ : Bool) :
    Forces (pinnedForm x₀) (∅ : Set Bool) {x₀} :=
  forces_empty_iff_range_subset.mpr (by rw [pinnedForm_range])

/-! ## N-maximality is doing work

At the pinned form, `{x₀}ᶜ` is not forced by the empty coalition, and
N-maximality says the grand coalition therefore forces `{x₀}`. Here that is true
for the stronger reason that everyone already had it -- but the implication is
the one the condition asserts.
-/

public theorem pinnedForm_nMax (x₀ : Bool) :
    ¬ Forces (pinnedForm x₀) (∅ : Set Bool) ({x₀}ᶜ) ∧
      Forces (pinnedForm x₀) (Set.univ : Set Bool) {x₀} := by
  constructor
  · rw [forces_empty_iff_range_subset, pinnedForm_range]
    intro h
    exact absurd (h rfl) (by simp)
  · exact forces_univ_of_not_forces_empty_compl (by
      rw [forces_empty_iff_range_subset, pinnedForm_range]
      intro h
      exact absurd (h rfl) (by simp))

/-! ## Individualism, satisfied and refuted

Theorem 3.3 is an equivalence, so it says nothing until a game form sits on each
side of it. `principalDecides` does -- the principal names the outcome, so it is
the dictator and every coalition's power is already the principal's. `vetoGame`
does not: `outcome s = s false && s true` needs both players to agree, so neither
forces `{true}` alone while together they do. That is the whole content of the
theorem, on the smallest pair that shows it.
-/

/-- The principal forces every outcome, so it is a dictator in Pauly's sense. -/
public theorem principalDecides_isDictator (X : Type) :
    IsDictator (principalDecides X) false := by
  rintro x -
  exact ⟨fun _ => x, fun s hs => hs ⟨false, rfl⟩⟩

/-- **A dictatorship is individualistic**, by Theorem 3.3. -/
public theorem principalDecides_individualistic (X : Type) [Nonempty X] :
    Individualistic (principalDecides X) := by
  have : ∀ i, Nonempty ((principalDecides X).strategy i) := fun _ => ‹Nonempty X›
  exact individualistic_iff_exists_dictator.mpr ⟨false, principalDecides_isDictator X⟩

/-- In the veto game the grand coalition forces `{true}` -- both players play
`true`. -/
public theorem vetoGame_univ_forces :
    Forces vetoGame (Set.univ : Set Bool) ({true} : Set Bool) :=
  forces_univ_iff.mpr ⟨fun _ => true, rfl⟩

/--
**The veto game is not individualistic.** The grand coalition forces `{true}`
and no individual does, so `E(N)` is strictly larger than `⋃ E({i})` and
Theorem 3.3 gives no dictator.

`vetoGame_not_forces` supplies the half about player `true`; the other player is
symmetric and is proved here.
-/
public theorem vetoGame_not_individualistic : ¬ Individualistic vetoGame := by
  intro hind
  have h2 : ({true} : Set Bool) ∈ ⋃ i : Bool, effectivity vetoGame ({i} : Set Bool) :=
    hind ▸ vetoGame_univ_forces
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp h2
  cases i
  · obtain ⟨sD, hsD⟩ := hi
    have h := hsD (fun b => cond b false (sD ⟨false, rfl⟩)) (by
      rintro ⟨b, hb⟩
      simp only [Set.mem_singleton_iff] at hb
      subst hb
      rfl)
    simp only [vetoGame, Set.mem_singleton_iff, Bool.and_eq_true] at h
    exact Bool.noConfusion (show (false : Bool) = true from h.2)
  · exact vetoGame_not_forces hi

/-! ## The block interface, inhabited

`BlockChoice` and Pauly's Claim over it say nothing until a partition with a
choice per block exists and its blocks really do force what they name. The
discrete partition on `principalDecides` supplies one with two genuine blocks:
the principal's block commits to `{true}` and forces it, the other block commits
to everything and forces that, and the intersection is `{true}`.
-/

/-- Each player is its own block. -/
@[expose] public def discreteBlocks : BlockChoice Bool Bool where
  rel := { r := fun i j => i = j, iseqv := ⟨fun _ => rfl, Eq.symm, Eq.trans⟩ }
  choice := fun i => if i then (Set.univ : Set Bool) else ({true} : Set Bool)
  choice_const := fun _ _ h => by rw [show _ = _ from h]

/-- Under the discrete partition a block is the singleton of any of its members. -/
public theorem discreteBlocks_blockOf (i : Bool) :
    discreteBlocks.blockOf (@Quotient.mk _ discreteBlocks.rel i) = ({i} : Set Bool) := by
  ext j
  simp only [BlockChoice.mem_blockOf, Set.mem_singleton_iff]
  exact ⟨fun h => Quotient.exact h, fun h => by rw [h]⟩

/-- **Every block forces what it committed to**, which is the hypothesis Pauly's
Claim runs on. -/
public theorem discreteBlocks_forces (b : Quotient discreteBlocks.rel) :
    Forces (principalDecides Bool) (discreteBlocks.blockOf b) (discreteBlocks.blockChoice b) := by
  induction b using Quotient.ind with
  | _ i =>
    rw [discreteBlocks_blockOf, discreteBlocks.blockChoice_mk]
    cases i
    · exact ⟨fun _ => true, fun s hs => by
        simp only [discreteBlocks, if_neg (by decide : ¬ (false = true))]
        exact hs ⟨false, rfl⟩⟩
    · exact ⟨fun _ => true, fun _ _ => by
        simp only [discreteBlocks]
        trivial⟩

/-- **So the claim fires**: the whole player set forces the intersection of the
block commitments, and that intersection is non-empty. -/
public theorem discreteBlocks_claim :
    Forces (principalDecides Bool) (Set.univ : Set Bool)
      (⋂ b, discreteBlocks.blockChoice b) ∧
    (⋂ b, discreteBlocks.blockChoice b).Nonempty := by
  have hne : ∀ i, Nonempty ((principalDecides Bool).strategy i) := fun _ => ⟨true⟩
  exact ⟨forces_iInter_blockChoice _ discreteBlocks_forces,
    iInter_blockChoice_nonempty _ discreteBlocks_forces⟩

/-! ## The refinement really splits

`BlockChoice.ofChoiceFunctions` produces a partition for any choice functions on a
finite player set. That alone does not say it produces an *interesting* one: a
construction that always returned the single block `⟨N⟩` would satisfy the same
type, and Pauly's Claim applied to one block says nothing.

Two players who name different sets for the whole player set are separated at the
very first refinement step, and the fixed point is finer than every step, so they
are separated there too.
-/

/-- Two players, each naming its own outcome for whatever coalition it is asked
about. -/
@[expose] public def rivalChoices : Bool → Set Bool → Set Bool :=
  fun i _ => {i}

/-- **The first step already separates them.** At stage `0` every player shares
one block, so both are asked about the same coalition and name different sets. -/
public theorem rivalChoices_refineSeq_one :
    ¬ (refineSeq rivalChoices 1).r true false := by
  rintro ⟨-, heq⟩
  simp only [rivalChoices, Set.singleton_eq_singleton_iff] at heq
  exact Bool.noConfusion heq

/-- **So the partition the construction returns is not the trivial one.** -/
public theorem rivalChoices_not_related :
    ¬ (BlockChoice.ofChoiceFunctions rivalChoices).rel.r true false := fun h =>
  rivalChoices_refineSeq_one (BlockChoice.ofChoiceFunctions_le rivalChoices 1 h)


/-! ## The remaining playability statements, at these witnesses

`vetoGame` has a strategy for every player, which is what the effectivity
package needs; `discreteBlocks` and `rivalChoices` supply the two block-choice
statements.
-/

/-- Both players have a strategy in the veto game, which is what the effectivity
package requires of a game form. -/
public instance vetoGame_nonempty (i : Bool) : Nonempty (vetoGame.strategy i) :=
  ⟨false⟩

/-- **Pauly's playability conditions, all five at once**, at the veto game. -/
public theorem vetoGame_effectivity_playable :
    (∀ C : Set Bool, (∅ : Set Bool) ∉ effectivity vetoGame C) ∧
    (∀ C : Set Bool, (Set.univ : Set Bool) ∈ effectivity vetoGame C) ∧
    (∀ A : Set Bool, Aᶜ ∉ effectivity vetoGame (∅ : Set Bool) →
      A ∈ effectivity vetoGame (Set.univ : Set Bool)) ∧
    (∀ (C : Set Bool) (A B : Set Bool), A ⊆ B →
      A ∈ effectivity vetoGame C → B ∈ effectivity vetoGame C) ∧
    (∀ (C D : Set Bool) (A B : Set Bool), Disjoint C D →
      A ∈ effectivity vetoGame C → B ∈ effectivity vetoGame D →
        A ∩ B ∈ effectivity vetoGame (C ∪ D)) :=
  effectivity_playable

/-- **Regularity, coalition monotonicity and a least element**, at the same
game -- the third component is `vetoGame_effectivity_empty` read as a principal
filter. -/
public theorem vetoGame_effectivity_regular_and_principal :
    (∀ (C : Set Bool) (A : Set Bool), A ∈ effectivity vetoGame C →
      Aᶜ ∉ effectivity vetoGame Cᶜ) ∧
    (∀ (C D : Set Bool), C ⊆ D → effectivity vetoGame C ⊆ effectivity vetoGame D) ∧
    (∃ A : Set Bool, A ∈ effectivity vetoGame (∅ : Set Bool) ∧
      ∀ B ∈ effectivity vetoGame (∅ : Set Bool), A ⊆ B) :=
  effectivity_regular_and_principal

/-- **An unsplit coalition's block commits to what its members named.** Under
the discrete partition every singleton is unsplit, so the hypothesis holds
rather than being assumed. -/
public theorem discreteBlocks_blockChoice_singleton (i : Bool) :
    discreteBlocks.blockChoice (@Quotient.mk _ discreteBlocks.rel i)
      = discreteBlocks.choice i :=
  BlockChoice.blockChoice_of_unsplit
    (C := ({i} : Set Bool))
    (by rw [discreteBlocks_blockOf])
    (Set.mem_singleton i)

/-- **Which refinement stage the construction returned is recoverable**, which
is how `rivalChoices_not_related` gets to reason about an object produced by
choice. -/
public theorem rivalChoices_ofChoiceFunctions_rel :
    (BlockChoice.ofChoiceFunctions rivalChoices).rel
      = refineSeq rivalChoices (exists_refineFixed rivalChoices).choose :=
  BlockChoice.ofChoiceFunctions_rel rivalChoices

end AISafetyAtlas.Examples.Sovereignty
