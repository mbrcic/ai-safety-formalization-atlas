module

public import AISafetyAtlas.Sovereignty.Separations
public import Mathlib.Data.Setoid.Partition
public import Mathlib.Data.Finite.Prod
public import Mathlib.Order.OrderIsoNat

/-!
# The effectivity function of a game form is playable

`Separations` defines `effectivity G C` as everything a coalition can force, and
proves laws about it one at a time. Coalition logic asks a sharper question:
*which* families of sets arise this way. Pauly's answer is a list of five closure
conditions, and a family satisfying them is **playable**.

This module proves `effectivity` satisfies that list.

## Pauly's definition, transcribed

Marc Pauly, *A Modal Logic for Coalitional Power in Games*, Journal of Logic and
Computation 12(1): 149-166, 2002, DOI `10.1093/logcom/12.1.149`, page 152, read
from the rendered page because the DVI-set mathematics does not extract:

> Call an effectivity function `E : P(N) → P(P(S))` *playable* iff (1) `∀C ⊆ N :
> ∅ ∉ E(C)`, (2) `∀C ⊆ N : S ∈ E(C)`, (3) `E` is `N`-maximal, (4) `E` is
> outcome-monotonic, and (5) `E` is superadditive.

with, on the same page, `E` *`C`-maximal* iff for all `X`, if `X̄ ∉ E(C̄)` then
`X ∈ E(C)` -- so `N`-maximality is that condition at `C = N`, where `C̄ = ∅` --
and `E` *`C`-regular* iff for all `X`, `X ∈ E(C)` implies `X̄ ∉ E(C̄)`.

The correspondence, each checked against that page:

| Pauly | here |
|---|---|
| (1) `∅ ∉ E(C)` | `not_forces_empty` |
| (2) `S ∈ E(C)` | `forces_univ`, in `Separations` |
| (3) `N`-maximality | `forces_univ_of_not_forces_empty_compl` |
| (4) outcome-monotonic | `Forces.mono`, in `Separations` |
| (5) superadditive | `forces_superadditive`, in `Separations` |
| regular | `not_forces_compl_of_forces` |
| coalition-monotonic | `Forces.mono_coalition`, in `Separations` |

So three of the five were already theorems here under other names, and
`not_forces_compl_of_forces` is `Forces.inter_nonempty_of_disjoint` -- proved to
discharge Gaerdenfors' consistency condition -- at `D = Cᶜ`, `B = Aᶜ`. Two
conditions are new: liveness and `N`-maximality.

**Regularity and coalition-monotonicity are not on Pauly's list.** His Lemma 3.1
*derives* both from playability. They are proved directly here instead, which is
a different route to the same statements and not a stronger result.

## What this is half of

Pauly's Theorem 3.2 is a characterisation: *an effectivity function is playable
iff it is the effectivity function of some strategic game.* `effectivity_playable`
below is the direction his proof dismisses in one sentence -- "one can easily
check that the effectivity function of any strategic game satisfies the five
properties mentioned". **The converse is the content, and it is false.**
`AISafetyAtlas.Sovereignty.PlayableConverse` carries the witness, which is Goranko,
Jamroga and Turrini's published counterexample and not this atlas's -- the cofinite
filter on the natural numbers is a playable effectivity function on one player
that no game form has -- and the four parts of the construction, which is built
there and proved to give `E_G = E` at every coalition except the two ends.

His construction on page 153 has four moving parts. All four are now built, parts
2 and 3 here and parts 1 and 4 in `PlayableConverse`:

1. **Strategies as triples.** A strategy for player `i` is `(f_i, t_i, h_i)`: a
   choice `f_i(C) ∈ E(C)` for every coalition `C` containing `i`, an index
   `t_i ∈ N`, and a choice function `h_i` picking an element of any non-empty set.
2. **An iterated partition refinement.** Given the profile of `f`s, refine
   `P_0 = ⟨N⟩` by splitting each block into players who agree on what that block
   should force, and iterate. Print's termination argument is *"since there are
   only finitely many players, this partitioning process will eventually stop"*.
   This is `refineSeq`, `exists_refineFixed` and
   `BlockChoice.ofChoiceFunctions`; the termination clause is
   `exists_stable_of_refining`, resting on `instFiniteSetoid`, which Mathlib does
   not carry.
3. **`G(f) = ⋂_l f(C_l)` is non-empty.** Each block forces its own set, so by
   superadditivity the union of the blocks forces the intersection, and liveness
   makes it non-empty. This is
   `AISafetyAtlas.Sovereignty.iInter_nonempty_of_pairwiseDisjoint`, proved over an
   arbitrary index type rather than only over the blocks of a finite partition.
4. **A dictator chosen by summing indices.** The outcome is `h_{i_0}(G(f))` where
   `i_0 = ((t_1 + ... + t_n) mod n) + 1`, so no proper subcoalition controls who
   picks. This is `dictator` and `exists_dictator_eq` in `PlayableConverse`, with
   the game itself as `paulyGame`.

`E_G = E` then holds at every coalition that is neither `∅` nor `N`, and **at
those two it fails** -- `Playable.effectivity_paulyGame_eq` carries both side
conditions. N-maximality is read exactly once in print's proof, in the `C = N`
step, and that step is the unsound one; no theorem in either module consumes it.

## One clause that is not Pauly's

`range_outcome_mem_effectivity_empty` says the empty coalition's family has a
least element, `Set.range G.outcome`. That is **not** part of playability; the
strings "truly playable" and "principal" appear nowhere in Pauly 2002. It was
taken from the truly-playable extension in the Lean development
`kaiobendrauf/cl-lean`, whose own source is unverified here, and it is stated
below as a separate result rather than folded into the playability bundle.

It is worth keeping because it is the formal shadow of a choice Pauly makes
explicitly on the same page: he does *not* assume the outcome function is
surjective, and does *not* require `X ∈ E(N)` for every non-empty `X`, since
"certain states may be unreachable no matter how the players play". The
unreachable outcomes are exactly what makes `Set.range G.outcome` a proper subset
and hence a non-trivial least element.

It is also, as it turns out, the missing condition. Playability makes `E(∅)` a
proper filter and says nothing about its having a least element; a filter on an
infinite set need not have one, and that is the whole of why Theorem 3.2's
converse fails. See `not_exists_gameForm_cofiniteEff` in `PlayableConverse`.
-/
namespace AISafetyAtlas.Sovereignty

universe u v w

variable {N : Type u} {X : Type v} {G : GameForm.{u, v, w} N X}

/-! ## The two degenerate coalitions

Both endpoints of the coalition lattice collapse to a quantifier over profiles,
and the playability conditions are easiest to read through these.
-/

/-- **The empty coalition forces exactly the sets every profile lands in.** It
commits to nothing, so it guarantees a target only when the target is unavoidable. -/
public theorem forces_empty_iff {A : Set X} :
    Forces G (∅ : Set N) A ↔ ∀ s : ∀ i, G.strategy i, G.outcome s ∈ A := by
  constructor
  · rintro ⟨_, h⟩ s; exact h s fun i => i.2.elim
  · exact fun h => ⟨fun i => i.2.elim, fun s _ => h s⟩

/-- **The grand coalition forces exactly the sets some profile lands in.** It
settles every strategy, so nothing is left to vary. -/
public theorem forces_univ_iff {A : Set X} :
    Forces G (Set.univ : Set N) A ↔ ∃ s : ∀ i, G.strategy i, G.outcome s ∈ A := by
  constructor
  · rintro ⟨sC, h⟩
    exact ⟨fun i => sC ⟨i, Set.mem_univ i⟩, h _ fun _ => rfl⟩
  · rintro ⟨s, hs⟩
    refine ⟨fun i => s i, fun s' hs' => ?_⟩
    have : s' = s := funext fun i => hs' ⟨i, Set.mem_univ i⟩
    exact this ▸ hs

/-- The empty coalition's effectivity family is the supersets of the reachable
outcomes. -/
public theorem forces_empty_iff_range_subset {A : Set X} :
    Forces G (∅ : Set N) A ↔ Set.range G.outcome ⊆ A := by
  rw [forces_empty_iff]
  exact ⟨fun h _ hx => by obtain ⟨s, rfl⟩ := hx; exact h s, fun h s => h ⟨s, rfl⟩⟩

/-! ## The playability conditions -/

/-- **Liveness.** No coalition forces the empty set: forcing is a guarantee about
an outcome that actually happens, and there is always an outcome. -/
public theorem not_forces_empty [∀ i, Nonempty (G.strategy i)] (C : Set N) :
    ¬ Forces G C (∅ : Set X) := by
  classical
  rintro ⟨sC, h⟩
  exact h (fun i => if hi : i ∈ C then sC ⟨i, hi⟩ else Classical.arbitrary _)
    fun i => by simp [i.2]

/-- **N-maximality.** If the empty coalition cannot force the complement of `A` --
that is, if landing outside `A` is not unavoidable -- then the grand coalition can
force `A`.

The content is that the two degenerate coalitions are dual: what nobody can
prevent, everybody together can achieve. -/
public theorem forces_univ_of_not_forces_empty_compl {A : Set X}
    (h : ¬ Forces G (∅ : Set N) Aᶜ) : Forces G (Set.univ : Set N) A := by
  classical
  rw [forces_empty_iff] at h
  obtain ⟨s, hs⟩ := not_forall.mp h
  exact forces_univ_iff.mpr ⟨s, not_not.mp hs⟩

/-- **Regularity.** A coalition and its complement cannot force complementary
targets. This is `Forces.inter_nonempty_of_disjoint` at `D = Cᶜ`, `B = Aᶜ`, and it
is the same law as Gaerdenfors' consistency condition. -/
public theorem not_forces_compl_of_forces [∀ i, Nonempty (G.strategy i)]
    {C : Set N} {A : Set X} (h : Forces G C A) : ¬ Forces G Cᶜ Aᶜ := by
  intro hc
  obtain ⟨x, hx, hxc⟩ := Forces.inter_nonempty_of_disjoint disjoint_compl_right h hc
  exact hxc hx

/-- **A principal element at the empty coalition.** The reachable outcomes are
themselves forced by nobody, and every set the empty coalition forces contains
them, so its effectivity family has a least element. This is what distinguishes a
*truly* playable structure from a merely playable one. -/
public theorem range_outcome_mem_effectivity_empty :
    Set.range G.outcome ∈ effectivity G (∅ : Set N) :=
  forces_empty_iff_range_subset.mpr subset_rfl

/-- The least element is least. -/
public theorem range_outcome_subset_of_mem_effectivity_empty {A : Set X}
    (h : A ∈ effectivity G (∅ : Set N)) : Set.range G.outcome ⊆ A :=
  forces_empty_iff_range_subset.mp h

/--
**Peleg's stipulated empty-coalition family, recovered under his own
surjectivity assumption.**

Peleg Definition 3.3 sets `E_α(∅; Γ) = {A}` by fiat and assumes the outcome
function is onto the social states. Without surjectivity the empty coalition's
family is the supersets of the reachable set. With it, that least element is
the whole space and the family is the singleton print writes.
-/
public theorem effectivity_empty_eq_singleton_univ
    (h : Function.Surjective G.outcome) :
    effectivity G (∅ : Set N) = ({Set.univ} : Set (Set X)) := by
  have hr : Set.range G.outcome = Set.univ := Set.range_eq_univ.mpr h
  ext A
  simp only [Set.mem_singleton_iff]
  constructor
  · intro hA
    exact Set.univ_subset_iff.mp (hr ▸ range_outcome_subset_of_mem_effectivity_empty hA)
  · rintro rfl
    rw [← hr]
    exact range_outcome_mem_effectivity_empty

/--
**Peleg's EF condition (ii), recovered under his own surjectivity
assumption.**

Print lists `E(N) = 2^A \ {∅}` as a defining condition on an effectivity
function. For the α-effectivity function of a game form whose outcome function
is onto it is a **theorem**: the grand coalition fixes a whole profile, so it
forces exactly the sets containing some reachable outcome, and surjectivity
makes that every non-empty set.

Stated here rather than in `Separations` because it is the companion of
`effectivity_empty_eq_singleton_univ` and carries the same hypothesis. Together
they are print's conditions (i) and (ii), and neither holds without
surjectivity -- which this repository does not impose, deliberately.
-/
public theorem effectivity_univ_eq_nonempty (h : Function.Surjective G.outcome) :
    effectivity G (Set.univ : Set N) = {A : Set X | A.Nonempty} := by
  ext A
  constructor
  · rintro ⟨sC, hsC⟩
    exact ⟨G.outcome fun i => sC ⟨i, trivial⟩, hsC _ fun _ => rfl⟩
  · rintro ⟨x, hx⟩
    obtain ⟨s, rfl⟩ := h x
    refine ⟨fun i => s i, fun s' hs' => ?_⟩
    have : s' = s := funext fun i => hs' ⟨i, trivial⟩
    rwa [this]

/-! ## The list, together

Bundled so a consumer can cite one name. The conjunction is exactly the five
playability conditions plus regularity and the principal element, with the two
already-proved ones supplied from `Separations`.
-/

/--
**`effectivity` is playable.**

Pauly's five conditions in his order: liveness, safety, `N`-maximality, outcome
monotonicity, superadditivity. This is the easy direction of his Theorem 3.2; see
the module header for what the hard direction would need.
-/
public theorem effectivity_playable [∀ i, Nonempty (G.strategy i)] :
    (∀ C : Set N, (∅ : Set X) ∉ effectivity G C) ∧
    (∀ C : Set N, (Set.univ : Set X) ∈ effectivity G C) ∧
    (∀ A : Set X, Aᶜ ∉ effectivity G (∅ : Set N) → A ∈ effectivity G (Set.univ : Set N)) ∧
    (∀ (C : Set N) (A B : Set X), A ⊆ B → A ∈ effectivity G C → B ∈ effectivity G C) ∧
    (∀ (C D : Set N) (A B : Set X), Disjoint C D →
      A ∈ effectivity G C → B ∈ effectivity G D → A ∩ B ∈ effectivity G (C ∪ D)) :=
  ⟨fun C => not_forces_empty C,
   fun C => forces_univ C,
   fun _ h => forces_univ_of_not_forces_empty_compl h,
   fun _ _ _ hAB hA => hA.mono hAB,
   fun _ _ _ _ hCD hA hB => forces_superadditive hCD hA hB⟩

/--
**The two consequences Pauly derives, and one condition he does not state.**

Regularity and coalition monotonicity are his Lemma 3.1, obtained here directly
rather than from playability. The third clause -- a least element at the empty
coalition -- is not in Pauly 2002 at all; see the module header.
-/
public theorem effectivity_regular_and_principal [∀ i, Nonempty (G.strategy i)] :
    (∀ (C : Set N) (A : Set X), A ∈ effectivity G C → Aᶜ ∉ effectivity G Cᶜ) ∧
    (∀ (C D : Set N), C ⊆ D → effectivity G C ⊆ effectivity G D) ∧
    (∃ A : Set X, A ∈ effectivity G (∅ : Set N) ∧
      ∀ B ∈ effectivity G (∅ : Set N), A ⊆ B) :=
  ⟨fun _ _ h => not_forces_compl_of_forces h,
   fun _ _ hCD _ hA => hA.mono_coalition hCD,
   ⟨Set.range G.outcome, range_outcome_mem_effectivity_empty,
     fun _ hB => range_outcome_subset_of_mem_effectivity_empty hB⟩⟩

/-! ## Pauly's Claim, over the partition rather than over its construction

Page 153 partitions the players into blocks that agree on what to force, sets
`G(f) = ⋂_l f(C_l)`, and claims that intersection is non-empty. The claim needs
only three things of the partition: that its blocks are disjoint, that they cover
the players, and that the choice is constant on each block so `f(C_l)` is
well-defined at all.

Those three are packaged here as `BlockChoice`, and the claim is proved over it.
Building the particular `P_∞(f)` print constructs -- iterating the refinement to a
fixed point -- is a separate obligation and is **not discharged here**; see the
note at the end of this section. Splitting them this way means the consumer side
of Theorem 3.2 can be written against the interface while the construction is
still missing.
-/

/--
**A partition of the players with a choice per block.**

`rel` is the partition, `choice i` is the set player `i`'s block commits to
forcing, and `choice_const` is what makes that a property of the block rather
than of the player. Print gets `choice_const` from stability of the refinement:
inside a block of the *fixed point*, members agree on the value at their own
block, which is exactly what lets print "simply write `f(C_l)`".
-/
public structure BlockChoice (N : Type u) (X : Type v) where
  /-- Which players share a block. -/
  rel : Setoid N
  /-- What a player's block commits to. -/
  choice : N → Set X
  /-- The commitment depends on the block, not the player. -/
  choice_const : ∀ i j, rel.r i j → choice i = choice j

namespace BlockChoice

variable {N : Type u} {X : Type v} (B : BlockChoice N X)

/-- The players in a given block. -/
@[expose] public def blockOf (b : Quotient B.rel) : Set N :=
  {i | @Quotient.mk _ B.rel i = b}

/-- What that block commits to forcing. -/
@[expose] public noncomputable def blockChoice (b : Quotient B.rel) : Set X :=
  Quotient.liftOn b B.choice B.choice_const

@[simp] public theorem mem_blockOf {b : Quotient B.rel} {i : N} :
    i ∈ B.blockOf b ↔ @Quotient.mk _ B.rel i = b := Iff.rfl

/-- Distinct blocks share no player. -/
public theorem blockOf_disjoint {b c : Quotient B.rel} (h : b ≠ c) :
    Disjoint (B.blockOf b) (B.blockOf c) := by
  rw [Set.disjoint_left]
  intro i hi hj
  exact h (hi ▸ hj ▸ rfl)

/-- Every player is in a block. -/
public theorem iUnion_blockOf : (⋃ b, B.blockOf b) = (Set.univ : Set N) := by
  ext i
  exact ⟨fun _ => trivial, fun _ => Set.mem_iUnion.mpr ⟨_, rfl⟩⟩

/-- The block's commitment is what each of its members named. -/
@[simp] public theorem blockChoice_mk (i : N) :
    B.blockChoice (@Quotient.mk _ B.rel i) = B.choice i := rfl

end BlockChoice

/--
**Pauly's Claim.** If every block forces what it committed to, the whole player
set forces the intersection of those commitments.

This is n-ary superadditivity at the partition, and it is the step his proof
justifies with "since `C_l` is effective for `f(C_l)` ... by superadditivity".
-/
public theorem forces_iInter_blockChoice [∀ i, Nonempty (G.strategy i)]
    (B : BlockChoice N X)
    (h : ∀ b : Quotient B.rel, Forces G (B.blockOf b) (B.blockChoice b)) :
    Forces G (Set.univ : Set N) (⋂ b, B.blockChoice b) := by
  have := forces_iInter_of_pairwiseDisjoint
    (fun _ _ hbc => B.blockOf_disjoint hbc) h
  rwa [B.iUnion_blockOf] at this

/--
**So the constructed outcome set is non-empty**, which is what print's Claim
asserts and what makes the game form's outcome function total.
-/
public theorem iInter_blockChoice_nonempty [∀ i, Nonempty (G.strategy i)]
    (B : BlockChoice N X)
    (h : ∀ b : Quotient B.rel, Forces G (B.blockOf b) (B.blockChoice b)) :
    (⋂ b, B.blockChoice b).Nonempty :=
  iInter_nonempty_of_pairwiseDisjoint (fun _ _ hbc => B.blockOf_disjoint hbc) h

/--
**A coalition that no refinement step would split.** Print needs, in both
directions of Theorem 3.2, that a coalition whose members all agree on what to
force lies inside a single block.
-/
@[expose] public def BlockChoice.Unsplit (B : BlockChoice N X) (C : Set N) : Prop :=
  ∃ b : Quotient B.rel, C ⊆ B.blockOf b

/-- An unsplit coalition's block commits to what its members named. -/
public theorem BlockChoice.blockChoice_of_unsplit {B : BlockChoice N X} {C : Set N}
    {b : Quotient B.rel} (hb : C ⊆ B.blockOf b) {i : N} (hi : i ∈ C) :
    B.blockChoice b = B.choice i := by
  have : @Quotient.mk _ B.rel i = b := hb hi
  rw [← this, B.blockChoice_mk]

/-! ### Print's `P_∞(f)`, built

`BlockChoice` is an interface, and Theorem 3.2 needs a particular inhabitant of
it: print's `P_∞(f)`, the fixed point of iterated refinement. **That construction
is now here**, in the section below -- `refineSeq`, `exists_refineFixed` and
`BlockChoice.ofChoiceFunctions`.

`Unsplit` is done too: `coalition_related_of_agree` is print's induction, and
`BlockChoice.unsplit_ofChoiceFunctions` lands it at the fixed point. **So part 2
of the four is complete.** Parts 1 and 4 -- the triples `(f_i, t_i, h_i)`, the
dictator chosen by `((t_1 + … + t_n) mod n) + 1`, and the two inclusions -- are in
`AISafetyAtlas.Sovereignty.PlayableConverse`, which also shows the equality
cannot be had at `∅` or at `N` by any construction -- from playability alone.
`AISafetyAtlas.Sovereignty.Representation` shows the two ends come back once
Peleg's page-72 conditions `E(∅) = {A}` and `E(N) = 2^A ∖ {∅}` are imposed, which
is where his Theorem 3.5 differs from Pauly's Theorem 3.2.
-/

/-! ### Finitely many players, finitely many partitions

Print spends one clause on this. Mathlib does not carry it, so it is proved here
rather than assumed, and it is stated for an arbitrary finite type because
nothing about it is specific to players.
-/

/-- **The setoids on a finite type are finite.** A setoid is determined by its
relation, and there are finitely many binary relations on a finite type. Mathlib
has `Finite (Quotient s)` but not this. -/
public instance instFiniteSetoid {α : Type*} [Finite α] : Finite (Setoid α) := by
  apply Finite.of_injective (fun s : Setoid α => (fun a b => s.r a b))
  intro s t h
  ext a b
  exact Iff.of_eq (congrFun (congrFun h a) b)

/--
**A refining sequence of partitions on a finite type stabilises.**

This is print's *"since there are only finitely many players, this partitioning
process will eventually stop"*, and it is the whole of the termination argument
Theorem 3.2's construction needs.

Refinement makes a setoid **smaller** in Mathlib's order, so the sequence is
decreasing and the statement is the descending chain condition; `Finite` supplies
well-foundedness in both directions, so the ascending-chain lemma applies to the
order dual.
-/
public theorem exists_stable_of_refining {α : Type*} [Finite α] (P : ℕ → Setoid α)
    (hrefine : ∀ n, P (n + 1) ≤ P n) : ∃ n, ∀ m, n ≤ m → P n = P m := by
  have hmono : Monotone fun n => OrderDual.toDual (P n) :=
    monotone_nat_of_le_succ fun n => hrefine n
  exact WellFoundedGT.monotone_chain_condition ⟨_, hmono⟩

/-! ### The refinement itself

Print's construction on page 153. Each player `i` brings a choice function `f i`
naming, for every coalition, a set that coalition is to force. Starting from the
partition with one block, split each block into the players who agree on what
*that block* should force, and iterate.
-/

/-- The block of `i` under `P`: the players `P` relates to `i`. -/
@[expose] public def blockUnder {N : Type u} (P : Setoid N) (i : N) : Set N :=
  {j | P.r i j}

/-- **One refinement step.** Keep `i` and `j` together when they were together
*and* they name the same set for the block they share. -/
@[expose] public def refineStep {N : Type u} {X : Type v}
    (f : N → Set N → Set X) (P : Setoid N) : Setoid N where
  r i j := P.r i j ∧ f i (blockUnder P i) = f j (blockUnder P j)
  iseqv := by
    constructor
    · intro i; exact ⟨P.refl i, rfl⟩
    · rintro i j ⟨h1, h2⟩; exact ⟨P.symm h1, h2.symm⟩
    · rintro i j k ⟨h1, h2⟩ ⟨h3, h4⟩; exact ⟨P.trans h1 h3, h2.trans h4⟩

/-- Refining only splits blocks; it never merges them. -/
public theorem refineStep_le {N : Type u} {X : Type v}
    (f : N → Set N → Set X) (P : Setoid N) : refineStep f P ≤ P :=
  fun _ _ h => h.1

/-- **The sequence `P_0, P_1, …`**, from the partition with one block. -/
@[expose] public def refineSeq {N : Type u} {X : Type v}
    (f : N → Set N → Set X) : ℕ → Setoid N
  | 0 => ⊤
  | n + 1 => refineStep f (refineSeq f n)

/-- It refines at every step, so `exists_stable_of_refining` applies to it. -/
public theorem refineSeq_le {N : Type u} {X : Type v}
    (f : N → Set N → Set X) (n : ℕ) : refineSeq f (n + 1) ≤ refineSeq f n :=
  refineStep_le f _

/-- Later partitions are finer. -/
public theorem refineSeq_antitone {N : Type u} {X : Type v}
    (f : N → Set N → Set X) {m n : ℕ} (hmn : m ≤ n) :
    refineSeq f n ≤ refineSeq f m := by
  induction n with
  | zero => rw [Nat.le_zero.mp hmn]
  | succ n ih =>
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · exact le_trans (refineSeq_le f n) (ih (Nat.lt_succ_iff.mp h))
      · rw [Nat.le_antisymm hmn h]

/--
**The refinement reaches a fixed point, and at it a block's members agree on what
their own block forces.**

This is what stabilisation was for. Away from the fixed point the members of a
block agree on the value at their *parent* block; at the fixed point the block is
its own parent, so they agree on its own value -- which is exactly
`BlockChoice.choice_const`.

The third conjunct records that the fixed point is finer than **every** stage, not
only the ones before it: past the stabilisation index the stages are equal, and
before it the sequence is antitone. Without it the fixed point is opaque, and
nothing downstream could show that the refinement ever actually splits a block.
-/
public theorem exists_refineFixed {N : Type u} {X : Type v} [Finite N]
    (f : N → Set N → Set X) :
    ∃ n : ℕ, refineStep f (refineSeq f n) = refineSeq f n ∧
      (∀ i j, (refineSeq f n).r i j →
        f i (blockUnder (refineSeq f n) i) = f j (blockUnder (refineSeq f n) j)) ∧
      ∀ m, refineSeq f n ≤ refineSeq f m := by
  obtain ⟨n, hn⟩ := exists_stable_of_refining (refineSeq f) (refineSeq_le f)
  refine ⟨n, (hn (n + 1) (Nat.le_succ n)).symm, fun i j hij => ?_, fun m => ?_⟩
  · have hstep : (refineStep f (refineSeq f n)).r i j := by
      rw [hn (n + 1) (Nat.le_succ n)] at hij
      exact hij
    exact hstep.2
  · rcases Nat.le_total m n with h | h
    · exact refineSeq_antitone f h
    · rw [hn m h]

/--
**Print's `P_∞(f)` as an inhabitant of the interface.**

Given the players' choice functions, the fixed point of the refinement is a
`BlockChoice`, with each block committing to the set its members agree on. Every
consumer written against the interface -- `forces_iInter_blockChoice`,
`iInter_blockChoice_nonempty` -- now has something to run on.
-/
@[expose] public noncomputable def BlockChoice.ofChoiceFunctions {N : Type u} {X : Type v}
    [Finite N] (f : N → Set N → Set X) : BlockChoice N X :=
  { rel := refineSeq f (exists_refineFixed f).choose
    choice := fun i => f i (blockUnder (refineSeq f (exists_refineFixed f).choose) i)
    choice_const := (exists_refineFixed f).choose_spec.2.1 }

/-- The partition returned is a stage of the refinement, and which stage is
recoverable. Both directions of reasoning about it go through this. -/
public theorem BlockChoice.ofChoiceFunctions_rel {N : Type u} {X : Type v} [Finite N]
    (f : N → Set N → Set X) :
    (BlockChoice.ofChoiceFunctions f).rel = refineSeq f (exists_refineFixed f).choose := rfl

/-- **The built partition is finer than every stage of the refinement.** So a
stage that separates two players witnesses that the fixed point separates them,
which is how anything gets shown about an object produced by choice. -/
public theorem BlockChoice.ofChoiceFunctions_le {N : Type u} {X : Type v} [Finite N]
    (f : N → Set N → Set X) (n : ℕ) :
    (BlockChoice.ofChoiceFunctions f).rel ≤ refineSeq f n :=
  (exists_refineFixed f).choose_spec.2.2 n

/-! ### `Unsplit`: which coalitions the refinement leaves whole -/

/-- Related players have the same block. -/
public theorem blockUnder_eq {N : Type u} {P : Setoid N} {i j : N} (h : P.r i j) :
    blockUnder P i = blockUnder P j := by
  ext k
  exact ⟨fun hk => P.trans (P.symm h) hk, fun hk => P.trans h hk⟩

/--
**No refinement stage splits a coalition whose members already agree.**

If every member of `C` names the same set for every coalition containing `C`,
then at every stage they are still together. The induction is print's: at stage
`0` everyone shares a block; at stage `n + 1` the members of `C` were together at
stage `n`, so `C` sits inside their common block, so the agreement hypothesis
applies to *that* block and the step keeps them together.
-/
public theorem coalition_related_of_agree {N : Type u} {X : Type v}
    (f : N → Set N → Set X) (C : Set N)
    (hagree : ∀ C' : Set N, C ⊆ C' → ∀ i ∈ C, ∀ j ∈ C, f i C' = f j C')
    (n : ℕ) : ∀ i ∈ C, ∀ j ∈ C, (refineSeq f n).r i j := by
  induction n with
  | zero => intro i _ j _; trivial
  | succ n ih =>
      intro i hi j hj
      refine ⟨ih i hi j hj, ?_⟩
      have hsub : C ⊆ blockUnder (refineSeq f n) i := fun k hk => ih i hi k hk
      have hblk : blockUnder (refineSeq f n) i = blockUnder (refineSeq f n) j :=
        blockUnder_eq (ih i hi j hj)
      calc f i (blockUnder (refineSeq f n) i)
          = f j (blockUnder (refineSeq f n) i) := hagree _ hsub i hi j hj
        _ = f j (blockUnder (refineSeq f n) j) := by rw [hblk]

/--
**`Unsplit`, at print's `P_∞(f)`.** A non-empty coalition whose members agree on
every coalition containing it lies inside a single block of the built partition.

This is the last of the two obligations the `BlockChoice` interface carried.
Non-emptiness is needed only to name the block; on the empty coalition the
statement is about which block it is nominally inside, and every block will do.
-/
public theorem BlockChoice.unsplit_ofChoiceFunctions {N : Type u} {X : Type v} [Finite N]
    (f : N → Set N → Set X) {C : Set N} (hC : C.Nonempty)
    (hagree : ∀ C' : Set N, C ⊆ C' → ∀ i ∈ C, ∀ j ∈ C, f i C' = f j C') :
    (BlockChoice.ofChoiceFunctions f).Unsplit C := by
  obtain ⟨i, hi⟩ := hC
  refine ⟨@Quotient.mk _ (BlockChoice.ofChoiceFunctions f).rel i, fun j hj => ?_⟩
  show @Quotient.mk _ (BlockChoice.ofChoiceFunctions f).rel j = _
  exact Quotient.sound (coalition_related_of_agree f C hagree _ j hj i hi)

/-! ## Theorem 3.3: when every coalition's power is already somebody's

Pauly's section 3.2, page 154. An effectivity function is **individualistic**
when it is playable and `E(N) = ⋃_{i ∈ N} E({i})` -- everything the grand
coalition can force, some individual can already force. Print's own gloss on why
the condition is stronger than it looks:

> while it seems to say only that the whole is equal to the sum of its parts, it
> actually says that the whole is equal to one particular part.

The proof is four lines and runs entirely on superadditivity and liveness: two
different players forcing two different outcomes would jointly force nothing,
which liveness forbids.
-/

/--
**Individualistic.** Print writes the condition as an equality. The `⊇` half is
free -- `iUnion_effectivity_singleton_subset` below -- so the content is the
other inclusion, but the definition is stated as print states it.

Print's own definition also asks that `E` be playable, which is automatic here
and therefore dropped. `IndividualisticEff` in `AISafetyAtlas.Sovereignty.PlayableConverse` is the same notion
on a bare effectivity function with that conjunct restored, and
`individualisticEff_effectivity_iff` is the lemma saying the
two agree on a game form.
-/
@[expose] public def Individualistic (G : GameForm.{u, v, w} N X) : Prop :=
  effectivity G (Set.univ : Set N) = ⋃ i : N, effectivity G ({i} : Set N)

/-- **A dictator forces every outcome the game can reach.**

Not every outcome of the type: print is explicit on the same page that the
outcome function need not be surjective, and a player cannot force what nobody
can bring about. Restricting to `Set.range G.outcome` is what keeps the notion
from being empty in exactly the games Pauly's Theorem 3.2 is careful about. -/
@[expose] public def IsDictator (G : GameForm.{u, v, w} N X) (d : N) : Prop :=
  ∀ x ∈ Set.range G.outcome, Forces G ({d} : Set N) ({x} : Set X)

/-- The easy half of the individualistic equation, by coalition monotonicity. -/
public theorem iUnion_effectivity_singleton_subset [∀ i, Nonempty (G.strategy i)] :
    (⋃ i : N, effectivity G ({i} : Set N)) ⊆ effectivity G (Set.univ : Set N) := by
  intro A hA
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hA
  exact hi.mono_coalition (Set.subset_univ _)

/--
**Theorem 3.3, the half that survives.** For a game form, its effectivity
function is individualistic exactly when the game form is a dictatorship.

**Corrected 2026-09-10.** This docstring stated print's own sentence -- *"An
effectivity function is individualistic iff it is the effectivity function of a
dictatorship"* -- and the statement below is not that. Print quantifies over an
arbitrary effectivity function; this quantifies over an existing `GameForm`, so
it says nothing about an `E` not already known to be some game's. That is not a
gap this module can close: print's own proof of the surviving direction opens
*"assume `E` is individualistic, and so there is a strategic game such that
`E = E_G`"*, and **that step is Theorem 3.2**, whose left-to-right direction
`AISafetyAtlas.Sovereignty.PlayableConverse` refutes at the cofinite filter.
Print's Theorem 3.3 therefore inherits Theorem 3.2's defect at the same witness,
and the game-form-internal biconditional below is what is left standing. Goranko,
Jamroga and Turrini's repair would recover it at *truly* playable effectivity
functions; that route is not taken here.

**That was an argument about print's proof, and on 2026-09-20 it became one
about print's statement.** `not_forall_individualisticEff_exists_dictator`, in
`AISafetyAtlas.Sovereignty.PlayableConverse`, refutes Theorem 3.3 at print's own quantifier: `cofiniteEff` satisfies print's
definition of *individualistic* — `IndividualisticEff`, which carries print's
playability conjunct as well as the equation below — and is the effectivity
function of no game form, so *a fortiori* of no dictatorship. The refutation
never reads the word *dictatorship*, so no reading of print's right-hand side
saves the sentence.

The direction that carries the content is left to right, and it is where "the
whole is one particular part" is earned: pick any reachable outcome, take the
individual who forces it, and every other reachable outcome must be forced by
that *same* individual -- a second one would give two disjoint singletons forced
by two disjoint coalitions, hence the empty set forced, which `not_forces_empty`
refutes.
-/
public theorem individualistic_iff_exists_dictator [Nonempty N]
    [∀ i, Nonempty (G.strategy i)] :
    Individualistic G ↔ ∃ d, IsDictator G d := by
  classical
  constructor
  · intro hind
    have hmemU : ∀ x ∈ Set.range G.outcome,
        ({x} : Set X) ∈ effectivity G (Set.univ : Set N) := by
      rintro x ⟨s, rfl⟩
      exact forces_univ_iff.mpr ⟨s, rfl⟩
    have hsome : ∀ x ∈ Set.range G.outcome,
        ∃ i, Forces G ({i} : Set N) ({x} : Set X) := by
      intro x hx
      have h2 : ({x} : Set X) ∈ ⋃ i : N, effectivity G ({i} : Set N) :=
        hind ▸ hmemU x hx
      exact Set.mem_iUnion.mp h2
    have ht₁ : G.outcome (fun _ => Classical.arbitrary _) ∈ Set.range G.outcome := ⟨_, rfl⟩
    obtain ⟨d, hd⟩ := hsome _ ht₁
    refine ⟨d, fun x hx => ?_⟩
    by_cases hxt : x = G.outcome (fun _ => Classical.arbitrary _)
    · exact hxt ▸ hd
    · obtain ⟨j, hj⟩ := hsome x hx
      have hjd : j = d := by
        by_contra hne
        have hdisj : Disjoint ({d} : Set N) ({j} : Set N) :=
          Set.disjoint_singleton.mpr fun h => hne h.symm
        have hjoint := forces_superadditive hdisj hd hj
        have hempty : ({G.outcome (fun _ => Classical.arbitrary _)} : Set X) ∩ {x} = ∅ :=
          Set.singleton_inter_eq_empty.mpr fun h => hxt (h.symm)
        rw [hempty] at hjoint
        exact not_forces_empty _ hjoint
      exact hjd ▸ hj
  · rintro ⟨d, hd⟩
    refine Set.Subset.antisymm (fun A hA => ?_) iUnion_effectivity_singleton_subset
    obtain ⟨s, hs⟩ := forces_univ_iff.mp hA
    exact Set.mem_iUnion.mpr ⟨d, (hd _ ⟨s, rfl⟩).mono (Set.singleton_subset_iff.mpr hs)⟩

end AISafetyAtlas.Sovereignty
