module

public import AISafetyAtlas.Sovereignty.Playability
public import Mathlib.Data.Set.Finite.Lattice
public import Mathlib.Data.ZMod.Basic

/-!
# Pauly's Theorem 3.2, the converse direction

`Playability` proves the easy direction: the effectivity function of a game form
satisfies Pauly's five conditions. This module takes an abstract effectivity
function satisfying them and asks what game it comes from.

Marc Pauly, *A Modal Logic for Coalitional Power in Games*, Journal of Logic and
Computation 12(1): 149-166, 2002, DOI `10.1093/logcom/12.1.149`, pages 151-154,
read from rendered page images because the paper is DVI-set and text extraction
drops the mathematics silently. Source pinned in
`SOURCES-2026-09-09-sovereignty.md` under
`pauly-coalition.pdf`.

Page 151 defines the effectivity function of a game:

> `X ∈ E_G(C)` iff `∃σ_C ∀σ_C̄ o(σ_C, σ_C̄) ∈ X`

which is `Forces` in `Separations`. Page 152 states

> **Theorem 3.2 (Characterization)** An effectivity function `E` is playable iff
> it is the effectivity function of some strategic game.

## The result of this module, and whose result it is

**The right-to-left direction is true and already proved** (`effectivity_playable`
in `Playability`). **The left-to-right direction, as printed, is false**, and
`not_exists_gameForm_cofiniteEff` below is a witness: a playable effectivity
function on one player over `ℕ` that is not `effectivity G` for any game form `G`.

**This refutation is not new, and this module does not claim it.** It is
Goranko, Jamroga and Turrini, *Strategic Games and Truly Playable Effectivity
Functions*, Autonomous Agents and Multi-Agent Systems 26: 288-314 (2013), DOI
`10.1007/s10458-012-9192-y`, conference version AAMAS 2011; pinned in
`SOURCES-2026-09-09-sovereignty.md` as the
author manuscript, the published text being subscription-only. Their abstract
states it: *"While the latter direction of the correspondence is correct, we show
that the former does not hold for a number of infinite state games. We point out
where the original proof of correspondence goes wrong."*

The witness below was built here before that paper was found, and it is **the
same counterexample**: their single player over `N` with `E({a})` the infinite
subsets and `E(∅)` the cofinite ones, obstructed because *"there are no minimal
cofinite sets"*. Arriving at it independently is evidence the Lean statement is
faithful; it is not a discovery. What this module contributes is the mechanized
form -- the five conditions checked, the non-existence proved rather than argued,
and the two inclusions proved exactly where they hold.

That paper is also the source of the notion `Playability` calls truly playable
and attributes to the Lean development `kaiobendrauf/cl-lean`; `cl-lean` is
formalizing it, not originating it.

The obstruction is one line of `Playability` that Pauly does not state. For a game
form, `effectivity G ∅` is the family of supersets of `Set.range G.outcome` --
`forces_empty_iff_range_subset` -- so it always has a **least element**.
Playability does not force that: the five conditions make `E ∅` a proper filter,
and a proper filter on an infinite set need not be principal. The cofinite filter
on `ℕ` is the witness.

This vindicates `range_outcome_mem_effectivity_empty`, which `Playability` carries
as a clause that "is **not** part of playability". It is not decoration: it is
exactly what Pauly's list is missing, and it is the condition Goranko, Jamroga and
Turrini add to reach their truly playable class.

**The printed proof breaks at a nameable step**, which those authors also
locate -- the step named below was found here independently and should be read
against theirs, not instead of it. Page 154 opens the right-to-left
inclusion with

> Suppose first that `C = N`. Then by `N`-maximality, `X̄ ∈ E(∅)`, and by the
> previous part of the proof, `X̄ ∈ E_G(∅)`.

and "the previous part of the proof" is the left-to-right inclusion, whose page-154
argument is

> note that `C` must be a subset of one of the partitions `C_l` in `P_∞(f)`.
> Hence `o(σ_N) = h_{i₀}(G(f)) ∈ G(f) ⊆ f(C_l) = X`.

At `C = ∅` the containment `C ⊆ C_l` is free but `f(C_l) = X` is never
established, because `f(C_l)` is what the *members* of `C_l` named and `C = ∅`
has no members to constrain them. So the left-to-right inclusion is unproved at
the empty coalition, and the `C = N` case of the other inclusion consumes it.

Goranko, Jamroga and Turrini reach the same two steps, in their numbering Step 5
and Step 6: *"there is no guarantee that any `i` will indeed choose `f_i` as its
strategy since the coalition `C` for which we can fix its strategy does not
include any players"*, and *"in order to establish the inclusion for `C = N`, it
is reduced to inclusion in step 5 for `C = ∅`"*. They carry one thing this module
does not: a **direct** refutation at `C = N` that does not route through the empty
coalition -- every player choosing `f_i(C) = S` everywhere with a common selector
`h_i(S) = x` puts `{x}` in `E_G(N)` for an `E` with `{x} ∉ E(N)`. That is a
second, independent obstruction at the grand coalition, and it is not formalized
here.

## What is built here

Playability as a hypothesis, print's Lemma 3.1 from it, superadditivity over a
finite family of disjoint coalitions -- which is the shape page 153's Claim needs
-- and the refutation. Then the construction itself, and the two inclusions where
they hold:

| print | here | side condition |
|---|---|---|
| `Σ_i = F_i × N × H` | `ChoiceFn`, `Picker`, `Strat` | -- |
| `G(f) = ⋂_l f(C_l)` | `outcomeSet`, `Playable.outcomeSet_nonempty` | -- |
| `i₀ = ((t_1 + ⋯ + t_n) mod n) + 1` | `dictator`, `exists_dictator_eq` | -- |
| the game `G` | `paulyGame` | -- |
| `E(C) ⊆ E_G(C)` | `Playable.mem_effectivity_paulyGame_of_mem` | `C.Nonempty` |
| `E_G(C) ⊆ E(C)` | `Playable.mem_of_mem_effectivity_paulyGame` | `C ≠ Set.univ` |
| `E = E_G` | `Playable.effectivity_paulyGame_eq`, both conditions | not at `∅`, not at `N` |

So the equality holds at every coalition other than the two ends of the lattice,
and it is not that the missing ends are unproved: they are false, by
`not_exists_gameForm_cofiniteEff`, which rules out any construction closing them
and so in particular this one. On one player there are no other coalitions, which
is why the witness needs only one.

**`N`-maximality is used nowhere below.** Both inclusions and every lemma they
rest on consume liveness, safety, outcome-monotonicity and superadditivity only.
Condition (3) is read exactly once in Pauly's proof, in the `C = N` step, and
that step is the broken one. The `Playability` header's remark that this is
"where N-maximality earns its place on the playability list" was written before
this module existed and is corrected there.
-/
namespace AISafetyAtlas.Sovereignty

universe u v w

/-! ## Playability as a predicate on an abstract effectivity function

Page 152:

> Call an effectivity function `E : P(N) → P(P(S))` *playable* iff (1) `∀C ⊆ N :
> ∅ ∉ E(C)`, (2) `∀C ⊆ N : S ∈ E(C)`, (3) `E` is `N`-maximal, (4) `E` is
> outcome-monotonic, and (5) `E` is superadditive.

`effectivity_playable` in `Playability` proves this conjunction for a game form's
own effectivity function; the fields below are that conjunction, in print's order,
given a name so it can be a hypothesis.
-/

/--
**Pauly's five playability conditions**, on an arbitrary effectivity function.

`N` is the whole player set, so print's `C̄` is `Cᶜ` and print's `N` is
`Set.univ`.
-/
public structure Playable {N : Type u} {X : Type v} (E : Set N → Set (Set X)) : Prop where
  /-- (1) No coalition is effective for the empty set. -/
  live : ∀ C : Set N, (∅ : Set X) ∉ E C
  /-- (2) Every coalition is effective for the whole outcome space. -/
  safe : ∀ C : Set N, (Set.univ : Set X) ∈ E C
  /-- (3) `N`-maximality: `E` is `C`-maximal at `C = Set.univ`, where `C̄ = ∅`. -/
  maximal : ∀ A : Set X, Aᶜ ∉ E (∅ : Set N) → A ∈ E (Set.univ : Set N)
  /-- (4) Outcome-monotonicity. -/
  mono : ∀ (C : Set N) (A B : Set X), A ⊆ B → A ∈ E C → B ∈ E C
  /-- (5) Superadditivity. -/
  superadd : ∀ (C D : Set N) (A B : Set X), Disjoint C D →
    A ∈ E C → B ∈ E D → A ∩ B ∈ E (C ∪ D)

/-- A game form's effectivity function is playable: `Playability`'s
`effectivity_playable`, repackaged. -/
public theorem playable_effectivity {N : Type u} {X : Type v}
    {G : GameForm.{u, v, w} N X} [∀ i, Nonempty (G.strategy i)] :
    Playable (effectivity G) :=
  { live := fun C => not_forces_empty C
    safe := fun C => forces_univ C
    maximal := fun _ h => forces_univ_of_not_forces_empty_compl h
    mono := fun _ _ _ hAB hA => hA.mono hAB
    superadd := fun _ _ _ _ hCD hA hB => forces_superadditive hCD hA hB }

namespace Playable

variable {N : Type u} {X : Type v} {E : Set N → Set (Set X)}

/-!
### Lemma 3.1

Page 152:

> **Lemma 3.1** Every playable effectivity function is regular and
> coalition-monotonic.

Print's proof, transcribed: regularity from (5) and (1), coalition-monotonicity
from (2) and (5) via `C'' := C' \ C`.
-/

/-- **Regularity**, print's Lemma 3.1 first half. A coalition and its complement
cannot both be effective for complementary sets, since superadditivity would make
the empty set effective for the grand coalition. -/
public theorem regular (hE : Playable E) {C : Set N} {A : Set X}
    (hA : A ∈ E C) : Aᶜ ∉ E Cᶜ := by
  intro hcompl
  have hd : Disjoint C Cᶜ := disjoint_compl_right
  have := hE.superadd C Cᶜ A Aᶜ hd hA hcompl
  rw [Set.inter_compl_self, Set.union_compl_self] at this
  exact hE.live _ this

/-- **Coalition-monotonicity**, print's Lemma 3.1 second half. A bigger coalition
is effective for at least as much: pad with `C' \ C`, which (2) makes effective
for everything. -/
public theorem mono_coalition (hE : Playable E) {C D : Set N} (hCD : C ⊆ D) :
    E C ⊆ E D := by
  intro A hA
  have hd : Disjoint C (D \ C) := disjoint_sdiff_self_right
  have := hE.superadd C (D \ C) A Set.univ hd hA (hE.safe _)
  rwa [Set.inter_univ, Set.union_sdiff_cancel hCD] at this

/-!
### Superadditivity over a finite family

Page 153's Claim runs superadditivity over the whole partition at once:

> Since `C_l` is effective for `f(C_l)`, i.e. `f(C_l) ∈ E(C_l)` for all `l ≤ k`,
> `⋂_{l=1}^{k} f(C_l) = G(f) ∈ E(N)` by superadditivity

Print writes this as one appeal. It is an induction on the number of blocks, and
the base case is where condition (2) is consumed: an empty family intersects to
the whole space, which the *empty* coalition is effective for.
-/

/-- **Superadditivity over a `Finset` of pairwise disjoint coalitions.** -/
public theorem biInter_mem {ι : Type*} (hE : Playable E) (C : ι → Set N)
    (A : ι → Set X) (s : Finset ι)
    (hdisj : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ i ∈ s, A i ∈ E (C i)) :
    (⋂ i ∈ s, A i) ∈ E (⋃ i ∈ s, C i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hE.safe (∅ : Set N)
  | insert a t ha ih =>
      have hdisj' : ∀ i ∈ t, ∀ j ∈ t, i ≠ j → Disjoint (C i) (C j) := by
        intro i hi j hj hij
        exact hdisj i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj) hij
      have hmem' : ∀ i ∈ t, A i ∈ E (C i) := by
        intro i hi; exact hmem i (Finset.mem_insert_of_mem hi)
      have hrec := ih hdisj' hmem'
      have hda : Disjoint (C a) (⋃ i ∈ t, C i) := by
        rw [Set.disjoint_iUnion₂_right]
        intro i hi
        exact hdisj a (Finset.mem_insert_self a t) i (Finset.mem_insert_of_mem hi)
          (fun h => ha (h ▸ hi))
      have := hE.superadd (C a) (⋃ i ∈ t, C i) (A a) (⋂ i ∈ t, A i) hda
        (hmem a (Finset.mem_insert_self a t)) hrec
      simpa [Finset.set_biInter_insert, Finset.set_biUnion_insert] using this

/-- **Superadditivity over a whole finite index type**, which is the shape page
153's Claim needs: the blocks of a partition of a finite player set. -/
public theorem iInter_mem {ι : Type*} [Fintype ι] (hE : Playable E) (C : ι → Set N)
    (A : ι → Set X) (hdisj : ∀ i j, i ≠ j → Disjoint (C i) (C j))
    (hmem : ∀ i, A i ∈ E (C i)) :
    (⋂ i, A i) ∈ E (⋃ i, C i) := by
  have := hE.biInter_mem C A Finset.univ (fun i _ j _ hij => hdisj i j hij)
    (fun i _ => hmem i)
  simpa using this

end Playable

/-! ## The converse fails: a playable effectivity function that is no game's

One player, outcomes `ℕ`, and the empty coalition's family is the cofinite filter.
Playability constrains `E ∅` to be a proper filter -- upward closed by (4), closed
under binary intersection by (5) at `C₁ = C₂ = ∅`, and missing `∅` by (1) -- and
says nothing about it having a least element. A game form's `effectivity G ∅`
always has one, namely `Set.range G.outcome`.
-/

/--
**The witness.** On one player and outcomes `ℕ`: the empty coalition is effective
for the cofinite sets, the grand coalition for the infinite sets.

Written as one formula over all `C : Set Unit` rather than by cases, so that no
decidability of set membership is needed. The two conjuncts are read at opposite
coalitions: the first is vacuous at `∅` and the second at `Set.univ`.
-/
@[expose] public def cofiniteEff : Set Unit → Set (Set ℕ) :=
  fun C => {A | (C.Nonempty → A.Infinite) ∧ (C = ∅ → Aᶜ.Finite)}

/-- At the empty coalition the witness is the cofinite filter. -/
public theorem mem_cofiniteEff_empty {A : Set ℕ} :
    A ∈ cofiniteEff ∅ ↔ Aᶜ.Finite := by
  constructor
  · intro h; exact h.2 rfl
  · intro h; exact ⟨fun hne => absurd hne (by simp), fun _ => h⟩

/-- At the grand coalition the witness is the infinite sets. -/
public theorem mem_cofiniteEff_univ {A : Set ℕ} :
    A ∈ cofiniteEff Set.univ ↔ A.Infinite := by
  constructor
  · intro h; exact h.1 ⟨(), trivial⟩
  · intro h
    exact ⟨fun _ => h, fun hEq => absurd (hEq ▸ (⟨(), trivial⟩ : (Set.univ : Set Unit).Nonempty))
      (by simp)⟩

/-- A coalition of one player is empty or everybody. -/
public theorem unit_coalition_cases (C : Set Unit) : C = ∅ ∨ C = Set.univ := by
  by_cases h : () ∈ C
  · right; ext u; cases u; simp [h]
  · left; ext u; cases u; simp [h]

/-- **The witness is playable.** All five conditions, in print's order. -/
public theorem cofiniteEff_playable : Playable cofiniteEff := by
  constructor
  · -- (1) liveness
    intro C hC
    rcases unit_coalition_cases C with rfl | rfl
    · exact Set.infinite_univ (α := ℕ) (by simpa using mem_cofiniteEff_empty.mp hC)
    · exact (mem_cofiniteEff_univ.mp hC) (by simp)
  · -- (2) safety
    intro C
    exact ⟨fun _ => Set.infinite_univ, fun _ => by simp⟩
  · -- (3) N-maximality
    intro A hA
    rw [mem_cofiniteEff_univ]
    rw [mem_cofiniteEff_empty] at hA
    rw [compl_compl] at hA
    exact hA
  · -- (4) outcome-monotonicity
    intro C A B hAB hA
    exact ⟨fun hne => (hA.1 hne).mono hAB, fun hC => (hA.2 hC).subset (Set.compl_subset_compl.mpr hAB)⟩
  · -- (5) superadditivity
    intro C D A B hCD hA hB
    rcases unit_coalition_cases C with rfl | rfl
    · rcases unit_coalition_cases D with rfl | rfl
      · rw [Set.union_self]
        rw [mem_cofiniteEff_empty] at hA hB ⊢
        rw [Set.compl_inter]
        exact hA.union hB
      · rw [Set.empty_union]
        rw [mem_cofiniteEff_empty] at hA
        rw [mem_cofiniteEff_univ] at hB ⊢
        have : (B \ Aᶜ).Infinite := hB.sdiff hA
        exact this.mono (by intro x hx; exact ⟨not_not.mp hx.2, hx.1⟩)
    · rcases unit_coalition_cases D with rfl | rfl
      · rw [Set.union_empty]
        rw [mem_cofiniteEff_empty] at hB
        rw [mem_cofiniteEff_univ] at hA ⊢
        have : (A \ Bᶜ).Infinite := hA.sdiff hB
        exact this.mono (by intro x hx; exact ⟨hx.1, not_not.mp hx.2⟩)
      · exact absurd (Set.disjoint_left.mp hCD (Set.mem_univ ())) (by simp)

/--
**Pauly's Theorem 3.2 is false from left to right.**

No game form on one player with outcomes `ℕ` has `cofiniteEff` as its effectivity
function, although `cofiniteEff_playable` says it satisfies every condition on
print's list.

The proof reads only the empty coalition. `forces_empty_iff_range_subset` makes
`effectivity G ∅` the supersets of `Set.range G.outcome`, so it has a least
element; the cofinite filter has none, because deleting one point of a cofinite
set leaves a cofinite set.
-/
public theorem not_exists_gameForm_cofiniteEff :
    ¬ ∃ G : GameForm.{0, 0, w} Unit ℕ, effectivity G = cofiniteEff := by
  rintro ⟨G, hG⟩
  set R := Set.range G.outcome with hR
  have hmem : R ∈ cofiniteEff ∅ := by
    rw [← hG]; exact range_outcome_mem_effectivity_empty
  have hRc : Rᶜ.Finite := mem_cofiniteEff_empty.mp hmem
  have hRinf : R.Infinite := by
    have := hRc.infinite_compl
    rwa [compl_compl] at this
  obtain ⟨r, hr⟩ := hRinf.nonempty
  have hdel : R \ {r} ∈ cofiniteEff ∅ := by
    rw [mem_cofiniteEff_empty]
    exact (hRc.union (Set.finite_singleton r)).subset (by
      intro x hx
      by_cases hxr : x = r
      · exact Or.inr hxr
      · exact Or.inl fun hxR => hx ⟨hxR, hxr⟩)
  have hsub : R ⊆ R \ {r} := by
    apply range_outcome_subset_of_mem_effectivity_empty
    rw [hG]; exact hdel
  exact (hsub hr).2 rfl

/-! ## Theorem 3.3 at print's own quantifier, and what it costs print

`AISafetyAtlas.Sovereignty.Playability` carries Pauly's Theorem 3.3 as a
biconditional **on an existing game form**, and its docstring says why: print
quantifies over an arbitrary effectivity function and print's own proof reaches
a game form through Theorem 3.2, whose converse `not_exists_gameForm_cofiniteEff`
refutes. That was an argument about print's proof. The two statements below make
it an argument about print's **statement**, at the same witness.
-/

/--
**Print's *individualistic*, on a bare effectivity function.**

Page 154: *"call an effectivity function `E` individualistic iff it is playable
and"* the grand coalition's power is the union of the individuals'. `Playability`'s
`Individualistic` carries only the equation, because playability is free for a
game form; here the conjunct is print's and is stated.
-/
@[expose] public def IndividualisticEff {N : Type u} {X : Type v}
    (E : Set N → Set (Set X)) : Prop :=
  Playable E ∧ E (Set.univ : Set N) = ⋃ i : N, E ({i} : Set N)

/-- On a game form the two readings agree: playability is automatic, so what is
left is the equation `Individualistic` carries. -/
public theorem individualisticEff_effectivity_iff {N : Type u} {X : Type v}
    {G : GameForm.{u, v, w} N X} [∀ i, Nonempty (G.strategy i)] :
    IndividualisticEff (effectivity G) ↔ Individualistic G :=
  ⟨fun h => h.2, fun h => ⟨playable_effectivity, h⟩⟩

/-- **The witness is individualistic.** On one player the union over individuals
is the grand coalition's own power, so the equation is free and playability is
`cofiniteEff_playable`. -/
public theorem cofiniteEff_individualisticEff : IndividualisticEff cofiniteEff := by
  refine ⟨cofiniteEff_playable, ?_⟩
  have huniv : (Set.univ : Set Unit) = ({()} : Set Unit) := by
    ext i; simp [Unit.ext]
  rw [huniv]
  exact (Set.iUnion_const _).symm

/--
**Pauly's Theorem 3.3 is false at print's own quantifier**, and by the witness
that refutes Theorem 3.2 rather than by a new one.

`cofiniteEff` is playable and its grand coalition's power is the union of the
individuals' — there is one individual — so it is individualistic in print's
sense. It is the effectivity function of no game form at all, so *a fortiori* of
no dictatorship, whatever a dictatorship is taken to be.

Stated without the word *dictatorship* on purpose: the refutation does not
depend on how print's right-hand side is read, because the witness is outside
the range of `effectivity` altogether. The dictatorship form is the corollary
below.
-/
public theorem not_forall_individualisticEff_exists_gameForm :
    ¬ ∀ E : Set Unit → Set (Set ℕ), IndividualisticEff E →
        ∃ G : GameForm.{0, 0, w} Unit ℕ, effectivity G = E := by
  intro h
  exact not_exists_gameForm_cofiniteEff (h cofiniteEff cofiniteEff_individualisticEff)

/-- **Theorem 3.3's left-to-right half, refuted as print states it.** An
individualistic effectivity function need not be the effectivity function of a
dictatorship, because it need not be the effectivity function of anything. -/
public theorem not_forall_individualisticEff_exists_dictator :
    ¬ ∀ E : Set Unit → Set (Set ℕ), IndividualisticEff E →
        ∃ (G : GameForm.{0, 0, w} Unit ℕ) (d : Unit),
          IsDictator G d ∧ effectivity G = E := by
  intro h
  obtain ⟨G, _, _, hGE⟩ := h cofiniteEff cofiniteEff_individualisticEff
  exact not_exists_gameForm_cofiniteEff ⟨G, hGE⟩

/-! ## Part 1: the strategies of page 153

> Now we can define the strategic game `G = (N, {Σ_i | i ∈ N}, o, S)` as follows:
> let `H = {h : P(S)\{∅} → S | h(X) ∈ X}`. Then we define `Σ_i = F_i × N × H` and
> `o(σ_N) = h_{i₀}(G(f))`, where `σ_N = (f_i, t_i, h_i)_{i∈N}` is a strategy
> profile and `i₀ = ((t_1 + ⋯ + t_n) mod n) + 1`

with, earlier on the same page,

> for `i ∈ N`, let `C_i = {C ⊆ N | i ∈ C}` be the set of coalitions of which `i`
> is a member. Let `F_i = {f_i : C_i → P(S) | ∀C : f_i(C) ∈ E(C)}`
-/

section Construction

variable {N : Type u} {X : Type v} {E : Set N → Set (Set X)}

/-- **Print's `F_i`.** A choice of a forceable set for every coalition the player
belongs to. Its domain is print's `C_i`, so a player names nothing about
coalitions it is not in. -/
@[expose] public def ChoiceFn (E : Set N → Set (Set X)) (i : N) : Type (max u v) :=
  {f : {C : Set N // i ∈ C} → Set X // ∀ C, f C ∈ E C.1}

/-- **Print's `H`.** A uniform way of picking an element out of any non-empty set. -/
@[expose] public def Picker (X : Type v) : Type v :=
  {h : {A : Set X // A.Nonempty} → X // ∀ A, h A ∈ A.1}

/-- **Print's `Σ_i = F_i × N × H`.** -/
@[expose] public def Strat (E : Set N → Set (Set X)) (i : N) : Type (max u v) :=
  ChoiceFn E i × N × Picker X

/-- Print's own note that `F_i` is inhabited: *"since for all coalitions `C`,
`S ∈ E(C)`, `F_i` will be non-empty for every player `i`"*. Condition (2) is what
lets a player name *something* everywhere, and it recurs wherever that is needed:
the empty family in `biInter_mem`, the coalitions a player is not in
(`Playable.fullChoice_mem`), and the coalitions that do not contain `C`
(`choiceFnForce`). -/
public theorem Playable.nonempty_choiceFn (hE : Playable E) (i : N) : Nonempty (ChoiceFn E i) :=
  ⟨⟨fun _ => Set.univ, fun C => hE.safe C.1⟩⟩

/-- `H` is inhabited by choice. -/
public instance : Nonempty (Picker X) :=
  ⟨⟨fun A => A.2.choose, fun A => A.2.choose_spec⟩⟩

/-- The constant choice function, which names the whole outcome space everywhere.
Print uses it for the complement coalition in the second inclusion: *"for all
`C' ⊇ C̄` and for all `i ∈ C̄` we have `f_i(C') = S`"*. -/
@[expose] public def choiceFnUniv (hE : Playable E) (i : N) : ChoiceFn E i :=
  ⟨fun _ => Set.univ, fun C => hE.safe C.1⟩

/-- A picker that returns a named element at one named set. Print's *"now we
define `h_{j₀}(G(f)) = s_0`"*. -/
public noncomputable def pickerAt (Y : Set X) (y : X) (hy : y ∈ Y) : Picker X := by
  classical
  refine ⟨fun A => if A.1 = Y then y else (Classical.arbitrary (Picker X)).1 A, fun A => ?_⟩
  show (if A.1 = Y then y else (Classical.arbitrary (Picker X)).1 A) ∈ A.1
  by_cases h : A.1 = Y
  · rw [if_pos h]; exact h ▸ hy
  · rw [if_neg h]; exact (Classical.arbitrary (Picker X)).2 A

@[simp] public theorem pickerAt_self {Y : Set X} {y : X} (hy : y ∈ Y) (hY : Y.Nonempty) :
    (pickerAt Y y hy).1 ⟨Y, hY⟩ = y := by
  simp [pickerAt]

/-! ### The profile's choice functions, read at every coalition

`refineStep` in `Playability` takes a total `f : N → Set N → Set X`. A player's
own `f_i` is defined only on the coalitions containing it, so it is extended by
the whole outcome space elsewhere. Nothing reads the extension: the refinement
evaluates `f i` only at `blockUnder P i`, which contains `i` by reflexivity.
-/

/-- The profile's choice functions as a total function, so `refineSeq` can run on
them. -/
@[expose] public noncomputable def fullChoice (σ : ∀ i, Strat E i) (i : N) (C : Set N) : Set X :=
  letI : Decidable (i ∈ C) := Classical.propDecidable _
  if h : i ∈ C then (σ i).1.1 ⟨C, h⟩ else Set.univ

public theorem fullChoice_of_mem (σ : ∀ i, Strat E i) {i : N} {C : Set N} (h : i ∈ C) :
    fullChoice σ i C = (σ i).1.1 ⟨C, h⟩ := by
  simp only [fullChoice]
  rw [dif_pos h]

/-- Every value of `fullChoice` is forceable by the coalition it is indexed at:
inside `C_i` because `F_i` says so, outside it because of condition (2). -/
public theorem Playable.fullChoice_mem (hE : Playable E) (σ : ∀ i, Strat E i) (i : N)
    (C : Set N) : fullChoice σ i C ∈ E C := by
  by_cases h : i ∈ C
  · rw [fullChoice_of_mem σ h]; exact (σ i).1.2 ⟨C, h⟩
  · simp only [fullChoice]; rw [dif_neg h]; exact hE.safe C

/-- Only the `f`-component of a profile is read by the partition. -/
public theorem fullChoice_congr {σ τ : ∀ i, Strat E i} (h : ∀ i, (σ i).1 = (τ i).1) :
    fullChoice σ = fullChoice τ := by
  funext i C
  simp only [fullChoice, h i]

/-! ### Print's `P_∞(f)` and `G(f)` at a profile -/

/-- Print's `P_∞(f)`, at the profile's choice functions. -/
@[expose] public noncomputable def partitionOf [Finite N] (σ : ∀ i, Strat E i) :
    BlockChoice N X :=
  BlockChoice.ofChoiceFunctions (fullChoice σ)

/-- Print's `G(f) = ⋂_{l=1}^{k} f(C_l)`. -/
@[expose] public noncomputable def outcomeSet [Finite N] (σ : ∀ i, Strat E i) : Set X :=
  ⋂ b, (partitionOf σ).blockChoice b

/-- The block of a class is the block of any of its members. -/
public theorem BlockChoice.blockOf_mk (B : BlockChoice N X) (i : N) :
    B.blockOf (@Quotient.mk _ B.rel i) = blockUnder B.rel i := by
  ext j
  constructor
  · intro hj; exact B.rel.symm (Quotient.exact hj)
  · intro hj; exact Quotient.sound (B.rel.symm hj)

/-- **Each block is effective for what it commits to**, which is the hypothesis
page 153's Claim runs superadditivity on. -/
public theorem Playable.blockChoice_mem [Finite N] (hE : Playable E) (σ : ∀ i, Strat E i)
    (b : Quotient (partitionOf σ).rel) :
    (partitionOf σ).blockChoice b ∈ E ((partitionOf σ).blockOf b) := by
  induction b using Quotient.inductionOn with
  | _ i =>
      rw [BlockChoice.blockChoice_mk, BlockChoice.blockOf_mk]
      exact hE.fullChoice_mem σ i _

/-- **Print's Claim, on `E` rather than on a game.** The blocks are disjoint and
cover the players, so superadditivity over the whole partition puts `G(f)` in
`E(N)`. -/
public theorem Playable.outcomeSet_mem_univ [Fintype N] (hE : Playable E)
    (σ : ∀ i, Strat E i) : outcomeSet σ ∈ E (Set.univ : Set N) := by
  classical
  have : Fintype (Quotient (partitionOf σ).rel) := Fintype.ofFinite _
  have h := hE.iInter_mem (partitionOf σ).blockOf (partitionOf σ).blockChoice
    (fun _ _ hbc => (partitionOf σ).blockOf_disjoint hbc) (fun b => hE.blockChoice_mem σ b)
  rwa [(partitionOf σ).iUnion_blockOf] at h

/-- > Claim: `G(f) ≠ ∅`. Proof: ... hence since `∅ ∉ E(N)`, `G(f)` cannot be empty. -/
public theorem Playable.outcomeSet_nonempty [Fintype N] (hE : Playable E)
    (σ : ∀ i, Strat E i) : (outcomeSet σ).Nonempty := by
  rcases Set.eq_empty_or_nonempty (outcomeSet σ) with h | h
  · exact absurd (h ▸ hE.outcomeSet_mem_univ σ) (hE.live _)
  · exact h

/-! ### The dictator, chosen by summing the indices

> The player who chooses which state in this set will be realized is then
> determined by adding up (modulo `n`) all the indices chosen as `t_i`.

Print writes `i₀ = ((t_1 + ⋯ + t_n) mod n) + 1` because its player set is
`{1, …, n}`. `mod n` and the `+1` are exactly the bookkeeping that makes
`{1, …, n}` into `ZMod n`, so at an abstract finite player type the sum is taken
in `ZMod (card N)` under a chosen enumeration. Which enumeration is irrelevant:
the only property the proof reads is `exists_dictator_eq` below.
-/

/-- An enumeration of the players as `ZMod n`, `n` their number. -/
public noncomputable def playerIndex (N : Type u) [Fintype N] [Nonempty N] :
    N ≃ ZMod (Fintype.card N) :=
  haveI : NeZero (Fintype.card N) := ⟨Fintype.card_ne_zero⟩
  Fintype.equivOfCardEq (by rw [ZMod.card])

/-- **Print's `i₀`.** -/
@[expose] public noncomputable def dictator [Fintype N] [Nonempty N] (t : N → N) : N :=
  (playerIndex N).symm (∑ i, playerIndex N (t i))

/--
**No proper subcoalition controls who picks.**

> Then choose a `t_{j₀}` such that `((t_1 + ⋯ + t_n) mod n) + 1 = j₀`.

One player can move the sum to anything, so any player outside a coalition can
make itself the one that picks, whatever the coalition chose. This is the only
property of the index arithmetic the construction uses.
-/
public theorem exists_dictator_eq [Fintype N] [Nonempty N] (j : N) (t : N → N) :
    ∃ t' : N → N, (∀ i, i ≠ j → t' i = t i) ∧ dictator t' = j := by
  classical
  have : NeZero (Fintype.card N) := ⟨Fintype.card_ne_zero⟩
  set e := playerIndex N with he
  set r := ∑ i ∈ Finset.univ.erase j, e (t i) with hr
  refine ⟨fun i => if i = j then e.symm (e j - r) else t i, fun i hi => by simp [hi], ?_⟩
  have hrest : ∑ i ∈ Finset.univ.erase j, e (if i = j then e.symm (e j - r) else t i) = r := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [if_neg (Finset.ne_of_mem_erase hi)]
  have hsum : ∑ i, e (if i = j then e.symm (e j - r) else t i) = e j := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j), if_pos rfl, Equiv.apply_symm_apply,
      hrest, sub_add_cancel]
  simp only [dictator, ← he, hsum, Equiv.symm_apply_apply]

/-! ### The game

Everything print's `o(σ_N) = h_{i₀}(G(f))` needs is now in place.
-/

/-- **Print's `G`.** The strategies are the triples, and the outcome is the
dictator's pick out of `G(f)`. -/
@[expose] public noncomputable def paulyGame [Fintype N] [Nonempty N] (hE : Playable E) :
    GameForm.{u, v, max u v} N X where
  strategy := Strat E
  outcome σ := ((σ (dictator fun i => (σ i).2.1)).2.2).1
    ⟨outcomeSet σ, hE.outcomeSet_nonempty σ⟩

public theorem paulyGame_outcome [Fintype N] [Nonempty N] (hE : Playable E)
    (σ : ∀ i, Strat E i) :
    (paulyGame hE).outcome σ =
      ((σ (dictator fun i => (σ i).2.1)).2.2).1 ⟨outcomeSet σ, hE.outcomeSet_nonempty σ⟩ :=
  rfl

/-- The outcome always lies in `G(f)`, because a picker picks inside its set. -/
public theorem paulyGame_outcome_mem [Fintype N] [Nonempty N] (hE : Playable E)
    (σ : ∀ i, Strat E i) : (paulyGame hE).outcome σ ∈ outcomeSet σ := by
  rw [paulyGame_outcome hE σ]
  exact ((σ (dictator fun i => (σ i).2.1)).2.2).2 ⟨outcomeSet σ, hE.outcomeSet_nonempty σ⟩

end Construction

/-! ## Part 4: the two inclusions

> It remains to show that for all `C ⊆ N`, `E(C) = E_G(C)`.

Both inclusions are proved, each with the side condition print's argument
actually needs. Neither side condition can be dropped **at print's hypotheses**:
`not_exists_gameForm_cofiniteEff` above rules out *any* construction that would
close both ends from playability alone, so in particular this one. Under strictly
stronger hypotheses they do close --
`AISafetyAtlas.Sovereignty.IsEffectivityFunction.effectivity_paulyGame` runs this
same game at every coalition once Peleg's `E(∅) = {A}` and `E(N) = 2^A ∖ {∅}` are
assumed, which is exactly what `cofiniteEff` violates.
-/

section Inclusions

variable {N : Type u} {X : Type v} {E : Set N → Set (Set X)}

/-- The set a member of `C` names at `C'`: print's `X` when `C' ⊇ C`, and the
whole space otherwise. Written as a union rather than a case split, so no
decidability of `C ⊆ C'` is needed anywhere downstream. -/
@[expose] public def forceOutside (C : Set N) (A : Set X) (C' : Set N) : Set X :=
  {x | x ∈ A ∨ ¬ C ⊆ C'}

public theorem forceOutside_of_subset {C C' : Set N} {A : Set X} (h : C ⊆ C') :
    forceOutside C A C' = A := by
  ext x; simp [forceOutside, h]

public theorem forceOutside_of_not_subset {C C' : Set N} {A : Set X} (h : ¬ C ⊆ C') :
    forceOutside C A C' = Set.univ := by
  ext x; simp [forceOutside, h]

/--
**Print's `C`-strategy for the first inclusion.**

> Choose any `C`-strategy `σ_C = (f_i, t_i, h_i)_{i∈C}` such that for all `i ∈ C`
> and for all `C' ⊇ C` we have `f_i(C') = X`. By coalition-monotonicity, such
> `f_i` exist.

Coalition-monotonicity is Lemma 3.1, so this is where the first inclusion spends
it. Off `C' ⊇ C` the value is the whole space, which condition (2) allows.
-/
@[expose] public def choiceFnForce (hE : Playable E) {C : Set N} {A : Set X}
    (hA : A ∈ E C) (i : N) : ChoiceFn E i :=
  ⟨fun C' => forceOutside C A C'.1, fun C' => by
    show forceOutside C A C'.1 ∈ E C'.1
    by_cases h : C ⊆ C'.1
    · rw [forceOutside_of_subset h]; exact hE.mono_coalition h hA
    · rw [forceOutside_of_not_subset h]; exact hE.safe _⟩

/--
**`E(C) ⊆ E_G(C)`, for a non-empty coalition.**

> To see this, note that `C` must be a subset of one of the partitions `C_l` in
> `P_∞(f)`. Hence `o(σ_N) = o(σ_C, σ_C̄) = h_{i₀}(G(f)) ∈ G(f) ⊆ f(C_l) = X`.

`C.Nonempty` is print's missing hypothesis, and it is not an artefact of this
formalization. `f(C_l) = X` is read off the members of `C_l` that lie in `C`; the
empty coalition has none, and `not_exists_gameForm_cofiniteEff` shows the missing
case is false rather than merely unproved.
-/
public theorem Playable.mem_effectivity_paulyGame_of_mem [Fintype N] [Nonempty N]
    (hE : Playable E) {C : Set N} (hC : C.Nonempty) {A : Set X} (hA : A ∈ E C) :
    A ∈ effectivity (paulyGame hE) C := by
  classical
  refine ⟨fun i => (choiceFnForce hE hA i, Classical.arbitrary N,
    Classical.arbitrary (Picker X)), fun σ hσ => ?_⟩
  have key : ∀ k ∈ C, ∀ D : Set N, k ∈ D → C ⊆ D → fullChoice σ k D = A := by
    intro k hk D hD hCD
    rw [fullChoice_of_mem σ hD, hσ ⟨k, hk⟩]
    exact forceOutside_of_subset hCD
  have hagree : ∀ D : Set N, C ⊆ D → ∀ i ∈ C, ∀ j ∈ C,
      fullChoice σ i D = fullChoice σ j D := by
    intro D hCD i hi j hj
    rw [key i hi D (hCD hi) hCD, key j hj D (hCD hj) hCD]
  obtain ⟨b, hb⟩ := BlockChoice.unsplit_ofChoiceFunctions (fullChoice σ) hC hagree
  obtain ⟨i, hi⟩ := hC
  have hmk : @Quotient.mk _ (partitionOf σ).rel i = b := hb hi
  have hCblock : C ⊆ blockUnder (partitionOf σ).rel i := by
    rw [← BlockChoice.blockOf_mk, hmk]; exact hb
  have hblock : (partitionOf σ).blockChoice b = A := by
    rw [← hmk, BlockChoice.blockChoice_mk]
    exact key i hi _ ((partitionOf σ).rel.refl i) hCblock
  have hmem := paulyGame_outcome_mem hE σ
  rw [← hblock]
  exact Set.mem_iInter.mp hmem b

/-- The profile that plays a coalition's strategy inside it and something else
outside: print's `(σ_C, σ_C̄)`. -/
@[expose] public noncomputable def splice (C : Set N) (sC : ∀ i : C, Strat E i)
    (τ : ∀ i, Strat E i) (i : N) : Strat E i :=
  letI : Decidable (i ∈ C) := Classical.propDecidable _
  if h : i ∈ C then sC ⟨i, h⟩ else τ i

public theorem splice_of_mem (C : Set N) (sC : ∀ i : C, Strat E i) (τ : ∀ i, Strat E i)
    {i : N} (h : i ∈ C) : splice C sC τ i = sC ⟨i, h⟩ := by
  simp only [splice]; rw [dif_pos h]

public theorem splice_of_not_mem (C : Set N) (sC : ∀ i : C, Strat E i) (τ : ∀ i, Strat E i)
    {i : N} (h : i ∉ C) : splice C sC τ i = τ i := by
  simp only [splice]; rw [dif_neg h]

/--
**`E_G(C) ⊆ E(C)`, for a coalition that is not everybody.**

> So assume from now on that `C ≠ N`, and let `j₀ ∈ N \ C`. Let `σ_C` be any
> strategy for coalition `C`. We must show that there is a strategy `σ_C̄` such
> that `o(σ_C, σ_C̄) ∉ X`.

Print's construction, transcribed. The complement names the whole space
everywhere, so it is never split and its block commits to `S`; the remaining
blocks lie inside `C`, so superadditivity puts `G(f)` in `E(C₀)` for some
`C₀ ⊆ C` and coalition-monotonicity moves it to `E(C)`. Then `X ∉ E(C)` leaves a
point of `G(f)` outside `X`, `h_{j₀}` is set to pick it, and `t_{j₀}` is set to
make `j₀` the one who picks.

`C ≠ Set.univ` is print's own hypothesis for this case. Print's `C = N` case is
the one that appeals to the first inclusion at the empty coalition, and is not
reproduced here because it is unsound; `not_exists_gameForm_cofiniteEff` shows no
repair of the construction recovers it.
-/
public theorem Playable.mem_of_mem_effectivity_paulyGame [Fintype N] [Nonempty N]
    (hE : Playable E) {C : Set N} (hC : C ≠ Set.univ) {A : Set X}
    (hA : A ∈ effectivity (paulyGame hE) C) : A ∈ E C := by
  classical
  by_contra hAC
  obtain ⟨sC0, hsC0⟩ := hA
  obtain ⟨sC, hsC⟩ : ∃ sC : ∀ i : C, Strat E i,
      ∀ s : ∀ i, Strat E i, (∀ i : C, s i = sC i) → (paulyGame hE).outcome s ∈ A :=
    ⟨fun i => sC0 i, fun s hs => hsC0 s hs⟩
  obtain ⟨j, hj⟩ : ∃ j : N, j ∉ C := by
    by_contra h
    exact hC (Set.eq_univ_of_forall (by simpa using h))
  -- the profile whose `f`-components are already fixed: `σ_C` on `C`, `S` off it
  obtain ⟨τ₀, hτ₀⟩ : ∃ τ₀ : ∀ i, Strat E i, ∀ i, τ₀ i =
      (choiceFnUniv hE i, Classical.arbitrary N, Classical.arbitrary (Picker X)) :=
    ⟨fun i => (choiceFnUniv hE i, Classical.arbitrary N, Classical.arbitrary (Picker X)),
      fun _ => rfl⟩
  obtain ⟨base, hbase⟩ : ∃ base : ∀ i, Strat E i, base = splice C sC τ₀ := ⟨_, rfl⟩
  have hbase_in : ∀ i (h : i ∈ C), base i = sC ⟨i, h⟩ := by
    intro i h; rw [hbase, splice_of_mem _ _ _ h]
  have hbase_notin : ∀ i, i ∉ C → base i = τ₀ i := by
    intro i h; rw [hbase, splice_of_not_mem _ _ _ h]
  have hbase_out : ∀ k, k ∉ C → ∀ D : Set N, fullChoice base k D = Set.univ := by
    intro k hk D
    by_cases hD : k ∈ D
    · rw [fullChoice_of_mem base hD, hbase_notin k hk, hτ₀ k]
      rfl
    · simp only [fullChoice]; rw [dif_neg hD]
  -- the complement is never split, and its block commits to the whole space
  obtain ⟨b₀, hb₀⟩ := BlockChoice.unsplit_ofChoiceFunctions (fullChoice base)
    ⟨j, hj⟩ (fun D _ i hi k hk => by rw [hbase_out i hi D, hbase_out k hk D])
  have hmk : @Quotient.mk _ (partitionOf base).rel j = b₀ := hb₀ hj
  have hb₀univ : (partitionOf base).blockChoice b₀ = Set.univ := by
    rw [← hmk, BlockChoice.blockChoice_mk]
    exact hbase_out j hj _
  -- so `G(f)` is the intersection over the remaining blocks, all of which sit in `C`
  have hYeq : outcomeSet base = ⋂ b : {b : Quotient (partitionOf base).rel // b ≠ b₀},
      (partitionOf base).blockChoice b.1 := by
    apply Set.Subset.antisymm
    · exact fun x hx => Set.mem_iInter.mpr fun b => Set.mem_iInter.mp hx b.1
    · intro x hx
      refine Set.mem_iInter.mpr fun b => ?_
      by_cases hbb : b = b₀
      · rw [hbb, hb₀univ]; trivial
      · exact Set.mem_iInter.mp hx ⟨b, hbb⟩
  have hcov : (⋃ b : {b : Quotient (partitionOf base).rel // b ≠ b₀},
      (partitionOf base).blockOf b.1) ⊆ C := by
    intro k hk
    obtain ⟨b, hkb⟩ := Set.mem_iUnion.mp hk
    by_contra hkC
    exact b.2 (((hb₀ hkC).symm.trans hkb).symm)
  have hfin : Fintype (Quotient (partitionOf base).rel) := Fintype.ofFinite _
  have hYC : outcomeSet base ∈ E C := by
    have h := hE.iInter_mem
      (fun b : {b : Quotient (partitionOf base).rel // b ≠ b₀} => (partitionOf base).blockOf b.1)
      (fun b => (partitionOf base).blockChoice b.1)
      (fun b c hbc => (partitionOf base).blockOf_disjoint fun hEq => hbc (Subtype.ext hEq))
      (fun b => hE.blockChoice_mem base b.1)
    rw [← hYeq] at h
    exact hE.mono_coalition hcov h
  -- `X ∉ E(C)` and `G(f) ∈ E(C)` leave a point of `G(f)` outside `X`
  obtain ⟨s₀, hs₀Y, hs₀A⟩ : ∃ x, x ∈ outcomeSet base ∧ x ∉ A := by
    by_contra h
    exact hAC (hE.mono C _ A (fun x hx => by
      by_contra hxA; exact h ⟨x, hx, hxA⟩) hYC)
  -- and `j` can make itself the one who picks
  obtain ⟨t, ht, htdict⟩ := exists_dictator_eq j (fun i => (base i).2.1)
  obtain ⟨τ₁, hτ₁⟩ : ∃ τ₁ : ∀ i, Strat E i, ∀ i, τ₁ i =
      (choiceFnUniv hE i, t i, pickerAt (outcomeSet base) s₀ hs₀Y) :=
    ⟨fun i => (choiceFnUniv hE i, t i, pickerAt (outcomeSet base) s₀ hs₀Y), fun _ => rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ : ∀ i, Strat E i, σ = splice C sC τ₁ := ⟨_, rfl⟩
  have hσ_in : ∀ i (h : i ∈ C), σ i = sC ⟨i, h⟩ := by
    intro i h; rw [hσ, splice_of_mem _ _ _ h]
  have hσ_notin : ∀ i, i ∉ C → σ i = τ₁ i := by
    intro i h; rw [hσ, splice_of_not_mem _ _ _ h]
  have hfst : ∀ i, (σ i).1 = (base i).1 := by
    intro i
    by_cases h : i ∈ C
    · rw [hσ_in i h, hbase_in i h]
    · rw [hσ_notin i h, hbase_notin i h, hτ₀ i, hτ₁ i]
  have hset : outcomeSet σ = outcomeSet base := by
    unfold outcomeSet partitionOf
    rw [fullChoice_congr hfst]
  have hsnd : (fun i => (σ i).2.1) = t := by
    funext i
    by_cases h : i ∈ C
    · have hij : i ≠ j := fun hEq => hj (hEq ▸ h)
      rw [hσ_in i h, ht i hij, hbase_in i h]
    · rw [hσ_notin i h, hτ₁ i]
  have hagreeC : ∀ i : C, σ i = sC i := fun i => hσ_in i i.2
  have hσj : (σ j).2.2 = pickerAt (outcomeSet base) s₀ hs₀Y := by
    rw [hσ_notin j hj, hτ₁ j]
  have hdict : dictator (fun i => (σ i).2.1) = j := by rw [hsnd, htdict]
  have hout : (paulyGame hE).outcome σ = s₀ := by
    rw [paulyGame_outcome hE σ, hdict, hσj,
      show (⟨outcomeSet σ, hE.outcomeSet_nonempty σ⟩ : {A : Set X // A.Nonempty})
        = ⟨outcomeSet base, hset ▸ hE.outcomeSet_nonempty σ⟩ from Subtype.ext hset]
    exact pickerAt_self hs₀Y _
  exact hs₀A (hout ▸ hsC σ hagreeC)

/--
**Where the equality does hold.** Everything except the two ends of the coalition
lattice.
-/
public theorem Playable.effectivity_paulyGame_eq [Fintype N] [Nonempty N]
    (hE : Playable E) {C : Set N} (hne : C.Nonempty) (huniv : C ≠ Set.univ) :
    effectivity (paulyGame hE) C = E C :=
  Set.Subset.antisymm (fun _ hX => hE.mem_of_mem_effectivity_paulyGame huniv hX)
    (fun _ hX => hE.mem_effectivity_paulyGame_of_mem hne hX)

end Inclusions

end AISafetyAtlas.Sovereignty
