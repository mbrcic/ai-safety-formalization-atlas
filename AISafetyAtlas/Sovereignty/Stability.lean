module

public import AISafetyAtlas.Sovereignty.Separations
public import Mathlib.Data.List.Chain
public import Mathlib.Order.Extension.Well

/-!
# Keiding's cycle, stated against this repository's effectivity families

Keiding (*Necessary and sufficient conditions for stability of effectivity
functions*, International Journal of Game Theory 14(2):93-101, 1985) proves that
an effectivity function is **stable exactly when it is acyclic**: Theorem 3.6
(p. 97) says a cycle makes it unstable, Theorem 3.8 (same page) says acyclicity
makes it stable.

What makes that worth stating here and not merely citing: Keiding's object is
`E : P(N) → P²(A)`, which **is** the type of `AISafetyAtlas.Sovereignty.effectivity`
— `Set N → Set (Set X)` — so the condition transcribes with no new substrate at
all. And the condition itself mentions **only `E`**. No preference, no utility,
no ordering appears anywhere in Definition 3.3. A purely combinatorial property
of a power distribution decides whether that distribution can be blocked from
every direction at once.

| Layer | Name | What it fixes |
|---|---|---|
| **Model** | `Cycle` | Definition 3.3 (p. 96), transcribed |
| **Model** | `Acyclic` | "there are no cycles in `E`" |
| **Bridge** | `GameFormAcyclic`, `gameFormAcyclic_iff` | The same condition read at a game form's own effectivity |

## What is here and what is deliberately not

**Theorem 3.6 is proved** (2026-09-16): a cycle makes `E` unstable. Print's
construction is followed step for step — `Dᵢ`, the relation `P̄ⁱ`, Lemma 3.7's
extension, and the preference read through blocks — and `not_stable_of_cycle` is
the result, with `acyclic_of_stable` its contrapositive. There is no separate
game-form form of either: `gameFormAcyclic_iff` is `Iff.rfl`, so `Acyclic
(effectivity G)` and `GameFormAcyclic G` are the same proposition and a consumer
holding a game form applies the general theorem directly.

**Theorem 3.8 is not.** Its proof runs the other way: from an empty core it
builds a cycle, choosing the `Cᵢ` inside the sets that dominate and closing them
up. That construction is not transcribed here.

**The layer this module used to say was missing is not the profiles.** An earlier
version of this header said the two theorems were blocked because the repository
has no preference-profile type; that was false. `SocialChoice.Profile` is
`Fin N → Preorder' A`, carried for Arrow, and it is Keiding's `K(A)^N`. What was
missing was the **core**, `C(A, E, R^N)` — `Sovereignty.Domination` blocks a
*demand* and mentions no preference, and `nonmonotonicCore` (in `TrulyPlayable`) is a
different object. It is defined above.

**Finiteness is cheaper than recorded, too.** Lemma 3.7 wants a finite set, and
Theorem 3.6 applies it to `Dᵢ ⊆ {1, …, k}` — `Fin c.len` here, finite for free.
Nothing above assumes `X` finite, where print's `A` is.

**The transcription is faithful in one respect worth naming.** Definition 3.3
(ii)'s chain condition quantifies over sequences `i₁, …, i_r` of indices; it is
rendered with `List.IsChain`, which is exactly "adjacent pairs are related", and
the sequence is kept nonempty structurally by splitting it as a head and a
tail rather than by carrying a proof that it is not empty.

`Remark 3.4` (p. 96) says the "or" in (ii) is **not exclusive**; `Or` is not
exclusive, so nothing is needed for that.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

/-!
## Definition 3.3

An effectivity function in Keiding's sense is any `E : Set N → Set (Set X)`.
This module takes it as a parameter rather than as a structure, because the one
instance that matters — `effectivity G` — is already a function of that type.
-/

/--
**A cycle in `E`** — Keiding, Definition 3.3, p. 96.

A family `(S₁, …, S_k; B₁, …, B_k)` with `Bᵢ ∈ E(Sᵢ)`, together with blocks
`C₁, …, C_k` partitioning the outcome space, such that each block misses its own
`B`, and no chain of blocks closes up unless the coalitions along it have empty
intersection.

`len` is Keiding's `k` and is positive: a family indexed by nothing is not a
family. `block` is his `C`.
-/
public structure Cycle {N : Type u} {X : Type v} (E : Set N → Set (Set X)) where
  /-- Keiding's `k`. -/
  len : ℕ
  /-- The family is not empty. -/
  pos : 0 < len
  /-- The coalitions `S₁, …, S_k`. -/
  S : Fin len → Set N
  /-- Print writes `Sᵢ ∈ 2^N` and defines `2^D = P(D) \ {∅}` (p. 94), so the
  coalitions of a cycle are **non-empty**. Recorded 2026-09-16: the first
  transcription dropped it, which made `Cycle` wider than Definition 3.3 and
  `Theorem 3.6` false, since the empty coalition dominates nothing. -/
  Snonempty : ∀ i, (S i).Nonempty
  /-- The sets `B₁, …, B_k` they are effective for. -/
  B : Fin len → Set X
  /-- `Bᵢ ∈ E(Sᵢ)`. -/
  effective : ∀ i, B i ∈ E (S i)
  /-- Keiding's `C₁, …, C_k`. -/
  block : Fin len → Set X
  /-- 3.3(i), first half: the blocks are pairwise disjoint. -/
  blockDisjoint : ∀ i j, i ≠ j → block i ∩ block j = ∅
  /-- 3.3(i), second half: the blocks cover the outcome space. -/
  blockCovers : (⋃ i, block i) = Set.univ
  /-- 3.3(ii), first half: `Cᵢ ∩ Bᵢ = ∅`. -/
  blockAvoids : ∀ i, block i ∩ B i = ∅
  /--
  3.3(ii), second half. Along any chain of indices whose consecutive blocks and
  `B`s meet, either the coalitions have empty intersection or the chain does not
  close up.

  The sequence is `i₁ :: rest`, so it is nonempty by construction; `getLast` is
  Keiding's `i_r` and the head is his `i₁`.
  -/
  chainCondition : ∀ (i₁ : Fin len) (rest : List (Fin len)),
    (i₁ :: rest).IsChain (fun a b => (block a ∩ B b).Nonempty) →
    (⋂ i ∈ (i₁ :: rest), S i) = ∅ ∨
      block ((i₁ :: rest).getLast (by simp)) ∩ B i₁ = ∅

/--
**Acyclicity** — Keiding, Definition 3.3, final sentence, p. 96: *"The
effectivity function `E : P(N) → P²(A)` is said to be acyclic if there are no
cycles in `E`."*
-/
@[expose] public def Acyclic {N : Type u} {X : Type v} (E : Set N → Set (Set X)) : Prop :=
  IsEmpty (Cycle E)

/-- Unfolding: acyclicity is exactly the refutation of every candidate cycle. -/
public theorem acyclic_iff {N : Type u} {X : Type v} (E : Set N → Set (Set X)) :
    Acyclic E ↔ (Cycle E → False) :=
  ⟨fun h c => h.elim c, fun h => ⟨h⟩⟩

/-- A cycle is exactly what refutes acyclicity. -/
public theorem not_acyclic_of_cycle {N : Type u} {X : Type v} {E : Set N → Set (Set X)}
    (c : Cycle E) : ¬ Acyclic E := fun h => h.elim c

/-!
## The bridge to game forms

Keiding's `E : P(N) → P²(A)` and this repository's `effectivity G : Set N →
Set (Set X)` are the same type, so the condition applies to a game form's own
power distribution with nothing in between.
-/

/-- **Keiding's condition, read at a game form.** -/
@[expose] public def GameFormAcyclic {N : Type u} {X : Type v}
    (G : GameForm.{u, v, w} N X) : Prop :=
  Acyclic (effectivity G)

/-- The bridge is definitional: there is no translation step to get wrong. -/
public theorem gameFormAcyclic_iff {N : Type u} {X : Type v}
    (G : GameForm.{u, v, w} N X) :
    GameFormAcyclic G ↔ Acyclic (effectivity G) :=
  Iff.rfl

/--
**A cycle at a game form refutes its acyclicity**, and by Theorem 3.6 its power
distribution is then unstable — apply `not_stable_of_cycle` to the same cycle,
once each `Bᵢ` is known non-empty.
-/
public theorem not_gameFormAcyclic_of_cycle {N : Type u} {X : Type v}
    {G : GameForm.{u, v, w} N X} (c : Cycle (effectivity G)) :
    ¬ GameFormAcyclic G :=
  not_acyclic_of_cycle c

/-!
## Two easy facts about the definition

Neither is Keiding's; both keep the transcription honest.
-/

/-- **An effectivity function that is effective for nothing is acyclic.** The
cheapest inhabitant of `Acyclic`, recorded so the predicate is known to be
satisfiable rather than assumed to be. -/
public theorem acyclic_bot {N : Type u} {X : Type v} :
    Acyclic (fun _ : Set N => (∅ : Set (Set X))) :=
  ⟨fun c => (c.effective ⟨0, c.pos⟩).elim⟩

/-- **A cycle's blocks never contain a point of their own `B`.** The content of
3.3(ii)'s first half, in the form a consumer uses it. -/
public theorem Cycle.not_mem_block_of_mem_B {N : Type u} {X : Type v}
    {E : Set N → Set (Set X)} (c : Cycle E) (i : Fin c.len) {x : X}
    (hx : x ∈ c.B i) : x ∉ c.block i := by
  intro hb
  have : x ∈ c.block i ∩ c.B i := ⟨hb, hx⟩
  rw [c.blockAvoids i] at this
  exact this

/-- **Consecutive indices along a chain are distinct.** Immediate from
3.3(ii)'s first half, and the reason a chain of length at least two visits more
than one coalition. -/
public theorem Cycle.ne_of_block_inter_B_nonempty {N : Type u} {X : Type v}
    {E : Set N → Set (Set X)} (c : Cycle E) {a b : Fin c.len}
    (h : (c.block a ∩ c.B b).Nonempty) : a ≠ b := by
  rintro rfl
  obtain ⟨x, hx⟩ := h
  exact c.not_mem_block_of_mem_B a hx.2 hx.1

/-!
## The core — Keiding, Definitions 2.1 to 2.3, p. 94

These are the objects Theorems 3.6 and 3.8 quantify over, read from the rendered
page rather than inferred from the theorems that use them.

Print's `K(A)` is the **weak orders**: *"a total and transitive binary relation
on `A`"*, with `xPy` iff `xRy` and not `yRx`. It is not `Preorder` — no
antisymmetry — and totality already gives reflexivity.

`AISafetyAtlas.SocialChoice.Profile` is the same object at `Type`, carried for
Arrow, but `Upstream.Arrow.Preorder'` is fixed at universe zero and this tree
takes `X : Type v`, so the weak order is restated here rather than imported. That
is the only reason; the two agree wherever both typecheck.

**Coalitions are non-empty.** Print writes `2^D = P(D) \ {∅}`, so `S ∈ 2^N` in
Definitions 2.2 and 3.3 means a non-empty coalition, and `B ∈ 2^A` means a
non-empty set of alternatives. Definition 2.2 also requires `x ∈ A \ B`. All
three are carried below; without them the empty coalition and the empty set
dominate everything and the core is empty for trivial reasons.
-/

/-- **A weak order** — Keiding p. 94: total and transitive. -/
public structure WeakOrder (X : Type v) where
  /-- The weak preference relation. -/
  le : X → X → Prop
  /-- Totality, which also gives reflexivity. -/
  total : ∀ x y, le x y ∨ le y x
  /-- Transitivity. -/
  trans : ∀ x y z, le x y → le y z → le x z

/-- **Strict preference**, print's `xPy`: `xRy` and not `yRx`. -/
@[expose] public def WeakOrder.lt {X : Type v} (R : WeakOrder X) (x y : X) : Prop :=
  R.le x y ∧ ¬ R.le y x

/-- Reflexivity, from totality. -/
public theorem WeakOrder.refl {X : Type v} (R : WeakOrder X) (x : X) : R.le x x :=
  (R.total x x).elim id id

/-- **A preference profile** — print's `K(A)^N`, one weak order per player. -/
public abbrev Profile (N : Type u) (X : Type v) := N → WeakOrder X

/--
**`B` dominates `x` via `S`** — Keiding, Definition 2.2, p. 94.

`S` non-empty and `B` non-empty are print's `S ∈ 2^N` and `B ∈ 2^A`; `x ∉ B` is
its `x ∈ A \ B`. The content is the last clause: every member of the coalition
strictly prefers **every** element of `B` to `x`.
-/
@[expose] public def DominatesVia {N : Type u} {X : Type v}
    (E : Set N → Set (Set X)) (R : Profile N X) (S : Set N) (B : Set X) (x : X) : Prop :=
  S.Nonempty ∧ B.Nonempty ∧ x ∉ B ∧ B ∈ E S ∧ ∀ i ∈ S, ∀ b ∈ B, (R i).lt b x

/-- **`x` is dominated**: some coalition dominates it with some set it can force. -/
@[expose] public def Dominated {N : Type u} {X : Type v}
    (E : Set N → Set (Set X)) (R : Profile N X) (x : X) : Prop :=
  ∃ S B, DominatesVia E R S B x

/-- **The core** `C(A, E, R^N)` — the undominated alternatives. -/
@[expose] public def core {N : Type u} {X : Type v}
    (E : Set N → Set (Set X)) (R : Profile N X) : Set X :=
  {x | ¬ Dominated E R x}

/-- **Stability** — Keiding, Definition 2.3: every profile leaves the core
non-empty. -/
@[expose] public def Stable {N : Type u} {X : Type v} (E : Set N → Set (Set X)) : Prop :=
  ∀ R : Profile N X, (core E R).Nonempty

/-- Membership in the core, unfolded. -/
public theorem mem_core_iff {N : Type u} {X : Type v}
    {E : Set N → Set (Set X)} {R : Profile N X} {x : X} :
    x ∈ core E R ↔ ¬ ∃ S B, DominatesVia E R S B x := Iff.rfl

/-- A dominated alternative is outside the core, which is the direction every
instability argument uses. -/
public theorem not_mem_core_of_dominated {N : Type u} {X : Type v}
    {E : Set N → Set (Set X)} {R : Profile N X} {x : X}
    (h : Dominated E R x) : x ∉ core E R := fun hc => hc h

/-- **Instability from an empty core at one profile.** -/
public theorem not_stable_of_core_eq_empty {N : Type u} {X : Type v}
    {E : Set N → Set (Set X)} {R : Profile N X}
    (h : ∀ x : X, Dominated E R x) : ¬ Stable E := by
  intro hstable
  obtain ⟨x, hx⟩ := hstable R
  exact hx (h x)

/-!
## Lemma 3.7 — Keiding p. 97

*"Let `P̄` be a binary relation on a finite set `D`, and suppose that `P̄` is
acyclic … Then there is `R̂ ∈ K(D)` such that for all `d, d' ∈ D`, `dP̄d' ⇒ dP̂d'`."*

Print proves it by repeatedly extracting a maximal element. Mathlib reaches the
same conclusion in three steps — the transitive closure of an acyclic relation on
a finite type is irreflexive and transitive, hence well-founded, and a
well-founded relation extends to a well order — so the extension is assembled
rather than reconstructed.

**The finiteness is on the index set, not on the outcomes.** Print states the
lemma on a finite `D` and Theorem 3.6 applies it to `Dᵢ ⊆ {1, …, k}`, which is
`Fin c.len` here and finite for free. Nothing below asks `X` to be finite.
-/

/-- **Lemma 3.7**, as a well order extending an acyclic relation. -/
public theorem exists_wellOrder_ge_of_acyclic {D : Type*} [Finite D] {r : D → D → Prop}
    (hacyc : ∀ d, ¬ Relation.TransGen r d d) :
    ∃ s : D → D → Prop, IsWellOrder D s ∧ ∀ a b, r a b → s a b := by
  have : IsTrans D (Relation.TransGen r) := ⟨fun _ _ _ => Relation.TransGen.trans⟩
  have : Std.Irrefl (Relation.TransGen r) := ⟨hacyc⟩
  have : IsWellFounded D (Relation.TransGen r) :=
    ⟨Finite.wellFounded_of_trans_of_irrefl _⟩
  obtain ⟨s, hle, hws⟩ := IsWellFounded.exists_well_order_ge (Relation.TransGen r)
  exact ⟨s, hws, fun a b hab => hle a b (Relation.TransGen.single hab)⟩

/-!
## Which block an outcome is in

3.3(i) makes the blocks a partition, so every outcome has exactly one. Theorem
3.6 needs the map, and needs it total, which is what covering buys.
-/

/-- Every outcome lies in a block — 3.3(i), second half. -/
public theorem Cycle.exists_block {N : Type u} {X : Type v}
    {E : Set N → Set (Set X)} (c : Cycle E) (x : X) : ∃ i, x ∈ c.block i := by
  have : x ∈ (⋃ i, c.block i) := by rw [c.blockCovers]; trivial
  simpa using this

/-- **The block containing an outcome.** -/
public noncomputable def Cycle.idx {N : Type u} {X : Type v}
    {E : Set N → Set (Set X)} (c : Cycle E) (x : X) : Fin c.len :=
  (c.exists_block x).choose

/-- `idx` names a block the outcome is actually in. -/
public theorem Cycle.mem_block_idx {N : Type u} {X : Type v}
    {E : Set N → Set (Set X)} (c : Cycle E) (x : X) : x ∈ c.block (c.idx x) :=
  (c.exists_block x).choose_spec

/-- And it is the only one — 3.3(i), first half. -/
public theorem Cycle.idx_eq_of_mem {N : Type u} {X : Type v}
    {E : Set N → Set (Set X)} (c : Cycle E) {x : X} {i : Fin c.len}
    (hx : x ∈ c.block i) : c.idx x = i := by
  by_contra hne
  have : x ∈ c.block (c.idx x) ∩ c.block i := ⟨c.mem_block_idx x, hx⟩
  rw [c.blockDisjoint _ _ hne] at this
  exact this

/-!
## Theorem 3.6 — Keiding p. 97: a cycle makes `E` unstable

Print's construction, followed step for step. For a player `p`, `Dᵢ` is the set
of indices whose coalition contains it; `P̄ⁱ` relates `h` to `j` when `C_h`
meets `B_j`; 3.3(ii) makes `P̄ⁱ` acyclic because the intersection of the
coalitions along any chain contains `p` and is therefore non-empty, so the other
disjunct must hold; Lemma 3.7 extends it to an ordering; and the player's
preference over outcomes is that ordering read through the block an outcome lies
in, with the blocks outside `Dᵢ` placed on top.

Two hypotheses of print's are carried explicitly rather than assumed of `E`.
`Cycle.Snonempty` is Definition 3.3's `Sᵢ ∈ 2^N`. `hB` is non-emptiness of each
`Bᵢ`, which print gets from Definition 2.1(i) — `∅ ∉ E(S)` — a condition this
module does not impose on `E`, since it takes `E` as an arbitrary function.

**`X` is not assumed finite**, where print's `A` is. The finiteness Lemma 3.7
needs lands on the index set `Fin c.len`, which is finite for free.
-/

/-- **Theorem 3.6.** If there is a cycle in `E`, then `E` is unstable. -/
public theorem not_stable_of_cycle {N : Type u} {X : Type v} {E : Set N → Set (Set X)}
    (c : Cycle E) (hB : ∀ i, (c.B i).Nonempty) : ¬ Stable E := by
  classical
  have key : ∀ p : N, ∃ Rp : WeakOrder X, ∀ h : Fin c.len, p ∈ c.S h →
      ∀ x ∈ c.B h, ∀ y ∈ c.block h, Rp.lt x y := by
    intro p
    set inD : Fin c.len → Prop := fun j => p ∈ c.S j with hinD
    set r : Fin c.len → Fin c.len → Prop :=
      fun a b => inD a ∧ inD b ∧ (c.block a ∩ c.B b).Nonempty with hr
    have hacyc : ∀ d, ¬ Relation.TransGen r d d := by
      intro d hd
      obtain ⟨e, hde, hed⟩ := Relation.TransGen.tail'_iff.mp hd
      obtain ⟨l, hchain, hlast⟩ := List.exists_isChain_cons_of_relationReflTransGen hde
      have htail : ∀ (a : Fin c.len) (m : List (Fin c.len)),
          (a :: m).IsChain r → ∀ i ∈ m, inD i := by
        intro a m
        induction m generalizing a with
        | nil => intro _ i hi; simp at hi
        | cons b w ih =>
          intro hch i hi
          rcases List.mem_cons.mp hi with rfl | hi
          · exact (List.isChain_cons_cons.mp hch).1.2.1
          · exact ih b (List.isChain_cons_cons.mp hch).2 i hi
      have hmem : ∀ i ∈ (d :: l), inD i := by
        intro i hi
        rcases List.mem_cons.mp hi with rfl | hi
        · exact hed.2.1
        · exact htail d l hchain i hi
      have hsub : (d :: l).IsChain (fun a b => (c.block a ∩ c.B b).Nonempty) := by
        refine hchain.imp ?_
        intro a b hab
        exact hab.2.2
      rcases c.chainCondition d l hsub with hcap | hclose
      · have : p ∈ ⋂ i ∈ (d :: l), c.S i := by
          simp only [Set.mem_iInter]
          intro i hi
          exact hmem i hi
        rw [hcap] at this
        exact this
      · rw [hlast] at hclose
        obtain ⟨z, hz⟩ := hed.2.2
        have : z ∈ c.block e ∩ c.B d := hz
        rw [hclose] at this
        exact this
    obtain ⟨s, hws, hge⟩ := exists_wellOrder_ge_of_acyclic hacyc
    have _inst : IsWellOrder (Fin c.len) s := hws
    have htri : ∀ a b, s a b ∨ a = b ∨ s b a := fun a b => trichotomous_of s a b
    have htrans : ∀ {a b d}, s a b → s b d → s a d := fun hab hbd => trans_of s hab hbd
    have hirr : ∀ a, ¬ s a a := fun a => irrefl_of s a
    have hasym : ∀ a b, s a b → ¬ s b a := fun a b hab hba => hirr a (htrans hab hba)
    set better : Fin c.len → Fin c.len → Prop :=
      fun a b => (¬ inD a ∧ inD b) ∨ (inD a ∧ inD b ∧ s a b) with hbetter
    have hbasym : ∀ a b, better a b → ¬ better b a := by
      rintro a b (⟨hna, hb⟩ | ⟨ha, hb, hab⟩) (⟨hnb, ha'⟩ | ⟨hb', ha', hba⟩)
      · exact hnb hb
      · exact hna ha'
      · exact hnb hb
      · exact hasym _ _ hab hba
    have hbneg : ∀ a b d, better d a → better d b ∨ better b a := by
      rintro a b d (⟨hnd, ha⟩ | ⟨hd, ha, hda⟩)
      · by_cases hb : inD b
        · exact Or.inl (Or.inl ⟨hnd, hb⟩)
        · exact Or.inr (Or.inl ⟨hb, ha⟩)
      · by_cases hb : inD b
        · rcases htri d b with hdb | rfl | hbd
          · exact Or.inl (Or.inr ⟨hd, hb, hdb⟩)
          · exact Or.inr (Or.inr ⟨hb, ha, hda⟩)
          · exact Or.inr (Or.inr ⟨hb, ha, htrans hbd hda⟩)
        · exact Or.inr (Or.inl ⟨hb, ha⟩)
    refine ⟨{ le := fun x y => ¬ better (c.idx y) (c.idx x)
              total := ?_
              trans := ?_ }, ?_⟩
    · intro x y
      by_cases h : better (c.idx y) (c.idx x)
      · exact Or.inr (hbasym _ _ h)
      · exact Or.inl h
    · intro x y z hxy hyz hcontra
      rcases hbneg (c.idx x) (c.idx y) (c.idx z) hcontra with h | h
      · exact hyz h
      · exact hxy h
    · intro h hp x hx y hy
      have hidxy : c.idx y = h := c.idx_eq_of_mem hy
      have hb : better (c.idx x) h := by
        by_cases hj : inD (c.idx x)
        · refine Or.inr ⟨hj, hp, hge _ _ ⟨hj, hp, ⟨x, c.mem_block_idx x, hx⟩⟩⟩
        · exact Or.inl ⟨hj, hp⟩
      rw [← hidxy] at hb
      exact ⟨hbasym _ _ hb, fun hn => hn hb⟩
  choose R hR using key
  refine not_stable_of_core_eq_empty (R := R) ?_
  intro x
  refine ⟨c.S (c.idx x), c.B (c.idx x),
    c.Snonempty _, hB _, ?_, c.effective _, ?_⟩
  · intro hx
    exact c.not_mem_block_of_mem_B _ hx (c.mem_block_idx x)
  · intro q hq b hb
    exact hR q (c.idx x) hq b hb x (c.mem_block_idx x)

/--
**Definition 2.1(i)** — Keiding p. 94: `∅ ∉ E(S)` for every `S`.

The one clause of the effectivity-function definition Theorem 3.6 consumes. This
module takes `E` as an arbitrary function, so the clause is a predicate a
consumer supplies rather than a field it may assume.
-/
@[expose] public def NoEmptySet {N : Type u} {X : Type v} (E : Set N → Set (Set X)) : Prop :=
  ∀ S, (∅ : Set X) ∉ E S

/-- **Theorem 3.6, contrapositive.** A stable effectivity function is acyclic.
This is the direction a consumer holding stability wants, and it needs no
non-emptiness hypothesis of its own: Definition 2.1(i) supplies it. -/
public theorem acyclic_of_stable {N : Type u} {X : Type v} {E : Set N → Set (Set X)}
    (hE : NoEmptySet E) (h : Stable E) : Acyclic E := by
  refine ⟨fun c => ?_⟩
  refine not_stable_of_cycle c (fun i => ?_) h
  rcases Set.eq_empty_or_nonempty (c.B i) with hemp | hne
  · exact absurd (hemp ▸ c.effective i) (hE (c.S i))
  · exact hne

/--
**A sufficient condition for 3.3(ii)'s chain clause.**

If distinct indices carry disjoint coalitions, the chain clause is free. A chain
either visits two indices, and then the intersection along it is already empty,
or it repeats one — which past length one contradicts 3.3(ii)'s first half,
because a chain step from `i` to `i` asks `Cᵢ ∩ Bᵢ` to be non-empty.

This is the shape every small cycle takes, and it is what makes one exhibitable
without discharging a quantifier over lists by hand.
-/
public theorem chainCondition_of_pairwise_disjoint {N : Type u} {X : Type v}
    {len : ℕ} {S : Fin len → Set N} {B block : Fin len → Set X}
    (havoid : ∀ i, block i ∩ B i = ∅)
    (hdisj : ∀ i j, i ≠ j → S i ∩ S j = ∅) :
    ∀ (i₁ : Fin len) (rest : List (Fin len)),
      (i₁ :: rest).IsChain (fun a b => (block a ∩ B b).Nonempty) →
      (⋂ i ∈ (i₁ :: rest), S i) = ∅ ∨
        block ((i₁ :: rest).getLast (by simp)) ∩ B i₁ = ∅ := by
  intro i₁ rest hchain
  by_cases hall : ∀ j ∈ (i₁ :: rest), j = i₁
  · right
    cases rest with
    | nil => simpa using havoid i₁
    | cons a w =>
      exfalso
      have ha : a = i₁ := hall a (by simp)
      subst ha
      obtain ⟨z, hz⟩ := (List.isChain_cons_cons.mp hchain).1
      have : z ∈ block a ∩ B a := hz
      rw [havoid a] at this
      exact this
  · left
    push Not at hall
    obtain ⟨j, hj, hne⟩ := hall
    refine Set.eq_empty_iff_forall_notMem.mpr ?_
    intro q hq
    simp only [Set.mem_iInter] at hq
    have h1 : q ∈ S i₁ := hq i₁ (by simp)
    have h2 : q ∈ S j := hq j hj
    have : q ∈ S j ∩ S i₁ := ⟨h2, h1⟩
    rw [hdisj j i₁ hne] at this
    exact this

/-- **A rank function certifies acyclicity.** Anything a strictly increasing
`ℕ`-valued measure runs along has no cycle, which is the cheapest way to
discharge Lemma 3.7's hypothesis on a concrete relation. -/
public theorem acyclic_of_rank {D : Type*} {r : D → D → Prop} (f : D → ℕ)
    (h : ∀ a b, r a b → f a < f b) : ∀ d, ¬ Relation.TransGen r d d := by
  have hmono : ∀ {a b}, Relation.TransGen r a b → f a < f b := by
    intro a b hab
    induction hab with
    | single hxy => exact h _ _ hxy
    | tail _ hyz ih => exact lt_trans ih (h _ _ hyz)
  exact fun d hd => absurd (hmono hd) (lt_irrefl _)

end AISafetyAtlas.Sovereignty
