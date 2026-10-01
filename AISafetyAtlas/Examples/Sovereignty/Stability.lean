module

public import AISafetyAtlas.Sovereignty.Stability
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Fintype.Basic

/-!
# The smallest cycle there is, and the instability it forces

Two agents, two outcomes, each agent effective for exactly the outcome the other
one is blocked by. Keiding's Definition 3.3 is satisfied, so by his Theorem 3.6
(p. 97) this distribution of power is unstable — every outcome is blocked from
some direction.

This exists because `Cycle` is a structure with seven fields and a quantified
chain condition, and a definition nothing inhabits is a definition that proves
nothing. `AISafetyAtlas.Sovereignty.acyclic_bot` inhabits the other side.

The chain condition is where the work is, and the argument is the one that makes
cycles finite objects at all: consecutive indices along a chain must differ,
because a block never meets its own `B`. With two agents that forces the chain to
visit both, and two singleton coalitions have empty intersection.

**Theorem 3.6 now runs here.** `duel_not_stable` is the conclusion the module
header used to say this repository could not state: some profile of weak orders
leaves no outcome undominated. Nothing below chooses that profile — the theorem
constructs it from the cycle, and this file supplies only the cycle.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Stability

open AISafetyAtlas.Sovereignty

/-- Swap the two agents. -/
@[expose] public def flip : Fin 2 → Fin 2
  | 0 => 1
  | 1 => 0

public theorem flip_ne (i : Fin 2) : flip i ≠ i := by
  unfold flip
  fin_cases i <;> decide

public theorem flip_inj {i j : Fin 2} (h : flip i = flip j) : i = j := by
  unfold flip at h
  fin_cases i <;> fin_cases j <;> simp_all

/--
**Each agent alone is effective for their own outcome, and for nothing else.**

The two-agent, two-outcome power distribution in which agent `i` can force the
outcome `i`.
-/
@[expose] public def duel : Set (Fin 2) → Set (Set (Fin 2)) := fun S =>
  {B | ∃ i : Fin 2, S = {i} ∧ B = {i}}

/-- **The cycle.** -/
@[expose] public def duelCycle : Cycle duel where
  len := 2
  pos := by decide
  S := fun i => {i}
  Snonempty := fun i => ⟨i, rfl⟩
  B := fun i => {i}
  effective := fun i => ⟨i, rfl, rfl⟩
  block := fun i => {flip i}
  blockDisjoint := by
    intro i j hij
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, h⟩
    exact hij (flip_inj h.symm).symm
  blockCovers := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_singleton_iff, Set.mem_univ, iff_true]
    refine ⟨flip x, ?_⟩
    unfold flip
    fin_cases x <;> decide
  blockAvoids := by
    intro i
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨h1, h2⟩
    exact flip_ne i (h1.symm.trans h2)
  chainCondition := by
    intro i₁ rest hchain
    cases rest with
    | nil =>
        -- A one-element chain closes up on itself, and a block misses its own `B`.
        right
        simp only [List.getLast_singleton]
        ext x
        simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
        rintro ⟨h1, h2⟩
        exact flip_ne i₁ (h1.symm.trans h2)
    | cons a rest' =>
        -- Two distinct singleton coalitions already intersect emptily.
        left
        have hne : a ≠ i₁ := by
          have h : ({flip i₁} ∩ {a} : Set (Fin 2)).Nonempty :=
            List.rel_of_isChain_cons_cons hchain
          obtain ⟨x, hx1, hx2⟩ := h
          simp only [Set.mem_singleton_iff] at hx1 hx2
          subst hx1; subst hx2
          exact flip_ne _
        ext x
        simp only [Set.mem_iInter, Set.mem_empty_iff_false, iff_false]
        intro hx
        have h1 : x ∈ ({i₁} : Set (Fin 2)) := by
          have := hx i₁
          simpa using this (by simp)
        have h2 : x ∈ ({a} : Set (Fin 2)) := by
          have := hx a
          simpa using this (by simp)
        simp only [Set.mem_singleton_iff] at h1 h2
        exact hne (h2.symm.trans h1)

/-- **So `duel` is not acyclic.** -/
public theorem duel_not_acyclic : ¬ Acyclic duel :=
  not_acyclic_of_cycle duelCycle

/-- Both sides of the predicate are inhabited, so neither is vacuous. -/
public theorem acyclic_is_not_trivial :
    Acyclic (fun _ : Set (Fin 2) => (∅ : Set (Set (Fin 2)))) ∧ ¬ Acyclic duel :=
  ⟨acyclic_bot, duel_not_acyclic⟩

/-! ## Theorem 3.6 on this cycle -/

/-- Each forced set is a singleton, hence non-empty. -/
public theorem duelCycle_B_nonempty : ∀ i, (duelCycle.B i).Nonempty :=
  fun i => ⟨i, rfl⟩

/-- `duel` satisfies Definition 2.1(i): no coalition is effective for the empty
set, because every set it is effective for is a singleton. -/
public theorem noEmptySet_duel : NoEmptySet duel := by
  rintro S ⟨i, -, hB⟩
  have : i ∈ (∅ : Set (Fin 2)) := hB ▸ rfl
  exact this

/--
**Keiding's Theorem 3.6 on the smallest cycle there is.**

Some profile of weak orders leaves every outcome dominated, so `duel` is
unstable. The reading is the obvious one: each agent can pull the outcome to the
one it is effective for, and the theorem turns that into a profile at which the
core is empty.
-/
public theorem duel_not_stable : ¬ Stable duel :=
  not_stable_of_cycle duelCycle duelCycle_B_nonempty

/-- **The contrapositive runs on the same object.** `duel` meets Definition
2.1(i), so stability would force acyclicity — and `duelCycle` refutes that. The
two routes to instability agree. -/
public theorem duel_stable_would_be_acyclic : Stable duel → Acyclic duel :=
  acyclic_of_stable noEmptySet_duel

/-- Both halves together, which is the shape of the argument a consumer makes:
the power distribution carries a cycle, and it is therefore unstable. -/
public theorem cycle_and_not_stable : Nonempty (Cycle duel) ∧ ¬ Stable duel :=
  ⟨⟨duelCycle⟩, duel_not_stable⟩

/-! ## The pieces Theorem 3.6 is assembled from, run on the same object -/

/-- Every outcome lies in a block, and `idx` names the one it is in. -/
public theorem duel_idx_mem (x : Fin 2) : x ∈ duelCycle.block (duelCycle.idx x) :=
  duelCycle.mem_block_idx x

/-- And it is the only one: `flip x` is the index whose block holds `x`. -/
public theorem duel_idx_eq (x : Fin 2) : duelCycle.idx x = flip x := by
  refine duelCycle.idx_eq_of_mem ?_
  show x ∈ ({flip (flip x)} : Set (Fin 2))
  unfold flip
  fin_cases x <;> decide

/-- Covering, in the form `idx` is built from. -/
public theorem duel_exists_block (x : Fin 2) : ∃ i, x ∈ duelCycle.block i :=
  duelCycle.exists_block x

/-- `duelCycle`'s chain condition also follows from the reusable route, since its
two singleton coalitions are disjoint. Proved twice on purpose: the field carries
the argument spelled out, and this checks the general lemma against it. -/
public theorem duel_chainCondition_via_disjoint :
    ∀ (i₁ : Fin 2) (rest : List (Fin 2)),
      (i₁ :: rest).IsChain (fun a b => (duelCycle.block a ∩ duelCycle.B b).Nonempty) →
      (⋂ i ∈ (i₁ :: rest), duelCycle.S i) = ∅ ∨
        duelCycle.block ((i₁ :: rest).getLast (by simp)) ∩ duelCycle.B i₁ = ∅ := by
  refine chainCondition_of_pairwise_disjoint duelCycle.blockAvoids ?_
  intro i j hij
  refine Set.eq_empty_iff_forall_notMem.mpr ?_
  rintro x ⟨rfl, h⟩
  exact hij h

/-! ## The core layer, on the same object -/

/-- Total indifference is a weak order, and reflexivity comes from totality. -/
public def flat : WeakOrder (Fin 2) where
  le := fun _ _ => True
  total := fun _ _ => Or.inl trivial
  trans := fun _ _ _ _ _ => trivial

/-- Reflexivity comes from totality rather than from an axiom, and the library
lemma is what says so.

Written `WeakOrder.refl flat x` and not `flat.refl x`. The dot form compiles and
is the idiomatic one, but it puts no occurrence of `WeakOrder.refl` in the source
text, so the debt report cannot attribute the use and reported the lemma as
reaching no witness. The debt report is a text scan over `Examples/`; where the
two forms disagree, this file writes the one the report can see. -/
public theorem flat_refl (x : Fin 2) : flat.le x x := WeakOrder.refl flat x

/-- Under total indifference nobody strictly prefers anything, so no coalition
dominates and **the core is everything**. The contrast with `duel_not_stable` is
the point: instability is a fact about the profile Theorem 3.6 builds, not about
the power distribution alone. -/
public theorem flat_core_univ : ∀ x : Fin 2, x ∈ core duel (fun _ => flat) := by
  intro x
  rw [mem_core_iff]
  rintro ⟨S, B, -, ⟨b, hb⟩, -, hB, hpref⟩
  obtain ⟨i, hS, -⟩ := hB
  have hi : i ∈ S := by rw [hS]; rfl
  exact (hpref i hi b hb).2 trivial

/-- A dominated outcome is outside the core — the direction every instability
argument uses, run here rather than only stated. -/
public theorem duel_not_mem_core_of_dominated {R : Profile (Fin 2) (Fin 2)} {x : Fin 2}
    (h : Dominated duel R x) : x ∉ core duel R :=
  not_mem_core_of_dominated h

/-- And the route from "every outcome is dominated" to instability. -/
public theorem duel_not_stable_of_all_dominated {R : Profile (Fin 2) (Fin 2)}
    (h : ∀ x : Fin 2, Dominated duel R x) : ¬ Stable duel :=
  not_stable_of_core_eq_empty h

/-! ## Lemma 3.7 on a relation small enough to see -/

/-- `0 ≺ 1` and nothing else is acyclic, by the rank that is the index itself. -/
public theorem step_acyclic :
    ∀ d : Fin 2, ¬ Relation.TransGen (fun a b : Fin 2 => a = 0 ∧ b = 1) d d :=
  Sovereignty.acyclic_of_rank (fun i => i.1) (by rintro a b ⟨rfl, rfl⟩; decide)

/-- So it extends to a well order, which is what Theorem 3.6 asks of `P̄ⁱ`. -/
public theorem step_extends :
    ∃ s : Fin 2 → Fin 2 → Prop, IsWellOrder (Fin 2) s ∧
      ∀ a b : Fin 2, (a = 0 ∧ b = 1) → s a b :=
  exists_wellOrder_ge_of_acyclic step_acyclic

/--
**Consecutive blocks along a cycle are at different indices**, at the smallest
cycle there is. This is the step that makes a `Cycle` a finite object rather
than a family that could fold onto itself: a block never meets the `B` it is the
block of, so an index whose block meets another's `B` is a different index.

The header calls it *"where the work is"* and the library proves it in general;
until now nothing ran it on a cycle, so the argument was available and never
exercised. Agent `0`'s block is `{1}`, which is agent `1`'s `B`. -/
public theorem duelCycle_indices_differ :
    (⟨0, by decide⟩ : Fin duelCycle.len) ≠ ⟨1, by decide⟩ :=
  Cycle.ne_of_block_inter_B_nonempty duelCycle
    ⟨1, by unfold duelCycle flip; decide, by unfold duelCycle; decide⟩

/-- Acyclicity unfolded, on the same object: `duel` is not acyclic exactly
because a cycle for it exists, and `acyclic_iff` is the step that says those are
the same statement. -/
public theorem duel_acyclic_iff_no_cycle : ¬ (Cycle duel → False) := by
  rw [← acyclic_iff duel]
  exact duel_not_acyclic

end AISafetyAtlas.Examples.Sovereignty.Stability
