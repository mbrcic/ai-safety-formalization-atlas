module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Composite goals, and the disjuncts that win immediately

The goal formalism MAIS-A2 states `prob:rate`, `prob:noisy` and
`prob:corruption` over, following Richens–Abel–Bellot–Everitt. This module is
the **syntax and the trajectory semantics** only: no environment, no policy, no
probability. Those are what MAIS-O33 needs next, and they are not here.

## What print writes

A **sub-goal** is `α = (op, 𝐠)` with `𝐠 ⊆ 𝐒 × 𝐀` and
`op ∈ {⊤, ○, ◇}` (*Now*, *Next*, *Eventually*), with an achievement time on a
trajectory: `0` for *Now* if `(s₀,a₀) ∈ 𝐠`, `1` for *Next* if `(s₁,a₁) ∈ 𝐠`,
the least `t` with `(s_t,a_t) ∈ 𝐠` for *Eventually*, and undefined otherwise.
A **sequential goal** `⟨α₁,…,α_k⟩` is satisfied when `α₁` has a finite
achievement time `T` and the trajectory shifted past `T` satisfies
`⟨α₂,…,α_k⟩`; its **depth** is `k`. A **composite goal** is a finite disjunction
of sequential goals, *"identified semantically with its set of disjuncts …; its
depth is the maximum over disjuncts"*.

That last clause is not decoration. `𝚿_n` is the set of **finite sets** of
sequential goals of depth at most `n`, so there are `2^Q - 1` of them where `Q`
counts the sequential goals — not `Q^n`, which is what a reading that bounded
the number of disjuncts would give. Every counting argument over the goal space
turns on which of the two it is.

## Why the achievement time is a predicate here

`IsAchievementTime α τ T` says `T` **is** the achievement time, minimality
included, rather than *"`α` is achieved at some point"*. Print says the
achievement time *is* the least such `t`, and the shift in the recursive clause
is taken past that one time; a weaker existential clause would let a sequential
goal be satisfied along a shift print does not take.

## The immediate-win disjuncts

`compositeSatisfies_of_now_disjunct` is the fact every counting argument over
this space rests on: a composite goal carrying a depth-one *Now* disjunct
`⟨(⊤, 𝐠)⟩` with `(s, a) ∈ 𝐠` is achieved with certainty by playing `a` at `s`,
**in every environment**, because a *Now* condition reads `(s₀, a₀)` and never a
transition probability. `card_compositeGoals_avoiding` counts how
many composite goals escape that, and `exceptional_ratio_lt` bounds the
fraction: `2^{1-R}`, doubly exponentially small in the state count.
-/

namespace AISafetyAtlas.Causal

/-! ## Syntax -/

/-- Print's three temporal operators, `⊤`, `○` and `◇`. -/
public inductive TemporalOp
  | /-- `⊤`: hit the set at time `0`. -/ now
  | /-- `○`: hit the set at time `1`. -/ next
  | /-- `◇`: hit the set at some time. -/ eventually
  deriving DecidableEq, Repr

public instance : Fintype TemporalOp :=
  ⟨{TemporalOp.now, TemporalOp.next, TemporalOp.eventually}, by intro x; cases x <;> decide⟩

@[simp] public theorem card_temporalOp : Fintype.card TemporalOp = 3 := rfl

/-- A sub-goal: an operator and the state–action set it demands be hit. -/
public structure SubGoal (S A : Type*) where
  /-- Which of print's three operators. -/
  op : TemporalOp
  /-- `𝐠 ⊆ 𝐒 × 𝐀`. -/
  target : Finset (S × A)

variable {S A : Type*}

public instance [DecidableEq S] [DecidableEq A] : DecidableEq (SubGoal S A) := fun a b ↦
  decidable_of_iff (a.op = b.op ∧ a.target = b.target) <| by
    cases a; cases b; simp [SubGoal.mk.injEq]

/-- A sequential goal `⟨α₁,…,α_k⟩`. Its depth is its length. -/
public abbrev SequentialGoal (S A : Type*) := List (SubGoal S A)

/-- A composite goal, **identified with its set of disjuncts** — which is print's
own convention, and the reason `𝚿_n` is exponential in the number of sequential
goals rather than polynomial. -/
public abbrev CompositeGoal (S A : Type*) := Finset (SequentialGoal S A)

/-- Print's depth of a sequential goal. -/
@[expose] public def SequentialGoal.depth (ψ : SequentialGoal S A) : ℕ := ψ.length

/-! ## Trajectory semantics

A trajectory is read as the sequence of its state–action pairs, which is all any
sub-goal inspects. -/

/-- `T` **is** the achievement time of `α` on `τ`: print's value, minimality
included, and `False` at every `T` when print leaves it undefined. -/
@[expose] public def IsAchievementTime (α : SubGoal S A) (τ : ℕ → S × A) (T : ℕ) : Prop :=
  match α.op with
  | .now => T = 0 ∧ τ 0 ∈ α.target
  | .next => T = 1 ∧ τ 1 ∈ α.target
  | .eventually => τ T ∈ α.target ∧ ∀ t < T, τ t ∉ α.target

/-- The achievement time is unique when it exists, so the shift the recursive
clause takes is well defined. -/
public theorem IsAchievementTime.unique {α : SubGoal S A} {τ : ℕ → S × A} {T T' : ℕ}
    (h : IsAchievementTime α τ T) (h' : IsAchievementTime α τ T') : T = T' := by
  unfold IsAchievementTime at h h'
  cases hop : α.op <;> rw [hop] at h h'
  · exact h.1.trans h'.1.symm
  · exact h.1.trans h'.1.symm
  · rcases lt_trichotomy T T' with hlt | heq | hgt
    · exact absurd h.1 (h'.2 T hlt)
    · exact heq
    · exact absurd h'.1 (h.2 T' hgt)

/-- Print's recursive satisfaction: the head's achievement time, then the tail on
the trajectory shifted past it. -/
@[expose] public def Satisfies : SequentialGoal S A → (ℕ → S × A) → Prop
  | [], _ => True
  | α :: rest, τ => ∃ T, IsAchievementTime α τ T ∧ Satisfies rest fun t ↦ τ (T + 1 + t)

/-- A composite goal is satisfied when one of its disjuncts is. -/
@[expose] public def CompositeSatisfies (Ψ : CompositeGoal S A) (τ : ℕ → S × A) : Prop :=
  ∃ ψ ∈ Ψ, Satisfies ψ τ

/-! ## The immediate-win disjuncts -/

/-- The depth-one *Now* goal demanding `𝐠` at time zero. -/
@[expose] public def nowGoal (g : Finset (S × A)) : SequentialGoal S A :=
  [{ op := .now, target := g }]

public theorem nowGoal_injective : Function.Injective (nowGoal (S := S) (A := A)) := by
  intro g g' h
  simpa [nowGoal, SubGoal.mk.injEq] using h

@[simp] public theorem satisfies_nowGoal_iff (g : Finset (S × A)) (τ : ℕ → S × A) :
    Satisfies (nowGoal g) τ ↔ τ 0 ∈ g := by
  constructor
  · rintro ⟨T, hT, -⟩
    exact hT.2
  · intro h
    exact ⟨0, ⟨rfl, h⟩, trivial⟩

/-- **The fact the whole counting argument rests on.** A composite goal carrying
a depth-one *Now* disjunct that the first state–action pair meets is achieved
outright, and nothing about the environment enters: a *Now* condition reads
`(s₀, a₀)` and never a transition probability, so the same first action is
optimal at that pair in **every** environment on the same `(𝐒, 𝐀)`. -/
public theorem compositeSatisfies_of_now_disjunct {Ψ : CompositeGoal S A}
    {g : Finset (S × A)} (hmem : nowGoal g ∈ Ψ) {τ : ℕ → S × A} (hτ : τ 0 ∈ g) :
    CompositeSatisfies Ψ τ :=
  ⟨nowGoal g, hmem, (satisfies_nowGoal_iff g τ).mpr hτ⟩

/-! ## The goal space at bounded depth

`𝚿_n` is where the counting happens, and its size is what the *"identified with
its set of disjuncts"* convention decides. -/

section Space

variable [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

public instance : Fintype (SubGoal S A) :=
  Fintype.ofEquiv (TemporalOp × Finset (S × A))
    { toFun := fun p ↦ ⟨p.1, p.2⟩
      invFun := fun α ↦ (α.op, α.target)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

omit [DecidableEq S] [DecidableEq A] in
public theorem card_subGoal :
    Fintype.card (SubGoal S A) = 3 * 2 ^ (Fintype.card S * Fintype.card A) := by
  rw [Fintype.card_congr (Equiv.mk (fun α : SubGoal S A ↦ (α.op, α.target))
    (fun p ↦ ⟨p.1, p.2⟩) (fun _ ↦ rfl) (fun _ ↦ rfl)), Fintype.card_prod,
    card_temporalOp, Fintype.card_finset, Fintype.card_prod]

/-- The sequential goals of a given depth. -/
@[expose] public def goalsOfLength : ℕ → Finset (SequentialGoal S A)
  | 0 => {[]}
  | k + 1 => ((Finset.univ : Finset (SubGoal S A)) ×ˢ goalsOfLength k).image fun p ↦ p.1 :: p.2

@[simp] public theorem mem_goalsOfLength {ψ : SequentialGoal S A} {k : ℕ} :
    ψ ∈ goalsOfLength k ↔ ψ.length = k := by
  induction k generalizing ψ with
  | zero => simp [goalsOfLength, List.length_eq_zero_iff]
  | succ k ih =>
    simp only [goalsOfLength, Finset.mem_image, Finset.mem_product, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨α, t⟩, ht, rfl⟩
      simp [ih.mp ht]
    · intro hlen
      cases ψ with
      | nil => simp at hlen
      | cons α t => exact ⟨(α, t), ih.mpr (by simpa using hlen), rfl⟩

public theorem card_goalsOfLength (k : ℕ) :
    (goalsOfLength (S := S) (A := A) k).card = Fintype.card (SubGoal S A) ^ k := by
  induction k with
  | zero => simp [goalsOfLength]
  | succ k ih =>
    rw [goalsOfLength, Finset.card_image_of_injective _ ?_, Finset.card_product,
      Finset.card_univ, ih, pow_succ, mul_comm]
    rintro ⟨α, t⟩ ⟨α', t'⟩ h
    simpa [Prod.ext_iff] using h

/-- The sequential goals of depth at most `n`. Print's depth is `k ≥ 1`, so the
empty list is not one of them. -/
@[expose] public def boundedGoals (n : ℕ) : Finset (SequentialGoal S A) :=
  (Finset.range n).biUnion fun k ↦ goalsOfLength (k + 1)

@[simp] public theorem mem_boundedGoals {ψ : SequentialGoal S A} {n : ℕ} :
    ψ ∈ boundedGoals n ↔ 1 ≤ ψ.depth ∧ ψ.depth ≤ n := by
  simp only [boundedGoals, Finset.mem_biUnion, Finset.mem_range, mem_goalsOfLength,
    SequentialGoal.depth]
  constructor
  · rintro ⟨k, hk, hlen⟩
    omega
  · rintro ⟨h1, h2⟩
    exact ⟨ψ.length - 1, by omega, by omega⟩

/-- **`𝚿_n`**: the composite goals of depth at most `n`, as finite **sets** of
disjuncts — print's convention, and the whole of what makes the space
exponential.

The **empty** disjunction is excluded, and print settles it: a composite goal's
*"depth is the maximum over disjuncts"*, which the empty set has not, so the
empty disjunction has no depth and cannot lie in `𝚿_n` for any `n`. The
ordinary reading of *"a finite disjunction of sequential goals"* agrees.

The counting does not depend on the argument: `exceptional_ratio_lt_with_empty`
proves the bound survives the other reading too, where `𝚿_n` has `2^Q` elements
and the exceptional fraction is `2^{-R}` rather than `2^{1-R}` — on one
hypothesis fewer. What *would* depend on it is the corruption budget of
`Causal.Corruption`, which is `η·|𝐒 × 𝚿_n|`: the two readings differ by `|𝐒|`
arguments, and neither budget dominates the other. That is why the exclusion is
settled by print's depth clause here rather than left as a choice. -/
@[expose] public def compositeGoals (n : ℕ) : Finset (CompositeGoal S A) :=
  (boundedGoals n).powerset.filter fun Ψ ↦ Ψ.Nonempty

/-- `|𝚿_n| = 2^Q - 1`. Not `Q^n`: the exponent is where the set-of-disjuncts
convention shows up, and every counting bound over the goal space depends on
it. -/
public theorem card_compositeGoals (n : ℕ) :
    (compositeGoals (S := S) (A := A) n).card = 2 ^ (boundedGoals (S := S) (A := A) n).card - 1 := by
  classical
  have hsplit : (boundedGoals (S := S) (A := A) n).powerset
      = insert (∅ : CompositeGoal S A) (compositeGoals n) := by
    ext Ψ
    simp only [compositeGoals, Finset.mem_insert, Finset.mem_filter, Finset.mem_powerset]
    rcases Finset.eq_empty_or_nonempty Ψ with rfl | hne
    · simp
    · simp [hne, hne.ne_empty]
  have hnotmem : (∅ : CompositeGoal S A) ∉ compositeGoals n := by
    simp [compositeGoals]
  have := congrArg Finset.card hsplit
  rw [Finset.card_powerset, Finset.card_insert_of_notMem hnotmem] at this
  omega

/-! ## Immediate wins -/

/-- The depth-one *Now* goals a fixed state–action pair already achieves. -/
@[expose] public def immediateWins (s : S) (a : A) : Finset (SequentialGoal S A) :=
  ((Finset.univ : Finset (S × A)).powerset.filter fun g ↦ (s, a) ∈ g).image nowGoal

public theorem immediateWins_subset_boundedGoals {n : ℕ} (hn : 1 ≤ n) (s : S) (a : A) :
    immediateWins (S := S) (A := A) s a ⊆ boundedGoals n := by
  intro ψ hψ
  simp only [immediateWins, Finset.mem_image] at hψ
  obtain ⟨g, -, rfl⟩ := hψ
  simp [nowGoal, SequentialGoal.depth, hn]

/-- Every immediate win is achieved by that pair, whatever the environment. -/
public theorem compositeSatisfies_of_immediateWin {Ψ : CompositeGoal S A} {s : S} {a : A}
    {ψ : SequentialGoal S A} (hψ : ψ ∈ immediateWins s a) (hmem : ψ ∈ Ψ)
    {τ : ℕ → S × A} (hτ : τ 0 = (s, a)) : CompositeSatisfies Ψ τ := by
  simp only [immediateWins, Finset.mem_image, Finset.mem_filter] at hψ
  obtain ⟨g, ⟨-, hsa⟩, rfl⟩ := hψ
  exact compositeSatisfies_of_now_disjunct hmem (by rw [hτ]; exact hsa)

/-- `R = 2^{|𝐒||𝐀| - 1}`: a subset containing one fixed pair is a subset of the
rest. -/
public theorem card_immediateWins (s : S) (a : A) :
    (immediateWins (S := S) (A := A) s a).card = 2 ^ (Fintype.card S * Fintype.card A - 1) := by
  classical
  rw [immediateWins, Finset.card_image_of_injective _ nowGoal_injective]
  have hset : ((Finset.univ : Finset (S × A)).powerset.filter fun g ↦ (s, a) ∈ g)
      = ((Finset.univ.erase (s, a)).powerset).image (insert (s, a)) := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image, Finset.subset_univ,
      true_and]
    constructor
    · intro hg
      exact ⟨g.erase (s, a), by
        intro x hx
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hx).1, Finset.mem_univ x⟩,
        Finset.insert_erase hg⟩
    · rintro ⟨t, ht, rfl⟩
      exact Finset.mem_insert_self _ _
  rw [hset, Finset.card_image_of_injOn, Finset.card_powerset, Finset.card_erase_of_mem
    (Finset.mem_univ _), Finset.card_univ, Fintype.card_prod]
  intro t ht t' ht' heq
  simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff, Finset.coe_subset]
    at ht ht'
  have hnt : (s, a) ∉ t := fun h ↦ (Finset.mem_erase.mp (ht h)).1 rfl
  have hnt' : (s, a) ∉ t' := fun h ↦ (Finset.mem_erase.mp (ht' h)).1 rfl
  rw [← Finset.erase_insert hnt, ← Finset.erase_insert hnt', heq]

/-! ## The counting bound -/

/-- Subsets of `G` disjoint from `I` are exactly the subsets of `G \ I`. -/
public theorem powerset_filter_disjoint {α : Type*} [DecidableEq α] (G I : Finset α) :
    G.powerset.filter (fun T ↦ Disjoint T I) = (G \ I).powerset := by
  ext T
  simp [Finset.mem_powerset, Finset.subset_sdiff]

/-- **Lemma 2's count.** The composite goals of depth at most `n` carrying no
immediate win for `(s, a)` number `2^{Q-R} - 1`. -/
public theorem card_compositeGoals_avoiding {n : ℕ} (hn : 1 ≤ n) (s : S) (a : A) :
    ((compositeGoals (S := S) (A := A) n).filter
        fun Ψ ↦ Disjoint Ψ (immediateWins s a)).card
      = 2 ^ ((boundedGoals (S := S) (A := A) n).card
          - (immediateWins (S := S) (A := A) s a).card) - 1 := by
  classical
  have hIG : immediateWins (S := S) (A := A) s a ⊆ boundedGoals n :=
    immediateWins_subset_boundedGoals hn s a
  have hempty : Disjoint (∅ : CompositeGoal S A) (immediateWins (S := S) (A := A) s a) :=
    Finset.disjoint_left.mpr fun x hx ↦ absurd hx (Finset.notMem_empty x)
  have hsplit : (boundedGoals (S := S) (A := A) n \ immediateWins s a).powerset
      = insert (∅ : CompositeGoal S A)
          ((compositeGoals n).filter fun Ψ ↦ Disjoint Ψ (immediateWins s a)) := by
    ext Ψ
    simp only [Finset.mem_powerset, Finset.subset_sdiff, Finset.mem_insert, Finset.mem_filter,
      compositeGoals]
    constructor
    · rintro ⟨hsub, hdisj⟩
      rcases Finset.eq_empty_or_nonempty Ψ with rfl | hne
      · exact Or.inl rfl
      · exact Or.inr ⟨⟨hsub, hne⟩, hdisj⟩
    · rintro (rfl | ⟨⟨hsub, -⟩, hdisj⟩)
      · exact ⟨Finset.empty_subset _, hempty⟩
      · exact ⟨hsub, hdisj⟩
  have hnotmem : (∅ : CompositeGoal S A)
      ∉ (compositeGoals (S := S) (A := A) n).filter
          fun Ψ ↦ Disjoint Ψ (immediateWins s a) := by
    simp [compositeGoals]
  have hcard := congrArg Finset.card hsplit
  rw [Finset.card_powerset, Finset.card_insert_of_notMem hnotmem] at hcard
  have hsd : (boundedGoals (S := S) (A := A) n \ immediateWins s a).card
      = (boundedGoals (S := S) (A := A) n).card
        - (immediateWins (S := S) (A := A) s a).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hIG]
  rw [hsd] at hcard
  omega

/-- **The exceptional fraction is below `2^{1-R}`.** With `|𝐀| = 2` and
`|𝐒| = m` this is `2^{1 - 2^{2m-1}}`: doubly exponentially small, which is why
one construction serves every corruption fraction at once. -/
public theorem exceptional_ratio_lt {Q R : ℕ} (hR : 1 ≤ R) (hRQ : R ≤ Q) :
    ((2 ^ (Q - R) - 1 : ℕ) : ℝ) / ((2 ^ Q - 1 : ℕ) : ℝ) < 2 / 2 ^ R := by
  have hQ : 1 ≤ Q := le_trans hR hRQ
  have h1 : (1 : ℕ) ≤ 2 ^ (Q - R) := Nat.one_le_two_pow
  have h2 : (1 : ℕ) ≤ 2 ^ Q := Nat.one_le_two_pow
  have hnum : ((2 ^ (Q - R) - 1 : ℕ) : ℝ) = (2 : ℝ) ^ (Q - R) - 1 := by
    rw [Nat.cast_sub h1]
    push_cast
    ring
  have hden : ((2 ^ Q - 1 : ℕ) : ℝ) = (2 : ℝ) ^ Q - 1 := by
    rw [Nat.cast_sub h2]
    push_cast
    ring
  have hRge : (2 : ℝ) ≤ 2 ^ R := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ R := pow_le_pow_right₀ (by norm_num) hR
  have hQge : (2 : ℝ) ≤ 2 ^ Q := by
    calc (2 : ℝ) = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ Q := pow_le_pow_right₀ (by norm_num) hQ
  have hdenpos : (0 : ℝ) < (2 : ℝ) ^ Q - 1 := by linarith
  have hRpos : (0 : ℝ) < (2 : ℝ) ^ R := by positivity
  have hsplit : (2 : ℝ) ^ (Q - R) * 2 ^ R = 2 ^ Q := by
    rw [← pow_add]
    congr 1
    omega
  rw [hnum, hden, div_lt_div_iff₀ hdenpos hRpos]
  have hexp : ((2 : ℝ) ^ (Q - R) - 1) * 2 ^ R = 2 ^ Q - 2 ^ R := by
    rw [sub_mul, one_mul, hsplit]
  rw [hexp]
  linarith

/-- **The counting bound is insensitive to the empty disjunction.** Under the
reading that admits it, `𝚿_n` has `2^Q` elements and the goals carrying no
immediate win number `2^{Q-R}`; the fraction is then `2^{-R}`, still below the
`2^{1-R}` bound — and on one hypothesis fewer than `exceptional_ratio_lt`, since
no immediate win need exist for `2^{-R}` to be small. So the choice made by
`compositeGoals` changes the count and not the conclusion. -/
public theorem exceptional_ratio_lt_with_empty {Q R : ℕ} (hRQ : R ≤ Q) :
    ((2 ^ (Q - R) : ℕ) : ℝ) / ((2 ^ Q : ℕ) : ℝ) < 2 / 2 ^ R := by
  have hQpos : (0 : ℝ) < 2 ^ Q := by positivity
  have hRpos : (0 : ℝ) < 2 ^ R := by positivity
  have hsplit : (2 : ℝ) ^ (Q - R) * 2 ^ R = 2 ^ Q := by
    rw [← pow_add]
    congr 1
    omega
  push_cast
  rw [div_lt_div_iff₀ hQpos hRpos]
  nlinarith [hsplit, hQpos]

end Space

end AISafetyAtlas.Causal
