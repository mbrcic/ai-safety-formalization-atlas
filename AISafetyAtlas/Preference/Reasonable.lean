module

public import AISafetyAtlas.Preference
public import Mathlib.Algebra.Group.Pi.Basic
public import Mathlib.Order.Lattice.Nat
public import Mathlib.Tactic.Linarith

/-!
# Basic operations and Proposition 7

## Statement intent

- **Objects.** The six basic operations of the source's §5.1.2, and an abstract
  complexity assignment on policies and on planner/reward pairs.
- **Assumptions.** The source's notion of a *`c`-reasonable language* — a
  language in which each basic operation is expressible by a short program — is
  **reparameterized** here. The source bounds the *composite* operations
  `F₁…F₄` and obtains distance `c` from the minimum. This structure instead
  assumes separate evaluation and construction bounds, and concludes `2 * c`.
  That is a valid conditional variation, not the source definition with the same
  constant, and the results below should be read accordingly.
- **Quantifier order.** The constant is fixed by the language, before any policy
  or pair is chosen.
- **Conclusion.** The source's Proposition 7: each of the three degenerate
  planner/reward pairs has complexity within `2 * c` of *every* pair compatible
  with the policy, hence is among the lowest-complexity compatible pairs.
- **Difference from the source.** The source builds complexity from program
  lengths in a language `L` and defines "comparable complexity" via a constant
  `c`; here the language is abstracted away and only the additive bounds it
  supplies are assumed. The bounds are stated with ℕ-valued complexity. The
  concrete plain-Kolmogorov instantiation of the same argument is in
  `AISafetyAtlas.Preference.Complexity`, where `behaviour_le_of_evaluatesTo` is
  `policy_le_of_compatible` with the structure field `op3` replaced by a real
  evaluation map — a planner program run on a reward. Nothing instantiates
  `ReasonableLanguage` itself at plain Kolmogorov complexity; that needs
  policies as bit strings and is not done.

## Explicit non-claims

- **Not** a construction of any particular reasonable language, nor a proof that
  one exists. Existence is the source's informal argument about short programs
  and is assumed here.
- **Not** supported by any nontrivial model. The only exhibited inhabitant of
  `ReasonableLanguage` is
  `AISafetyAtlas.Examples.SixTargets.degenerateLanguage`, in which every
  complexity is zero and `c = 0`. Propositions 7 and 8 hold there but say
  nothing, since all complexities coincide. Whether a *nontrivial* `c`-reasonable
  language exists is exactly the source's informal claim, and nothing in the
  atlas establishes it. Read the propositions as conditional statements about
  any language meeting the bounds, not as evidence that an interesting one
  exists.
- **Not** the source's §4.1 regret results, Proposition 10, or Appendix A.
  §5.2 and Proposition 8 *are* treated, in `proposition_eight` below.
- **Not** the source's own `c`-reasonable-language parameterisation: see the
  reparameterization note above, which is why Proposition 7 here concludes
  `2 * c` rather than `c`. The source's parameterisation, with the composite
  operations `F₁…F₄` and distance `c`, is formalized separately in
  `AISafetyAtlas.Preference.SourceComplexity`. Prefer that module when source
  parity matters.
- **Not** a claim that the *intended* pair is of high complexity, which is the
  second half of the source's informal Theorem 2.

Survey row: **BY-011**. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Preference

variable {S A : Type*}

/-- A planner/reward pair, the object whose complexity the source compares. -/
public abbrev Pair (S A : Type*) : Type _ :=
  Planner (RewardFn S A) (Policy S A) × RewardFn S A

section Operations

variable [Fintype A] [Nonempty A] [DecidableEq A]

/-- `f₁(p) = (p, 0)`: pair a planner with the trivial reward. -/
@[expose] public def op1 (p : Planner (RewardFn S A) (Policy S A)) : Pair S A := (p, 0)

/-- `f₂(R) = (p_g, R)`: pair a reward with the greedy planner. -/
@[expose] public noncomputable def op2 (R : RewardFn S A) : Pair S A := (greedyPlanner, R)

/-- `f₃(p, R) = p(R)`: evaluation. -/
@[expose] public def op3 (x : Pair S A) : Policy S A := x.1 x.2

/-- `f₄(p, R) = (-p, -R)`: the anti-rational negation. -/
@[expose] public def op4 (x : Pair S A) : Pair S A := ((fun R' => x.1 (-R')), -x.2)

/-- `f₅(π) = p_π`: the indifferent planner for a policy. -/
@[expose] public def op5 (π : Policy S A) : Planner (RewardFn S A) (Policy S A) :=
  indifferentPlanner π

/-- `f₆(π) = R_π`: the reward paying for a policy's action. -/
@[expose] public def op6 (π : Policy S A) : RewardFn S A := rewardOf π

/-! ### The degenerate pairs, built from the operations, are compatible -/

omit [Fintype A] [Nonempty A] [DecidableEq A] in
/-- `(p_π, 0) = f₁(f₅(π))` is compatible with `π`. -/
public theorem op3_op1_op5 (π : Policy S A) : op3 (op1 (op5 π)) = π := rfl

/-- `(p_g, R_π) = f₂(f₆(π))` is compatible with `π`. -/
public theorem op3_op2_op6 (π : Policy S A) : op3 (op2 (op6 π)) = π :=
  greedy_rewardOf π

/-- `(-p_g, -R_π) = f₄(f₂(f₆(π)))` is compatible with `π`. -/
public theorem op3_op4_op2_op6 (π : Policy S A) : op3 (op4 (op2 (op6 π))) = π := by
  show greedyPlanner (- -rewardOf π) = π
  rw [neg_neg]
  exact greedy_rewardOf π

omit [Fintype A] [Nonempty A] [DecidableEq A] in
/-- `f₄` is an involution: `F₄ ∘ F₄ = id`. The source notes this when arguing
that `F`-complexity is non-negative. -/
public theorem op4_op4 (x : Pair S A) : op4 (op4 x) = x := by
  obtain ⟨p, R⟩ := x
  simp only [op4, neg_neg]

omit [Fintype A] [Nonempty A] [DecidableEq A] in
/-- `f₄` preserves the evaluated policy: negating both planner and reward leaves
the behaviour unchanged. This is the source's observation opening §5.2. -/
public theorem op3_op4 (x : Pair S A) : op3 (op4 x) = op3 x := by
  show x.1 (- -x.2) = x.1 x.2
  rw [neg_neg]

end Operations

/-!
## The source's bounded reward space

The source's space of candidate rewards is
`ℛ = {R : 𝒮 × 𝒜 → [-1, 1]} = [-1, 1]^{𝒮×𝒜}` (Armstrong and Mindermann, §3,
`am-reward-space`). `RewardFn` is real-valued and wider; the subtype below picks
out exactly print's set, and the three lemmas after it show that print's own
constructions -- the zero reward of `f₁`, the reward `R_π` of `f₆`, and the
negation of `f₄` -- stay inside it, so every pair the propositions build from a
pair with a bounded reward again has a bounded reward.
-/

/-- A reward function takes values in print's interval `[-1, 1]`. -/
@[expose] public def IsBoundedReward (R : RewardFn S A) : Prop :=
  ∀ s a, R s a ∈ Set.Icc (-1 : ℝ) 1

/-- **The source's reward space** `ℛ = [-1, 1]^{𝒮×𝒜}` (Armstrong and
Mindermann, §3): the reward functions with values in `[-1, 1]`. -/
public abbrev BoundedRewardFn (S A : Type*) : Type _ :=
  {R : RewardFn S A // IsBoundedReward R}

/-- The trivial reward of `f₁(p) = (p, 0)` is in print's reward space. -/
public theorem isBoundedReward_zero : IsBoundedReward (0 : RewardFn S A) := fun _ _ => by
  simp only [Pi.zero_apply, Set.mem_Icc]; norm_num

/-- The reward `R_π = f₆(π)` takes values in `{0, 1}`, so it is in print's
reward space. -/
public theorem isBoundedReward_rewardOf [DecidableEq A] (π : Policy S A) :
    IsBoundedReward (rewardOf π) := fun s a => by
  unfold rewardOf
  split_ifs <;> simp only [Set.mem_Icc] <;> norm_num

/-- Print's reward space is closed under the negation used by `f₄`. -/
public theorem IsBoundedReward.neg {R : RewardFn S A} (h : IsBoundedReward R) :
    IsBoundedReward (-R) := fun s a => by
  obtain ⟨h1, h2⟩ := h s a
  simp only [Pi.neg_apply, Set.mem_Icc]
  constructor <;> linarith

/-!
## Comparable complexity and lowest complexity, at any complexity and any `c`

Armstrong and Mindermann, §5.1 (`am-comparable`, `am-lowest`, PDF p. 6): "choose
a constant `c ≥ 0`, then `(p, R)` and `(p', R')` are of comparable complexity if
`‖K_L(p, R) − K_L(p', R')‖ ≤ c`", and for a set `S ⊂ 𝒫 × ℛ` the pair
`(p, R) ∈ S` "is amongst the lowest complexity in `S` if
`‖K_L(p, R) − min_{(p', R') ∈ S} K_L(p', R')‖ ≤ c`".

Both are stated here for an arbitrary complexity `K : Pair S A → ℕ` (print's
`K_L`, a Kolmogorov complexity and so natural-valued) and an arbitrary real
`c`, with no language structure: print defines them before, and independently
of, any reasonableness assumption. The language structures' relations are
instances (`ReasonableLanguage.proposition_eight_comparable`,
`Source.ReasonableForF.amongLowestCompatible_iff`).
-/

/-- **Comparable complexity** (Armstrong and Mindermann, §5.1, `am-comparable`):
`‖K(x) − K(y)‖ ≤ c`. -/
@[expose] public def ComparableComplexity (K : Pair S A → ℕ) (c : ℝ) (x y : Pair S A) : Prop :=
  |(K x : ℝ) - K y| ≤ c

/-- At a natural constant, comparable complexity is the two one-sided bounds
the propositions conclude. -/
public theorem comparableComplexity_iff (K : Pair S A → ℕ) (c : ℕ) (x y : Pair S A) :
    ComparableComplexity K c x y ↔ K x ≤ K y + c ∧ K y ≤ K x + c := by
  unfold ComparableComplexity
  rw [abs_le]
  constructor
  · rintro ⟨h1, h2⟩
    constructor
    · exact_mod_cast (by linarith : (K x : ℝ) ≤ K y + c)
    · exact_mod_cast (by linarith : (K y : ℝ) ≤ K x + c)
  · rintro ⟨h1, h2⟩
    have h1' : (K x : ℝ) ≤ K y + c := by exact_mod_cast h1
    have h2' : (K y : ℝ) ≤ K x + c := by exact_mod_cast h2
    constructor <;> linarith

/-- Comparable complexity is symmetric, as print's norm makes it. -/
public theorem ComparableComplexity.symm {K : Pair S A → ℕ} {c : ℝ} {x y : Pair S A}
    (h : ComparableComplexity K c x y) : ComparableComplexity K c y x := by
  unfold ComparableComplexity at *
  rwa [abs_sub_comm]

/-- **Amongst the lowest complexity in a set** (Armstrong and Mindermann, §5.1,
`am-lowest`), for any set `T` of pairs: `x ∈ T` and no pair of `T` beats it by
more than `c`.

Print writes the distance to `min_{T} K`. Because `K` is natural-valued, that
minimum is attained on every nonempty `T`, and `amongLowest_iff_min` shows the
two readings agree exactly. -/
@[expose] public def AmongLowest (K : Pair S A → ℕ) (c : ℝ) (T : Set (Pair S A))
    (x : Pair S A) : Prop :=
  x ∈ T ∧ ∀ y ∈ T, (K x : ℝ) ≤ K y + c

/-- `AmongLowest` is print's formula `‖K(x) − min_{y ∈ T} K(y)‖ ≤ c`, with the
minimum written as `sInf (K '' T)`, attained because `K` is natural-valued. -/
public theorem amongLowest_iff_min (K : Pair S A → ℕ) (c : ℝ) (T : Set (Pair S A))
    (x : Pair S A) :
    AmongLowest K c T x ↔ x ∈ T ∧ |(K x : ℝ) - (sInf (K '' T) : ℕ)| ≤ c := by
  constructor
  · rintro ⟨hx, hmin⟩
    refine ⟨hx, ?_⟩
    obtain ⟨y, hy, hyeq⟩ := Nat.sInf_mem (⟨K x, x, hx, rfl⟩ : (K '' T).Nonempty)
    have hle : sInf (K '' T) ≤ K x := Nat.sInf_le ⟨x, hx, rfl⟩
    have hle' : ((sInf (K '' T) : ℕ) : ℝ) ≤ K x := by exact_mod_cast hle
    have := hmin y hy
    rw [hyeq] at this
    rw [abs_of_nonneg (by linarith)]
    linarith
  · rintro ⟨hx, habs⟩
    refine ⟨hx, fun y hy => ?_⟩
    have hle : sInf (K '' T) ≤ K y := Nat.sInf_le ⟨y, hy, rfl⟩
    have hle' : ((sInf (K '' T) : ℕ) : ℝ) ≤ K y := by exact_mod_cast hle
    have := (abs_le.mp habs).2
    linarith

/-!
## `c`-reasonable languages
-/

/--
An abstract complexity assignment with additive bounds for evaluation, the
three degenerate-pair constructions, and pair negation. This is a
reparameterized interface for the bounds used below, not the source's literal
definition of a `c`-reasonable language.
-/
public structure ReasonableLanguage (S A : Type*)
    [Fintype A] [Nonempty A] [DecidableEq A] where
  /-- Complexity of a planner/reward pair. -/
  KPair : Pair S A → ℕ
  /-- Complexity of a policy. -/
  KPolicy : Policy S A → ℕ
  /-- The additive slack used by each recorded bound. -/
  c : ℕ
  /-- `f₃` is cheap: evaluating a pair costs at most `c` over the pair. -/
  eval_le : ∀ x : Pair S A, KPolicy (op3 x) ≤ KPair x + c
  /-- `f₁ ∘ f₅` is cheap: the indifferent pair costs at most `c` over the policy. -/
  indifferent_le : ∀ π : Policy S A, KPair (op1 (op5 π)) ≤ KPolicy π + c
  /-- `f₂ ∘ f₆` is cheap: the greedy pair costs at most `c` over the policy. -/
  greedy_le : ∀ π : Policy S A, KPair (op2 (op6 π)) ≤ KPolicy π + c
  /-- `f₄ ∘ f₂ ∘ f₆` is cheap: the anti-rational pair costs at most `c`. -/
  antirational_le : ∀ π : Policy S A, KPair (op4 (op2 (op6 π))) ≤ KPolicy π + c
  /-- `f₄` is cheap on *any* pair, not only the degenerate ones. This is the
  bound §5.2 needs. -/
  neg_le : ∀ x : Pair S A, KPair (op4 x) ≤ KPair x + c

namespace ReasonableLanguage

variable [Fintype A] [Nonempty A] [DecidableEq A]
variable (L : ReasonableLanguage S A) (π : Policy S A) (x : Pair S A)

/-- Compatibility, in the source's sense: the pair evaluates to the policy.

`AISafetyAtlas.Preference.Source.ReasonableForF.Compatible` is this same
definition, character for character and with the same type, in the namespace of
the source-literal language structure. Neither is derived from the other, and a
reader who finds one should know the other exists; whether they should be one
declaration is a question about how far `Source.` mirrors are kept separate, not
a question about the mathematics. -/
@[expose] public def Compatible (x : Pair S A) (π : Policy S A) : Prop := op3 x = π

/-- Any compatible pair lower-bounds the policy's complexity, up to `c`.
This is the source's first claim in §5.1, via `f₃`. -/
public theorem policy_le_of_compatible (h : Compatible x π) :
    L.KPolicy π ≤ L.KPair x + L.c := by
  have := L.eval_le x
  rwa [h] at this

/-- **Proposition 7, first pair.** `(p_π, 0)` is within `2c` of any compatible pair. -/
public theorem indifferent_le_compatible (h : Compatible x π) :
    L.KPair (op1 (op5 π)) ≤ L.KPair x + 2 * L.c := by
  have h1 := L.indifferent_le π
  have h2 := L.policy_le_of_compatible π x h
  omega

/-- **Proposition 7, second pair.** `(p_g, R_π)` is within `2c` of any compatible pair. -/
public theorem greedy_le_compatible (h : Compatible x π) :
    L.KPair (op2 (op6 π)) ≤ L.KPair x + 2 * L.c := by
  have h1 := L.greedy_le π
  have h2 := L.policy_le_of_compatible π x h
  omega

/-- **Proposition 7, third pair.** `(-p_g, -R_π)` is within `2c` of any compatible pair. -/
public theorem antirational_le_compatible (h : Compatible x π) :
    L.KPair (op4 (op2 (op6 π))) ≤ L.KPair x + 2 * L.c := by
  have h1 := L.antirational_le π
  have h2 := L.policy_le_of_compatible π x h
  omega

/--
**Proposition 7.**

All three degenerate planner/reward pairs are among the lowest-complexity pairs
compatible with the policy: each is within `2c` of every compatible pair, and
each is itself compatible.
-/
public theorem proposition_seven (h : Compatible x π) :
    (Compatible (op1 (op5 π)) π ∧
      L.KPair (op1 (op5 π)) ≤ L.KPair x + 2 * L.c) ∧
    (Compatible (op2 (op6 π)) π ∧
      L.KPair (op2 (op6 π)) ≤ L.KPair x + 2 * L.c) ∧
    (Compatible (op4 (op2 (op6 π))) π ∧
      L.KPair (op4 (op2 (op6 π))) ≤ L.KPair x + 2 * L.c) :=
  ⟨⟨op3_op1_op5 π, L.indifferent_le_compatible π x h⟩,
   ⟨op3_op2_op6 π, L.greedy_le_compatible π x h⟩,
   ⟨op3_op4_op2_op6 π, L.antirational_le_compatible π x h⟩⟩

/--
**Proposition 8 (source §5.2).**

If a pair is compatible with the policy then so is its negation, and the two are
of comparable complexity: the negated pair costs at most `c` more.

So complexity fails to distinguish a reasonable human reward function from its
negative. Unlike `proposition_seven`, this applies to *every* compatible pair,
including the intended one, not only the degenerate constructions.
-/
public theorem proposition_eight (h : Compatible x π) :
    Compatible (op4 x) π ∧
      L.KPair (op4 x) ≤ L.KPair x + L.c ∧
      L.KPair x ≤ L.KPair (op4 x) + L.c := by
  refine ⟨by rw [Compatible, op3_op4]; exact h, L.neg_le x, ?_⟩
  have := L.neg_le (op4 x)
  rwa [op4_op4] at this

/-- **Proposition 8, in print's vocabulary** (source §5.2): a compatible pair's
negation is compatible with the same policy and the two are *of comparable
complexity* in the sense of `ComparableComplexity` (`am-comparable`) at the
language's constant. A corollary of `proposition_eight`, which is unchanged. -/
public theorem proposition_eight_comparable (h : Compatible x π) :
    Compatible (op4 x) π ∧ ComparableComplexity L.KPair L.c x (op4 x) := by
  obtain ⟨hc, h1, h2⟩ := L.proposition_eight π x h
  exact ⟨hc, (comparableComplexity_iff _ _ _ _).mpr ⟨h2, h1⟩⟩

end ReasonableLanguage

end AISafetyAtlas.Preference
