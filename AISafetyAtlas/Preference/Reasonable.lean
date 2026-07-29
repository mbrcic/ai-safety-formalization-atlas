module

public import AISafetyAtlas.Preference
public import Mathlib.Algebra.Group.Pi.Basic

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
  concrete plain-Kolmogorov instantiation of the same argument, for the first
  degenerate pair, is in `AISafetyAtlas.Preference.Complexity`.

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

/-- Compatibility, in the source's sense: the pair evaluates to the policy. -/
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

end ReasonableLanguage

end AISafetyAtlas.Preference
