module

public import AISafetyAtlas.Preference
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith
public import Mathlib.Order.Bounds.Basic

/-!
# Overriding human reward functions (source Appendix B)

## Statement intent

- **Objects.** An abstract model of an agent acting alongside a human: a type of
  agent actions, the human policy each action results in, a value assignment for
  policies under rewards, and an optimal value.
- **Assumptions.** Values never exceed the optimum; there is a distinguished
  no-op action; and for each reward there is an action making the resulting human
  policy optimal for it. The source assumes the last of these when it says the
  agent can "make the human into a rational `Ṙ`-maximiser".
- **Quantifier order.** The reward is fixed first; actions are then compared
  against it.
- **Conclusion.** Both an unrelativised regret predicate (`Overrides`) and
  Definition 11 relative to a compatible `(p, R)` (`OverridesFor`); equation
  (2) for the rationalising action; §B.2's claim that when the human is not
  already optimal, rationalising yields greater value than action `0`; and
  **both** of appendix B.1's branches about inaction — zero regret under a
  fully rational planner (`regret_noop_eq_zero_of_rationalPlanner`) and positive
  regret otherwise (`noop_overrides_of_suboptimal`) — together with the fact
  that they exhaust the cases (`regret_noop_eq_zero_or_overrides`). These are
  scalar comparisons; no agent preference or choice rule is defined here.
- **Difference from the source.** §B.2 also argues, informally and with an
  explicit "very plausible", that the agent can often do better still by choosing
  a reward `Rᵃ` that is easy to maximise. That existential claim is not
  formalized. No transition dynamics, discounting, or MDP structure is developed;
  value and optimal value are abstract fields.

## Explicit non-claims

- **Not** an agent preference or choice rule. `rationalise_strictly_better` is a
  value inequality; nothing here says what an agent selects.
- **Not** a full MDP realization of Definition 11. `OverridesFor` restores the
  compatible decomposition, but outcomes and values remain abstract and “high
  regret” is represented by an explicit threshold. `Overrides` is retained only
  as the unrelativised shadow.
- **Not** a claim that any real system overrides human preferences.
- **Not** the source's speculative part of §B.2 about choosing an easily
  maximised `Rᵃ`.
- **Not** a treatment of "mental integrity" or "self-determination", which the
  source's own footnote flags as absent from the formalism.

Survey row: **BY-011**. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Preference

/--
An abstract model of an agent whose actions reshape the human policy.

`resulting a` is the human policy after the agent takes action `a`; `noop` is the
action of leaving the human alone; `rationalise R` is an action making the human
an optimal `R`-maximiser.
-/
public structure OverrideModel (S A Act : Type*) where
  /-- The human policy resulting from an agent action. -/
  resulting : Act → Policy S A
  /-- Value of a human policy under a reward. -/
  value : RewardFn S A → Policy S A → ℝ
  /-- The best value attainable under a reward. -/
  optValue : RewardFn S A → ℝ
  /-- No policy beats the optimum. -/
  le_optValue : ∀ R π, value R π ≤ optValue R
  /-- Leaving the human alone. -/
  noop : Act
  /-- An action making the human optimal for the given reward. -/
  rationalise : RewardFn S A → Act
  /-- That action does make the human optimal. -/
  rationalise_optimal : ∀ R, value R (resulting (rationalise R)) = optValue R

namespace OverrideModel

variable {S A Act : Type*} (M : OverrideModel S A Act)

/-- Regret of the human policy resulting from an agent action, under a reward. -/
@[expose] public def regret (R : RewardFn S A) (a : Act) : ℝ :=
  M.optValue R - M.value R (M.resulting a)

/-- Regret is never negative: no action beats the optimal value it is measured
against. Sanity condition on the definition, and what lets a regret bound be
read as a shortfall rather than a signed quantity. -/
public theorem regret_nonneg (R : RewardFn S A) (a : Act) : 0 ≤ M.regret R a :=
  sub_nonneg.mpr (M.le_optValue R _)

/--
**Definition 11.** The agent's action `a` *overrides* the reward `R` at
threshold `θ` when it leaves the human in a situation whose regret for `R` is at
least `θ`.

The source states this with an informal "high regret"; the threshold is made an
explicit parameter here rather than fixed, since the source notes there is no
natural zero.
-/
@[expose] public def Overrides (R : RewardFn S A) (θ : ℝ) (a : Act) : Prop :=
  θ ≤ M.regret R a

/--
**§B.2.** If the human is not already optimal for the reward, then rationalising
them yields a strictly greater value for that reward than leaving them alone.

This is a scalar value inequality only. No agent preference or choice rule is
defined in this module, so it does not by itself say any agent *prefers* to act;
that reading needs a decision rule that is not formalized here. Note also that
rationalising has zero regret (`regret_rationalise`), so it is not an
`Overrides R θ` action for positive `θ`: the source describes this as overriding
the human *policy*, which Definition 11 does not cover.
-/
public theorem rationalise_strictly_better (R : RewardFn S A)
    (h : M.value R (M.resulting M.noop) < M.optValue R) :
    M.value R (M.resulting M.noop) < M.value R (M.resulting (M.rationalise R)) := by
  rw [M.rationalise_optimal R]
  exact h

/--
**§B.2, the no-natural-zero observation.** A suboptimal human is already in a
positive-regret situation, so *inaction* itself counts as an override at every
threshold up to that regret.
-/
public theorem noop_overrides_of_suboptimal (R : RewardFn S A)
    (h : M.value R (M.resulting M.noop) < M.optValue R) :
    0 < M.regret R M.noop ∧ ∀ θ ≤ M.regret R M.noop, M.Overrides R θ M.noop := by
  refine ⟨sub_pos.mpr h, fun θ hθ => hθ⟩

/-- Rationalising incurs no regret. -/
public theorem regret_rationalise (R : RewardFn S A) :
    M.regret R (M.rationalise R) = 0 := by
  simp [regret, M.rationalise_optimal R]

/-!
### Appendix B in the source's own terms

`Overrides` above drops the source's relativisation to a compatible pair. The
declarations below restore it, and add the two displayed equations.
-/

/--
**Equation (1).**  The source writes regret against
`max_{b ∈ A^a} V_Ṙ^{π̇'|b}`, a maximum over the *agent's* actions rather than an
unexplained optimum.  In this model that maximum exists and equals `optValue`,
since `rationalise R` attains it.
-/
public theorem optValue_isGreatest (R : RewardFn S A) :
    IsGreatest {v : ℝ | ∃ a : Act, v = M.value R (M.resulting a)} (M.optValue R) := by
  constructor
  · exact ⟨M.rationalise R, (M.rationalise_optimal R).symm⟩
  · rintro v ⟨a, rfl⟩
    exact M.le_optValue R _

/--
**Definition 11, relativised.**  The source's definition is given *relative to a
compatible pair* `(p, R)`: the agent's action `a` overrides the human reward
function when it leaves the human in a situation of high regret for `R`, where
`(p, R)` is a decomposition of the resulting human behaviour.

`Overrides` is the unrelativised shadow of this; `overrides_of_overridesFor`
records that this is the stronger notion.
-/
@[expose] public def OverridesFor
    (p : Planner (RewardFn S A) (Policy S A)) (R : RewardFn S A)
    (θ : ℝ) (a : Act) : Prop :=
  Explains p R (M.resulting a) ∧ θ ≤ M.regret R a

/-- The relativised notion implies the unrelativised one. -/
public theorem overrides_of_overridesFor
    {p : Planner (RewardFn S A) (Policy S A)} {R : RewardFn S A}
    {θ : ℝ} {a : Act} (h : M.OverridesFor p R θ a) : M.Overrides R θ a := h.2

/--
Every agent action admits *some* compatible pair explaining the resulting human
policy, by Theorem 1.  So relativisation never rules an action out; it only
records which decomposition the regret is being measured against.
-/
public theorem exists_overridesFor (R : RewardFn S A) (θ : ℝ) (a : Act)
    (h : θ ≤ M.regret R a) :
    ∃ p : Planner (RewardFn S A) (Policy S A), M.OverridesFor p R θ a :=
  ⟨fun _ => M.resulting a, rfl, h⟩

/--
**Equation (2).**  The value of the action that rationalises the human for
`Ragent`, when the agent gives probability `1 - ε` to `Rtrue` and probability
`ε` to `Ragent`.

Unlike an earlier atlas definition, this does not accept an arbitrary action:
the source's `ε V*_{Ragent}` term is justified specifically because this action
makes the resulting human policy `Ragent`-optimal.
-/
@[expose] public def mixtureValue (ε : ℝ)
    (Rtrue Ragent : RewardFn S A) : ℝ :=
  ε * M.optValue Ragent +
    (1 - ε) * M.value Rtrue (M.resulting (M.rationalise Ragent))

/--
The value of action `0` / no-op under the true reward.  It is separate from
equation (2): no-op does not acquire an `ε * optValue` term unless it is itself
known to rationalise the human for the hypothesised reward.
-/
@[expose] public def noopValue (Rtrue : RewardFn S A) : ℝ :=
  M.value Rtrue (M.resulting M.noop)

/--
**The source's "at the very least" claim.**

Choosing `Ragent = Rtrue` and rationalising makes equation (2) equal to the
optimum `V*_Ṙ`, at every mixture weight.  So overriding never costs the agent
anything relative to the true optimum.
-/
public theorem mixtureValue_rationalise (ε : ℝ) (R : RewardFn S A) :
    M.mixtureValue ε R R = M.optValue R := by
  simp only [mixtureValue, M.rationalise_optimal R]
  ring

/--
When the human is not already optimal, the source's action `0` value is
strictly worse than the value of rationalising for the true reward.

This is the source's closing observation of §B.2, that a less-than-rational
human gives the agent a definite gain from overriding.
-/
public theorem noopValue_lt_mixtureValue_rationalise (ε : ℝ) (R : RewardFn S A)
    (h : M.value R (M.resulting M.noop) < M.optValue R) :
    M.noopValue R < M.mixtureValue ε R R := by
  rw [mixtureValue_rationalise]
  exact h

/-! ### Appendix B.1's other branch, and why both are here

Print writes two things about inaction two paragraphs apart, and they do not
conflict because they assume different planners.

> We already know that `π̇` is optimal with respect to `Ṙ` (by definition), so
> the regret for `a = 0` is `0`.

That is the **fully rational planner**: the decomposition explaining the
human's own behaviour returns an optimal policy. Print then takes the other
branch — a less-than-rational human, for whom inaction is strictly worse — and
`noop_overrides_of_suboptimal` above is that one. The declarations below are the
first, so the module carries both, and `regret_noop_eq_zero_or_overrides` is the
dichotomy that makes them exhaustive rather than merely compatible.
-/

/--
**Print's fully rational planner.** The planner returns, for every reward, a
policy of optimal value — print's *"`π̇` is optimal with respect to `Ṙ` (by
definition)"*, where the *by definition* is the rationality assumption on the
decomposition and not a property of the human.
-/
@[expose] public def IsRationalPlanner (p : Planner (RewardFn S A) (Policy S A)) : Prop :=
  ∀ R, M.value R (p R) = M.optValue R

/--
**Appendix B.1, the first branch.** If the human's behaviour under inaction is
explained by a compatible pair whose planner is fully rational, then inaction
has zero regret.
-/
public theorem regret_noop_eq_zero_of_rationalPlanner
    {p : Planner (RewardFn S A) (Policy S A)} (hp : M.IsRationalPlanner p)
    (R : RewardFn S A) (hexp : Explains p R (M.resulting M.noop)) :
    M.regret R M.noop = 0 := by
  have : M.value R (M.resulting M.noop) = M.optValue R := by
    rw [← hexp]; exact hp R
  simp [regret, this]

/--
**The closed form print draws from that branch.** With inaction at zero regret
the optimum *is* the human's own value, so the regret of any other action is
exactly how far below the untouched human it leaves them.
-/
public theorem regret_eq_noopValue_sub_of_rationalPlanner
    {p : Planner (RewardFn S A) (Policy S A)} (hp : M.IsRationalPlanner p)
    (R : RewardFn S A) (hexp : Explains p R (M.resulting M.noop)) (a : Act) :
    M.regret R a = M.noopValue R - M.value R (M.resulting a) := by
  have h : M.value R (M.resulting M.noop) = M.optValue R := by
    rw [← hexp]; exact hp R
  simp [regret, noopValue, h]

/--
**Under that branch inaction is not an override**, at any positive threshold —
which is what makes print's first paragraph a claim about the agent's incentive
and not a restatement of Definition 11.
-/
public theorem not_overrides_noop_of_rationalPlanner
    {p : Planner (RewardFn S A) (Policy S A)} (hp : M.IsRationalPlanner p)
    (R : RewardFn S A) (hexp : Explains p R (M.resulting M.noop))
    {θ : ℝ} (hθ : 0 < θ) : ¬ M.Overrides R θ M.noop := by
  rw [Overrides, M.regret_noop_eq_zero_of_rationalPlanner hp R hexp]
  exact not_le.mpr hθ

/--
**The two branches are exhaustive.** Inaction either has no regret at all or is
itself an override at every threshold up to its regret — print's two paragraphs
are the two cases of this, and nothing in the model admits a third.
-/
public theorem regret_noop_eq_zero_or_overrides (R : RewardFn S A) :
    M.regret R M.noop = 0 ∨
      (0 < M.regret R M.noop ∧ ∀ θ ≤ M.regret R M.noop, M.Overrides R θ M.noop) := by
  rcases eq_or_lt_of_le (M.regret_nonneg R M.noop) with h | h
  · exact Or.inl h.symm
  · exact Or.inr ⟨h, fun _ hθ => hθ⟩

end OverrideModel

end AISafetyAtlas.Preference
