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
  (2) for the rationalising action; and §B.2's claim that when the human is not
  already optimal, rationalising yields greater value than action `0`. These are
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

end OverrideModel

end AISafetyAtlas.Preference
