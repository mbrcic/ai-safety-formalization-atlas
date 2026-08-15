module

public import AISafetyAtlas.Wireheading.GoalPreservation
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite-percept Theorem 12 induction step, without surjectivity

`AISafetyAtlas.Wireheading.GoalPreservation` proves a deterministic
specialization of Everitt, Filan, Daswani and Hutter, AGI 2016, LNCS 9782,
Theorem 12 (extended version `arXiv:1605.03142`, Theorem 16), but
only under `names_surjective`: at every history, *every* world-action and
next-policy pair is emitted by some represented policy.  That premise is
stronger than the source's, which introduces a naming map `ι : P → Π` and says
explicitly that not every policy can have a name.

This module removes it from the one-step induction argument.

## What the source's proof actually uses

Reading the proof of Theorem 12, the comparison is never against an arbitrary
policy.  It is against `π₁`, the agent's own initial policy, which *is* named by
assumption, so the action `(ǎ_t, π₁)` is always available.  The proof then
argues:

* if the selected continuation `π_{t+1}` were worse than `π₁` at some percept,
  it would be no better at any percept and strictly worse at that one;
* percepts are drawn from a finite full-support probability mass function, so a
  pointwise inequality that is strict somewhere makes the *expectation*
  strictly worse;
* hence `(ǎ_t, π_{t+1})` would be strictly worse than the available alternative
  `(ǎ_t, π₁)`, contradicting the optimality of `π_t`.

So the two ingredients are **nameability of the initial policy** and **full
support**, not surjectivity of the naming map.  `Model` records exactly those:
`initial` is a name, `initial_dominates` says `π₁` is optimal in the form the
proof uses, and `prob_sum_one` / `prob_pos` make `prob` a full-support finite
probability mass function.

## Explicit non-claims

* **Finitely many percepts.** Expectations are normalized `Finset` sums over a
  `Fintype`, not integrals. No measure theory is used, so this is the
  finite-percept case of the source's `E_{e_t}`.
* **Not the full source theorem.** `initial_dominates` and `contValue`
  are given; the source derives the corresponding facts from
  modification-independent `ρ` and `u₁` together with the optimal-policy-existence
  result the technical report proves as its Theorem 20 in Appendix A — the
  published chapter prints no proofs, so that is the only place it appears — which
  is not reproduced.  What is reproduced is the induction step of Theorem 12, which
  is where `names_surjective` was previously needed.
* **On-policy only**, as in the source: nothing is claimed off the reached path.
* **Not utility modification**, only policy modification.

Landscape entry: `LAND-GOAL-001`.  No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Wireheading.GoalPreservationSource

/--
A policy self-modification model with stochastic percepts.

`act p h` is `ι(p)` applied at `h`, giving a world action and the *name* of the
next policy.  There is no assumption that every pair arises this way.
-/
public structure Model (History WorldAction PolicyName Percept : Type*)
    [Fintype Percept] where
  /-- The named policy's choice: a world action and the next policy's name. -/
  act : PolicyName → History → WorldAction × PolicyName
  /-- History extension by a world action and the percept received. -/
  extend : History → WorldAction → Percept → History
  /-- The initial utility `u₁`. -/
  utility : History → ℝ
  /-- Discount factor. -/
  discount : ℝ
  /-- It is positive. -/
  discount_pos : 0 < discount
  /-- Probability mass assigned to each next percept. -/
  prob : History → WorldAction → Percept → ℝ
  /-- The percept weights are normalized for every history and world action. -/
  prob_sum_one : ∀ h a, ∑ e : Percept, prob h a e = 1
  /-- **Full support**: every percept has positive weight.  This is what turns a
  pointwise strict inequality into a strict inequality of expectations. -/
  prob_pos : ∀ h a e, 0 < prob h a e
  /-- The realistic continuation value of a named policy, evaluated under the
  initial utility. -/
  contValue : PolicyName → History → ℝ
  /-- The initial policy's name.  Nameability of `π₁` is the assumption that
  replaces surjectivity of the naming map. -/
  initial : PolicyName
  /-- `π₁` is optimal, in the form the source's proof uses. -/
  initial_dominates : ∀ p h, contValue p h ≤ contValue initial h

namespace Model

variable {History WorldAction PolicyName Percept : Type*} [Fintype Percept]
variable (M : Model History WorldAction PolicyName Percept)

/-- The realistic `Q` value of a world-action and next-policy pair, as an
expectation over percepts. -/
@[expose] public noncomputable def qValue (h : History)
    (a : WorldAction × PolicyName) : ℝ :=
  ∑ e : Percept, M.prob h a.1 e *
    (M.utility (M.extend h a.1 e) +
      M.discount * M.contValue a.2 (M.extend h a.1 e))

/-- A named policy chooses a `Q`-maximizing action at a history. -/
@[expose] public def OptimalAt (p : PolicyName) (h : History) : Prop :=
  ∀ a, M.qValue h a ≤ M.qValue h (M.act p h)

/-- Swapping in a dominated continuation cannot raise the `Q` value, and lowers
it strictly as soon as it is strictly worse at one percept. -/
public theorem qValue_lt_of_lt (h : History) (w : WorldAction)
    (q : PolicyName) (e₀ : Percept)
    (hstrict : M.contValue q (M.extend h w e₀) <
      M.contValue M.initial (M.extend h w e₀)) :
    M.qValue h (w, q) < M.qValue h (w, M.initial) := by
  refine Finset.sum_lt_sum (fun e _ => ?_) ⟨e₀, Finset.mem_univ e₀, ?_⟩
  · have hle := M.initial_dominates q (M.extend h w e)
    have hdisc : M.discount * M.contValue q (M.extend h w e) ≤
        M.discount * M.contValue M.initial (M.extend h w e) :=
      mul_le_mul_of_nonneg_left hle M.discount_pos.le
    exact mul_le_mul_of_nonneg_left (by linarith) (le_of_lt (M.prob_pos h w e))
  · have hmul :
        M.discount * M.contValue q (M.extend h w e₀) <
          M.discount * M.contValue M.initial (M.extend h w e₀) :=
      mul_lt_mul_of_pos_left hstrict M.discount_pos
    exact mul_lt_mul_of_pos_left (by linarith) (M.prob_pos h w e₀)

/--
**The induction step of Theorem 12, without surjectivity.**

If the current policy acts optimally at a history, the continuation it selects
achieves exactly the initial policy's value at every reachable successor.

The proof never quantifies over unnamed policies.  It compares only against
`(ǎ, initial)`, which is available because `initial` is a name, and uses full
support to turn a single strict percept into a strictly worse expectation.
-/
public theorem selected_matches_initial {p : PolicyName} {h : History}
    (hopt : M.OptimalAt p h) (e : Percept) :
    M.contValue (M.act p h).2 (M.extend h (M.act p h).1 e) =
      M.contValue M.initial (M.extend h (M.act p h).1 e) := by
  by_contra hne
  have hle := M.initial_dominates (M.act p h).2 (M.extend h (M.act p h).1 e)
  have hstrict :
      M.contValue (M.act p h).2 (M.extend h (M.act p h).1 e) <
        M.contValue M.initial (M.extend h (M.act p h).1 e) :=
    lt_of_le_of_ne hle hne
  have hlt := M.qValue_lt_of_lt h (M.act p h).1 (M.act p h).2 e hstrict
  have hcmp := hopt ((M.act p h).1, M.initial)
  have hself : M.qValue h ((M.act p h).1, (M.act p h).2) = M.qValue h (M.act p h) := by
    congr 1
  rw [hself] at hlt
  exact absurd hcmp (not_le.mpr hlt)

/--
**Realistic policy modification is safe, on-policy.**

At every reachable successor, the value obtained by the self-modified
continuation equals the value the initial policy would have obtained.  This is
equation (13) of the source at one step, and it holds with no constraint on
which policies have names beyond the initial one having one.
-/
public theorem safe_modification {p : PolicyName} {h : History}
    (hopt : M.OptimalAt p h) :
    ∀ e : Percept,
      M.contValue (M.act p h).2 (M.extend h (M.act p h).1 e) =
        M.contValue M.initial (M.extend h (M.act p h).1 e) :=
  fun e => M.selected_matches_initial hopt e

/--
The `Q` value of the selected action equals that of re-selecting the initial
policy: self-modification is value-neutral for the initial objective.
-/
public theorem qValue_selected_eq_initial {p : PolicyName} {h : History}
    (hopt : M.OptimalAt p h) :
    M.qValue h (M.act p h) = M.qValue h ((M.act p h).1, M.initial) := by
  have hfun : ∀ e : Percept,
      M.contValue (M.act p h).2 (M.extend h (M.act p h).1 e) =
        M.contValue M.initial (M.extend h (M.act p h).1 e) :=
    M.safe_modification hopt
  have hself : M.qValue h (M.act p h) =
      M.qValue h ((M.act p h).1, (M.act p h).2) := by congr 1
  rw [hself]
  simp only [qValue]
  exact Finset.sum_congr rfl (fun e _ => by rw [hfun e])

end Model

end AISafetyAtlas.Wireheading.GoalPreservationSource
