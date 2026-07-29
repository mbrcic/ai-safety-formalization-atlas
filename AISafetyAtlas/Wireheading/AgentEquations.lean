module

public import AISafetyAtlas.Wireheading.Objective
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Ring and Orseau's agent equations, at finite horizon

`AISafetyAtlas.Wireheading.Objective` isolates the observation that Ring and
Orseau's four agents differ only in their utility and horizon functions, but it
does so over an abstract `value` that has nothing to do with their value
equations.  This module writes those equations down.

## The source equations

Ring and Orseau, *Delusion, Survival, and Intelligent Agents*, AGI 2011, §2:

```
(1)  a_{|h|}  := argmax_{a ∈ A} v_{|h|}(ha)
(2)  v_t(ha)  := Σ_{o ∈ O} ρ(o | ha) · v_t(hao)
(3)  v_t(h)   := w(t, |h|) · u(h) + max_{a ∈ A} v_t(ha)
```

An agent is described by a utility `u : H → ℝ`, a horizon weighting
`w : ℕ → ℕ → ℝ`, and a prior `ρ`.  The four agents of the paper share `ρ`, the
action set and the observation set, and differ only in `(u, w)`.

## The finite-horizon form, and the truncation

Equations (2) and (3) are mutually recursive with no base case, so they do not
define a function without an infinite-horizon limit.  `value` truncates at a
remaining depth `n`:

* `value ρ ag t 0 h = w(t, |h|) · u(h)`, the tail beyond the window discarded;
* `value ρ ag t (n+1) h` is equation (3) with equation (2) substituted, over
  the depth-`n` values of the one-step extensions.

`truncation_exact` makes the truncation error explicit rather than leaving it
implicit: once the horizon weighting vanishes past the window, deepening the
recursion changes nothing, so the finite-horizon value *is* the value.  That is
the condition under which the finite form is not an approximation.

## What is proved

* `value_eq_of_agree_on_window`: the value at depth `n` depends only on the
  utility and horizon inside the reachable window.  This is the factorization
  claim with content: it uses the recursion, unlike the record congruence in
  `Objective`.
* `truncation_exact`: with a vanishing horizon tail, depth `n` and depth `n+1`
  agree.
* `bestAction` and `bestAction_max`: equation (1).

## Explicit non-claims

* **Not AIXI.**  `ρ` is an arbitrary conditional weighting, not a universal
  prior; nothing here is about Solomonoff induction or incomputability.
* **Not a probability measure.**  `ρ.cond` is a real-valued weight with no
  normalization or nonnegativity assumed.  Equation (2) is written as a finite
  sum over a `Fintype` of observations, not as an expectation.
* **Unbounded utility codomain.** The source uses utilities in `[0,1]`;
  `Agent.utility` is real-valued without a range invariant. The recursive
  equalities and locality proof remain valid at this more general type.
* **No infinite-horizon limit**, hence no convergence or contraction argument.
* **Not the delusion box.**  The paper's Statements 1 to 7 are informal
  arguments about four specific agents; none is formalized here, and the paper
  does not state them as theorems.

Landscape entry: `LAND-WIRE-OBJ-001`.  No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Wireheading.AgentEquations

/-- Interaction histories: alternating actions and observations. -/
public abbrev History (Action Obs : Type*) : Type _ := List (Action × Obs)

/-- The two components that distinguish Ring and Orseau's four agents. -/
public structure Agent (Action Obs : Type*) where
  /-- Utility of a history, the source's `u`. -/
  utility : History Action Obs → ℝ
  /-- Horizon weighting, the source's `w(t, k)`. -/
  horizon : ℕ → ℕ → ℝ

/-- The agent's prior knowledge, the source's `ρ`, as a conditional weighting of
the next observation given a history and an action. -/
public structure Belief (Action Obs : Type*) where
  /-- `cond h a o` is the source's `ρ(o | ha)`. -/
  cond : History Action Obs → Action → Obs → ℝ

variable {Action Obs : Type*} [Fintype Action] [Nonempty Action] [Fintype Obs]

/--
Equations (2) and (3) at remaining depth `n`.

At depth `0` only the current step's weighted utility is counted; the tail
beyond the window is discarded.  See `truncation_exact` for when that discards
nothing.
-/
@[expose] public noncomputable def value (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t : ℕ) :
    ℕ → History Action Obs → ℝ
  | 0, h => ag.horizon t h.length * ag.utility h
  | n + 1, h =>
      ag.horizon t h.length * ag.utility h +
        (Finset.univ : Finset Action).sup' Finset.univ_nonempty
          (fun a => ∑ o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)]))

/-- Equation (2): the value of an action is the weighted sum over observations
of the values of the resulting histories. -/
@[expose] public noncomputable def actionValue (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t n : ℕ) (h : History Action Obs) (a : Action) : ℝ :=
  ∑ o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])

/-- Equation (3), restated in terms of `actionValue`. -/
public theorem value_succ (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (t n : ℕ) (h : History Action Obs) :
    value ρ ag t (n + 1) h =
      ag.horizon t h.length * ag.utility h +
        (Finset.univ : Finset Action).sup' Finset.univ_nonempty
          (actionValue ρ ag t n h) := rfl

/-- Equation (1): an action attaining the maximum action value. -/
@[expose] public noncomputable def bestAction (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t n : ℕ) (h : History Action Obs) : Action :=
  ((Finset.univ : Finset Action).exists_mem_eq_sup' Finset.univ_nonempty
    (actionValue ρ ag t n h)).choose

/-- The chosen action is maximal, which is what equation (1) asserts. -/
public theorem bestAction_max (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (t n : ℕ) (h : History Action Obs) (a : Action) :
    actionValue ρ ag t n h a ≤ actionValue ρ ag t n h (bestAction ρ ag t n h) := by
  have hsup :
      (Finset.univ : Finset Action).sup' Finset.univ_nonempty
          (actionValue ρ ag t n h) =
        actionValue ρ ag t n h (bestAction ρ ag t n h) :=
    ((Finset.univ : Finset Action).exists_mem_eq_sup' Finset.univ_nonempty
      (actionValue ρ ag t n h)).choose_spec.2
  rw [← hsup]
  exact Finset.le_sup' _ (Finset.mem_univ a)

/-!
### Factorization, with the recursion doing the work
-/

/--
**Finite-horizon factorization.**

With the prior fixed, the depth-`n` value depends only on the utility and
horizon *inside the reachable window*: histories no longer than `|h| + n`, and
horizon indices no larger than `|h| + n`.

Two agents may therefore differ arbitrarily outside the window and still agree
on it.  Unlike `Objective.value_congr`, this proof unfolds the recursion.
-/
public theorem value_eq_of_agree_on_window (ρ : Belief Action Obs)
    (ag₁ ag₂ : Agent Action Obs) (t : ℕ) :
    ∀ (n : ℕ) (h : History Action Obs),
      (∀ h' : History Action Obs, h'.length ≤ h.length + n →
        ag₁.utility h' = ag₂.utility h') →
      (∀ k ≤ h.length + n, ag₁.horizon t k = ag₂.horizon t k) →
      value ρ ag₁ t n h = value ρ ag₂ t n h := by
  intro n
  induction n with
  | zero =>
      intro h hu hw
      simp only [value]
      rw [hu h (by simp), hw h.length (by simp)]
  | succ n ih =>
      intro h hu hw
      have hstep : ∀ a : Action, ∀ o : Obs,
          value ρ ag₁ t n (h ++ [(a, o)]) = value ρ ag₂ t n (h ++ [(a, o)]) := by
        intro a o
        refine ih (h ++ [(a, o)]) (fun h' hh' => hu h' ?_) (fun k hk => hw k ?_)
        · simp only [List.length_append, List.length_cons, List.length_nil] at hh'
          omega
        · simp only [List.length_append, List.length_cons, List.length_nil] at hk
          omega
      have hfun :
          (fun a => ∑ o : Obs, ρ.cond h a o * value ρ ag₁ t n (h ++ [(a, o)])) =
            (fun a => ∑ o : Obs, ρ.cond h a o * value ρ ag₂ t n (h ++ [(a, o)])) := by
        funext a
        exact Finset.sum_congr rfl (fun o _ => by rw [hstep a o])
      simp only [value]
      rw [hu h (by simp), hw h.length (by simp), hfun]

/--
Once the horizon weighting vanishes from a point on, every value computed from a
history at least that long is zero.
-/
public theorem value_eq_zero_of_horizon_vanishes (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t m : ℕ)
    (hzero : ∀ k, m ≤ k → ag.horizon t k = 0) :
    ∀ (n : ℕ) (h : History Action Obs), m ≤ h.length →
      value ρ ag t n h = 0 := by
  intro n
  induction n with
  | zero =>
      intro h hm
      simp only [value, hzero h.length hm, zero_mul]
  | succ n ih =>
      intro h hm
      have hinner : ∀ a : Action,
          (∑ o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])) = 0 := by
        intro a
        refine Finset.sum_eq_zero (fun o _ => ?_)
        rw [ih (h ++ [(a, o)]) (by simp; omega), mul_zero]
      have hfun :
          (fun a => ∑ o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])) =
            (fun _ : Action => (0 : ℝ)) := funext hinner
      simp only [value, hzero h.length hm, zero_mul, zero_add, hfun]
      simp

/--
**The truncation is exact once the horizon vanishes past the window.**

If the horizon weighting is zero at every index from `|h| + n` on, then
deepening the recursion by one step changes nothing.  This is the condition
under which the finite-horizon form is the source's value rather than an
approximation of it, and it is why the truncation error is stated here instead
of being left implicit.
-/
public theorem truncation_exact (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (t : ℕ) :
    ∀ (n : ℕ) (h : History Action Obs),
      (∀ k, h.length + n ≤ k → ag.horizon t k = 0) →
      value ρ ag t n h = value ρ ag t (n + 1) h := by
  intro n
  induction n with
  | zero =>
      intro h hzero
      have h0 : value ρ ag t 0 h = 0 :=
        value_eq_zero_of_horizon_vanishes ρ ag t h.length
          (fun k hk => hzero k (by omega)) 0 h le_rfl
      have h1 : value ρ ag t 1 h = 0 :=
        value_eq_zero_of_horizon_vanishes ρ ag t h.length
          (fun k hk => hzero k (by omega)) 1 h le_rfl
      rw [h0, h1]
  | succ n ih =>
      intro h hzero
      have hstep : ∀ a : Action, ∀ o : Obs,
          value ρ ag t n (h ++ [(a, o)]) = value ρ ag t (n + 1) (h ++ [(a, o)]) := by
        intro a o
        refine ih (h ++ [(a, o)]) (fun k hk => hzero k ?_)
        simp only [List.length_append, List.length_cons, List.length_nil] at hk
        omega
      have hfun :
          (fun a => ∑ o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])) =
            (fun a => ∑ o : Obs, ρ.cond h a o * value ρ ag t (n + 1) (h ++ [(a, o)])) := by
        funext a
        exact Finset.sum_congr rfl (fun o _ => by rw [hstep a o])
      simp only [value, hfun]

end AISafetyAtlas.Wireheading.AgentEquations
