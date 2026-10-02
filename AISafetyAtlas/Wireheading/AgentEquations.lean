module

public import AISafetyAtlas.Wireheading.Objective
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.ConditionallyCompleteLattice.Finset
public import Mathlib.Topology.Algebra.InfiniteSum.Basic
public import Mathlib.Topology.MetricSpace.Basic

/-!
# Ring and Orseau's agent equations, at finite horizon

`AISafetyAtlas.Wireheading.Objective` isolates the observation that Ring and
Orseau's four agents differ only in their utility and horizon functions, but it
does so over an abstract `value` that has nothing to do with their value
equations.  This module writes those equations down.

## The source equations

Ring and Orseau, *Delusion, Survival, and Intelligent Agents*, AGI 2011, §2.

**Which text this was checked against, corrected on 2026-09-09.** The Springer
chapter (LNAI 6830, pp. 11–20) is closed: OpenAlex reports it with no repository
copy and Unpaywall reports no open location. What has been read is the **author
deposit on HAL**, `hal-01000226v1`, sha256
`a207ab73c87896e0663e4998906aa4c4bcef6d93a43d8e29ebc3cdb81e32ea6d` in the
project's literature directory, manifest `SOURCES-2026-09-09-wireheading.md`.
It has **not** been compared with the publisher's typeset chapter, and
pagination differs.

**Two author drafts exist and they index differently.** An earlier version of
this paragraph said that "the published paper" indexes the selected action at
`|h| + 1` while "the AGI-2011 conference draft" indexes it at `|h|`. That was
withdrawn on the first reading, because the HAL deposit *is* the AGI-11 paper
and it uses `a_{t_h}` with `t_h = |h| + 1` stated explicitly. A second author
draft, sha256 `ee44df16375d04f4e714c99d24fc1344bef6f324338b7b6c5567182fd6ac0b9f`
(11 pp. of paper against the HAL copy's 10, created 2011-03-07, a distinct draft
at 0.83 token-level similarity), was pinned later the same day, and it writes
`a_{|h|}` and defines no `t_h`. So both conventions are real and each belongs to
a different draft; what was never established — and is still not — is which one
the **Springer chapter** prints, since that text remains closed. Equations (2)
and (3) are character-identical across the two drafts. Nothing below moves
either way: `t` is a parameter here, so both indexings instantiate it. The
display uses the `|h|` form.

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
* `bestAction` and `bestAction_max`: equation (1), at the attainment the source
  presupposes by writing an argmax rather than at a finite action set.
* `attains_of_fintype` and `value_succ_eq_sup'`: the finite readings, so the
  signatures this module carried before 2026-09-13 are instances of these.

The *ValueBounds* module extends this namespace with the bounds
that make the two unconditional operators above denote at print's hypotheses,
and with the infinite-horizon limit the printed equations never supply:
`infiniteValue`, `tendsto_value_infiniteValue`, the certified truncation error
`value_error_le_tail`, and `infiniteValue_eq`, which is equation (3) at that
limit.  It claims no attainment.

## Explicit non-claims

* **Not AIXI.**  `ρ` is an arbitrary conditional weighting, not a universal
  prior; nothing here is about Solomonoff induction or incomputability.
* **Not a probability measure.**  `ρ.cond` is a real-valued weight with no
  normalization or nonnegativity assumed.  Equation (2) is written as a sum over
  observations, not as an expectation.
* **No finiteness on the observation type.**  Since 2026-09-13 the sum is
  unconditional over an **arbitrary** `Obs`, which is the source's own
  quantifier: its setup fixes only `a ∈ 𝒜` and `o ∈ 𝒪` and bounds neither.
  No summability hypothesis was added to buy this — the three theorems below
  need only congruence and the vanishing case, both of which hold of the
  unconditional sum.  `actionValue_eq_sum` recovers the finite sum at a
  `Fintype`, so the previous signature is an instance of this one.
  **The implication this rested on is now proved.** `∑'` is Mathlib's
  unconditional sum, which is `0` by convention at a family that is not
  summable, so until 2026-09-13 the claim that the value here is the source's
  value was a statement about the source's hypotheses that the tree did not
  carry. `actionValue_summable` carries it: at
  `Belief.IsSubprobability` and `|u| ≤ 1` — print's `ρ` a probability and its
  `u : ℋ → [0,1]` — the observation family is summable at every depth, so the
  sum denotes. `actionValue_eq_sum` still recovers the finite case. At a family
  outside those hypotheses this module says something that is not the source's
  equation, and nothing here claims otherwise.
* **No finiteness on the action type either.**  Since 2026-09-13 `value` takes
  the supremum over an **arbitrary** `Action`, which is again the source's own
  quantifier: it bounds `𝒜` nowhere and then writes *argmax* in (1) and *max*
  in (3).  Attainment is the source's presupposition, and it is carried as the
  hypothesis `Attains` rather than bought with a `Fintype` instance the source
  does not have.  `attains_of_fintype` discharges it at a finite action set and
  `value_succ_eq_sup'` recovers the finite maximum, so the previous signatures
  are instances of these.  No hypothesis was added to `value`, `actionValue`,
  `value_eq_of_agree_on_window`, `value_eq_zero_of_horizon_vanishes` or
  `truncation_exact`: none of them needs the maximum attained, or the action
  type inhabited, and four of them never needed either.
  **The implication this rested on is now proved, and one gap survives it.**
  `⨆` is Mathlib's conditional supremum, which is `0` by convention at a family
  that is empty or unbounded above.  `actionValue_bddAbove` shows
  the family is bounded above at `Belief.IsSubprobability` and `|u| ≤ 1`, which
  are print's own conditions, so the supremum denotes rather than defaulting;
  `value_succ_eq_sup'` still recovers the finite case.  **Bounded is not
  attained.**  Where the maximum is not attained, equation (3) here is a
  supremum and the source's is a maximum, and those differ — which is why
  `Attains` remains a hypothesis and is not derived from the bound.
* **Unbounded utility codomain.** The source uses utilities in `[0,1]`;
  `Agent.utility` is real-valued without a range invariant. The recursive
  equalities and locality proof remain valid at this more general type.
* **No infinite-horizon limit**, hence no convergence or contraction argument.
* **Not the delusion box, and not the four agents.**  Both are in
  `AISafetyAtlas.Wireheading.DelusionBox`, which is built on this module.  The
  paper's Statements 1 to 7 are informal arguments rather than theorems; three
  of them are proved there with the premises their arguments use supplied as
  named hypotheses, and four of them are not proved anywhere.

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

/--
**The history mass generated by a belief.** The product of successive
conditionals along `h`.

Print's `ρ(h)` is this quantity when `ρ` is a prior over programs and `ρ(h)` is
the total mass of programs consistent with `h`. Here it is the same unfolding
at the observation-conditional the atlas has, which is the cheap half of
recovering Ring and Orseau's knowledge-seeking agent: the utility `u(h) = -ρ(h)`
must be the agent's own `ρ`, not an independent parameter.
-/
@[expose] public def historyMass {Action Obs : Type*} (ρ : Belief Action Obs) :
    History Action Obs → ℝ :=
  fun h => go h []
where
  go : History Action Obs → History Action Obs → ℝ
    | [], _pre => 1
    | p :: rest, pre => ρ.cond pre p.1 p.2 * go rest (pre ++ [p])

/-- The empty history has mass one. -/
public theorem historyMass_nil {Action Obs : Type*} (ρ : Belief Action Obs) :
    historyMass ρ [] = 1 :=
  rfl

/-- The unfolding `historyMass` is defined by, with the prefix exposed. -/
private theorem historyMass_go_append {Action Obs : Type*} (ρ : Belief Action Obs)
    (q : Action × Obs) :
    ∀ (l pre : History Action Obs),
      historyMass.go ρ (l ++ [q]) pre
        = historyMass.go ρ l pre * ρ.cond (pre ++ l) q.1 q.2
  | [], pre => by simp [historyMass.go]
  | x :: rest, pre => by
      simp only [List.cons_append, historyMass.go]
      rw [historyMass_go_append ρ q rest (pre ++ [x])]
      simp [mul_assoc]

/-- **The mass of an extended history factors.** Print's `ρ(h)` is a product of
successive conditionals, so one more step multiplies by one more conditional.
This is what makes a posterior weight update multiplicatively. -/
public theorem historyMass_append_singleton {Action Obs : Type*} (ρ : Belief Action Obs)
    (h : History Action Obs) (a : Action) (o : Obs) :
    historyMass ρ (h ++ [(a, o)]) = historyMass ρ h * ρ.cond h a o := by
  simpa [historyMass] using historyMass_go_append ρ (a, o) h []

/-- A nonnegative belief has nonnegative history mass. -/
public theorem historyMass_nonneg {Action Obs : Type*} {ρ : Belief Action Obs}
    (hρ : ∀ h a o, 0 ≤ ρ.cond h a o) (h : History Action Obs) :
    0 ≤ historyMass ρ h := by
  suffices hgo : ∀ (l pre : History Action Obs), 0 ≤ historyMass.go ρ l pre by
    exact hgo h []
  intro l
  induction l with
  | nil => intro pre; simp [historyMass.go]
  | cons x rest ih =>
      intro pre
      exact mul_nonneg (hρ _ _ _) (ih _)

/-- A one-step history has mass equal to the first conditional. -/
public theorem historyMass_singleton {Action Obs : Type*} (ρ : Belief Action Obs)
    (a : Action) (o : Obs) :
    historyMass ρ [(a, o)] = ρ.cond [] a o := by
  simp [historyMass, historyMass.go]

variable {Action Obs : Type*}

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
        ⨆ a : Action, ∑' o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])

/-- Equation (2): the value of an action is the weighted sum over observations
of the values of the resulting histories. -/
@[expose] public noncomputable def actionValue (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t n : ℕ) (h : History Action Obs) (a : Action) : ℝ :=
  ∑' o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])

/--
**The finite reading is recovered.** At a `Fintype` of observations the
unconditional sum is the finite one, so every statement in this module is the
printed equation in the case the source's own examples live in.

This is what makes dropping `[Fintype Obs]` a widening rather than a different
claim: the old signature is the instance, and the lemma is the instantiation.
-/
public theorem actionValue_eq_sum [Fintype Obs] (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t n : ℕ) (h : History Action Obs) (a : Action) :
    actionValue ρ ag t n h a =
      ∑ o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)]) :=
  tsum_fintype _

/-- Equation (3), restated in terms of `actionValue`. -/
public theorem value_succ (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (t n : ℕ) (h : History Action Obs) :
    value ρ ag t (n + 1) h =
      ag.horizon t h.length * ag.utility h +
        ⨆ a : Action, actionValue ρ ag t n h a := rfl

/--
**The finite reading of the maximum is recovered.** At a `Fintype` of actions the
supremum is the maximum over `Finset.univ`, which is the form equation (3) is
written in and the form this module carried before 2026-09-13.

This is what makes dropping `[Fintype Action]` a widening rather than a different
claim: the old signature is the instance, and the lemma is the instantiation.
-/
public theorem value_succ_eq_sup' [Fintype Action] [Nonempty Action]
    (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t n : ℕ) (h : History Action Obs) :
    value ρ ag t (n + 1) h =
      ag.horizon t h.length * ag.utility h +
        (Finset.univ : Finset Action).sup' Finset.univ_nonempty
          (actionValue ρ ag t n h) := by
  rw [value_succ, Finset.sup'_univ_eq_ciSup]

/--
**The presupposition equation (1) makes by writing an argmax**: that the maximum
over the action set is attained.

The source bounds `𝒜` nowhere — its setup fixes only `a ∈ 𝒜` and `o ∈ 𝒪` — and
then writes *argmax* in (1) and *max* in (3). Attainment is therefore print's own
assumption, carried here as a hypothesis rather than bought with a `Fintype`
instance the source does not have. It is strictly weaker: `attains_of_fintype`
discharges it at a finite action set, and nothing else does.
-/
@[expose] public def Attains (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (t n : ℕ) (h : History Action Obs) : Prop :=
  ∃ a : Action, ∀ b : Action,
    actionValue ρ ag t n h b ≤ actionValue ρ ag t n h a

/-- A finite action set attains its maximum, which is the case the source's own
examples live in and the case this module carried before 2026-09-13. -/
public theorem attains_of_fintype [Fintype Action] [Nonempty Action]
    (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t n : ℕ) (h : History Action Obs) :
    Attains ρ ag t n h := by
  obtain ⟨a, -, ha⟩ :=
    (Finset.univ : Finset Action).exists_mem_eq_sup' Finset.univ_nonempty
      (actionValue ρ ag t n h)
  exact ⟨a, fun b => ha ▸ Finset.le_sup' _ (Finset.mem_univ b)⟩

/-- Equation (1): an action attaining the maximum action value. -/
@[expose] public noncomputable def bestAction (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t n : ℕ) (h : History Action Obs)
    (hat : Attains ρ ag t n h) : Action := hat.choose

/-- The chosen action is maximal, which is what equation (1) asserts. -/
public theorem bestAction_max (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (t n : ℕ) (h : History Action Obs) (hat : Attains ρ ag t n h) (a : Action) :
    actionValue ρ ag t n h a ≤
      actionValue ρ ag t n h (bestAction ρ ag t n h hat) :=
  hat.choose_spec a

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
          (fun a => ∑' o : Obs, ρ.cond h a o * value ρ ag₁ t n (h ++ [(a, o)])) =
            (fun a => ∑' o : Obs, ρ.cond h a o * value ρ ag₂ t n (h ++ [(a, o)])) := by
        funext a
        exact tsum_congr (fun o => by rw [hstep a o])
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
          (∑' o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])) = 0 := by
        intro a
        refine (tsum_congr (fun o => ?_)).trans tsum_zero
        rw [ih (h ++ [(a, o)]) (by simp; omega), mul_zero]
      have hfun :
          (fun a => ∑' o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])) =
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
          (fun a => ∑' o : Obs, ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])) =
            (fun a => ∑' o : Obs, ρ.cond h a o * value ρ ag t (n + 1) (h ++ [(a, o)])) := by
        funext a
        exact tsum_congr (fun o => by rw [hstep a o])
      simp only [value, hfun]

end AISafetyAtlas.Wireheading.AgentEquations
