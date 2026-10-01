module

public import AISafetyAtlas.Wireheading.ValueBounds

/-!
# Bayesian mixtures of two environments

Ring and Orseau's *Arguments* for Statements 1 to 3 treat the value of an action
as a `P(DB)`-weighted average of its value under two hypotheses — a delusion box
is present, or it is not. `AISafetyAtlas.Wireheading.DelusionBox.MixesAt` carries
that as a named hypothesis, `mixesAt_zero` proves it at remaining depth zero, and
`Examples…not_mixesAt_one` proves it **false** at remaining depth one: equation
(3)'s maximum sits inside the recursion and a maximum does not commute with a
convex combination.

This module is what the argument needs instead.

## Why a fixed weight is the wrong object

A single weight `p` applied to every conditional is not a mixture of two
environments; it is a third environment that never learns. Carrying it through
one step of the recursion leaves a cross term
`p(1-p)·∑ₒ (ρbox(o) − ρfree(o))·(vbox(hao) − vfree(hao))` whose sign is not
determined, so neither the equality nor either inequality closes.

`posterior` is the weight that does update, and `mixtureBelief` is the mixture
taken at it. `mixtureBelief_cond_mul_posterior` is Bayes' rule in the form the
induction consumes, and it is what makes the cross term vanish.

## The two laws, and why print needs both

* `policyValue_mixture` — a **fixed policy's** value is exactly the posterior
  average of its value under the two environments. Equality, because no maximum
  intervenes.
* `value_mixture_le` — the **optimal** value is at most that average. The gap is
  the value of knowing which environment one is in.

Print uses an equality on both branches of its comparison. The upper bound is
what the `no` branch needs and the lower bound from a committed policy is what
the `yes` branch needs, and only one of the two is what print wrote.

Observations are finite here, which is the setting Ring and Orseau's delusion-box
construction lives in; the two laws are stated at `Fintype Obs` and nothing else
in the cluster is narrowed by that.
-/

namespace AISafetyAtlas.Wireheading.Mixture

open AISafetyAtlas.Wireheading.AgentEquations

variable {Action Obs : Type*}

/--
**The posterior weight on the first environment.** Print writes `P(DB)` once and
never updates it; this is the weight after `h`, which is what a mixture of two
environments actually carries. Division by zero is zero, so an unreachable
history gets weight zero on both sides and the laws below still hold there.
-/
@[expose] public noncomputable def posterior (p : ℝ) (ρbox ρfree : Belief Action Obs)
    (h : History Action Obs) : ℝ :=
  p * historyMass ρbox h /
    (p * historyMass ρbox h + (1 - p) * historyMass ρfree h)

/-- The Bayesian mixture of two environments at prior weight `p`. -/
@[expose] public noncomputable def mixtureBelief (p : ℝ)
    (ρbox ρfree : Belief Action Obs) : Belief Action Obs where
  cond := fun h a o =>
    posterior p ρbox ρfree h * ρbox.cond h a o
      + (1 - posterior p ρbox ρfree h) * ρfree.cond h a o

/-- The mixture's conditional, unfolded. -/
public theorem mixtureBelief_cond (p : ℝ) (ρbox ρfree : Belief Action Obs)
    (h : History Action Obs) (a : Action) (o : Obs) :
    (mixtureBelief p ρbox ρfree).cond h a o
      = posterior p ρbox ρfree h * ρbox.cond h a o
        + (1 - posterior p ρbox ρfree h) * ρfree.cond h a o := rfl

/-- **At the empty history the posterior is the prior.** Both masses are one, so
print's `P(DB)` and the weight this module carries agree exactly at the point a
comparison at the root is made. -/
public theorem posterior_nil (p : ℝ) (ρbox ρfree : Belief Action Obs) :
    posterior p ρbox ρfree [] = p := by
  simp [posterior, historyMass_nil]

section Bounds

variable {p : ℝ} {ρbox ρfree : Belief Action Obs}

/-- The posterior is a weight. -/
public theorem posterior_nonneg (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbox : ∀ h a o, 0 ≤ ρbox.cond h a o) (hfree : ∀ h a o, 0 ≤ ρfree.cond h a o)
    (h : History Action Obs) : 0 ≤ posterior p ρbox ρfree h := by
  apply div_nonneg (mul_nonneg hp0 (historyMass_nonneg hbox h))
  exact add_nonneg (mul_nonneg hp0 (historyMass_nonneg hbox h))
    (mul_nonneg (by linarith) (historyMass_nonneg hfree h))

/-- And it is at most one. -/
public theorem posterior_le_one (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbox : ∀ h a o, 0 ≤ ρbox.cond h a o) (hfree : ∀ h a o, 0 ≤ ρfree.cond h a o)
    (h : History Action Obs) : posterior p ρbox ρfree h ≤ 1 := by
  have hB := historyMass_nonneg hbox h
  have hF := historyMass_nonneg hfree h
  have hnum : 0 ≤ p * historyMass ρbox h := mul_nonneg hp0 hB
  have hrest : 0 ≤ (1 - p) * historyMass ρfree h := mul_nonneg (by linarith) hF
  rcases eq_or_lt_of_le (add_nonneg hnum hrest) with hd | hd
  · simp [posterior, ← hd]
  · rw [posterior, div_le_one hd]
    linarith

end Bounds

/-- Cancelling the mixture's own normaliser, including where it vanishes. -/
private theorem div_mul_div_cancel_nonneg {N D D' : ℝ} (hD : 0 < D) (hN : 0 ≤ N)
    (hD' : 0 ≤ D') (hND' : N ≤ D') : D' / D * (N / D') = N / D := by
  rcases eq_or_lt_of_le hD' with h | h
  · have hN0 : N = 0 := le_antisymm (h ▸ hND') hN
    simp [← h, hN0]
  · field_simp

/-- The arithmetic core of Bayes' rule, with the two masses abstract. -/
private theorem bayes_arith {B F b f p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hB : 0 ≤ B) (hF : 0 ≤ F) (hb : 0 ≤ b) (hf : 0 ≤ f) :
    (p * B / (p * B + (1 - p) * F) * b
        + (1 - p * B / (p * B + (1 - p) * F)) * f)
      * (p * (B * b) / (p * (B * b) + (1 - p) * (F * f)))
      = p * B / (p * B + (1 - p) * F) * b := by
  have h1p : 0 ≤ 1 - p := by linarith
  have hpB : 0 ≤ p * B := mul_nonneg hp0 hB
  have hqF : 0 ≤ (1 - p) * F := mul_nonneg h1p hF
  have hpBb : 0 ≤ p * (B * b) := mul_nonneg hp0 (mul_nonneg hB hb)
  have hqFf : 0 ≤ (1 - p) * (F * f) := mul_nonneg h1p (mul_nonneg hF hf)
  have hRHS : p * B / (p * B + (1 - p) * F) * b
      = p * (B * b) / (p * B + (1 - p) * F) := by
    rw [div_mul_eq_mul_div]
    ring_nf
  rcases eq_or_lt_of_le (add_nonneg hpB hqF) with hD | hD
  · have hpB0 : p * B = 0 := le_antisymm (by linarith) hpB
    have hpBb0 : p * (B * b) = 0 := by
      have hassoc : p * (B * b) = p * B * b := by ring
      rw [hassoc, hpB0, zero_mul]
    rw [hRHS, ← hD, hpBb0]
    simp
  · have hmix : p * B / (p * B + (1 - p) * F) * b
        + (1 - p * B / (p * B + (1 - p) * F)) * f
        = (p * (B * b) + (1 - p) * (F * f)) / (p * B + (1 - p) * F) := by
      field_simp
      ring
    rw [hmix, hRHS]
    exact div_mul_div_cancel_nonneg hD hpBb (add_nonneg hpBb hqFf) (by linarith)

/--
**Bayes' rule, in the form the induction consumes.** The mixture's probability of
the next observation, times the posterior after it, is the posterior now times
the first environment's probability. This is exactly what makes the cross term a
fixed weight leaves behind vanish.
-/
public theorem mixtureBelief_cond_mul_posterior {p : ℝ} {ρbox ρfree : Belief Action Obs}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbox : ∀ h a o, 0 ≤ ρbox.cond h a o) (hfree : ∀ h a o, 0 ≤ ρfree.cond h a o)
    (h : History Action Obs) (a : Action) (o : Obs) :
    (mixtureBelief p ρbox ρfree).cond h a o
        * posterior p ρbox ρfree (h ++ [(a, o)])
      = posterior p ρbox ρfree h * ρbox.cond h a o := by
  simp only [mixtureBelief_cond, posterior, historyMass_append_singleton]
  exact bayes_arith hp0 hp1 (historyMass_nonneg hbox h) (historyMass_nonneg hfree h)
    (hbox h a o) (hfree h a o)

/-- The complementary half: the same product against the second environment. -/
public theorem mixtureBelief_cond_mul_one_sub_posterior {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbox : ∀ h a o, 0 ≤ ρbox.cond h a o) (hfree : ∀ h a o, 0 ≤ ρfree.cond h a o)
    (h : History Action Obs) (a : Action) (o : Obs) :
    (mixtureBelief p ρbox ρfree).cond h a o
        * (1 - posterior p ρbox ρfree (h ++ [(a, o)]))
      = (1 - posterior p ρbox ρfree h) * ρfree.cond h a o := by
  have hb := mixtureBelief_cond_mul_posterior hp0 hp1 hbox hfree h a o
  have : (mixtureBelief p ρbox ρfree).cond h a o
      * (1 - posterior p ρbox ρfree (h ++ [(a, o)]))
      = (mixtureBelief p ρbox ρfree).cond h a o
        - (mixtureBelief p ρbox ρfree).cond h a o
          * posterior p ρbox ρfree (h ++ [(a, o)]) := by ring
  rw [this, hb, mixtureBelief_cond]
  ring

/-- The mixture of two nonnegative beliefs is nonnegative. -/
public theorem mixtureBelief_cond_nonneg {p : ℝ} {ρbox ρfree : Belief Action Obs}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbox : ∀ h a o, 0 ≤ ρbox.cond h a o) (hfree : ∀ h a o, 0 ≤ ρfree.cond h a o)
    (h : History Action Obs) (a : Action) (o : Obs) :
    0 ≤ (mixtureBelief p ρbox ρfree).cond h a o := by
  have h0 := posterior_nonneg hp0 hp1 hbox hfree h
  have h1 := posterior_le_one hp0 hp1 hbox hfree h
  exact add_nonneg (mul_nonneg h0 (hbox h a o))
    (mul_nonneg (by linarith) (hfree h a o))

/--
**A fixed policy's value.** Equation (2)'s sum with the policy's own action in
place of equation (3)'s maximum.

Print has no such object, and the repair of its argument needs one: a committed
policy's value is *linear* in the belief, where the optimal value is only
sub-linear. That is the whole difference between the two laws below.
-/
@[expose] public noncomputable def policyValue (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (π : History Action Obs → Action) (t : ℕ) :
    ℕ → History Action Obs → ℝ
  | 0, h => ag.horizon t h.length * ag.utility h
  | n + 1, h =>
      ag.horizon t h.length * ag.utility h +
        ∑' o : Obs, ρ.cond h (π h) o * policyValue ρ ag π t n (h ++ [(π h, o)])

/-- Depth zero discards the tail, as equation (3)'s truncation does. -/
public theorem policyValue_zero (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (π : History Action Obs → Action) (t : ℕ) (h : History Action Obs) :
    policyValue ρ ag π t 0 h = ag.horizon t h.length * ag.utility h := rfl

/--
**A committed policy's value is exactly the posterior average.** No maximum
intervenes, so the linearity print assumes really does hold — for a fixed
policy, and only for a fixed policy.
-/
public theorem policyValue_mixture [Fintype Obs] {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbox : ∀ h a o, 0 ≤ ρbox.cond h a o) (hfree : ∀ h a o, 0 ≤ ρfree.cond h a o)
    (ag : Agent Action Obs) (π : History Action Obs → Action) (t : ℕ) :
    ∀ (n : ℕ) (h : History Action Obs),
      policyValue (mixtureBelief p ρbox ρfree) ag π t n h
        = posterior p ρbox ρfree h * policyValue ρbox ag π t n h
          + (1 - posterior p ρbox ρfree h) * policyValue ρfree ag π t n h
  | 0, h => by simp only [policyValue_zero]; ring
  | n + 1, h => by
      have key : ∀ o : Obs,
          (mixtureBelief p ρbox ρfree).cond h (π h) o
              * policyValue (mixtureBelief p ρbox ρfree) ag π t n (h ++ [(π h, o)])
            = posterior p ρbox ρfree h
                * (ρbox.cond h (π h) o
                  * policyValue ρbox ag π t n (h ++ [(π h, o)]))
              + (1 - posterior p ρbox ρfree h)
                * (ρfree.cond h (π h) o
                  * policyValue ρfree ag π t n (h ++ [(π h, o)])) := by
        intro o
        have expand : ∀ X q vb vf : ℝ,
            X * (q * vb + (1 - q) * vf) = X * q * vb + X * (1 - q) * vf := by
          intros; ring
        rw [policyValue_mixture hp0 hp1 hbox hfree ag π t n (h ++ [(π h, o)]), expand,
          mixtureBelief_cond_mul_posterior hp0 hp1 hbox hfree h (π h) o,
          mixtureBelief_cond_mul_one_sub_posterior hp0 hp1 hbox hfree h (π h) o]
        ring
      simp only [policyValue, tsum_fintype]
      rw [Finset.sum_congr rfl (fun o _ => key o), Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- **A committed policy never beats the optimum.** Equation (3)'s maximum
dominates whatever action the policy takes. -/
public theorem policyValue_le_value [Fintype Obs] [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (π : History Action Obs → Action) (t : ℕ) :
    ∀ (n : ℕ) (h : History Action Obs), policyValue ρ ag π t n h ≤ value ρ ag t n h
  | 0, _ => le_of_eq rfl
  | n + 1, h => by
      rw [policyValue, value_succ]
      have hstep :
          ∑' o : Obs, ρ.cond h (π h) o * policyValue ρ ag π t n (h ++ [(π h, o)])
            ≤ actionValue ρ ag t n h (π h) := by
        rw [actionValue_eq_sum, tsum_fintype]
        exact Finset.sum_le_sum fun o _ =>
          mul_le_mul_of_nonneg_left
            (policyValue_le_value hρ ag hu π t n (h ++ [(π h, o)])) (hρ.nonneg _ _ _)
      have hle := hstep.trans (le_ciSup (actionValue_bddAbove hρ ag hu t n h) (π h))
      linarith

/--
**The optimal value is at most the posterior average.** This is the direction
print's decomposition actually has, and the gap is the value of knowing which
environment one is in — the quantity `Examples…not_mixesAt_one` exhibits.

Print uses an equality. On the branch where print needs a *lower* bound this
inequality points the wrong way, which is why the repair goes through
`policyValue_mixture` at a committed policy instead.
-/
public theorem value_mixture_le [Fintype Obs] [Nonempty Action] {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t : ℕ) :
    ∀ (n : ℕ) (h : History Action Obs),
      value (mixtureBelief p ρbox ρfree) ag t n h
        ≤ posterior p ρbox ρfree h * value ρbox ag t n h
          + (1 - posterior p ρbox ρfree h) * value ρfree ag t n h
  | 0, h => le_of_eq (by simp only [value]; ring)
  | n + 1, h => by
      have hq0 := posterior_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h
      have hq1 := posterior_le_one hp0 hp1 hboxS.nonneg hfreeS.nonneg h
      have hq1' : (0 : ℝ) ≤ 1 - posterior p ρbox ρfree h := by linarith
      have hsup : (⨆ a, actionValue (mixtureBelief p ρbox ρfree) ag t n h a)
          ≤ posterior p ρbox ρfree h * (⨆ a, actionValue ρbox ag t n h a)
            + (1 - posterior p ρbox ρfree h) * (⨆ a, actionValue ρfree ag t n h a) := by
        apply ciSup_le
        intro a
        have hstep : actionValue (mixtureBelief p ρbox ρfree) ag t n h a
            ≤ posterior p ρbox ρfree h * actionValue ρbox ag t n h a
              + (1 - posterior p ρbox ρfree h) * actionValue ρfree ag t n h a := by
          rw [actionValue_eq_sum, actionValue_eq_sum, actionValue_eq_sum,
            Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_le_sum fun o _ => ?_
          have hmono := mul_le_mul_of_nonneg_left
            (value_mixture_le hp0 hp1 hboxS hfreeS ag hu t n (h ++ [(a, o)]))
            (mixtureBelief_cond_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h a o)
          refine hmono.trans (le_of_eq ?_)
          have expand : ∀ X q vb vf : ℝ,
              X * (q * vb + (1 - q) * vf) = X * q * vb + X * (1 - q) * vf := by
            intros; ring
          rw [expand,
            mixtureBelief_cond_mul_posterior hp0 hp1 hboxS.nonneg hfreeS.nonneg h a o,
            mixtureBelief_cond_mul_one_sub_posterior hp0 hp1 hboxS.nonneg hfreeS.nonneg h a o]
          ring
        refine hstep.trans ?_
        gcongr
        · exact le_ciSup (actionValue_bddAbove hboxS ag hu t n h) a
        · exact le_ciSup (actionValue_bddAbove hfreeS ag hu t n h) a
      rw [value_succ, value_succ, value_succ]
      nlinarith [hsup, hq0, hq1']

/-- The mixture of two subprobabilities is one. -/
public theorem mixtureBelief_isSubprobability {p : ℝ} {ρbox ρfree : Belief Action Obs}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability) :
    (mixtureBelief p ρbox ρfree).IsSubprobability where
  nonneg h a o := mixtureBelief_cond_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h a o
  summable h a :=
    ((hboxS.summable h a).mul_left _).add ((hfreeS.summable h a).mul_left _)
  total_le_one h a := by
    have hq0 := posterior_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h
    have hq1 := posterior_le_one hp0 hp1 hboxS.nonneg hfreeS.nonneg h
    have hb := hboxS.total_le_one h a
    have hf := hfreeS.total_le_one h a
    have hbn : 0 ≤ ∑' o, ρbox.cond h a o := tsum_nonneg fun o => hboxS.nonneg h a o
    have hfn : 0 ≤ ∑' o, ρfree.cond h a o := tsum_nonneg fun o => hfreeS.nonneg h a o
    have hsplit : ∑' o, (mixtureBelief p ρbox ρfree).cond h a o
        = posterior p ρbox ρfree h * (∑' o, ρbox.cond h a o)
          + (1 - posterior p ρbox ρfree h) * (∑' o, ρfree.cond h a o) := by
      rw [show (fun o => (mixtureBelief p ρbox ρfree).cond h a o)
            = fun o => posterior p ρbox ρfree h * ρbox.cond h a o
              + (1 - posterior p ρbox ρfree h) * ρfree.cond h a o from rfl,
        Summable.tsum_add ((hboxS.summable h a).mul_left _) ((hfreeS.summable h a).mul_left _),
        tsum_mul_left, tsum_mul_left]
    rw [hsplit]
    nlinarith

/--
**Equation (2)'s bound at the mixture.** The action-level form of
`value_mixture_le`, which is what the comparison in Ring and Orseau's
*Arguments* actually compares.
-/
public theorem actionValue_mixture_le [Fintype Obs] [Nonempty Action] {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t n : ℕ)
    (h : History Action Obs) (a : Action) :
    actionValue (mixtureBelief p ρbox ρfree) ag t n h a
      ≤ posterior p ρbox ρfree h * actionValue ρbox ag t n h a
        + (1 - posterior p ρbox ρfree h) * actionValue ρfree ag t n h a := by
  rw [actionValue_eq_sum, actionValue_eq_sum, actionValue_eq_sum,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun o _ => ?_
  have hmono := mul_le_mul_of_nonneg_left
    (value_mixture_le hp0 hp1 hboxS hfreeS ag hu t n (h ++ [(a, o)]))
    (mixtureBelief_cond_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h a o)
  refine hmono.trans (le_of_eq ?_)
  have expand : ∀ X q vb vf : ℝ,
      X * (q * vb + (1 - q) * vf) = X * q * vb + X * (1 - q) * vf := by
    intros; ring
  rw [expand,
    mixtureBelief_cond_mul_posterior hp0 hp1 hboxS.nonneg hfreeS.nonneg h a o,
    mixtureBelief_cond_mul_one_sub_posterior hp0 hp1 hboxS.nonneg hfreeS.nonneg h a o]
  ring

/-- Equation (2) at a committed policy: the observation sum under the action the
policy takes. -/
@[expose] public noncomputable def policyActionValue (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (π : History Action Obs → Action) (t n : ℕ)
    (h : History Action Obs) : ℝ :=
  ∑' o : Obs, ρ.cond h (π h) o * policyValue ρ ag π t n (h ++ [(π h, o)])

/-- The committed recursion, one step, in terms of it. -/
public theorem policyValue_succ (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (π : History Action Obs → Action) (t n : ℕ) (h : History Action Obs) :
    policyValue ρ ag π t (n + 1) h
      = ag.horizon t h.length * ag.utility h + policyActionValue ρ ag π t n h := rfl

/-- **A committed policy's action value mixes exactly**, which is the lower
bound the `yes` branch of print's comparison needs and the optimal value cannot
supply. -/
public theorem policyActionValue_mixture [Fintype Obs] {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hbox : ∀ h a o, 0 ≤ ρbox.cond h a o) (hfree : ∀ h a o, 0 ≤ ρfree.cond h a o)
    (ag : Agent Action Obs) (π : History Action Obs → Action) (t n : ℕ)
    (h : History Action Obs) :
    policyActionValue (mixtureBelief p ρbox ρfree) ag π t n h
      = posterior p ρbox ρfree h * policyActionValue ρbox ag π t n h
        + (1 - posterior p ρbox ρfree h) * policyActionValue ρfree ag π t n h := by
  have h1 := policyValue_mixture hp0 hp1 hbox hfree ag π t (n + 1) h
  rw [policyValue_succ, policyValue_succ, policyValue_succ] at h1
  have hring : posterior p ρbox ρfree h
        * (ag.horizon t h.length * ag.utility h + policyActionValue ρbox ag π t n h)
      + (1 - posterior p ρbox ρfree h)
        * (ag.horizon t h.length * ag.utility h + policyActionValue ρfree ag π t n h)
      = ag.horizon t h.length * ag.utility h
        + (posterior p ρbox ρfree h * policyActionValue ρbox ag π t n h
          + (1 - posterior p ρbox ρfree h) * policyActionValue ρfree ag π t n h) := by
    ring
  rw [hring] at h1
  linarith

/-- A committed policy's action value never beats equation (2) at its own
action. -/
public theorem policyActionValue_le_actionValue [Fintype Obs] [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (π : History Action Obs → Action) (t n : ℕ)
    (h : History Action Obs) :
    policyActionValue ρ ag π t n h ≤ actionValue ρ ag t n h (π h) := by
  rw [policyActionValue, actionValue_eq_sum, tsum_fintype]
  exact Finset.sum_le_sum fun o _ =>
    mul_le_mul_of_nonneg_left
      (policyValue_le_value hρ ag hu π t n (h ++ [(π h, o)])) (hρ.nonneg _ _ _)

end AISafetyAtlas.Wireheading.Mixture
