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

The first statements of the laws are at `Fintype Obs`. The tsum forms at the
end of the module drop that, as print's eq. (2) has no finiteness, and the
`infinite…` forms carry the laws to the infinite-horizon value.
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


/-!
## The laws at an arbitrary observation type

Ring and Orseau, AGI 2011, eq. (2) sums over `o ∈ 𝒪` with no finiteness, and the
source card S11 records no finiteness or cardinality bound on `𝒜` or `𝒪`. The
declarations below are the laws above with `[Fintype Obs]` removed: the
observation sums are genuine `tsum`s, made to denote by bounded integrands
(`abs_policyValue_le_horizonBudget`, `actionValue_summable`) under print's own
probability (`Belief.IsSubprobability`) and utility range (`|u| ≤ 1`).

**Scope against the finite laws.** These need `IsSubprobability` and `|u| ≤ 1`
where `policyValue_mixture` and `policyActionValue_mixture` needed only
nonnegative conditionals, so neither form contains the other: the finite laws are
wider on the utility axis at a finite `Obs`, these are wider on the observation
axis. Both hypotheses are print's own, and every consumer already carries them.
-/

section ArbitraryObs

/-- A committed policy's value is nonnegative when every weighted utility is. -/
public theorem policyValue_nonneg {ρ : Belief Action Obs} (hρ : ∀ h a o, 0 ≤ ρ.cond h a o)
    (ag : Agent Action Obs) (π : History Action Obs → Action) (t : ℕ)
    (hwu : ∀ h : History Action Obs, 0 ≤ ag.horizon t h.length * ag.utility h) :
    ∀ (n : ℕ) (h : History Action Obs), 0 ≤ policyValue ρ ag π t n h
  | 0, h => hwu h
  | n + 1, h => by
      rw [policyValue_succ]
      exact add_nonneg (hwu h) (tsum_nonneg fun _ =>
        mul_nonneg (hρ _ _ _) (policyValue_nonneg hρ ag π t hwu n _))

/-- And so is its action value. -/
public theorem policyActionValue_nonneg {ρ : Belief Action Obs}
    (hρ : ∀ h a o, 0 ≤ ρ.cond h a o) (ag : Agent Action Obs)
    (π : History Action Obs → Action) (t : ℕ)
    (hwu : ∀ h : History Action Obs, 0 ≤ ag.horizon t h.length * ag.utility h)
    (n : ℕ) (h : History Action Obs) : 0 ≤ policyActionValue ρ ag π t n h :=
  tsum_nonneg fun _ => mul_nonneg (hρ _ _ _) (policyValue_nonneg hρ ag π t hwu n _)

/-- A committed policy's finite-depth value is bounded by the absolute horizon
budget, with no finiteness of the observation type and no horizon summability. -/
public theorem abs_policyValue_le_horizonBudget {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (π : History Action Obs → Action) (t n : ℕ) (h : History Action Obs) :
    |policyValue ρ ag π t n h| ≤ horizonBudget ag t n h.length := by
  induction n generalizing h with
  | zero =>
    simpa [policyValue, horizonBudget, abs_mul] using
      mul_le_mul_of_nonneg_left (hu h) (abs_nonneg (ag.horizon t h.length))
  | succ n ih =>
    have hb := horizonBudget_nonneg ag t n (h.length + 1)
    have hs : |policyActionValue ρ ag π t n h| ≤ horizonBudget ag t n (h.length + 1) := by
      apply hρ.abs_tsum_mul_le h (π h) hb
      intro o
      simpa using ih (h ++ [(π h, o)])
    rw [policyValue_succ]
    change _ ≤ |ag.horizon t h.length| + horizonBudget ag t n (h.length + 1)
    exact (abs_add_le _ _).trans (add_le_add
      (by simpa [abs_mul] using
        mul_le_mul_of_nonneg_left (hu h) (abs_nonneg (ag.horizon t h.length))) hs)

private theorem policyValue_summable {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (π : History Action Obs → Action) (t n : ℕ) (h : History Action Obs) (a : Action) :
    Summable (fun o ↦ ρ.cond h a o * policyValue ρ ag π t n (h ++ [(a, o)])) :=
  hρ.summable_mul h a (b := horizonBudget ag t n (h.length + 1)) fun o => by
    simpa using abs_policyValue_le_horizonBudget hρ ag hu π t n (h ++ [(a, o)])

/-- **`policyValue_mixture` at an arbitrary observation type.** A committed
policy's value under the Bayesian mixture is exactly the posterior average of its
values under the two environments. -/
public theorem policyValue_mixture_tsum {p : ℝ} {ρbox ρfree : Belief Action Obs}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (π : History Action Obs → Action) (t : ℕ) :
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
        rw [policyValue_mixture_tsum hp0 hp1 hboxS hfreeS ag hu π t n (h ++ [(π h, o)]),
          expand,
          mixtureBelief_cond_mul_posterior hp0 hp1 hboxS.nonneg hfreeS.nonneg h (π h) o,
          mixtureBelief_cond_mul_one_sub_posterior hp0 hp1 hboxS.nonneg hfreeS.nonneg h
            (π h) o]
        ring
      have hsum : policyActionValue (mixtureBelief p ρbox ρfree) ag π t n h
          = posterior p ρbox ρfree h * policyActionValue ρbox ag π t n h
            + (1 - posterior p ρbox ρfree h) * policyActionValue ρfree ag π t n h := by
        simp only [policyActionValue]
        rw [tsum_congr key,
          Summable.tsum_add ((policyValue_summable hboxS ag hu π t n h (π h)).mul_left _)
            ((policyValue_summable hfreeS ag hu π t n h (π h)).mul_left _),
          tsum_mul_left, tsum_mul_left]
      rw [policyValue_succ, policyValue_succ, policyValue_succ, hsum]
      ring

/-- **`policyValue_le_value` at an arbitrary observation type.** -/
public theorem policyValue_le_value_tsum [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (π : History Action Obs → Action) (t : ℕ) :
    ∀ (n : ℕ) (h : History Action Obs), policyValue ρ ag π t n h ≤ value ρ ag t n h
  | 0, _ => le_of_eq rfl
  | n + 1, h => by
      rw [policyValue, value_succ]
      have hstep :
          ∑' o : Obs, ρ.cond h (π h) o * policyValue ρ ag π t n (h ++ [(π h, o)])
            ≤ actionValue ρ ag t n h (π h) :=
        Summable.tsum_le_tsum (fun o => mul_le_mul_of_nonneg_left
            (policyValue_le_value_tsum hρ ag hu π t n (h ++ [(π h, o)])) (hρ.nonneg _ _ _))
          (policyValue_summable hρ ag hu π t n h (π h))
          (actionValue_summable hρ ag hu t n h (π h))
      have hle := hstep.trans (le_ciSup (actionValue_bddAbove hρ ag hu t n h) (π h))
      linarith

/-- One step of the optimal-value bound, from the bound one level down. -/
private theorem actionValue_mixture_le_of_value [Nonempty Action] {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t n : ℕ)
    (h : History Action Obs) (a : Action)
    (hv : ∀ o : Obs, value (mixtureBelief p ρbox ρfree) ag t n (h ++ [(a, o)])
        ≤ posterior p ρbox ρfree (h ++ [(a, o)]) * value ρbox ag t n (h ++ [(a, o)])
          + (1 - posterior p ρbox ρfree (h ++ [(a, o)]))
            * value ρfree ag t n (h ++ [(a, o)])) :
    actionValue (mixtureBelief p ρbox ρfree) ag t n h a
      ≤ posterior p ρbox ρfree h * actionValue ρbox ag t n h a
        + (1 - posterior p ρbox ρfree h) * actionValue ρfree ag t n h a := by
  have hsplit : posterior p ρbox ρfree h * actionValue ρbox ag t n h a
        + (1 - posterior p ρbox ρfree h) * actionValue ρfree ag t n h a
      = ∑' o, (posterior p ρbox ρfree h * (ρbox.cond h a o * value ρbox ag t n (h ++ [(a, o)]))
          + (1 - posterior p ρbox ρfree h)
            * (ρfree.cond h a o * value ρfree ag t n (h ++ [(a, o)]))) := by
    unfold actionValue
    rw [Summable.tsum_add ((actionValue_summable hboxS ag hu t n h a).mul_left _)
      ((actionValue_summable hfreeS ag hu t n h a).mul_left _), tsum_mul_left, tsum_mul_left]
  rw [hsplit]
  unfold actionValue
  refine Summable.tsum_le_tsum (fun o => ?_)
    (actionValue_summable (mixtureBelief_isSubprobability hp0 hp1 hboxS hfreeS) ag hu t n h a)
    (((actionValue_summable hboxS ag hu t n h a).mul_left _).add
      ((actionValue_summable hfreeS ag hu t n h a).mul_left _))
  have hmono := mul_le_mul_of_nonneg_left (hv o)
    (mixtureBelief_cond_nonneg hp0 hp1 hboxS.nonneg hfreeS.nonneg h a o)
  refine hmono.trans (le_of_eq ?_)
  have expand : ∀ X q vb vf : ℝ,
      X * (q * vb + (1 - q) * vf) = X * q * vb + X * (1 - q) * vf := by
    intros; ring
  rw [expand,
    mixtureBelief_cond_mul_posterior hp0 hp1 hboxS.nonneg hfreeS.nonneg h a o,
    mixtureBelief_cond_mul_one_sub_posterior hp0 hp1 hboxS.nonneg hfreeS.nonneg h a o]
  ring

/-- **`value_mixture_le` at an arbitrary observation type.** -/
public theorem value_mixture_le_tsum [Nonempty Action] {p : ℝ}
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
        refine (actionValue_mixture_le_of_value hp0 hp1 hboxS hfreeS ag hu t n h a
          (fun _ => value_mixture_le_tsum hp0 hp1 hboxS hfreeS ag hu t n _)).trans ?_
        gcongr
        · exact le_ciSup (actionValue_bddAbove hboxS ag hu t n h) a
        · exact le_ciSup (actionValue_bddAbove hfreeS ag hu t n h) a
      rw [value_succ, value_succ, value_succ]
      nlinarith [hsup, hq0, hq1']

/-- **`actionValue_mixture_le` at an arbitrary observation type.** -/
public theorem actionValue_mixture_le_tsum [Nonempty Action] {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t n : ℕ)
    (h : History Action Obs) (a : Action) :
    actionValue (mixtureBelief p ρbox ρfree) ag t n h a
      ≤ posterior p ρbox ρfree h * actionValue ρbox ag t n h a
        + (1 - posterior p ρbox ρfree h) * actionValue ρfree ag t n h a :=
  actionValue_mixture_le_of_value hp0 hp1 hboxS hfreeS ag hu t n h a
    (fun _ => value_mixture_le_tsum hp0 hp1 hboxS hfreeS ag hu t n _)

/-- **`policyActionValue_mixture` at an arbitrary observation type.** -/
public theorem policyActionValue_mixture_tsum {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (π : History Action Obs → Action) (t n : ℕ) (h : History Action Obs) :
    policyActionValue (mixtureBelief p ρbox ρfree) ag π t n h
      = posterior p ρbox ρfree h * policyActionValue ρbox ag π t n h
        + (1 - posterior p ρbox ρfree h) * policyActionValue ρfree ag π t n h := by
  have h1 := policyValue_mixture_tsum hp0 hp1 hboxS hfreeS ag hu π t (n + 1) h
  rw [policyValue_succ, policyValue_succ, policyValue_succ] at h1
  linarith

/-- **`policyActionValue_le_actionValue` at an arbitrary observation type.** -/
public theorem policyActionValue_le_actionValue_tsum [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (π : History Action Obs → Action) (t n : ℕ)
    (h : History Action Obs) :
    policyActionValue ρ ag π t n h ≤ actionValue ρ ag t n h (π h) :=
  Summable.tsum_le_tsum (fun o => mul_le_mul_of_nonneg_left
      (policyValue_le_value_tsum hρ ag hu π t n (h ++ [(π h, o)])) (hρ.nonneg _ _ _))
    (policyValue_summable hρ ag hu π t n h (π h))
    (actionValue_summable hρ ag hu t n h (π h))

end ArbitraryObs

/-!
## The laws at the infinite-horizon value

Ring and Orseau's recursion (2)–(3) has no terminal condition (source card S11),
so print's comparison is between untruncated values. `infinitePolicyValue` is a
committed policy's value as the limit of the depth-`n` values, and
`infinitePolicyActionValue` its action value as the limit of the depth-`n` action
values; both limits exist at `Belief.IsSubprobability`, `|u| ≤ 1` and an
absolutely summable horizon, the conditions under which `infiniteValue` is
print's value (`ValueBounds`). Every equality and inequality between depth-`n`
quantities above passes to these limits.
-/

section InfiniteHorizon

/-- One more step of a committed policy changes its value by at most that step's
horizon weight. -/
public theorem abs_policyValue_succ_sub_le {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (π : History Action Obs → Action) (t n : ℕ) (h : History Action Obs) :
    |policyValue ρ ag π t (n + 1) h - policyValue ρ ag π t n h|
      ≤ |ag.horizon t (h.length + n + 1)| := by
  induction n generalizing h with
  | zero =>
    rw [policyValue_succ, policyValue_zero, add_sub_cancel_left, policyActionValue]
    apply hρ.abs_tsum_mul_le h (π h) (abs_nonneg _)
    intro o
    simpa [policyValue_zero, abs_mul] using
      mul_le_mul_of_nonneg_left (hu (h ++ [(π h, o)])) (abs_nonneg (ag.horizon t (h.length + 1)))
  | succ n ih =>
    rw [policyValue_succ, policyValue_succ, add_sub_add_left_eq_sub]
    unfold policyActionValue
    rw [← (policyValue_summable hρ ag hu π t (n + 1) h (π h)).tsum_sub
      (policyValue_summable hρ ag hu π t n h (π h))]
    simp only [← mul_sub]
    apply hρ.abs_tsum_mul_le h (π h) (abs_nonneg _)
    intro o
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (h ++ [(π h, o)])

/-- A summable horizon makes a committed policy's finite-depth values Cauchy. -/
public theorem policyValue_cauchySeq {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (π : History Action Obs → Action) (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|))
    (h : History Action Obs) :
    CauchySeq (fun n ↦ policyValue ρ ag π t n h) := by
  apply cauchySeq_of_dist_le_of_summable (fun n ↦ |ag.horizon t (h.length + n + 1)|)
  · intro n
    simpa [Real.dist_eq, abs_sub_comm] using abs_policyValue_succ_sub_le hρ ag hu π t n h
  · exact hw.comp_injective (by intro i j he; dsimp at he; omega)

/-- A committed policy's infinite-horizon value: the limit of its depth-`n`
values. `tendsto_policyValue_infinitePolicyValue` states when the limit exists. -/
@[expose] public noncomputable def infinitePolicyValue (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (π : History Action Obs → Action) (t : ℕ)
    (h : History Action Obs) : ℝ :=
  Filter.limUnder Filter.atTop (fun n ↦ policyValue ρ ag π t n h)

/-- The infinite-horizon committed value is the actual limit, at print's
probability and utility range and an absolutely summable horizon. -/
public theorem tendsto_policyValue_infinitePolicyValue {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (π : History Action Obs → Action) (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|))
    (h : History Action Obs) :
    Filter.Tendsto (fun n ↦ policyValue ρ ag π t n h) Filter.atTop
      (nhds (infinitePolicyValue ρ ag π t h)) :=
  (policyValue_cauchySeq hρ ag hu π t hw h).tendsto_limUnder

/-- A committed policy's infinite-horizon action value: the limit of the
depth-`n` committed action values `policyActionValue`. -/
@[expose] public noncomputable def infinitePolicyActionValue (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (π : History Action Obs → Action) (t : ℕ)
    (h : History Action Obs) : ℝ :=
  Filter.limUnder Filter.atTop (fun n ↦ policyActionValue ρ ag π t n h)

/-- The committed action values converge to `infinitePolicyActionValue`, which is
the infinite committed value less the current weighted utility. -/
public theorem tendsto_policyActionValue_infinitePolicyActionValue
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (π : History Action Obs → Action) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    Filter.Tendsto (fun n ↦ policyActionValue ρ ag π t n h) Filter.atTop
      (nhds (infinitePolicyActionValue ρ ag π t h)) := by
  have ht : Filter.Tendsto (fun n ↦ policyActionValue ρ ag π t n h) Filter.atTop
      (nhds (infinitePolicyValue ρ ag π t h - ag.horizon t h.length * ag.utility h)) := by
    refine (((tendsto_policyValue_infinitePolicyValue hρ ag hu π t hw h).comp
      (Filter.tendsto_add_atTop_nat 1)).sub_const
        (ag.horizon t h.length * ag.utility h)).congr (fun n => ?_)
    simp [Function.comp, policyValue_succ]
  rw [infinitePolicyActionValue, ht.limUnder_eq]
  exact ht

/-- **A committed policy's infinite-horizon action value mixes exactly**, the
limit of `policyActionValue_mixture_tsum`. -/
public theorem infinitePolicyActionValue_mixture {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (π : History Action Obs → Action) (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|))
    (h : History Action Obs) :
    infinitePolicyActionValue (mixtureBelief p ρbox ρfree) ag π t h
      = posterior p ρbox ρfree h * infinitePolicyActionValue ρbox ag π t h
        + (1 - posterior p ρbox ρfree h) * infinitePolicyActionValue ρfree ag π t h := by
  have hm := tendsto_policyActionValue_infinitePolicyActionValue
    (mixtureBelief_isSubprobability hp0 hp1 hboxS hfreeS) ag hu π t hw h
  have hc := ((tendsto_policyActionValue_infinitePolicyActionValue hboxS ag hu π t hw h).const_mul
      (posterior p ρbox ρfree h)).add
    ((tendsto_policyActionValue_infinitePolicyActionValue hfreeS ag hu π t hw h).const_mul
      (1 - posterior p ρbox ρfree h))
  exact tendsto_nhds_unique hm (hc.congr fun n =>
    (policyActionValue_mixture_tsum hp0 hp1 hboxS hfreeS ag hu π t n h).symm)

/-- **A committed policy never beats the optimum at the infinite-horizon value.** -/
public theorem infinitePolicyActionValue_le_infiniteActionValue [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (π : History Action Obs → Action) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    infinitePolicyActionValue ρ ag π t h ≤ infiniteActionValue ρ ag t h (π h) :=
  le_of_tendsto_of_tendsto'
    (tendsto_policyActionValue_infinitePolicyActionValue hρ ag hu π t hw h)
    (tendsto_actionValue_infiniteActionValue hρ ag hu t hw h (π h))
    (fun n => policyActionValue_le_actionValue_tsum hρ ag hu π t n h)

/-- **Equation (2)'s bound at the mixture, at the infinite-horizon value**: the
limit of `actionValue_mixture_le_tsum`. -/
public theorem infiniteActionValue_mixture_le [Nonempty Action] {p : ℝ}
    {ρbox ρfree : Belief Action Obs} (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hboxS : ρbox.IsSubprobability) (hfreeS : ρfree.IsSubprobability)
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) (a : Action) :
    infiniteActionValue (mixtureBelief p ρbox ρfree) ag t h a
      ≤ posterior p ρbox ρfree h * infiniteActionValue ρbox ag t h a
        + (1 - posterior p ρbox ρfree h) * infiniteActionValue ρfree ag t h a :=
  le_of_tendsto_of_tendsto'
    (tendsto_actionValue_infiniteActionValue
      (mixtureBelief_isSubprobability hp0 hp1 hboxS hfreeS) ag hu t hw h a)
    (((tendsto_actionValue_infiniteActionValue hboxS ag hu t hw h a).const_mul _).add
      ((tendsto_actionValue_infiniteActionValue hfreeS ag hu t hw h a).const_mul _))
    (fun n => actionValue_mixture_le_tsum hp0 hp1 hboxS hfreeS ag hu t n h a)

end InfiniteHorizon

end AISafetyAtlas.Wireheading.Mixture
