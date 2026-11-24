module

public import AISafetyAtlas.Wireheading.ProgramPrior
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics

/-!
# The optimal agent `A^μ` at any tie rule, and at the lexicographic rule wherever it denotes

Ring and Orseau, AGI 2011, §2, optimal variants (*"if the learning agent takes the
same actions as the non-learning one, then its behavior is also optimal"*), and
Orseau and Ring, AGI 2011, §2.1 (`A^μ`, mistakes, asymptotic optimality), with
print's tie rule (*"Ties are broken lexicographically"*, footnote 4 of the first;
*"Ties are broken in lexicographical order"*, footnote 5 of the second).

`ProgramPrior` states these at `[LinearOrder Action] [WellFoundedLT Action]`
with `InfAttains` at every history. Print names no order on the actions and no
finiteness of the action set. This module states them

* at any tie rule whose choice is a maximiser (`Model.optimal_of_maximizer`), and
* at print's lexicographic rule wherever it denotes, i.e. where the maximisers
  have a least element (`InfLexAttains`), with no well-foundedness of the order
  (`Model.optimalActionOfLeast` and the declarations after it).

Under `[WellFoundedLT Action]` each least-maximiser declaration agrees with its
`ProgramPrior` counterpart (`optimalActionOfLeast_eq_optimalAction`,
`mistakeOfLeast_iff_mistake`, `asymptoticallyOptimalOfLeast_iff`).
-/

namespace AISafetyAtlas.Wireheading.ProgramPrior

open AgentEquations

namespace Model

variable {Code Action Obs : Type*} (M : Model Code Action Obs)

/-- **A learning agent that takes a maximiser of `A^μ`'s objective is optimal**
(Ring and Orseau, AGI 2011, §2, optimal variants, with footnote 4). If at every
history the true program explains, the policy `π` takes an action maximising the
infinite action value at the point prior `μ`, then that action maximises the
action value in the true environment. `A^μ` under any tie rule takes such an
action, the lexicographic rule included, so a learning agent copying it satisfies
`hmax`; no order on the actions and no attainment argument is needed (`hmax`
witnesses attainment). `τ h` is the time index (any choice). -/
public theorem optimal_of_maximizer [DecidableEq Obs] (q₀ : Code)
    (ag : Agent Action Obs) (τ : History Action Obs → ℕ) (π : History Action Obs → Action)
    (hmax : ∀ h, M.Consistent q₀ h → ∀ b,
      infiniteActionValue (M.point q₀).belief ag (τ h) h b ≤
        infiniteActionValue (M.point q₀).belief ag (τ h) h (π h))
    (h : History Action Obs) (hc : M.Consistent q₀ h) (b : Action) :
    infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag (τ h) h b ≤
      infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag (τ h) h (π h) := by
  rw [← M.infiniteActionValue_point_eq q₀ ag _ h hc,
    ← M.infiniteActionValue_point_eq q₀ ag _ h hc]
  exact hmax h hc b

/-- **The same with print's lexicographic tie rule wherever it denotes**: taking
`A^μ`'s actions, where `A^μ` picks the least maximiser at the point prior
(`infiniteLexBestActionOfLeast`), is optimal for the true environment on every
history the true program explains. No well-foundedness of the order. -/
public theorem optimal_of_same_infiniteLexBestActionOfLeast [PartialOrder Action]
    [DecidableEq Obs] (q₀ : Code) (ag : Agent Action Obs) (τ : History Action Obs → ℕ)
    (hl : ∀ h, InfLexAttains (M.point q₀).belief ag (τ h) h) (π : History Action Obs → Action)
    (hsame : ∀ h, M.Consistent q₀ h →
      π h = infiniteLexBestActionOfLeast (M.point q₀).belief ag (τ h) h (hl h))
    (h : History Action Obs) (hc : M.Consistent q₀ h) (b : Action) :
    infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag (τ h) h b ≤
      infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag (τ h) h (π h) :=
  M.optimal_of_maximizer q₀ ag τ π (fun h hc b ↦ by
    rw [hsame h hc]; exact infiniteLexBestActionOfLeast_max _ ag _ h (hl h) b) h hc b

/-- **`A^μ`'s action with print's lexicographic tie rule wherever it denotes**
(Orseau and Ring, AGI 2011, §2.1, footnote 5): the least maximiser of the infinite
action value at the point prior, time index `t = |h|`. The hypothesis is that the
maximisers have a least element at this history; no well-foundedness. -/
@[expose] public noncomputable def optimalActionOfLeast [PartialOrder Action] (q₀ : Code)
    (ag : Agent Action Obs) (h : History Action Obs)
    (hl : InfLexAttains (M.point q₀).belief ag h.length h) : Action :=
  infiniteLexBestActionOfLeast (M.point q₀).belief ag h.length h hl

/-- `optimalActionOfLeast` maximises the action value in the true environment. -/
public theorem optimalActionOfLeast_max [PartialOrder Action] [DecidableEq Obs] (q₀ : Code)
    (ag : Agent Action Obs) (h : History Action Obs)
    (hl : InfLexAttains (M.point q₀).belief ag h.length h) (hc : M.Consistent q₀ h)
    (b : Action) :
    infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag h.length h b ≤
      infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag h.length h
        (M.optimalActionOfLeast q₀ ag h hl) := by
  rw [← M.infiniteActionValue_point_eq q₀ ag _ h hc,
    ← M.infiniteActionValue_point_eq q₀ ag _ h hc]
  exact infiniteLexBestActionOfLeast_max _ ag _ h hl b

/-- Under a well-founded order it is `optimalAction`. -/
public theorem optimalActionOfLeast_eq_optimalAction [LinearOrder Action]
    [WellFoundedLT Action] (q₀ : Code) (ag : Agent Action Obs) (h : History Action Obs)
    (hl : InfLexAttains (M.point q₀).belief ag h.length h)
    (hat : InfAttains (M.point q₀).belief ag h.length h) :
    M.optimalActionOfLeast q₀ ag h hl = M.optimalAction q₀ ag h hat :=
  infiniteLexBestActionOfLeast_eq _ ag _ h hl hat

/-- A learning agent taking `optimalActionOfLeast`'s actions is optimal for the true
environment on every history the true program explains. -/
public theorem optimal_of_same_optimalActionOfLeast [PartialOrder Action] [DecidableEq Obs]
    (q₀ : Code) (ag : Agent Action Obs)
    (hl : ∀ h : History Action Obs, InfLexAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action)
    (hsame : ∀ h, M.Consistent q₀ h → π h = M.optimalActionOfLeast q₀ ag h (hl h))
    (h : History Action Obs) (hc : M.Consistent q₀ h) (b : Action) :
    infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag h.length h b ≤
      infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag h.length h (π h) := by
  rw [hsame h hc]
  exact M.optimalActionOfLeast_max q₀ ag h (hl h) hc b

/-- `A^μ` as a policy, wherever print's lexicographic rule denotes at every history. -/
@[expose] public noncomputable def optimalPolicyOfLeast [PartialOrder Action] (q₀ : Code)
    (ag : Agent Action Obs)
    (hl : ∀ h : History Action Obs, InfLexAttains (M.point q₀).belief ag h.length h) :
    History Action Obs → Action :=
  fun h => M.optimalActionOfLeast q₀ ag h (hl h)

/-- A **mistake** of `π` at `h` against `optimalPolicyOfLeast` (Orseau and Ring,
AGI 2011, §2.1): its action differs from `A^μ`'s given the same history. -/
@[expose] public def MistakeOfLeast [PartialOrder Action] (q₀ : Code) (ag : Agent Action Obs)
    (hl : ∀ h : History Action Obs, InfLexAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action) (h : History Action Obs) : Prop :=
  π h ≠ M.optimalPolicyOfLeast q₀ ag hl h

/-- **Asymptotic optimality** against `optimalPolicyOfLeast` (Orseau and Ring,
AGI 2011, §2.1), at the per-step reading of `AsymptoticallyOptimal`: along the
policy's run in the true environment it eventually makes no mistakes. -/
@[expose] public def AsymptoticallyOptimalOfLeast [PartialOrder Action] (q₀ : Code)
    (ag : Agent Action Obs)
    (hl : ∀ h : History Action Obs, InfLexAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action) : Prop :=
  ∀ᶠ k in Filter.atTop, ¬ M.MistakeOfLeast q₀ ag hl π (trajectory (M.run q₀) π k)

/-- Under a well-founded order a mistake is a `ProgramPrior` mistake. -/
public theorem mistakeOfLeast_iff_mistake [LinearOrder Action] [WellFoundedLT Action]
    (q₀ : Code) (ag : Agent Action Obs)
    (hl : ∀ h : History Action Obs, InfLexAttains (M.point q₀).belief ag h.length h)
    (hat : ∀ h : History Action Obs, InfAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action) (h : History Action Obs) :
    M.MistakeOfLeast q₀ ag hl π h ↔ M.Mistake q₀ ag hat π h := by
  simp only [MistakeOfLeast, Mistake, optimalPolicyOfLeast, optimalPolicy,
    M.optimalActionOfLeast_eq_optimalAction q₀ ag h (hl h) (hat h)]

/-- Under a well-founded order this is `AsymptoticallyOptimal`. -/
public theorem asymptoticallyOptimalOfLeast_iff [LinearOrder Action] [WellFoundedLT Action]
    (q₀ : Code) (ag : Agent Action Obs)
    (hl : ∀ h : History Action Obs, InfLexAttains (M.point q₀).belief ag h.length h)
    (hat : ∀ h : History Action Obs, InfAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action) :
    M.AsymptoticallyOptimalOfLeast q₀ ag hl π ↔ M.AsymptoticallyOptimal q₀ ag hat π := by
  simp only [AsymptoticallyOptimalOfLeast, AsymptoticallyOptimal,
    M.mistakeOfLeast_iff_mistake q₀ ag hl hat]

open Classical in
/-- Asymptotic optimality is the mistake indicator tending to zero. -/
public theorem asymptoticallyOptimalOfLeast_iff_tendsto [PartialOrder Action] (q₀ : Code)
    (ag : Agent Action Obs)
    (hl : ∀ h : History Action Obs, InfLexAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action) :
    M.AsymptoticallyOptimalOfLeast q₀ ag hl π ↔
      Filter.Tendsto (fun k => if M.MistakeOfLeast q₀ ag hl π (trajectory (M.run q₀) π k)
        then (1 : ℝ) else 0) Filter.atTop (nhds 0) := by
  constructor
  · intro hev
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    simp [hk]
  · intro ht
    have hlt := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hlt] with k hk hm
    simp [hm] at hk

open Classical in
/-- **Asymptotic optimality at the rate reading** (Orseau and Ring, AGI 2011, §2.1:
*"its performance is measured in terms of the number of mistakes it makes [...] The
agent is asymptotically optimal if the number of mistakes it makes tends towards
zero"*), against `optimalPolicyOfLeast`: along the policy's run in the true
environment, the fraction of the first n steps at which it makes a mistake tends
to zero. It is the Cesàro mean of the mistake indicator of
`asymptoticallyOptimalOfLeast_iff_tendsto`, i.e. the mistake count before step n
divided by n. `AsymptoticallyOptimalOfLeast` is the per-step reading; it implies
this one (`asymptoticallyOptimalRateOfLeast_of_asymptoticallyOptimalOfLeast`). -/
@[expose] public def AsymptoticallyOptimalRateOfLeast [PartialOrder Action] (q₀ : Code)
    (ag : Agent Action Obs)
    (hl : ∀ h : History Action Obs, InfLexAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action) : Prop :=
  Filter.Tendsto (fun n : ℕ => (n⁻¹ : ℝ) * ∑ k ∈ Finset.range n,
      if M.MistakeOfLeast q₀ ag hl π (trajectory (M.run q₀) π k) then (1 : ℝ) else 0)
    Filter.atTop (nhds 0)

/-- **Per-step asymptotic optimality gives the rate**: a policy that eventually makes
no mistakes along its run makes mistakes at a vanishing fraction of its steps, the
Cesàro mean of an indicator tending to zero. -/
public theorem asymptoticallyOptimalRateOfLeast_of_asymptoticallyOptimalOfLeast
    [PartialOrder Action] (q₀ : Code) (ag : Agent Action Obs)
    (hl : ∀ h : History Action Obs, InfLexAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action) (hπ : M.AsymptoticallyOptimalOfLeast q₀ ag hl π) :
    M.AsymptoticallyOptimalRateOfLeast q₀ ag hl π :=
  ((M.asymptoticallyOptimalOfLeast_iff_tendsto q₀ ag hl π).mp hπ).cesaro

/-- `A^μ` is asymptotically optimal: it never makes a mistake. -/
public theorem asymptoticallyOptimalOfLeast_optimalPolicyOfLeast [PartialOrder Action]
    (q₀ : Code) (ag : Agent Action Obs)
    (hl : ∀ h : History Action Obs, InfLexAttains (M.point q₀).belief ag h.length h) :
    M.AsymptoticallyOptimalOfLeast q₀ ag hl (M.optimalPolicyOfLeast q₀ ag hl) :=
  Filter.Eventually.of_forall fun _ hm => hm rfl

/-- **Same actions, same prediction mistakes** (Orseau and Ring, AGI 2011, §2.1),
with `A^μ_p` breaking ties by print's lexicographic rule wherever it denotes: a
learning prediction agent taking `optimalPolicyOfLeast`'s action at every step of
its run in the true environment has the same utility as `A^μ_p` at every step. -/
public theorem same_prediction_mistakes_of_least [PartialOrder Action] [DecidableEq Obs]
    (q₀ : Code)
    (predict : History Action Obs → Obs) (m : ℕ)
    (hl : ∀ h : History Action Obs,
      InfLexAttains (M.point q₀).belief (DelusionBox.predictionAgent predict m) h.length h)
    (π : History Action Obs → Action)
    (hsame : ∀ k, π (trajectory (M.run q₀) π k) =
      M.optimalPolicyOfLeast q₀ (DelusionBox.predictionAgent predict m) hl
        (trajectory (M.run q₀) π k))
    (k : ℕ) :
    (DelusionBox.predictionAgent predict m).utility (trajectory (M.run q₀) π k) =
      (DelusionBox.predictionAgent predict m).utility
        (trajectory (M.run q₀)
          (M.optimalPolicyOfLeast q₀ (DelusionBox.predictionAgent predict m) hl) k) := by
  rw [trajectory_eq_of_agree (M.run q₀) π _ hsame k]

end Model

end AISafetyAtlas.Wireheading.ProgramPrior
