module

public import AISafetyAtlas.Preference.AnyGreedy
public import AISafetyAtlas.Preference.TimedComplexity

/-!
# Proposition 10 at every greedy planner

Armstrong and Mindermann, appendix A, Proposition 10 (amapp-prop10, PDF p. 1):
*"If planner can take in algorithms generating reward functions, rather than
simply reward functions, then the results of Proposition 7 still apply to
(p_g, R_π̇) and (−p_g, −R_π̇) in this situation."*

`AISafetyAtlas.Preference.Source.CodePlanning.proposition_ten_greedy` and
`AISafetyAtlas.Preference.Source.CodePlanning.proposition_ten_antigreedy` take
the code planner to output `AISafetyAtlas.Preference.greedyPlanner` of the
reward its input computes. Print fixes no tie rule for p_g, so the statements
below take any greedy planner g (`AISafetyAtlas.Preference.IsGreedy`); the
existing ones are the instance g := `greedyPlanner`. The language interface
(`TimedLanguage`, `CodePlanning`, `CodePlanning.Wrapping`) does not mention the
greedy planner, so it is unchanged: the wrapper W′ falls back to the code of
p_g, whichever p_g is.
-/

namespace AISafetyAtlas.Preference.Source

open AISafetyAtlas.Preference
open scoped ENNReal

variable {S A Alg : Type*}

namespace CodePlanning

variable {L : TimedLanguage S A Alg} (P : CodePlanning L) [DecidableEq A]

/-- **Proposition 10, second sentence, greedy pair, at every greedy planner**
(Armstrong and Mindermann, appendix A, amapp-prop10). For any greedy planner g,
whatever its tie rule, in any time-bounded language with code planners and the
wrappers W, W′: let q be g on codes (on a code of R it outputs g(R)) and α_q an
algorithm for it. Then for every policy π, (q, R_π) is amongst the
lowest-Kt_L code-planner pairs compatible with π, within l(α_q) + 3c + log(1 + c),
and amongst the lowest-KT_L ones, within l(α_q) + 4c.
`proposition_ten_greedy` is the instance g := `greedyPlanner`. -/
public theorem proposition_ten_greedy_of_isGreedy {g : Planner (RewardFn S A) (Policy S A)}
    (hg : IsGreedy g) (W : P.Wrapping rewardOf) {αg : Alg}
    {qg : Alg → Policy S A} (hαg : P.GenCodePlanner αg qg)
    (hqg : ∀ (β : Alg) (R : RewardFn S A), L.GenReward β R → qg β = g R)
    (π : Policy S A) :
    AmongLowestIn (fun y => L.CodeCompatible y π) P.codeKt
        (L.len αg + 3 * L.c + ENNReal.ofReal (Real.log (1 + L.c))) (qg, rewardOf π) ∧
      AmongLowestIn (fun y => L.CodeCompatible y π) P.codeKT
        (L.len αg + 4 * L.c) (qg, rewardOf π) := by
  have hq : ∀ (α' : Alg) (σ : Policy S A), L.GenPolicy α' σ → qg (W.wrapReward α') = σ :=
    fun α' σ h => (hqg _ _ (W.genReward_wrapReward h)).trans (hg.apply_rewardOf σ)
  have hc : L.CodeCompatible (qg, rewardOf π) π :=
    fun β hβ => (hqg β _ hβ).trans (hg.apply_rewardOf π)
  refine ⟨P.amongLowestIn_wrap W logTime logTime_mono _ (fun t => logTime_add_le t L.c)
    hαg hq hc, ?_⟩
  have h := P.amongLowestIn_wrap W (fun t => (t : ℝ≥0∞))
    (fun _ _ h => by dsimp only; exact_mod_cast h) (L.c : ℝ≥0∞) (fun t => by push_cast; rfl)
    hαg hq hc
  rwa [show (L.len αg : ℝ≥0∞) + 3 * L.c + L.c = L.len αg + 4 * L.c by ring] at h

/-- **Proposition 10, second sentence, anti-rational pair, at every greedy
planner** (amapp-prop10: *"… and (−p_g, −R_π̇) in this situation"*). As
`proposition_ten_greedy_of_isGreedy`, with q the planner −g on codes (on a code
of R it outputs g(−R), print's Definition 5) and the wrappers for −R_π.
`proposition_ten_antigreedy` is the instance g := `greedyPlanner`. -/
public theorem proposition_ten_antigreedy_of_isGreedy
    {g : Planner (RewardFn S A) (Policy S A)} (hg : IsGreedy g)
    (W : P.Wrapping fun π => -rewardOf π) {αn : Alg}
    {qn : Alg → Policy S A} (hαn : P.GenCodePlanner αn qn)
    (hqn : ∀ (β : Alg) (R : RewardFn S A), L.GenReward β R → qn β = g (-R))
    (π : Policy S A) :
    AmongLowestIn (fun y => L.CodeCompatible y π) P.codeKt
        (L.len αn + 3 * L.c + ENNReal.ofReal (Real.log (1 + L.c))) (qn, -rewardOf π) ∧
      AmongLowestIn (fun y => L.CodeCompatible y π) P.codeKT
        (L.len αn + 4 * L.c) (qn, -rewardOf π) := by
  have hq : ∀ (α' : Alg) (σ : Policy S A), L.GenPolicy α' σ → qn (W.wrapReward α') = σ :=
    fun α' σ h => (hqn _ _ (W.genReward_wrapReward h)).trans (hg.negPlanner_neg_rewardOf σ)
  have hc : L.CodeCompatible (qn, -rewardOf π) π :=
    fun β hβ => (hqn β _ hβ).trans (hg.negPlanner_neg_rewardOf π)
  refine ⟨P.amongLowestIn_wrap W logTime logTime_mono _ (fun t => logTime_add_le t L.c)
    hαn hq hc, ?_⟩
  have h := P.amongLowestIn_wrap W (fun t => (t : ℝ≥0∞))
    (fun _ _ h => by dsimp only; exact_mod_cast h) (L.c : ℝ≥0∞) (fun t => by push_cast; rfl)
    hαn hq hc
  rwa [show (L.len αn : ℝ≥0∞) + 3 * L.c + L.c = L.len αn + 4 * L.c by ring] at h

end CodePlanning

end AISafetyAtlas.Preference.Source
