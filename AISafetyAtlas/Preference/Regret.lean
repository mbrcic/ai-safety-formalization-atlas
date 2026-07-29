module

public import AISafetyAtlas.Preference
public import Mathlib.Data.Real.Basic

/-!
# Half-maximal regret is not ruled out by observation (source §4.1.2)

Armstrong and Mindermann combine their planner/reward unidentifiability theorem
with Everitt et al.'s corrupted-reward no-free-lunch bound.  This module keeps
the two ingredients separate: `RegretModel` records attained maxima, while
`HalfMaximalRegretBound` is an explicit certificate proved by
`AISafetyAtlas.Wireheading.Corruption.everitt_theorem_eleven`.

The result is abstract over reward/environment and behaviour types.  It builds
no MDP and asserts nothing about a deployed system.

Survey row: **BY-011**; the certificate belongs to **BY-039**.
-/

namespace AISafetyAtlas.Preference

/-- An abstract regret model with genuine, attained worst-case maxima. -/
public structure RegretModel (Reward Behaviour : Type*) where
  /-- Regret of a behaviour in an environment/reward hypothesis. -/
  regret : Reward → Behaviour → ℝ
  /-- Maximum regret over the environment class. -/
  worstCaseRegret : Behaviour → ℝ
  /-- Every environment's regret is bounded by `worstCaseRegret`. -/
  worstCaseRegret_upper :
    ∀ R : Reward, ∀ π : Behaviour, regret R π ≤ worstCaseRegret π
  /-- The maximum is attained. -/
  worstCaseRegret_attained :
    ∀ π : Behaviour, ∃ R : Reward, worstCaseRegret π = regret R π
  /-- A behaviour with maximal worst-case regret. -/
  worstPolicy : Behaviour
  /-- `worstPolicy` is worst. -/
  worstPolicy_worst :
    ∀ π : Behaviour, worstCaseRegret π ≤ worstCaseRegret worstPolicy

/--
An explicit certificate for the Everitt et al. (IJCAI 2017) Theorem 11
conclusion.  Keeping this separate prevents the BY-011 bridge from silently
assuming BY-039.
-/
public structure HalfMaximalRegretBound {Reward Behaviour : Type*}
    (M : RegretModel Reward Behaviour) : Prop where
  bound :
    ∀ π : Behaviour,
      M.worstCaseRegret M.worstPolicy / 2 ≤ M.worstCaseRegret π

namespace RegretModel

variable {Reward Behaviour : Type*} (M : RegretModel Reward Behaviour)

/--
**Observation cannot rule out half-maximal regret (source §4.1.2).**

For any observed behaviour `πh` and candidate agent behaviour `πa`, some reward
both remains compatible with the observation and inflicts at least
half-maximal regret.
-/
public theorem cannot_rule_out_half_maximal_regret
    (everitt : HalfMaximalRegretBound M)
    (πh πa : Behaviour) :
    ∃ (R : Reward) (p : Planner Reward Behaviour),
      Explains p R πh ∧
        M.worstCaseRegret M.worstPolicy / 2 ≤ M.regret R πa := by
  obtain ⟨R, hR⟩ := M.worstCaseRegret_attained πa
  obtain ⟨p, hp⟩ := exists_planner (R := Reward) πh R
  exact ⟨R, p, hp, hR ▸ everitt.bound πa⟩

/-- Set-level form of `cannot_rule_out_half_maximal_regret`. -/
public theorem bad_compatible_rewards_nonempty
    (everitt : HalfMaximalRegretBound M) (πh πa : Behaviour) :
    {R : Reward |
        (∃ p : Planner Reward Behaviour, Explains p R πh) ∧
        M.worstCaseRegret M.worstPolicy / 2 ≤ M.regret R πa}.Nonempty := by
  obtain ⟨R, p, hp, hR⟩ :=
    M.cannot_rule_out_half_maximal_regret everitt πh πa
  exact ⟨R, ⟨p, hp⟩, hR⟩

end RegretModel
end AISafetyAtlas.Preference
