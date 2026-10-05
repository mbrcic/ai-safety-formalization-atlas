module

public import AISafetyAtlas.Wireheading.CRMDP

/-!
# The zero-horizon model: every extremum is `0 ≤ 0`

`Model.bestPolicy_best`, `worstEnvironment_worst` and `worstPolicy_worst` are
inequalities between finite sums `returnOver transition horizon start μ π`
over `Finset.range horizon`. At `horizon = 0` every such sum is the empty sum,
so all three inequalities collapse to `0 ≤ 0` regardless of which policy or
environment fills the argument -- the cheapest possible instantiation of a
structure with three genuine extremum fields.
-/

namespace AISafetyAtlas.Examples.Wireheading.CRMDP

open AISafetyAtlas.Wireheading.CRMDP

/-- The zero corrupted-reward, always-identity-corruption environment. -/
public def trivialEnv : Env Unit where
  trueReward := fun _ => ⟨0, le_refl 0, by norm_num⟩
  corruption := fun _ x => x

/-- The zero-horizon model: nothing is ever returned, so every extremum
condition is `0 ≤ 0`. -/
public noncomputable def trivialModel : Model Unit Unit where
  transition := fun _ _ => ()
  horizon := 0
  start := ()
  bestPolicy := fun _ _ => ()
  bestPolicy_best := by intro μ π; simp [returnOver]
  worstEnvironment := fun _ => trivialEnv
  worstEnvironment_worst := by intro π μ; simp [returnOver]
  worstPolicy := fun _ => ()
  worstPolicy_worst := by intro π; simp [returnOver]

/-- **No policy separates an environment from its complement, at the
witness.** -/
public theorem trivial_run_complement (n : ℕ) :
    run (fun _ _ => ()) trivialEnv.complement (fun _ => ()) () n =
      run (fun _ _ => ()) trivialEnv (fun _ => ()) () n :=
  run_complement (fun _ _ => ()) trivialEnv (fun _ => ()) () n

/-- **The half-maximal regret bound, packaged at the CRMDP level, at the
witness.** -/
public theorem trivialModel_halfMaximalRegretBound :
    AISafetyAtlas.Preference.HalfMaximalRegretBound
      trivialModel.toComplementedClass.toRegretModel :=
  Model.halfMaximalRegretBound trivialModel

/-- **No planner rules out half-maximal regret, at the witness.** -/
public theorem trivialModel_cannot_rule_out_half_maximal_regret :
    ∃ (μ : Env Unit)
      (p : AISafetyAtlas.Preference.Planner (Env Unit) (Policy Unit Unit)),
      AISafetyAtlas.Preference.Explains p μ (fun _ => ()) ∧
        trivialModel.toComplementedClass.toRegretModel.worstCaseRegret
            trivialModel.toComplementedClass.toRegretModel.worstPolicy / 2 ≤
          trivialModel.toComplementedClass.toRegretModel.regret μ (fun _ => ()) :=
  Model.cannot_rule_out_half_maximal_regret trivialModel (fun _ => ()) (fun _ => ())

end AISafetyAtlas.Examples.Wireheading.CRMDP
