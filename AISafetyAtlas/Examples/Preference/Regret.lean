module

public import AISafetyAtlas.Preference.Regret
public import AISafetyAtlas.Examples.Wireheading.Corruption

/-!
# Half-maximal regret is not ruled out, at the cheapest certificate

`AISafetyAtlas.Examples.Wireheading.Corruption.trivialClass_halfMaximalRegretBound`
already discharges `HalfMaximalRegretBound` at the cheapest `ComplementedClass`.
Reuse it here to instantiate the set-level Preference-side conclusion, at the
only behaviour the model has.
-/

namespace AISafetyAtlas.Examples.Preference

open AISafetyAtlas.Preference AISafetyAtlas.Examples.Wireheading.Corruption

/-- The bad-compatible-rewards set is nonempty, at the trivial regret model. -/
theorem trivial_bad_compatible_rewards_nonempty :
    {R : Bool |
        (∃ p : Planner Bool Unit, Explains p R ()) ∧
        trivialClass.toRegretModel.worstCaseRegret
            trivialClass.toRegretModel.worstPolicy / 2 ≤
          trivialClass.toRegretModel.regret R ()}.Nonempty :=
  RegretModel.bad_compatible_rewards_nonempty trivialClass.toRegretModel
    trivialClass_halfMaximalRegretBound () ()

/-- **Half the worst-case regret cannot be ruled out.** The sharper form of the
same fact: not merely that a bad compatible reward *exists*, but that for any
pair of behaviours one can exhibit a reward and a planner explaining the first
while the second suffers at least half the worst case. The set form above says
the class is inhabited; this says what inhabits it and against which behaviour.
-/
theorem trivial_cannot_rule_out_half :
    ∃ (R : Bool) (p : Planner Bool Unit),
      Explains p R () ∧
        trivialClass.toRegretModel.worstCaseRegret
            trivialClass.toRegretModel.worstPolicy / 2
          ≤ trivialClass.toRegretModel.regret R () :=
  RegretModel.cannot_rule_out_half_maximal_regret trivialClass.toRegretModel
    trivialClass_halfMaximalRegretBound () ()

end AISafetyAtlas.Examples.Preference
