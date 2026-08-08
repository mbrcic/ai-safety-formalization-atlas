module

import AISafetyAtlas
import Mathlib.Tactic.NormNum

/-!
# Downstream consumers of the three workbench surfaces

Thin patterns—not new research results and not production systems. They show
how a later proof or assurance argument can *import* the facades as ingredients:

* **Compositional** — multiparty goals that do not factor into local contracts
* **Wireheading** — half-maximal regret on a nonzero complemented class
* **Preference** — behaviour does not pin down reward, with an explicit regret
  certificate (not a silent model field)

Engineers may treat these cores as reference specifications inside a larger
argument; correspondence to an implementation is out of scope here.
-/

namespace AISafetyAtlas.Examples.WorkbenchConsumers

open AISafetyAtlas.Compositional
open AISafetyAtlas.Compositional.LocalContractBoundary
open AISafetyAtlas.Compositional.Hyperproperties
open AISafetyAtlas.Wireheading.Corruption
open AISafetyAtlas.Preference

/-! ## Compositional consumer: multiparty goals need non-local structure -/

/--
**Design use of the boundary.**  If two agents must output the same bit, the
accepted joint configurations are not a rectangle.  Independent per-agent
contracts of the form `P₁(a₁) ∧ P₂(a₂)` cannot express that goal; use
relational or hyperproperty machinery instead.
-/
example : ¬ IsRectangle Agreement ∧ ¬ ExchangeClosed Agreement :=
  ⟨not_isRectangle_agreement, not_exchangeClosed_agreement⟩

/--
**Multi-execution use.**  “At most one complete trace” is 2-safety and is not
a pure per-trace property: membership depends on the whole system, not on each
trace against a fixed allowed set.
-/
example :
    IsKSafety (fun p t : Bool => p = t) 2 (AtMostOneTrace Bool) ∧
      ¬ IsPureTraceProperty (AtMostOneTrace Bool) :=
  atMostOneTrace_bool_boundary

/-! ## Wireheading consumer: nonzero half-maximal regret -/

/--
Two environments, policies match environments for return 1 else 0.  Worst-case
regret of the worst policy is 1, so the Everitt core forces every policy to
carry at least `1/2`.
-/
def binaryCorruption : ComplementedClass Bool Bool where
  returnValue := fun μ π => if μ = π then 1 else 0
  horizon := 1
  complement := Bool.not
  complement_involutive := by
    intro μ
    cases μ <;> rfl
  complement_return := by
    intro μ π
    cases μ <;> cases π <;> norm_num
  bestPolicy := id
  bestPolicy_best := by
    intro μ π
    cases μ <;> cases π <;> norm_num
  worstEnvironment := Bool.not
  worstEnvironment_worst := by
    intro π μ
    cases π <;> cases μ <;> norm_num
  worstPolicy := false
  worstPolicy_worst := by
    intro π
    cases π <;> norm_num

/-- The algebraic bound is nontrivial on this class: worst-case regret is 1. -/
example : binaryCorruption.worstCaseRegret binaryCorruption.worstPolicy = 1 := by
  simp [ComplementedClass.worstCaseRegret, ComplementedClass.regret,
    binaryCorruption]

/-- Every policy inherits at least half of that worst-case regret. -/
example (π : Bool) :
    (1 : ℝ) / 2 ≤ binaryCorruption.worstCaseRegret π := by
  have h := binaryCorruption.everitt_theorem_eleven π
  have hw : binaryCorruption.worstCaseRegret binaryCorruption.worstPolicy = 1 := by
    simp [ComplementedClass.worstCaseRegret, ComplementedClass.regret,
      binaryCorruption]
  simpa [hw] using h

/-! The gate used by the preference bridge has a concrete inhabitant. -/
example : HalfMaximalRegretBound binaryCorruption.toRegretModel :=
  binaryCorruption.halfMaximalRegretBound

/-! ## Preference consumer: unidentifiability + regret certificate -/

/--
**Cross-surface pattern for a later theory paper.**  Observed behaviour `πh`
does not rule out a reward on which agent behaviour `πa` still carries at least
half-maximal worst-case regret.  The Everitt bound is an explicit certificate
from Wireheading, not a silent field of the preference model.
-/
example (πh πa : Bool) :
    ∃ (R : Bool) (p : Planner Bool Bool),
      Explains p R πh ∧
        binaryCorruption.toRegretModel.worstCaseRegret
            binaryCorruption.toRegretModel.worstPolicy / 2 ≤
          binaryCorruption.toRegretModel.regret R πa :=
  binaryCorruption.toRegretModel.cannot_rule_out_half_maximal_regret
    binaryCorruption.halfMaximalRegretBound πh πa

/-- Behaviour alone never eliminates any reward hypothesis. -/
example (π : Bool → Bool) (R : Bool → Bool → ℝ) :
    ∃ p : Planner (Bool → Bool → ℝ) (Bool → Bool), Explains p R π :=
  exists_planner π R

end AISafetyAtlas.Examples.WorkbenchConsumers
