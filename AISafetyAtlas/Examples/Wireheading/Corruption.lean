module

public import AISafetyAtlas.Wireheading.Corruption

/-!
# The bound, packaged, at the cheapest complemented class

`halfMaximalRegretBound` merely repackages `everitt_theorem_eleven` for the
regret bridge, so any `ComplementedClass` grounds it. A single-policy class
collapses every field's inequality to a comparison of a value with itself:
there is only one policy, so `bestPolicy` and `worstPolicy` are forced, and
every "worst over policies" clause is trivial.
-/

namespace AISafetyAtlas.Examples.Wireheading.Corruption

open AISafetyAtlas.Wireheading.Corruption

/-- Two environments, complementary returns, one policy. -/
public def trivialClass : ComplementedClass Bool Unit where
  returnValue := fun μ _ => if μ then 1 else 0
  horizon := 1
  complement := Bool.not
  complement_involutive := Bool.not_not
  complement_return := by intro μ π; cases μ <;> norm_num
  bestPolicy := fun _ => ()
  bestPolicy_best := by intro μ π; exact le_refl _
  worstEnvironment := fun _ => false
  worstEnvironment_worst := by
    intro π μ
    show (if μ then (1:ℝ) else 0) - (if μ then (1:ℝ) else 0) ≤
      (if false then (1:ℝ) else 0) - (if false then (1:ℝ) else 0)
    simp
  worstPolicy := ()
  worstPolicy_worst := by intro π; exact le_refl _

/-- **The half-maximal regret bound, packaged, at the witness.** -/
public theorem trivialClass_halfMaximalRegretBound :
    AISafetyAtlas.Preference.HalfMaximalRegretBound trivialClass.toRegretModel :=
  ComplementedClass.halfMaximalRegretBound trivialClass

/-! ## A class where the bound is not `0 ≤ 0`

`trivialClass` has a one-point policy type, so every regret on it is zero and
Theorem 11 reads `0 / 2 ≤ 0`. That grounds the statement without exercising it.
`matchClass` gives the policy two values, so the worst-case regret is a real `1`
and the theorem's conclusion is the non-vacuous `1 / 2 ≤ 1`.
-/

/-- Two environments and two policies: the policy that matches its environment
earns `1`, and any other earns `0`. -/
@[expose] public def matchClass : ComplementedClass Bool Bool where
  returnValue := fun μ π => if μ = π then 1 else 0
  horizon := 1
  complement := Bool.not
  complement_involutive := Bool.not_not
  complement_return := by intro μ π; cases μ <;> cases π <;> norm_num
  bestPolicy := fun μ => μ
  bestPolicy_best := by intro μ π; cases μ <;> cases π <;> norm_num
  worstEnvironment := fun π => !π
  worstEnvironment_worst := by intro π μ; cases π <;> cases μ <;> norm_num
  worstPolicy := true
  worstPolicy_worst := by intro π; cases π <;> norm_num

/-- Every policy's worst case here costs the full `1`: whatever it plays, the
complement environment is the one it does not match. -/
public theorem matchClass_worstCaseRegret (π : Bool) :
    matchClass.worstCaseRegret π = 1 := by
  cases π <;>
    simp [ComplementedClass.worstCaseRegret, ComplementedClass.regret, matchClass]

/-- **Everitt et al. Theorem 11, applied.** Named in full rather than through
`M.everitt_theorem_eleven`: four declarations in the tree carry that leaf, so the
dotted form is evidence for all of them and therefore for none. -/
public theorem matchClass_everitt_theorem_eleven (π : Bool) :
    matchClass.worstCaseRegret matchClass.worstPolicy / 2 ≤ matchClass.worstCaseRegret π :=
  ComplementedClass.everitt_theorem_eleven matchClass π

/-- The bound the theorem certifies on this class, with both sides evaluated:
`1 / 2 ≤ 1`, which is the half-maximal claim doing work. -/
public theorem matchClass_half_le_one : (1 : ℝ) / 2 ≤ 1 := by
  have h := matchClass_everitt_theorem_eleven true
  rwa [matchClass_worstCaseRegret, matchClass_worstCaseRegret] at h

end AISafetyAtlas.Examples.Wireheading.Corruption
