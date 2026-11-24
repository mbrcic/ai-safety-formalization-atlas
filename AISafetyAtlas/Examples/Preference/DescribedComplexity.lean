module

public import AISafetyAtlas.Preference.DescribedComplexity

/-!
# Described pairs, at one state and two actions

Print's instance: `S = {s}`, `A = {a₁, a₂}` (here `Unit` and `Bool`), and the
policy `π̇(s) = true`. A constant program codes `π̇`, another codes the zero
reward, and the source's degenerate pair `(p_π̇, 0)` is described by
`degeneratePair`; so `Describes` is inhabited and the §5.1 lower bound applies
to that pair with its `K` bounded by a concrete string.
-/

namespace AISafetyAtlas.Examples.Preference.DescribedComplexity

open AISafetyAtlas.Preference Kolmogorov
open Nat.Partrec (Code)

/-- The policy playing `true`. -/
@[expose] public def truePolicy : Policy Unit Bool := fun _ => true

/-- A string naming the constant program returning `true`. -/
@[expose] public def truePolicyCode : BitString :=
  pairString (Encodable.encode (Code.const (Encodable.encode true))) []

/-- A string naming the constant program returning the rational `0`. -/
@[expose] public def zeroRewardCode : BitString :=
  pairString (Encodable.encode (Code.const (Encodable.encode (0 : ℚ)))) []

/-- `truePolicyCode` codes `truePolicy`. -/
public theorem codesPolicy_truePolicy : CodesPolicy truePolicyCode truePolicy := fun _ => by
  rw [truePolicyCode, pairProgram_pairString, Denumerable.ofNat_encode, Code.eval_const]
  exact Part.mem_some _

/-- `zeroRewardCode` codes the zero reward. -/
public theorem codesReward_zero : CodesReward zeroRewardCode (0 : RewardFn Unit Bool) :=
  fun _ _ n => ⟨0, by
    rw [zeroRewardCode, pairProgram_pairString, Denumerable.ofNat_encode, Code.eval_const]
    exact Part.mem_some _, by simp⟩

/-- **The source's `(p_π̇, 0)` is described**, by the degenerate pair string. -/
public theorem describes_indifferent_zero :
    Describes (indifferentPlanner truePolicy, (0 : RewardFn Unit Bool))
      (degeneratePair zeroRewardCode truePolicyCode) :=
  describes_degeneratePair codesPolicy_truePolicy codesReward_zero

/-- **Print's claim (1) at that pair**: `K(π̇) ≤ K(p_π̇, 0) + c`, and
`K(p_π̇, 0)` is at most the plain complexity of the describing string. -/
public theorem plainKPolicy_truePolicy_le (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ, plainKPolicy Unit Bool U truePolicy ≤
        plainKPair Unit Bool U (indifferentPlanner truePolicy, 0) + (c : ENat) ∧
      plainKPair Unit Bool U (indifferentPlanner truePolicy, 0) ≤
        plainK U (degeneratePair zeroRewardCode truePolicyCode) := by
  obtain ⟨c, hc⟩ := plainKPolicy_le_plainKPair_of_compatible (S := Unit) (A := Bool) U hU
  exact ⟨c, hc _ _ rfl, plainKPair_le_of_describes U describes_indifferent_zero⟩

/-- A description of a compatible pair evaluates to a code of the policy. -/
example : ∃ b, EvaluatesTo (degeneratePair zeroRewardCode truePolicyCode) b ∧
    CodesPolicy b truePolicy :=
  exists_evaluatesTo_of_describes (y := (indifferentPlanner truePolicy, 0)) rfl
    describes_indifferent_zero

/-- `K(π̇)` is at most the plain complexity of its code. -/
example (U : Map) : plainKPolicy Unit Bool U truePolicy ≤ plainK U truePolicyCode :=
  plainKPolicy_le_of_codesPolicy U codesPolicy_truePolicy

/-- `evalPair` is `runOn` at the pair's two slots. -/
example :
    evalPair truePolicyCode = runOn (pairProgram truePolicyCode) (pairReward truePolicyCode) :=
  evalPair_eq_runOn _

end AISafetyAtlas.Examples.Preference.DescribedComplexity
