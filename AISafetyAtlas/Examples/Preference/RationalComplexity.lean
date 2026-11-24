module

public import AISafetyAtlas.Preference.RationalComplexity
public import AISafetyAtlas.Examples.Preference.DescribedComplexity

/-!
# The degenerate pairs at exact rational codes, at one state and two actions

Print's instance: S = {s}, A = {a₁, a₂} (here `Unit` and `Bool`), the policy
π̇(s) = true, and the greedy planner with tie order false, true. The three
degenerate pairs are compatible with π̇; with exact rational codes their
complexity is within one constant of K(π̇), which is at most the plain
complexity of a concrete string, so the bounds are not ⊤ ≤ ⊤.
-/

namespace AISafetyAtlas.Examples.Preference.RationalComplexity

open AISafetyAtlas.Preference Kolmogorov
open AISafetyAtlas.Examples.Preference.DescribedComplexity
open Nat.Partrec (Code)

/-- The tie order false, true lists every action. -/
public theorem covers : ∀ a : Bool, a ∈ [false, true] := by decide

/-- Every finite nonempty action type has a covering listing. -/
example : ∃ (a₀ : Bool) (l : List Bool), ∀ a, a ∈ a₀ :: l :=
  AISafetyAtlas.Preference.exists_covering_listing

/-- The greedy planner with tie order false, true picks a maximiser. -/
example (R : RewardFn Unit Bool) (a : Bool) :
    R () a ≤ R () (AISafetyAtlas.Preference.greedyOn false [true] R ()) :=
  AISafetyAtlas.Preference.greedyOn_max covers R () a

/-- p_g(R_π̇) = π̇. -/
public theorem greedy_truePolicy :
    AISafetyAtlas.Preference.greedyOn false [true] (rewardOf truePolicy) = truePolicy :=
  AISafetyAtlas.Preference.greedyOn_rewardOf covers truePolicy

/-- (−p_g)(−R_π̇) = π̇. -/
public theorem antigreedy_truePolicy :
    negPlanner (AISafetyAtlas.Preference.greedyOn false [true]) (-rewardOf truePolicy) =
      truePolicy :=
  AISafetyAtlas.Preference.negPlanner_greedyOn_neg_rewardOf covers truePolicy

/-- `zeroRewardCode` codes the zero reward exactly. -/
public theorem exactCodesReward_zero :
    AISafetyAtlas.Preference.ExactCodesReward zeroRewardCode (0 : RewardFn Unit Bool) :=
  fun _ _ => ⟨0, by simp, fun _ => by
    rw [zeroRewardCode, pairProgram_pairString, Denumerable.ofNat_encode, Code.eval_const]
    exact Part.mem_some _⟩

/-- An exact code is an approximation code. -/
example : CodesReward zeroRewardCode (0 : RewardFn Unit Bool) :=
  AISafetyAtlas.Preference.ExactCodesReward.codesReward exactCodesReward_zero

/-- **(p_π̇, 0) has an exact description**, the degenerate pair string. -/
public theorem describesExact_indifferent_zero :
    AISafetyAtlas.Preference.DescribesExact (indifferentPlanner truePolicy, (0 : RewardFn Unit Bool))
      (degeneratePair zeroRewardCode truePolicyCode) := by
  refine ⟨by rw [degeneratePair, pairReward_pairString]; exact exactCodesReward_zero,
    fun _ _ _ => ⟨truePolicyCode, ?_, codesPolicy_truePolicy⟩⟩
  rw [runOn, degeneratePair, pairProgram_pairString, Denumerable.ofNat_encode, Code.eval_const]
  simp [Encodable.encodek]

/-- Exact and approximation-code descriptions are hybrid descriptions. -/
example :
    AISafetyAtlas.Preference.DescribesHybrid (indifferentPlanner truePolicy, (0 : RewardFn Unit Bool))
        (degeneratePair zeroRewardCode truePolicyCode) ∧
      AISafetyAtlas.Preference.DescribesHybrid (indifferentPlanner truePolicy, (0 : RewardFn Unit Bool))
        (degeneratePair zeroRewardCode truePolicyCode) :=
  ⟨AISafetyAtlas.Preference.DescribesExact.describesHybrid describesExact_indifferent_zero,
    AISafetyAtlas.Preference.Describes.describesHybrid describes_indifferent_zero⟩

/-- The hybrid complexity is below the exact and the approximation-code ones. -/
example (U : Map) (y : Pair Unit Bool) :
    AISafetyAtlas.Preference.plainKPairHybrid Unit Bool U y ≤
        AISafetyAtlas.Preference.plainKPairExact Unit Bool U y ∧
      AISafetyAtlas.Preference.plainKPairHybrid Unit Bool U y ≤ plainKPair Unit Bool U y :=
  ⟨AISafetyAtlas.Preference.plainKPairHybrid_le_plainKPairExact U y,
    AISafetyAtlas.Preference.plainKPairHybrid_le_plainKPair U y⟩

/-- **Claim (1) at the greedy pair**, in both codings: K(π̇) ≤ K(p_g, R_π̇) + c. -/
public theorem claim_one_greedy (U : Map) (hU : isOptimalConditional U) :
    (∃ c : ℕ, plainKPolicy Unit Bool U truePolicy ≤
      AISafetyAtlas.Preference.plainKPairHybrid Unit Bool U
        (AISafetyAtlas.Preference.greedyOn false [true], rewardOf truePolicy) + (c : ENat)) ∧
    ∃ c : ℕ, plainKPolicy Unit Bool U truePolicy ≤
      AISafetyAtlas.Preference.plainKPairExact Unit Bool U
        (AISafetyAtlas.Preference.greedyOn false [true], rewardOf truePolicy) + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    AISafetyAtlas.Preference.plainKPolicy_le_plainKPairHybrid_of_compatible (S := Unit) (A := Bool)
      U hU
  obtain ⟨c', hc'⟩ :=
    AISafetyAtlas.Preference.plainKPolicy_le_plainKPairExact_of_compatible (S := Unit) (A := Bool)
      U hU
  exact ⟨⟨c, hc _ _ greedy_truePolicy⟩, ⟨c', hc' _ _ greedy_truePolicy⟩⟩

/-- **The greedy and anti-greedy pairs are cheap**: their exact complexity is at
most the plain complexity of `truePolicyCode` plus one constant. -/
public theorem degenerate_le_truePolicyCode (U : Map) (hU : isOptimalConditional U) :
    ∃ c : ℕ,
      AISafetyAtlas.Preference.plainKPairExact Unit Bool U
          (AISafetyAtlas.Preference.greedyOn false [true], rewardOf truePolicy) ≤
        plainK U truePolicyCode + (c : ENat) ∧
      AISafetyAtlas.Preference.plainKPairExact Unit Bool U
          (negPlanner (AISafetyAtlas.Preference.greedyOn false [true]), -rewardOf truePolicy) ≤
        plainK U truePolicyCode + (c : ENat) := by
  obtain ⟨c, hc⟩ :=
    AISafetyAtlas.Preference.plainKPairExact_degenerate_le (S := Unit) U hU false [true]
  have hK := plainKPolicy_le_of_codesPolicy U codesPolicy_truePolicy
  refine ⟨c, (hc truePolicy _ (by simp)).trans ?_, (hc truePolicy _ (by simp)).trans ?_⟩ <;>
    gcongr

/-- **Claim (2) at π̇**, in both codings: each degenerate pair is within one
constant of K(π̇) and of every pair compatible with π̇; here applied to the
greedy pair against the indifferent pair. -/
public theorem claim_two (U : Map) (hU : isOptimalConditional U) :
    (∃ c : ℕ,
      AISafetyAtlas.Preference.plainKPairExact Unit Bool U
          (AISafetyAtlas.Preference.greedyOn false [true], rewardOf truePolicy) ≤
        AISafetyAtlas.Preference.plainKPairExact Unit Bool U
          (indifferentPlanner truePolicy, 0) + (c : ENat)) ∧
    ∃ c : ℕ,
      AISafetyAtlas.Preference.plainKPairHybrid Unit Bool U
          (negPlanner (AISafetyAtlas.Preference.greedyOn false [true]), -rewardOf truePolicy) ≤
        plainKPolicy Unit Bool U truePolicy + (c : ENat) ∧
      plainKPolicy Unit Bool U truePolicy ≤
        AISafetyAtlas.Preference.plainKPairHybrid Unit Bool U
          (negPlanner (AISafetyAtlas.Preference.greedyOn false [true]), -rewardOf truePolicy) +
            (c : ENat) := by
  obtain ⟨c, hc⟩ := AISafetyAtlas.Preference.degenerate_near_minimal_exact (S := Unit) U hU covers
  obtain ⟨c', hc'⟩ :=
    AISafetyAtlas.Preference.degenerate_near_minimal_hybrid (S := Unit) U hU covers
  have h2 := hc' truePolicy
    (negPlanner (AISafetyAtlas.Preference.greedyOn false [true]), -rewardOf truePolicy) (by simp)
  have h1 := hc truePolicy
    (AISafetyAtlas.Preference.greedyOn false [true], rewardOf truePolicy) (by simp)
  exact ⟨⟨c, h1.2.2 (indifferentPlanner truePolicy, 0) rfl⟩, ⟨c', h2.2.1, h2.1⟩⟩

end AISafetyAtlas.Examples.Preference.RationalComplexity
