module

public import AISafetyAtlas.Preference.SourceComplexity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Propositions 7 and 8, source parameterization, at the constant-zero language

`ReasonableForF` needs no work to instantiate: the all-zero complexity
assignment is trivially `0`-reasonable for `F`, since every inequality reduces
to `0 ≤ 0`. This is enough to exercise the compatibility lemmas, which do not
depend on the constant being nontrivial.
-/

namespace AISafetyAtlas.Examples.Preference

open AISafetyAtlas.Preference.Source

/-- The constant-zero complexity assignment: `0`-reasonable for `F`, trivially. -/
public def zeroLanguage : ReasonableForF Bool Bool where
  KPair := fun _ => 0
  c := 0
  F_complexity_le := fun _ _ => le_refl 0

/-- `Compatible` and `ReasonableLanguage.Compatible` agree, at a concrete
policy and its indifferent pair. -/
theorem zeroLanguage_compatible_iff (π : AISafetyAtlas.Preference.Policy Bool Bool) :
    ReasonableForF.Compatible (S := Bool) (A := Bool)
        (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π)) π ↔
      AISafetyAtlas.Preference.ReasonableLanguage.Compatible
        (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π)) π :=
  ReasonableForF.compatible_iff _ π

/-- Negating `AmongLowestCompatible` is `NotAmongLowestCompatible`, at the
indifferent pair for a concrete policy. -/
theorem zeroLanguage_notAmongLowest_iff (π : AISafetyAtlas.Preference.Policy Bool Bool) :
    zeroLanguage.NotAmongLowestCompatible π
        (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π)) ↔
      ¬ zeroLanguage.AmongLowestCompatible π
        (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π)) :=
  ReasonableForF.notAmongLowest_iff zeroLanguage π _
    (ReasonableForF.compatible_indifferent π)

/-! ## Armstrong and Mindermann's three propositions, at the zero language

`zeroLanguage` inhabits `ReasonableForF` with no work at all, which is the point
of the abstraction. What it was not used for is running the three numbered
results that quantify over every such language.
-/

/-- **Proposition 7.** The three degenerate planner-reward pairs are all among
the lowest-complexity explanations of any policy — which is the statement that
makes the degeneracy a problem rather than a curiosity. -/
public theorem zero_proposition_seven (π : AISafetyAtlas.Preference.Policy Bool Bool) :
    zeroLanguage.AmongLowestCompatible π
        (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π)) ∧
      zeroLanguage.AmongLowestCompatible π
        (AISafetyAtlas.Preference.op2 (AISafetyAtlas.Preference.op6 π)) ∧
      zeroLanguage.AmongLowestCompatible π
        (AISafetyAtlas.Preference.op4
          (AISafetyAtlas.Preference.op2 (AISafetyAtlas.Preference.op6 π))) :=
  ReasonableForF.proposition_seven zeroLanguage π

/-- **Proposition 8.** Negating the reward preserves compatibility and moves the
complexity by at most the language's constant, in both directions. So the
anti-rational pair is no harder to write down than the intended one. -/
public theorem zero_proposition_eight {x : AISafetyAtlas.Preference.Pair Bool Bool}
    {π : AISafetyAtlas.Preference.Policy Bool Bool}
    (h : AISafetyAtlas.Preference.Source.ReasonableForF.Compatible x π) :
    AISafetyAtlas.Preference.Source.ReasonableForF.Compatible (AISafetyAtlas.Preference.Source.F₄ x) π ∧
      zeroLanguage.KPair (AISafetyAtlas.Preference.Source.F₄ x) ≤ zeroLanguage.KPair x + zeroLanguage.c ∧
      zeroLanguage.KPair x ≤ zeroLanguage.KPair (AISafetyAtlas.Preference.Source.F₄ x) + zeroLanguage.c :=
  ReasonableForF.proposition_eight zeroLanguage h

/-- **Theorem 2, conditionally.** If the intended pair is *not* among the lowest,
all three degenerate pairs are strictly simpler than it — so complexity does not
single out the intended explanation, it actively prefers the degenerate ones. -/
public theorem zero_theorem_two (π : AISafetyAtlas.Preference.Policy Bool Bool)
    (intended : AISafetyAtlas.Preference.Pair Bool Bool)
    (h9 : zeroLanguage.NotAmongLowestCompatible π intended) :
    zeroLanguage.KPair (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 π))
        < zeroLanguage.KPair intended ∧
      zeroLanguage.KPair (AISafetyAtlas.Preference.op2 (AISafetyAtlas.Preference.op6 π))
        < zeroLanguage.KPair intended ∧
      zeroLanguage.KPair (AISafetyAtlas.Preference.op4
          (AISafetyAtlas.Preference.op2 (AISafetyAtlas.Preference.op6 π)))
        < zeroLanguage.KPair intended :=
  ReasonableForF.theorem_two_conditional zeroLanguage π intended h9

/-! ## Print's definitions at an arbitrary complexity and constant

Witnesses for the source-parity definitions of §3 and §5.1 that need no
reasonable language: the bounded reward space, comparable complexity, lowest
complexity in an arbitrary set, and the `F`-complexity.
-/

section PrintDefinitions

open AISafetyAtlas.Preference

/-- `R_π` at the identity policy, as an element of print's reward space
`[-1, 1]^{𝒮×𝒜}`. -/
public def rewardOfIdBounded : BoundedRewardFn Bool Bool :=
  ⟨rewardOf id, isBoundedReward_rewardOf id⟩

/-- The three rewards the degenerate pairs carry -- `0`, `R_π` and `-R_π` --
are all in print's reward space. -/
public theorem degenerate_rewards_bounded (π : Policy Bool Bool) :
    IsBoundedReward (0 : RewardFn Bool Bool) ∧ IsBoundedReward (rewardOf π) ∧
      IsBoundedReward (-rewardOf π) :=
  ⟨isBoundedReward_zero, isBoundedReward_rewardOf π,
    AISafetyAtlas.Preference.IsBoundedReward.neg (isBoundedReward_rewardOf π)⟩

/-- A complexity that charges `1` for a pair whose reward pays at `(true, true)`
and `0` otherwise. Not a Kolmogorov complexity; it only has to tell the
indifferent pair from the greedy pair. -/
public noncomputable def payComplexity : Pair Bool Bool → ℕ := fun x =>
  open Classical in if x.2 true true = 0 then 0 else 1

private theorem payComplexity_indifferent (π : Policy Bool Bool) :
    payComplexity (op1 (op5 π)) = 0 := by
  simp [payComplexity, op1]

private theorem payComplexity_greedy_id :
    payComplexity (op2 (op6 (id : Policy Bool Bool))) = 1 := by
  simp [payComplexity, op2, op6, rewardOf]

/-- The set of the source's defect instance for `am-lowest`: the indifferent
pair and the greedy pair for the identity policy. -/
public noncomputable def twoPairs : Set (Pair Bool Bool) :=
  {op1 (op5 id), op2 (op6 id)}

/-- **Lowest complexity in an arbitrary set**, at a two-element set that is not
a compatible set of any language: the indifferent pair is amongst the lowest at
`c = 0`. -/
public theorem indifferent_amongLowest_twoPairs :
    AmongLowest payComplexity 0 twoPairs (op1 (op5 id)) := by
  refine ⟨Or.inl rfl, fun y _ => ?_⟩
  rw [payComplexity_indifferent]
  simp

/-- ...and the greedy pair is not, so the definition is not vacuous at this
set. -/
public theorem greedy_not_amongLowest_twoPairs :
    ¬ AmongLowest payComplexity 0 twoPairs (op2 (op6 id)) := by
  rintro ⟨-, h⟩
  have := h (op1 (op5 id)) (Or.inl rfl)
  rw [payComplexity_indifferent, payComplexity_greedy_id] at this
  norm_num at this

/-- **Comparable complexity**, at `c = 1`, between the indifferent and the greedy
pair, which are not negations of each other; at `c = 0` they are not
comparable. -/
public theorem indifferent_greedy_comparable :
    ComparableComplexity payComplexity 1 (op1 (op5 id)) (op2 (op6 id)) ∧
      ¬ ComparableComplexity payComplexity 0 (op1 (op5 id)) (op2 (op6 id)) := by
  unfold ComparableComplexity
  rw [payComplexity_indifferent, payComplexity_greedy_id]
  norm_num

/-- `ComparableComplexity.symm`, at the same two pairs. -/
public theorem greedy_indifferent_comparable :
    ComparableComplexity payComplexity 1 (op2 (op6 id)) (op1 (op5 id)) :=
  AISafetyAtlas.Preference.ComparableComplexity.symm indifferent_greedy_comparable.1

/-- **The `F`-complexity of the zero language is `0`**: at most its constant
`0` by `fComplexity_le`, and non-negative by footnote 10. -/
public theorem zeroLanguage_fComplexity :
    fComplexity zeroLanguage.KPair = 0 :=
  le_antisymm ((zeroLanguage.fComplexity_le).trans_eq (by simp [zeroLanguage]))
    (fComplexity_nonneg _)

/-- `AmongLowestCompatible` read as `AmongLowest` at the compatible set. -/
public theorem zeroLanguage_amongLowest (π : Policy Bool Bool) :
    AmongLowest zeroLanguage.KPair zeroLanguage.c {y | ReasonableForF.Compatible y π}
      (op1 (op5 π)) :=
  (ReasonableForF.amongLowestCompatible_iff zeroLanguage π _).mp
    (ReasonableForF.indifferent_amongLowest zeroLanguage π)

/-- **Proposition 8 in print's vocabulary**, source parameterization, at a
compatible pair. -/
public theorem zero_proposition_eight_comparable (π : Policy Bool Bool) :
    ReasonableForF.Compatible (F₄ (op1 (op5 π))) π ∧
      ComparableComplexity zeroLanguage.KPair zeroLanguage.c (op1 (op5 π))
        (F₄ (op1 (op5 π))) :=
  AISafetyAtlas.Preference.Source.ReasonableForF.proposition_eight_comparable zeroLanguage
    (ReasonableForF.compatible_indifferent π)

/-- The all-zero assignment as a `ReasonableLanguage`, the reparameterized
interface, so that its Proposition 8 corollary can be applied. -/
public def zeroReasonableLanguage : ReasonableLanguage Bool Bool where
  KPair := fun _ => 0
  KPolicy := fun _ => 0
  c := 0
  eval_le := fun _ => le_refl 0
  indifferent_le := fun _ => le_refl 0
  greedy_le := fun _ => le_refl 0
  antirational_le := fun _ => le_refl 0
  neg_le := fun _ => le_refl 0

/-- **Proposition 8 in print's vocabulary**, reparameterized interface, at a
compatible pair. -/
public theorem zeroReasonable_proposition_eight_comparable (π : Policy Bool Bool) :
    ReasonableLanguage.Compatible (op4 (op1 (op5 π))) π ∧
      ComparableComplexity zeroReasonableLanguage.KPair zeroReasonableLanguage.c
        (op1 (op5 π)) (op4 (op1 (op5 π))) :=
  AISafetyAtlas.Preference.ReasonableLanguage.proposition_eight_comparable
    zeroReasonableLanguage π _ (op3_op1_op5 π)

/-- Print's min form of "amongst the lowest", at `payComplexity` on all pairs. -/
example := AISafetyAtlas.Preference.amongLowest_iff_min payComplexity 0 Set.univ

end PrintDefinitions

/-! ## Proposition 7 at a real-valued measure, from the `F₁` bound alone

`zeroOneMeasure` is real-valued and charges `1` to a pair with a nonzero reward
and `0` otherwise. `F₁` always outputs the zero reward, so its bound holds at
`c = 0`; `F₂` outputs the greedy pair with a nonzero reward, so its bound fails
at `c = 0`, and the measure is not `0`-reasonable for `F`. The first clause of
Proposition 10 still applies to it. -/

section MeasureWide

open AISafetyAtlas.Preference

open scoped Classical in
/-- A real-valued complexity measure: `0` on pairs with the zero reward, `1`
otherwise. -/
public noncomputable def zeroOneMeasure (x : Pair Bool Bool) : ℝ :=
  if x.2 = 0 then 0 else 1

private theorem zeroOneMeasure_nonneg (x : Pair Bool Bool) : 0 ≤ zeroOneMeasure x := by
  unfold zeroOneMeasure; split_ifs <;> norm_num

/-- The `F₁` bound holds at `c = 0`: `F₁` outputs the zero reward. -/
public theorem zeroOneMeasure_F₁_le (x : Pair Bool Bool) :
    zeroOneMeasure (F₁ x) ≤ zeroOneMeasure x + 0 := by
  have h : zeroOneMeasure (F₁ x) = 0 := by
    unfold zeroOneMeasure F₁ op1
    simp
  rw [h, add_zero]
  exact zeroOneMeasure_nonneg x

/-- The `F₂` bound fails at `c = 0`, so no `0`-reasonable language for `F` has
this measure. -/
public theorem not_zeroOneMeasure_F₂_le :
    ¬ ∀ x : Pair Bool Bool, zeroOneMeasure (F₂ x) ≤ zeroOneMeasure x + 0 := by
  intro h
  have hb := h (op1 (op5 (fun _ => true)))
  have h0 : zeroOneMeasure (op1 (op5 (fun _ => true))) = 0 := by
    unfold zeroOneMeasure op1; simp
  have h1 : zeroOneMeasure (F₂ (op1 (op5 (fun _ => true)))) = 1 := by
    unfold zeroOneMeasure
    rw [if_neg]
    intro hz
    have := congrFun (congrFun hz true) true
    simp [F₂, op2, op6, op3, op1, op5, indifferentPlanner, rewardOf] at this
  rw [h0, h1] at hb
  norm_num at hb

/-- **Proposition 10, first clause, at the witness**: the indifferent pair is
amongst the lowest under a real-valued measure that only the `F₁` bound
controls. -/
public theorem zeroOneMeasure_indifferent_amongLowestFor (π : Policy Bool Bool) :
    AmongLowestFor zeroOneMeasure 0 π (op1 (op5 π)) :=
  indifferent_amongLowestFor zeroOneMeasure 0 zeroOneMeasure_F₁_le π

/-- **Proposition 7 at a real-valued measure**, at the constant measure
`log 2` with constant `0`: every composite bound holds. -/
public theorem log_two_proposition_seven (π : Policy Bool Bool) :
    AmongLowestFor (fun _ : Pair Bool Bool => Real.log 2) 0 π (op1 (op5 π)) ∧
      AmongLowestFor (fun _ : Pair Bool Bool => Real.log 2) 0 π (op2 (op6 π)) ∧
      AmongLowestFor (fun _ : Pair Bool Bool => Real.log 2) 0 π (op4 (op2 (op6 π))) :=
  proposition_seven_of_bounds _ 0 (fun _ _ => by simp) π

/-- The two greedy-side lemmas, at the constant measure. -/
example (π : Policy Bool Bool) :
    AmongLowestFor (fun _ : Pair Bool Bool => (0 : ℝ)) 0 π (op2 (op6 π)) ∧
      AmongLowestFor (fun _ : Pair Bool Bool => (0 : ℝ)) 0 π (op4 (op2 (op6 π))) :=
  ⟨greedy_amongLowestFor _ 0 (fun _ => by simp) π,
    antirational_amongLowestFor _ 0 (fun _ => by simp) π⟩

/-- The language structure's predicate is the natural-valued case, at the
zero language. -/
example (π : Policy Bool Bool) (x : Pair Bool Bool) :
    zeroLanguage.AmongLowestCompatible π x ↔ AmongLowestFor zeroLanguage.KPair zeroLanguage.c π x :=
  ReasonableForF.amongLowestCompatible_iff_amongLowestFor zeroLanguage π x

end MeasureWide

/-- Conjecture 9's antecedent is inhabited: the zero language, the policy
`id` and its indifferent pair meet every premise when each predicate admits
them, and Proposition 7 then refutes the conjecture at that degenerate choice. -/
example : ¬ AISafetyAtlas.Preference.Source.ConjectureNine (S := Bool) (A := Bool)
    (· = zeroLanguage) (· = id)
    (· = AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 id)) :=
  AISafetyAtlas.Preference.Source.not_conjectureNine_of_indifferent rfl rfl rfl

/-- A language in which Conjecture 9 holds at one pair: complexity `1` on pairs
whose reward at `(true, true)` has absolute value `2`, and `0` elsewhere. The
composites `F₁`, `F₂`, `F₃` produce rewards valued in `{0, 1, -1}` and `F₄`
negates the reward, so the language is `0`-reasonable for `F`. -/
public noncomputable def spikeLanguage : ReasonableForF Bool Bool where
  KPair := fun x => open Classical in if |x.2 true true| = 2 then 1 else 0
  c := 0
  F_complexity_le := by
    intro i x
    fin_cases i <;>
      simp [Fmap, F₁, F₂, F₃, F₄, AISafetyAtlas.Preference.op1, AISafetyAtlas.Preference.op2,
        AISafetyAtlas.Preference.op3, AISafetyAtlas.Preference.op4,
        AISafetyAtlas.Preference.op6, AISafetyAtlas.Preference.rewardOf] <;>
      split_ifs <;> norm_num at *

/-- The pair that `spikeLanguage` charges: a planner returning `id` on every
reward, with the constant reward `2`. -/
public def spikePair : AISafetyAtlas.Preference.Pair Bool Bool := (fun _ => id, fun _ _ => 2)

/-- Conjecture 9 holds when the reasonable language is `spikeLanguage`, the human
policy is `id` and the reasonable pair is `spikePair`: the indifferent pair is
compatible and cheaper by more than `c = 0`. -/
public theorem spike_conjectureNine :
    AISafetyAtlas.Preference.Source.ConjectureNine (· = spikeLanguage) (· = id) (· = spikePair) := by
  rintro L rfl π rfl x rfl hc
  refine ⟨hc, AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 id),
    ReasonableForF.compatible_indifferent id, ?_⟩
  simp [spikeLanguage, spikePair, AISafetyAtlas.Preference.op1]

/-- Theorem 2's lower-complexity half from Conjecture 9, at a language where the
conjecture holds: each degenerate pair costs `0` against `spikePair`'s `1`. -/
example :
    spikeLanguage.KPair (AISafetyAtlas.Preference.op1 (AISafetyAtlas.Preference.op5 id)) <
        spikeLanguage.KPair spikePair ∧
      spikeLanguage.KPair (AISafetyAtlas.Preference.op2 (AISafetyAtlas.Preference.op6 id)) <
        spikeLanguage.KPair spikePair ∧
      spikeLanguage.KPair (AISafetyAtlas.Preference.op4
          (AISafetyAtlas.Preference.op2 (AISafetyAtlas.Preference.op6 id))) <
        spikeLanguage.KPair spikePair :=
  AISafetyAtlas.Preference.Source.ConjectureNine.theorem_two spike_conjectureNine rfl rfl rfl rfl

end AISafetyAtlas.Examples.Preference
