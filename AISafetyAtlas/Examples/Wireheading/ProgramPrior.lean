module

public import AISafetyAtlas.Wireheading.ProgramPrior

/-! A two-program prior: each program always emits its own Boolean code. One
observation eliminates half the prior; the normalized observation product is
proved equal to the retained mass. -/

namespace AISafetyAtlas.Examples.Wireheading.ProgramPrior

open AISafetyAtlas.Wireheading AgentEquations

/-- Two deterministic programs, initially equally likely. -/
@[expose] public noncomputable def twoPrograms : ProgramPrior.Model Bool Unit Bool where
  run := fun q _ _ ↦ q
  weight := fun _ ↦ 1 / 2
  nonneg := by intro q; norm_num
  summable := Summable.of_finite

/-- Both programs are initially possible. -/
public theorem mass_empty : twoPrograms.mass [] = 1 := by
  rw [ProgramPrior.Model.mass_nil, tsum_fintype]
  norm_num [twoPrograms, Fintype.sum_bool]

/-- Observing true discards exactly the false-output program. -/
public theorem mass_true : twoPrograms.mass [((), true)] = 1 / 2 := by
  classical
  have hc (q : Bool) : twoPrograms.Consistent q [((), true)] ↔ q = true := by
    simpa [ProgramPrior.Model.Consistent.nil, twoPrograms] using
      twoPrograms.consistent_snoc q [] () true
  rw [ProgramPrior.Model.mass, tsum_fintype]
  simp only [Fintype.sum_bool, Set.indicator_apply, Set.mem_ofPred_eq, hc]
  norm_num [twoPrograms]

/-- The product of induced conditionals recovers the normalized prior mass. -/
public theorem product_mass_true : historyMass twoPrograms.belief [((), true)] = 1 / 2 := by
  rw [twoPrograms.historyMass_eq_mass mass_empty, mass_true]

/-- The literal mortality horizon differs from the delusion horizon on this program model. -/
public theorem knowledge_horizons_differ :
    (twoPrograms.companionKnowledgeAgent 2).horizon 1 1 ≠
      (twoPrograms.knowledgeAgent 2).horizon 1 1 :=
  DelusionBox.knowledgeAgent_horizon_ne twoPrograms.mass

/-- The probability bounds apply to a concrete program prior, with no extra probability premise. -/
public theorem value_bound (ag : Agent Unit Bool) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Unit Bool) :
    |value twoPrograms.belief ag t n h| ≤ horizonBudget ag t n h.length :=
  abs_value_le_horizonBudget twoPrograms.belief_isSubprobability ag hu t n h

/-- After observing true, the posterior expectation uses only the surviving
program. This exercises the program/observation sum interchange at a nonempty history. -/
public theorem posterior_true :
    (∑' o, twoPrograms.belief.cond [((), true)] () o * (if o then (1 : ℝ) else 0)) = 1 := by
  have hf (o : Bool) : |if o then (1 : ℝ) else 0| ≤ 1 := by cases o <;> norm_num
  rw [twoPrograms.expectation_eq_programSum _ _ _ hf, mass_true, tsum_fintype]
  have hc (q : Bool) : twoPrograms.Consistent q [((), true)] ↔ q = true := by
    simpa [ProgramPrior.Model.Consistent.nil, twoPrograms] using
      twoPrograms.consistent_snoc q [] () true
  simp only [Fintype.sum_bool, Set.indicator_apply, Set.mem_ofPred_eq, hc]
  norm_num [twoPrograms]

/-! ## The remaining program-prior identities, at `twoPrograms`

`value_bound` and `posterior_true` already take an arbitrary agent. The four
below need a concrete one, so that the bounded-utility hypothesis is met rather
than carried.
-/

/-- An agent whose utility is identically zero, and so bounded by one. -/
@[expose] public def nullAgent : Agent Unit Bool where
  utility := fun _ ↦ 0
  horizon := fun _ _ ↦ 1

/-- Its utility is bounded, which is the hypothesis the value lemmas take. -/
public theorem nullAgent_bounded (h : History Unit Bool) :
    |nullAgent.utility h| ≤ 1 := by
  simp [nullAgent]

/-- **Mass times conditional is the extended mass**: the prior renormalizes
exactly, with no leak. -/
public theorem twoPrograms_mass_mul_cond (o : Bool) :
    twoPrograms.mass [] * twoPrograms.belief.cond [] () o
      = twoPrograms.mass ([] ++ [((), o)]) :=
  twoPrograms.mass_mul_cond [] () o

/-- **A surviving program's relative weight can only rise.** `true` survives the
observation `true`, and its prior weight is positive, so both hypotheses hold
here rather than being assumed. -/
public theorem twoPrograms_relative_weight_le :
    twoPrograms.weight true / twoPrograms.mass []
      ≤ twoPrograms.weight true / twoPrograms.mass ([] ++ [((), true)]) := by
  refine twoPrograms.relative_weight_le true [] () true ?_ (by norm_num [twoPrograms])
  simpa [ProgramPrior.Model.Consistent.nil, twoPrograms] using
    (twoPrograms.consistent_snoc true [] () true).mpr
      ⟨ProgramPrior.Model.Consistent.nil, rfl⟩

/-- **On a consistent history the mixture collapses to the single program**, so
the prior adds nothing the point model does not already say. -/
public theorem twoPrograms_value_point_eq (t n : ℕ) :
    value (twoPrograms.point true).belief nullAgent t n []
      = value (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent t n [] :=
  twoPrograms.value_point_eq true nullAgent t n [] ProgramPrior.Model.Consistent.nil

/-- **The action value is a sum over consistent programs**, normalized by the
surviving mass. -/
public theorem twoPrograms_actionValue_eq_programSum (t n : ℕ) :
    actionValue twoPrograms.belief nullAgent t n [] ()
      = (∑' q, {q | twoPrograms.Consistent q []}.indicator twoPrograms.weight q *
          value twoPrograms.belief nullAgent t n ([] ++ [((), twoPrograms.run q [] ())]))
        / twoPrograms.mass [] :=
  twoPrograms.actionValue_eq_programSum nullAgent nullAgent_bounded t n [] ()

/-! ## Statement 3's prior inequality, on this model

Print's Statement 3 takes `𝒬_B` to be the set of environments containing a
delusion box and `q_b ∈ 𝒬_B` the true one, and runs on `ρ(q_b) < ρ(𝒬_B)`. Here
both programs are the whole set, so the inequality is strict on it and the mass
of the set is the total prior mass.

What print does **not** prove, and what is therefore not here, is the next step:
*"it takes fewer errors to converge to `𝒬_B` than to `q_b`"*, which print's own
preceding sentence sources to another paper — *"a predictor makes approximately
`−log(ρ(q))` errors [2]"*.
-/

/-- The two-program set is print's `𝒬_B`, and it carries the whole prior mass. -/
public theorem setMass_univ : twoPrograms.setMass (Set.univ : Set Bool) = 1 := by
  rw [ProgramPrior.Model.setMass, tsum_fintype]
  norm_num [twoPrograms, Fintype.sum_bool]

/-- **Print's `ρ(q_b) ≤ ρ(𝒬_B)`** at the true program. -/
public theorem weight_le_setMass_univ :
    twoPrograms.weight true ≤ twoPrograms.setMass (Set.univ : Set Bool) :=
  twoPrograms.weight_le_setMass (Set.mem_univ true)

/-- **And print's strict `<`**, because the class contains a second program of
positive weight — which is what makes `𝒬_B` a class rather than a singleton. -/
public theorem weight_lt_setMass_univ :
    twoPrograms.weight true < twoPrograms.setMass (Set.univ : Set Bool) :=
  twoPrograms.weight_lt_setMass (Set.mem_univ true) (Set.mem_univ false)
    (by decide) (by norm_num [twoPrograms])

/-- The set mass is nonnegative, and the history mass is the set mass at the
consistent programs. -/
public theorem mass_eq_setMass_true :
    twoPrograms.mass [((), true)]
      = twoPrograms.setMass {q | twoPrograms.Consistent q [((), true)]} :=
  twoPrograms.mass_eq_setMass _

/-- Set masses are nonnegative here as everywhere. -/
public theorem setMass_univ_nonneg :
    0 ≤ twoPrograms.setMass (Set.univ : Set Bool) :=
  twoPrograms.setMass_nonneg _

end AISafetyAtlas.Examples.Wireheading.ProgramPrior
