module

public import AISafetyAtlas.Wireheading.ProgramPriorTies

/-! A one-program model over the actions `WithBot ℤ`, whose order is not
well-founded: every action ties, the tie set has the least element `⊥`, and
print's lexicographic `A^μ` exists there although `ProgramPrior.Model.optimalAction`
(at `[WellFoundedLT Action]`) does not apply. The `Bool` instance checks the
agreement with `ProgramPrior` on a well-founded order. -/

namespace AISafetyAtlas.Examples.Wireheading.ProgramPriorTies

open AISafetyAtlas.Wireheading AgentEquations

/-- One program emitting the unit observation, over any action type. -/
@[expose] public def unitModel (Action : Type*) : ProgramPrior.Model Unit Action Unit where
  run := fun _ _ _ ↦ ()
  weight := fun _ ↦ 1
  nonneg := fun _ ↦ zero_le_one
  summable := Summable.of_finite

/-- Zero utility and zero horizon. -/
@[expose] public def zeroAgent (Action : Type*) : Agent Action Unit where
  utility := fun _ ↦ 0
  horizon := fun _ _ ↦ 0

/-- Every infinite action value of the zero agent is zero, under any belief. -/
public theorem zeroAgent_infiniteActionValue {Action : Type*} (ρ : Belief Action Unit) (t : ℕ)
    (h : History Action Unit) (a : Action) : infiniteActionValue ρ (zeroAgent Action) t h a = 0 := by
  have hv (h' : History Action Unit) : infiniteValue ρ (zeroAgent Action) t h' = 0 := by
    have hz : (fun n ↦ value ρ (zeroAgent Action) t n h') = fun _ ↦ 0 := funext fun n ↦
      value_eq_zero_of_horizon_vanishes ρ (zeroAgent Action) t 0 (fun _ _ ↦ rfl) n h'
        (Nat.zero_le _)
    rw [infiniteValue, hz]
    exact tendsto_const_nhds.limUnder_eq
  simp [infiniteActionValue, hv]

/-- On `WithBot ℤ` print's tie rule denotes at every history: the tie set is
everything, and `⊥` is its least element. -/
public theorem withBot_infLexAttains (h : History (WithBot ℤ) Unit) :
    InfLexAttains ((unitModel (WithBot ℤ)).point ()).belief (zeroAgent (WithBot ℤ)) h.length h :=
  ⟨⊥, fun b ↦ by simp [zeroAgent_infiniteActionValue], fun _ _ ↦ bot_le⟩

/-- **`A^μ` with print's tie rule on a non-well-founded action set** picks `⊥`. -/
public theorem withBot_optimalActionOfLeast (h : History (WithBot ℤ) Unit) :
    (unitModel (WithBot ℤ)).optimalActionOfLeast () (zeroAgent (WithBot ℤ)) h
      (withBot_infLexAttains h) = ⊥ :=
  le_bot_iff.mp (infiniteLexBestActionOfLeast_le _ _ _ _ _ (a := ⊥)
    (fun b ↦ by simp [zeroAgent_infiniteActionValue]))

/-- `A^μ`'s action there is optimal in the true environment. -/
public theorem withBot_optimalActionOfLeast_max (h : History (WithBot ℤ) Unit)
    (hc : (unitModel (WithBot ℤ)).Consistent () h) (b : WithBot ℤ) :
    infiniteActionValue (DelusionBox.diracBelief ((unitModel (WithBot ℤ)).run ()))
        (zeroAgent (WithBot ℤ)) h.length h b ≤
      infiniteActionValue (DelusionBox.diracBelief ((unitModel (WithBot ℤ)).run ()))
        (zeroAgent (WithBot ℤ)) h.length h
        ((unitModel (WithBot ℤ)).optimalActionOfLeast () (zeroAgent (WithBot ℤ)) h
          (withBot_infLexAttains h)) :=
  (unitModel (WithBot ℤ)).optimalActionOfLeast_max () _ h _ hc b

/-- **A learning agent copying `A^μ`'s lexicographic choice is optimal**, on the
non-well-founded action set, by `optimal_of_maximizer`. -/
public theorem withBot_optimal_of_maximizer (h : History (WithBot ℤ) Unit)
    (hc : (unitModel (WithBot ℤ)).Consistent () h) (b : WithBot ℤ) :
    infiniteActionValue (DelusionBox.diracBelief ((unitModel (WithBot ℤ)).run ()))
        (zeroAgent (WithBot ℤ)) h.length h b ≤
      infiniteActionValue (DelusionBox.diracBelief ((unitModel (WithBot ℤ)).run ()))
        (zeroAgent (WithBot ℤ)) h.length h
        ((unitModel (WithBot ℤ)).optimalPolicyOfLeast () (zeroAgent (WithBot ℤ))
          withBot_infLexAttains h) :=
  (unitModel (WithBot ℤ)).optimal_of_maximizer () (zeroAgent (WithBot ℤ)) List.length
    ((unitModel (WithBot ℤ)).optimalPolicyOfLeast () (zeroAgent (WithBot ℤ))
      withBot_infLexAttains)
    (fun h _ b ↦ by simp [zeroAgent_infiniteActionValue]) h hc b

/-- The same through `optimal_of_same_infiniteLexBestActionOfLeast`. -/
public theorem withBot_optimal_of_same_infiniteLexBestActionOfLeast
    (h : History (WithBot ℤ) Unit) (hc : (unitModel (WithBot ℤ)).Consistent () h)
    (b : WithBot ℤ) :
    infiniteActionValue (DelusionBox.diracBelief ((unitModel (WithBot ℤ)).run ()))
        (zeroAgent (WithBot ℤ)) h.length h b ≤
      infiniteActionValue (DelusionBox.diracBelief ((unitModel (WithBot ℤ)).run ()))
        (zeroAgent (WithBot ℤ)) h.length h
        ((unitModel (WithBot ℤ)).optimalPolicyOfLeast () (zeroAgent (WithBot ℤ))
          withBot_infLexAttains h) :=
  (unitModel (WithBot ℤ)).optimal_of_same_infiniteLexBestActionOfLeast () _ List.length
    withBot_infLexAttains _ (fun _ _ ↦ rfl) h hc b

/-- The same through `optimal_of_same_optimalActionOfLeast`. -/
public theorem withBot_optimal_of_same_optimalActionOfLeast
    (h : History (WithBot ℤ) Unit) (hc : (unitModel (WithBot ℤ)).Consistent () h)
    (b : WithBot ℤ) :
    infiniteActionValue (DelusionBox.diracBelief ((unitModel (WithBot ℤ)).run ()))
        (zeroAgent (WithBot ℤ)) h.length h b ≤
      infiniteActionValue (DelusionBox.diracBelief ((unitModel (WithBot ℤ)).run ()))
        (zeroAgent (WithBot ℤ)) h.length h
        ((unitModel (WithBot ℤ)).optimalPolicyOfLeast () (zeroAgent (WithBot ℤ))
          withBot_infLexAttains h) :=
  (unitModel (WithBot ℤ)).optimal_of_same_optimalActionOfLeast () _ withBot_infLexAttains _
    (fun _ _ ↦ rfl) h hc b

/-- `A^μ` is asymptotically optimal on the non-well-founded action set. -/
public theorem withBot_asymptoticallyOptimalOfLeast :
    (unitModel (WithBot ℤ)).AsymptoticallyOptimalOfLeast () (zeroAgent (WithBot ℤ))
      withBot_infLexAttains
      ((unitModel (WithBot ℤ)).optimalPolicyOfLeast () (zeroAgent (WithBot ℤ))
        withBot_infLexAttains) :=
  (unitModel (WithBot ℤ)).asymptoticallyOptimalOfLeast_optimalPolicyOfLeast () _ _

open Classical in
/-- Its mistake indicator tends to zero. -/
public theorem withBot_mistake_tendsto :
    Filter.Tendsto (fun k ↦ if (unitModel (WithBot ℤ)).MistakeOfLeast () (zeroAgent (WithBot ℤ))
        withBot_infLexAttains
        ((unitModel (WithBot ℤ)).optimalPolicyOfLeast () (zeroAgent (WithBot ℤ))
          withBot_infLexAttains)
        (ProgramPrior.trajectory ((unitModel (WithBot ℤ)).run ())
          ((unitModel (WithBot ℤ)).optimalPolicyOfLeast () (zeroAgent (WithBot ℤ))
            withBot_infLexAttains) k)
      then (1 : ℝ) else 0) Filter.atTop (nhds 0) :=
  ((unitModel (WithBot ℤ)).asymptoticallyOptimalOfLeast_iff_tendsto () _ _ _).mp
    withBot_asymptoticallyOptimalOfLeast

/-- The trajectory after k steps of the one-program model has length k. -/
public theorem unitModel_trajectory_length (π : History (WithBot ℤ) Unit → WithBot ℤ) (k : ℕ) :
    (ProgramPrior.trajectory ((unitModel (WithBot ℤ)).run ()) π k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ProgramPrior.trajectory, ih]

/-- A policy that departs from A^μ's ⊥ at the empty history only. -/
@[expose] public def errOnceBot : History (WithBot ℤ) Unit → WithBot ℤ :=
  fun h ↦ if h.isEmpty then ((0 : ℤ) : WithBot ℤ) else ⊥

/-- It does make a mistake: at the start. -/
public theorem errOnceBot_mistake :
    (unitModel (WithBot ℤ)).MistakeOfLeast () (zeroAgent (WithBot ℤ)) withBot_infLexAttains
      errOnceBot (ProgramPrior.trajectory ((unitModel (WithBot ℤ)).run ()) errOnceBot 0) := by
  simp only [ProgramPrior.Model.MistakeOfLeast, ProgramPrior.Model.optimalPolicyOfLeast,
    withBot_optimalActionOfLeast]
  simp [errOnceBot, ProgramPrior.trajectory]

/-- **It is asymptotically optimal at the per-step reading**: no mistake after the
first step. -/
public theorem errOnceBot_asymptoticallyOptimalOfLeast :
    (unitModel (WithBot ℤ)).AsymptoticallyOptimalOfLeast () (zeroAgent (WithBot ℤ))
      withBot_infLexAttains errOnceBot := by
  rw [ProgramPrior.Model.AsymptoticallyOptimalOfLeast, Filter.eventually_atTop]
  refine ⟨1, fun k hk => ?_⟩
  have hne : ProgramPrior.trajectory ((unitModel (WithBot ℤ)).run ()) errOnceBot k ≠ [] := by
    intro he
    have := unitModel_trajectory_length errOnceBot k
    rw [he] at this
    simp at this
    omega
  simp only [ProgramPrior.Model.MistakeOfLeast, ProgramPrior.Model.optimalPolicyOfLeast,
    withBot_optimalActionOfLeast, not_not]
  simp [errOnceBot, hne]

/-- **And so at the rate reading**
(`asymptoticallyOptimalRateOfLeast_of_asymptoticallyOptimalOfLeast`): one mistake
in the first n steps, a fraction 1/n tending to zero. -/
public theorem errOnceBot_asymptoticallyOptimalRateOfLeast :
    (unitModel (WithBot ℤ)).AsymptoticallyOptimalRateOfLeast () (zeroAgent (WithBot ℤ))
      withBot_infLexAttains errOnceBot :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.asymptoticallyOptimalRateOfLeast_of_asymptoticallyOptimalOfLeast
    (unitModel (WithBot ℤ)) () (zeroAgent (WithBot ℤ)) withBot_infLexAttains errOnceBot
    errOnceBot_asymptoticallyOptimalOfLeast

/-- On `Bool` the lexicographic rule denotes at every history (finite, well-founded). -/
public theorem bool_infLexAttains {ag : Agent Bool Unit} (h : History Bool Unit) :
    InfLexAttains ((unitModel Bool).point ()).belief ag h.length h :=
  infLexAttains_of_infAttains (infAttains_of_fintype _ _ _ h)

/-- Same actions, same prediction mistakes, at the `Bool` instance. -/
public theorem bool_same_prediction_mistakes (predict : History Bool Unit → Unit) (k : ℕ) :
    (DelusionBox.predictionAgent predict 1).utility
        (ProgramPrior.trajectory ((unitModel Bool).run ())
          ((unitModel Bool).optimalPolicyOfLeast () (DelusionBox.predictionAgent predict 1)
            bool_infLexAttains) k) =
      (DelusionBox.predictionAgent predict 1).utility
        (ProgramPrior.trajectory ((unitModel Bool).run ())
          ((unitModel Bool).optimalPolicyOfLeast () (DelusionBox.predictionAgent predict 1)
            bool_infLexAttains) k) :=
  (unitModel Bool).same_prediction_mistakes_of_least () predict 1 bool_infLexAttains _
    (fun _ ↦ rfl) k

/-- On `Bool` the least-maximiser `A^μ` is `ProgramPrior`'s `optimalAction`. -/
public theorem bool_optimalActionOfLeast_eq (h : History Bool Unit) :
    (unitModel Bool).optimalActionOfLeast () (zeroAgent Bool) h (bool_infLexAttains h) =
      (unitModel Bool).optimalAction () (zeroAgent Bool) h (infAttains_of_fintype _ _ _ h) :=
  (unitModel Bool).optimalActionOfLeast_eq_optimalAction () _ h _ _

/-- On `Bool` the two mistake notions agree. -/
public theorem bool_mistakeOfLeast_iff (π : History Bool Unit → Bool) (h : History Bool Unit) :
    (unitModel Bool).MistakeOfLeast () (zeroAgent Bool) (fun h ↦ bool_infLexAttains h) π h ↔
      (unitModel Bool).Mistake () (zeroAgent Bool)
        (fun h ↦ infAttains_of_fintype _ _ _ h) π h :=
  (unitModel Bool).mistakeOfLeast_iff_mistake () _ _ _ π h

/-- On `Bool` the two asymptotic-optimality notions agree. -/
public theorem bool_asymptoticallyOptimalOfLeast_iff (π : History Bool Unit → Bool) :
    (unitModel Bool).AsymptoticallyOptimalOfLeast () (zeroAgent Bool)
        (fun h ↦ bool_infLexAttains h) π ↔
      (unitModel Bool).AsymptoticallyOptimal () (zeroAgent Bool)
        (fun h ↦ infAttains_of_fintype _ _ _ h) π :=
  (unitModel Bool).asymptoticallyOptimalOfLeast_iff () _ _ _ π

end AISafetyAtlas.Examples.Wireheading.ProgramPriorTies
