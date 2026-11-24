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

/-! ## The optimal variant at the infinite-horizon value, at `twoPrograms` -/

/-- Equation (2) at the point prior is equation (2) at the non-learning belief. -/
public theorem twoPrograms_actionValue_point_eq (t n : ℕ) :
    actionValue (twoPrograms.point true).belief nullAgent t n [] ()
      = actionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent t n [] () :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.actionValue_point_eq twoPrograms true nullAgent t n [] ProgramPrior.Model.Consistent.nil ()

/-- **The infinite-horizon value at the point prior is the non-learning one.** -/
public theorem twoPrograms_infiniteValue_point_eq (t : ℕ) :
    infiniteValue (twoPrograms.point true).belief nullAgent t []
      = infiniteValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent t [] :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.infiniteValue_point_eq twoPrograms true nullAgent t [] ProgramPrior.Model.Consistent.nil

/-- The same for infinite-horizon action values. -/
public theorem twoPrograms_infiniteActionValue_point_eq (t : ℕ) :
    infiniteActionValue (twoPrograms.point true).belief nullAgent t [] ()
      = infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent t [] () :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.infiniteActionValue_point_eq twoPrograms true nullAgent t [] ProgramPrior.Model.Consistent.nil ()

/-- **Taking `A^μ`'s depth-`n` actions is optimal in the true environment**: the
policy that copies `bestAction` at the point prior satisfies the hypothesis by
construction. -/
public theorem twoPrograms_optimal_of_same_bestAction (n : ℕ) (h : History Unit Bool)
    (hc : twoPrograms.Consistent true h) (b : Unit) :
    actionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent h.length n h b ≤
      actionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent h.length n h
        (bestAction (twoPrograms.point true).belief nullAgent h.length n h
          (attains_of_fintype _ _ _ _ _)) :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.optimal_of_same_bestAction twoPrograms true nullAgent List.length n
    (fun _ => attains_of_fintype _ _ _ _ _) _ (fun _ _ => rfl) h hc b

/-- The same at the infinite-horizon value. -/
public theorem twoPrograms_optimal_of_same_infiniteBestAction (h : History Unit Bool)
    (hc : twoPrograms.Consistent true h) (b : Unit) :
    infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent h.length h b ≤
      infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent h.length h
        (infiniteBestAction (twoPrograms.point true).belief nullAgent h.length h
          (infAttains_of_fintype _ _ _ _)) :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.optimal_of_same_infiniteBestAction twoPrograms true nullAgent List.length
    (fun _ => infAttains_of_fintype _ _ _ _) _ (fun _ _ => rfl) h hc b

/-- And along the whole trajectory the copying policy generates. -/
public theorem twoPrograms_optimal_along_trajectory (k : ℕ) (b : Unit) :
    let π : History Unit Bool → Unit := fun h =>
      infiniteBestAction (twoPrograms.point true).belief nullAgent h.length h
        (infAttains_of_fintype _ _ _ _)
    infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent
        (ProgramPrior.trajectory (twoPrograms.run true) π k).length
        (ProgramPrior.trajectory (twoPrograms.run true) π k) b ≤
      infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent
        (ProgramPrior.trajectory (twoPrograms.run true) π k).length
        (ProgramPrior.trajectory (twoPrograms.run true) π k)
        (π (ProgramPrior.trajectory (twoPrograms.run true) π k)) :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.optimal_along_trajectory twoPrograms true nullAgent List.length
    (fun _ => infAttains_of_fintype _ _ _ _) _ (fun _ _ => rfl) k b

/-- `A^μ` calculates the optimal action for the true environment. -/
public theorem twoPrograms_optimalAction_max (b : Unit) :
    infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent 0 [] b ≤
      infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent 0 []
        (twoPrograms.optimalAction true nullAgent [] (infAttains_of_fintype _ _ _ _)) :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.optimalAction_max twoPrograms true nullAgent [] (infAttains_of_fintype _ _ _ _)
    ProgramPrior.Model.Consistent.nil b

/-! ## Asymptotic optimality is not trivial

A two-action model where `A^μ` is computable: the agent's horizon is zero, so
every action ties and the lexicographic rule makes `A^μ` always choose `false`.
A policy that errs once, at the empty history, is asymptotically optimal without
being mistake-free; a policy that always errs is not asymptotically optimal. -/

/-- Two programs over two actions; each echoes the action it is given. -/
@[expose] public noncomputable def echoPrograms : ProgramPrior.Model Bool Bool Bool where
  run := fun _ _ a ↦ a
  weight := fun _ ↦ 1 / 2
  nonneg := by intro q; norm_num
  summable := Summable.of_finite

/-- An agent with zero horizon over two actions. -/
@[expose] public def mutedAgent : Agent Bool Bool where
  utility := fun _ ↦ 0
  horizon := fun _ _ ↦ 0

/-- Every infinite action value of the muted agent is zero, under any belief. -/
public theorem mutedAgent_infiniteActionValue (ρ : Belief Bool Bool) (t : ℕ)
    (h : History Bool Bool) (a : Bool) : infiniteActionValue ρ mutedAgent t h a = 0 := by
  have hv : ∀ h', infiniteValue ρ mutedAgent t h' = 0 := by
    intro h'
    have hz : (fun n ↦ value ρ mutedAgent t n h') = fun _ ↦ 0 := funext fun n ↦
      value_eq_zero_of_horizon_vanishes ρ mutedAgent t 0 (fun _ _ ↦ rfl) n h' (Nat.zero_le _)
    rw [infiniteValue, hz]
    exact tendsto_const_nhds.limUnder_eq
  simp [infiniteActionValue, hv]

/-- The attainment `A^μ` needs, at every history. -/
public theorem echo_infAttains (h : History Bool Bool) :
    InfAttains (echoPrograms.point true).belief mutedAgent h.length h :=
  infAttains_of_fintype _ _ _ _

/-- `A^μ` always chooses `false`, by the tie rule. -/
public theorem echo_optimalPolicy (h : History Bool Bool) :
    echoPrograms.optimalPolicy true mutedAgent echo_infAttains h = false :=
  le_bot_iff.mp (infiniteLexBestAction_le _ _ _ _ (echo_infAttains h) (a := false)
    (fun b => by rw [mutedAgent_infiniteActionValue, mutedAgent_infiniteActionValue]))

/-- The trajectory after `k` steps has length `k`. -/
public theorem trajectory_length (π : History Bool Bool → Bool) (k : ℕ) :
    (ProgramPrior.trajectory (echoPrograms.run true) π k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [ProgramPrior.trajectory, ih]

/-- Errs at the empty history only. -/
@[expose] public def errOnce : History Bool Bool → Bool := fun h ↦ h.isEmpty

/-- `errOnce` does make a mistake: at the start. -/
public theorem errOnce_mistake :
    echoPrograms.Mistake true mutedAgent echo_infAttains errOnce
      (ProgramPrior.trajectory (echoPrograms.run true) errOnce 0) := by
  simp [ProgramPrior.Model.Mistake, echo_optimalPolicy, errOnce, ProgramPrior.trajectory]

/-- **`errOnce` is asymptotically optimal** although it is not mistake-free. -/
public theorem errOnce_asymptoticallyOptimal :
    echoPrograms.AsymptoticallyOptimal true mutedAgent echo_infAttains errOnce := by
  rw [ProgramPrior.Model.AsymptoticallyOptimal, Filter.eventually_atTop]
  refine ⟨1, fun k hk => ?_⟩
  have hne : ProgramPrior.trajectory (echoPrograms.run true) errOnce k ≠ [] := by
    intro he
    have := trajectory_length errOnce k
    rw [he] at this
    simp at this
    omega
  simp [ProgramPrior.Model.Mistake, echo_optimalPolicy, errOnce, hne]

/-- The indicator form of the same: the mistake indicator tends to zero. -/
public theorem errOnce_tendsto :
    Filter.Tendsto (fun k => open Classical in if echoPrograms.Mistake true mutedAgent
        echo_infAttains errOnce (ProgramPrior.trajectory (echoPrograms.run true) errOnce k)
      then (1 : ℝ) else 0) Filter.atTop (nhds 0) :=
  (AISafetyAtlas.Wireheading.ProgramPrior.Model.asymptoticallyOptimal_iff_tendsto echoPrograms true mutedAgent echo_infAttains errOnce).mp
    errOnce_asymptoticallyOptimal

/-- A policy that always errs is not asymptotically optimal. -/
public theorem alwaysTrue_not_asymptoticallyOptimal :
    ¬ echoPrograms.AsymptoticallyOptimal true mutedAgent echo_infAttains (fun _ ↦ true) := by
  intro hev
  obtain ⟨k, hk⟩ := hev.exists
  exact hk (by simp [ProgramPrior.Model.Mistake, echo_optimalPolicy])

/-- `A^μ` itself is asymptotically optimal. -/
public theorem echo_optimalPolicy_asymptoticallyOptimal :
    echoPrograms.AsymptoticallyOptimal true mutedAgent echo_infAttains
      (echoPrograms.optimalPolicy true mutedAgent echo_infAttains) :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.asymptoticallyOptimal_optimalPolicy echoPrograms true mutedAgent echo_infAttains

/-- Every trajectory is explained by the true program. -/
public theorem echo_trajectory_consistent (k : ℕ) :
    echoPrograms.Consistent true (ProgramPrior.trajectory (echoPrograms.run true) errOnce k) :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.trajectory_consistent echoPrograms true errOnce k

/-! ## AIXI's prior `ξ`, on a two-word code

The code `{[false], [true]}` has every word of length one, so a list of codewords
is recovered from its concatenation: the code is uniquely decodable. -/

/-- The two one-bit programs. -/
public def bitCode : Set (List Bool) := {[false], [true]}

private theorem bitCode_decode (L : List (List Bool)) (hL : ∀ w ∈ L, w ∈ bitCode) :
    L = L.flatten.map (fun b => [b]) := by
  induction L with
  | nil => rfl
  | cons w L ih =>
    have hw : w = [false] ∨ w = [true] := by simpa [bitCode] using hL w (by simp)
    have ih' := ih (fun v hv => hL v (by simp [hv]))
    rcases hw with rfl | rfl <;> simp [← ih']

/-- The one-bit code is uniquely decodable. -/
public theorem bitCode_uniquelyDecodable : InformationTheory.UniquelyDecodable bitCode := by
  intro L₁ L₂ h₁ h₂ hf
  rw [bitCode_decode L₁ h₁, bitCode_decode L₂ h₂, hf]

/-- Each one-bit program outputs its own bit. -/
@[expose] public def bitRun : {q : List Bool // q ∈ bitCode} → History Unit Bool → Unit → Bool :=
  fun q _ _ ↦ q.1.headD false

/-- `ξ` at the empty history is at most one (Kraft–McMillan), at the witness. -/
public theorem xi_mass_nil_le_one :
    (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).mass [] ≤ 1 :=
  ProgramPrior.xiModel_mass_nil_le_one bitCode bitCode_uniquelyDecodable bitRun

/-- And it is positive: the program `[true]` has weight `1/2` and explains the
empty history, so `ξ` is not the zero prior. -/
public theorem xi_mass_nil_pos :
    0 < (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).mass [] :=
  ProgramPrior.Model.mass_pos_of_consistent _ ⟨[true], by simp [bitCode]⟩ []
    ProgramPrior.Model.Consistent.nil (by simp [ProgramPrior.xiModel])

/-- **Print's `ξ(h) = Σ_{q ∈ 𝒬_h} 2^{-|q|}`**, at the witness. -/
public theorem xi_mass_formula (h : History Unit Bool) :
    (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).mass h =
      ∑' q, {q | (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).Consistent q h}.indicator
        (fun q : {q : List Bool // q ∈ bitCode} => (1 / 2 : ℝ) ^ q.1.length) q :=
  ProgramPrior.xiModel_mass bitCode bitCode_uniquelyDecodable bitRun h

/-- Kraft–McMillan on every finite set of one-bit programs. -/
public theorem bitCode_sum_le_one (s : Finset {q : List Bool // q ∈ bitCode}) :
    ∑ q ∈ s, (1 / 2 : ℝ) ^ q.1.length ≤ 1 :=
  AISafetyAtlas.Wireheading.ProgramPrior.xi_sum_le_one bitCode_uniquelyDecodable s

/-- **AIXI: the reinforcement-learning agent paired with `ξ`.** Its equation (2)
sums over observations a family that is summable, so the value denotes. -/
public theorem aixi_actionValue_summable (t n : ℕ) (h : History Unit Bool) :
    Summable (fun o ↦
      (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).belief.cond h () o *
        value (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).belief
          (DelusionBox.rlAgent (fun b : Bool ↦ if b then (1 : ℝ) else 0) 1) t n (h ++ [((), o)])) :=
  actionValue_summable
    (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).belief_isSubprobability _
    (by
      intro h
      simp only [DelusionBox.rlAgent, DelusionBox.lastReward]
      split
      · norm_num
      · split_ifs <;> norm_num) t n h ()


/-! ## Wave 3: AIXI's action, the lexicographic optimal variant, and prediction
mistakes -/

/-- **On a finite action set every linear order is well-founded**, so the
lexicographic tie rule (`lexArgmax`, `optimalAction`, `aixiAction`) needs no
hypothesis beyond the order there. -/
public theorem finite_linearOrder_wellFoundedLT {α : Type*} [Fintype α] [LinearOrder α] :
    WellFoundedLT α :=
  inferInstance

/-- AIXI's conditional is the ratio of `ξ` masses, at the witness. -/
public theorem aixi_cond_formula (h : History Unit Bool) (o : Bool) :
    (ProgramPrior.aixiBelief bitCode bitCode_uniquelyDecodable bitRun).cond h () o =
      (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).mass (h ++ [((), o)]) /
        (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).mass h :=
  ProgramPrior.aixiBelief_cond bitCode bitCode_uniquelyDecodable bitRun h () o

/-- AIXI's belief is a subprobability, at the witness. -/
public theorem aixi_isSubprobability :
    (ProgramPrior.aixiBelief bitCode bitCode_uniquelyDecodable bitRun).IsSubprobability :=
  ProgramPrior.aixiBelief_isSubprobability bitCode bitCode_uniquelyDecodable bitRun

/-- `ξ` is the product of AIXI's conditionals times `ξ(∅)`, at the witness. -/
public theorem aixi_mass_historyMass (h : History Unit Bool) :
    (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).mass h =
      (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).mass [] *
        historyMass (ProgramPrior.aixiBelief bitCode bitCode_uniquelyDecodable bitRun) h :=
  ProgramPrior.xi_mass_eq_historyMass_aixiBelief bitCode bitCode_uniquelyDecodable bitRun h

/-- **AIXI's action maximises its value under `ξ`**, at the witness (one action,
finitely many, so the attainment print presupposes holds). -/
public theorem aixi_action_max (h : History Unit Bool) (b : Unit) :
    infiniteActionValue (ProgramPrior.aixiBelief bitCode bitCode_uniquelyDecodable bitRun)
        (DelusionBox.rlAgent (fun o : Bool ↦ if o then (1 : ℝ) else 0) 1) h.length h b ≤
      infiniteActionValue (ProgramPrior.aixiBelief bitCode bitCode_uniquelyDecodable bitRun)
        (DelusionBox.rlAgent (fun o : Bool ↦ if o then (1 : ℝ) else 0) 1) h.length h
        (ProgramPrior.aixiAction bitCode bitCode_uniquelyDecodable bitRun
          (fun o : Bool ↦ if o then (1 : ℝ) else 0) 1 h (infAttains_of_fintype _ _ _ _)) :=
  ProgramPrior.aixiAction_max bitCode bitCode_uniquelyDecodable bitRun _ 1 h
    (infAttains_of_fintype _ _ _ _) b

/-- **Taking the lexicographic `A^μ`'s actions is optimal**, at print's
companion time index `t_h = |h| + 1` (Ring and Orseau, AGI 2011). -/
public theorem twoPrograms_optimal_of_same_infiniteLexBestAction (h : History Unit Bool)
    (hc : twoPrograms.Consistent true h) (b : Unit) :
    infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent
        (h.length + 1) h b ≤
      infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent
        (h.length + 1) h
        (infiniteLexBestAction (twoPrograms.point true).belief nullAgent (h.length + 1) h
          (infAttains_of_fintype _ _ _ _)) :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.optimal_of_same_infiniteLexBestAction twoPrograms
    true nullAgent (fun h => h.length + 1) (fun _ => infAttains_of_fintype _ _ _ _) _
    (fun _ _ => rfl) h hc b

/-- Taking `optimalAction`'s actions is optimal, at the time index `t = |h|`. -/
public theorem twoPrograms_optimal_of_same_optimalAction (h : History Unit Bool)
    (hc : twoPrograms.Consistent true h) (b : Unit) :
    infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent h.length h b ≤
      infiniteActionValue (DelusionBox.diracBelief (twoPrograms.run true)) nullAgent h.length h
        (twoPrograms.optimalAction true nullAgent h (infAttains_of_fintype _ _ _ _)) :=
  AISafetyAtlas.Wireheading.ProgramPrior.Model.optimal_of_same_optimalAction twoPrograms true
    nullAgent (fun _ => infAttains_of_fintype _ _ _ _) _ (fun _ _ => rfl) h hc b

/-- A prediction agent over the echo programs that always predicts `true`. -/
@[expose] public def predictTrue : History Bool Bool → Bool := fun _ ↦ true

/-- The attainment `A^μ_p` needs, at every history. -/
public theorem echo_pred_infAttains (h : History Bool Bool) :
    InfAttains (echoPrograms.point true).belief (DelusionBox.predictionAgent predictTrue 1)
      h.length h :=
  infAttains_of_fintype _ _ _ _

/-- A learning policy that takes `A^μ_p`'s action at every history, so it takes
the same actions along its run. -/
@[expose] public noncomputable def copyPolicy : History Bool Bool → Bool := fun h ↦
  echoPrograms.optimalPolicy true (DelusionBox.predictionAgent predictTrue 1)
    echo_pred_infAttains h

/-- Policies that agree along one's run generate the same run, at the witness. -/
public theorem echo_trajectory_eq (k : ℕ) :
    ProgramPrior.trajectory (echoPrograms.run true) copyPolicy k =
      ProgramPrior.trajectory (echoPrograms.run true)
        (echoPrograms.optimalPolicy true (DelusionBox.predictionAgent predictTrue 1)
          echo_pred_infAttains) k :=
  ProgramPrior.trajectory_eq_of_agree _ _ _ (fun _ => rfl) k

/-- **Same actions, same prediction mistakes**, at the witness. -/
public theorem echo_same_prediction_mistakes (k : ℕ) :
    (DelusionBox.predictionAgent predictTrue 1).utility
        (ProgramPrior.trajectory (echoPrograms.run true) copyPolicy k) =
      (DelusionBox.predictionAgent predictTrue 1).utility
        (ProgramPrior.trajectory (echoPrograms.run true)
          (echoPrograms.optimalPolicy true (DelusionBox.predictionAgent predictTrue 1)
            echo_pred_infAttains) k) :=
  ProgramPrior.Model.same_prediction_mistakes echoPrograms true predictTrue 1
    echo_pred_infAttains copyPolicy (fun _ => rfl) k

/-- The prediction utility after an observation is the hit indicator. -/
public theorem predictTrue_utility_snoc (h : History Bool Bool) (a o : Bool) :
    (DelusionBox.predictionAgent predictTrue 1).utility (h ++ [(a, o)]) =
      if predictTrue h = o then 1 else 0 :=
  DelusionBox.predictionAgent_utility_snoc predictTrue 1 h a o


/-! ### Partial programs

`oneShot` has one program, which outputs `true` after the first action and then
produces no output. The one-step history keeps the whole prior, and every
two-step extension has mass zero: the program-sum is a strict semimeasure,
which no total `Model` can produce (`Model.mass_sum_extensions` is an equality). -/

/-- One program that answers once and then stops producing output. -/
@[expose] public noncomputable def oneShot : ProgramPrior.PartialModel Unit Unit Bool where
  run := fun _ h _ ↦ if h = [] then some true else none
  weight := fun _ ↦ 1
  nonneg := by intro q; norm_num
  summable := Summable.of_finite

/-- The program explains the one-step history. -/
public theorem oneShot_consistent_one : ProgramPrior.PartialModel.Consistent oneShot () [((), true)] := by
  have := (ProgramPrior.PartialModel.consistent_snoc oneShot () [] () true).mpr ⟨.nil, by simp [oneShot]⟩
  simpa using this

/-- The one-step history keeps the whole prior. -/
public theorem oneShot_mass_one : oneShot.mass [((), true)] = 1 := by
  rw [ProgramPrior.PartialModel.mass, tsum_fintype, Finset.univ_unique, Finset.sum_singleton,
    Set.indicator_of_mem (show default ∈ {q | oneShot.Consistent q [((), true)]} from
      oneShot_consistent_one)]
  rfl

/-- No two-step history is explained: the program has stopped producing output. -/
public theorem oneShot_mass_two (o : Bool) : oneShot.mass ([((), true)] ++ [((), o)]) = 0 := by
  classical
  have hc : ¬ oneShot.Consistent () ([((), true)] ++ [((), o)]) := by
    rw [ProgramPrior.PartialModel.consistent_snoc oneShot]
    simp [oneShot]
  rw [ProgramPrior.PartialModel.mass, tsum_fintype, Finset.univ_unique, Finset.sum_singleton,
    Set.indicator_of_notMem (show default ∉ {q | oneShot.Consistent q ([((), true)] ++ [((), o)])}
      from hc)]

/-- **The partial-program mass is a strict semimeasure** at the witness:
`Σ_o ξ(h a o) < ξ(h)`, alongside the general `≤`. -/
public theorem oneShot_strict_semimeasure :
    ∑' o, oneShot.mass ([((), true)] ++ [((), o)]) < oneShot.mass [((), true)] ∧
      ∑' o, oneShot.mass ([((), true)] ++ [((), o)]) ≤ oneShot.mass [((), true)] := by
  refine ⟨?_, ProgramPrior.PartialModel.mass_sum_extensions_le oneShot _ _⟩
  simp only [oneShot_mass_two, tsum_zero, oneShot_mass_one]
  norm_num

/-- The belief after the one-step history loses all its mass, and is still a
subprobability; mass, conditioning and the history product at the witness. -/
public theorem oneShot_belief (h : History Unit Bool) (a : Unit) (o : Bool) :
    (ProgramPrior.PartialModel.belief oneShot).cond [((), true)] () o = 0 ∧ oneShot.belief.IsSubprobability ∧
      0 ≤ oneShot.mass h ∧ oneShot.mass [] = ∑' q, oneShot.weight q ∧
      oneShot.mass (h ++ [(a, o)]) ≤ oneShot.mass h ∧
      0 ≤ oneShot.belief.cond h a o ∧
      oneShot.mass h * oneShot.belief.cond h a o = oneShot.mass (h ++ [(a, o)]) ∧
      oneShot.mass h = oneShot.mass [] * historyMass oneShot.belief h ∧
      Summable (oneShot.belief.cond h a) := by
  refine ⟨?_, ProgramPrior.PartialModel.belief_isSubprobability oneShot, ProgramPrior.PartialModel.mass_nonneg oneShot h,
    ProgramPrior.PartialModel.mass_nil oneShot, ProgramPrior.PartialModel.mass_snoc_le oneShot h a o, ProgramPrior.PartialModel.belief_nonneg oneShot h a o,
    ProgramPrior.PartialModel.mass_mul_cond oneShot h a o, ProgramPrior.PartialModel.mass_eq_historyMass oneShot h,
    ProgramPrior.PartialModel.belief_summable oneShot h a⟩
  change oneShot.mass ([((), true)] ++ [((), o)]) / oneShot.mass [((), true)] = 0
  rw [oneShot_mass_two, zero_div]

/-- The total two-program model embeds with the same mass and belief. -/
public theorem twoPrograms_toPartial (h : History Unit Bool) (q : Bool) :
    ((ProgramPrior.Model.toPartial twoPrograms).Consistent q h ↔ twoPrograms.Consistent q h) ∧
      twoPrograms.toPartial.mass h = twoPrograms.mass h ∧
      twoPrograms.toPartial.belief.cond = twoPrograms.belief.cond :=
  ⟨ProgramPrior.Model.toPartial_consistent twoPrograms q h,
    ProgramPrior.Model.toPartial_mass twoPrograms h,
    ProgramPrior.Model.toPartial_belief_cond twoPrograms⟩

/-- One-bit programs that answer their own bit once and then stop. -/
@[expose] public def bitPartialRun :
    {q : List Bool // q ∈ bitCode} → History Unit Bool → Unit → Option Bool :=
  fun q h _ ↦ if h = [] then some (q.1.headD false) else none

/-- **Print's `ξ` over partial programs**, with AIXI's belief, at the witness. -/
public theorem partialXi_facts (h : History Unit Bool) (a : Unit) (o : Bool) :
    (ProgramPrior.partialXiModel bitCode bitCode_uniquelyDecodable bitPartialRun).mass h =
        ∑' q, {q | (ProgramPrior.partialXiModel bitCode bitCode_uniquelyDecodable
          bitPartialRun).Consistent q h}.indicator
          (fun q : {q : List Bool // q ∈ bitCode} => (1 / 2 : ℝ) ^ q.1.length) q ∧
      (ProgramPrior.partialAixiBelief bitCode bitCode_uniquelyDecodable bitPartialRun).cond h a o =
        (ProgramPrior.partialXiModel bitCode bitCode_uniquelyDecodable bitPartialRun).mass
            (h ++ [(a, o)]) /
          (ProgramPrior.partialXiModel bitCode bitCode_uniquelyDecodable bitPartialRun).mass h ∧
      (ProgramPrior.partialAixiBelief bitCode bitCode_uniquelyDecodable
        bitPartialRun).IsSubprobability ∧
      (ProgramPrior.partialXiModel bitCode bitCode_uniquelyDecodable bitPartialRun).mass h =
        (ProgramPrior.partialXiModel bitCode bitCode_uniquelyDecodable bitPartialRun).mass [] *
          historyMass (ProgramPrior.partialAixiBelief bitCode bitCode_uniquelyDecodable
            bitPartialRun) h :=
  ⟨ProgramPrior.partialXiModel_mass _ _ _ h, ProgramPrior.partialAixiBelief_cond _ _ _ h a o,
    ProgramPrior.partialAixiBelief_isSubprobability _ _ _,
    ProgramPrior.partialXi_mass_eq_historyMass _ _ _ h⟩

/-- The total `ξ` is the partial one with always-answering programs, at the witness. -/
public theorem xiModel_toPartial_bit :
    (ProgramPrior.xiModel bitCode bitCode_uniquelyDecodable bitRun).toPartial =
      ProgramPrior.partialXiModel bitCode bitCode_uniquelyDecodable
        (fun q h a => some (bitRun q h a)) :=
  ProgramPrior.xiModel_toPartial _ _ _

/-! Total-model lemmas named in full: their leaf names are shared with `PartialModel`. -/
example (h : History Unit Bool) : 0 ≤ twoPrograms.mass h := AISafetyAtlas.Wireheading.ProgramPrior.Model.mass_nonneg twoPrograms h
example (h : History Unit Bool) (o : Bool) :
    twoPrograms.mass (h ++ [((), o)]) ≤ twoPrograms.mass h := AISafetyAtlas.Wireheading.ProgramPrior.Model.mass_snoc_le twoPrograms h () o
example (h : History Unit Bool) (o : Bool) := AISafetyAtlas.Wireheading.ProgramPrior.Model.belief_nonneg twoPrograms h () o
example (h : History Unit Bool) := AISafetyAtlas.Wireheading.ProgramPrior.Model.belief_summable twoPrograms h ()
example := AISafetyAtlas.Wireheading.ProgramPrior.Model.belief_isSubprobability twoPrograms
/-! ## Footnote 6 along the environment's own histories

The prediction agent predicting `true` whatever the history and the action. `allTrueEnv` answers `true` everywhere;
`trueWhileTrue` answers `true` while every observation so far is `true` and
`false` after any `false`, a history neither environment ever generates. Both make
no mistake along their runs, they differ as response functions, and they generate
the same history under every policy. The every-history reading of footnote 6
(`DelusionBox.predictionAgent_existsUnique_zero_mistakes`) excludes
`trueWhileTrue`; the run reading admits it and identifies it with `allTrueEnv` as
a program on actions.
-/

/-- Always answers `true`. -/
@[expose] public def allTrueEnv : History Bool Bool → Bool → Bool := fun _ _ => true

/-- Answers `true` while every observation so far is `true`, `false` otherwise. -/
@[expose] public def trueWhileTrue : History Bool Bool → Bool → Bool :=
  fun h _ => h.all (fun p => p.2)

/-- Every history `trueWhileTrue` generates has only `true` observations. -/
public theorem trueWhileTrue_trajectory_all (π : History Bool Bool → Bool) (k : ℕ) :
    (ProgramPrior.trajectory trueWhileTrue π k).all (fun p => p.2) = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [ProgramPrior.trajectory, List.all_append, ih, Bool.true_and]
    simp [trueWhileTrue, ih]

/-- `allTrueEnv` makes no mistake along its runs. -/
public theorem allTrueEnv_zeroMistakesOnRuns :
    AISafetyAtlas.Wireheading.ProgramPrior.ZeroMistakesOnRuns (fun (_ : History Bool Bool) (_ : Bool) => true) 1 allTrueEnv :=
  AISafetyAtlas.Wireheading.ProgramPrior.zeroMistakesOnRuns_predict (fun _ _ => true) 1

/-- `trueWhileTrue` makes no mistake along its runs. -/
public theorem trueWhileTrue_zeroMistakesOnRuns :
    ProgramPrior.ZeroMistakesOnRuns (fun (_ : History Bool Bool) (_ : Bool) => true) 1 trueWhileTrue :=
  (AISafetyAtlas.Wireheading.ProgramPrior.zeroMistakesOnRuns_iff _ 1 _).mpr
    fun π k => trueWhileTrue_trajectory_all π k

/-- The two environments differ as response functions, after a `false`. -/
public theorem trueWhileTrue_ne_allTrueEnv : trueWhileTrue ≠ allTrueEnv := by
  intro h
  have := congrFun (congrFun h [(true, false)]) true
  simp [trueWhileTrue, allTrueEnv] at this

/-- So `trueWhileTrue` errs at some history it never generates: the every-history
condition of `DelusionBox.predictionAgent_existsUnique_zero_mistakes` fails. -/
public theorem trueWhileTrue_not_zero_mistakes_everywhere :
    ¬ ∀ h a, (DelusionBox.predictionAgent (fun _ : History Bool Bool => true) 1).utility
      (h ++ [(a, trueWhileTrue h a)]) = 1 := by
  intro hall
  exact trueWhileTrue_ne_allTrueEnv
    ((AISafetyAtlas.Wireheading.DelusionBox.predictionAgent_utility_eq_one_iff _ 1 _).mp hall)

/-- **Footnote 6 along runs, applied**: the two zero-mistake environments generate
the same history under every policy. -/
public theorem trueWhileTrue_trajectory_eq (π : History Bool Bool → Bool) (k : ℕ) :
    ProgramPrior.trajectory trueWhileTrue π k = ProgramPrior.trajectory allTrueEnv π k :=
  AISafetyAtlas.Wireheading.ProgramPrior.trajectory_eq_of_zeroMistakesOnRuns
    trueWhileTrue_zeroMistakesOnRuns allTrueEnv_zeroMistakesOnRuns π k

/-- And they answer every action alike at every history `trueWhileTrue` generates. -/
public theorem trueWhileTrue_apply_eq (π : History Bool Bool → Bool) (k : ℕ) (a : Bool) :
    trueWhileTrue (ProgramPrior.trajectory trueWhileTrue π k) a =
      allTrueEnv (ProgramPrior.trajectory trueWhileTrue π k) a :=
  AISafetyAtlas.Wireheading.ProgramPrior.apply_eq_of_zeroMistakesOnRuns
    trueWhileTrue_zeroMistakesOnRuns allTrueEnv_zeroMistakesOnRuns π k a

/-- Each answers every action with the prediction at the histories it generates. -/
public theorem trueWhileTrue_apply_eq_predict (π : History Bool Bool → Bool) (k : ℕ) (a : Bool) :
    trueWhileTrue (ProgramPrior.trajectory trueWhileTrue π k) a = true :=
  AISafetyAtlas.Wireheading.ProgramPrior.apply_eq_predict_of_zeroMistakesOnRuns
    trueWhileTrue_zeroMistakesOnRuns π k a

/-- **Footnote 6 along runs**, existence and uniqueness of the generated histories,
at the prediction agent predicting `true`. -/
public theorem true_existsUnique_zero_mistakes_on_runs :
    (∃ E : History Bool Bool → Bool → Bool,
        ProgramPrior.ZeroMistakesOnRuns (fun (_ : History Bool Bool) (_ : Bool) => true) 1 E) ∧
      ∀ E E' : History Bool Bool → Bool → Bool,
        ProgramPrior.ZeroMistakesOnRuns (fun (_ : History Bool Bool) (_ : Bool) => true) 1 E →
        ProgramPrior.ZeroMistakesOnRuns (fun (_ : History Bool Bool) (_ : Bool) => true) 1 E' →
          ∀ (π : History Bool Bool → Bool) (k : ℕ),
            ProgramPrior.trajectory E π k = ProgramPrior.trajectory E' π k :=
  AISafetyAtlas.Wireheading.ProgramPrior.predictionAgentAct_existsUnique_zero_mistakes_on_runs
    (fun _ _ => true) 1

/-- The same at the action-blind predictor of `DelusionBox.predictionAgent`. -/
public theorem true_existsUnique_zero_mistakes_on_runs_blind :
    (∃ E : History Bool Bool → Bool → Bool,
        ProgramPrior.ZeroMistakesOnRuns (fun (h : History Bool Bool) (_ : Bool) =>
          (fun _ : History Bool Bool => true) h) 1 E) ∧
      ∀ E E' : History Bool Bool → Bool → Bool,
        ProgramPrior.ZeroMistakesOnRuns (fun (h : History Bool Bool) (_ : Bool) =>
          (fun _ : History Bool Bool => true) h) 1 E →
        ProgramPrior.ZeroMistakesOnRuns (fun (h : History Bool Bool) (_ : Bool) =>
          (fun _ : History Bool Bool => true) h) 1 E' →
          ∀ (π : History Bool Bool → Bool) (k : ℕ),
            ProgramPrior.trajectory E π k = ProgramPrior.trajectory E' π k :=
  AISafetyAtlas.Wireheading.ProgramPrior.predictionAgent_existsUnique_zero_mistakes_on_runs
    (fun _ => true) 1

example (q : Bool) := AISafetyAtlas.Wireheading.ProgramPrior.Model.consistent_snoc twoPrograms q [] () true
example (h : History Unit Bool) := AISafetyAtlas.Wireheading.ProgramPrior.Model.mass_eq_historyMass twoPrograms h
example (h : History Unit Bool) (o : Bool) := AISafetyAtlas.Wireheading.ProgramPrior.Model.mass_mul_cond twoPrograms h () o

end AISafetyAtlas.Examples.Wireheading.ProgramPrior
