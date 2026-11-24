module

public import AISafetyAtlas.Wireheading.DelusionBox
public import AISafetyAtlas.Wireheading.ValueBounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.InformationTheory.Coding.KraftMcMillan

/-!
# Program mass and the observation belief it induces

Orseau and Ring, *Self-Modification and Mortality in Artificial Agents*,
author version, pp.2–4: a history has the summed prior weight of its consistent
programs. The program interpreter is a parameter, so a concrete programming
language can instantiate it without a finite code or observation alphabet.

The prior need not have total mass one. The observation product recovers its
**normalized** history mass; the knowledge agent below uses the unnormalized
mass printed in the source. Zero-mass histories have zero conditional weights.

## Non-claims

No universal machine, Solomonoff prior, computability or asymptotic optimality
is proved here. No delusion or self-modification Statement follows from merely
having a program prior. `Model`'s interpreter is total on the histories
presented to it; programs that stop producing output are covered by
`PartialModel` at the end of this module, whose mass is a semimeasure.
-/

namespace AISafetyAtlas.Wireheading.ProgramPrior

open AgentEquations

/-- A program interpretation and a summable nonnegative prior. Strict positivity
on the source's program class can be supplied by an instantiation; zero weights
also admit the source's optimal non-learning point mass. -/
public structure Model (Code Action Obs : Type*) where
  /-- Interpret a program after the recorded interactions and the next action. -/
  run : Code → History Action Obs → Action → Obs
  /-- Prior weight of the program, before seeing observations. -/
  weight : Code → ℝ
  /-- Prior weights are nonnegative. -/
  nonneg : ∀ q, 0 ≤ weight q
  /-- The source requires finite total consistent mass, including at the empty history. -/
  summable : Summable weight

namespace Model

variable {Code Action Obs : Type*} (M : Model Code Action Obs)

/-- A program is consistent when it produces every recorded observation. -/
public inductive Consistent (q : Code) : History Action Obs → Prop
  | nil : Consistent q []
  | snoc {h : History Action Obs} {a : Action} {o : Obs} :
      Consistent q h → M.run q h a = o → Consistent q (h ++ [(a, o)])

/-- Consistency at an extended history is exactly old consistency and a matching output. -/
public theorem consistent_snoc (q : Code) (h : History Action Obs) (a : Action) (o : Obs) :
    M.Consistent q (h ++ [(a, o)]) ↔ M.Consistent q h ∧ M.run q h a = o := by
  constructor
  · intro hc
    generalize he : h ++ [(a, o)] = hs at hc
    cases hc with
    | nil => simp at he
    | @snoc h' a' o' old output =>
      have hl : h.length = h'.length := by simpa using congrArg List.length he
      obtain ⟨hh, hp⟩ := List.append_inj he hl
      have ha : a = a' := by simpa using congrArg (fun l ↦ l.head?.map Prod.fst) hp
      have ho : o = o' := by simpa using congrArg (fun l ↦ l.head?.map Prod.snd) hp
      subst h' a' o'
      exact ⟨old, output⟩
  · rintro ⟨hc, ho⟩
    exact .snoc hc ho

/-- The source's sum over consistent programs, with inconsistent weights set to zero. -/
@[expose] public noncomputable def mass (h : History Action Obs) : ℝ :=
  ∑' q, {q | M.Consistent q h}.indicator M.weight q

private theorem mass_summable (h : History Action Obs) :
    Summable ({q | M.Consistent q h}.indicator M.weight) :=
  M.summable.indicator _

/-- Every consistent-history mass is nonnegative. -/
public theorem mass_nonneg (h : History Action Obs) : 0 ≤ M.mass h := by
  apply tsum_nonneg
  intro q
  classical
  simp only [Set.indicator_apply]
  split_ifs <;> simp [M.nonneg]

/-- The empty-history mass is the total prior weight, not implicitly one. -/
public theorem mass_nil : M.mass [] = ∑' q, M.weight q := by
  simp [mass, Consistent.nil]

/-- Observing another output can only discard programs and decrease prior mass. -/
public theorem mass_snoc_le (h : History Action Obs) (a : Action) (o : Obs) :
    M.mass (h ++ [(a, o)]) ≤ M.mass h := by
  classical
  apply Summable.tsum_le_tsum _ (M.mass_summable _) (M.mass_summable _)
  intro q
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, consistent_snoc]
  split_ifs <;> simp_all [M.nonneg]

/-- The conditional observation weights induced by the program prior. Division
at a zero-mass history is zero and is not asserted to be a probability there. -/
@[expose] public noncomputable def belief : Belief Action Obs where
  cond := fun h a o ↦ M.mass (h ++ [(a, o)]) / M.mass h

/-- The induced conditionals are nonnegative, including at impossible histories. -/
public theorem belief_nonneg (h : History Action Obs) (a : Action) (o : Obs) :
    0 ≤ M.belief.cond h a o := div_nonneg (M.mass_nonneg _) (M.mass_nonneg _)

/-- The defining conditioning identity also holds at impossible histories:
all of their extensions have zero mass. -/
public theorem mass_mul_cond (h : History Action Obs) (a : Action) (o : Obs) :
    M.mass h * M.belief.cond h a o = M.mass (h ++ [(a, o)]) := by
  by_cases hz : M.mass h = 0
  · have he : M.mass (h ++ [(a, o)]) = 0 :=
      le_antisymm (by simpa [hz] using M.mass_snoc_le h a o) (M.mass_nonneg _)
    simp [hz, he, belief]
  · exact mul_div_cancel₀ _ hz

private theorem mass_mul_go (tail pre : History Action Obs) :
    M.mass pre * historyMass.go M.belief tail pre = M.mass (pre ++ tail) := by
  induction tail generalizing pre with
  | nil => simp [historyMass.go]
  | cons p rest ih =>
    rw [historyMass.go, ← mul_assoc, M.mass_mul_cond, ih]
    simp

/-- The observation product is the normalized program mass. This multiplicative
form remains valid even when the entire prior has zero mass. -/
public theorem mass_eq_historyMass (h : History Action Obs) :
    M.mass h = M.mass [] * historyMass M.belief h := by
  simpa [historyMass] using (M.mass_mul_go h []).symm

/-- Recover the existing observation-level convention when the prior has mass one. -/
public theorem historyMass_eq_mass (hunit : M.mass [] = 1) (h : History Action Obs) :
    historyMass M.belief h = M.mass h := by
  simpa [hunit] using (M.mass_eq_historyMass h).symm

private theorem extension_sum (h : History Action Obs) (a : Action) (q : Code) :
    (∑' o, {q | M.Consistent q (h ++ [(a, o)])}.indicator M.weight q) =
      {q | M.Consistent q h}.indicator M.weight q := by
  classical
  rw [tsum_eq_single (M.run q h a)]
  · simp [Set.indicator_apply, consistent_snoc]
  · intro o ho
    simp [consistent_snoc, Ne.symm ho]

private theorem extensions_summable (h : History Action Obs) (a : Action) :
    Summable (fun p : Code × Obs ↦
      {q | M.Consistent q (h ++ [(a, p.2)])}.indicator M.weight p.1) := by
  classical
  apply (summable_prod_of_nonneg (by
    intro p
    simp only [Set.indicator_apply]
    split_ifs <;> simp [M.nonneg])).mpr
  constructor
  · intro q
    apply summable_of_ne_finset_zero (s := {M.run q h a})
    intro o ho
    simp only [Finset.mem_singleton] at ho
    simp [consistent_snoc, Ne.symm ho]
  · simpa only [extension_sum] using M.mass_summable h

/-- Programs consistent with a history partition by their next output. -/
public theorem mass_sum_extensions (h : History Action Obs) (a : Action) :
    ∑' o, M.mass (h ++ [(a, o)]) = M.mass h := by
  have hs := M.extensions_summable h a
  change Summable (Function.uncurry (fun q o ↦
    {q | M.Consistent q (h ++ [(a, o)])}.indicator M.weight q)) at hs
  exact hs.tsum_comm.trans (tsum_congr (M.extension_sum h a))

/-- The induced observation weights sum to one at precisely the histories where
conditioning is justified by positive mass. No finite observation type is used. -/
public theorem belief_sum (h : History Action Obs) (a : Action) (hh : M.mass h ≠ 0) :
    ∑' o, M.belief.cond h a o = 1 := by
  simp only [belief, tsum_div_const, mass_sum_extensions, div_self hh]

/-- The observation family is summable, independently of whether the history is possible. -/
public theorem belief_summable (h : History Action Obs) (a : Action) :
    Summable (M.belief.cond h a) := by
  have hs := (M.extensions_summable h a).prod_symm.prod
  change Summable (fun o ↦ M.mass (h ++ [(a, o)])) at hs
  exact hs.div_const (M.mass h)

/-- The program-induced belief satisfies the probability obligations of the value bounds. -/
public theorem belief_isSubprobability : M.belief.IsSubprobability where
  nonneg := M.belief_nonneg
  summable := M.belief_summable
  total_le_one := by
    intro h a
    by_cases hh : M.mass h = 0
    · simp [belief, hh]
    · exact (M.belief_sum h a hh).le

/-- A consistent program with positive prior mass makes the history possible. -/
public theorem mass_pos_of_consistent (q : Code) (h : History Action Obs)
    (hc : M.Consistent q h) (hq : 0 < M.weight q) : 0 < M.mass h := by
  classical
  refine (M.mass_summable h).tsum_pos ?_ q ?_
  · intro q
    simp only [Set.indicator_apply]
    split_ifs <;> simp [M.nonneg]
  · simpa [hc] using hq

/-- The knowledge agent uses this prior's own mass, not an unrelated parameter. -/
@[expose] public noncomputable def knowledgeAgent (m : ℕ) : Agent Action Obs :=
  DelusionBox.knowledgeAgent M.mass m

/-- The mortality source's literal horizon with the same program-derived utility. -/
@[expose] public noncomputable def companionKnowledgeAgent (m : ℕ) : Agent Action Obs :=
  DelusionBox.companionKnowledgeAgent M.mass m

/-- A point prior on a designated true program. The interpreter is shared with
the learning model; replacing its weights leaves utility and horizon untouched. -/
@[expose] public noncomputable def point (q₀ : Code) : Model Code Action Obs := by
  classical
  exact {
    run := M.run
    weight := fun q ↦ if q = q₀ then 1 else 0
    nonneg := by intro q; split_ifs <;> norm_num
    summable := summable_of_ne_finset_zero (s := {q₀}) (by simp) }

/-- Changing prior weights does not change which histories a program explains. -/
public theorem point_consistent (q₀ q : Code) (h : History Action Obs) :
    (M.point q₀).Consistent q h ↔ M.Consistent q h := by
  constructor
  · intro hc
    induction hc with
    | nil => exact .nil
    | snoc hc ho ih => exact .snoc ih ho
  · intro hc
    induction hc with
    | nil => exact .nil
    | snoc hc ho ih => exact .snoc ih ho

open Classical in
/-- The true-program prior assigns one exactly to histories that program explains. -/
public theorem point_mass (q₀ : Code) (h : History Action Obs) :
    (M.point q₀).mass h = if M.Consistent q₀ h then 1 else 0 := by
  classical
  rw [mass, tsum_eq_single q₀]
  · simp only [Set.indicator_apply, Set.mem_ofPred_eq, point_consistent]
    simp [point]
  · intro q hq
    simp [point, hq, Set.indicator_apply]

/-- On a true-program history the induced point prior is exactly the atlas's
observation-level optimal-variant belief. Off that history it is undefined as a
probability and is represented by zero, so no off-support equality is claimed. -/
public theorem point_belief_eq [DecidableEq Obs] (q₀ : Code) (h : History Action Obs)
    (hc : M.Consistent q₀ h) (a : Action) (o : Obs) :
    (M.point q₀).belief.cond h a o = (DelusionBox.diracBelief (M.run q₀)).cond h a o := by
  classical
  simp [belief, point_mass, hc, consistent_snoc, DelusionBox.diracBelief, eq_comm]

/-- The finite value at a point prior recovers the existing non-learning value
at every history consistent with the designated true program. Utility is kept
fixed while only the belief changes, as required by the mortality source. -/
public theorem value_point_eq [DecidableEq Obs] (q₀ : Code) (ag : Agent Action Obs)
    (t n : ℕ) (h : History Action Obs) (hc : M.Consistent q₀ h) :
    value (M.point q₀).belief ag t n h = value (DelusionBox.diracBelief (M.run q₀)) ag t n h := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    simp only [value]
    congr 1
    apply congrArg iSup
    funext a
    apply tsum_congr
    intro o
    rw [M.point_belief_eq q₀ h hc]
    by_cases ho : M.run q₀ h a = o
    · rw [ih _ (.snoc hc ho)]
    · simp [DelusionBox.diracBelief, Ne.symm ho]

/-- Equation (2) at the point prior is equation (2) at the non-learning
variant's belief, on every history the true program explains (Ring and Orseau,
AGI 2011, §2, optimal variants: *"replacing `ρ` by `μ` in (only) equation (2)"*). -/
public theorem actionValue_point_eq [DecidableEq Obs] (q₀ : Code) (ag : Agent Action Obs)
    (t n : ℕ) (h : History Action Obs) (hc : M.Consistent q₀ h) (a : Action) :
    actionValue (M.point q₀).belief ag t n h a =
      actionValue (DelusionBox.diracBelief (M.run q₀)) ag t n h a := by
  apply tsum_congr
  intro o
  rw [M.point_belief_eq q₀ h hc]
  by_cases ho : M.run q₀ h a = o
  · rw [M.value_point_eq q₀ ag t n _ (.snoc hc ho)]
  · simp [DelusionBox.diracBelief, Ne.symm ho]

/-- **The infinite-horizon value at the point prior is the non-learning
variant's**, on every history the true program explains. Print's `A^μ` (Ring
and Orseau, AGI 2011, §2; Orseau and Ring, AGI 2011, §2.1) uses the recursion
(2)–(3), which has no terminal condition; this is `value_point_eq` carried to
`infiniteValue`, the limit of the depth-`n` values. The equality needs no
summability hypothesis: both sides are `limUnder` of sequences that agree at
every depth. Where the limit exists (`tendsto_value_infiniteValue`, at
`Belief.IsSubprobability`, `|u| ≤ 1` and a summable horizon) it is print's
value, and `infiniteValue_eq` gives print's recursion at `μ`. -/
public theorem infiniteValue_point_eq [DecidableEq Obs] (q₀ : Code) (ag : Agent Action Obs)
    (t : ℕ) (h : History Action Obs) (hc : M.Consistent q₀ h) :
    infiniteValue (M.point q₀).belief ag t h =
      infiniteValue (DelusionBox.diracBelief (M.run q₀)) ag t h := by
  unfold infiniteValue
  congr 1
  funext n
  exact M.value_point_eq q₀ ag t n h hc

/-- Equation (2) at the infinite-horizon value: the point prior and the
non-learning variant's belief give the same action values on every history the
true program explains. -/
public theorem infiniteActionValue_point_eq [DecidableEq Obs] (q₀ : Code)
    (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs) (hc : M.Consistent q₀ h)
    (a : Action) :
    infiniteActionValue (M.point q₀).belief ag t h a =
      infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag t h a := by
  apply tsum_congr
  intro o
  rw [M.point_belief_eq q₀ h hc]
  by_cases ho : M.run q₀ h a = o
  · rw [M.infiniteValue_point_eq q₀ ag t _ (.snoc hc ho)]
  · simp [DelusionBox.diracBelief, Ne.symm ho]

/-! ### Statement 3's prior inequality

Print's Statement 3 opens: *"Let `𝒬_B` be the set of environments containing a
delusion box, and let `q_b ∈ 𝒬_B` be the true environment. Because
`ρ(q_b) < ρ(𝒬_B)`, it takes fewer errors to converge to `𝒬_B` than to `q_b`."*

The **inequality** is this paper's and is proved here. The **error count** is
not: the sentence before Statement 3 sources it — *"for an environment `q ∈ 𝒬`,
a predictor makes approximately `−log(ρ(q))` errors [2]"* — so the convergence
rate is a cited theorem of another paper, and formalizing it is that paper's
grading and not this one's.
-/

/--
**The prior mass of a set of programs**, print's `ρ(𝒬)` written at a set rather
than at a history. `mass` is this at the set of programs consistent with a
history, which `mass_eq_setMass` records.
-/
@[expose] public noncomputable def setMass (S : Set Code) : ℝ :=
  ∑' q, S.indicator M.weight q

/-- The history mass is the set mass at the consistent programs. -/
public theorem mass_eq_setMass (h : History Action Obs) :
    M.mass h = M.setMass {q | M.Consistent q h} :=
  rfl

/-- Set masses are nonnegative. -/
public theorem setMass_nonneg (S : Set Code) : 0 ≤ M.setMass S := by
  classical
  refine tsum_nonneg fun q => ?_
  simp only [Set.indicator_apply]
  split_ifs <;> simp [M.nonneg]

/--
**Print's `ρ(q_b) < ρ(𝒬_B)`, at the inequality that always holds.**

One program's prior weight never exceeds the mass of a set containing it. Print
writes the strict form; `weight_lt_setMass` is that, and it needs a second
member of the set carrying positive weight — which print's `𝒬_B`, a whole class
of environments containing a delusion box, has and a singleton would not.
-/
public theorem weight_le_setMass {S : Set Code} {q : Code} (hq : q ∈ S) :
    M.weight q ≤ M.setMass S := by
  classical
  have hs : Summable (S.indicator M.weight) := M.summable.indicator S
  have hle := hs.le_tsum q (fun b _ => by
    simp only [Set.indicator_apply]
    split_ifs <;> simp [M.nonneg])
  rwa [Set.indicator_of_mem hq] at hle

/--
**Print's strict `ρ(q_b) < ρ(𝒬_B)`.** The true environment is one member of the
class; any other member of positive weight makes the inequality strict.
-/
public theorem weight_lt_setMass {S : Set Code} {q q' : Code} (hq : q ∈ S)
    (hq' : q' ∈ S) (hne : q' ≠ q) (hpos : 0 < M.weight q') :
    M.weight q < M.setMass S := by
  classical
  have hs : Summable (S.indicator M.weight) := M.summable.indicator S
  have hfin : ∑ i ∈ ({q, q'} : Finset Code), S.indicator M.weight i ≤ M.setMass S := by
    refine Summable.sum_le_tsum _ (fun i _ => ?_) hs
    simp only [Set.indicator_apply]
    split_ifs <;> simp [M.nonneg]
  rw [Finset.sum_pair (Ne.symm hne), Set.indicator_of_mem hq,
    Set.indicator_of_mem hq'] at hfin
  linarith

/-- A surviving positive-weight program's relative probability increases when
observations discard other programs. This is the monotonicity described on p.4;
it does not assert convergence or identify a universal prior. -/
public theorem relative_weight_le (q : Code) (h : History Action Obs) (a : Action) (o : Obs)
    (hc : M.Consistent q (h ++ [(a, o)])) (hq : 0 < M.weight q) :
    M.weight q / M.mass h ≤ M.weight q / M.mass (h ++ [(a, o)]) := by
  exact div_le_div_of_nonneg_left hq.le (M.mass_pos_of_consistent q _ hc hq)
    (M.mass_snoc_le h a o)

/-- Summing a bounded continuation over observations is the same as summing it
against the posterior over consistent programs. The continuation is held fixed:
it is not reoptimized separately inside each program hypothesis. -/
public theorem expectation_eq_programSum (h : History Action Obs) (a : Action)
    (f : Obs → ℝ) {b : ℝ} (hf : ∀ o, |f o| ≤ b) :
    (∑' o, M.belief.cond h a o * f o) =
      (∑' q, {q | M.Consistent q h}.indicator M.weight q * f (M.run q h a)) /
        M.mass h := by
  classical
  let g : Code → Obs → ℝ := fun q o ↦
    {q | M.Consistent q (h ++ [(a, o)])}.indicator M.weight q * f o
  have hg : Summable (Function.uncurry g) := by
    apply ((M.extensions_summable h a).mul_right b).of_norm_bounded
    intro p
    dsimp [g, Function.uncurry]
    rw [abs_mul]
    have hn : 0 ≤ {q | M.Consistent q (h ++ [(a, p.2)])}.indicator M.weight p.1 := by
      simp only [Set.indicator_apply]
      split_ifs <;> simp [M.nonneg]
    rw [abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left (hf p.2) hn
  have hone (q : Code) : (∑' o, g q o) =
      {q | M.Consistent q h}.indicator M.weight q * f (M.run q h a) := by
    rw [tsum_eq_single (M.run q h a)]
    · simp [g, consistent_snoc, Set.indicator_apply]
    · intro o ho
      simp [g, consistent_snoc, Ne.symm ho]
  calc
    _ = (∑' o, M.mass (h ++ [(a, o)]) * f o) / M.mass h := by
      simp only [belief, div_mul_eq_mul_div, tsum_div_const]
    _ = (∑' o, ∑' q, g q o) / M.mass h := by
      congr 1
      apply tsum_congr
      intro o
      simp only [g, mass, tsum_mul_right]
    _ = (∑' q, ∑' o, g q o) / M.mass h := by rw [hg.tsum_comm]
    _ = _ := by simp only [hone]

/-- The program-posterior formula at every finite planning depth. This removes
the need for an assumed linear decomposition of separately optimized values. -/
public theorem actionValue_eq_programSum [Nonempty Action]
    (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) (a : Action) :
    actionValue M.belief ag t n h a =
      (∑' q, {q | M.Consistent q h}.indicator M.weight q *
        value M.belief ag t n (h ++ [(a, M.run q h a)])) / M.mass h := by
  apply M.expectation_eq_programSum h a
    (fun o ↦ value M.belief ag t n (h ++ [(a, o)]))
    (b := horizonBudget ag t n (h.length + 1))
  intro o
  simpa using abs_value_le_horizonBudget M.belief_isSubprobability ag hu t n
    (h ++ [(a, o)])

end Model

/-! ### Trajectories, the optimal agent `A^μ`, and asymptotic optimality

Ring and Orseau, AGI 2011, §2, optimal variants: *"if the learning agent takes
the same actions as the non-learning one, then its behavior is also optimal with
respect to its utility and horizon functions."* Orseau and Ring, AGI 2011, §2.1:
*"`A^μ` is defined by (1-3), where the universal `ρ` is replaced by the specific
`μ`"*, and *"An agent is said to be asymptotically optimal if its performance
tends towards that of `A^μ` … The agent is asymptotically optimal if the number
of mistakes it makes tends towards zero."*
-/

/-- The history generated by a policy `π` against a deterministic environment
`E`, after `k` steps. -/
@[expose] public def trajectory {Action Obs : Type*} (E : History Action Obs → Action → Obs)
    (π : History Action Obs → Action) : ℕ → History Action Obs
  | 0 => []
  | k + 1 => trajectory E π k ++ [(π (trajectory E π k), E (trajectory E π k) (π (trajectory E π k)))]

namespace Model

variable {Code Action Obs : Type*} (M : Model Code Action Obs)

/-- Every history a policy generates against the true program is explained by
that program, so the point-prior lemmas apply along it. -/
public theorem trajectory_consistent (q₀ : Code) (π : History Action Obs → Action) (k : ℕ) :
    M.Consistent q₀ (trajectory (M.run q₀) π k) := by
  induction k with
  | zero => exact .nil
  | succ k ih => exact .snoc ih rfl

/--
**A learning agent that takes the non-learning agent's actions is optimal,** at
depth `n` (Ring and Orseau, AGI 2011, §2, optimal variants). `τ h` is the time
index at history `h` (print's `t_h = |h| + 1`; any choice is allowed). If at
every history the true program explains, the policy `π` takes the action `A^μ`
takes — `bestAction` at the point prior `μ` — then that action maximises the
action value in the true environment `diracBelief (M.run q₀)`. The infinite-
horizon form is `optimal_of_same_infiniteBestAction`.
-/
public theorem optimal_of_same_bestAction [DecidableEq Obs] (q₀ : Code)
    (ag : Agent Action Obs) (τ : History Action Obs → ℕ) (n : ℕ)
    (hat : ∀ h, Attains (M.point q₀).belief ag (τ h) n h) (π : History Action Obs → Action)
    (hsame : ∀ h, M.Consistent q₀ h →
      π h = bestAction (M.point q₀).belief ag (τ h) n h (hat h))
    (h : History Action Obs) (hc : M.Consistent q₀ h) (b : Action) :
    actionValue (DelusionBox.diracBelief (M.run q₀)) ag (τ h) n h b ≤
      actionValue (DelusionBox.diracBelief (M.run q₀)) ag (τ h) n h (π h) := by
  rw [← M.actionValue_point_eq q₀ ag _ n h hc, ← M.actionValue_point_eq q₀ ag _ n h hc,
    hsame h hc]
  exact bestAction_max _ ag _ n h (hat h) b

/-- **The same at the infinite-horizon value**, print's recursion without
truncation: taking `A^μ`'s actions (`infiniteBestAction` at the point prior) is
optimal for the true environment on every history the true program explains. -/
public theorem optimal_of_same_infiniteBestAction [DecidableEq Obs] (q₀ : Code)
    (ag : Agent Action Obs) (τ : History Action Obs → ℕ)
    (hat : ∀ h, InfAttains (M.point q₀).belief ag (τ h) h) (π : History Action Obs → Action)
    (hsame : ∀ h, M.Consistent q₀ h →
      π h = infiniteBestAction (M.point q₀).belief ag (τ h) h (hat h))
    (h : History Action Obs) (hc : M.Consistent q₀ h) (b : Action) :
    infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag (τ h) h b ≤
      infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag (τ h) h (π h) := by
  rw [← M.infiniteActionValue_point_eq q₀ ag _ h hc,
    ← M.infiniteActionValue_point_eq q₀ ag _ h hc, hsame h hc]
  exact infiniteBestAction_max _ ag _ h (hat h) b

/-- **The same with print's lexicographic tie rule** (Ring and Orseau, AGI 2011,
§2, optimal variants, with footnote 4, *"Ties are broken lexicographically"*):
taking `A^μ`'s actions, where `A^μ` breaks ties by `infiniteLexBestAction` at the
point prior, is optimal for the true environment on every history the true
program explains. `τ h` is the time index (print's `t_h = |h| + 1`; any choice is
allowed); `optimal_of_same_optimalAction` is the `τ = |h|` instance. -/
public theorem optimal_of_same_infiniteLexBestAction [LinearOrder Action]
    [WellFoundedLT Action] [DecidableEq Obs] (q₀ : Code)
    (ag : Agent Action Obs) (τ : History Action Obs → ℕ)
    (hat : ∀ h, InfAttains (M.point q₀).belief ag (τ h) h) (π : History Action Obs → Action)
    (hsame : ∀ h, M.Consistent q₀ h →
      π h = infiniteLexBestAction (M.point q₀).belief ag (τ h) h (hat h))
    (h : History Action Obs) (hc : M.Consistent q₀ h) (b : Action) :
    infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag (τ h) h b ≤
      infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag (τ h) h (π h) := by
  rw [← M.infiniteActionValue_point_eq q₀ ag _ h hc,
    ← M.infiniteActionValue_point_eq q₀ ag _ h hc, hsame h hc]
  exact infiniteLexBestAction_max _ ag _ h (hat h) b

/-- **Trajectory-wise optimality.** Along the whole history the policy generates
in the true environment, every action it takes is optimal there, when it takes
`A^μ`'s actions. -/
public theorem optimal_along_trajectory [DecidableEq Obs] (q₀ : Code)
    (ag : Agent Action Obs) (τ : History Action Obs → ℕ)
    (hat : ∀ h, InfAttains (M.point q₀).belief ag (τ h) h) (π : History Action Obs → Action)
    (hsame : ∀ h, M.Consistent q₀ h →
      π h = infiniteBestAction (M.point q₀).belief ag (τ h) h (hat h))
    (k : ℕ) (b : Action) :
    infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag
        (τ (trajectory (M.run q₀) π k)) (trajectory (M.run q₀) π k) b ≤
      infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag
        (τ (trajectory (M.run q₀) π k)) (trajectory (M.run q₀) π k)
        (π (trajectory (M.run q₀) π k)) :=
  M.optimal_of_same_infiniteBestAction q₀ ag τ hat π hsame _
    (M.trajectory_consistent q₀ π k) b

/--
**The optimal agent `A^μ`'s action** (Orseau and Ring, AGI 2011, §2.1): equations
(1)–(3) with `ρ` replaced by the point prior `μ` on the true program `q₀`, at the
infinite-horizon value, with time index `t = |h|` (print's `a_{|h|} := argmax_a
v_{|h|}(ha)`) and ties broken lexicographically (print's footnote 5), so that
`A^μ` is a function of the history and "mistake" below does not depend on an
arbitrary choice among tied actions.
-/
@[expose] public noncomputable def optimalAction [LinearOrder Action] [WellFoundedLT Action]
    (q₀ : Code) (ag : Agent Action Obs) (h : History Action Obs)
    (hat : InfAttains (M.point q₀).belief ag h.length h) : Action :=
  infiniteLexBestAction (M.point q₀).belief ag h.length h hat

/-- `A^μ` calculates the optimal action: on every history the true program
explains, its action maximises the action value in the true environment. -/
public theorem optimalAction_max [LinearOrder Action] [WellFoundedLT Action]
    [DecidableEq Obs] (q₀ : Code) (ag : Agent Action Obs) (h : History Action Obs)
    (hat : InfAttains (M.point q₀).belief ag h.length h) (hc : M.Consistent q₀ h)
    (b : Action) :
    infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag h.length h b ≤
      infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag h.length h
        (M.optimalAction q₀ ag h hat) := by
  rw [← M.infiniteActionValue_point_eq q₀ ag _ h hc,
    ← M.infiniteActionValue_point_eq q₀ ag _ h hc]
  exact infiniteLexBestAction_max _ ag _ h hat b

/-- A learning agent that takes `A^μ`'s actions (`optimalAction`, time index
`t = |h|` as in Orseau and Ring, AGI 2011, §2.1) is optimal for the true
environment on every history the true program explains. -/
public theorem optimal_of_same_optimalAction [LinearOrder Action] [WellFoundedLT Action]
    [DecidableEq Obs] (q₀ : Code) (ag : Agent Action Obs)
    (hat : ∀ h : History Action Obs, InfAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action)
    (hsame : ∀ h, M.Consistent q₀ h → π h = M.optimalAction q₀ ag h (hat h))
    (h : History Action Obs) (hc : M.Consistent q₀ h) (b : Action) :
    infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag h.length h b ≤
      infiniteActionValue (DelusionBox.diracBelief (M.run q₀)) ag h.length h (π h) := by
  rw [hsame h hc]
  exact M.optimalAction_max q₀ ag h (hat h) hc b

/-- `A^μ` as a policy, given the attainment print presupposes at every history. -/
@[expose] public noncomputable def optimalPolicy [LinearOrder Action] [WellFoundedLT Action]
    (q₀ : Code) (ag : Agent Action Obs)
    (hat : ∀ h : History Action Obs, InfAttains (M.point q₀).belief ag h.length h) :
    History Action Obs → Action :=
  fun h => M.optimalAction q₀ ag h (hat h)

/-- A **mistake** of the policy `π` at history `h`: its action differs from
`A^μ`'s given the same history (Orseau and Ring, AGI 2011, §2.1). -/
@[expose] public def Mistake [LinearOrder Action] [WellFoundedLT Action]
    (q₀ : Code) (ag : Agent Action Obs)
    (hat : ∀ h : History Action Obs, InfAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action) (h : History Action Obs) : Prop :=
  π h ≠ M.optimalPolicy q₀ ag hat h

/--
**Asymptotic optimality** (Orseau and Ring, AGI 2011, §2.1): along the history the
policy generates in the true environment, it eventually makes no mistakes.

**Reading.** Print's *"the number of mistakes it makes tends towards zero"* is
informal. It is read here as the per-step mistake indicator tending to zero,
which for a `0/1` indicator is "eventually no mistakes", i.e. finitely many
mistakes along the trajectory — matching print's *"past mistakes have only
finite consequences"*. `asymptoticallyOptimal_iff_tendsto` states the indicator
form. The other reading, the mistake *frequency* (mistakes up to step `k`,
divided by `k`) tending to zero, is weaker and is not the one defined here.
-/
@[expose] public def AsymptoticallyOptimal [LinearOrder Action] [WellFoundedLT Action]
    (q₀ : Code) (ag : Agent Action Obs)
    (hat : ∀ h : History Action Obs, InfAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action) : Prop :=
  ∀ᶠ k in Filter.atTop, ¬ M.Mistake q₀ ag hat π (trajectory (M.run q₀) π k)

open Classical in
/-- Asymptotic optimality is the mistake indicator tending to zero, print's
*"the number of mistakes it makes tends towards zero"* at the per-step reading. -/
public theorem asymptoticallyOptimal_iff_tendsto [LinearOrder Action] [WellFoundedLT Action]
    (q₀ : Code) (ag : Agent Action Obs)
    (hat : ∀ h : History Action Obs, InfAttains (M.point q₀).belief ag h.length h)
    (π : History Action Obs → Action) :
    M.AsymptoticallyOptimal q₀ ag hat π ↔
      Filter.Tendsto (fun k => if M.Mistake q₀ ag hat π (trajectory (M.run q₀) π k)
        then (1 : ℝ) else 0) Filter.atTop (nhds 0) := by
  constructor
  · intro hev
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hev] with k hk
    simp [hk]
  · intro ht
    have hlt := ht.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
    filter_upwards [hlt] with k hk hm
    simp [hm] at hk

/-- `A^μ` is asymptotically optimal: it never makes a mistake. -/
public theorem asymptoticallyOptimal_optimalPolicy [LinearOrder Action] [WellFoundedLT Action]
    (q₀ : Code) (ag : Agent Action Obs)
    (hat : ∀ h : History Action Obs, InfAttains (M.point q₀).belief ag h.length h) :
    M.AsymptoticallyOptimal q₀ ag hat (M.optimalPolicy q₀ ag hat) :=
  Filter.Eventually.of_forall fun _ hm => hm rfl

end Model

/-! ### Same actions, same prediction mistakes

Orseau and Ring, AGI 2011, §2.1: *"`ρ` is not replaced by `μ` in utility
functions, i.e. `A^μ_p` predicts the future inputs with `ρ` (so as to be compared
with `A^ρ_p`) … if `A^μ_p` and `A^ρ_p` take the same actions, they make the same
prediction mistakes."* The prediction agent's utility is a function of the history
and the predictor only (`DelusionBox.predictionAgent_utility_snoc`), never of the
belief, so `A^μ_p` and `A^ρ_p` share it by construction; what remains is that the
same actions against the same deterministic environment give the same histories.
-/

/-- Two policies that take the same action at every history along one's
trajectory against a deterministic environment generate the same trajectory. -/
public theorem trajectory_eq_of_agree {Action Obs : Type*}
    (E : History Action Obs → Action → Obs) (π π' : History Action Obs → Action)
    (hsame : ∀ k, π (trajectory E π k) = π' (trajectory E π k)) :
    ∀ k, trajectory E π k = trajectory E π' k
  | 0 => rfl
  | k + 1 => by
      simp only [trajectory]
      rw [← trajectory_eq_of_agree E π π' hsame k, hsame k]

/-- **Same actions, same prediction mistakes** (Orseau and Ring, AGI 2011, §2.1):
if a learning prediction agent `π` (`A^ρ_p`) takes `A^μ_p`'s action at every step
of its run in the true environment, the two prediction agents' utilities agree at
every step, so they make the same prediction mistakes (utility `0` after an
observation is a mistake, `DelusionBox.predictionAgent_utility_snoc`). Both use
the same predictor `predict`, print's `ρ`-based predictor. -/
public theorem Model.same_prediction_mistakes {Code Action Obs : Type*}
    (M : Model Code Action Obs) [LinearOrder Action] [WellFoundedLT Action] [DecidableEq Obs]
    (q₀ : Code) (predict : History Action Obs → Obs) (m : ℕ)
    (hat : ∀ h : History Action Obs,
      InfAttains (M.point q₀).belief (DelusionBox.predictionAgent predict m) h.length h)
    (π : History Action Obs → Action)
    (hsame : ∀ k, π (trajectory (M.run q₀) π k) =
      M.optimalPolicy q₀ (DelusionBox.predictionAgent predict m) hat (trajectory (M.run q₀) π k))
    (k : ℕ) :
    (DelusionBox.predictionAgent predict m).utility (trajectory (M.run q₀) π k) =
      (DelusionBox.predictionAgent predict m).utility
        (trajectory (M.run q₀) (M.optimalPolicy q₀ (DelusionBox.predictionAgent predict m) hat) k) := by
  rw [trajectory_eq_of_agree (M.run q₀) π _ hsame k]

/-! ### Footnote 6 along the environment's own histories

Orseau and Ring, *Self-Modification and Mortality in Artificial Agents*, AGI 2011,
footnote 6, PDF p. 4: *"there is only one environment in which the prediction
makes 0 mistake"*. Print's environments are programs on actions, and "makes 0
mistake" constrains only the histories the environment itself generates.
`DelusionBox.predictionAgent_existsUnique_zero_mistakes` asks for no mistake at
every history, including histories the environment never produces, and is unique
as a response function. Here the condition is read along the environment's own
runs (`ZeroMistakesOnRuns`), under every policy, so under every action sequence;
two such environments generate the same history for every policy
(`trajectory_eq_of_zeroMistakesOnRuns`) and answer every action alike at every
history they generate (`apply_eq_of_zeroMistakesOnRuns`). The predictor reads the
current action (`DelusionBox.predictionAgentAct`); the action-blind predictor of
`DelusionBox.predictionAgent` is the instance
`predictionAgent_existsUnique_zero_mistakes_on_runs`. Uniqueness as a function
on all histories fails at this reading, since an environment is unconstrained off
its runs; the Examples witness two such environments that differ off their runs.
-/

/-- **The prediction makes no mistake along the environment's own runs**: for every
policy, at every step of the history the deterministic environment E generates
against it, the utility of the prediction agent with an action-aware predictor
(`DelusionBox.predictionAgentAct`, print's prediction from the history and the
current action) is one. A policy that reads only the
history's length is an action sequence, so this covers every action sequence.
Histories E never generates are unconstrained. -/
@[expose] public def ZeroMistakesOnRuns {Action Obs : Type*} [DecidableEq Obs]
    (predict : History Action Obs → Action → Obs) (m : ℕ) (E : History Action Obs → Action → Obs) :
    Prop :=
  ∀ (π : History Action Obs → Action) (k : ℕ),
    (DelusionBox.predictionAgentAct predict m).utility (trajectory E π (k + 1)) = 1

/-- No mistake along the runs is exactly: at every history the environment
generates, its answer to the policy's action is the prediction made there for that
action. -/
public theorem zeroMistakesOnRuns_iff {Action Obs : Type*} [DecidableEq Obs]
    (predict : History Action Obs → Action → Obs) (m : ℕ) (E : History Action Obs → Action → Obs) :
    ZeroMistakesOnRuns predict m E ↔
      ∀ (π : History Action Obs → Action) (k : ℕ),
        E (trajectory E π k) (π (trajectory E π k)) =
          predict (trajectory E π k) (π (trajectory E π k)) := by
  refine forall_congr' fun π => forall_congr' fun k => ?_
  simp only [trajectory]
  rw [DelusionBox.predictionAgentAct_utility_snoc]
  constructor
  · intro hk
    split_ifs at hk with hp
    · exact hp.symm
    · norm_num at hk
  · intro hk
    rw [if_pos hk.symm]

/-- The predictor itself, read as an environment, makes no mistake along its runs (it
makes none at any history). -/
public theorem zeroMistakesOnRuns_predict {Action Obs : Type*} [DecidableEq Obs]
    (predict : History Action Obs → Action → Obs) (m : ℕ) :
    ZeroMistakesOnRuns predict m predict :=
  (zeroMistakesOnRuns_iff predict m _).mpr fun _ _ => rfl

/-- **Two environments that never err along their own runs generate the same
history for every policy**, so for every action sequence (Orseau and Ring, AGI
2011, footnote 6, at print's reading: the zero-mistake condition binds only the
histories each environment generates). Induction on the step count: the histories
agree so far, and each environment answers the policy's next action with the same
prediction. -/
public theorem trajectory_eq_of_zeroMistakesOnRuns {Action Obs : Type*} [DecidableEq Obs]
    {predict : History Action Obs → Action → Obs} {m : ℕ} {E E' : History Action Obs → Action → Obs}
    (hE : ZeroMistakesOnRuns predict m E) (hE' : ZeroMistakesOnRuns predict m E')
    (π : History Action Obs → Action) : ∀ k, trajectory E π k = trajectory E' π k
  | 0 => rfl
  | k + 1 => by
      have ih := trajectory_eq_of_zeroMistakesOnRuns hE hE' π k
      have h1 := (zeroMistakesOnRuns_iff predict m E).mp hE π k
      have h2 := (zeroMistakesOnRuns_iff predict m E').mp hE' π k
      simp only [trajectory]
      rw [h1, h2, ih]

/-- A trajectory after k steps has length k. -/
private theorem trajectory_length' {Action Obs : Type*} (E : History Action Obs → Action → Obs)
    (π : History Action Obs → Action) : ∀ k, (trajectory E π k).length = k
  | 0 => rfl
  | k + 1 => by simp [trajectory, trajectory_length' E π k]

/-- Switching the policy's action at one step count leaves the trajectory up to that
step unchanged. -/
private theorem trajectory_switch {Action Obs : Type*} (E : History Action Obs → Action → Obs)
    (π : History Action Obs → Action) (k : ℕ) (a : Action) :
    ∀ j, j ≤ k →
      trajectory E (fun h => if h.length = k then a else π h) j = trajectory E π j
  | 0, _ => rfl
  | j + 1, hj => by
      have ih := trajectory_switch E π k a j (by omega)
      have hne : (trajectory E π j).length ≠ k := by rw [trajectory_length']; omega
      simp only [trajectory, ih, if_neg hne]

/-- **An environment that never errs along its runs answers every action with the
prediction, at every history it generates**: the policy that takes that action at
that step generates the same history up to it. -/
public theorem apply_eq_predict_of_zeroMistakesOnRuns {Action Obs : Type*} [DecidableEq Obs]
    {predict : History Action Obs → Action → Obs} {m : ℕ} {E : History Action Obs → Action → Obs}
    (hE : ZeroMistakesOnRuns predict m E) (π : History Action Obs → Action) (k : ℕ)
    (a : Action) : E (trajectory E π k) a = predict (trajectory E π k) a := by
  have h := (zeroMistakesOnRuns_iff predict m E).mp hE
    (fun h => if h.length = k then a else π h) k
  rw [trajectory_switch E π k a k le_rfl] at h
  rwa [if_pos (trajectory_length' E π k)] at h

/-- **Two environments that never err along their runs are the same program on
actions**: at every history either generates they answer every action alike. -/
public theorem apply_eq_of_zeroMistakesOnRuns {Action Obs : Type*} [DecidableEq Obs]
    {predict : History Action Obs → Action → Obs} {m : ℕ} {E E' : History Action Obs → Action → Obs}
    (hE : ZeroMistakesOnRuns predict m E) (hE' : ZeroMistakesOnRuns predict m E')
    (π : History Action Obs → Action) (k : ℕ) (a : Action) :
    E (trajectory E π k) a = E' (trajectory E π k) a := by
  rw [apply_eq_predict_of_zeroMistakesOnRuns hE π k a, trajectory_eq_of_zeroMistakesOnRuns hE hE' π k,
    apply_eq_predict_of_zeroMistakesOnRuns hE' π k a]

/-- **Footnote 6 along the environment's own histories** (Orseau and Ring, AGI 2011,
footnote 6, PDF p. 4: *"there is only one environment in which the prediction makes
0 mistake"*): an environment that makes no prediction mistake along its own runs
exists, and any two such environments generate the same history for every policy,
so for every action sequence; they are one environment as a program on actions.
Print's zero-mistake condition binds only generated histories, which is why the
uniqueness is of the generated histories and not of the response function at every
history (`DelusionBox.predictionAgent_existsUnique_zero_mistakes` is that stronger
reading). -/
public theorem predictionAgentAct_existsUnique_zero_mistakes_on_runs {Action Obs : Type*}
    [DecidableEq Obs] (predict : History Action Obs → Action → Obs) (m : ℕ) :
    (∃ E : History Action Obs → Action → Obs, ZeroMistakesOnRuns predict m E) ∧
      ∀ E E' : History Action Obs → Action → Obs,
        ZeroMistakesOnRuns predict m E → ZeroMistakesOnRuns predict m E' →
          ∀ (π : History Action Obs → Action) (k : ℕ), trajectory E π k = trajectory E' π k :=
  ⟨⟨_, zeroMistakesOnRuns_predict predict m⟩,
    fun _ _ hE hE' π => trajectory_eq_of_zeroMistakesOnRuns hE hE' π⟩

/-- **Footnote 6 along runs for the action-blind predictor** of
`DelusionBox.predictionAgent`, the instance of
`predictionAgentAct_existsUnique_zero_mistakes_on_runs` at a predictor that ignores
the current action (`DelusionBox.predictionAgent_eq_predictionAgentAct`). -/
public theorem predictionAgent_existsUnique_zero_mistakes_on_runs {Action Obs : Type*}
    [DecidableEq Obs] (predict : History Action Obs → Obs) (m : ℕ) :
    (∃ E : History Action Obs → Action → Obs,
        ZeroMistakesOnRuns (fun h (_ : Action) => predict h) m E) ∧
      ∀ E E' : History Action Obs → Action → Obs,
        ZeroMistakesOnRuns (fun h (_ : Action) => predict h) m E →
        ZeroMistakesOnRuns (fun h (_ : Action) => predict h) m E' →
          ∀ (π : History Action Obs → Action) (k : ℕ), trajectory E π k = trajectory E' π k :=
  predictionAgentAct_existsUnique_zero_mistakes_on_runs _ m

/-! ### AIXI's prior `ξ`

Ring and Orseau, AGI 2011, §2, reinforcement-learning agent: *"For the special
case of the reinforcement-learning agent AIXI: `ρ(h) = ξ(h) := Σ_{q ∈ 𝒬_h}
2^{-|q|}` (where `|q|` is the length of program `q`)."*

`xiModel` is the program model with weight `2^{-|q|}` on a uniquely decodable
set `P` of binary programs (a prefix-free program set, the universal machine's
domain, is one); its mass at `h` is print's `ξ(h)` (`xiModel_mass`), and AIXI
is `DelusionBox.rlAgent` paired with `(xiModel P hP run).belief`. Summability is
the Kraft–McMillan inequality.

**Scope.** The interpreter `run` is total, as `Model.run` is: every program
answers every history and action. Print's programs need not halt; a program
that diverges is in no `𝒬_h` past the point of divergence, and that partial
semantics is `partialXiModel` (§ Partial programs below), of which `xiModel` is
the total case (`xiModel_toPartial`). No universal machine is fixed: `run` is a
parameter.
-/

/-- A subset of a uniquely decodable code is uniquely decodable. -/
private theorem uniquelyDecodable_mono {α : Type*} {S T : Set (List α)} (hST : S ⊆ T)
    (hT : InformationTheory.UniquelyDecodable T) : InformationTheory.UniquelyDecodable S :=
  fun L₁ L₂ h₁ h₂ hf => hT L₁ L₂ (fun w hw => hST (h₁ w hw)) (fun w hw => hST (h₂ w hw)) hf

/-- Kraft–McMillan on every finite set of programs: the weights `2^{-|q|}` of a
uniquely decodable code sum to at most one. -/
public theorem xi_sum_le_one {P : Set (List Bool)} (hP : InformationTheory.UniquelyDecodable P)
    (s : Finset {q : List Bool // q ∈ P}) :
    ∑ q ∈ s, (1 / 2 : ℝ) ^ q.1.length ≤ 1 := by
  have hk := InformationTheory.kraft_mcmillan_inequality (α := Bool)
    (S := s.map (Function.Embedding.subtype _))
    (uniquelyDecodable_mono (fun w hw => by
      simp only [Finset.coe_map, Function.Embedding.coe_subtype, Set.mem_image,
        Finset.mem_coe] at hw
      obtain ⟨q, -, rfl⟩ := hw
      exact q.2) hP)
  simpa [Finset.sum_map, Fintype.card_bool] using hk

/-- **AIXI's program model** (Ring and Orseau, AGI 2011, §2): weight `2^{-|q|}`
on the programs of a uniquely decodable set `P`, interpreted by `run`. -/
@[expose] public noncomputable def xiModel {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Obs) :
    Model {q : List Bool // q ∈ P} Action Obs where
  run := run
  weight := fun q => (1 / 2 : ℝ) ^ q.1.length
  nonneg := fun q => by positivity
  summable := summable_of_sum_le (fun q => by positivity) (xi_sum_le_one hP)

/-- **Print's `ξ(h) := Σ_{q ∈ 𝒬_h} 2^{-|q|}`**: the mass of `xiModel` at `h` is
the sum of `2^{-|q|}` over the programs consistent with `h`. -/
public theorem xiModel_mass {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Obs)
    (h : History Action Obs) :
    (xiModel P hP run).mass h =
      ∑' q, {q | (xiModel P hP run).Consistent q h}.indicator
        (fun q : {q : List Bool // q ∈ P} => (1 / 2 : ℝ) ^ q.1.length) q :=
  rfl

/-- `ξ` of the empty history is at most one (Kraft–McMillan), so `ξ` is a
semimeasure rather than an unnormalized weight. -/
public theorem xiModel_mass_nil_le_one {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Obs) :
    (xiModel P hP run).mass [] ≤ 1 := by
  rw [Model.mass_nil]
  exact Real.tsum_le_of_sum_le (xiModel P hP run).nonneg (xi_sum_le_one hP)


/-- **AIXI's belief** (Orseau and Ring, AGI 2011, §2.1, `A_rl`: *"For the special
case of the reinforcement-learning agent AIXI: `ρ(h) = ξ(h) := Σ_{q ∈ 𝒬_h}
2^{-|q|}`"*): the observation conditionals induced by `xiModel`,
`ξ(hao) / ξ(h)`. -/
@[expose] public noncomputable def aixiBelief {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Obs) :
    Belief Action Obs :=
  (xiModel P hP run).belief

/-- AIXI's conditional is the ratio of `ξ` masses. -/
public theorem aixiBelief_cond {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Obs)
    (h : History Action Obs) (a : Action) (o : Obs) :
    (aixiBelief P hP run).cond h a o =
      (xiModel P hP run).mass (h ++ [(a, o)]) / (xiModel P hP run).mass h :=
  rfl

/-- AIXI's belief is a subprobability, so the value bounds and the
infinite-horizon value apply to it. -/
public theorem aixiBelief_isSubprobability {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Obs) :
    (aixiBelief P hP run).IsSubprobability :=
  (xiModel P hP run).belief_isSubprobability

/-- The product of AIXI's conditionals along a history is `ξ` normalised by
`ξ(∅)`: print's `ρ(h) = ξ(h)` up to the prior's total mass. -/
public theorem xi_mass_eq_historyMass_aixiBelief {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Obs)
    (h : History Action Obs) :
    (xiModel P hP run).mass h = (xiModel P hP run).mass [] * historyMass (aixiBelief P hP run) h :=
  (xiModel P hP run).mass_eq_historyMass h

/--
**AIXI's action** (Orseau and Ring, AGI 2011, §2.1 with §2, eq. (3) and
footnote 5): the reinforcement-learning agent `A_rl` with `ρ = ξ`, choosing
a at index |h| := the argmax over a of v at |h| of ha at the infinite-horizon value with ties broken
lexicographically. Time index `t = |h|`, this paper's convention (§2.1).

**Interpretive choices.** Programs are binary strings of a uniquely decodable set
`P` (a prefix-free domain is one) with `|q|` their length, and the interpreter
`run` is a total parameter; no universal machine is fixed, and programs that stop
producing output are modelled by `partialAixiBelief`, not here (see `xiModel`). The lexicographic order is a well-founded linear
order on the actions (`lexArgmax`); on a finite action set every linear order is
one.
-/
@[expose] public noncomputable def aixiAction {Action Obs : Type*} [LinearOrder Action]
    [WellFoundedLT Action] (P : Set (List Bool)) (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Obs)
    (reward : Obs → ℝ) (m : ℕ) (h : History Action Obs)
    (hat : InfAttains (aixiBelief P hP run) (DelusionBox.rlAgent reward m) h.length h) :
    Action :=
  infiniteLexBestAction (aixiBelief P hP run) (DelusionBox.rlAgent reward m) h.length h hat

/-- AIXI's action maximises its own infinite-horizon action value under `ξ`. -/
public theorem aixiAction_max {Action Obs : Type*} [LinearOrder Action]
    [WellFoundedLT Action] (P : Set (List Bool)) (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Obs)
    (reward : Obs → ℝ) (m : ℕ) (h : History Action Obs)
    (hat : InfAttains (aixiBelief P hP run) (DelusionBox.rlAgent reward m) h.length h)
    (b : Action) :
    infiniteActionValue (aixiBelief P hP run) (DelusionBox.rlAgent reward m) h.length h b ≤
      infiniteActionValue (aixiBelief P hP run) (DelusionBox.rlAgent reward m) h.length h
        (aixiAction P hP run reward m h hat) :=
  infiniteLexBestAction_max _ _ _ h hat b


/-! ### Partial programs

Orseau and Ring, AGI 2011, §2: *"To say that a program `q ∈ 𝒬` is consistent
with `h` means that the program outputs the observations in the history if it is
given the actions as input"*, with `𝒬` the set of all programs, and
`ρ(h) = Σ_{q ∈ 𝒬_h} ρ(q)`; for AIXI, `ξ(h) := Σ_{q ∈ 𝒬_h} 2^{-|q|}`.

`Model.run` is total. A program of print's `𝒬` may stop producing output (halt
without answering, or diverge), and from then on it is in no `𝒬_h`. `PartialModel`
is the carrier with `run : Code → History → Action → Option Obs`: `none` is "no
output", read classically (a diverging program is `none`). Consistency requires
`run q h a = some o`. Mass, belief and the historyMass product carry over
unchanged; the sum over next observations becomes an inequality
(`PartialModel.mass_sum_extensions_le`), so the mass is a semimeasure and the
belief a subprobability that can lose mass. `Model.toPartial` embeds every total
model with the same mass (`Model.toPartial_mass`), and `partialXiModel` is print's
`ξ` over partial programs, of which `xiModel` is the total case
(`xiModel_toPartial`).
-/

/-- A program interpretation that may produce no output, with a summable
nonnegative prior (Orseau and Ring, AGI 2011, §2: programs of `𝒬`). -/
public structure PartialModel (Code Action Obs : Type*) where
  /-- Interpret a program after the recorded interactions and the next action;
  `none` when it produces no observation. -/
  run : Code → History Action Obs → Action → Option Obs
  /-- Prior weight of the program, before seeing observations. -/
  weight : Code → ℝ
  /-- Prior weights are nonnegative. -/
  nonneg : ∀ q, 0 ≤ weight q
  /-- The source requires finite total consistent mass, including at the empty history. -/
  summable : Summable weight

namespace PartialModel

variable {Code Action Obs : Type*} (M : PartialModel Code Action Obs)

/-- A program is consistent when it outputs every recorded observation. -/
public inductive Consistent (q : Code) : History Action Obs → Prop
  | nil : Consistent q []
  | snoc {h : History Action Obs} {a : Action} {o : Obs} :
      Consistent q h → M.run q h a = some o → Consistent q (h ++ [(a, o)])

/-- Consistency at an extended history is old consistency and a matching output. -/
public theorem consistent_snoc (q : Code) (h : History Action Obs) (a : Action) (o : Obs) :
    M.Consistent q (h ++ [(a, o)]) ↔ M.Consistent q h ∧ M.run q h a = some o := by
  constructor
  · intro hc
    generalize he : h ++ [(a, o)] = hs at hc
    cases hc with
    | nil => simp at he
    | @snoc h' a' o' old output =>
      have hl : h.length = h'.length := by simpa using congrArg List.length he
      obtain ⟨hh, hp⟩ := List.append_inj he hl
      have ha : a = a' := by simpa using congrArg (fun l ↦ l.head?.map Prod.fst) hp
      have ho : o = o' := by simpa using congrArg (fun l ↦ l.head?.map Prod.snd) hp
      subst h' a' o'
      exact ⟨old, output⟩
  · rintro ⟨hc, ho⟩
    exact .snoc hc ho

/-- Print's `ρ(h) = Σ_{q ∈ 𝒬_h} ρ(q)` over partial programs. -/
@[expose] public noncomputable def mass (h : History Action Obs) : ℝ :=
  ∑' q, {q | M.Consistent q h}.indicator M.weight q

private theorem mass_summable (h : History Action Obs) :
    Summable ({q | M.Consistent q h}.indicator M.weight) :=
  M.summable.indicator _

private theorem indicator_nonneg (s : Set Code) (q : Code) : 0 ≤ s.indicator M.weight q := by
  classical
  simp only [Set.indicator_apply]
  split_ifs <;> simp [M.nonneg]

/-- Every consistent-history mass is nonnegative. -/
public theorem mass_nonneg (h : History Action Obs) : 0 ≤ M.mass h :=
  tsum_nonneg fun q => M.indicator_nonneg _ q

/-- The empty-history mass is the total prior weight. -/
public theorem mass_nil : M.mass [] = ∑' q, M.weight q := by
  simp [mass, Consistent.nil]

/-- Observing another output can only discard programs and decrease prior mass. -/
public theorem mass_snoc_le (h : History Action Obs) (a : Action) (o : Obs) :
    M.mass (h ++ [(a, o)]) ≤ M.mass h := by
  classical
  apply Summable.tsum_le_tsum _ (M.mass_summable _) (M.mass_summable _)
  intro q
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, consistent_snoc]
  split_ifs <;> simp_all [M.nonneg]

/-- The conditional observation weights `ρ(hao)/ρ(h)`; zero at a zero-mass history. -/
@[expose] public noncomputable def belief : Belief Action Obs where
  cond := fun h a o ↦ M.mass (h ++ [(a, o)]) / M.mass h

/-- The induced conditionals are nonnegative. -/
public theorem belief_nonneg (h : History Action Obs) (a : Action) (o : Obs) :
    0 ≤ M.belief.cond h a o := div_nonneg (M.mass_nonneg _) (M.mass_nonneg _)

/-- The conditioning identity, including at impossible histories. -/
public theorem mass_mul_cond (h : History Action Obs) (a : Action) (o : Obs) :
    M.mass h * M.belief.cond h a o = M.mass (h ++ [(a, o)]) := by
  by_cases hz : M.mass h = 0
  · have he : M.mass (h ++ [(a, o)]) = 0 :=
      le_antisymm (by simpa [hz] using M.mass_snoc_le h a o) (M.mass_nonneg _)
    simp [hz, he, belief]
  · exact mul_div_cancel₀ _ hz

private theorem mass_mul_go (tail pre : History Action Obs) :
    M.mass pre * historyMass.go M.belief tail pre = M.mass (pre ++ tail) := by
  induction tail generalizing pre with
  | nil => simp [historyMass.go]
  | cons p rest ih =>
    rw [historyMass.go, ← mul_assoc, M.mass_mul_cond, ih]
    simp

/-- The observation product is the program mass normalised by the empty-history mass. -/
public theorem mass_eq_historyMass (h : History Action Obs) :
    M.mass h = M.mass [] * historyMass M.belief h := by
  simpa [historyMass] using (M.mass_mul_go h []).symm

private theorem extension_sum_le (h : History Action Obs) (a : Action) (q : Code) :
    (∑' o, {q | M.Consistent q (h ++ [(a, o)])}.indicator M.weight q) ≤
      {q | M.Consistent q h}.indicator M.weight q := by
  classical
  cases hr : M.run q h a with
  | none =>
    have hz : ∀ o, {q | M.Consistent q (h ++ [(a, o)])}.indicator M.weight q = 0 := by
      intro o
      simp [consistent_snoc, hr]
    simp only [hz, tsum_zero]
    exact M.indicator_nonneg _ q
  | some o₀ =>
    rw [tsum_eq_single o₀]
    · simp [Set.indicator_apply, consistent_snoc, hr]
    · intro o ho
      simp [consistent_snoc, hr, Ne.symm ho]

private theorem extensions_summable (h : History Action Obs) (a : Action) :
    Summable (fun p : Code × Obs ↦
      {q | M.Consistent q (h ++ [(a, p.2)])}.indicator M.weight p.1) := by
  classical
  apply (summable_prod_of_nonneg (fun p => M.indicator_nonneg _ p.1)).mpr
  constructor
  · intro q
    apply summable_of_ne_finset_zero (s := (M.run q h a).toFinset)
    intro o ho
    simp only [Option.mem_toFinset, Option.mem_def] at ho
    simp [consistent_snoc, ho]
  · exact Summable.of_nonneg_of_le (fun q => tsum_nonneg fun o => M.indicator_nonneg _ q)
      (M.extension_sum_le h a) (M.mass_summable h)

/-- **Print's `ξ` is a semimeasure**: programs that stop producing output drop
out, so the next-observation masses sum to at most the current mass. -/
public theorem mass_sum_extensions_le (h : History Action Obs) (a : Action) :
    ∑' o, M.mass (h ++ [(a, o)]) ≤ M.mass h := by
  have hs := M.extensions_summable h a
  change Summable (Function.uncurry (fun q o ↦
    {q | M.Consistent q (h ++ [(a, o)])}.indicator M.weight q)) at hs
  refine hs.tsum_comm.trans_le ?_
  exact Summable.tsum_le_tsum (M.extension_sum_le h a)
    (Summable.of_nonneg_of_le (fun q => tsum_nonneg fun o => M.indicator_nonneg _ q)
      (M.extension_sum_le h a) (M.mass_summable h)) (M.mass_summable h)

/-- The observation family is summable. -/
public theorem belief_summable (h : History Action Obs) (a : Action) :
    Summable (M.belief.cond h a) := by
  have hs := (M.extensions_summable h a).prod_symm.prod
  change Summable (fun o ↦ M.mass (h ++ [(a, o)])) at hs
  exact hs.div_const (M.mass h)

/-- The partial-program belief is a subprobability; mass lost to programs that
stop producing output makes the total strictly below one possible. -/
public theorem belief_isSubprobability : M.belief.IsSubprobability where
  nonneg := M.belief_nonneg
  summable := M.belief_summable
  total_le_one := by
    intro h a
    by_cases hh : M.mass h = 0
    · simp [belief, hh]
    · simp only [belief, tsum_div_const]
      exact div_le_one_of_le₀ (M.mass_sum_extensions_le h a) (M.mass_nonneg h)

end PartialModel

namespace Model

variable {Code Action Obs : Type*} (M : Model Code Action Obs)

/-- A total program model is the partial model whose programs always output. -/
@[expose] public def toPartial : PartialModel Code Action Obs where
  run := fun q h a => some (M.run q h a)
  weight := M.weight
  nonneg := M.nonneg
  summable := M.summable

/-- The embedding keeps consistency. -/
public theorem toPartial_consistent (q : Code) (h : History Action Obs) :
    M.toPartial.Consistent q h ↔ M.Consistent q h := by
  constructor
  · intro hc
    induction hc with
    | nil => exact .nil
    | snoc _ ho ih => exact .snoc ih (Option.some_injective _ ho)
  · intro hc
    induction hc with
    | nil => exact .nil
    | snoc _ ho ih => exact .snoc ih (congrArg some ho)

/-- The embedding keeps the mass. -/
public theorem toPartial_mass (h : History Action Obs) : M.toPartial.mass h = M.mass h := by
  simp only [PartialModel.mass, mass, toPartial_consistent]
  rfl

/-- The embedding keeps the belief. -/
public theorem toPartial_belief_cond : M.toPartial.belief.cond = M.belief.cond := by
  funext h a o
  simp only [PartialModel.belief, belief, toPartial_mass]

end Model

/-- **AIXI's program model over partial programs** (Orseau and Ring, AGI 2011,
§2): weight `2^{-|q|}` on the programs of a uniquely decodable set `P`,
interpreted by a `run` that may produce no output. -/
@[expose] public noncomputable def partialXiModel {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Option Obs) :
    PartialModel {q : List Bool // q ∈ P} Action Obs where
  run := run
  weight := fun q => (1 / 2 : ℝ) ^ q.1.length
  nonneg := fun q => by positivity
  summable := summable_of_sum_le (fun q => by positivity) (xi_sum_le_one hP)

/-- **Print's `ξ(h) := Σ_{q ∈ 𝒬_h} 2^{-|q|}`** over partial programs. -/
public theorem partialXiModel_mass {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Option Obs)
    (h : History Action Obs) :
    (partialXiModel P hP run).mass h =
      ∑' q, {q | (partialXiModel P hP run).Consistent q h}.indicator
        (fun q : {q : List Bool // q ∈ P} => (1 / 2 : ℝ) ^ q.1.length) q :=
  rfl

/-- The total `xiModel` is the partial one whose programs always output. -/
public theorem xiModel_toPartial {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Obs) :
    (xiModel P hP run).toPartial = partialXiModel P hP (fun q h a => some (run q h a)) :=
  rfl

/-- **AIXI's belief over partial programs** (Orseau and Ring, AGI 2011, §2.1,
`A_rl` with `ρ = ξ`): the conditionals `ξ(hao)/ξ(h)`. -/
@[expose] public noncomputable def partialAixiBelief {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Option Obs) :
    Belief Action Obs :=
  (partialXiModel P hP run).belief

/-- AIXI's conditional over partial programs is the ratio of `ξ` masses. -/
public theorem partialAixiBelief_cond {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Option Obs)
    (h : History Action Obs) (a : Action) (o : Obs) :
    (partialAixiBelief P hP run).cond h a o =
      (partialXiModel P hP run).mass (h ++ [(a, o)]) / (partialXiModel P hP run).mass h :=
  rfl

/-- AIXI's belief over partial programs is a subprobability. -/
public theorem partialAixiBelief_isSubprobability {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Option Obs) :
    (partialAixiBelief P hP run).IsSubprobability :=
  (partialXiModel P hP run).belief_isSubprobability

/-- The product of AIXI's conditionals over partial programs is `ξ` normalised
by `ξ(∅)`. -/
public theorem partialXi_mass_eq_historyMass {Action Obs : Type*} (P : Set (List Bool))
    (hP : InformationTheory.UniquelyDecodable P)
    (run : {q : List Bool // q ∈ P} → History Action Obs → Action → Option Obs)
    (h : History Action Obs) :
    (partialXiModel P hP run).mass h =
      (partialXiModel P hP run).mass [] * historyMass (partialAixiBelief P hP run) h :=
  (partialXiModel P hP run).mass_eq_historyMass h

end AISafetyAtlas.Wireheading.ProgramPrior
