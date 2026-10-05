module

public import AISafetyAtlas.Wireheading.DelusionBox
public import AISafetyAtlas.Wireheading.ValueBounds
public import Mathlib.Topology.Algebra.InfiniteSum.Real

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
having a program prior. The interpreter is total on the histories presented to
it; partial/nonterminating program semantics are not covered by this interface.
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

end AISafetyAtlas.Wireheading.ProgramPrior
