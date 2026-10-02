module

public import AISafetyAtlas.Wireheading.AgentEquations
public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Bounds for the Ring–Orseau value equations

Finite-depth values under subprobability observation weights and bounded
utility are bounded uniformly in the action. Thus the real supremum and sum
used by the equations denote their mathematical values, rather than their
out-of-domain default zero. The bounds require no finite action or observation
type. The module also constructs the infinite-horizon limit and proves its
Bellman equation under absolute summability of the horizon. It does not prove
action attainment or convergence for the goal agent's constant-one horizon.
-/

namespace AISafetyAtlas.Wireheading.AgentEquations

variable {Action Obs : Type*}

/-- Probability weights, allowing total mass below one for impossible histories
or terminated computations. The probability case has total mass exactly one. -/
public structure Belief.IsSubprobability (ρ : Belief Action Obs) : Prop where
  /-- Each observation weight is nonnegative. -/
  nonneg : ∀ h a o, 0 ≤ ρ.cond h a o
  /-- Observation weights are summable on an arbitrary observation type. -/
  summable : ∀ h a, Summable (ρ.cond h a)
  /-- Missing mass can terminate, but never creates extra probability. -/
  total_le_one : ∀ h a, ∑' o, ρ.cond h a o ≤ 1

/-- A finite tail's absolute horizon budget. -/
@[expose] public def horizonBudget (ag : Agent Action Obs) (t : ℕ) : ℕ → ℕ → ℝ
  | 0, k => |ag.horizon t k|
  | n + 1, k => |ag.horizon t k| + horizonBudget ag t n (k + 1)

/-- Horizon budgets are nonnegative, including for signed horizon weights. -/
public theorem horizonBudget_nonneg (ag : Agent Action Obs) (t n k : ℕ) :
    0 ≤ horizonBudget ag t n k := by
  induction n generalizing k with
  | zero => exact abs_nonneg _
  | succ n ih => exact add_nonneg (abs_nonneg _) (ih _)

/-- A bounded function is integrable against the discrete observation weights. -/
public theorem Belief.IsSubprobability.summable_mul {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (h : History Action Obs) (a : Action)
    {f : Obs → ℝ} {b : ℝ} (hf : ∀ o, |f o| ≤ b) :
    Summable (fun o ↦ ρ.cond h a o * f o) := by
  apply ((hρ.summable h a).mul_right b).of_norm_bounded
  intro o
  simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg h a o)] using
    mul_le_mul_of_nonneg_left (hf o) (hρ.nonneg h a o)

/-- Expectation cannot exceed a uniform absolute bound. -/
public theorem Belief.IsSubprobability.abs_tsum_mul_le {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (h : History Action Obs) (a : Action)
    {f : Obs → ℝ} {b : ℝ} (hb : 0 ≤ b) (hf : ∀ o, |f o| ≤ b) :
    |∑' o, ρ.cond h a o * f o| ≤ b := by
  have hn := tsum_of_norm_bounded ((hρ.summable h a).hasSum.mul_right b)
    (fun o ↦ show ‖ρ.cond h a o * f o‖ ≤ ρ.cond h a o * b by
      simpa [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg h a o)] using
        mul_le_mul_of_nonneg_left (hf o) (hρ.nonneg h a o))
  have hn' : |∑' o, ρ.cond h a o * f o| ≤ (∑' o, ρ.cond h a o) * b := by
    simpa only [Real.norm_eq_abs] using hn
  exact hn'.trans (by nlinarith [hρ.total_le_one h a])

/-- The finite-depth value is bounded by the absolute horizon budget. -/
public theorem abs_value_le_horizonBudget [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) :
    |value ρ ag t n h| ≤ horizonBudget ag t n h.length := by
  induction n generalizing h with
  | zero =>
    simpa [value, horizonBudget, abs_mul] using
      mul_le_mul_of_nonneg_left (hu h) (abs_nonneg (ag.horizon t h.length))
  | succ n ih =>
    have hb := horizonBudget_nonneg ag t n (h.length + 1)
    have ha (a : Action) : |actionValue ρ ag t n h a| ≤
        horizonBudget ag t n (h.length + 1) := by
      apply hρ.abs_tsum_mul_le h a hb
      intro o
      simpa using ih (h ++ [(a, o)])
    have hbounded : BddAbove (Set.range (actionValue ρ ag t n h)) :=
      ⟨_, fun _ ⟨a, ha'⟩ ↦ ha' ▸ (abs_le.mp (ha a)).2⟩
    have hs : |⨆ a, actionValue ρ ag t n h a| ≤ horizonBudget ag t n (h.length + 1) := by
      apply abs_le.mpr
      constructor
      · obtain ⟨a⟩ := ‹Nonempty Action›
        exact (abs_le.mp (ha a)).1.trans (le_ciSup hbounded a)
      · exact ciSup_le (fun a ↦ (abs_le.mp (ha a)).2)
    change |ag.horizon t h.length * ag.utility h + ⨆ a, actionValue ρ ag t n h a| ≤ _
    exact (abs_add_le _ _).trans (add_le_add
      (by simpa [abs_mul] using
        mul_le_mul_of_nonneg_left (hu h) (abs_nonneg (ag.horizon t h.length))) hs)

/-- No summability side condition is needed beyond the source's probability and
bounded-utility conditions at a finite depth. -/
public theorem actionValue_summable [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) (a : Action) :
    Summable (fun o ↦ ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])) := by
  apply hρ.summable_mul h a (b := horizonBudget ag t n (h.length + 1))
  intro o
  simpa using abs_value_le_horizonBudget hρ ag hu t n (h ++ [(a, o)])

/-- The observation sum is uniformly bounded across actions. -/
public theorem abs_actionValue_le_horizonBudget [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) (a : Action) :
    |actionValue ρ ag t n h a| ≤ horizonBudget ag t n (h.length + 1) := by
  apply hρ.abs_tsum_mul_le h a (horizonBudget_nonneg ag t n (h.length + 1))
  intro o
  simpa using abs_value_le_horizonBudget hρ ag hu t n (h ++ [(a, o)])

/-- The conditional supremum in the value equation is taken over a bounded family. -/
public theorem actionValue_bddAbove [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) : BddAbove (Set.range (actionValue ρ ag t n h)) := by
  refine ⟨horizonBudget ag t n (h.length + 1), ?_⟩
  rintro _ ⟨a, rfl⟩
  exact (abs_le.mp (abs_actionValue_le_horizonBudget hρ ag hu t n h a)).2

private theorem abs_sup_sub_sup_le [Nonempty Action] {f g : Action → ℝ} {b : ℝ}
    (hf : BddAbove (Set.range f)) (hg : BddAbove (Set.range g))
    (hfg : ∀ a, |f a - g a| ≤ b) : |(⨆ a, f a) - ⨆ a, g a| ≤ b := by
  have h₁ : (⨆ a, f a) ≤ (⨆ a, g a) + b := by
    apply ciSup_le
    intro a
    have ha := le_ciSup hg a
    have hb := (abs_le.mp (hfg a)).2
    linarith
  have h₂ : (⨆ a, g a) ≤ (⨆ a, f a) + b := by
    apply ciSup_le
    intro a
    have ha := le_ciSup hf a
    have hb := (abs_le.mp (hfg a)).1
    linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- Adding a single time step changes value by at most that step's horizon weight.
The estimate is uniform over histories of a given length and over actions. -/
public theorem abs_value_succ_sub_le [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) :
    |value ρ ag t (n + 1) h - value ρ ag t n h| ≤ |ag.horizon t (h.length + n + 1)| := by
  induction n generalizing h with
  | zero =>
    have ha (a : Action) := abs_actionValue_le_horizonBudget hρ ag hu t 0 h a
    simp only [horizonBudget] at ha
    simp only [value, Nat.add_zero, add_sub_cancel_left]
    change |⨆ a, actionValue ρ ag t 0 h a| ≤ _
    apply abs_le.mpr
    constructor
    · obtain ⟨a⟩ := ‹Nonempty Action›
      exact (abs_le.mp (ha a)).1.trans (le_ciSup (actionValue_bddAbove hρ ag hu t 0 h) a)
    · exact ciSup_le (fun a ↦ (abs_le.mp (ha a)).2)
  | succ n ih =>
    simp only [value, add_sub_add_left_eq_sub]
    apply abs_sup_sub_sup_le (actionValue_bddAbove hρ ag hu t (n + 1) h)
      (actionValue_bddAbove hρ ag hu t n h)
    intro a
    unfold actionValue
    rw [← (actionValue_summable hρ ag hu t (n + 1) h a).tsum_sub
      (actionValue_summable hρ ag hu t n h a)]
    simp only [← mul_sub]
    apply hρ.abs_tsum_mul_le h a (abs_nonneg _)
    intro o
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (h ++ [(a, o)])

/-- The source's summable horizon makes finite-depth values a Cauchy sequence. -/
public theorem value_cauchySeq [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    CauchySeq (fun n ↦ value ρ ag t n h) := by
  apply cauchySeq_of_dist_le_of_summable (fun n ↦ |ag.horizon t (h.length + n + 1)|)
  · intro n
    simpa [Real.dist_eq, abs_sub_comm] using abs_value_succ_sub_le hρ ag hu t n h
  · exact hw.comp_injective (by intro i j he; dsimp at he; omega)

/-- Infinite-horizon value, obtained from the finite-depth approximants. The
convergence theorem states the probability, utility and horizon conditions that
make this limit denote. No attainment of its action supremum is claimed. -/
@[expose] public noncomputable def infiniteValue (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs) : ℝ :=
  Filter.limUnder Filter.atTop (fun n ↦ value ρ ag t n h)

/-- Under the source's bounded-utility and summable-horizon conditions, the
infinite value is the actual limit of the finite values. -/
public theorem tendsto_value_infiniteValue [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    Filter.Tendsto (fun n ↦ value ρ ag t n h) Filter.atTop (nhds (infiniteValue ρ ag t h)) :=
  (value_cauchySeq hρ ag hu t hw h).tendsto_limUnder

/-- A certified truncation error, uniform at every history of the same length. -/
public theorem value_error_le_tail [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (n : ℕ) (h : History Action Obs) :
    |value ρ ag t n h - infiniteValue ρ ag t h| ≤
      ∑' i : ℕ, |ag.horizon t (h.length + (n + i) + 1)| := by
  apply dist_le_tsum_of_dist_le_of_tendsto (fun n ↦ |ag.horizon t (h.length + n + 1)|)
    (fun n ↦ ?_) (hw.comp_injective (by intro i j he; dsimp at he; omega))
    (tendsto_value_infiniteValue hρ ag hu t hw h) n
  simpa [Real.dist_eq, abs_sub_comm] using abs_value_succ_sub_le hρ ag hu t n h

private theorem horizonBudget_eq_sum (ag : Agent Action Obs) (t n k : ℕ) :
    horizonBudget ag t n k = ∑ i ∈ Finset.range (n + 1), |ag.horizon t (k + i)| := by
  induction n generalizing k with
  | zero => simp [horizonBudget]
  | succ n ih =>
    rw [horizonBudget, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_left_comm, add_comm]

private theorem horizonBudget_le_total (ag : Agent Action Obs) (t n k : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|)) :
    horizonBudget ag t n k ≤ ∑' i : ℕ, |ag.horizon t (k + i)| := by
  rw [horizonBudget_eq_sum]
  exact Summable.sum_le_tsum _ (fun i _ ↦ abs_nonneg _)
    (hw.comp_injective (by intro i j he; exact Nat.add_left_cancel he))

/-- The infinite value is bounded by the remaining absolute horizon mass. -/
public theorem abs_infiniteValue_le [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    |infiniteValue ρ ag t h| ≤ ∑' i : ℕ, |ag.horizon t (h.length + i)| := by
  apply le_of_tendsto' (tendsto_value_infiniteValue hρ ag hu t hw h).abs
  intro n
  exact (abs_value_le_horizonBudget hρ ag hu t n h).trans
    (horizonBudget_le_total ag t n h.length hw)

/-- The action value at the infinite-horizon continuation. -/
@[expose] public noncomputable def infiniteActionValue (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs) (a : Action) : ℝ :=
  ∑' o, ρ.cond h a o * infiniteValue ρ ag t (h ++ [(a, o)])

private theorem infiniteActionValue_summable [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) (a : Action) :
    Summable (fun o ↦ ρ.cond h a o * infiniteValue ρ ag t (h ++ [(a, o)])) := by
  apply hρ.summable_mul h a (b := ∑' i : ℕ, |ag.horizon t (h.length + 1 + i)|)
  intro o
  simpa using abs_infiniteValue_le hρ ag hu t hw (h ++ [(a, o)])

/-- Infinite action values are bounded uniformly, so their real supremum denotes. -/
public theorem infiniteActionValue_bddAbove [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    BddAbove (Set.range (infiniteActionValue ρ ag t h)) := by
  refine ⟨∑' i : ℕ, |ag.horizon t (h.length + 1 + i)|, ?_⟩
  rintro _ ⟨a, rfl⟩
  apply le_trans (le_abs_self _)
  apply hρ.abs_tsum_mul_le h a (tsum_nonneg (fun _ ↦ abs_nonneg _))
  intro o
  simpa using abs_infiniteValue_le hρ ag hu t hw (h ++ [(a, o)])

private theorem actionValue_error_le_tail [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (n : ℕ)
    (h : History Action Obs) (a : Action) :
    |actionValue ρ ag t n h a - infiniteActionValue ρ ag t h a| ≤
      ∑' i : ℕ, |ag.horizon t (h.length + 1 + (n + i) + 1)| := by
  unfold actionValue infiniteActionValue
  rw [← (actionValue_summable hρ ag hu t n h a).tsum_sub
    (infiniteActionValue_summable hρ ag hu t hw h a)]
  simp only [← mul_sub]
  apply hρ.abs_tsum_mul_le h a (tsum_nonneg (fun _ ↦ abs_nonneg _))
  intro o
  simpa using value_error_le_tail hρ ag hu t hw n (h ++ [(a, o)])

/-- The infinite-horizon Bellman equation follows from uniform tail control.
This supplies the limit missing from the mutually recursive printed equations;
it does not replace the source's attainment presupposition by a theorem. -/
public theorem infiniteValue_eq [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    infiniteValue ρ ag t h = ag.horizon t h.length * ag.utility h +
      ⨆ a, infiniteActionValue ρ ag t h a := by
  have hs : Filter.Tendsto (fun n ↦ ⨆ a, actionValue ρ ag t n h a) Filter.atTop
      (nhds (⨆ a, infiniteActionValue ρ ag t h a)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
      ((tendsto_sum_nat_add (fun k ↦ |ag.horizon t k|)).comp
        (Filter.tendsto_add_atTop_nat (h.length + 2)))
    simp only [Function.comp_apply, Real.dist_eq]
    have he := abs_sup_sub_sup_le (actionValue_bddAbove hρ ag hu t n h)
      (infiniteActionValue_bddAbove hρ ag hu t hw h)
      (actionValue_error_le_tail hρ ag hu t hw n h)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he
  have hv := (tendsto_value_infiniteValue hρ ag hu t hw h).comp
    (Filter.tendsto_add_atTop_nat 1)
  have he := hs.const_add (ag.horizon t h.length * ag.utility h)
  exact tendsto_nhds_unique hv he

end AISafetyAtlas.Wireheading.AgentEquations
