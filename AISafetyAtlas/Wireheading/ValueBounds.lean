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
Bellman equation under a dominated tail: a per-length utility bound `b` with
`|u h| ≤ b |h|` and `Summable (|w t ·| * b)` (the dominated-tail family).
Absolute summability of the horizon at `|u| ≤ 1` is the case `b ≡ 1`; `u ≡ 0`
with the constant-one horizon is the case `b ≡ 0`. It does not prove action
attainment, nor convergence for the constant-one horizon at a utility that does
not decay against it.
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

/-- A finite tail's horizon budget weighted by a per-length utility bound `b`
(`|u h| ≤ b |h|`). At `b ≡ 1` it is `horizonBudget` (`dominatedBudget_one`). -/
@[expose] public def dominatedBudget (ag : Agent Action Obs) (b : ℕ → ℝ) (t : ℕ) :
    ℕ → ℕ → ℝ
  | 0, k => |ag.horizon t k| * b k
  | n + 1, k => |ag.horizon t k| * b k + dominatedBudget ag b t n (k + 1)

/-- Dominated budgets are nonnegative at a nonnegative utility bound. -/
public theorem dominatedBudget_nonneg (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hb : ∀ k, 0 ≤ b k) (t n k : ℕ) : 0 ≤ dominatedBudget ag b t n k := by
  induction n generalizing k with
  | zero => exact mul_nonneg (abs_nonneg _) (hb _)
  | succ n ih => exact add_nonneg (mul_nonneg (abs_nonneg _) (hb _)) (ih _)

/-- At the unit utility bound the dominated budget is the absolute horizon budget. -/
public theorem dominatedBudget_one (ag : Agent Action Obs) (t n k : ℕ) :
    dominatedBudget ag (fun _ ↦ 1) t n k = horizonBudget ag t n k := by
  induction n generalizing k with
  | zero => simp [dominatedBudget, horizonBudget]
  | succ n ih => simp [dominatedBudget, horizonBudget, ih]

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

/-- The finite-depth value is bounded by the dominated budget, at a per-length
utility bound `b` (Ring and Orseau, AGI 2011, §2, eq. (3); print states no bound
on `w` and none on `u` beyond its range). -/
public theorem abs_value_le_dominatedBudget [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t n : ℕ) (h : History Action Obs) :
    |value ρ ag t n h| ≤ dominatedBudget ag b t n h.length := by
  induction n generalizing h with
  | zero =>
    simpa [value, dominatedBudget, abs_mul] using
      mul_le_mul_of_nonneg_left (hub h) (abs_nonneg (ag.horizon t h.length))
  | succ n ih =>
    have hb' := dominatedBudget_nonneg ag hb t n (h.length + 1)
    have ha (a : Action) : |actionValue ρ ag t n h a| ≤
        dominatedBudget ag b t n (h.length + 1) := by
      apply hρ.abs_tsum_mul_le h a hb'
      intro o
      simpa using ih (h ++ [(a, o)])
    have hbounded : BddAbove (Set.range (actionValue ρ ag t n h)) :=
      ⟨_, fun _ ⟨a, ha'⟩ ↦ ha' ▸ (abs_le.mp (ha a)).2⟩
    have hs : |⨆ a, actionValue ρ ag t n h a| ≤ dominatedBudget ag b t n (h.length + 1) := by
      apply abs_le.mpr
      constructor
      · obtain ⟨a⟩ := ‹Nonempty Action›
        exact (abs_le.mp (ha a)).1.trans (le_ciSup hbounded a)
      · exact ciSup_le (fun a ↦ (abs_le.mp (ha a)).2)
    change |ag.horizon t h.length * ag.utility h + ⨆ a, actionValue ρ ag t n h a| ≤ _
    exact (abs_add_le _ _).trans (add_le_add
      (by simpa [abs_mul] using
        mul_le_mul_of_nonneg_left (hub h) (abs_nonneg (ag.horizon t h.length))) hs)

/-- The finite-depth value is bounded by the absolute horizon budget. -/
public theorem abs_value_le_horizonBudget [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) :
    |value ρ ag t n h| ≤ horizonBudget ag t n h.length := by
  simpa [dominatedBudget_one] using
    abs_value_le_dominatedBudget hρ ag (b := fun _ ↦ 1) (fun _ ↦ zero_le_one) hu t n h

/-- The observation sum at depth `n` is summable under a per-length utility bound. -/
public theorem actionValue_summable_of_dominated [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t n : ℕ) (h : History Action Obs)
    (a : Action) :
    Summable (fun o ↦ ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])) := by
  apply hρ.summable_mul h a (b := dominatedBudget ag b t n (h.length + 1))
  intro o
  simpa using abs_value_le_dominatedBudget hρ ag hb hub t n (h ++ [(a, o)])

/-- No summability side condition is needed beyond the source's probability and
bounded-utility conditions at a finite depth. -/
public theorem actionValue_summable [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) (a : Action) :
    Summable (fun o ↦ ρ.cond h a o * value ρ ag t n (h ++ [(a, o)])) :=
  actionValue_summable_of_dominated hρ ag (b := fun _ ↦ 1) (fun _ ↦ zero_le_one) hu t n h a

/-- The observation sum is bounded by the dominated budget, uniformly in the action. -/
public theorem abs_actionValue_le_dominatedBudget [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t n : ℕ) (h : History Action Obs)
    (a : Action) :
    |actionValue ρ ag t n h a| ≤ dominatedBudget ag b t n (h.length + 1) := by
  apply hρ.abs_tsum_mul_le h a (dominatedBudget_nonneg ag hb t n (h.length + 1))
  intro o
  simpa using abs_value_le_dominatedBudget hρ ag hb hub t n (h ++ [(a, o)])

/-- The observation sum is uniformly bounded across actions. -/
public theorem abs_actionValue_le_horizonBudget [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) (a : Action) :
    |actionValue ρ ag t n h a| ≤ horizonBudget ag t n (h.length + 1) := by
  simpa [dominatedBudget_one] using
    abs_actionValue_le_dominatedBudget hρ ag (b := fun _ ↦ 1) (fun _ ↦ zero_le_one) hu t n h a

/-- The conditional supremum is over a bounded family under a per-length utility bound. -/
public theorem actionValue_bddAbove_of_dominated [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t n : ℕ) (h : History Action Obs) :
    BddAbove (Set.range (actionValue ρ ag t n h)) := by
  refine ⟨dominatedBudget ag b t n (h.length + 1), ?_⟩
  rintro _ ⟨a, rfl⟩
  exact (abs_le.mp (abs_actionValue_le_dominatedBudget hρ ag hb hub t n h a)).2

/-- The conditional supremum in the value equation is taken over a bounded family. -/
public theorem actionValue_bddAbove [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) : BddAbove (Set.range (actionValue ρ ag t n h)) :=
  actionValue_bddAbove_of_dominated hρ ag (b := fun _ ↦ 1) (fun _ ↦ zero_le_one) hu t n h

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

/-- Adding a single time step changes value by at most that step's horizon weight
times the utility bound at that length. The estimate is uniform over histories of
a given length and over actions. -/
public theorem abs_value_succ_sub_le_of_dominated [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t n : ℕ) (h : History Action Obs) :
    |value ρ ag t (n + 1) h - value ρ ag t n h| ≤
      |ag.horizon t (h.length + n + 1)| * b (h.length + n + 1) := by
  induction n generalizing h with
  | zero =>
    have ha (a : Action) := abs_actionValue_le_dominatedBudget hρ ag hb hub t 0 h a
    simp only [dominatedBudget] at ha
    simp only [value, Nat.add_zero, add_sub_cancel_left]
    change |⨆ a, actionValue ρ ag t 0 h a| ≤ _
    apply abs_le.mpr
    constructor
    · obtain ⟨a⟩ := ‹Nonempty Action›
      exact (abs_le.mp (ha a)).1.trans
        (le_ciSup (actionValue_bddAbove_of_dominated hρ ag hb hub t 0 h) a)
    · exact ciSup_le (fun a ↦ (abs_le.mp (ha a)).2)
  | succ n ih =>
    simp only [value, add_sub_add_left_eq_sub]
    apply abs_sup_sub_sup_le (actionValue_bddAbove_of_dominated hρ ag hb hub t (n + 1) h)
      (actionValue_bddAbove_of_dominated hρ ag hb hub t n h)
    intro a
    unfold actionValue
    rw [← (actionValue_summable_of_dominated hρ ag hb hub t (n + 1) h a).tsum_sub
      (actionValue_summable_of_dominated hρ ag hb hub t n h a)]
    simp only [← mul_sub]
    apply hρ.abs_tsum_mul_le h a (mul_nonneg (abs_nonneg _) (hb _))
    intro o
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using ih (h ++ [(a, o)])

/-- Adding a single time step changes value by at most that step's horizon weight.
The estimate is uniform over histories of a given length and over actions. -/
public theorem abs_value_succ_sub_le [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t n : ℕ) (h : History Action Obs) :
    |value ρ ag t (n + 1) h - value ρ ag t n h| ≤ |ag.horizon t (h.length + n + 1)| := by
  simpa using
    abs_value_succ_sub_le_of_dominated hρ ag (b := fun _ ↦ 1) (fun _ ↦ zero_le_one) hu t n h

/-- A summable dominated tail stays summable when the utility bound is replaced by
its positive part, so the statements below need no sign condition on `b`. -/
private theorem summable_mul_max_zero {ag : Agent Action Obs} {t : ℕ} {b : ℕ → ℝ}
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) :
    Summable (fun k ↦ |ag.horizon t k| * max (b k) 0) :=
  hw.abs.of_nonneg_of_le (fun k ↦ mul_nonneg (abs_nonneg _) (le_max_right _ _))
    (fun k ↦ by
      rw [abs_mul, abs_abs]
      exact mul_le_mul_of_nonneg_left (max_le (le_abs_self _) (abs_nonneg _)) (abs_nonneg _))

/-- A dominated tail makes finite-depth values a Cauchy sequence (Ring and Orseau,
AGI 2011, §2, eq. (3), whose Setting puts no summability condition on `w`): it
suffices that `|w t ·|` is summable against a per-length bound on `|u|`. -/
public theorem value_cauchySeq_of_dominated [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (h : History Action Obs) :
    CauchySeq (fun n ↦ value ρ ag t n h) := by
  apply cauchySeq_of_dist_le_of_summable
    (fun n ↦ |ag.horizon t (h.length + n + 1)| * max (b (h.length + n + 1)) 0)
  · intro n
    simpa [Real.dist_eq, abs_sub_comm] using abs_value_succ_sub_le_of_dominated hρ ag
      (b := fun k ↦ max (b k) 0) (fun _ ↦ le_max_right _ _)
      (fun h ↦ (hub h).trans (le_max_left _ _)) t n h
  · exact (summable_mul_max_zero hw).comp_injective (by intro i j he; dsimp at he; omega)

/-- An absolutely summable horizon at `|u| ≤ 1` makes finite-depth values a Cauchy
sequence: the case `b ≡ 1` of `value_cauchySeq_of_dominated`. -/
public theorem value_cauchySeq [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    CauchySeq (fun n ↦ value ρ ag t n h) :=
  value_cauchySeq_of_dominated hρ ag (b := fun _ ↦ 1) hu t (by simpa using hw) h

/-- Infinite-horizon value, obtained from the finite-depth approximants. The
convergence theorem states the probability, utility and horizon conditions that
make this limit denote. No attainment of its action supremum is claimed. -/
@[expose] public noncomputable def infiniteValue (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs) : ℝ :=
  Filter.limUnder Filter.atTop (fun n ↦ value ρ ag t n h)

/-- Under a dominated tail, the infinite value is the actual limit of the finite
values (Ring and Orseau, AGI 2011, §2, eq. (3): "the expected sum of future
(weighted) utility values"). -/
public theorem tendsto_value_infiniteValue_of_dominated [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (h : History Action Obs) :
    Filter.Tendsto (fun n ↦ value ρ ag t n h) Filter.atTop (nhds (infiniteValue ρ ag t h)) :=
  (value_cauchySeq_of_dominated hρ ag hub t hw h).tendsto_limUnder

/-- Under `|u| ≤ 1` and an absolutely summable horizon, the infinite value is the
actual limit of the finite values: the case `b ≡ 1` of
`tendsto_value_infiniteValue_of_dominated`. -/
public theorem tendsto_value_infiniteValue [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    Filter.Tendsto (fun n ↦ value ρ ag t n h) Filter.atTop (nhds (infiniteValue ρ ag t h)) :=
  (value_cauchySeq hρ ag hu t hw h).tendsto_limUnder

/-- A certified truncation error under a dominated tail, uniform at every history of
the same length. -/
public theorem value_error_le_tail_of_dominated [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (n : ℕ) (h : History Action Obs) :
    |value ρ ag t n h - infiniteValue ρ ag t h| ≤
      ∑' i : ℕ, |ag.horizon t (h.length + (n + i) + 1)| * b (h.length + (n + i) + 1) := by
  apply dist_le_tsum_of_dist_le_of_tendsto
    (fun n ↦ |ag.horizon t (h.length + n + 1)| * b (h.length + n + 1))
    (fun n ↦ ?_) (hw.comp_injective (by intro i j he; dsimp at he; omega))
    (tendsto_value_infiniteValue_of_dominated hρ ag hub t hw h) n
  simpa [Real.dist_eq, abs_sub_comm] using abs_value_succ_sub_le_of_dominated hρ ag hb hub t n h

/-- A certified truncation error, uniform at every history of the same length. -/
public theorem value_error_le_tail [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (n : ℕ) (h : History Action Obs) :
    |value ρ ag t n h - infiniteValue ρ ag t h| ≤
      ∑' i : ℕ, |ag.horizon t (h.length + (n + i) + 1)| := by
  simpa using value_error_le_tail_of_dominated hρ ag (b := fun _ ↦ 1) (fun _ ↦ zero_le_one)
    hu t (by simpa using hw) n h

private theorem dominatedBudget_eq_sum (ag : Agent Action Obs) (b : ℕ → ℝ) (t n k : ℕ) :
    dominatedBudget ag b t n k =
      ∑ i ∈ Finset.range (n + 1), |ag.horizon t (k + i)| * b (k + i) := by
  induction n generalizing k with
  | zero => simp [dominatedBudget]
  | succ n ih =>
    rw [dominatedBudget, ih]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.add_zero, Nat.add_left_comm, add_comm]

private theorem dominatedBudget_le_total (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hb : ∀ k, 0 ≤ b k) (t n k : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) :
    dominatedBudget ag b t n k ≤ ∑' i : ℕ, |ag.horizon t (k + i)| * b (k + i) := by
  rw [dominatedBudget_eq_sum]
  exact Summable.sum_le_tsum _ (fun i _ ↦ mul_nonneg (abs_nonneg _) (hb _))
    (hw.comp_injective (i := fun i ↦ k + i) (by intro i j he; exact Nat.add_left_cancel he))

/-- The infinite value is bounded by the remaining dominated tail mass. -/
public theorem abs_infiniteValue_le_of_dominated [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ} (hb : ∀ k, 0 ≤ b k)
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (h : History Action Obs) :
    |infiniteValue ρ ag t h| ≤ ∑' i : ℕ, |ag.horizon t (h.length + i)| * b (h.length + i) := by
  apply le_of_tendsto' (tendsto_value_infiniteValue_of_dominated hρ ag hub t hw h).abs
  intro n
  exact (abs_value_le_dominatedBudget hρ ag hb hub t n h).trans
    (dominatedBudget_le_total ag hb t n h.length hw)

/-- The infinite value is bounded by the remaining absolute horizon mass. -/
public theorem abs_infiniteValue_le [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    |infiniteValue ρ ag t h| ≤ ∑' i : ℕ, |ag.horizon t (h.length + i)| := by
  simpa using abs_infiniteValue_le_of_dominated hρ ag (b := fun _ ↦ 1) (fun _ ↦ zero_le_one)
    hu t (by simpa using hw) h

/-- The action value at the infinite-horizon continuation. -/
@[expose] public noncomputable def infiniteActionValue (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs) (a : Action) : ℝ :=
  ∑' o, ρ.cond h a o * infiniteValue ρ ag t (h ++ [(a, o)])

private theorem infiniteActionValue_summable_of_dominated [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hb : ∀ k, 0 ≤ b k) (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (h : History Action Obs) (a : Action) :
    Summable (fun o ↦ ρ.cond h a o * infiniteValue ρ ag t (h ++ [(a, o)])) := by
  apply hρ.summable_mul h a
    (b := ∑' i : ℕ, |ag.horizon t (h.length + 1 + i)| * b (h.length + 1 + i))
  intro o
  simpa using abs_infiniteValue_le_of_dominated hρ ag hb hub t hw (h ++ [(a, o)])

private theorem infiniteActionValue_bddAbove_of_nonneg [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hb : ∀ k, 0 ≤ b k) (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (h : History Action Obs) :
    BddAbove (Set.range (infiniteActionValue ρ ag t h)) := by
  refine ⟨∑' i : ℕ, |ag.horizon t (h.length + 1 + i)| * b (h.length + 1 + i), ?_⟩
  rintro _ ⟨a, rfl⟩
  apply le_trans (le_abs_self _)
  apply hρ.abs_tsum_mul_le h a (tsum_nonneg (fun _ ↦ mul_nonneg (abs_nonneg _) (hb _)))
  intro o
  simpa using abs_infiniteValue_le_of_dominated hρ ag hb hub t hw (h ++ [(a, o)])

/-- Under a dominated tail, infinite action values are bounded uniformly, so their
real supremum denotes. -/
public theorem infiniteActionValue_bddAbove_of_dominated [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (h : History Action Obs) :
    BddAbove (Set.range (infiniteActionValue ρ ag t h)) :=
  infiniteActionValue_bddAbove_of_nonneg hρ ag (b := fun k ↦ max (b k) 0)
    (fun _ ↦ le_max_right _ _) (fun h ↦ (hub h).trans (le_max_left _ _)) t
    (summable_mul_max_zero hw) h

/-- Infinite action values are bounded uniformly, so their real supremum denotes. -/
public theorem infiniteActionValue_bddAbove [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    BddAbove (Set.range (infiniteActionValue ρ ag t h)) :=
  infiniteActionValue_bddAbove_of_dominated hρ ag (b := fun _ ↦ 1) hu t (by simpa using hw) h

private theorem actionValue_error_le_tail_of_dominated [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hb : ∀ k, 0 ≤ b k) (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (n : ℕ)
    (h : History Action Obs) (a : Action) :
    |actionValue ρ ag t n h a - infiniteActionValue ρ ag t h a| ≤
      ∑' i : ℕ, |ag.horizon t (h.length + 1 + (n + i) + 1)| *
        b (h.length + 1 + (n + i) + 1) := by
  unfold actionValue infiniteActionValue
  rw [← (actionValue_summable_of_dominated hρ ag hb hub t n h a).tsum_sub
    (infiniteActionValue_summable_of_dominated hρ ag hb hub t hw h a)]
  simp only [← mul_sub]
  apply hρ.abs_tsum_mul_le h a (tsum_nonneg (fun _ ↦ mul_nonneg (abs_nonneg _) (hb _)))
  intro o
  simpa using value_error_le_tail_of_dominated hρ ag hb hub t hw n (h ++ [(a, o)])

/-- **Print's recursion (3) at the infinite-horizon value, under a dominated tail**
(Ring and Orseau, AGI 2011, §2, eq. (3); the Setting states no summability
condition on `w`). The hypotheses are a per-length utility bound `|u h| ≤ b |h|`
and `Summable (|w t ·| * b)`; no sign condition on `b` and no summability of
`|w t ·|` alone. At `b ≡ 1` this is `infiniteValue_eq`; at `u ≡ 0` and `b ≡ 0` it
covers every horizon, the constant-one horizon included. Horizons whose weighted
utility series converges only conditionally are not covered. -/
public theorem infiniteValue_eq_of_dominated [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (h : History Action Obs) :
    infiniteValue ρ ag t h = ag.horizon t h.length * ag.utility h +
      ⨆ a, infiniteActionValue ρ ag t h a := by
  have hb' : ∀ k, 0 ≤ max (b k) 0 := fun _ ↦ le_max_right _ _
  have hub' : ∀ h, |ag.utility h| ≤ max (b h.length) 0 := fun h ↦ (hub h).trans (le_max_left _ _)
  have hw' := summable_mul_max_zero hw
  have hs : Filter.Tendsto (fun n ↦ ⨆ a, actionValue ρ ag t n h a) Filter.atTop
      (nhds (⨆ a, infiniteActionValue ρ ag t h a)) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
      ((tendsto_sum_nat_add (fun k ↦ |ag.horizon t k| * max (b k) 0)).comp
        (Filter.tendsto_add_atTop_nat (h.length + 2)))
    simp only [Function.comp_apply, Real.dist_eq]
    have he := abs_sup_sub_sup_le (actionValue_bddAbove_of_dominated hρ ag hb' hub' t n h)
      (infiniteActionValue_bddAbove_of_nonneg hρ ag hb' hub' t hw' h)
      (actionValue_error_le_tail_of_dominated hρ ag hb' hub' t hw' n h)
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using he
  have hv := (tendsto_value_infiniteValue_of_dominated hρ ag hub t hw h).comp
    (Filter.tendsto_add_atTop_nat 1)
  have he := hs.const_add (ag.horizon t h.length * ag.utility h)
  exact tendsto_nhds_unique hv he

/-- The infinite-horizon Bellman equation follows from uniform tail control.
This supplies the limit missing from the mutually recursive printed equations;
it does not replace the source's attainment presupposition by a theorem. The
dominated-tail form is `infiniteValue_eq_of_dominated`. -/
public theorem infiniteValue_eq [Nonempty Action] {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs) :
    infiniteValue ρ ag t h = ag.horizon t h.length * ag.utility h +
      ⨆ a, infiniteActionValue ρ ag t h a :=
  infiniteValue_eq_of_dominated hρ ag (b := fun _ ↦ 1) hu t (by simpa using hw) h

/-- **Equation (2) at depth `n` converges to equation (2) at the infinite-horizon
value under a dominated tail** (Ring and Orseau, AGI 2011, §2, eq. (2)): a
per-length utility bound `b` with `Summable (|w t ·| * b)`. -/
public theorem tendsto_actionValue_infiniteActionValue_of_dominated [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (h : History Action Obs) (a : Action) :
    Filter.Tendsto (fun n ↦ actionValue ρ ag t n h a) Filter.atTop
      (nhds (infiniteActionValue ρ ag t h a)) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ ↦ dist_nonneg) (fun n ↦ ?_)
    ((tendsto_sum_nat_add (fun k ↦ |ag.horizon t k| * max (b k) 0)).comp
      (Filter.tendsto_add_atTop_nat (h.length + 2)))
  simp only [Function.comp_apply, Real.dist_eq]
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    actionValue_error_le_tail_of_dominated hρ ag (b := fun k ↦ max (b k) 0)
      (fun _ ↦ le_max_right _ _) (fun h ↦ (hub h).trans (le_max_left _ _)) t
      (summable_mul_max_zero hw) n h a

/-- **Equation (2) at depth `n` converges to equation (2) at the infinite-horizon
value** (Ring and Orseau, AGI 2011, §2, eq. (2); Orseau and Ring, AGI 2011, §2,
eq. (2)), at `Belief.IsSubprobability`, `|u| ≤ 1` and an absolutely summable
horizon. This is what carries a comparison of two depth-`n` action values that
holds at every depth to print's untruncated values. -/
public theorem tendsto_actionValue_infiniteActionValue [Nonempty Action]
    {ρ : Belief Action Obs} (hρ : ρ.IsSubprobability) (ag : Agent Action Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|))
    (h : History Action Obs) (a : Action) :
    Filter.Tendsto (fun n ↦ actionValue ρ ag t n h a) Filter.atTop
      (nhds (infiniteActionValue ρ ag t h a)) :=
  tendsto_actionValue_infiniteActionValue_of_dominated hρ ag (b := fun _ ↦ 1) hu t
    (by simpa using hw) h a

/-- A subprobability that puts weight one on an observation puts weight zero on
every other: the conditional is the point mass there. -/
public theorem Belief.IsSubprobability.cond_eq_zero_of_eq_one {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) {h : History Action Obs} {a : Action} {k o : Obs}
    (hk : ρ.cond h a k = 1) (ho : o ≠ k) : ρ.cond h a o = 0 := by
  classical
  have hle := (hρ.summable h a).sum_le_tsum ({k, o} : Finset Obs)
    (fun i _ ↦ hρ.nonneg h a i)
  rw [Finset.sum_pair (Ne.symm ho), hk] at hle
  linarith [hρ.total_le_one h a, hρ.nonneg h a o]

/-- A subprobability's conditional weight on one observation is at most one. -/
public theorem Belief.IsSubprobability.cond_le_one {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (h : History Action Obs) (a : Action) (o : Obs) :
    ρ.cond h a o ≤ 1 :=
  ((hρ.summable h a).le_tsum o (fun i _ => hρ.nonneg h a i)).trans (hρ.total_le_one h a)

/-!
### Equation (1) at the infinite-horizon value

Ring and Orseau, AGI 2011, §2, eq. (1): a_{t_h} := argmax over a ∈ 𝒜 of v_{t_h}(ha),
with `v` from the recursion (2)–(3), which has no terminal condition. The
depth-`n` `bestAction` maximises the truncated `actionValue`; the declarations
below maximise `infiniteActionValue`, whose link to print's recursion is
`infiniteValue_eq`.

**Scope.** The argmax itself needs no hypothesis beyond the attainment print
presupposes. Its identification with print's recursion (3), in
`infiniteValue_eq_infiniteBestAction_of_dominated`, is at
`Belief.IsSubprobability` and a dominated tail: a per-length utility bound
`|u h| ≤ b |h|` with `Summable (|w t ·| * b)`; `infiniteValue_eq_infiniteBestAction`
is its case `b ≡ 1` (`|u| ≤ 1`, `Summable |w t ·|`). Print's `v_t` is a real
number only where the weighted utility series converges, so the convergence
condition is where (3) denotes; weighted utility series that converge only
conditionally (signed weights) are outside this identification and are not
claimed.
-/

/-- The attainment equation (1) presupposes, at the infinite-horizon value:
some action maximises `infiniteActionValue`. -/
@[expose] public def InfAttains (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (t : ℕ) (h : History Action Obs) : Prop :=
  ∃ a : Action, ∀ b : Action, infiniteActionValue ρ ag t h b ≤ infiniteActionValue ρ ag t h a

/-- A finite action set attains the infinite-horizon maximum. -/
public theorem infAttains_of_fintype [Fintype Action] [Nonempty Action]
    (ρ : Belief Action Obs) (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs) :
    InfAttains ρ ag t h := by
  obtain ⟨a, -, ha⟩ :=
    (Finset.univ : Finset Action).exists_mem_eq_sup' Finset.univ_nonempty
      (infiniteActionValue ρ ag t h)
  exact ⟨a, fun b => ha ▸ Finset.le_sup' _ (Finset.mem_univ b)⟩

/-- Equation (1) at the infinite-horizon value (Ring and Orseau, AGI 2011, §2):
an action attaining the maximum of `infiniteActionValue`. A new definition beside
the depth-`n` `bestAction`, which is unchanged. -/
@[expose] public noncomputable def infiniteBestAction (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs)
    (hat : InfAttains ρ ag t h) : Action := hat.choose

/-- The infinite-horizon best action is maximal. -/
public theorem infiniteBestAction_max (ρ : Belief Action Obs) (ag : Agent Action Obs)
    (t : ℕ) (h : History Action Obs) (hat : InfAttains ρ ag t h) (a : Action) :
    infiniteActionValue ρ ag t h a ≤
      infiniteActionValue ρ ag t h (infiniteBestAction ρ ag t h hat) :=
  hat.choose_spec a

/-- **Print's recursion (3) with its max attained at equation (1)'s argmax, under a
dominated tail** (Ring and Orseau, AGI 2011, §2, eqs. (1) and (3); the Setting
states no summability condition on `w`): a per-length utility bound
`|u h| ≤ b |h|` with `Summable (|w t ·| * b)`. At `b ≡ 1` this is
`infiniteValue_eq_infiniteBestAction`. -/
public theorem infiniteValue_eq_infiniteBestAction_of_dominated {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) {b : ℕ → ℝ}
    (hub : ∀ h, |ag.utility h| ≤ b h.length) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k| * b k)) (h : History Action Obs)
    (hat : InfAttains ρ ag t h) :
    infiniteValue ρ ag t h = ag.horizon t h.length * ag.utility h +
      infiniteActionValue ρ ag t h (infiniteBestAction ρ ag t h hat) := by
  have : Nonempty Action := ⟨hat.choose⟩
  have hmax := infiniteBestAction_max ρ ag t h hat
  rw [infiniteValue_eq_of_dominated hρ ag hub t hw h,
    (ciSup_le hmax).antisymm (le_ciSup ⟨_, Set.forall_mem_range.2 hmax⟩ _)]

/-- **Print's recursion (3) with its max attained at equation (1)'s argmax.** At
print's probability, bounded utility and an absolutely summable horizon, the
infinite value is the current weighted utility plus the action value of the
infinite-horizon best action. -/
public theorem infiniteValue_eq_infiniteBestAction {ρ : Belief Action Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent Action Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (t : ℕ) (hw : Summable (fun k ↦ |ag.horizon t k|)) (h : History Action Obs)
    (hat : InfAttains ρ ag t h) :
    infiniteValue ρ ag t h = ag.horizon t h.length * ag.utility h +
      infiniteActionValue ρ ag t h (infiniteBestAction ρ ag t h hat) :=
  infiniteValue_eq_infiniteBestAction_of_dominated hρ ag (b := fun _ ↦ 1) hu t
    (by simpa using hw) h hat

/-- Equation (1) at the infinite-horizon value with footnote 4's lexicographic
tie rule: the least maximiser in a well-founded linear order on the actions
(see `lexArgmax` for the reading of "lexicographically"). -/
@[expose] public noncomputable def infiniteLexBestAction [LinearOrder Action]
    [WellFoundedLT Action] (ρ : Belief Action Obs) (ag : Agent Action Obs) (t : ℕ)
    (h : History Action Obs) (hat : InfAttains ρ ag t h) : Action :=
  lexArgmax (infiniteActionValue ρ ag t h) hat

/-- The lexicographic infinite-horizon best action is maximal. -/
public theorem infiniteLexBestAction_max [LinearOrder Action] [WellFoundedLT Action]
    (ρ : Belief Action Obs) (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs)
    (hat : InfAttains ρ ag t h) (a : Action) :
    infiniteActionValue ρ ag t h a ≤
      infiniteActionValue ρ ag t h (infiniteLexBestAction ρ ag t h hat) :=
  lexArgmax_max _ hat a

/-- The lexicographic infinite-horizon best action is the least maximiser. -/
public theorem infiniteLexBestAction_le [LinearOrder Action] [WellFoundedLT Action]
    (ρ : Belief Action Obs) (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs)
    (hat : InfAttains ρ ag t h) {a : Action}
    (ha : ∀ b, infiniteActionValue ρ ag t h b ≤ infiniteActionValue ρ ag t h a) :
    infiniteLexBestAction ρ ag t h hat ≤ a :=
  lexArgmax_le _ hat ha

/-- Where print's lexicographic tie rule denotes at the infinite-horizon value
(Ring and Orseau, AGI 2011, footnote 4; Orseau and Ring, AGI 2011, footnote 5):
the maximisers of `infiniteActionValue` have a least element in the order on the
actions. It implies `InfAttains`; under `[WellFoundedLT Action]` it follows from
`InfAttains` (`infLexAttains_of_infAttains`). -/
@[expose] public def InfLexAttains [PartialOrder Action] (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs) : Prop :=
  ∃ a : Action, IsLeast
    {a | ∀ b : Action, infiniteActionValue ρ ag t h b ≤ infiniteActionValue ρ ag t h a} a

/-- A least maximiser is a maximiser. -/
public theorem InfLexAttains.infAttains [PartialOrder Action] {ρ : Belief Action Obs}
    {ag : Agent Action Obs} {t : ℕ} {h : History Action Obs} (hl : InfLexAttains ρ ag t h) :
    InfAttains ρ ag t h :=
  ⟨hl.choose, hl.choose_spec.1⟩

/-- In a well-founded linear order, attainment gives a least maximiser. -/
public theorem infLexAttains_of_infAttains [LinearOrder Action] [WellFoundedLT Action]
    {ρ : Belief Action Obs} {ag : Agent Action Obs} {t : ℕ} {h : History Action Obs}
    (hat : InfAttains ρ ag t h) : InfLexAttains ρ ag t h :=
  exists_isLeast_maximizers _ hat

/-- Equation (1) at the infinite-horizon value with print's lexicographic tie rule,
wherever the rule denotes (Ring and Orseau, AGI 2011, eq. (1) and footnote 4): the
least maximiser of `infiniteActionValue`, with no well-foundedness of the order on
the actions and no finiteness of the action set. -/
@[expose] public noncomputable def infiniteLexBestActionOfLeast [PartialOrder Action]
    (ρ : Belief Action Obs) (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs)
    (hl : InfLexAttains ρ ag t h) : Action :=
  lexArgmaxOfLeast (infiniteActionValue ρ ag t h) hl

/-- The least-maximiser infinite-horizon best action is maximal. -/
public theorem infiniteLexBestActionOfLeast_max [PartialOrder Action] (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs) (hl : InfLexAttains ρ ag t h)
    (a : Action) :
    infiniteActionValue ρ ag t h a ≤
      infiniteActionValue ρ ag t h (infiniteLexBestActionOfLeast ρ ag t h hl) :=
  lexArgmaxOfLeast_max _ hl a

/-- The least-maximiser infinite-horizon best action is below every maximiser. -/
public theorem infiniteLexBestActionOfLeast_le [PartialOrder Action] (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs) (hl : InfLexAttains ρ ag t h)
    {a : Action} (ha : ∀ b, infiniteActionValue ρ ag t h b ≤ infiniteActionValue ρ ag t h a) :
    infiniteLexBestActionOfLeast ρ ag t h hl ≤ a :=
  lexArgmaxOfLeast_le _ hl ha

/-- Under a well-founded order it is `infiniteLexBestAction`. -/
public theorem infiniteLexBestActionOfLeast_eq [LinearOrder Action] [WellFoundedLT Action]
    (ρ : Belief Action Obs) (ag : Agent Action Obs) (t : ℕ) (h : History Action Obs)
    (hl : InfLexAttains ρ ag t h) (hat : InfAttains ρ ag t h) :
    infiniteLexBestActionOfLeast ρ ag t h hl = infiniteLexBestAction ρ ag t h hat :=
  lexArgmaxOfLeast_eq_lexArgmax _ hat hl

/-! ### Exact truncation at a horizon of finite support

Ring and Orseau's recursion (3) has no terminal condition (source card S11), and
`infiniteValue` is the limit of the depth-n values. When the horizon weight is
zero from some index on, as for the window horizon of print's reinforcement-learning
and prediction agents, that limit is attained at a finite depth: `truncation_exact`
makes the depth-n values constant once the recursion reaches past the support.
No summability, probability or utility condition is needed.
-/

/-- **The infinite value is a finite-depth value once the horizon has vanished**
(Ring and Orseau, AGI 2011, §2, eq. (3)): if the horizon weight at time t is zero
at every index from K on, the infinite-horizon value at h is the depth-N value
for every depth with K ≤ |h| + N. -/
public theorem infiniteValue_eq_value_of_horizon_vanishes (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t K : ℕ) (hzero : ∀ k, K ≤ k → ag.horizon t k = 0)
    (h : History Action Obs) {N : ℕ} (hN : K ≤ h.length + N) :
    infiniteValue ρ ag t h = value ρ ag t N h := by
  have hconst : ∀ n, N ≤ n → value ρ ag t n h = value ρ ag t N h := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => rfl
    | succ n hn ih =>
      rw [← ih]
      exact (truncation_exact ρ ag t n h (fun k hk => hzero k (by omega))).symm
  exact (tendsto_atTop_of_eventually_const hconst).limUnder_eq

/-- **Equation (2) at the infinite-horizon value is equation (2) at a finite depth
once the horizon has vanished** (Ring and Orseau, AGI 2011, §2, eq. (2)): every
extension h ++ [(a, o)] has length |h| + 1, so one depth N with
K ≤ |h| + 1 + N serves every observation. -/
public theorem infiniteActionValue_eq_actionValue_of_horizon_vanishes (ρ : Belief Action Obs)
    (ag : Agent Action Obs) (t K : ℕ) (hzero : ∀ k, K ≤ k → ag.horizon t k = 0)
    (h : History Action Obs) {N : ℕ} (hN : K ≤ h.length + 1 + N) (a : Action) :
    infiniteActionValue ρ ag t h a = actionValue ρ ag t N h a := by
  unfold infiniteActionValue actionValue
  refine tsum_congr fun o => ?_
  rw [infiniteValue_eq_value_of_horizon_vanishes ρ ag t K hzero (h ++ [(a, o)]) (N := N)
    (by simpa using hN)]

end AISafetyAtlas.Wireheading.AgentEquations
