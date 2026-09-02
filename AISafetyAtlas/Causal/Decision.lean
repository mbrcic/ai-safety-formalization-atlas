module

public import AISafetyAtlas.Causal.MarginClass
public import Mathlib.Algebra.Order.GroupWithZero.Finset
public import Mathlib.Order.Bounds.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Finite unmediated decision tasks

This is the Assumption 1 projection of a finite single-decision CID. The chance
joint is independent of the decision, a policy is a distribution on an arbitrary
finite decision alphabet conditional on visible chance variables, and value is
the resulting expected utility.

## Grounding and non-claims

* `Policy`, `value`, `regret` and the query packaging carry the value field `𝕜` as a
  parameter, so probability mixtures are the RE24 Definition-3 simplex over whichever
  field a statement picks, and the printed real case is an instance rather than an
  extrapolation.
* Policies and expected utility are the unmediated projection of RE24 Section
  2.2. RE24 Definition 4 and Everitt et al. 2021 Definition 4 are mediated CIDs,
  so they motivate this projection but are not its literal definition.
* `HasRegretAtMost` is the regret inequality used in the A2 query model and the
  RE24 main text. RE24 Definition 5 packages the policy oracle, not this inequality.
  Zero-regret fibrewise optimality is proved below; it is not stored in the definition.
* `gap`, `signPolicy`, and `value_const_sub` are binary-decision corollaries.
  Appendix B equation (3) is one hard-intervention instance, not their definition.
* `InIdentifiedSet`, `modelError`, and `IsRadius` remain A2 query packaging.
  They are related to RE24 Theorem 2, but are not its recovered `G' ⊆ G` or
  its function `γ(δ)`.
* Decision and utility are not DAG vertices here. Mediated tasks require a full
  CID layer and are outside this handoff.
-/

namespace AISafetyAtlas.Causal

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {dim : C → ℕ}
variable {Decision : Type*} [Fintype Decision] [DecidableEq Decision]
variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

public theorem Model.jointProbMix_nonneg (M : Model C dim 𝕜) (w : ProbMixture C dim 𝕜)
    (v : Assignment C dim) : 0 ≤ M.jointProbMix w.1 v := by
  unfold Model.jointProbMix
  exact Finset.sum_nonneg fun σ _ ↦ mul_nonneg (w.2.1 σ) (M.jointProb_nonneg σ v)

public theorem Model.jointProbMix_sum (M : Model C dim 𝕜) (w : ProbMixture C dim 𝕜) :
    ∑ v : Assignment C dim, M.jointProbMix w.1 v = 1 := by
  unfold Model.jointProbMix
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, M.jointProb_sum, mul_one]
  simpa using w.2.2

/-! ## Policies -/

/-- A stochastic decision rule on a finite decision alphabet. -/
public structure Policy {C : Type*} [Fintype C] [DecidableEq C]
    {dim : C → ℕ} (visible : Finset C) (Decision : Type*)
    [Fintype Decision] [DecidableEq Decision]
    (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] where
  /-- Conditional decision probabilities. -/
  prob : Assignment C dim → Decision → 𝕜
  /-- Policy probabilities are nonnegative. -/
  prob_nonneg : ∀ v d, 0 ≤ prob v d
  /-- Each conditional decision distribution sums to one. -/
  prob_sum : ∀ v, ∑ d : Decision, prob v d = 1
  /-- The policy reads only the visible variables. -/
  prob_parents :
    ∀ v w d, (∀ c ∈ visible, v c = w c) → prob v d = prob w d

/-- Two policies are equal when their probability kernels are equal. -/
@[ext] public theorem Policy.ext {visible : Finset C}
    {π π' : Policy (dim := dim) visible Decision 𝕜} (h : π.prob = π'.prob) : π = π' := by
  cases π
  cases π'
  cases h
  rfl

/-- The deterministic constant policy `do(D=d)`. -/
public def Policy.const (visible : Finset C) (d₀ : Decision) :
    Policy (dim := dim) visible Decision 𝕜 where
  prob := fun _ d ↦ if d = d₀ then 1 else 0
  prob_nonneg := by
    intro v d
    split_ifs <;> norm_num
  prob_sum := by
    intro v
    simp
  prob_parents := by
    intro v w d _
    rfl

/-- A canonical full assignment representing a visible fibre. -/
@[expose] public def fibreRep (M : Model C dim 𝕜) (visible : Finset C)
    (v : Assignment C dim) : Assignment C dim :=
  fun c ↦ if _h : c ∈ visible then v c else ⟨0, M.dim_pos c⟩

public theorem fibreRep_mem (M : Model C dim 𝕜) (visible : Finset C)
    (v : Assignment C dim) :
    ∀ c ∈ visible, fibreRep M visible v c = v c := by
  intro c hc
  simp [fibreRep, hc]

public theorem fibreRep_idem (M : Model C dim 𝕜) (visible : Finset C)
    (v : Assignment C dim) :
    fibreRep M visible (fibreRep M visible v) = fibreRep M visible v := by
  funext c
  by_cases hc : c ∈ visible <;> simp [fibreRep, hc]

namespace Model

/-- Expected utility contributed by one visible fibre if decision `d` is chosen. -/
@[expose] public def fibreScore (M : Model C dim 𝕜) (sk : Skeleton C dim Decision 𝕜)
    (visible : Finset C) (w : ProbMixture C dim 𝕜) (r : Assignment C dim)
    (d : Decision) : 𝕜 :=
  ∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
    ∀ c ∈ visible, v c = r c), M.jointProbMix w.1 v * sk.utility d v

/-- Value, written once per visible fibre. -/
@[expose] public def value (M : Model C dim 𝕜) (sk : Skeleton C dim Decision 𝕜)
    (visible : Finset C) (π : Policy (dim := dim) visible Decision 𝕜)
    (w : ProbMixture C dim 𝕜) : 𝕜 :=
  ∑ r ∈ Finset.univ.image (fibreRep M visible),
    ∑ d : Decision, π.prob r d * M.fibreScore sk visible w r d

/-- The fibre expression equals the direct unmediated expectation. -/
public theorem value_eq (M : Model C dim 𝕜) (sk : Skeleton C dim Decision 𝕜)
    (visible : Finset C) (π : Policy (dim := dim) visible Decision 𝕜)
    (w : ProbMixture C dim 𝕜) :
    M.value sk visible π w =
      ∑ v : Assignment C dim, M.jointProbMix w.1 v *
        ∑ d : Decision, π.prob v d * sk.utility d v := by
  classical
  unfold value fibreScore
  have hfiber :=
    (Finset.sum_fiberwise (s := (Finset.univ : Finset (Assignment C dim)))
      (fibreRep M visible)
      (fun v ↦ M.jointProbMix w.1 v *
        ∑ d : Decision, π.prob v d * sk.utility d v)).symm
  rw [hfiber]
  symm
  set inner : Assignment C dim → 𝕜 := fun r ↦
    ∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
      fibreRep M visible v = r),
      M.jointProbMix w.1 v * ∑ d : Decision, π.prob v d * sk.utility d v
  have hzero : ∀ r : Assignment C dim,
      r ∉ Finset.univ.image (fibreRep M visible) → inner r = 0 := by
    intro r hr
    have hempty :
        Finset.univ.filter (fun v : Assignment C dim ↦ fibreRep M visible v = r) = ∅ := by
      ext v
      constructor
      · intro hv
        exact (hr (Finset.mem_image.mpr ⟨v, Finset.mem_univ v,
          (Finset.mem_filter.mp hv).2⟩)).elim
      · intro hv
        exact (Finset.notMem_empty v hv).elim
    simp [inner, hempty]
  trans ∑ r ∈ Finset.univ.image (fibreRep M visible), inner r
  · exact (Finset.sum_subset (Finset.subset_univ _)
      (fun r _ hr ↦ hzero r hr)).symm
  apply Finset.sum_congr rfl
  intro r hr
  simp only [inner]
  have hfilter :
      Finset.univ.filter (fun v : Assignment C dim ↦ fibreRep M visible v = r) =
        Finset.univ.filter (fun v : Assignment C dim ↦ ∀ c ∈ visible, v c = r c) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hrep c hc
      have := congrArg (fun f : Assignment C dim ↦ f c) hrep
      simpa [fibreRep, hc] using this
    · intro hag
      rcases Finset.mem_image.mp hr with ⟨u, -, hu⟩
      have hr_fixed : fibreRep M visible r = r := by
        rw [← hu, fibreRep_idem]
      funext c
      by_cases hc : c ∈ visible
      · simp [fibreRep, hc, hag c hc]
      · have hr0 := congrArg (fun f : Assignment C dim ↦ f c) hr_fixed
        simpa [fibreRep, hc] using hr0
  rw [hfilter]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro v hv
  have hag : ∀ c ∈ visible, v c = r c := by
    exact (Finset.mem_filter.mp hv).2
  have hπ : π.prob r d = π.prob v d :=
    (π.prob_parents v r d hag).symm
  rw [hπ]
  ring

/-- Masking is constant on visible-fibre representatives. -/
public theorem Δmask_fibreRep (M : Model C dim 𝕜) (gap : Assignment C dim → 𝕜)
    (visible : Finset C) (v : Assignment C dim) (mix : ProbMixture C dim 𝕜) :
    M.Δmask gap visible (fibreRep M visible v) mix = M.Δmask gap visible v mix := by
  unfold Model.Δmask
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hu c hc
    simpa [fibreRep, hc] using hu c hc
  · intro hu c hc
    simpa [fibreRep, hc] using hu c hc

/-! ## Fibrewise optimum -/

public noncomputable def bestDecision [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C) (w : ProbMixture C dim 𝕜)
    (r : Assignment C dim) : Decision :=
  Classical.choose
    (Finset.exists_max_image Finset.univ (M.fibreScore sk visible w r)
      Finset.univ_nonempty)

omit [DecidableEq Decision] in
public theorem fibreScore_le_best [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C) (w : ProbMixture C dim 𝕜)
    (r : Assignment C dim) (d : Decision) :
    M.fibreScore sk visible w r d ≤
      M.fibreScore sk visible w r (M.bestDecision sk visible w r) := by
  exact (Classical.choose_spec
    (Finset.exists_max_image Finset.univ (M.fibreScore sk visible w r)
      Finset.univ_nonempty)).2 d (Finset.mem_univ d)

/-- A deterministic policy choosing a fibrewise maximizer. -/
public noncomputable def bestPolicy [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C) (w : ProbMixture C dim 𝕜) :
    Policy (dim := dim) visible Decision 𝕜 where
  prob := fun v d ↦
    if d = M.bestDecision sk visible w (fibreRep M visible v) then 1 else 0
  prob_nonneg := by
    intro v d
    split_ifs <;> norm_num
  prob_sum := by
    intro v
    simp
  prob_parents := by
    intro v v' d h
    have hrep : fibreRep M visible v = fibreRep M visible v' := by
      funext c
      by_cases hc : c ∈ visible
      · simp [fibreRep, hc, h c hc]
      · simp [fibreRep, hc]
    rw [hrep]

@[expose] public noncomputable def optimalValue [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C) (w : ProbMixture C dim 𝕜) : 𝕜 :=
  ∑ r ∈ Finset.univ.image (fibreRep M visible),
    M.fibreScore sk visible w r (M.bestDecision sk visible w r)

public theorem value_bestPolicy [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C) (w : ProbMixture C dim 𝕜) :
    M.value sk visible (M.bestPolicy sk visible w) w = M.optimalValue sk visible w := by
  classical
  unfold value optimalValue
  apply Finset.sum_congr rfl
  intro r hr
  have hr_fixed : fibreRep M visible r = r := by
    rcases Finset.mem_image.mp hr with ⟨v, -, hv⟩
    rw [← hv, fibreRep_idem]
  simp [bestPolicy, hr_fixed]

@[expose] public noncomputable def regret [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) : 𝕜 :=
  M.optimalValue sk visible w - M.value sk visible π w

@[expose] public noncomputable def IsOptimal [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) : Prop :=
  M.regret sk visible π w = 0

/-- The regret inequality used by the A2 query model and the RE24 main text. -/
@[expose] public noncomputable def HasRegretAtMost [Nonempty Decision]
    (M : Model C dim 𝕜) (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) (δ : 𝕜) : Prop :=
  M.regret sk visible π w ≤ δ

public theorem regret_decomp [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) :
    M.regret sk visible π w =
      ∑ r ∈ Finset.univ.image (fibreRep M visible),
        ∑ d : Decision, π.prob r d *
          (M.fibreScore sk visible w r (M.bestDecision sk visible w r) -
            M.fibreScore sk visible w r d) := by
  classical
  unfold regret optimalValue value
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro r hr
  calc
    M.fibreScore sk visible w r (M.bestDecision sk visible w r) -
        ∑ d : Decision, π.prob r d * M.fibreScore sk visible w r d =
      (∑ d : Decision, π.prob r d) *
          M.fibreScore sk visible w r (M.bestDecision sk visible w r) -
        ∑ d : Decision, π.prob r d * M.fibreScore sk visible w r d := by
      rw [π.prob_sum]
      ring
    _ = _ := by
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun d _ ↦ by ring

public theorem value_le_optimal [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) :
    M.value sk visible π w ≤ M.optimalValue sk visible w := by
  classical
  unfold value optimalValue
  apply Finset.sum_le_sum
  intro r hr
  calc
    ∑ d : Decision, π.prob r d * M.fibreScore sk visible w r d ≤
        ∑ d : Decision, π.prob r d *
          M.fibreScore sk visible w r (M.bestDecision sk visible w r) := by
      apply Finset.sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (M.fibreScore_le_best sk visible w r d)
        (π.prob_nonneg r d)
    _ = M.fibreScore sk visible w r (M.bestDecision sk visible w r) := by
      rw [← Finset.sum_mul, π.prob_sum]
      simp

public theorem regret_nonneg [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) :
    0 ≤ M.regret sk visible π w :=
  sub_nonneg.mpr (M.value_le_optimal sk visible π w)

public theorem isOptimal_iff_regret_zero [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) :
    M.IsOptimal sk visible π w ↔ M.regret sk visible π w = 0 := Iff.rfl

/-- Zero regret is exactly support on fibrewise maximizing decisions. Ties are
unconstrained: any mixture supported on the argmax set is allowed. -/
public theorem regret_eq_zero_iff [Nonempty Decision] (M : Model C dim 𝕜)
    (sk : Skeleton C dim Decision 𝕜) (visible : Finset C)
    (π : Policy (dim := dim) visible Decision 𝕜) (w : ProbMixture C dim 𝕜) :
    M.regret sk visible π w = 0 ↔
      ∀ r ∈ Finset.univ.image (fibreRep M visible), ∀ d,
        0 < π.prob r d →
          M.fibreScore sk visible w r d =
            M.fibreScore sk visible w r (M.bestDecision sk visible w r) := by
  classical
  rw [M.regret_decomp sk visible π w]
  constructor
  · intro h r hr d hp
    have houter := (Finset.sum_eq_zero_iff_of_nonneg fun r _ ↦
      Finset.sum_nonneg fun d _ ↦ mul_nonneg (π.prob_nonneg r d)
        (sub_nonneg.mpr (M.fibreScore_le_best sk visible w r d))).mp h r hr
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun d _ ↦
      mul_nonneg (π.prob_nonneg r d)
        (sub_nonneg.mpr (M.fibreScore_le_best sk visible w r d))).mp
          houter d (Finset.mem_univ d)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left (ne_of_gt hp)) |>.symm
  · intro h
    apply (Finset.sum_eq_zero_iff_of_nonneg fun r _ ↦
      Finset.sum_nonneg fun d _ ↦ mul_nonneg (π.prob_nonneg r d)
        (sub_nonneg.mpr (M.fibreScore_le_best sk visible w r d))).mpr
    intro r hr
    apply (Finset.sum_eq_zero_iff_of_nonneg fun d _ ↦
      mul_nonneg (π.prob_nonneg r d)
        (sub_nonneg.mpr (M.fibreScore_le_best sk visible w r d))).mpr
    intro d hd
    by_cases hp : 0 < π.prob r d
    · rw [h r hr d hp]
      ring
    · have hp0 : π.prob r d = 0 := le_antisymm (le_of_not_gt hp) (π.prob_nonneg r d)
      simp [hp0]

end Model

/-! ## Binary-decision corollaries -/

namespace Model

/-- The two binary fibre scores differ by exactly the masked gap transform.

This is the fibrewise form of MAIS-A2's decomposition `eq:decomp`, and it is what
makes the behavioral transform carry all behavioral information: anything read
off the *difference* of the two scores — a sign, a regret, a softmax response —
is a function of `Δmask` alone, so two models with equal transforms are
indistinguishable through any of them. -/
public theorem fibreScore_true_sub_false (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (w : ProbMixture C dim 𝕜) (r : Assignment C dim) :
    M.fibreScore sk visible w r true - M.fibreScore sk visible w r false =
      M.Δmask sk.gap visible r w := by
  unfold fibreScore Δmask Skeleton.gap
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ ↦ by ring

public def preferredDecision (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (w : ProbMixture C dim 𝕜) (v : Assignment C dim) : Bool :=
  decide (0 < M.Δmask sk.gap visible v w)

/-- The binary policy choosing `true` exactly when its fibre gap is positive. -/
@[expose] public def signPolicy (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (w : ProbMixture C dim 𝕜) :
    Policy (dim := dim) visible Bool 𝕜 where
  prob := fun v d ↦
    if d = M.preferredDecision sk visible w v then 1 else 0
  prob_nonneg := by
    intro v d
    split_ifs <;> norm_num
  prob_sum := by
    intro v
    rw [Fintype.sum_bool]
    cases M.preferredDecision sk visible w v <;> simp
  prob_parents := by
    intro v v' d h
    have hfilter :
        Finset.univ.filter (fun u : Assignment C dim ↦ ∀ c ∈ visible, u c = v c) =
          Finset.univ.filter (fun u : Assignment C dim ↦ ∀ c ∈ visible, u c = v' c) := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro hu c hc
        exact (hu c hc).trans (h c hc)
      · intro hu c hc
        exact (hu c hc).trans (h c hc).symm
    have hmask : M.Δmask sk.gap visible v w = M.Δmask sk.gap visible v' w := by
      unfold Model.Δmask
      rw [hfilter]
    have hpref : M.preferredDecision sk visible w v =
        M.preferredDecision sk visible w v' := by
      unfold preferredDecision
      rw [hmask]
    rw [hpref]

private theorem coeff_le_sign (gap p : 𝕜) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    p * gap ≤ (if 0 < gap then (1 : 𝕜) else 0) * gap := by
  by_cases hgap : 0 < gap
  · simp only [if_pos hgap, one_mul]
    exact mul_le_of_le_one_left (le_of_lt hgap) hp1
  · simp only [if_neg hgap, zero_mul]
    exact mul_nonpos_of_nonneg_of_nonpos hp0 (le_of_not_gt hgap)

/-- Every binary policy is bounded by the fibrewise sign policy. -/
public theorem value_le_sign (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (π : Policy (dim := dim) visible Bool 𝕜)
    (w : ProbMixture C dim 𝕜) :
    M.value sk visible π w ≤ M.value sk visible (M.signPolicy sk visible w) w := by
  classical
  unfold value
  apply Finset.sum_le_sum
  intro r hr
  rw [Fintype.sum_bool, Fintype.sum_bool]
  have hsum := π.prob_sum r
  rw [Fintype.sum_bool] at hsum
  have hp0 := π.prob_nonneg r true
  have hp1 : π.prob r true ≤ 1 := by linarith [π.prob_nonneg r false]
  have hcoeff := coeff_le_sign
    (M.fibreScore sk visible w r true - M.fibreScore sk visible w r false)
    (π.prob r true) hp0 hp1
  rw [M.fibreScore_true_sub_false sk visible w r] at hcoeff
  have hpfalse : π.prob r false = 1 - π.prob r true := by
    linarith
  have hvalue :
      π.prob r true * M.fibreScore sk visible w r true +
          π.prob r false * M.fibreScore sk visible w r false =
        M.fibreScore sk visible w r false + π.prob r true *
          (M.fibreScore sk visible w r true - M.fibreScore sk visible w r false) := by
    rw [hpfalse]
    ring
  by_cases hgap : 0 < M.Δmask sk.gap visible r w
  · have ht : (M.signPolicy sk visible w).prob r true = 1 := by
      simp [signPolicy, preferredDecision, hgap]
    have hf : (M.signPolicy sk visible w).prob r false = 0 := by
      simp [signPolicy, preferredDecision, hgap]
    rw [ht, hf]
    simp only [one_mul, zero_mul, add_zero]
    rw [hvalue]
    have hdiff := M.fibreScore_true_sub_false sk visible w r
    simp only [if_pos hgap] at hcoeff
    rw [← hdiff] at hcoeff
    linarith
  · have ht : (M.signPolicy sk visible w).prob r true = 0 := by
      simp [signPolicy, preferredDecision, hgap]
    have hf : (M.signPolicy sk visible w).prob r false = 1 := by
      simp [signPolicy, preferredDecision, hgap]
    rw [ht, hf]
    simp only [zero_mul, one_mul, zero_add]
    rw [hvalue]
    have hdiff := M.fibreScore_true_sub_false sk visible w r
    simp only [if_neg hgap] at hcoeff
    rw [← hdiff] at hcoeff
    linarith

/-- The fibrewise sign policy is optimal, hence has zero regret. -/
public theorem regret_signPolicy_eq_zero (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (w : ProbMixture C dim 𝕜) :
    M.regret sk visible (M.signPolicy sk visible w) w = 0 := by
  have hupper := M.value_le_optimal sk visible (M.signPolicy sk visible w) w
  have hlower := M.value_le_sign sk visible (M.bestPolicy sk visible w) w
  rw [M.value_bestPolicy] at hlower
  unfold regret
  rw [sub_eq_zero]
  exact le_antisymm hlower hupper

/-- Equal utility-gap transforms produce the same canonical optimal policy. -/
public theorem signPolicy_eq_of_behaviorEq (sk : Skeleton C dim Bool 𝕜)
    {M M' : Model C dim 𝕜} (hEq : sk.BehaviorEq M M')
    (visible : Finset C) (hvisible : visible ⊆ sk.observed) (w : ProbMixture C dim 𝕜) :
    M.signPolicy sk visible w = M'.signPolicy sk visible w := by
  apply Policy.ext
  funext v d
  have hmask := hEq visible hvisible v w
  -- `simp` rewrites both sides to the same term but no longer closes on it.
  simp [signPolicy, preferredDecision, hmask]
  rfl

/-- The constant-policy difference is the general utility-gap transform. -/
public theorem value_const_sub (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (w : ProbMixture C dim 𝕜) :
    M.value sk visible (Policy.const visible true) w -
      M.value sk visible (Policy.const visible false) w = M.Δmix sk.gap w.1 := by
  rw [M.value_eq, M.value_eq]
  simp only [Policy.const, Fintype.sum_bool]
  simp
  unfold Model.Δmix Skeleton.gap
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun v _ ↦ by ring

/-- Positive binary fibre gap forces every zero-regret policy to choose `true`. -/
public theorem prob_true_eq_one_of_gap_pos (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (π : Policy (dim := dim) visible Bool 𝕜)
    (w : ProbMixture C dim 𝕜) (r : Assignment C dim)
    (hr : r ∈ Finset.univ.image (fibreRep M visible))
    (hgap : 0 < M.Δmask sk.gap visible r w)
    (hregret : M.regret sk visible π w = 0) : π.prob r true = 1 := by
  have hsupport := (M.regret_eq_zero_iff sk visible π w).mp hregret
  have hfalse : π.prob r false = 0 := by
    apply le_antisymm
    · apply le_of_not_gt
      intro hp
      have heq := hsupport r hr false hp
      have hbest := M.fibreScore_le_best sk visible w r true
      have hdiff := M.fibreScore_true_sub_false sk visible w r
      rw [← heq] at hbest
      linarith
    · exact π.prob_nonneg r false
  have hsum := π.prob_sum r
  rw [Fintype.sum_bool, hfalse] at hsum
  linarith

/-- Negative binary fibre gap forces every zero-regret policy to choose `false`. -/
public theorem prob_true_eq_zero_of_gap_neg (M : Model C dim 𝕜) (sk : Skeleton C dim Bool 𝕜)
    (visible : Finset C) (π : Policy (dim := dim) visible Bool 𝕜)
    (w : ProbMixture C dim 𝕜) (r : Assignment C dim)
    (hr : r ∈ Finset.univ.image (fibreRep M visible))
    (hgap : M.Δmask sk.gap visible r w < 0)
    (hregret : M.regret sk visible π w = 0) : π.prob r true = 0 := by
  apply le_antisymm
  · apply le_of_not_gt
    intro hp
    have hsupport := (M.regret_eq_zero_iff sk visible π w).mp hregret
    have heq := hsupport r hr true hp
    have hbest := M.fibreScore_le_best sk visible w r false
    have hdiff := M.fibreScore_true_sub_false sk visible w r
    rw [← heq] at hbest
    linarith
  · exact π.prob_nonneg r true

end Model

/-! ## A2 identified-set packaging -/

public abbrev PolicyFamily (sk : Skeleton C dim Bool 𝕜) :=
  ∀ (visible : Finset C), visible ⊆ sk.observed →
    ProbMixture C dim 𝕜 → Policy (dim := dim) visible Bool 𝕜

@[expose] public noncomputable def AdmissibleFamily (M : Model C dim 𝕜)
    (sk : Skeleton C dim Bool 𝕜) (δ : 𝕜) (family : PolicyFamily sk) : Prop :=
  ∀ (visible : Finset C) (hvisible : visible ⊆ sk.observed) (w : ProbMixture C dim 𝕜),
    M.HasRegretAtMost sk visible (family visible hvisible w) w δ

@[expose] public noncomputable def InIdentifiedSet (sk : Skeleton C dim Bool 𝕜)
    (lam δ : 𝕜) (M M' : Model C dim 𝕜) : Prop :=
  sk.MarginClass M lam ∧ sk.MarginClass M' lam ∧
    ∃ family : PolicyFamily sk,
      AdmissibleFamily M sk δ family ∧ AdmissibleFamily M' sk δ family

/-- The identified set grows with the regret bound.

Admissibility is a `≤ δ` bound on every shifted task, so a family admissible at
`δ` is admissible at any larger bound. `subsec:queries` defines `I_δ(M)` for
`δ ≥ 0`, and this is the monotonicity that definition implies: a collision at
regret zero is a collision at every positive regret, which is what carries a
`δ = 0` indistinguishability construction into a statement about `φ(δ)` as
`δ → 0`. -/
public theorem inIdentifiedSet_mono {sk : Skeleton C dim Bool 𝕜} {lam δ δ' : 𝕜}
    (h : δ ≤ δ') {M M' : Model C dim 𝕜} (hId : InIdentifiedSet sk lam δ M M') :
    InIdentifiedSet sk lam δ' M M' := by
  obtain ⟨hM, hM', family, hA, hA'⟩ := hId
  exact ⟨hM, hM', family, fun v hv w => le_trans (hA v hv w) h,
    fun v hv w => le_trans (hA' v hv w) h⟩

/-- Equal transforms give both models one common zero-regret policy family.

This machine-checks the forward direction of the optimal-policy equivalence used
in MAIS A2. Reconstructing the numerical transform from an arbitrary optimal
policy oracle is the converse source proposition and remains outside this layer. -/
public theorem inIdentifiedSet_zero_of_behaviorEq (sk : Skeleton C dim Bool 𝕜)
    (lam : 𝕜) {M M' : Model C dim 𝕜} (hM : sk.MarginClass M lam)
    (hM' : sk.MarginClass M' lam) (hEq : sk.BehaviorEq M M') :
    InIdentifiedSet sk lam 0 M M' := by
  let family : PolicyFamily sk := fun visible _ w ↦ M.signPolicy sk visible w
  refine ⟨hM, hM', family, ?_, ?_⟩
  · intro visible hvisible w
    change M.regret sk visible (M.signPolicy sk visible w) w ≤ 0
    exact le_of_eq (M.regret_signPolicy_eq_zero sk visible w)
  · intro visible hvisible w
    change M'.regret sk visible (M.signPolicy sk visible w) w ≤ 0
    rw [M.signPolicy_eq_of_behaviorEq sk hEq visible hvisible w]
    exact le_of_eq (M'.regret_signPolicy_eq_zero sk visible w)

/-- The extension of the source's `δ ≥ 0` domain is empty at
negative tolerances, because regret is nonnegative. -/
public theorem not_inIdentifiedSet_of_neg (sk : Skeleton C dim Bool 𝕜)
    (lam δ : 𝕜) (M M' : Model C dim 𝕜) (hδ : δ < 0) :
    ¬InIdentifiedSet sk lam δ M M' := by
  intro h
  rcases h with ⟨_, _, family, hfamily, _⟩
  have hvisible : (∅ : Finset C) ⊆ sk.observed := Finset.empty_subset _
  let w : ProbMixture C dim 𝕜 := ProbMixture.dirac (fun _ ↦ identityIntervention)
  have hnonneg := M.regret_nonneg sk ∅ (family ∅ hvisible w) w
  have hupper := hfamily ∅ hvisible w
  change M.regret sk ∅ (family ∅ hvisible w) w ≤ δ at hupper
  linarith

public theorem not_inIdentifiedSet_of_opposite_sign (sk : Skeleton C dim Bool 𝕜)
    (lam : 𝕜) (M M' : Model C dim 𝕜) (visible : Finset C)
    (hvisible : visible ⊆ sk.observed) (w : ProbMixture C dim 𝕜) (v : Assignment C dim)
    (hpositive : 0 < M.Δmask sk.gap visible v w)
    (hnegative : M'.Δmask sk.gap visible v w < 0) :
    ¬InIdentifiedSet sk lam 0 M M' := by
  intro h
  rcases h with ⟨_, _, family, hfamily, hfamily'⟩
  let r := fibreRep M visible v
  have hr : r ∈ Finset.univ.image (fibreRep M visible) :=
    Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  have hpos_r : 0 < M.Δmask sk.gap visible r w := by
    simpa [r] using hpositive.trans_eq (M.Δmask_fibreRep sk.gap visible v w).symm
  have hrep : fibreRep M visible v = fibreRep M' visible v := by
    funext c
    by_cases hc : c ∈ visible <;> simp [fibreRep, hc]
  have hneg_r : M'.Δmask sk.gap visible r w < 0 := by
    unfold r
    rw [hrep, M'.Δmask_fibreRep]
    exact hnegative
  have hreg : M.regret sk visible (family visible hvisible w) w = 0 :=
    le_antisymm (hfamily visible hvisible w) (M.regret_nonneg sk visible _ w)
  have hreg' : M'.regret sk visible (family visible hvisible w) w = 0 :=
    le_antisymm (hfamily' visible hvisible w) (M'.regret_nonneg sk visible _ w)
  have hone := M.prob_true_eq_one_of_gap_pos sk visible _ w r hr hpos_r hreg
  have hr' : r ∈ Finset.univ.image (fibreRep M' visible) := by
    unfold r
    rw [hrep]
    exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
  have hzero := M'.prob_true_eq_zero_of_gap_neg sk visible _ w r hr' hneg_r hreg'
  linarith

public noncomputable def optimalPolicyFamily (M : Model C dim 𝕜)
    (sk : Skeleton C dim Bool 𝕜) : PolicyFamily sk :=
  fun visible _ w ↦ M.bestPolicy sk visible w

public theorem inIdentifiedSet_self (sk : Skeleton C dim Bool 𝕜) (lam δ : 𝕜)
    (M : Model C dim 𝕜) (hM : sk.MarginClass M lam) (hδ : 0 ≤ δ) :
    InIdentifiedSet sk lam δ M M := by
  refine ⟨hM, hM, optimalPolicyFamily M sk, ?_, ?_⟩
  all_goals
    intro visible hvisible w
    change M.regret sk visible (M.bestPolicy sk visible w) w ≤ δ
    unfold Model.regret
    rw [M.value_bestPolicy]
    simpa using hδ

public theorem inIdentifiedSet_symm (sk : Skeleton C dim Bool 𝕜) (lam δ : 𝕜)
    {M M' : Model C dim 𝕜} (h : InIdentifiedSet sk lam δ M M') :
    InIdentifiedSet sk lam δ M' M := by
  rcases h with ⟨hM, hM', family, hfamily, hfamily'⟩
  exact ⟨hM', hM, family, hfamily', hfamily⟩

/-! ## A2 model error and radius -/

@[expose] public noncomputable def cptError (M M' : Model C dim 𝕜) (c : C) : 𝕜 :=
  Finset.sup' Finset.univ
    ⟨(⟨0, M.dim_pos c⟩, fun i ↦ ⟨0, M.dim_pos i⟩), Finset.mem_univ _⟩
    fun av : Fin (dim c) × Assignment C dim ↦
      |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|

public theorem cptError_nonneg (M M' : Model C dim 𝕜) (c : C) :
    0 ≤ cptError M M' c := by
  classical
  unfold cptError
  let z : Fin (dim c) × Assignment C dim :=
    (⟨0, M.dim_pos c⟩, fun i ↦ ⟨0, M.dim_pos i⟩)
  calc
    0 ≤ |M.cpt c z.1 z.2 - M'.cpt c z.1 z.2| := abs_nonneg _
    _ ≤ Finset.sup' Finset.univ
        ⟨z, Finset.mem_univ z⟩
        (fun av : Fin (dim c) × Assignment C dim ↦
          |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|) :=
      Finset.le_sup'
        (fun av : Fin (dim c) × Assignment C dim ↦
          |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|)
        (Finset.mem_univ z)

@[expose] public noncomputable def modelError [Nonempty C] (M M' : Model C dim 𝕜) : 𝕜 :=
  if M.parents = M'.parents then
    Finset.sup' Finset.univ Finset.univ_nonempty (cptError M M')
  else 1

/-- Table entries lie in the unit interval, so their differences lie in `[-1, 1]`
and every `cptError` is at most `1`. -/
public theorem cptError_le_one (M M' : Model C dim 𝕜) (c : C) :
    cptError M M' c ≤ 1 := by
  classical
  refine Finset.sup'_le _ _ fun av _ ↦ ?_
  rw [abs_le]
  have h1 := M.cpt_nonneg c av.1 av.2
  have h2 := M.cpt_le_one c av.1 av.2
  have h3 := M'.cpt_nonneg c av.1 av.2
  have h4 := M'.cpt_le_one c av.1 av.2
  constructor <;> linarith

/-- The printed error is non-negative. On the graph branch it is `1`; on the
table branch it is a supremum of absolute values. -/
public theorem modelError_nonneg [Nonempty C] (M M' : Model C dim 𝕜) :
    0 ≤ modelError M M' := by
  classical
  unfold modelError
  by_cases hp : M.parents = M'.parents
  · rw [if_pos hp]
    exact le_trans (cptError_nonneg M M' (Classical.arbitrary C))
      (Finset.le_sup' _ (Finset.mem_univ _))
  · rw [if_neg hp]
    exact zero_le_one

/-- Two models with different graphs cannot both be well approximated by one
estimate: the printed error is `1` against whichever of them the estimate
disagrees with.

This is the two-point inequality a minimax lower bound runs on. `subsec:queries`
writes the error as *"`1` if `Ĝ ≠ G`"*, so an estimate has to pick a graph, and
picking one puts the full error `1` on the other model. -/
public theorem one_le_modelError_add [Nonempty C] {M M' : Model C dim 𝕜}
    (hpar : M.parents ≠ M'.parents) (N : Model C dim 𝕜) :
    1 ≤ modelError M N + modelError M' N := by
  classical
  by_cases h : M.parents = N.parents
  · have hne : M'.parents ≠ N.parents := fun hc ↦ hpar (h.trans hc.symm)
    have h1 : modelError M' N = 1 := by unfold modelError; rw [if_neg hne]
    have h0 := modelError_nonneg M N
    rw [h1]
    linarith
  · have h1 : modelError M N = 1 := by unfold modelError; rw [if_neg h]
    have h0 := modelError_nonneg M' N
    rw [h1]
    linarith

/-- The printed error is at most `1`, which is what makes it integrable against
any probability measure. Both branches are bounded by `1`: the graph branch is
`1` exactly, and the table branch is a supremum of differences of numbers in the
unit interval. -/
public theorem modelError_le_one [Nonempty C] (M M' : Model C dim 𝕜) :
    modelError M M' ≤ 1 := by
  classical
  unfold modelError
  by_cases hp : M.parents = M'.parents
  · rw [if_pos hp]
    exact Finset.sup'_le _ _ fun c _ ↦ cptError_le_one M M' c
  · rw [if_neg hp]

public theorem cptError_eq_zero_iff (M M' : Model C dim 𝕜) (c : C) :
    cptError M M' c = 0 ↔ ∀ a v, M.cpt c a v = M'.cpt c a v := by
  classical
  constructor
  · intro h a v
    have hle : |M.cpt c a v - M'.cpt c a v| ≤ cptError M M' c := by
      unfold cptError
      exact Finset.le_sup'
        (fun av : Fin (dim c) × Assignment C dim ↦
          |M.cpt c av.1 av.2 - M'.cpt c av.1 av.2|)
        (Finset.mem_univ (a, v))
    rw [h] at hle
    exact sub_eq_zero.mp (abs_eq_zero.mp (le_antisymm hle (abs_nonneg _)))
  · intro h
    apply le_antisymm
    · unfold cptError
      refine Finset.sup'_le _ _ ?_
      intro av hav
      simp [h av.1 av.2]
    · exact cptError_nonneg M M' c

public theorem modelError_eq_zero_iff [Nonempty C] (M M' : Model C dim 𝕜) :
    modelError M M' = 0 ↔ M = M' := by
  classical
  unfold modelError
  by_cases hp : M.parents = M'.parents
  · rw [if_pos hp]
    constructor
    · intro hmax
      have hc : ∀ c, cptError M M' c = 0 := by
        intro c
        apply le_antisymm
        · have hle := Finset.le_sup' (cptError M M') (Finset.mem_univ c)
          rw [hmax] at hle
          exact hle
        · exact cptError_nonneg M M' c
      apply Model.ext hp
      funext c a v
      exact (cptError_eq_zero_iff M M' c).mp (hc c) a v
    · intro h
      subst M'
      apply le_antisymm
      · refine Finset.sup'_le _ _ ?_
        intro c hc
        exact le_of_eq ((cptError_eq_zero_iff M M c).mpr fun a v ↦ rfl)
      · let c := Classical.choice (inferInstance : Nonempty C)
        have hc0 : 0 ≤ cptError M M c := by
          rw [(cptError_eq_zero_iff M M c).mpr fun a v ↦ rfl]
        exact hc0.trans (Finset.le_sup' _ (Finset.mem_univ c))
  · rw [if_neg hp]
    constructor
    · norm_num
    · intro h
      exact (hp (congrArg Model.parents h)).elim

@[expose] public def radiusErrors [Nonempty C] (sk : Skeleton C dim Bool 𝕜)
    (lam δ : 𝕜) : Set 𝕜 :=
  {e | ∃ M M' : Model C dim 𝕜, sk.MarginClass M lam ∧ InIdentifiedSet sk lam δ M M' ∧
    e = modelError M M'}

@[expose] public def IsRadius [Nonempty C] (sk : Skeleton C dim Bool 𝕜)
    (lam δ r : 𝕜) : Prop :=
  IsLUB (radiusErrors sk lam δ) r

end AISafetyAtlas.Causal
