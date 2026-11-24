module

public import AISafetyAtlas.Preference.Override
public import AISafetyAtlas.Preference.Reasonable
public import AISafetyAtlas.Wireheading.Corruption
public import AISafetyAtlas.Decision.DiscountedValue
public import AISafetyAtlas.Decision.BoundedValue

/-!
# The regret and override models at a finite discounted MDP

`AISafetyAtlas.Preference.Override` and `AISafetyAtlas.Preference.Regret` carry
values as structure fields. This module supplies them from Armstrong and
Mindermann's own setting (§3): an MDP with a discrete state space, a finite
action space, a probabilistic transition function and a fixed starting state,
deterministic Markov policies, and the value `V^π_R(ŝ)` of a policy, here the
discounted value `AISafetyAtlas.Decision.vPi` of a state-action reward. Three
results of the source become statements about that MDP.

* **§4.1.2's half-maximal bound** (`discounted_half_maximal_regret`): for any
  policy, the worst case over print's reward space `[-1, 1]^{𝒮×𝒜}` of its regret
  is at least half the joint worst case over policies and rewards. It holds on
  any nonempty state type, at the bounded value `vPiBdd`, by the sign-reward
  argument `half_maximal_regret_of_signReward`, which needs no finiteness and is
  shared with the episodic return (`AISafetyAtlas.Preference.Episodic`). On a
  finite state type it is also `ComplementedClass.everitt_theorem_eleven` at the
  class `discountedClass`, whose complement is negation of the reward.
* **Appendix B's augmented MDP** (`augmentMDP`): the state is doubled by a
  boolean that never changes; `vPi_augmentMDP` computes every value on the
  doubled MDP from the base MDP, copy by copy. With it, the agent's regret of
  overriding is print's `V*_Ṙ − V^{π^a}_Ṙ` (`augRegret_overriding`) and
  inaction has zero regret under an optimal human (`augRegret_noop`).
* **Equation (2)'s two halves** (`beliefValue_overriding`, `beliefValue_noop`):
  the expected value under the belief "`Ṙ` with probability `1 − ε`, the twisted
  `Ṙ^a` with probability `ε`" is computed, not named. On an arbitrary nonempty
  state type the same is `beliefValueBdd_overriding` and `beliefValueBdd_noop`,
  through the copy lemma `vPiBdd_augmentMDP`.

## Scope against print

* **States.** Print's state space is *discrete*. The half-maximal bound and
  equation (2) hold on any nonempty state type, at `vPiBdd`
  (`AISafetyAtlas.Decision.BoundedValue`), with bounded rewards (print's
  `[-1, 1]`, or any bound `C` for equation (2)). The override model
  `discountedOverride`, the augmented regret `augRegret` and `discountedClass`
  need finitely many states, which is what `vPi`'s fixed-point construction and
  the maxima over policies use.
* **`V*` as a maximum over policies.** Print writes `V*_R(s)` for the value of
  the optimal policy. On a finite state type `optValueAt` is the maximum over
  all deterministic Markov policies of `V^π_R(ŝ)` at the fixed start state; on
  an arbitrary one `optValueBdd` is the supremum, and the theorems take the
  maximising policy as a hypothesis. Either agrees with the value of a
  uniformly optimal policy wherever one exists (Bellman theory, not proved
  here).
* **Discounting.** Print leaves the return unspecified (*"the results of this
  paper apply to both discounted rewards and episodic environments settings"*);
  here the discounted value at any `γ < 1` is used, and the episodic
  (finite-horizon, undiscounted) return is `AISafetyAtlas.Preference.Episodic`.
-/

namespace AISafetyAtlas.Preference.Discounted

open AISafetyAtlas.Preference AISafetyAtlas.Decision
open scoped NNReal

variable {S A : Type*} [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A]

/-! ## Expectation through a map, and the value of a negated or constant reward -/

omit [DecidableEq S] [Fintype A] [Nonempty A] in
/-- The expectation of `g` under the image of `p` is the expectation of `g ∘ f`
under `p`. -/
private theorem expect_map {T : Type*} [Fintype T] (p : PMF S) (f : S → T) (g : T → ℝ) :
    expect (p.map f) g = expect p (g ∘ f) := by
  rw [← PMF.bind_pure_comp, expect_bind, expect_eq_sum]
  exact Finset.sum_congr rfl fun s _ => by simp

omit [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **The value is odd in the reward**: negating the reward negates the value. -/
public theorem vPi_neg (M : MDP S A) (r : S → A → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    (π : S → A) : vPi M (-r) hγ π = -vPi M r hγ π := by
  refine (vPi_unique M (-r) hγ π ?_).symm
  funext s
  have hneg : expect (M.transition s (π s)) (-vPi M r hγ π) =
      -expect (M.transition s (π s)) (vPi M r hγ π) := by
    rw [expect_eq_sum, expect_eq_sum, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun t _ => by simp
  simp only [bellmanPolicyOp, qVal, Pi.neg_apply]
  rw [hneg, vPi_bellman M r hγ π s]
  ring

omit [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **A policy earning the same reward `k` at every state has value
`k / (1 − γ)`** everywhere. -/
public theorem vPi_const_reward (M : MDP S A) (r : S → A → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    (π : S → A) (k : ℝ) (hk : ∀ s, r s (π s) = k) :
    vPi M r hγ π = fun _ => k / (1 - (γ : ℝ)) := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  refine (vPi_unique M r hγ π ?_).symm
  funext s
  simp only [bellmanPolicyOp, qVal, expect_const, hk s]
  field_simp [show (1 - (γ : ℝ)) ≠ 0 by linarith]
  ring

omit [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **Rewards in `[-1, 1]` give values in `[-1/(1−γ), 1/(1−γ)]`.** -/
public theorem abs_vPi_le [Nonempty S] (M : MDP S A) (r : S → A → ℝ) {γ : ℝ≥0}
    (hγ : γ < 1) (π : S → A) (hr : ∀ s a, |r s a| ≤ 1) (s : S) :
    |vPi M r hγ π s| ≤ 1 / (1 - (γ : ℝ)) := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  obtain ⟨t, ht⟩ := Finite.exists_max fun s => |vPi M r hγ π s|
  have hexp : |expect (M.transition t (π t)) (vPi M r hγ π)| ≤ |vPi M r hγ π t| :=
    abs_expect_le _ ht
  have hbell : |vPi M r hγ π t| ≤ 1 + (γ : ℝ) * |vPi M r hγ π t| := by
    calc |vPi M r hγ π t|
        = |r t (π t) + (γ : ℝ) * expect (M.transition t (π t)) (vPi M r hγ π)| := by
          rw [← vPi_bellman M r hγ π t]
      _ ≤ |r t (π t)| + |(γ : ℝ) * expect (M.transition t (π t)) (vPi M r hγ π)| :=
          abs_add_le _ _
      _ ≤ 1 + (γ : ℝ) * |vPi M r hγ π t| := by
          rw [abs_mul, abs_of_nonneg γ.coe_nonneg]
          exact add_le_add (hr t (π t)) (mul_le_mul_of_nonneg_left hexp γ.coe_nonneg)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [ht s, abs_nonneg (vPi M r hγ π t), γ.coe_nonneg]

/-! ## The same facts on an arbitrary nonempty state type

Print's state space is *discrete*, with finiteness not stated. `vPiBdd`
(`AISafetyAtlas.Decision.BoundedValue`) values a policy on any nonempty state
type at a bounded reward, and `vPiBdd_eq_vPi` makes it `vPi` on a finite one. -/

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **Rewards bounded by `C` give values bounded by `C/(1−γ)`**, on any nonempty
state type. Without a maximum over states the bound runs through the supremum of
`|v|`, which the Bellman equation bounds by `C + γ` times itself. -/
public theorem abs_vPiBdd_le [Nonempty S] (M : MDP S A) (r : S → A → ℝ) {γ : ℝ≥0}
    (hγ : γ < 1) (π : S → A) {C : ℝ} (hr : ∀ s, |r s (π s)| ≤ C) (s : S) :
    |vPiBdd M r hγ π hr s| ≤ C / (1 - (γ : ℝ)) := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  set v := vPiBdd M r hγ π hr with hv
  obtain ⟨B, hB⟩ := vPiBdd_bounded M r hγ π hr
  have hbdd : BddAbove (Set.range fun t => |v t|) := ⟨B, Set.forall_mem_range.2 hB⟩
  have hle : ∀ t, |v t| ≤ ⨆ t, |v t| := fun t => le_ciSup hbdd t
  have hm : (⨆ t, |v t|) ≤ C + (γ : ℝ) * ⨆ t, |v t| := by
    refine ciSup_le fun t => ?_
    have hexp : |expect (M.transition t (π t)) v| ≤ ⨆ t, |v t| := abs_expect_le _ hle
    calc |v t| = |r t (π t) + (γ : ℝ) * expect (M.transition t (π t)) v| :=
          congrArg abs (vPiBdd_bellman M r hγ π hr t)
      _ ≤ |r t (π t)| + |(γ : ℝ) * expect (M.transition t (π t)) v| := abs_add_le _ _
      _ ≤ C + (γ : ℝ) * ⨆ t, |v t| := by
          rw [abs_mul, abs_of_nonneg γ.coe_nonneg]
          exact add_le_add (hr t) (mul_le_mul_of_nonneg_left hexp γ.coe_nonneg)
  rw [le_div_iff₀ (by linarith)]
  nlinarith [hle s, γ.coe_nonneg, abs_nonneg (v s)]

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **A policy earning the same reward `k` at every state has value
`k / (1 − γ)`**, on any nonempty state type. -/
public theorem vPiBdd_const_reward [Nonempty S] (M : MDP S A) (r : S → A → ℝ) {γ : ℝ≥0}
    (hγ : γ < 1) (π : S → A) {C : ℝ} (hr : ∀ s, |r s (π s)| ≤ C) (k : ℝ)
    (hk : ∀ s, r s (π s) = k) :
    vPiBdd M r hγ π hr = fun _ => k / (1 - (γ : ℝ)) := by
  have hγ' : (γ : ℝ) < 1 := by exact_mod_cast hγ
  refine (vPiBdd_unique M r hγ π hr ⟨|k / (1 - (γ : ℝ))|, fun _ => le_refl _⟩
    fun s => ?_).symm
  simp only [bellmanPolicyOp, qVal, expect_const, hk s]
  field_simp [show (1 - (γ : ℝ)) ≠ 0 by linarith]
  ring

/-! ## The optimal value at the start state -/

/-- **`V*_R(ŝ)`, as the best value over the deterministic Markov policies** at
the start state (Armstrong and Mindermann, §4.1.2, `am-def-value`). There are
finitely many policies, so the maximum exists. -/
@[expose] public noncomputable def optValueAt (M : MDP S A) (R : RewardFn S A) {γ : ℝ≥0}
    (hγ : γ < 1) (s₀ : S) : ℝ :=
  (Finset.univ : Finset (S → A)).sup' Finset.univ_nonempty fun π => vPi M R hγ π s₀

/-- A policy attaining `optValueAt`: print's optimal policy `π*_R` at `ŝ`. -/
@[expose] public noncomputable def argmaxPolicy (M : MDP S A) (R : RewardFn S A)
    {γ : ℝ≥0} (hγ : γ < 1) (s₀ : S) : S → A :=
  (Finset.exists_max_image (Finset.univ : Finset (S → A)) (fun π => vPi M R hγ π s₀)
    Finset.univ_nonempty).choose

/-- No policy beats the optimal value. -/
public theorem vPi_le_optValueAt (M : MDP S A) (R : RewardFn S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (π : S → A) : vPi M R hγ π s₀ ≤ optValueAt M R hγ s₀ :=
  Finset.le_sup' (fun π => vPi M R hγ π s₀) (Finset.mem_univ π)

/-- The chosen policy attains the optimal value. -/
public theorem vPi_argmaxPolicy (M : MDP S A) (R : RewardFn S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) : vPi M R hγ (argmaxPolicy M R hγ s₀) s₀ = optValueAt M R hγ s₀ := by
  have h := (Finset.exists_max_image (Finset.univ : Finset (S → A))
    (fun π => vPi M R hγ π s₀) Finset.univ_nonempty).choose_spec
  exact le_antisymm (vPi_le_optValueAt M R hγ s₀ _)
    (Finset.sup'_le _ _ fun π _ => h.2 π (Finset.mem_univ π))

/-! ## The override model of a discounted MDP -/

/--
**The override model at a finite discounted MDP.** The agent's actions are
print's `𝒜^a`: `none` is action `0`, leaving the human on `π̇`, and `some π` is
`(1, ·)`, forcing the human onto `π`. Values are `vPi` at the start state and the
optimum is `optValueAt`; rationalising for `R` forces `argmaxPolicy`.
-/
@[expose] public noncomputable def discountedOverride (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) : OverrideModel S A (Option (S → A)) where
  resulting a := a.getD πdot
  value R π := vPi M R hγ π s₀
  optValue R := optValueAt M R hγ s₀
  le_optValue R π := vPi_le_optValueAt M R hγ s₀ π
  noop := none
  rationalise R := some (argmaxPolicy M R hγ s₀)
  rationalise_optimal R := vPi_argmaxPolicy M R hγ s₀

/-! ## Appendix B's augmented MDP -/

omit [DecidableEq S] [Fintype S] [Fintype A] [Nonempty A] in
/-- **The augmented MDP `M*`** (Armstrong and Mindermann, appendix B,
`amapp-def-augmented`, PDF p. 2: *"each state is augmented with an extra boolean
variable ... The extra boolean never changes"*). -/
@[expose] public noncomputable def augmentMDP (M : MDP S A) : MDP (S × Bool) A where
  transition x a := (M.transition x.1 a).map fun s => (s, x.2)

omit [DecidableEq S] [Fintype S] [Fintype A] [Nonempty A] in
/-- **The mixed policy `π̇'`**: `π₀` on `𝒮₀ = 𝒮 × {0}` and `π₁` on
`𝒮₁ = 𝒮 × {1}` (`amapp-def-augmented`). -/
@[expose] public def mixPolicy (π₀ π₁ : S → A) : S × Bool → A :=
  fun x => if x.2 then π₁ x.1 else π₀ x.1

omit [DecidableEq S] [Fintype S] [Fintype A] [Nonempty A] in
/-- A reward on `𝒮` extended to `𝒮*` *"by just forgetting about the boolean
factor"* (`amapp-def-planners-rewards`). -/
@[expose] public def liftReward (R : RewardFn S A) : S × Bool → A → ℝ :=
  fun x a => R x.1 a

omit [DecidableEq S] [Fintype S] [Fintype A] [Nonempty A] in
/-- **The twisted reward `Ṙ^a`**: `Ṙ` on `𝒮₀` and `R^a` on `𝒮₁`
(`amapp-def-planners-rewards`). -/
@[expose] public def twistReward (Rdot Ra : RewardFn S A) : S × Bool → A → ℝ :=
  fun x a => if x.2 then Ra x.1 a else Rdot x.1 a

omit [DecidableEq S] [Fintype A] [Nonempty A] in
/--
**Values on `M*` are values on `M`, copy by copy.** Because the boolean never
changes, the value of any policy for any reward at `(s, b)` is the base MDP's
value, from `s`, of the reward and policy read on the copy `b`.
-/
public theorem vPi_augmentMDP (M : MDP S A) (r : S × Bool → A → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    (π : S × Bool → A) (s : S) (b : Bool) :
    vPi (augmentMDP M) r hγ π (s, b) =
      vPi M (fun s a => r (s, b) a) hγ (fun s => π (s, b)) s := by
  let v : S × Bool → ℝ := fun x => vPi M (fun s a => r (s, x.2) a) hγ (fun s => π (s, x.2)) x.1
  have hfix : bellmanPolicyOp (augmentMDP M) r γ π v = v := by
    funext x
    obtain ⟨t, c⟩ := x
    simp only [bellmanPolicyOp, qVal, augmentMDP]
    rw [expect_map]
    exact (vPi_bellman M (fun s a => r (s, c) a) hγ (fun s => π (s, c)) t).symm
  exact (congrFun (vPi_unique (augmentMDP M) r hγ π hfix) (s, b)).symm

/-- **The value of an agent action on `M*`**, print's `V^{π̇'|a}` from the very
beginning of the MDP (`amapp-def-state-convention`): action `0` (`none`) starts
the human at `ŝ₀ = (ŝ, 0)` and `(1, π^a)` (`some π^a`) at `ŝ₁ = (ŝ, 1)`, with the
human following the mixed policy of `π̇` and the forced policy. -/
@[expose] public noncomputable def augActionValue (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (r : S × Bool → A → ℝ) (a : Option (S → A)) : ℝ :=
  vPi (augmentMDP M) r hγ (mixPolicy πdot (a.getD πdot)) (s₀, a.isSome)

/-- **Equation (1) on `M*`** (`amapp-eq1-regret`): `Reg(M*, a, r) =
max_{b ∈ 𝒜^a} V^{π̇'|b}_r − V^{π̇'|a}_r`. -/
@[expose] public noncomputable def augRegret (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (r : S × Bool → A → ℝ) (a : Option (S → A)) : ℝ :=
  (Finset.univ : Finset (Option (S → A))).sup' Finset.univ_nonempty
      (fun b => augActionValue M hγ s₀ πdot r b) -
    augActionValue M hγ s₀ πdot r a

/-- At a reward that forgets the boolean, an agent action's value on `M*` is the
base MDP's value of the policy it leaves the human on: the override model's
value. -/
public theorem augActionValue_liftReward (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (R : RewardFn S A) (a : Option (S → A)) :
    augActionValue M hγ s₀ πdot (liftReward R) a =
      (discountedOverride M hγ s₀ πdot).value R
        ((discountedOverride M hγ s₀ πdot).resulting a) := by
  cases a with
  | none => simp [augActionValue, vPi_augmentMDP, mixPolicy, liftReward, discountedOverride]
  | some π => simp [augActionValue, vPi_augmentMDP, mixPolicy, liftReward, discountedOverride]

/-- **`M*`'s regret is the override model's regret**, at a reward that forgets
the boolean: equation (1)'s maximum over the agent's actions is `V*_R`. -/
public theorem augRegret_eq_regret (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (R : RewardFn S A) (a : Option (S → A)) :
    augRegret M hγ s₀ πdot (liftReward R) a = (discountedOverride M hγ s₀ πdot).regret R a := by
  have hmax : (Finset.univ : Finset (Option (S → A))).sup' Finset.univ_nonempty
      (fun b => augActionValue M hγ s₀ πdot (liftReward R) b) = optValueAt M R hγ s₀ := by
    simp only [augActionValue_liftReward, discountedOverride]
    refine le_antisymm (Finset.sup'_le _ _ fun b _ => vPi_le_optValueAt M R hγ s₀ _) ?_
    refine le_trans ?_ (Finset.le_sup' _ (Finset.mem_univ (some (argmaxPolicy M R hγ s₀))))
    exact (vPi_argmaxPolicy M R hγ s₀).ge
  rw [augRegret, hmax, augActionValue_liftReward]
  rfl

/-- **Appendix B.1's closed form** (Armstrong and Mindermann, appendix B,
`amapp-zero-regret-inaction`, PDF p. 3: *"for `a = (1, π^a)`,
`Reg(M*, (1, π^a), Ṙ) = V*_Ṙ − V^{π^a}_Ṙ`"*), with the regret computed on the
augmented MDP and the two values on the base MDP. -/
public theorem augRegret_overriding (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (Rdot : RewardFn S A) (πa : S → A) :
    augRegret M hγ s₀ πdot (liftReward Rdot) (some πa) =
      optValueAt M Rdot hγ s₀ - vPi M Rdot hγ πa s₀ := by
  rw [augRegret_eq_regret]
  rfl

/-- **Appendix B.1's first sentence**: *"`π̇` is optimal with respect to `Ṙ`
... so the regret for `a = 0` is `0`"*, on the augmented MDP. -/
public theorem augRegret_noop (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (Rdot : RewardFn S A)
    (hopt : vPi M Rdot hγ πdot s₀ = optValueAt M Rdot hγ s₀) :
    augRegret M hγ s₀ πdot (liftReward Rdot) none = 0 := by
  rw [augRegret_eq_regret]
  show optValueAt M Rdot hγ s₀ - vPi M Rdot hγ πdot s₀ = 0
  rw [hopt, sub_self]

/-! ## Equation (2), computed -/

/-- **The agent's expected value under its belief** (Armstrong and Mindermann,
appendix B.2, `amapp-eq2`): the human's reward is `Ṙ` with probability `1 − ε`
and the twisted `Ṙ^a` with probability `ε`, and each is evaluated on `M*` at the
agent's action. -/
@[expose] public noncomputable def beliefValue (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A) (a : Option (S → A)) : ℝ :=
  ε * augActionValue M hγ s₀ πdot (twistReward Rdot Ra) a +
    (1 - ε) * augActionValue M hγ s₀ πdot (liftReward Rdot) a

omit [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **Action `(1, π)`, for any forced policy**: *"`Ṙ^a` and `R^a` agree given
action 1"*, so the twisted term is `π`'s value for `R^a`. -/
public theorem beliefValue_some (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A) (π : S → A) :
    beliefValue M hγ s₀ πdot ε Rdot Ra (some π) =
      ε * vPi M Ra hγ π s₀ + (1 - ε) * vPi M Rdot hγ π s₀ := by
  simp [beliefValue, augActionValue, vPi_augmentMDP, mixPolicy, twistReward, liftReward]

/-- **Equation (2)** (`amapp-eq2`, PDF pp. 3-4: *"`(1, π^a)` gives
`ε V*_{R^a} + (1 − ε) V^{π^a}_Ṙ`, since `Ṙ^a` and `R^a` agree given action 1"*):
at the action forcing the `R^a`-optimal policy, the expected value under the
belief **is** the override model's `mixtureValue`. -/
public theorem beliefValue_overriding (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A) :
    beliefValue M hγ s₀ πdot ε Rdot Ra (some (argmaxPolicy M Ra hγ s₀)) =
      (discountedOverride M hγ s₀ πdot).mixtureValue ε Rdot Ra := by
  rw [beliefValue_some, vPi_argmaxPolicy]
  rfl

/-- **Action `0`** (`amapp-eq2`: *"the agent's action `0` gives expected reward
`V*_Ṙ`, since `Ṙ` and `Ṙ^a` agree given `0`"*): when `π̇` is optimal for `Ṙ`,
both terms of the belief are `V*_Ṙ`. -/
public theorem beliefValue_noop (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A)
    (hopt : vPi M Rdot hγ πdot s₀ = optValueAt M Rdot hγ s₀) :
    beliefValue M hγ s₀ πdot ε Rdot Ra none = optValueAt M Rdot hγ s₀ := by
  have h : beliefValue M hγ s₀ πdot ε Rdot Ra none =
      ε * vPi M Rdot hγ πdot s₀ + (1 - ε) * vPi M Rdot hγ πdot s₀ := by
    simp [beliefValue, augActionValue, vPi_augmentMDP, mixPolicy, twistReward, liftReward]
  rw [h, hopt]
  ring

/-! ## Equation (2) on an arbitrary nonempty state type

The finite development above reads `V*` through `optValueAt`, a maximum over the
finitely many policies. On an infinite state type there are infinitely many, and
`V*_R(ŝ)` is the supremum `optValueBdd` of `vPiBdd` over them; the theorems below
take print's `π^a` *"the policy that maximises the expectation of `R^a`"* as a
hypothesis on a given policy, and `π̇`'s optimality likewise. Rewards are bounded
by an arbitrary `C`, the reward bound `vPiBdd` needs (print's `[-1, 1]` is
`C = 1`). -/

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- The expectation under the image of `p` along an injective map is the
expectation of the composite, on arbitrary types. -/
public theorem expect_map_of_injective {T : Type*} (p : PMF S) {f : S → T}
    (hf : Function.Injective f) (g : T → ℝ) :
    expect (p.map f) g = expect p (g ∘ f) := by
  classical
  have hmap : ∀ s, (p.map f) (f s) = p s := by
    intro s
    rw [PMF.map_apply]
    have : ∀ a, (if f s = f a then p a else 0) = if a = s then p a else 0 := fun a => by
      simp only [hf.eq_iff, eq_comm]
    rw [tsum_congr this, tsum_ite_eq]
  rw [expect, expect, ← hf.tsum_eq]
  · exact tsum_congr fun s => by simp [hmap]
  · intro t ht
    by_contra h
    apply ht
    have : (p.map f) t = 0 := by
      rw [PMF.apply_eq_zero_iff, PMF.mem_support_map_iff]
      rintro ⟨a, -, rfl⟩
      exact h ⟨a, rfl⟩
    simp [this]

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **Values on `M*` are values on `M`, copy by copy**, on any nonempty state
type: the bounded counterpart of `vPi_augmentMDP`. -/
public theorem vPiBdd_augmentMDP [Nonempty S] (M : MDP S A) (r : S × Bool → A → ℝ)
    {γ : ℝ≥0} (hγ : γ < 1) (π : S × Bool → A) {C : ℝ} (hr : ∀ x, |r x (π x)| ≤ C)
    (s : S) (b : Bool) :
    vPiBdd (augmentMDP M) r hγ π hr (s, b) =
      vPiBdd M (fun s a => r (s, b) a) hγ (fun s => π (s, b)) (fun s => hr (s, b)) s := by
  let v : S × Bool → ℝ := fun x =>
    vPiBdd M (fun s a => r (s, x.2) a) hγ (fun s => π (s, x.2)) (fun s => hr (s, x.2)) x.1
  have hbdd : Blackwell.UniformBounded v := by
    obtain ⟨B₀, h₀⟩ := vPiBdd_bounded M (fun s a => r (s, false) a) hγ
      (fun s => π (s, false)) (fun s => hr (s, false))
    obtain ⟨B₁, h₁⟩ := vPiBdd_bounded M (fun s a => r (s, true) a) hγ
      (fun s => π (s, true)) (fun s => hr (s, true))
    refine ⟨max B₀ B₁, fun x => ?_⟩
    obtain ⟨t, c⟩ := x
    cases c
    · exact (h₀ t).trans (le_max_left _ _)
    · exact (h₁ t).trans (le_max_right _ _)
  have hfix : ∀ x, v x = bellmanPolicyOp (augmentMDP M) r γ π v x := by
    intro x
    obtain ⟨t, c⟩ := x
    simp only [bellmanPolicyOp, qVal, augmentMDP]
    rw [expect_map_of_injective _ (fun a b h => (Prod.mk.inj h).1)]
    exact vPiBdd_bellman M (fun s a => r (s, c) a) hγ (fun s => π (s, c))
      (fun s => hr (s, c)) t
  exact (congrFun (vPiBdd_unique (augmentMDP M) r hγ π hr hbdd hfix) (s, b)).symm

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **`V*_R(ŝ)` on an arbitrary nonempty state type**: the supremum over the
deterministic Markov policies of their value at the start state. The values are
bounded by `C/(1−γ)` (`abs_vPiBdd_le`), so this is a genuine supremum. -/
@[expose] public noncomputable def optValueBdd [Nonempty S] (M : MDP S A) (R : RewardFn S A)
    {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ s a, |R s a| ≤ C) (s₀ : S) : ℝ :=
  ⨆ π : S → A, vPiBdd M R hγ π (fun s => hR s (π s)) s₀

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- A policy maximising the value at the start state attains `optValueBdd`. -/
public theorem optValueBdd_eq_of_max [Nonempty S] (M : MDP S A) (R : RewardFn S A)
    {γ : ℝ≥0} (hγ : γ < 1) {C : ℝ} (hR : ∀ s a, |R s a| ≤ C) (s₀ : S) (πa : S → A)
    (hmax : ∀ π : S → A, vPiBdd M R hγ π (fun s => hR s (π s)) s₀ ≤
      vPiBdd M R hγ πa (fun s => hR s (πa s)) s₀) :
    optValueBdd M R hγ hR s₀ = vPiBdd M R hγ πa (fun s => hR s (πa s)) s₀ :=
  have : Nonempty (S → A) := ⟨πa⟩
  le_antisymm (ciSup_le hmax) (le_ciSup ⟨_, Set.forall_mem_range.2 hmax⟩ πa)

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **The value of an agent action on `M*`**, on an arbitrary nonempty state
type: `augActionValue` with `vPiBdd` for `vPi`. -/
@[expose] public noncomputable def augActionValueBdd [Nonempty S] (M : MDP S A) {γ : ℝ≥0}
    (hγ : γ < 1) (s₀ : S) (πdot : S → A) (r : S × Bool → A → ℝ) {C : ℝ}
    (hr : ∀ x a, |r x a| ≤ C) (a : Option (S → A)) : ℝ :=
  vPiBdd (augmentMDP M) r hγ (mixPolicy πdot (a.getD πdot)) (fun x => hr x _) (s₀, a.isSome)

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- A bound on `Ṙ` and on `R^a` bounds the twisted reward. -/
public theorem abs_twistReward_le {Rdot Ra : RewardFn S A} {C : ℝ}
    (hRdot : ∀ s a, |Rdot s a| ≤ C) (hRa : ∀ s a, |Ra s a| ≤ C) (x : S × Bool) (a : A) :
    |twistReward Rdot Ra x a| ≤ C := by
  unfold twistReward
  split_ifs
  exacts [hRa _ _, hRdot _ _]

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **The agent's expected value under its belief** (`amapp-eq2`), on an
arbitrary nonempty state type: `beliefValue` with `vPiBdd` for `vPi`. -/
@[expose] public noncomputable def beliefValueBdd [Nonempty S] (M : MDP S A) {γ : ℝ≥0}
    (hγ : γ < 1) (s₀ : S) (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A) {C : ℝ}
    (hRdot : ∀ s a, |Rdot s a| ≤ C) (hRa : ∀ s a, |Ra s a| ≤ C) (a : Option (S → A)) : ℝ :=
  ε * augActionValueBdd M hγ s₀ πdot (twistReward Rdot Ra) (abs_twistReward_le hRdot hRa) a +
    (1 - ε) * augActionValueBdd M hγ s₀ πdot (liftReward Rdot) (fun x a => hRdot x.1 a) a

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **Action `(1, π)`, for any forced policy**, on an arbitrary nonempty state
type: the twisted term is `π`'s value for `R^a`. -/
public theorem beliefValueBdd_some [Nonempty S] (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A) {C : ℝ}
    (hRdot : ∀ s a, |Rdot s a| ≤ C) (hRa : ∀ s a, |Ra s a| ≤ C) (π : S → A) :
    beliefValueBdd M hγ s₀ πdot ε Rdot Ra hRdot hRa (some π) =
      ε * vPiBdd M Ra hγ π (fun s => hRa s (π s)) s₀ +
        (1 - ε) * vPiBdd M Rdot hγ π (fun s => hRdot s (π s)) s₀ := by
  simp only [beliefValueBdd, augActionValueBdd]
  rw [vPiBdd_augmentMDP, vPiBdd_augmentMDP]
  rfl

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **Equation (2)**, on an arbitrary nonempty state type (`amapp-eq2`, PDF
pp. 3-4: *"`(1, π^a)` gives `ε V*_{R^a} + (1 − ε) V^{π^a}_Ṙ`"*), with `π^a` any
policy maximising the value of `R^a` at the start state. -/
public theorem beliefValueBdd_overriding [Nonempty S] (M : MDP S A) {γ : ℝ≥0}
    (hγ : γ < 1) (s₀ : S) (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A) {C : ℝ}
    (hRdot : ∀ s a, |Rdot s a| ≤ C) (hRa : ∀ s a, |Ra s a| ≤ C) (πa : S → A)
    (hmax : ∀ π : S → A, vPiBdd M Ra hγ π (fun s => hRa s (π s)) s₀ ≤
      vPiBdd M Ra hγ πa (fun s => hRa s (πa s)) s₀) :
    beliefValueBdd M hγ s₀ πdot ε Rdot Ra hRdot hRa (some πa) =
      ε * optValueBdd M Ra hγ hRa s₀ +
        (1 - ε) * vPiBdd M Rdot hγ πa (fun s => hRdot s (πa s)) s₀ := by
  rw [beliefValueBdd_some, optValueBdd_eq_of_max M Ra hγ hRa s₀ πa hmax]

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- **Action `0`**, on an arbitrary nonempty state type (`amapp-eq2`: *"the
agent's action `0` gives expected reward `V*_Ṙ`"*): when `π̇` maximises the value
of `Ṙ` at the start state, the belief's value is `V*_Ṙ`. -/
public theorem beliefValueBdd_noop [Nonempty S] (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A) {C : ℝ}
    (hRdot : ∀ s a, |Rdot s a| ≤ C) (hRa : ∀ s a, |Ra s a| ≤ C)
    (hopt : ∀ π : S → A, vPiBdd M Rdot hγ π (fun s => hRdot s (π s)) s₀ ≤
      vPiBdd M Rdot hγ πdot (fun s => hRdot s (πdot s)) s₀) :
    beliefValueBdd M hγ s₀ πdot ε Rdot Ra hRdot hRa none = optValueBdd M Rdot hγ hRdot s₀ := by
  have h : beliefValueBdd M hγ s₀ πdot ε Rdot Ra hRdot hRa none =
      ε * vPiBdd M Rdot hγ πdot (fun s => hRdot s (πdot s)) s₀ +
        (1 - ε) * vPiBdd M Rdot hγ πdot (fun s => hRdot s (πdot s)) s₀ := by
    simp only [beliefValueBdd, augActionValueBdd]
    rw [vPiBdd_augmentMDP, vPiBdd_augmentMDP]
    rfl
  rw [h, optValueBdd_eq_of_max M Rdot hγ hRdot s₀ πdot hopt]
  ring

/-! ## §4.1.2's half-maximal bound at a discounted MDP -/

open scoped Classical in
/-- **The worst reward for a policy**, `R_π(s, a) = −1` on the policy's action and
`+1` elsewhere: it is in print's reward space, the policy earns `−1` at every
step, and any other action earns `+1`. -/
@[expose] public noncomputable def signReward (π : S → A) : RewardFn S A :=
  fun s a => if a = π s then -1 else 1

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- `R_π` is in print's reward space. -/
public theorem isBoundedReward_signReward (π : S → A) : IsBoundedReward (signReward π) :=
  fun s a => by unfold signReward; split_ifs <;> norm_num

omit [Fintype S] [DecidableEq S] [Fintype A] [Nonempty A] in
/-- A reward in print's space is bounded by `1` in absolute value. -/
public theorem abs_le_one_of_isBoundedReward {R : RewardFn S A} (h : IsBoundedReward R)
    (s : S) (a : A) : |R s a| ≤ 1 :=
  abs_le.mpr (h s a)

/-- **Regret is at most `2/(1−γ)`** in print's reward space: print's
`Reg(π, R)(ŝ) = V*_R(ŝ) − V^π_R(ŝ)`, with `V*_R(ŝ)` attained by `argmaxPolicy`. -/
public theorem argmax_regret_le_two_div (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1) (s₀ : S)
    (R : RewardFn S A) (hR : IsBoundedReward R) (π : S → A) :
    vPi M R hγ (argmaxPolicy M R hγ s₀) s₀ - vPi M R hγ π s₀ ≤ 2 / (1 - (γ : ℝ)) := by
  have : Nonempty S := ⟨s₀⟩
  have h1 := abs_le.mp (abs_vPi_le M R hγ (argmaxPolicy M R hγ s₀)
    (abs_le_one_of_isBoundedReward hR) s₀)
  have h2 := abs_le.mp (abs_vPi_le M R hγ π (abs_le_one_of_isBoundedReward hR) s₀)
  have : 2 / (1 - (γ : ℝ)) = 1 / (1 - (γ : ℝ)) + 1 / (1 - (γ : ℝ)) := by ring
  linarith [h1.2, h2.1]

/-- **`R_π` attains that bound for `π`**, at two or more actions: `π` earns `−1`
at every step and a policy avoiding `π`'s action earns `+1`. -/
public theorem argmax_regret_signReward [Nontrivial A] (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) (π : S → A) :
    vPi M (signReward π) hγ (argmaxPolicy M (signReward π) hγ s₀) s₀ -
      vPi M (signReward π) hγ π s₀ = 2 / (1 - (γ : ℝ)) := by
  refine le_antisymm (argmax_regret_le_two_div M hγ s₀ _ (isBoundedReward_signReward π) π) ?_
  let π' : S → A := fun s => (exists_ne (π s)).choose
  have hπ' : ∀ s, π' s ≠ π s := fun s => (exists_ne (π s)).choose_spec
  have hlow : vPi M (signReward π) hγ π = fun _ => -1 / (1 - (γ : ℝ)) :=
    vPi_const_reward M _ hγ π (-1) fun s => by simp [signReward]
  have hhigh : vPi M (signReward π) hγ π' = fun _ => 1 / (1 - (γ : ℝ)) :=
    vPi_const_reward M _ hγ π' 1 fun s => by simp [signReward, hπ' s]
  have hbest := vPi_le_optValueAt M (signReward π) hγ s₀ π'
  rw [vPi_argmaxPolicy, hlow]
  rw [hhigh] at hbest
  have : 2 / (1 - (γ : ℝ)) = 1 / (1 - (γ : ℝ)) - -1 / (1 - (γ : ℝ)) := by ring
  linarith

/-- At a single action there is a single policy, and every regret is `0`. -/
public theorem argmax_regret_eq_zero_of_subsingleton [Subsingleton A] (M : MDP S A) {γ : ℝ≥0}
    (hγ : γ < 1) (s₀ : S) (R : RewardFn S A) (π : S → A) :
    vPi M R hγ (argmaxPolicy M R hγ s₀) s₀ - vPi M R hγ π s₀ = 0 := by
  rw [Subsingleton.elim (argmaxPolicy M R hγ s₀) π, sub_self]

/--
**The complemented class of a finite discounted MDP.** Environments are print's
reward space `[-1, 1]^{𝒮×𝒜}`, returns are `V^π_R(ŝ)`, the complement of a reward
is its negation (so returns sum to `0`), the best policy is `argmaxPolicy`, the
worst reward for `π` is `signReward π`, and every policy is a worst policy: at
two or more actions every policy has worst-case regret `2/(1−γ)`, at one action
every regret is `0`.
-/
@[expose] public noncomputable def discountedClass (M : MDP S A) {γ : ℝ≥0} (hγ : γ < 1)
    (s₀ : S) :
    AISafetyAtlas.Wireheading.Corruption.ComplementedClass (BoundedRewardFn S A) (S → A) where
  returnValue R π := vPi M R.1 hγ π s₀
  horizon := 0
  complement R := ⟨-R.1, R.2.neg⟩
  complement_involutive R := Subtype.ext (neg_neg R.1)
  complement_return R π := by
    simp only [vPi_neg, Pi.neg_apply]
    ring
  bestPolicy R := argmaxPolicy M R.1 hγ s₀
  bestPolicy_best R π := by
    rw [vPi_argmaxPolicy]
    exact vPi_le_optValueAt M R.1 hγ s₀ π
  worstEnvironment π := ⟨signReward π, isBoundedReward_signReward π⟩
  worstEnvironment_worst π R := by
    rcases subsingleton_or_nontrivial A with hA | hA
    · rw [argmax_regret_eq_zero_of_subsingleton, argmax_regret_eq_zero_of_subsingleton]
    · rw [argmax_regret_signReward]
      exact argmax_regret_le_two_div M hγ s₀ R.1 R.2 π
  worstPolicy := fun _ => Classical.arbitrary A
  worstPolicy_worst π := by
    rcases subsingleton_or_nontrivial A with hA | hA
    · rw [argmax_regret_eq_zero_of_subsingleton, argmax_regret_eq_zero_of_subsingleton]
    · rw [argmax_regret_signReward, argmax_regret_signReward]

omit [Fintype S] [DecidableEq S] [Fintype A] in
/--
**The sign-reward argument for §4.1.2's half-maximal bound, at any return.**
Let `G R σ` be any return of policy `σ` under a reward `R` of print's space
`[-1, 1]^{𝒮×𝒜}`, bounded by `B` in absolute value, such that under `R_π`
(`signReward π`) the policy `π` earns `−B` and every policy avoiding `π`'s action
everywhere earns `B`. Then every policy's worst-case regret (Definition 10's
`worstCaseRegretOf`, with real suprema) is `2B` at two or more actions and `0` at
one, so the half bound holds. No finiteness of the state space and no
complemented class are used.
-/
public theorem half_maximal_regret_of_signReward (G : BoundedRewardFn S A → (S → A) → ℝ)
    (B : ℝ) (hG : ∀ R σ, |G R σ| ≤ B)
    (hlow : ∀ π, G ⟨signReward π, isBoundedReward_signReward π⟩ π = -B)
    (hhigh : ∀ π σ, (∀ s, σ s ≠ π s) →
      G ⟨signReward π, isBoundedReward_signReward π⟩ σ = B)
    (π : S → A) :
    (⨆ π' : S → A, AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf G Set.univ π') / 2 ≤
      AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf G Set.univ π := by
  have hne : Nonempty (Set.univ : Set (BoundedRewardFn S A)) :=
    ⟨⟨⟨0, isBoundedReward_zero⟩, Set.mem_univ _⟩⟩
  rcases subsingleton_or_nontrivial A with hA | hA
  · have hz : ∀ σ, AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf G Set.univ σ = 0 := by
      intro σ
      simp only [AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf,
        AISafetyAtlas.Wireheading.Corruption.regretOf]
      have : ∀ (μ : BoundedRewardFn S A) (π' : S → A), G μ π' - G μ σ = 0 := fun μ π' => by
        rw [Subsingleton.elim π' σ, sub_self]
      simp [this]
    simp [hz]
  · have hbound : ∀ μ σ π', G μ π' - G μ σ ≤ 2 * B := fun μ σ π' => by
      linarith [(abs_le.mp (hG μ π')).2, (abs_le.mp (hG μ σ)).1]
    have hreg : ∀ μ σ, AISafetyAtlas.Wireheading.Corruption.regretOf G μ σ ≤ 2 * B :=
      fun μ σ => ciSup_le fun π' => hbound μ σ π'
    have hw : ∀ σ, AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf G Set.univ σ =
        2 * B := by
      intro σ
      refine le_antisymm (ciSup_le fun μ => hreg μ σ) ?_
      let σ' : S → A := fun s => (exists_ne (σ s)).choose
      have hσ' : ∀ s, σ' s ≠ σ s := fun s => (exists_ne (σ s)).choose_spec
      let μ : BoundedRewardFn S A := ⟨signReward σ, isBoundedReward_signReward σ⟩
      have h1 : 2 * B ≤ AISafetyAtlas.Wireheading.Corruption.regretOf G μ σ := by
        refine le_trans ?_ (le_ciSup ⟨2 * B, Set.forall_mem_range.2 (hbound μ σ)⟩ σ')
        rw [hhigh σ σ' hσ', hlow σ]
        ring_nf
        exact le_refl _
      exact h1.trans (le_ciSup (f := fun μ : (Set.univ : Set (BoundedRewardFn S A)) =>
        AISafetyAtlas.Wireheading.Corruption.regretOf G μ σ)
        ⟨2 * B, Set.forall_mem_range.2 fun μ => hreg μ σ⟩ ⟨μ, Set.mem_univ _⟩)
    have hB : 0 ≤ B := (abs_nonneg _).trans (hG ⟨0, isBoundedReward_zero⟩ π)
    simp only [hw, ciSup_const]
    linarith

omit [Fintype S] [DecidableEq S] [Fintype A] in
/--
**§4.1.2's half-maximal bound at a discounted MDP with a discrete state space**
(Armstrong and Mindermann, §4.1.2, `am-half-maximal`, PDF p. 4: *"for any `π`,
`max_{R ∈ ℛ} Reg(π, R)(s) ≥ ½ (max_{π' ∈ Π, R ∈ ℛ} Reg(π', R)(s))"*), at print's
reward space `ℛ = [-1, 1]^{𝒮×𝒜}` and policy space `Π = 𝒮 → 𝒜`, with
`Reg(π, R)(s) = V*_R(s) − V^π_R(s)` read through Definition 10's `regretOf` at
the return `V^π_R(ŝ)`, and `V*_R(ŝ)` the supremum over policies. The state type
is any nonempty type (print's *discrete* `𝒮`, finiteness not stated) and the
value is `vPiBdd`; on a finite state type it is `vPi` (`vPiBdd_eq_vPi`), where
the bound is also `ComplementedClass.everitt_theorem_eleven` at
`discountedClass`. Obtained from `half_maximal_regret_of_signReward` with
`B = 1/(1−γ)`.
-/
public theorem discounted_half_maximal_regret [Nonempty S] (M : MDP S A) {γ : ℝ≥0}
    (hγ : γ < 1) (s₀ : S) (π : S → A) :
    (⨆ π' : S → A, AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (R : BoundedRewardFn S A) (σ : S → A) =>
          vPiBdd M R.1 hγ σ (fun s => abs_le_one_of_isBoundedReward R.2 s (σ s)) s₀)
        Set.univ π') / 2 ≤
      AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (R : BoundedRewardFn S A) (σ : S → A) =>
          vPiBdd M R.1 hγ σ (fun s => abs_le_one_of_isBoundedReward R.2 s (σ s)) s₀)
        Set.univ π := by
  refine half_maximal_regret_of_signReward _ (1 / (1 - (γ : ℝ)))
    (fun R σ => abs_vPiBdd_le M R.1 hγ σ _ s₀) (fun π => ?_) (fun π σ hσ => ?_) π
  · rw [vPiBdd_const_reward M _ hγ π _ (-1) fun s => by simp [signReward]]
    ring
  · rw [vPiBdd_const_reward M _ hγ σ _ 1 fun s => by simp [signReward, hσ s]]

end AISafetyAtlas.Preference.Discounted
