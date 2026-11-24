module

public import AISafetyAtlas.Preference.Discounted
public import AISafetyAtlas.Decision.EpisodicValue

/-!
# The regret and override results at an episodic MDP

Armstrong and Mindermann's setting (§3, PDF p. 3): *"The results of this paper
apply to both discounted rewards and episodic environments settings."*
`AISafetyAtlas.Preference.Discounted` renders the results at the discounted value;
this module renders them at the episodic one, the expected undiscounted reward
over a horizon of `T` steps (`AISafetyAtlas.Decision.vPiEpisodic`), on an
arbitrary state type (print's *discrete* `𝒮`, finiteness not stated).

* **§4.1.2's half-maximal bound** (`episodic_half_maximal_regret`), by the same
  sign-reward argument as the discounted one,
  `Discounted.half_maximal_regret_of_signReward`, with bound `T`.
* **Appendix B's augmented MDP** (`vPiEpisodic_augmentMDP`): values on `M*` are
  values on `M`, copy by copy, at every horizon.
* **Equation (2)'s two halves** (`beliefValueEp_overriding`, `beliefValueEp_noop`).
* **Equation (2) under random termination** (`beliefValueTerm_some`,
  `beliefValueTerm_overriding`, `beliefValueTerm_noop`): the episode ends when the
  process first reaches a terminal state, after a random number of steps, and
  the value is the undiscounted return up to then
  (`AISafetyAtlas.Decision.vPiTerm`). The copy lemma holds at every horizon
  (`vPiStopped_augmentMDP`), so the equalities hold with no convergence
  hypothesis. The fixed horizon is the instance with a clock in the state
  (`vPiTerm_clockMDP`, `beliefValueTerm_clockMDP`).

## Scope against print

* `V*_R(ŝ)` is `optValueEp`, the supremum over stationary deterministic policies
  of the `T`-step value at the start state; the theorems take the maximising
  policy as a hypothesis. Print's `Π` is deterministic Markov policies
  (`am-policy-space`); a horizon-dependent optimum is not used. The half-maximal
  bound is unaffected by that choice: the sign reward already pins every
  worst-case regret at `2T`.
* The value is the finite-horizon Bellman recursion, not proved equal to the
  expected reward sum along `AISafetyAtlas.Decision.MDP.run`
  (see `AISafetyAtlas.Decision.EpisodicValue`).
* Under random termination V^*_R(ŝ) is `optValueTerm`, the supremum over the
  same stationary deterministic policies of the return up to termination. The
  return is a limit of stopped values; where that limit fails to exist the
  value is `Filter.limUnder`'s junk, and the equalities still hold there. Print
  presupposes the return exists, and `AISafetyAtlas.Decision.vPiTerm_eq_of_tendsto`
  identifies the value when it does.
-/

namespace AISafetyAtlas.Preference.Episodic

open AISafetyAtlas.Preference AISafetyAtlas.Decision AISafetyAtlas.Preference.Discounted

variable {S A : Type*}

/-! ## §4.1.2's half-maximal bound -/

/--
**§4.1.2's half-maximal bound at an episodic MDP** (Armstrong and Mindermann,
§4.1.2, `am-half-maximal`, PDF p. 4: *"for any `π`, `max_{R ∈ ℛ} Reg(π, R)(s) ≥
½ (max_{π' ∈ Π, R ∈ ℛ} Reg(π', R)(s))"*), at print's reward space
`ℛ = [-1, 1]^{𝒮×𝒜}` and policy space `Π = 𝒮 → 𝒜`, with `V^π_R(ŝ)` the
expected undiscounted reward over `T` steps from the start state and regret read
through Definition 10's `regretOf`. Any state type, any horizon.
-/
public theorem episodic_half_maximal_regret [Nonempty A] (M : MDP S A) (T : ℕ) (s₀ : S)
    (π : S → A) :
    (⨆ π' : S → A, AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (R : BoundedRewardFn S A) (σ : S → A) => vPiEpisodic M R.1 T σ s₀)
        Set.univ π') / 2 ≤
      AISafetyAtlas.Wireheading.Corruption.worstCaseRegretOf
        (fun (R : BoundedRewardFn S A) (σ : S → A) => vPiEpisodic M R.1 T σ s₀)
        Set.univ π := by
  refine half_maximal_regret_of_signReward _ (T : ℝ)
    (fun R σ => by
      simpa using abs_vPiEpisodic_le M R.1 σ
        (fun s => abs_le_one_of_isBoundedReward R.2 s (σ s)) T s₀)
    (fun π => ?_) (fun π σ hσ => ?_) π
  · rw [vPiEpisodic_const_reward M _ π (-1) (fun s => by simp [signReward])]
    ring
  · rw [vPiEpisodic_const_reward M _ σ 1 (fun s => by simp [signReward, hσ s])]
    ring

/-! ## Appendix B's augmented MDP -/

/-- **Values on `M*` are values on `M`, copy by copy**, at every horizon: the
episodic counterpart of `vPi_augmentMDP`. -/
public theorem vPiEpisodic_augmentMDP (M : MDP S A) (r : S × Bool → A → ℝ) (T : ℕ)
    (π : S × Bool → A) (s : S) (b : Bool) :
    vPiEpisodic (augmentMDP M) r T π (s, b) =
      vPiEpisodic M (fun s a => r (s, b) a) T (fun s => π (s, b)) s := by
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
    rw [vPiEpisodic_succ, vPiEpisodic_succ]
    simp only [augmentMDP]
    rw [expect_map_of_injective _ (fun a c h => (Prod.mk.inj h).1)]
    congr 2
    funext t
    exact ih t

/-- **`V*_R(ŝ)` at horizon `T`**: the supremum over the deterministic Markov
policies of their `T`-step value at the start state (bounded by `T · C` at a
reward bounded by `C`). -/
@[expose] public noncomputable def optValueEp (M : MDP S A) (R : RewardFn S A) (T : ℕ)
    (s₀ : S) : ℝ :=
  ⨆ π : S → A, vPiEpisodic M R T π s₀

/-- A policy maximising the `T`-step value at the start state attains
`optValueEp`. -/
public theorem optValueEp_eq_of_max (M : MDP S A) (R : RewardFn S A) (T : ℕ) (s₀ : S)
    (πa : S → A) (hmax : ∀ π : S → A, vPiEpisodic M R T π s₀ ≤ vPiEpisodic M R T πa s₀) :
    optValueEp M R T s₀ = vPiEpisodic M R T πa s₀ :=
  have : Nonempty (S → A) := ⟨πa⟩
  le_antisymm (ciSup_le hmax) (le_ciSup ⟨_, Set.forall_mem_range.2 hmax⟩ πa)

/-- **The value of an agent action on `M*`** at horizon `T`
(`amapp-def-state-convention`): action `0` (`none`) starts the human at
`(ŝ, 0)` and `(1, π^a)` (`some π^a`) at `(ŝ, 1)`, the human following the mixed
policy. -/
@[expose] public noncomputable def augActionValueEp (M : MDP S A) (T : ℕ) (s₀ : S)
    (πdot : S → A) (r : S × Bool → A → ℝ) (a : Option (S → A)) : ℝ :=
  vPiEpisodic (augmentMDP M) r T (mixPolicy πdot (a.getD πdot)) (s₀, a.isSome)

/-- **The agent's expected value under its belief** at horizon `T`
(`amapp-eq2`): `Ṙ` with probability `1 − ε` and the twisted `Ṙ^a` with
probability `ε`, each evaluated on `M*` at the agent's action. -/
@[expose] public noncomputable def beliefValueEp (M : MDP S A) (T : ℕ) (s₀ : S)
    (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A) (a : Option (S → A)) : ℝ :=
  ε * augActionValueEp M T s₀ πdot (twistReward Rdot Ra) a +
    (1 - ε) * augActionValueEp M T s₀ πdot (liftReward Rdot) a

/-- **Action `(1, π)`, for any forced policy**, at horizon `T`: the twisted term
is `π`'s value for `R^a`. -/
public theorem beliefValueEp_some (M : MDP S A) (T : ℕ) (s₀ : S) (πdot : S → A) (ε : ℝ)
    (Rdot Ra : RewardFn S A) (π : S → A) :
    beliefValueEp M T s₀ πdot ε Rdot Ra (some π) =
      ε * vPiEpisodic M Ra T π s₀ + (1 - ε) * vPiEpisodic M Rdot T π s₀ := by
  simp [beliefValueEp, augActionValueEp, vPiEpisodic_augmentMDP, mixPolicy, twistReward,
    liftReward]

/-- **Action 0**, at horizon T: both terms are π̇'s value for Ṙ, since
Ṙ and Ṙ^a agree on the copy 𝒮₀. -/
public theorem beliefValueEp_none (M : MDP S A) (T : ℕ) (s₀ : S) (πdot : S → A) (ε : ℝ)
    (Rdot Ra : RewardFn S A) :
    beliefValueEp M T s₀ πdot ε Rdot Ra none =
      ε * vPiEpisodic M Rdot T πdot s₀ + (1 - ε) * vPiEpisodic M Rdot T πdot s₀ := by
  simp [beliefValueEp, augActionValueEp, vPiEpisodic_augmentMDP, mixPolicy, twistReward,
    liftReward]

/-- **Equation (2) at an episodic MDP** (`amapp-eq2`, PDF pp. 3-4: *"`(1, π^a)`
gives `ε V*_{R^a} + (1 − ε) V^{π^a}_Ṙ`"*), with `π^a` any policy maximising the
`T`-step value of `R^a` at the start state. -/
public theorem beliefValueEp_overriding (M : MDP S A) (T : ℕ) (s₀ : S) (πdot : S → A)
    (ε : ℝ) (Rdot Ra : RewardFn S A) (πa : S → A)
    (hmax : ∀ π : S → A, vPiEpisodic M Ra T π s₀ ≤ vPiEpisodic M Ra T πa s₀) :
    beliefValueEp M T s₀ πdot ε Rdot Ra (some πa) =
      ε * optValueEp M Ra T s₀ + (1 - ε) * vPiEpisodic M Rdot T πa s₀ := by
  rw [beliefValueEp_some, optValueEp_eq_of_max M Ra T s₀ πa hmax]

/-- **Action `0` at an episodic MDP** (`amapp-eq2`: *"the agent's action `0`
gives expected reward `V*_Ṙ`"*): when `π̇` maximises the `T`-step value of `Ṙ`
at the start state, the belief's value is `V*_Ṙ`. -/
public theorem beliefValueEp_noop (M : MDP S A) (T : ℕ) (s₀ : S) (πdot : S → A) (ε : ℝ)
    (Rdot Ra : RewardFn S A)
    (hopt : ∀ π : S → A, vPiEpisodic M Rdot T π s₀ ≤ vPiEpisodic M Rdot T πdot s₀) :
    beliefValueEp M T s₀ πdot ε Rdot Ra none = optValueEp M Rdot T s₀ := by
  have h : beliefValueEp M T s₀ πdot ε Rdot Ra none =
      ε * vPiEpisodic M Rdot T πdot s₀ + (1 - ε) * vPiEpisodic M Rdot T πdot s₀ := by
    simp [beliefValueEp, augActionValueEp, vPiEpisodic_augmentMDP, mixPolicy, twistReward,
      liftReward]
  rw [h, optValueEp_eq_of_max M Rdot T s₀ πdot hopt]
  ring

/-! ## Random termination

The episode ends when the process first reaches a terminal state term ⊆ 𝒮;
on M^* the terminal states are the copies term × {0, 1}, since the extra
boolean never changes. -/

/-- **Stopped values on M^* are stopped values on M, copy by copy**, at every
horizon. -/
public theorem vPiStopped_augmentMDP (M : MDP S A) (term : Set S) (r : S × Bool → A → ℝ)
    (T : ℕ) (π : S × Bool → A) (s : S) (b : Bool) :
    vPiStopped (augmentMDP M) (Prod.fst ⁻¹' term) r T π (s, b) =
      vPiStopped M term (fun s a => r (s, b) a) T (fun s => π (s, b)) s := by
  induction T generalizing s with
  | zero => rfl
  | succ T ih =>
    by_cases hs : s ∈ term
    · rw [vPiStopped_of_mem _ _ _ _ (show (s, b) ∈ Prod.fst ⁻¹' term from hs),
        vPiStopped_of_mem _ _ _ _ hs]
    · rw [vPiStopped_succ_of_notMem _ _ _ _ (show (s, b) ∉ Prod.fst ⁻¹' term from hs),
        vPiStopped_succ_of_notMem _ _ _ _ hs]
      simp only [augmentMDP]
      rw [expect_map_of_injective _ (fun a c h => (Prod.mk.inj h).1)]
      congr 2
      funext t
      exact ih t

/-- **Returns up to termination on M^* are returns on M, copy by copy.** No
convergence is assumed: the two stopped sequences agree term by term. -/
public theorem vPiTerm_augmentMDP (M : MDP S A) (term : Set S) (r : S × Bool → A → ℝ)
    (π : S × Bool → A) (s : S) (b : Bool) :
    vPiTerm (augmentMDP M) (Prod.fst ⁻¹' term) r π (s, b) =
      vPiTerm M term (fun s a => r (s, b) a) (fun s => π (s, b)) s := by
  simp only [vPiTerm, vPiStopped_augmentMDP]

/-- **V^*_R(ŝ) under random termination**: the supremum over the deterministic
Markov policies of their return up to termination from the start state. -/
@[expose] public noncomputable def optValueTerm (M : MDP S A) (term : Set S)
    (R : RewardFn S A) (s₀ : S) : ℝ :=
  ⨆ π : S → A, vPiTerm M term R π s₀

/-- A policy maximising the return up to termination at the start state attains
`optValueTerm`. -/
public theorem optValueTerm_eq_of_max (M : MDP S A) (term : Set S) (R : RewardFn S A)
    (s₀ : S) (πa : S → A)
    (hmax : ∀ π : S → A, vPiTerm M term R π s₀ ≤ vPiTerm M term R πa s₀) :
    optValueTerm M term R s₀ = vPiTerm M term R πa s₀ :=
  have : Nonempty (S → A) := ⟨πa⟩
  le_antisymm (ciSup_le hmax) (le_ciSup ⟨_, Set.forall_mem_range.2 hmax⟩ πa)

/-- **The value of an agent action on M^* under random termination**
(amapp-def-state-convention): action 0 (none) starts the human at (ŝ, 0)
and (1, π^a) (some π^a) at (ŝ, 1), the human following the mixed policy
until a terminal state is reached. -/
@[expose] public noncomputable def augActionValueTerm (M : MDP S A) (term : Set S) (s₀ : S)
    (πdot : S → A) (r : S × Bool → A → ℝ) (a : Option (S → A)) : ℝ :=
  vPiTerm (augmentMDP M) (Prod.fst ⁻¹' term) r (mixPolicy πdot (a.getD πdot)) (s₀, a.isSome)

/-- **The agent's expected value under its belief, under random termination**
(amapp-eq2): Ṙ with probability 1 − ε and the twisted Ṙ^a with
probability ε, each evaluated on M^* at the agent's action. -/
@[expose] public noncomputable def beliefValueTerm (M : MDP S A) (term : Set S) (s₀ : S)
    (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A) (a : Option (S → A)) : ℝ :=
  ε * augActionValueTerm M term s₀ πdot (twistReward Rdot Ra) a +
    (1 - ε) * augActionValueTerm M term s₀ πdot (liftReward Rdot) a

/-- **Action (1, π), for any forced policy, under random termination**: the
twisted term is π's return for R^a. -/
public theorem beliefValueTerm_some (M : MDP S A) (term : Set S) (s₀ : S) (πdot : S → A)
    (ε : ℝ) (Rdot Ra : RewardFn S A) (π : S → A) :
    beliefValueTerm M term s₀ πdot ε Rdot Ra (some π) =
      ε * vPiTerm M term Ra π s₀ + (1 - ε) * vPiTerm M term Rdot π s₀ := by
  simp [beliefValueTerm, augActionValueTerm, vPiTerm_augmentMDP, mixPolicy, twistReward,
    liftReward]

/-- **Action 0, under random termination**: both terms are π̇'s return for
Ṙ. -/
public theorem beliefValueTerm_none (M : MDP S A) (term : Set S) (s₀ : S) (πdot : S → A)
    (ε : ℝ) (Rdot Ra : RewardFn S A) :
    beliefValueTerm M term s₀ πdot ε Rdot Ra none =
      ε * vPiTerm M term Rdot πdot s₀ + (1 - ε) * vPiTerm M term Rdot πdot s₀ := by
  simp [beliefValueTerm, augActionValueTerm, vPiTerm_augmentMDP, mixPolicy, twistReward,
    liftReward]

/-- **Equation (2) under random termination** (amapp-eq2, PDF pp. 3-4:
*"(1, π^a) gives ε V^*_{R^a} + (1 − ε) V^{π^a}_Ṙ"*), with the episode ending
at the first terminal state and π^a any policy maximising the return of R^a
up to termination at the start state. No horizon, discount or convergence
hypothesis. -/
public theorem beliefValueTerm_overriding (M : MDP S A) (term : Set S) (s₀ : S)
    (πdot : S → A) (ε : ℝ) (Rdot Ra : RewardFn S A) (πa : S → A)
    (hmax : ∀ π : S → A, vPiTerm M term Ra π s₀ ≤ vPiTerm M term Ra πa s₀) :
    beliefValueTerm M term s₀ πdot ε Rdot Ra (some πa) =
      ε * optValueTerm M term Ra s₀ + (1 - ε) * vPiTerm M term Rdot πa s₀ := by
  rw [beliefValueTerm_some, optValueTerm_eq_of_max M term Ra s₀ πa hmax]

/-- **Action 0 under random termination** (amapp-eq2: *"the agent's action
0 gives expected reward V^*_Ṙ"*): when π̇ maximises the return of Ṙ up to
termination at the start state, the belief's value is V^*_Ṙ. -/
public theorem beliefValueTerm_noop (M : MDP S A) (term : Set S) (s₀ : S) (πdot : S → A)
    (ε : ℝ) (Rdot Ra : RewardFn S A)
    (hopt : ∀ π : S → A, vPiTerm M term Rdot π s₀ ≤ vPiTerm M term Rdot πdot s₀) :
    beliefValueTerm M term s₀ πdot ε Rdot Ra none = optValueTerm M term Rdot s₀ := by
  rw [beliefValueTerm_none, optValueTerm_eq_of_max M term Rdot s₀ πdot hopt]
  ring

/-! ## The fixed horizon as random termination with a clock

Footnote 6's state encoding: put the elapsed time in the state and make every
state at time T or later terminal. The episode then ends after exactly T
steps, and the return up to termination is the T-step value. -/

/-- **M with a clock**: the state carries the elapsed time, which each step
increments. -/
@[expose] public noncomputable def clockMDP (M : MDP S A) : MDP (S × ℕ) A where
  transition x a := (M.transition x.1 a).map fun s => (s, x.2 + 1)

/-- **The stopped value of the clocked MDP at horizon set {k ≥ T}** is the
min n (T − k)-step value of M, for a reward and a policy that ignore the
clock. -/
public theorem vPiStopped_clockMDP (M : MDP S A) (r : RewardFn S A) (π : S → A) (T n : ℕ)
    (s : S) (k : ℕ) :
    vPiStopped (clockMDP M) {x | T ≤ x.2} (fun x a => r x.1 a) n (fun x => π x.1) (s, k) =
      vPiEpisodic M r (min n (T - k)) π s := by
  induction n generalizing s k with
  | zero => simp
  | succ n ih =>
    by_cases hk : T ≤ k
    · rw [vPiStopped_of_mem _ _ _ _ (show (s, k) ∈ {x : S × ℕ | T ≤ x.2} from hk),
        show T - k = 0 by omega, Nat.min_zero, vPiEpisodic_zero]
    · rw [vPiStopped_succ_of_notMem _ _ _ _ (show (s, k) ∉ {x : S × ℕ | T ≤ x.2} from hk),
        show min (n + 1) (T - k) = min n (T - (k + 1)) + 1 by omega, vPiEpisodic_succ]
      simp only [clockMDP]
      rw [expect_map_of_injective _ (fun a c h => (Prod.mk.inj h).1)]
      congr 2
      funext t
      exact ih t (k + 1)

/-- **The fixed horizon is an instance of random termination**: on the clocked
MDP with every state at time T or later terminal, the return up to
termination from time 0 is the T-step value vPiEpisodic M r T π s. -/
public theorem vPiTerm_clockMDP (M : MDP S A) (r : RewardFn S A) (π : S → A) (T : ℕ)
    (s : S) :
    vPiTerm (clockMDP M) {x | T ≤ x.2} (fun x a => r x.1 a) (fun x => π x.1) (s, 0) =
      vPiEpisodic M r T π s := by
  refine vPiTerm_eq_of_tendsto _ _ _ _ _ (tendsto_atTop_of_eventually_const (i₀ := T) ?_)
  intro n hn
  rw [vPiStopped_clockMDP, Nat.sub_zero, Nat.min_eq_right hn]

/-- **Equation (2)'s belief value at a fixed horizon is the clocked
random-termination one**, at every agent action, for the human and override
policies and the rewards lifted to the clocked state. Bridges the
random-termination results to the fixed-horizon ones (`beliefValueEp`). -/
public theorem beliefValueTerm_clockMDP (M : MDP S A) (T : ℕ) (s₀ : S) (πdot : S → A)
    (ε : ℝ) (Rdot Ra : RewardFn S A) (a : Option (S → A)) :
    beliefValueTerm (clockMDP M) {x | T ≤ x.2} (s₀, 0) (fun x => πdot x.1) ε
        (fun x b => Rdot x.1 b) (fun x b => Ra x.1 b) (a.map fun π x => π x.1) =
      beliefValueEp M T s₀ πdot ε Rdot Ra a := by
  cases a with
  | none =>
    rw [Option.map_none, beliefValueTerm_none, beliefValueEp_none, vPiTerm_clockMDP]
  | some π =>
    rw [Option.map_some, beliefValueTerm_some, beliefValueEp_some, vPiTerm_clockMDP,
      vPiTerm_clockMDP]

end AISafetyAtlas.Preference.Episodic
