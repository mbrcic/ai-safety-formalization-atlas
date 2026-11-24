import AISafetyAtlas.Preference
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
Armstrong and Mindermann (2018), NeurIPS 31, §5.1.1, p. 5. "For any given
policy `π`, we can define the indifferent planner `p_π`, which maps any reward
function to `π`. We can also define the reward function `R_π`, so that
`R_π(s, a) = 1` if `π(s) = a`, and `R_π(s, a) = 0` otherwise." Rewards are the
tables `S × A → [-1, 1]` and policies the deterministic Markov maps `S → A` of
an MDP/R with a discrete state space, a finite action space, a start state
and a probabilistic transition function (§3, p. 3). The cited definitions are
`AISafetyAtlas.Preference.indifferentPlanner` and
`AISafetyAtlas.Preference.rewardOf`.

Each definition is compared through its defining clause: `p` is the
indifferent planner of `b` when `p r = b` for every `r`, and `ρ` is the
indicator reward of `π` when `ρ(s, a) = [a = π s]` for every `(s, a)`. The map
has one part per definition (G12 applied to each), each a single map of the
definition's input and candidate.

* Planner, at `(b, p)`: as in transfer 075, the MDP/R with states `R ⊕ B`,
  Boolean actions, start state `inr b` and self-loops. A reward `r` is coded by
  the table equal to `1` at its tagged state and `0` elsewhere, a behaviour
  `b'` by the policy playing `true` exactly at its tagged state (both codes
  injective). The printed planner decodes a coded reward, applies `p` and codes
  the result; on any other reward it returns the code of `b`.
* Indicator reward, at `(π, ρ)`: the MDP/R with states `Option (S × A)`,
  Boolean actions, start state `none` and self-loops. The state `(s, a)` holds
  a candidate action and the action `true` plays it; the printed policy plays
  `true` at `(s, a)` exactly when `π s = a`, so it is `π` read on candidates.
  The printed reward at `((s, a), true)` is `ρ(s, a)` (values outside
  `[-1, 1]` go to `1/2`, which is neither `0` nor `1`); elsewhere it is print's
  `R_π` of the printed policy, as no original value corresponds there.
  Print's clause at `((s, a), true)` is the Lean clause at `(s, a)`.

Reading (no ruling settles it): "discrete" is read as imposing no cardinality
bound on the state space (as in transfer 075). The printed `-R_π` is not a
cited declaration and is not transferred. The forward direction is given for
the indicator reward (print's `R_π` is `rewardOf`); for the planner it is
definitional at `R := Reward S A`, `B := S → A`.

Checked: `lake env lean docs/provenance/transfers/175-indifferent-planner-indicator.lean`
-/

namespace Transfer175

open AISafetyAtlas.Preference Classical

universe u v w x

/-- Print's reward space `[-1, 1]^(S × A)`. -/
abbrev Reward (S : Type u) (A : Type v) : Type (max u v) := S × A → Set.Icc (-1 : ℝ) 1

/-- Print's MDP/R: a start state and a probabilistic transition function, finite actions. -/
structure MDPR (S : Type u) (A : Type v) [Finite A] where
  start : S
  T : S → A → PMF S

/-- Print's indifferent planner `p_π`. -/
def printIndifferent {S : Type u} {A : Type v} [Finite A] (_M : MDPR S A) (π : S → A) :
    Reward S A → (S → A) := fun _ ↦ π

/-- Print's policy-indicator reward `R_π`. -/
noncomputable def printReward {S : Type u} {A : Type v} [Finite A] (_M : MDPR S A)
    (π : S → A) : Reward S A :=
  fun z ↦ if π z.1 = z.2 then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

/-- Print's two defining clauses at printed instances: `p` is `p_π₁`, `R` is `R_π₂`. -/
def PrintStatement {S₁ S₂ A₁ A₂ : Type*} [Finite A₁] [Finite A₂]
    (M₁ : MDPR S₁ A₁) (π₁ : S₁ → A₁) (p : Reward S₁ A₁ → (S₁ → A₁))
    (M₂ : MDPR S₂ A₂) (π₂ : S₂ → A₂) (R : Reward S₂ A₂) : Prop :=
  (∀ Rw, p Rw = printIndifferent M₁ π₁ Rw) ∧ ∀ z, (R z : ℝ) = printReward M₂ π₂ z

def LeanStatement {R : Type u} {B : Type v} {S : Type w} {A : Type x} [DecidableEq A]
    (b : B) (p : Planner R B) (π : S → A) (ρ : RewardFn S A) : Prop :=
  (∀ r, p r = indifferentPlanner b r) ∧ ∀ s a, ρ s a = rewardOf π s a

section

variable {R : Type u} {B : Type v} {S : Type w} {A : Type x} [DecidableEq A]

noncomputable def encReward (r : R) : Reward (R ⊕ B) Bool :=
  fun z ↦ if z.1 = Sum.inl r then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

theorem encReward_injective : Function.Injective (encReward (R := R) (B := B)) := by
  intro r r' h
  by_contra hne
  have h1 := congrFun h (Sum.inl r, true)
  have hne' : (Sum.inl r : R ⊕ B) ≠ Sum.inl r' := by simpa using hne
  simp [encReward, hne'] at h1

noncomputable def encPolicy (b : B) : R ⊕ B → Bool := fun z ↦ decide (z = Sum.inr b)

theorem encPolicy_injective : Function.Injective (encPolicy (R := R) (B := B)) := by
  intro b b' h
  simpa [encPolicy] using congrFun h (Sum.inr b)

/-- The planner part of the map: environment, policy code of `b`, printed planner. -/
noncomputable def phiPlannerMDP (b : B) : MDPR (R ⊕ B) Bool :=
  ⟨Sum.inr b, fun z _ ↦ PMF.pure z⟩

noncomputable def phiPlanner (b : B) (p : Planner R B) :
    Reward (R ⊕ B) Bool → (R ⊕ B → Bool) :=
  fun Q ↦ if h : ∃ r, encReward r = Q then encPolicy (p h.choose) else encPolicy b

theorem defining_planner (b : B) (p : Planner R B) :
    (∀ r, p r = indifferentPlanner b r) ↔
      ∀ Q, phiPlanner b p Q = printIndifferent (phiPlannerMDP b) (encPolicy b) Q := by
  constructor
  · intro h Q
    unfold phiPlanner printIndifferent
    split_ifs with hQ
    · rw [h]; rfl
    · rfl
  · intro h r
    have hr := h (encReward r)
    have he : ∃ r', encReward (B := B) r' = encReward r := ⟨r, rfl⟩
    simp only [phiPlanner, printIndifferent, dif_pos he] at hr
    rw [← encReward_injective he.choose_spec]
    exact encPolicy_injective hr

/-- The indicator part of the map: candidate-action states and the policy `π` on them. -/
noncomputable def phiRewardMDP : MDPR (Option (S × A)) Bool := ⟨none, fun z _ ↦ PMF.pure z⟩

def phiPolicy (π : S → A) : Option (S × A) → Bool
  | some (s, a) => decide (π s = a)
  | none => false

noncomputable def clamp (y : ℝ) : Set.Icc (-1 : ℝ) 1 :=
  if h : y ∈ Set.Icc (-1 : ℝ) 1 then ⟨y, h⟩ else ⟨1 / 2, by norm_num⟩

theorem clamp_ind (y : ℝ) (c : Prop) [Decidable c] :
    ((clamp y : ℝ) = if c then 1 else 0) ↔ y = if c then 1 else 0 := by
  unfold clamp
  split_ifs with h1 h2 h2
  · rfl
  · rfl
  · exact ⟨fun e ↦ by norm_num at e, fun e ↦ (h1 (by rw [e]; norm_num)).elim⟩
  · exact ⟨fun e ↦ by norm_num at e, fun e ↦ (h1 (by rw [e]; norm_num)).elim⟩

noncomputable def phiReward (π : S → A) (ρ : RewardFn S A) : Reward (Option (S × A)) Bool
  | (some (s, a), true) => clamp (ρ s a)
  | z => printReward phiRewardMDP (phiPolicy π) z

theorem defining_reward (π : S → A) (ρ : RewardFn S A) :
    (∀ s a, ρ s a = rewardOf π s a) ↔
      ∀ z, (phiReward π ρ z : ℝ) = printReward phiRewardMDP (phiPolicy π) z := by
  have key : ∀ s a, ((phiReward π ρ (some (s, a), true) : ℝ) =
      printReward phiRewardMDP (phiPolicy π) (some (s, a), true)) ↔
        ρ s a = rewardOf π s a := by
    intro s a
    have hp : (phiPolicy π (some (s, a)) = true) ↔ a = π s := by
      simp [phiPolicy, eq_comm]
    simp only [phiReward, printReward, rewardOf]
    rw [apply_ite (fun t : Set.Icc (-1 : ℝ) 1 ↦ (t : ℝ)), clamp_ind]
    simp only [hp]
  refine ⟨fun h z ↦ ?_, fun h s a ↦ (key s a).mp (h _)⟩
  rcases z with ⟨_ | ⟨s, a⟩, _ | _⟩
  · rfl
  · rfl
  · rfl
  · exact (key s a).mpr (h s a)

theorem lean_of_print (b : B) (p : Planner R B) (π : S → A) (ρ : RewardFn S A) :
    PrintStatement (phiPlannerMDP b) (encPolicy b) (phiPlanner b p)
      phiRewardMDP (phiPolicy π) (phiReward π ρ) →
    LeanStatement b p π ρ :=
  fun h ↦ ⟨(defining_planner b p).mpr h.1, (defining_reward π ρ).mpr h.2⟩

end

/-- Forward direction for the indicator part: print's `R_π` is `rewardOf`. -/
theorem print_of_lean_reward {S : Type u} {A : Type v} [Finite A] [DecidableEq A]
    (M : MDPR S A) (π : S → A) (s : S) (a : A) :
    (printReward M π (s, a) : ℝ) = rewardOf π s a := by
  simp only [printReward, rewardOf, eq_comm (a := π s)]
  split_ifs <;> rfl

end Transfer175
