import AISafetyAtlas.Preference
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
Armstrong and Mindermann (2018), NeurIPS 31, Theorem 1, second paragraph,
p. 4. For every planner `p` and every policy `π` in the image of `p`, some
reward `R` satisfies `p(R) = π`. Rewards are the tables
`S × A → [-1, 1]` and policies the deterministic Markov maps `S → A` of an
MDP/R with a discrete state space, a finite action space, a start state and a
probabilistic transition function (§3, p. 3). The cited theorem is
`AISafetyAtlas.Preference.exists_reward`.

The map builds an MDP/R with Boolean actions, the state type
`Option (R ⊕ B)`, start state `none` and deterministic self-loops. A reward
`r` is encoded by the table equal to `1` at its tagged state and `0`
elsewhere; a behaviour `b` by the policy that plays `true` exactly at its
tagged state. The printed planner decodes an encoded reward, applies `p` and
encodes the result; on any other reward it returns the constant `false`
policy, which no behaviour encodes. The printed policy is the code of `b`.
The image premise transfers through the code of a preimage. A printed
witness reward must be encoded, and injectivity of the behaviour code turns
it into a Lean witness.

"Discrete" is read as imposing no cardinality bound on the state space
(finiteness of the state space is not stated, p. 3); the map's state space
has the cardinality of `R ⊕ B`. No ruling settles this reading. If
"discrete" means countable, the map is a print instance only for countable
`R` and `B`, and the transfer is not shown in general.

Checked: `lake env lean docs/provenance/transfers/075-planner-image-reward.lean`
-/

namespace Transfer075

open AISafetyAtlas.Preference

universe u v w

/-- Print's reward space `[-1, 1]^(S × A)`. -/
abbrev Reward (S : Type w) (A : Type) : Type w := S × A → Set.Icc (-1 : ℝ) 1

def PrintStatement : Prop :=
  ∀ (S : Type w) (A : Type) [Fintype A] (_T : S → A → PMF S) (_start : S)
    (p : Reward S A → (S → A)) (π : S → A), π ∈ Set.range p → ∃ R, p R = π

def LeanStatement : Prop :=
  ∀ {R : Type u} {B : Type v} (p : Planner R B) (b : B),
    b ∈ Set.range p → ∃ r : R, Explains p r b

section

variable {R : Type u} {B : Type v}

/-- The map's state space. -/
abbrev St (R : Type u) (B : Type v) : Type (max u v) := Option (R ⊕ B)

noncomputable def encReward (r : R) : Reward (St R B) Bool := by
  classical
  exact fun q ↦ if q.1 = some (Sum.inl r) then ⟨1, by norm_num⟩ else ⟨0, by norm_num⟩

noncomputable def encPolicy (b : B) : St R B → Bool := by
  classical
  exact fun s ↦ decide (s = some (Sum.inr b))

theorem encReward_injective : Function.Injective (encReward (R := R) (B := B)) := by
  intro r r' h
  have h1 := congrFun h (some (Sum.inl r), true)
  by_contra hne
  have hne' : (some (Sum.inl r) : St R B) ≠ some (Sum.inl r') := by simpa using hne
  simp [encReward, hne'] at h1

theorem encPolicy_injective : Function.Injective (encPolicy (R := R) (B := B)) := by
  intro b b' h
  have h1 := congrFun h (some (Sum.inr b))
  simpa [encPolicy] using h1.symm

theorem encPolicy_ne_const (b : B) : encPolicy (R := R) b ≠ fun _ ↦ false := by
  intro h
  have h1 := congrFun h (some (Sum.inr b))
  simp [encPolicy] at h1

/-- The printed planner of the map. -/
noncomputable def phiPlanner (p : Planner R B) : Reward (St R B) Bool → (St R B → Bool) := by
  classical
  exact fun Q ↦ if h : ∃ r, encReward r = Q then encPolicy (p h.choose) else fun _ ↦ false

/-- The map: environment with self-loops and start `none`, the planner above, and the code
of `b`. -/
noncomputable def phi (p : Planner R B) (b : B) :
    (St R B → Bool → PMF (St R B)) × St R B ×
      (Reward (St R B) Bool → (St R B → Bool)) × (St R B → Bool) :=
  (fun s _ ↦ PMF.pure s, none, phiPlanner p, encPolicy b)

theorem phiPlanner_enc (p : Planner R B) (r : R) :
    phiPlanner p (encReward r) = encPolicy (p r) := by
  have h : ∃ r', encReward r' = encReward (B := B) r := ⟨r, rfl⟩
  simp only [phiPlanner, dif_pos h]
  rw [encReward_injective h.choose_spec]

theorem H (p : Planner R B) (b : B) (hb : b ∈ Set.range p) :
    (phi p b).2.2.2 ∈ Set.range (phi p b).2.2.1 := by
  obtain ⟨r, rfl⟩ := hb
  exact ⟨encReward r, phiPlanner_enc p r⟩

theorem C (p : Planner R B) (b : B)
    (h : ∃ Q, (phi p b).2.2.1 Q = (phi p b).2.2.2) : ∃ r : R, Explains p r b := by
  obtain ⟨Q, hQ⟩ := h
  change phiPlanner p Q = encPolicy b at hQ
  by_cases hdec : ∃ r, encReward r = Q
  · obtain ⟨r, rfl⟩ := hdec
    rw [phiPlanner_enc] at hQ
    exact ⟨r, encPolicy_injective hQ⟩
  · simp only [phiPlanner, dif_neg hdec] at hQ
    exact (encPolicy_ne_const b hQ.symm).elim

end

theorem lean_of_print : PrintStatement.{max u v} → LeanStatement.{u, v} := by
  intro hp R B p b hb
  exact C p b (hp (St R B) Bool (phi p b).1 (phi p b).2.1 (phi p b).2.2.1
    (phi p b).2.2.2 (H p b hb))

theorem print_of_lean : LeanStatement.{w, w} → PrintStatement.{w} := by
  intro hl S A _ _ _ p π hπ
  exact hl p π hπ

end Transfer075
