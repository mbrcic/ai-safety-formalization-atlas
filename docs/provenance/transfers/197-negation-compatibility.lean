import AISafetyAtlas.Preference.Reasonable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Probability.ProbabilityMassFunction.Monad

/-!
Armstrong and Mindermann (2018), NeurIPS 31, §5.2, p. 7: "If `(ṗ, Ṙ)` is
compatible with `π̇`, then so is `(−ṗ, −Ṙ) = f₄(ṗ, Ṙ) = F₄(ṗ, Ṙ)`." A pair
`(p, R)` is compatible with `π̇` when `p(R) = π̇` (§3.2), and `−p(R) = p(−R)`
(Definition 5). Print's planners map the reward tables `S × A → [-1, 1]` to the
deterministic policies `S → A` of an MDP/R with a discrete state space, a finite
action space, a start state and a probabilistic transition function (§3). The
cited declaration is `AISafetyAtlas.Preference.op3_op4` (`op4_op4`, also cited,
states that `f₄` is an involution, which print does not claim here). Its states
and actions are arbitrary types and its rewards unbounded real tables.

The map sends a Lean pair `(p, R)` to an MDP/R with states `Option (S × A)`,
actions `Bool`, deterministic self-loops and start state `none`, and takes the
policy `π̇ := p(R)`. A reward table `r` is coded by squashing each value through
the odd injection `x ↦ arctan x / π` into `(-1/2, 1/2)` (placed at state
`some (s, a)`, either action, and `0` at `none`), so the code commutes with
negation. A policy `π` is coded by the policy that plays `true` at `some (s, a)`
exactly when `π s = a`. The image planner decodes a coded reward, applies `p` and
codes the policy (any other reward goes to the constant `false` policy). (H)
is `p'(code R) = code (p R)`. For (C), print's conclusion
`(−p')(−code R) = p'(−(−code R)) = code (p R)` becomes
`code (p (−(−R))) = code (p R)` by commuting the code with negation twice, and
injectivity of the policy code gives `op3 (op4 (p, R)) = op3 (p, R)`.

reading: "discrete" is read as imposing no cardinality bound on the state space
(as in transfer 075); the map's state space has the cardinality of `S × A`. No
ruling settles this. If "discrete" means countable, the map is a print instance
only for countable `S` and `A`.

Checked: `lake env lean docs/provenance/transfers/197-negation-compatibility.lean`
-/

namespace Transfer197

open AISafetyAtlas.Preference

universe u v w

/-- Print's reward space `ℛ = [-1, 1]^(S × A)`. -/
abbrev PReward (S A : Type*) : Type _ := {R : S × A → ℝ // ∀ sa, R sa ∈ Set.Icc (-1 : ℝ) 1}

/-- The negative `−R` of a print reward. -/
def PReward.neg {S A : Type*} (R : PReward S A) : PReward S A :=
  ⟨fun sa => -R.1 sa, fun sa => ⟨by linarith [(R.2 sa).2], by linarith [(R.2 sa).1]⟩⟩

/-- Definition 5: `−p(R) = p(−R)`. -/
def negPlanner {S A : Type*} (p : PReward S A → (S → A)) : PReward S A → (S → A) :=
  fun R => p R.neg

/-- §5.2 at print's instances: compatibility of `(p, R)` with `π̇` gives
compatibility of `(−p, −R)` with `π̇`. -/
def PrintStatement : Prop :=
  ∀ (S : Type w) (A : Type) [Fintype A] (_T : S → A → PMF S) (_start : S)
    (p : PReward S A → (S → A)) (R : PReward S A) (π : S → A),
    p R = π → negPlanner p R.neg = π

def LeanStatement : Prop :=
  ∀ {S : Type u} {A : Type v} (x : Pair S A), op3 (op4 x) = op3 x

section

variable {S : Type u} {A : Type v}

/-- The odd squashing map into `(-1/2, 1/2)`. -/
noncomputable def sq (x : ℝ) : ℝ := Real.arctan x / Real.pi

theorem sq_mem (x : ℝ) : sq x ∈ Set.Icc (-1 : ℝ) 1 := by
  have h1 := Real.arctan_lt_pi_div_two x
  have h2 := Real.neg_pi_div_two_lt_arctan x
  have hp := Real.pi_pos
  constructor
  · rw [sq, le_div_iff₀ hp]; linarith
  · rw [sq, div_le_iff₀ hp]; linarith

/-- The reward code. -/
noncomputable def codeR (r : RewardFn S A) : PReward (Option (S × A)) Bool :=
  ⟨fun q => q.1.elim 0 (fun sa => sq (r sa.1 sa.2)), fun q => by
    rcases q with ⟨_ | sa, b⟩
    · show (0 : ℝ) ∈ _; norm_num
    · exact sq_mem _⟩

/-- The policy code. -/
noncomputable def codeP (π : S → A) : Option (S × A) → Bool := by
  classical
  exact fun q => q.elim false (fun sa => decide (π sa.1 = sa.2))

theorem codeR_neg (r : RewardFn S A) : (codeR r).neg = codeR (-r) := by
  apply Subtype.ext
  funext q
  rcases q with ⟨_ | sa, b⟩
  · simp [PReward.neg, codeR]
  · simp [PReward.neg, codeR, sq, Real.arctan_neg, neg_div]

theorem codeR_injective : Function.Injective (codeR (S := S) (A := A)) := by
  intro r r' h
  funext s a
  have h1 := congrArg (fun U : PReward (Option (S × A)) Bool => U.1 (some (s, a), true)) h
  simp only [codeR, Option.elim, sq] at h1
  exact Real.arctan_injective ((div_left_inj' Real.pi_ne_zero).mp h1)

theorem codeP_injective : Function.Injective (codeP (S := S) (A := A)) := by
  intro π π' h
  funext s
  have h1 := congrFun h (some (s, π s))
  simp [codeP] at h1
  exact h1.symm

/-- The image planner: decode the reward, apply `p`, code the policy. -/
noncomputable def phiP (p : Planner (RewardFn S A) (Policy S A)) :
    PReward (Option (S × A)) Bool → (Option (S × A) → Bool) := by
  classical
  exact fun U => if h : ∃ r, codeR r = U then codeP (p h.choose) else fun _ => false

theorem phiP_codeR (p : Planner (RewardFn S A) (Policy S A)) (r : RewardFn S A) :
    phiP p (codeR r) = codeP (p r) := by
  have h : ∃ r', codeR r' = codeR r := ⟨r, rfl⟩
  simp only [phiP, dif_pos h]
  rw [codeR_injective h.choose_spec]

/-- (H): the image pair is compatible with the code of `p(R)`. -/
theorem H (x : Pair S A) : phiP x.1 (codeR x.2) = codeP (op3 x) :=
  phiP_codeR x.1 x.2

/-- (C): print's conclusion at the image gives the Lean conclusion. -/
theorem C (x : Pair S A) (h : negPlanner (phiP x.1) (codeR x.2).neg = codeP (op3 x)) :
    op3 (op4 x) = op3 x := by
  simp only [negPlanner, codeR_neg, phiP_codeR] at h
  exact codeP_injective h

end

theorem lean_of_print : PrintStatement.{max u v} → LeanStatement.{u, v} := by
  intro hp S A x
  exact C x (hp (Option (S × A)) Bool (fun s _ => PMF.pure s) none (phiP x.1) (codeR x.2)
    (codeP (op3 x)) (H x))

open Classical in
/-- A print planner, extended to unbounded reward tables by its value at `R`. -/
noncomputable def extend {S A : Type*} (p : PReward S A → (S → A)) (R : PReward S A) :
    Planner (RewardFn S A) (Policy S A) :=
  fun r => if h : ∀ sa : S × A, r sa.1 sa.2 ∈ Set.Icc (-1 : ℝ) 1 then
    p ⟨fun sa => r sa.1 sa.2, h⟩ else p R

theorem print_of_lean : LeanStatement.{w, 0} → PrintStatement.{w} := by
  intro hl S A _ _ _ p R π hπ
  have h := hl (extend p R, fun s a => R.1 (s, a))
  change extend p R (-(-fun s a => R.1 (s, a))) = extend p R (fun s a => R.1 (s, a)) at h
  have h1 : ∀ sa : S × A, (-(-fun s a => R.1 (s, a))) sa.1 sa.2 ∈ Set.Icc (-1 : ℝ) 1 :=
    fun sa => R.neg.neg.2 sa
  have h2 : ∀ sa : S × A, R.1 (sa.1, sa.2) ∈ Set.Icc (-1 : ℝ) 1 := fun sa => R.2 sa
  rw [extend, extend, dif_pos h1, dif_pos h2] at h
  exact h.trans hπ

end Transfer197
