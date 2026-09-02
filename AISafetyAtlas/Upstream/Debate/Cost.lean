/-
Vendored from `google-deepmind/debate` (Apache-2.0) via the Lean v4.31.0 port
`LukaHobor/debate` @ `dafe25d`, and migrated in place to Lean v4.33.0. Changed at
the header, and in proof scripts to build at that toolchain; no statement is
altered, and one `private lemma verabind_cost_eq_zero` is added. Ledger and
rationale: `vendor/debate/PROVENANCE.md`.
-/

module

public import AISafetyAtlas.Upstream.Debate.Comp.Basic
public import AISafetyAtlas.Upstream.Debate.Details
public import AISafetyAtlas.Upstream.Debate.Protocol
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Data.Vector.Basic

@[expose] public section

-- Linters off per `vendor/debate/PROVENANCE.md`; no correctness linter is
-- touched and incomplete proofs stay errors.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.style.longLine false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false

/-!
# Query complexity for each agent in the debate protocol

See `Correct.lean` for the summary.
-/

open Classical
open Prob
open Option (some none)
open Real (log)
open Set
open scoped Real
noncomputable section

variable {i : OracleId}
variable {o : Oracle}
variable {n t : ℕ}
variable {k c s b e p q v : ℝ}

/-!
### Costs for a single player invocation
-/

/-- Alice takes the expected number of samples -/
@[simp] lemma alice_cost {y : List.Vector Bool n} {o : Oracle} :
    (alice c q _ y).cost (fun _ ↦ o) AliceId = samples c q := by
  simp only [alice, alice', Comp.cost_estimate, Comp.cost_query, mul_one]

/-- Bob takes the expected number of samples -/
@[simp] lemma bob_cost {y : List.Vector Bool n} {p : ℝ} {o : Oracle} :
    (bob s b q _ y p).cost (fun _ => o) BobId = samples ((b-s)/2) q := by
  simp only [bob, bob', alice', Comp.cost_bind, Comp.cost_estimate, Comp.cost_query, mul_one,
    Comp.prob_estimate, Comp.prob_query, Comp.cost_pure, exp_const, add_zero]

/-- Vera takes the expected number of samples -/
@[simp] lemma vera_cost {y : List.Vector Bool n} {p : ℝ} {o : Oracle} :
    (vera c s v _ y p).cost (fun _ => o) VeraId = samples ((s-c)/2) v := by
  simp only [vera, bob', alice', Comp.cost_bind, Comp.cost_estimate, Comp.cost_query, mul_one,
    Comp.prob_estimate, Comp.prob_query, Comp.cost_pure, exp_const, add_zero]

/-- The vera-then-error branch costs nothing to anyone but Vera.

`zero_cost` used to discharge this in place. At Lean v4.33 its `rw
[Comp.cost_eq_zero]` no longer matches through the bind, so the bind is peeled
by elaborating `Comp.cost_bind` as a term -- `rw` will not match it either. -/
private lemma verabind_cost_eq_zero {i : OracleId} (m : i ∉ ({VeraId} : Set OracleId))
    (v : Comp {VeraId} Bool) (o : OracleId → Oracle) :
    (v.allow_all >>= fun d => (pure (Except.error d) : Comp Set.univ (Except Bool α))).cost o i
      = 0 := by
  refine (Comp.cost_bind _ _ _ _).trans ?_
  rw [Comp.cost_allow_all, Comp.cost_eq_zero m]
  simp only [Comp.cost_pure, exp_const, add_zero]

/-!
### Alice and Bob cost
-/

/-- Alice makes few queries, regardless of Bob and Vera -/
lemma alice_steps_cost (o : Oracle) (bob : Bob) (vera : Vera) (n : ℕ):
    (steps (alice c q) bob vera n).cost (fun _ ↦ o) AliceId ≤ n * samples c q := by
  induction' n with n h
  · simp only [Nat.zero_eq, steps, CharP.cast_eq_zero, zero_mul]
    exact le_of_eq (Comp.cost_pure _ _ _)
  · simp only [steps, Comp.cost_bind, Nat.cast_succ, add_mul, one_mul]
    refine add_le_add h (exp_le_of_forall_le (fun y m ↦ ?_))
    induction y
    · exact (Comp.cost_pure _ _ _).le.trans (Nat.cast_nonneg _)
    · simp only [step, Comp.sample'_bind, pure_bind, Comp.cost_bind, alice_cost,
        Comp.prob_allow_all, add_le_iff_nonpos_right, Comp.cost_allow_all]
      refine exp_le_of_forall_le fun _ _ ↦ add_nonpos (by zero_cost) ?_
      refine exp_le_of_forall_le fun x m ↦ ?_
      induction x
      · simp only [Bool.false_eq_true, reduceIte, reduceCtorEq, ite_false, Comp.cost_bind, Comp.cost_allow_all, Comp.prob_allow_all,
          Comp.cost_pure, exp_const, add_zero]
        first
          | exact verabind_cost_eq_zero (by not_mem) _ _
          | exact le_of_eq (verabind_cost_eq_zero (by not_mem) _ _)
      · simp only [Bool.false_eq_true, reduceIte, reduceCtorEq, ite_true]
        refine le_of_eq ((Comp.cost_sample _ _ _ _).trans ?_)
        exact exp_eq_zero fun x _ => Comp.cost_pure _ _ _

/-- Bob makes few queries, regardless of Alice and Vera -/
lemma bob_steps_cost (o : Oracle) (alice : Alice) (vera : Vera) (n : ℕ):
    (steps alice (bob s b q) vera n).cost (fun _ ↦ o) BobId ≤ n * samples ((b-s)/2) q := by
  induction' n with n h
  · simp only [Nat.zero_eq, steps, CharP.cast_eq_zero, zero_mul]
    exact le_of_eq (Comp.cost_pure _ _ _)
  · simp only [steps, Comp.cost_bind, Nat.cast_succ, add_mul, one_mul]
    refine add_le_add h (exp_le_of_forall_le (fun y m ↦ ?_))
    induction y
    · exact (Comp.cost_pure _ _ _).le.trans (Nat.cast_nonneg _)
    · simp only [step, Comp.sample'_bind, pure_bind, Comp.cost_bind, Comp.cost_allow_all,
        Comp.prob_allow_all]
      have b0 : ∀ y o, (alice n y).cost o BobId = 0 := by intro _ _; zero_cost
      rw [b0, zero_add]
      refine exp_le_of_forall_le fun _ _ ↦ ?_
      simp only [bob_cost, add_le_iff_nonpos_right]
      refine (exp_eq_zero fun x _ ↦ ?_).le
      induction x
      · simp only [Bool.false_eq_true, reduceIte, reduceCtorEq, ite_false, Comp.cost_bind, Comp.cost_allow_all, Comp.prob_allow_all,
          Comp.cost_pure, exp_const, add_zero]
        exact verabind_cost_eq_zero (by not_mem) _ _
      · simp only [Bool.false_eq_true, reduceIte, reduceCtorEq, ite_true]
        refine (Comp.cost_sample _ _ _ _).trans ?_
        exact exp_eq_zero fun x _ => Comp.cost_pure _ _ _

/-- Alice makes few queries, regardless of Bob and Vera -/
theorem alice_debate_cost (o : Oracle) (bob : Bob) (vera : Vera) (t : ℕ):
    (debate (alice c q) bob vera t).cost' o AliceId ≤ (t+1) * samples c q := by
  simp only [debate, Comp.cost', Comp.cost_bind]
  have e : ((t:ℝ) + 1) * samples c q = (t + 1) * samples c q + 0 := by rw [add_zero]
  rw [e]
  apply add_le_add
  · rw [←Nat.cast_add_one]; apply alice_steps_cost
  · refine exp_le_of_forall_le (fun y m ↦ ?_)
    induction y; repeat simp only [Comp.cost_pure, le_refl]

/-- Bob makes few queries, regardless of Alice and Vera -/
theorem bob_debate_cost (o : Oracle) (alice : Alice) (vera : Vera) (t : ℕ):
    (debate alice (bob s b q) vera t).cost' o BobId ≤ (t+1) * samples ((b-s)/2) q := by
  simp only [debate, Comp.cost', Comp.cost_bind]
  have e : ∀ x, ((t:ℝ) + 1) * samples x q = (t + 1) * samples x q + 0 := by
    simp only [add_zero, forall_const]
  rw [e]
  apply add_le_add
  · rw [←Nat.cast_add_one]; apply bob_steps_cost
  · refine exp_le_of_forall_le (fun y m ↦ ?_)
    induction y; repeat simp only [Comp.cost_pure, le_refl]

/-- Alice makes `O(k^2 t log t)` queries with default parameters -/
theorem alice_fast (k : ℝ) (k0 : 0 < k) (t : ℕ) (bob : Bob) (vera : Vera) :
    let p := Params.defaults k t k0
    (debate (alice p.c p.q) bob vera t).cost' o AliceId ≤
      (t+1) * (5000 * k^2 * Real.log (200 * (t+1)) + 1) := by
  refine le_trans (alice_debate_cost _ _ _ _) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simp only [Params.defaults, samples, ← Real.log_inv]
  generalize hn : (t+1 : ℝ) = n
  field_simp
  simp only [mul_pow, mul_div_assoc (Real.log _), mul_div_right_comm, mul_right_comm _ _ (2 : ℝ)]
  norm_num
  refine le_trans (Nat.ceil_lt_add_one ?_).le (le_of_eq (by ring))
  exact mul_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by linarith))) (by positivity)

/-- Bob makes `O(k^2 t log t)` queries with default parameters -/
theorem bob_fast (k : ℝ) (k0 : 0 < k) (t : ℕ) (alice : Alice) (vera : Vera) :
    let p := Params.defaults k t k0
    (debate alice (bob p.s p.b p.q) vera t).cost' o BobId ≤
      (t+1) * (20000 / 9 * k^2 * Real.log (200 * (t+1)) + 1) := by
  generalize hd : (20000 / 9 : ℝ) = d
  refine le_trans (bob_debate_cost _ _ _ _) ?_
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  simp only [Params.defaults, samples, ← Real.log_inv]
  generalize hn : (t+1 : ℝ) = n
  field_simp
  simp only [mul_pow, mul_div_assoc (Real.log _), mul_div_right_comm, mul_right_comm _ _ (2 : ℝ)]
  norm_num
  simp only [hd, mul_comm (Real.log _)]
  refine le_trans (Nat.ceil_lt_add_one ?_).le (le_of_eq (by ring))
  exact mul_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by linarith))) (by positivity)
/-!
### Vera cost

Vera runs at most once, so we transpose the algorithm to make that obvious before doing the
cost calculation.
-/

/-- State for use by Vera at the end -/
def StateV (n : ℕ) := Except (Σ n : ℕ, List.Vector Bool n × ℝ) (List.Vector Bool n)

/-- One step of the debate protocol, without Vera
    c and s are the completeness and soundness parameters of the verifier. -/
def stepV (alice : Alice) (bob : Bob) (y : List.Vector Bool n) :
    Comp {AliceId,BobId} (StateV (n+1)) := do
  let p ← (alice _ y).allow (by subset)
  if ←(bob _ y p).allow (by subset) then do  -- Bob accepts Alice's probability, so take the step
    let x ← bernoulli p  -- This is Figure 4, steps 2b,2c,2d, as a fixed part of the protocol
    return .ok (y.cons x)
  else  -- Bob rejects, so we record verifier inputs and end the computation
    return .error ⟨_,y,p⟩

/-- `n` steps of the debate protocol, without Vera -/
def stepsV (alice : Alice) (bob : Bob) : (n : ℕ) → Comp {AliceId,BobId} (StateV n)
| 0 => pure (.ok List.Vector.nil)
| n+1 => do match ←stepsV alice bob n with
  | .ok y => stepV alice bob y
  | .error r => return .error r

/-- Turn `StateV` into `State` with a Vera call -/
def postV (vera : Vera) (x : StateV n) : Comp AllIds (State n) := match x with
| .ok y => return .ok y
| .error ⟨_,y,p⟩ => return .error (←(vera _ y p).allow_all)

/-- Relate `stepsV` and `steps `-/
lemma post_stepsV (alice : Alice) (bob : Bob) (vera : Vera) :
    (stepsV alice bob n).allow_all >>= postV vera = steps alice bob vera n := by
  induction' n with n h
  · rfl
  · simp only [stepsV, Comp.allow_all_bind, bind_assoc, steps, ← h]
    apply congr_arg₂ _ rfl ?_
    ext x; induction' x with n y p
    · -- `dsimp only` iota-reduces the match on the literal constructor. Every
      -- rewrite here is then applied as a term: new in v4.33, `rw` first checks
      -- that the target is type-correct at `implicit` transparency, and the type
      -- synonyms `StateV` and `State` do not unfold there, so it refuses before
      -- matching any pattern. Elaboration unifies up to defeq and is unaffected.
      dsimp only
      refine (congrArg (· >>= postV vera) (Comp.allow_all_pure _)).trans ?_
      refine (pure_bind _ _).trans ?_
      simp only [postV]
      exact Eq.symm ((bind_assoc _ _ _).trans (bind_congr fun x => pure_bind _ _))
    · simp only [stepV, Comp.sample'_bind, pure_bind, Comp.allow_all_bind, Comp.allow_all_allow,
        bind_assoc, postV, step]
      apply congr_arg₂ _ rfl ?_; ext p; apply congr_arg₂ _ rfl ?_; ext b
      induction b
      · rfl
      · simp only [Bool.false_eq_true, reduceIte, reduceCtorEq, ite_true]
        rfl

/-- Vera makes few queries, regardless of Alice and Bob -/
theorem vera_debate_cost (o : Oracle) (alice : Alice) (bob : Bob) (t : ℕ):
    (debate alice bob (vera c s v) t).cost' o VeraId ≤ samples ((s-c)/2) v := by
  have z : (stepsV alice bob (t+1)).cost (fun _ ↦ o) VeraId = 0 := by zero_cost
  simp only [Comp.cost', debate, ← post_stepsV, bind_assoc, Comp.cost_bind, Comp.cost_allow_all, z,
    Comp.prob_allow_all, zero_add, ge_iff_le]
  refine exp_le_of_forall_le fun x _ ↦ ?_
  refine le_trans (add_le_of_nonpos_right ?_) ?_
  · refine exp_le_of_forall_le fun x _ ↦ ?_
    induction x; repeat simp only [Comp.cost_pure, le_refl]
  · simp only [postV]
    induction x
    · refine le_of_eq ((Comp.cost_bind _ _ _ _).trans ?_)
      rw [Comp.cost_allow_all, vera_cost]
      exact add_eq_left.mpr (exp_eq_zero fun x _ => Comp.cost_pure _ _ _)
    · exact (Comp.cost_pure _ _ _).le.trans (Nat.cast_nonneg _)

/-- A calculation used in `vera_fast` -/
lemma log_200_mul_20000_le : Real.log 200 * 20000 ≤ 106000 := by
  rw [← le_div_iff₀ (by norm_num), Real.log_le_iff_le_exp (by norm_num)]
  norm_num
  rw [← Real.exp_one_rpow, div_eq_mul_inv, Real.rpow_mul (by positivity),
    Real.le_rpow_inv_iff_of_pos (by norm_num) (by positivity) (by norm_num)]
  refine le_trans ?_ (Real.rpow_le_rpow (by norm_num) Real.exp_one_gt_d9.le (by norm_num))
  norm_num

/-- Vera makes `O(k^2)` queries with default parameters -/
theorem vera_fast (k : ℝ) (k0 : 0 < k) (t : ℕ) (alice : Alice) (bob : Bob) :
    let p := Params.defaults k t k0
    (debate alice bob (vera p.c p.s p.v) t).cost' o VeraId ≤ 106000 * k^2 + 1 := by
  refine le_trans (vera_debate_cost _ _ _ _) ?_
  simp only [Params.defaults, samples, ← Real.log_inv]
  field_simp
  refine le_trans (Nat.ceil_lt_add_one (by positivity)).le ?_
  simp only [mul_pow, mul_div_assoc (Real.log _), mul_div_right_comm, mul_right_comm _ _ (2 : ℝ)]
  norm_num [← mul_assoc]
  rw [mul_comm (k ^ 2) 106000]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  linarith [log_200_mul_20000_le]
