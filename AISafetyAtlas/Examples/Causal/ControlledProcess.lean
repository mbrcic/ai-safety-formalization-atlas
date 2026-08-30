module

public import AISafetyAtlas.Causal.ControlledProcess

/-!
# The two separated environments MAIS-O33's candidate turns on

`AISafetyAtlas.Causal.ControlledProcess` renders MAIS-A2's environment. This
module runs it on the pair MAIS issue
[#9](https://github.com/lionellevine/MAIS/issues/9) constructs, and checks the
arithmetic the candidate's impossibility step rests on.

Two kernels on `m + 2` states and two actions agree everywhere except the row
`(0, 0)`, where one sends mass `1/10` to state `1` and spreads `9/10` over the
rest, and the other does the reverse. Then:

* every entry is positive, so both are **communicating** — the condition print
  imposes, obtained here in one step;
* the two are `4/5` apart at `(0, 0, 1)`, which is the separation;
* at `n = 101` and `δ = 1/2` the reconstruction radius is `2/√50`, and
  `2 · 2/√50 < 4/5`, so the two required balls are **disjoint**.

## Why `δ = 1/2` and not `δ = 0`

The candidate takes `δ = 0`, which makes its agents exactly optimal and forces
an optimal-policy-existence theorem for reachability on a finite process —
absent from Mathlib, and the largest single dependency in the layer. Print
admits any `δ ∈ [0,1)` with `(n-1)(1-δ) > 4`, and `radius_admissible_at_101_half`
records that `δ = 1/2` at `n = 101` is admissible while
`balls_disjoint_at_101_half` records that the separation still works there. At
`δ > 0` the bounded agents can be built by approximating the supremum rather
than attaining it. See `docs/provenance/mais-o33-statability.md`.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Causal.ControlledProcess

open AISafetyAtlas.Causal

/-! ## The pair -/

/-- The kernel: uniform everywhere except the row `(0, 0)`, where mass `p` goes
to state `1` and `1 - p` is spread over the other `m + 1` states. -/
@[expose] public noncomputable def kern (m : ℕ) (p : ℝ) :
    Fin (m + 2) → Fin 2 → Fin (m + 2) → ℝ :=
  fun s a s' ↦
    if s = 0 ∧ a = 0 then (if s' = 1 then p else (1 - p) / (m + 1))
    else 1 / (m + 2)

/-- The controlled Markov process it defines, for any `p` strictly between zero
and one. -/
@[expose] public noncomputable def env (m : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    ControlledMarkovProcess (Fin (m + 2)) (Fin 2) where
  prob := kern m p
  prob_nonneg := by
    intro s a s'
    unfold kern
    have hm : (0 : ℝ) < m + 1 := by positivity
    have hm2 : (0 : ℝ) < m + 2 := by positivity
    split_ifs
    · exact hp0.le
    · positivity
    · positivity
  prob_sum := by
    intro s a
    unfold kern
    by_cases h : s = 0 ∧ a = 0
    · simp only [if_pos h]
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (1 : Fin (m + 2)))]
      have hc : ∀ s' ∈ (Finset.univ : Finset (Fin (m + 2))).erase 1,
          (if s' = 1 then p else (1 - p) / (m + 1)) = (1 - p) / (m + 1) := by
        intro s' hs'
        rw [if_neg (Finset.ne_of_mem_erase hs')]
      rw [Finset.sum_congr rfl hc, Finset.sum_const, if_pos rfl,
        Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      have hm : (m : ℝ) + 1 ≠ 0 := by positivity
      have hcast : ((m + 2 - 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
        push_cast [Nat.add_sub_cancel]
        ring
      rw [hcast]
      field_simp
      ring
    · simp only [if_neg h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hm2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp

/-- Every entry is positive. -/
public theorem fullSupport (m : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (env m p hp0 hp1).FullSupport := by
  intro s a s'
  show 0 < kern m p s a s'
  unfold kern
  have hm : (0 : ℝ) < m + 1 := by positivity
  have hm2 : (0 : ℝ) < m + 2 := by positivity
  split_ifs
  · exact hp0
  · exact div_pos (by linarith) hm
  · positivity

/-- **Both environments are communicating**, which is print's condition on the
instances MAIS-O33 quantifies over. -/
public theorem communicating (m : ℕ) (p : ℝ) (hp0 : 0 < p) (hp1 : p < 1) :
    (env m p hp0 hp1).Communicating :=
  ControlledMarkovProcess.communicating_of_fullSupport (fullSupport m p hp0 hp1)

/-- The first world: `P⁰(1 ∣ 0, 0) = 1/10`. -/
@[expose] public noncomputable def env0 (m : ℕ) :
    ControlledMarkovProcess (Fin (m + 2)) (Fin 2) :=
  env m (1 / 10) (by norm_num) (by norm_num)

/-- The second world: `P¹(1 ∣ 0, 0) = 9/10`. -/
@[expose] public noncomputable def env1 (m : ℕ) :
    ControlledMarkovProcess (Fin (m + 2)) (Fin 2) :=
  env m (9 / 10) (by norm_num) (by norm_num)

/-- **The separation**: the two kernels are `4/5` apart at `(0, 0, 1)`. -/
public theorem separated (m : ℕ) : (env0 m).SeparatedBy (env1 m) (4 / 5) := by
  refine ⟨0, 0, 1, ?_⟩
  show (4 : ℝ) / 5 ≤ |kern m (1 / 10) 0 0 1 - kern m (9 / 10) 0 0 1|
  unfold kern
  norm_num

/-! ## The reconstruction radius at `n = 101`, `δ = 1/2` -/

/-- The instance is admissible: `(n-1)(1-δ) = 50 > 4`. -/
public theorem radius_admissible_at_101_half :
    4 < ((101 : ℝ) - 1) * (1 - 1 / 2) := by norm_num

/-- `√50 > 5`, which is the only estimate the radius needs. -/
public theorem five_lt_sqrt_fifty : (5 : ℝ) < Real.sqrt 50 := by
  have h : (5 : ℝ) = Real.sqrt 25 := by
    rw [show (25 : ℝ) = 5 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- **The two reconstruction balls are disjoint at `δ = 1/2`**, so the candidate
does not need `δ = 0` — and therefore does not need the attainment theorem that
`δ = 0` forces. -/
public theorem balls_disjoint_at_101_half :
    2 * reconstructionRadius 101 (1 / 2) < 4 / 5 := by
  have hs : (0 : ℝ) < Real.sqrt 50 := lt_trans (by norm_num) five_lt_sqrt_fifty
  have hval : reconstructionRadius 101 (1 / 2) = 2 / Real.sqrt 50 := by
    unfold reconstructionRadius
    norm_num
  rw [hval, show (2 : ℝ) * (2 / Real.sqrt 50) = 4 / Real.sqrt 50 by ring,
    div_lt_div_iff₀ hs (by norm_num : (0 : ℝ) < 5)]
  linarith [five_lt_sqrt_fifty]

/-- No estimate can serve both worlds at that radius, so a single output law
cannot succeed with probability `2/3` in both. -/
public theorem no_common_estimate (m : ℕ) {Q : Fin (m + 2) → Fin 2 → Fin (m + 2) → ℝ}
    (h0 : (env0 m).WithinBall Q (reconstructionRadius 101 (1 / 2)))
    (h1 : (env1 m).WithinBall Q (reconstructionRadius 101 (1 / 2))) : False :=
  ControlledMarkovProcess.not_withinBall_both (separated m) balls_disjoint_at_101_half h0 h1

end AISafetyAtlas.Examples.Causal.ControlledProcess
