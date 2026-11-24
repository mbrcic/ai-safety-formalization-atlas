module

public import AISafetyAtlas.InformationTheory.CountableDataProcessing
public import AISafetyAtlas.Examples.InformationTheory.DataProcessing

/-!
# Data processing at a countable alphabet of finite entropy — witness

The truth is the flip count itself: the identity on ℕ under the geometric law
`AISafetyAtlas.Examples.InformationTheory.flipLaw` (Cover & Thomas, Problem 2.1,
shifted to start at 0). It takes every natural number, so no `FiniteRange`
statement applies to it (`AISafetyAtlas.Examples.InformationTheory.not_finiteRange_id_nat`),
and its entropy series converges (Problem 2.1 puts it at 2 bits). The observation is half the
count, rounded down, and the estimate is a quarter of it, a function of the
observation, so truth, observation and estimate form a Markov chain.
-/

namespace AISafetyAtlas.Examples.InformationTheory

open MeasureTheory ProbabilityTheory Real Function

/-- The flip count has finite entropy: its entropy series converges. -/
public theorem summable_negMulLog_flipLaw :
    Summable fun n : ℕ => negMulLog ((flipLaw.map (id : ℕ → ℕ)).real {n}) := by
  have hterm : ∀ n : ℕ, negMulLog ((flipLaw.map (id : ℕ → ℕ)).real {n})
      = log 2 / 2 * ((n : ℝ) ^ 1 * (1 / 2 : ℝ) ^ n) + log 2 / 2 * (1 / 2 : ℝ) ^ n := by
    intro n
    rw [Measure.map_id, geometricMeasure_real_singleton (by simp [Subtype.ext_iff])]
    simp only [negMulLog, pow_one]
    rw [show (1 - (1 / 2 : ℝ)) ^ n * (1 / 2) = ((1 / 2 : ℝ)) ^ (n + 1) by ring, log_pow,
      one_div, log_inv]
    push_cast
    ring
  simp only [hterm]
  have hr : ‖(1 / 2 : ℝ)‖ < 1 := by norm_num
  exact ((summable_pow_mul_geometric_of_norm_lt_one 1 hr).mul_left _).add
    ((summable_geometric_of_norm_lt_one hr).mul_left _)

/-- Data processing in entropy form at the flip count, Cover & Thomas (2.130)'s
second inequality with an infinite-alphabet truth of finite entropy: knowing a
quarter of the count leaves at least as much uncertainty about it as knowing
half. An instance of
`AISafetyAtlas.InformationTheory.condEntropy_le_condEntropy_of_isMarkovChain_of_summable`,
outside `AISafetyAtlas.InformationTheory.condEntropy_le_condEntropy_of_isMarkovChain_countable`. -/
public theorem condEntropy_flipCount_half_le_quarter :
    H[(id : ℕ → ℕ) | (fun n : ℕ => n / 2) ; flipLaw]
      ≤ H[(id : ℕ → ℕ) | (fun n : ℕ => n / 2 / 2) ; flipLaw] :=
  AISafetyAtlas.InformationTheory.condEntropy_le_condEntropy_of_isMarkovChain_of_summable
    flipLaw measurable_id Measurable.of_discrete Measurable.of_discrete
    summable_negMulLog_flipLaw
    (AISafetyAtlas.InformationTheory.isMarkovChain_comp_countable (X := (id : ℕ → ℕ))
      (Measurable.of_discrete (f := fun n : ℕ => n / 2)) (fun m : ℕ => m / 2))

/-! ## Each lemma of the chain at the flip count

Every intermediate statement of
`AISafetyAtlas.InformationTheory.condEntropy_le_condEntropy_of_isMarkovChain_of_summable`,
instantiated with the infinite-range truth `id` under `flipLaw`.
-/

/-- `AISafetyAtlas.InformationTheory.negMulLog_tsum_le` on the tail of the
flip-count masses (counts at least 1, total mass 1/2): lumping the tail into one
mass does not raise its entropy contribution. -/
public theorem negMulLog_tsum_flipLaw_tail_le :
    negMulLog (∑' n : ℕ, (flipLaw.map (id : ℕ → ℕ)).real {n + 1})
      ≤ ∑' n : ℕ, negMulLog ((flipLaw.map (id : ℕ → ℕ)).real {n + 1}) :=
  AISafetyAtlas.InformationTheory.negMulLog_tsum_le (fun _ => measureReal_nonneg)
    ((AISafetyAtlas.InformationTheory.summable_measureReal_map_singleton
      (μ := flipLaw) (id : ℕ → ℕ)).comp_injective Nat.succ_injective)
    (summable_negMulLog_flipLaw.comp_injective Nat.succ_injective)

/-- `AISafetyAtlas.InformationTheory.entropy_eq_tsum` at the flip count. -/
public theorem entropy_flipLaw_eq_tsum :
    H[(id : ℕ → ℕ) ; flipLaw] = ∑' n : ℕ, negMulLog ((flipLaw.map (id : ℕ → ℕ)).real {n}) :=
  AISafetyAtlas.InformationTheory.entropy_eq_tsum id

/-- `AISafetyAtlas.InformationTheory.summable_negMulLog_of_finiteRange` at the
parity of the flip count. -/
public theorem summable_negMulLog_natParity :
    Summable fun n : ℕ => negMulLog ((flipLaw.map natParity).real {n}) :=
  AISafetyAtlas.InformationTheory.summable_negMulLog_of_finiteRange Measurable.of_discrete

/-- `AISafetyAtlas.InformationTheory.entropy_comp_le_of_summable`: the parity of
the flip count has at most its entropy. -/
public theorem entropy_natParity_le_flipCount :
    H[natParity ∘ (id : ℕ → ℕ) ; flipLaw] ≤ H[(id : ℕ → ℕ) ; flipLaw] :=
  AISafetyAtlas.InformationTheory.entropy_comp_le_of_summable measurable_id
    summable_negMulLog_flipLaw natParity

/-- `AISafetyAtlas.InformationTheory.sum_sum_mul_negMulLog_cond_le_entropy` at
the flip count and its half. -/
public theorem sum_sum_flipCount_half_le (F G : Finset ℕ) :
    ∑ y ∈ F, ∑ x ∈ G, (flipLaw.map (fun n : ℕ => n / 2)).real {y}
        * negMulLog ((flipLaw[|(fun n : ℕ => n / 2) ⁻¹' {y}].map (id : ℕ → ℕ)).real {x})
      ≤ H[(id : ℕ → ℕ) ; flipLaw] :=
  AISafetyAtlas.InformationTheory.sum_sum_mul_negMulLog_cond_le_entropy measurable_id
    Measurable.of_discrete summable_negMulLog_flipLaw F G

/-- `AISafetyAtlas.InformationTheory.summable_mul_negMulLog_cond` at the flip
count and its half. -/
public theorem summable_flipCount_half :
    Summable fun q : ℕ × ℕ => (flipLaw.map (fun n : ℕ => n / 2)).real {q.1}
      * negMulLog ((flipLaw[|(fun n : ℕ => n / 2) ⁻¹' {q.1}].map (id : ℕ → ℕ)).real {q.2}) :=
  AISafetyAtlas.InformationTheory.summable_mul_negMulLog_cond measurable_id
    Measurable.of_discrete summable_negMulLog_flipLaw

/-- `AISafetyAtlas.InformationTheory.tsum_mul_negMulLog_cond_le_entropy` at the
flip count and its half. -/
public theorem tsum_flipCount_half_le :
    ∑' q : ℕ × ℕ, (flipLaw.map (fun n : ℕ => n / 2)).real {q.1}
        * negMulLog ((flipLaw[|(fun n : ℕ => n / 2) ⁻¹' {q.1}].map (id : ℕ → ℕ)).real {q.2})
      ≤ H[(id : ℕ → ℕ) ; flipLaw] :=
  AISafetyAtlas.InformationTheory.tsum_mul_negMulLog_cond_le_entropy measurable_id
    Measurable.of_discrete summable_negMulLog_flipLaw

/-- `AISafetyAtlas.InformationTheory.summable_negMulLog_cond`: the flip count
given its half has finite entropy on every fibre. -/
public theorem summable_flipCount_cond_half (y : ℕ) :
    Summable fun x : ℕ =>
      negMulLog ((flipLaw[|(fun n : ℕ => n / 2) ⁻¹' {y}].map (id : ℕ → ℕ)).real {x}) :=
  AISafetyAtlas.InformationTheory.summable_negMulLog_cond measurable_id Measurable.of_discrete
    summable_negMulLog_flipLaw y

/-- `AISafetyAtlas.InformationTheory.hasSum_condEntropy_of_summable` at the flip
count given its half. -/
public theorem hasSum_condEntropy_flipCount_half :
    HasSum (fun y => (flipLaw.map (fun n : ℕ => n / 2)).real {y}
        * H[(id : ℕ → ℕ) | (fun n : ℕ => n / 2) ← y ; flipLaw])
      H[(id : ℕ → ℕ) | (fun n : ℕ => n / 2) ; flipLaw] :=
  AISafetyAtlas.InformationTheory.hasSum_condEntropy_of_summable measurable_id
    Measurable.of_discrete summable_negMulLog_flipLaw

/-- `AISafetyAtlas.InformationTheory.condEntropy_le_entropy_of_summable` at the
flip count given its half. -/
public theorem condEntropy_flipCount_half_le_entropy :
    H[(id : ℕ → ℕ) | (fun n : ℕ => n / 2) ; flipLaw] ≤ H[(id : ℕ → ℕ) ; flipLaw] :=
  AISafetyAtlas.InformationTheory.condEntropy_le_entropy_of_summable measurable_id
    Measurable.of_discrete summable_negMulLog_flipLaw

/-- `AISafetyAtlas.InformationTheory.hasSum_condEntropy_pair_of_summable` at the
flip count given its half and its parity. -/
public theorem hasSum_condEntropy_pair_flipCount :
    HasSum (fun y => flipLaw.real ((fun n : ℕ => n / 2) ⁻¹' {y})
        * H[(id : ℕ → ℕ) | natParity ; flipLaw[|(fun n : ℕ => n / 2) ⁻¹' {y}]])
      H[(id : ℕ → ℕ) | ⟨(fun n : ℕ => n / 2), natParity⟩ ; flipLaw] :=
  AISafetyAtlas.InformationTheory.hasSum_condEntropy_pair_of_summable measurable_id
    Measurable.of_discrete Measurable.of_discrete summable_negMulLog_flipLaw

/-- `AISafetyAtlas.InformationTheory.condEntropy_comp_of_injective_of_summable`
at the injective `Nat.succ`. -/
public theorem condEntropy_flipCount_succ_half_eq :
    H[(id : ℕ → ℕ) | Nat.succ ∘ (fun n : ℕ => n / 2) ; flipLaw]
      = H[(id : ℕ → ℕ) | (fun n : ℕ => n / 2) ; flipLaw] :=
  AISafetyAtlas.InformationTheory.condEntropy_comp_of_injective_of_summable measurable_id
    Measurable.of_discrete Nat.succ_injective summable_negMulLog_flipLaw

/-- `AISafetyAtlas.InformationTheory.condEntropy_pair_eq_of_isMarkovChain_of_summable`
along the chain count, half, quarter. -/
public theorem condEntropy_flipCount_pair_eq :
    H[(id : ℕ → ℕ) | ⟨(fun n : ℕ => n / 2), (fun n : ℕ => n / 2 / 2)⟩ ; flipLaw]
      = H[(id : ℕ → ℕ) | (fun n : ℕ => n / 2) ; flipLaw] :=
  AISafetyAtlas.InformationTheory.condEntropy_pair_eq_of_isMarkovChain_of_summable measurable_id
    Measurable.of_discrete Measurable.of_discrete summable_negMulLog_flipLaw
    (AISafetyAtlas.InformationTheory.isMarkovChain_comp_countable (X := (id : ℕ → ℕ))
      (Measurable.of_discrete (f := fun n : ℕ => n / 2)) (fun m : ℕ => m / 2))

/-- `AISafetyAtlas.InformationTheory.condEntropy_pair_le_of_summable` with the
half and the parity as conditioners. -/
public theorem condEntropy_flipCount_pair_le :
    H[(id : ℕ → ℕ) | ⟨(fun n : ℕ => n / 2), natParity⟩ ; flipLaw]
      ≤ H[(id : ℕ → ℕ) | natParity ; flipLaw] :=
  AISafetyAtlas.InformationTheory.condEntropy_pair_le_of_summable measurable_id
    Measurable.of_discrete Measurable.of_discrete summable_negMulLog_flipLaw

end AISafetyAtlas.Examples.InformationTheory
