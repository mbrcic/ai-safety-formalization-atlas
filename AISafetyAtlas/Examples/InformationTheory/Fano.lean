module

public import AISafetyAtlas.InformationTheory.Fano
public import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# Fano's inequality — worked consequences

Three checks that the general statement in `AISafetyAtlas.InformationTheory.Fano`
has the intended content.

1. **It implies the printed statement.** Cover & Thomas take the estimator to be
   a function `X̂ = g(Y)` of an observation. `fano_of_estimator` is that case,
   obtained by instantiating the general theorem — no separate proof.
2. **It reads correctly at the boundary.** `condEntropy_nonpos_of_perfect` reads
   the inequality at zero error: a perfect estimate forces the conditional
   entropy to be at most zero, which is the qualitative statement Fano is usually
   quoted for. This is a sanity check on the *shape* of the bound, not evidence
   of non-vacuity — deriving a true consequence proves nothing about vacuity,
   since a vacuous theorem entails everything. Non-vacuity is item 3.
3. **It cannot be improved, and it is not vacuous.**
   `entropy_eq_fano_of_witness` exhibits equality at
   *every* error probability `p ∈ [0, 1]`: the truth sits on a fixed guess with
   probability `1 − p` and is otherwise uniform on the rest of the alphabet.
   This is exactly the instance of `entropy_le_fano` at `A = Finset.univ`, so
   the bound is attained along the whole curve and neither term can be reduced.

The first two are corollaries, pinning the general form to the readings a
consumer will want. The third is a witness, and is what makes "sharp" a checked
claim rather than a remark.
-/

namespace AISafetyAtlas.Examples.InformationTheory

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal
open AISafetyAtlas.InformationTheory

universe uΩ uS uT

variable {Ω : Type uΩ} {S : Type uS}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
variable [Countable S] [DecidableEq S]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] [DecidableEq S] in
/-- A perfect estimate has zero error probability. -/
public theorem errorProb_eq_zero_of_forall_eq (μ : Measure Ω) {X X' : Ω → S}
    (h : ∀ ω, X ω = X' ω) : errorProb μ X X' = 0 := by
  have hempty : {ω | X ω ≠ X' ω} = (∅ : Set Ω) := by
    ext ω
    simp [h ω]
  rw [errorProb, hempty]
  simp

/--
**Fano at zero error.** If the estimate is always right, the truth carries no
conditional uncertainty beyond it. This is the boundary reading of the
inequality — a check on its shape, not on its non-vacuity, which is
`entropy_eq_fano_of_witness`.
-/
public theorem condEntropy_nonpos_of_perfect {A : Finset S} (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A) (hX'A : ∀ ω, X' ω ∈ A) (h : ∀ ω, X ω = X' ω)
    [FiniteRange X] [FiniteRange X'] :
    H[X | X' ; μ] ≤ 0 := by
  have hf := fano (A := A) μ hX hX' hXA hX'A
  rw [errorProb_eq_zero_of_forall_eq μ h] at hf
  simpa using hf

/--
**The printed statement is the estimator case.** Cover & Thomas require the
estimate to be a function of an observation; that is this corollary, obtained by
instantiating the general theorem at `X' := g ∘ Y`. Nothing is reproved.
-/
public theorem fano_of_estimator {T : Type uT} [MeasurableSpace T] {A : Finset S}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → S} {Y : Ω → T} {g : T → S}
    (hX : Measurable X) (hY : Measurable Y) (hg : Measurable g)
    (hXA : ∀ ω, X ω ∈ A) (hgA : ∀ ω, g (Y ω) ∈ A)
    [FiniteRange X] [FiniteRange (g ∘ Y)] :
    H[X | g ∘ Y ; μ]
      ≤ errorProb μ X (g ∘ Y) * Real.log ((A.card : ℝ) - 1)
        + binEntropy (errorProb μ X (g ∘ Y)) :=
  fano (A := A) μ hX (hg.comp hY) hXA hgA


/-! ## The bound is attained, at every error probability -/

/--
The weights of Cover & Thomas's sharpness example: mass `1 − p` on the guess,
and the remaining `p` spread evenly over the other `n − 1` values of the
alphabet.
-/
@[expose] public noncomputable def fanoWeights {n : ℕ} (y₀ : Fin n) (p : ℝ) : Fin n → ℝ≥0∞ :=
  fun x => if x = y₀ then ENNReal.ofReal (1 - p) else ENNReal.ofReal (p / ((n : ℝ) - 1))

/-- The weights are a probability vector. -/
public theorem sum_fanoWeights {n : ℕ} (hn : 2 ≤ n) (y₀ : Fin n) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : ∑ x, fanoWeights y₀ p x = 1 := by
  classical
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hsplit : ∑ x, fanoWeights y₀ p x
      = fanoWeights y₀ p y₀ + ∑ x ∈ Finset.univ.erase y₀, fanoWeights y₀ p x := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y₀)]
  have hconst : ∀ x ∈ Finset.univ.erase y₀,
      fanoWeights y₀ p x = ENNReal.ofReal (p / ((n : ℝ) - 1)) := by
    intro x hx
    simp [fanoWeights, (Finset.mem_erase.mp hx).1]
  rw [hsplit, Finset.sum_congr rfl hconst, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have hcard : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    have : 1 ≤ n := by omega
    push_cast [this]
    ring
  rw [nsmul_eq_mul, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), hcard]
  rw [mul_div_cancel₀ _ (ne_of_gt hn1)]
  simp only [fanoWeights, if_true]
  rw [← ENNReal.ofReal_add (by linarith) hp0]
  simp

/-- The witness measure: the truth is `1 − p` likely to equal the guess `y₀`, and
otherwise uniform on the rest of the alphabet. -/
@[expose] public noncomputable def fanoWitness {n : ℕ} (hn : 2 ≤ n) (y₀ : Fin n) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Measure (Fin n) :=
  (PMF.ofFintype (fanoWeights y₀ p) (sum_fanoWeights hn y₀ hp0 hp1)).toMeasure

public instance {n : ℕ} (hn : 2 ≤ n) (y₀ : Fin n) {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    IsProbabilityMeasure (fanoWitness hn y₀ hp0 hp1) := by
  unfold fanoWitness
  infer_instance

/--
The arithmetic behind the witness: spreading `p` over `n − 1` values contributes
exactly `binEntropy p + p·log(n − 1)`, which is Fano's right-hand side.
-/
private theorem fano_witness_identity {n : ℕ} (hn : 2 ≤ n) {p : ℝ} (hp0 : 0 ≤ p) :
    Real.negMulLog (1 - p) + ((n : ℝ) - 1) * Real.negMulLog (p / ((n : ℝ) - 1))
      = p * Real.log ((n : ℝ) - 1) + binEntropy p := by
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  rcases eq_or_lt_of_le hp0 with h | hp
  · rw [← h]
    simp
  · rw [Real.negMulLog, Real.negMulLog,
      Real.log_div (ne_of_gt hp) (ne_of_gt hn1),
      binEntropy_eq_negMulLog_add_negMulLog_one_sub, Real.negMulLog, Real.negMulLog]
    field_simp
    ring

/--
**Fano's inequality is attained, at every error probability.**

Cover & Thomas record sharpness as an example. This is that example: the truth
sits on the guess `y₀` with probability `1 − p` and is otherwise uniform on the
remaining `n − 1` values, and the estimate is the constant `y₀`. Then the error
probability is exactly `p`, and Fano holds with equality.

Since `p` is arbitrary in `[0, 1]`, the bound is attained along the whole curve,
not at one point — so neither the coefficient of `log(n − 1)` nor the
`binEntropy` term can be reduced.
-/
public theorem entropy_eq_fano_of_witness {n : ℕ} (hn : 2 ≤ n) (y₀ : Fin n) {p : ℝ}
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    H[(id : Fin n → Fin n) ; fanoWitness hn y₀ hp0 hp1]
      = errorProb (fanoWitness hn y₀ hp0 hp1) id (fun _ => y₀)
          * Real.log (((Finset.univ : Finset (Fin n)).card : ℝ) - 1)
        + binEntropy (errorProb (fanoWitness hn y₀ hp0 hp1) id (fun _ => y₀)) := by
  classical
  have hn1 : (0 : ℝ) < (n : ℝ) - 1 := by
    have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    linarith
  have hcardn : (((Finset.univ : Finset (Fin n)).card : ℝ)) = (n : ℝ) := by simp
  have hmass : ∀ x : Fin n, (fanoWitness hn y₀ hp0 hp1) {x} = fanoWeights y₀ p x := by
    intro x
    rw [fanoWitness, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton x),
      PMF.ofFintype_apply]
  -- the error probability is `p`
  have herr : errorProb (fanoWitness hn y₀ hp0 hp1) (id : Fin n → Fin n) (fun _ => y₀) = p := by
    have hset : {ω : Fin n | (id ω) ≠ (fun _ => y₀) ω}
        = ((Finset.univ.erase y₀ : Finset (Fin n)) : Set (Fin n)) := by
      ext x; simp
    have hconst : ∀ x ∈ Finset.univ.erase y₀,
        fanoWeights y₀ p x = ENNReal.ofReal (p / ((n : ℝ) - 1)) := by
      intro x hx
      simp [fanoWeights, (Finset.mem_erase.mp hx).1]
    have hcard : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : 1 ≤ n := by omega
      push_cast [this]
      ring
    rw [errorProb, hset, fanoWitness, PMF.toMeasure_apply_finset]
    simp only [PMF.ofFintype_apply]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
      ← ENNReal.ofReal_mul (by positivity), hcard, mul_div_cancel₀ _ (ne_of_gt hn1),
      ENNReal.toReal_ofReal hp0]
  -- the entropy is the two-term sum
  have hent : H[(id : Fin n → Fin n) ; fanoWitness hn y₀ hp0 hp1]
      = Real.negMulLog (1 - p) + ((n : ℝ) - 1) * Real.negMulLog (p / ((n : ℝ) - 1)) := by
    rw [entropy_eq_sum_finset (A := (Finset.univ : Finset (Fin n))) (by simp)]
    have hterm : ∀ x : Fin n,
        (((fanoWitness hn y₀ hp0 hp1).map id).real {x}) = (fanoWeights y₀ p x).toReal := by
      intro x
      rw [Measure.map_id, Measure.real, hmass x]
    rw [Finset.sum_congr rfl (fun x _ => by rw [hterm x])]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ y₀)]
    have hy₀ : (fanoWeights y₀ p y₀).toReal = 1 - p := by
      simp [fanoWeights, ENNReal.toReal_ofReal (by linarith : (0:ℝ) ≤ 1 - p)]
    have hother : ∀ x ∈ Finset.univ.erase y₀,
        Real.negMulLog ((fanoWeights y₀ p x).toReal)
          = Real.negMulLog (p / ((n : ℝ) - 1)) := by
      intro x hx
      rw [show fanoWeights y₀ p x = ENNReal.ofReal (p / ((n : ℝ) - 1)) by
        simp [fanoWeights, (Finset.mem_erase.mp hx).1],
        ENNReal.toReal_ofReal (by positivity)]
    rw [hy₀, Finset.sum_congr rfl hother, Finset.sum_const,
      Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    have hcard : ((n - 1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
      have : 1 ≤ n := by omega
      push_cast [this]
      ring
    rw [hcard]
  rw [hent, herr, hcardn, fano_witness_identity hn hp0]

end AISafetyAtlas.Examples.InformationTheory
