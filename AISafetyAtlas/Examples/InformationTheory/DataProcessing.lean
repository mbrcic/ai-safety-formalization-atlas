module

public import AISafetyAtlas.InformationTheory.DataProcessing
public import AISafetyAtlas.InformationTheory.Fano

/-!
# Data processing — worked consequences

Four checks on `AISafetyAtlas.InformationTheory.DataProcessing`.

1. **It composes with Fano.** `fano_of_markov` is the statement the
   `AISafetyAtlas.InformationTheory.Fano` docstring promised: for a Markov chain
   `X → Y → X̂`, the *observation* `Y` — not merely the estimate — is bounded by
   the error probability of the estimate. This is the form used in converse
   arguments: it says that if `Y` leaves `X` uncertain, then **no** estimate
   built from `Y` can have small error.
2. **The printed corollary is an instance.** `fano_of_estimator_chain` is the
   textbook reading, `X̂ = g(Y)`, obtained by instantiating (1) — no new proof.
3. **The inequality is tight exactly at reversible processing.**
   `mutualInfo_comp_eq_of_injective` shows an injective `g` loses nothing, so the
   `≤` in the data-processing inequality cannot be improved to `<` in general.

4. **The Markov hypothesis is load-bearing.**
   `condMutualInfo_gt_mutualInfo_of_parity` is Cover & Thomas's closing
   counterexample for §2.8: two fair bits and their parity, where conditioning
   *raises* mutual information. Without it, `condMutualInfo_le_mutualInfo`'s
   hypothesis would be assumed necessary and never checked.

The first three are not new mathematics; they exist to pin the general
statements to the readings a consumer will want. The fourth is a witness.
-/

namespace AISafetyAtlas.Examples.InformationTheory

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uΩ uS uT uU

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T]
variable [Countable S] [Countable T] [DecidableEq S]

/-- The printed finite-family chain rule is usable beyond its old two-variable instance. -/
private theorem three_variable_chain_rule {V W : Type*} [Fintype V]
    [MeasurableSpace V] [MeasurableSingletonClass V]
    [MeasurableSpace W] [MeasurableSingletonClass W] [Countable W]
    (mu : Measure Ω) [IsZeroOrProbabilityMeasure mu]
    (Y : Ω → W) (X : Fin 3 → Ω → V) (hY : Measurable Y)
    (hX : ∀ i, Measurable (X i)) [FiniteRange Y] :
    I[Y : observationVector X ; mu] =
      ∑ i : Fin 3, I[Y : X i | observationPrefix X i ; mu] :=
  mutualInfo_chain_rule_fin mu Y X hY hX

/--
**Fano along a Markov chain.** If `X → Y → X̂`, then the uncertainty the
*observation* leaves about the truth is bounded by the error probability of the
estimate.

Stated for an arbitrary Markov chain rather than for `X̂ = g(Y)`, so it also
covers randomised estimators, which the printed form does not.
-/
public theorem fano_of_markov {A : Finset S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} {X' : Ω → S}
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A) (hX'A : ∀ ω, X' ω ∈ A)
    [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    (hmarkov : IsMarkovChain X Y X' μ) :
    H[X | Y ; μ]
      ≤ errorProb μ X X' * Real.log ((A.card : ℝ) - 1)
        + binEntropy (errorProb μ X X') :=
  le_trans (condEntropy_le_condEntropy_of_isMarkovChain μ hX hY hX' hmarkov)
    (fano (A := A) μ hX hX' hXA hX'A)

/--
**The textbook chain `X → Y → X̂ = g(Y)`**, obtained by instantiating
`fano_of_markov` at the Markov chain supplied by `isMarkovChain_comp`. Nothing
is reproved.
-/
public theorem fano_of_estimator_chain {A : Finset S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} {g : T → S}
    (hX : Measurable X) (hY : Measurable Y) (hg : Measurable g)
    (hXA : ∀ ω, X ω ∈ A) (hgA : ∀ ω, g (Y ω) ∈ A)
    [FiniteRange X] [FiniteRange Y] :
    H[X | Y ; μ]
      ≤ errorProb μ X (g ∘ Y) * Real.log ((A.card : ℝ) - 1)
        + binEntropy (errorProb μ X (g ∘ Y)) :=
  fano_of_markov (A := A) μ hX hY (hg.comp hY) hXA hgA (isMarkovChain_comp μ hX hY hg)

/--
**Fano along a Markov chain, estimate unconstrained** — Cover & Thomas's
Theorem 2.10.1 with both inequalities chained, in the generality they state it:
the estimate is not confined to `X`'s alphabet, and the constant is `log |A|`.

`fano_of_markov` above is the sharp companion, which buys `log(|A| − 1)` by
confining the estimate. Neither implies the other; the source prints both.
-/
public theorem fano_of_markov_unrestricted {A : Finset S} (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} {X' : Ω → S}
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A)
    [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    (hmarkov : IsMarkovChain X Y X' μ) :
    H[X | Y ; μ]
      ≤ errorProb μ X X' * Real.log (A.card : ℝ)
        + binEntropy (errorProb μ X X') :=
  le_trans (condEntropy_le_condEntropy_of_isMarkovChain μ hX hY hX' hmarkov)
    (fano_unrestricted (A := A) μ hX hX' hXA)

omit [DecidableEq S] in
/--
**Fano along a Markov chain whose estimate lives in another alphabet.**

The last axis on which Theorem 2.10.1 is more general than the sharp corollary:
`X̂` need not take values in `X`'s type at all. Composing the data-processing
step with `fano_of_embedding` costs one `le_trans`.
-/
public theorem fano_of_markov_embedding {U : Type uU} [MeasurableSpace U]
    [MeasurableSingletonClass U] [Countable U] [DecidableEq U]
    {A : Finset S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} {X' : Ω → U} {ι : S → U} (hι : Injective ι)
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A)
    [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    [FiniteRange (errorPair (ι ∘ X) X')]
    (hmarkov : IsMarkovChain X Y X' μ) :
    H[X | Y ; μ]
      ≤ errorProb μ (ι ∘ X) X' * Real.log (A.card : ℝ)
        + binEntropy (errorProb μ (ι ∘ X) X') :=
  le_trans (condEntropy_le_condEntropy_of_isMarkovChain μ hX hY hX' hmarkov)
    (fano_of_embedding (A := A) μ hι hX hX' hXA)

/--
**Cover & Thomas (2.131) at the printed quantity.** Their weakening of (2.130)
bounds `H(X|Y)` — the uncertainty given the *observation* — not `H(X|X̂)`. So it
is the chained form that matches, and `fano_le_log_two_add` alone does not.

The printed `1` is one bit; at natural logarithm that is `log 2`.
-/
public theorem fano_le_log_two_add_of_markov {A : Finset S} (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} {X' : Ω → S}
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A)
    [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    (hmarkov : IsMarkovChain X Y X' μ) :
    H[X | Y ; μ] ≤ Real.log 2 + errorProb μ X X' * Real.log (A.card : ℝ) :=
  le_trans (condEntropy_le_condEntropy_of_isMarkovChain μ hX hY hX' hmarkov)
    (fano_le_log_two_add (A := A) μ hX hX' hXA)

/--
**Cover & Thomas (2.132) at the printed quantity** — the form converse arguments
use, bounding the error probability below by what the *observation* leaves
uncertain.

`2 ≤ |A|` is the source's own implicit hypothesis: it divides by `log|𝒳|`.
-/
public theorem le_errorProb_of_markov {A : Finset S} (μ : Measure Ω)
    [IsProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} {X' : Ω → S}
    (hX : Measurable X) (hY : Measurable Y) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A) (hA : 2 ≤ A.card)
    [FiniteRange X] [FiniteRange Y] [FiniteRange X']
    (hmarkov : IsMarkovChain X Y X' μ) :
    (H[X | Y ; μ] - Real.log 2) / Real.log (A.card : ℝ) ≤ errorProb μ X X' := by
  have hlog : 0 < Real.log (A.card : ℝ) := by
    refine Real.log_pos ?_
    exact_mod_cast hA
  rw [div_le_iff₀ hlog]
  have hstep := condEntropy_le_condEntropy_of_isMarkovChain μ hX hY hX' hmarkov
  have hmain := le_errorProb (A := A) μ hX hX' hXA hA
  rw [div_le_iff₀ hlog] at hmain
  linarith

omit [DecidableEq S] in
/--
**The bound is attained.** Reversible processing loses nothing, so the
data-processing inequality cannot be strengthened to a strict one. Equivalently,
this is the equality case of `mutualInfo_eq_iff_isMarkovChain` made concrete.
-/
public theorem mutualInfo_comp_eq_of_injective (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {Y : Ω → T} {g : T → T} (hX : Measurable X) (hY : Measurable Y)
    (hg : Measurable g) (hginj : Injective g)
    [FiniteRange X] [FiniteRange Y] :
    I[X : g ∘ Y ; μ] = I[X : Y ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX (hg.comp hY) μ,
    mutualInfo_eq_entropy_sub_condEntropy hX hY μ,
    condEntropy_of_injective' μ hX hY g hginj (by fun_prop)]

/-! ## Off a Markov chain, conditioning can increase mutual information

`condMutualInfo_le_mutualInfo` needs the Markov hypothesis, and Cover & Thomas
close §2.8 by showing it is load-bearing: two independent fair bits `X`, `Y` and
their sum `Z` have `I(X;Y) = 0` but `I(X;Y|Z) = 1` bit. Knowing the parity makes
each bit determine the other.

This is that counterexample. It is here because a hypothesis asserted to be
load-bearing and never witnessed is a hypothesis nobody has checked. -/

/-- Two bits, uniformly distributed — the sample space of the counterexample. -/
public abbrev TwoBits : Type := Fin 2 × Fin 2

/-- The uniform measure on two bits. -/
@[expose] public noncomputable def twoBitsUniform : Measure TwoBits :=
  uniformOn (Set.univ : Set TwoBits)

public instance : IsProbabilityMeasure twoBitsUniform := by
  unfold twoBitsUniform; infer_instance

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  [Countable S] [Countable T] [DecidableEq S] in
/--
A two-bit variable whose every fibre has two points is uniform, so it carries
`log 2`. Used for each of the three variables below.
-/
public theorem entropy_eq_log_two_of_fibres (f : TwoBits → Fin 2)
    (hf : ∀ a : Fin 2, (Finset.univ.filter fun ω : TwoBits => f ω = a).card = 2) :
    H[f ; twoBitsUniform] = Real.log 2 := by
  classical
  have hpre : ∀ a : Fin 2, (f ⁻¹' {a})
      = ((Finset.univ.filter fun ω : TwoBits => f ω = a : Finset TwoBits) : Set TwoBits) := by
    intro a; ext ω; simp
  have huniform : IsUniform (Set.univ : Set (Fin 2)) f twoBitsUniform := by
    constructor
    · intro x _ y _
      rw [twoBitsUniform, uniformOn_univ, uniformOn_univ, hpre x, hpre y,
        Measure.count_apply_finset, Measure.count_apply_finset, hf x, hf y]
    · simp
  rw [IsUniform.entropy_eq' Set.finite_univ huniform (Measurable.of_discrete)]
  norm_num [Set.ncard_univ, Nat.card_eq_fintype_card]

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  [Countable S] [Countable T] [DecidableEq S] in
/-- Any injective recoding of the whole state carries the full `log 4`. -/
public theorem entropy_eq_log_four_of_injective {U : Type*} [MeasurableSpace U]
    [MeasurableSingletonClass U] [Countable U]
    (g : TwoBits → U) (hg : Function.Injective g) :
    H[g ; twoBitsUniform] = Real.log 4 := by
  have hcomp : H[g ∘ (id : TwoBits → TwoBits) ; twoBitsUniform]
      = H[(id : TwoBits → TwoBits) ; twoBitsUniform] :=
    entropy_comp_of_injective twoBitsUniform measurable_id g hg
  have hid : H[(id : TwoBits → TwoBits) ; twoBitsUniform] = Real.log 4 := by
    rw [twoBitsUniform, IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
    norm_num [Set.ncard_univ, Nat.card_eq_fintype_card]
  rw [← hid, ← hcomp]
  rfl

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  [Countable S] [Countable T] [DecidableEq S] in
/--
The entropy of any two-bit variable, read off its fibre sizes. Needed for the
*integer* sum below, whose three values are not equally likely and so is not
covered by `entropy_eq_log_two_of_fibres`.
-/
public theorem entropy_eq_sum_negMulLog_fibres {U : Type*} [Fintype U] [MeasurableSpace U]
    [MeasurableSingletonClass U] [Countable U] [DecidableEq U] (f : TwoBits → U) :
    H[f ; twoBitsUniform]
      = ∑ u : U, Real.negMulLog
          (((Finset.univ.filter fun ω : TwoBits => f ω = u).card : ℝ) / 4) := by
  classical
  have hmass : ∀ u : U, (twoBitsUniform.map f).real {u}
      = ((Finset.univ.filter fun ω : TwoBits => f ω = u).card : ℝ) / 4 := by
    intro u
    have hpre : (f ⁻¹' {u})
        = ((Finset.univ.filter fun ω : TwoBits => f ω = u : Finset TwoBits) : Set TwoBits) := by
      ext ω; simp
    rw [Measure.real, Measure.map_apply (Measurable.of_discrete) (measurableSet_singleton u),
      hpre, twoBitsUniform, uniformOn_univ, Measure.count_apply_finset]
    rw [ENNReal.toReal_div]
    simp
  rw [entropy_eq_sum_finset (A := (Finset.univ : Finset U)) (by simp)]
  exact Finset.sum_congr rfl fun u _ => by rw [hmass u]

/-- The first bit. -/
@[expose] public def bitFst : TwoBits → Fin 2 := fun ω => ω.1

/-- The second bit. -/
@[expose] public def bitSnd : TwoBits → Fin 2 := fun ω => ω.2

/-- Their parity — the variable that couples them. -/
@[expose] public def bitParity : TwoBits → Fin 2 := fun ω => ω.1 + ω.2

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  [Countable S] [Countable T] [DecidableEq S] in
/-- Each of the three variables is a fair bit. -/
public theorem entropy_bits :
    H[bitFst ; twoBitsUniform] = Real.log 2
      ∧ H[bitSnd ; twoBitsUniform] = Real.log 2
      ∧ H[bitParity ; twoBitsUniform] = Real.log 2 :=
  ⟨entropy_eq_log_two_of_fibres bitFst (by decide),
   entropy_eq_log_two_of_fibres bitSnd (by decide),
   entropy_eq_log_two_of_fibres bitParity (by decide)⟩

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  [Countable S] [Countable T] [DecidableEq S] in
/--
**Conditioning can increase mutual information** — Cover & Thomas's closing
remark for §2.8, with their example.

`bitFst` and `bitSnd` are two fair bits and `bitParity` is their sum. The bits
are independent, so `I(X;Y) = 0`; but the parity determines each from the other,
so `I(X;Y | Z) = log 2`.

This is what makes the Markov hypothesis of `condMutualInfo_le_mutualInfo`
load-bearing rather than decorative: drop it and the conclusion fails.

Every entropy here is read off a cardinality. The three single-bit entropies are
`entropy_eq_log_two_of_fibres`; the three joint ones are
`entropy_eq_log_four_of_injective`, because each pairing is an injective
recoding of the whole two-bit state. The chain rule turns those into the
conditional entropies.
-/
public theorem condMutualInfo_gt_mutualInfo_of_parity :
    I[bitFst : bitSnd ; twoBitsUniform]
      < I[bitFst : bitSnd | bitParity ; twoBitsUniform] := by
  have hm : ∀ f : TwoBits → Fin 2, Measurable f := fun _ => Measurable.of_discrete
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  obtain ⟨hF, hS, hP⟩ := entropy_bits
  -- the three pairings are injective recodings, so each carries `log 4`
  have hFS : H[⟨bitFst, bitSnd⟩ ; twoBitsUniform] = Real.log 4 :=
    entropy_eq_log_four_of_injective _ (by decide)
  have hFP : H[⟨bitFst, bitParity⟩ ; twoBitsUniform] = Real.log 4 :=
    entropy_eq_log_four_of_injective _ (by decide)
  have hSP : H[⟨bitSnd, bitParity⟩ ; twoBitsUniform] = Real.log 4 :=
    entropy_eq_log_four_of_injective _ (by decide)
  have hFSP : H[⟨bitFst, ⟨bitSnd, bitParity⟩⟩ ; twoBitsUniform] = Real.log 4 :=
    entropy_eq_log_four_of_injective _ (by decide)
  -- the two bits are independent
  have hIndep : I[bitFst : bitSnd ; twoBitsUniform] = 0 := by
    rw [mutualInfo_eq_entropy_sub_condEntropy (hm _) (hm _),
      chain_rule'' twoBitsUniform (hm _) (hm _), hFS, hS, hF]
    linarith
  -- the parity closes the loop
  have hCond : I[bitFst : bitSnd | bitParity ; twoBitsUniform] = Real.log 2 := by
    rw [condMutualInfo_eq' (hm _) (hm _) (hm _),
      chain_rule'' twoBitsUniform (hm _) (hm _),
      chain_rule'' twoBitsUniform (hm _) (Measurable.of_discrete), hFP, hP, hFSP, hSP]
    linarith
  rw [hIndep, hCond]
  exact Real.log_pos (by norm_num)


/-! ### Cover & Thomas's own numbers

The counterexample above uses `X ⊕ Y`, which gives the larger gap. The printed
one uses the **integer** sum `Z = X + Y ∈ {0,1,2}` and gets `½` bit — the
`P(Z = 1)` factor in the printed derivation only makes sense for a three-valued
`Z`. Both are recorded, so the attribution is exact and the sharper witness is
still available. -/

/-- The integer sum of the two bits: Cover & Thomas's third variable. -/
@[expose] public def bitIntSum : TwoBits → Fin 3 :=
  fun ω => ⟨(ω.1 : ℕ) + (ω.2 : ℕ), by omega⟩

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  [Countable S] [Countable T] [DecidableEq S] in
/-- The integer sum is not uniform: it takes the middle value half the time, so
it carries `(3/2)·log 2` — three half-bits — rather than `log 3`. -/
public theorem entropy_bitIntSum :
    H[bitIntSum ; twoBitsUniform] = (3 / 2 : ℝ) * Real.log 2 := by
  have c0 : (Finset.univ.filter fun ω : TwoBits => bitIntSum ω = 0).card = 1 := by decide
  have c1 : (Finset.univ.filter fun ω : TwoBits => bitIntSum ω = 1).card = 2 := by decide
  have c2 : (Finset.univ.filter fun ω : TwoBits => bitIntSum ω = 2).card = 1 := by decide
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [entropy_eq_sum_negMulLog_fibres, Fin.sum_univ_three, c0, c1, c2]
  have e1 : ((1 : ℕ) : ℝ) / 4 = 4⁻¹ := by norm_num
  have e2 : ((2 : ℕ) : ℝ) / 4 = 2⁻¹ := by norm_num
  rw [e1, e2]
  simp only [Real.negMulLog, Real.log_inv]
  rw [hlog4]
  ring

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
  [MeasurableSingletonClass S] [MeasurableSingletonClass T]
  [Countable S] [Countable T] [DecidableEq S] in
/--
**Cover & Thomas's counterexample, at their numbers.** With `Z` the *integer*
sum of two fair bits, `I(X;Y) = 0` and `I(X;Y | Z) = ½` bit — the value the book
prints.

`condMutualInfo_gt_mutualInfo_of_parity` proves the same phenomenon with
`Z = X ⊕ Y`, where the gap is a full bit. That is the sharper witness; this one
is the faithful transcription.
-/
public theorem condMutualInfo_eq_half_bit_of_intSum :
    I[bitFst : bitSnd | bitIntSum ; twoBitsUniform] = (1 / 2 : ℝ) * Real.log 2
      ∧ I[bitFst : bitSnd ; twoBitsUniform] = 0 := by
  have hm : ∀ f : TwoBits → Fin 2, Measurable f := fun _ => Measurable.of_discrete
  have hmZ : Measurable bitIntSum := Measurable.of_discrete
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  obtain ⟨hF, hS, _⟩ := entropy_bits
  have hFS : H[⟨bitFst, bitSnd⟩ ; twoBitsUniform] = Real.log 4 :=
    entropy_eq_log_four_of_injective _ (by decide)
  have hFZ : H[⟨bitFst, bitIntSum⟩ ; twoBitsUniform] = Real.log 4 :=
    entropy_eq_log_four_of_injective _ (by decide)
  have hSZ : H[⟨bitSnd, bitIntSum⟩ ; twoBitsUniform] = Real.log 4 :=
    entropy_eq_log_four_of_injective _ (by decide)
  have hFSZ : H[⟨bitFst, ⟨bitSnd, bitIntSum⟩⟩ ; twoBitsUniform] = Real.log 4 :=
    entropy_eq_log_four_of_injective _ (by decide)
  constructor
  · rw [condMutualInfo_eq' (hm _) (hm _) hmZ,
      chain_rule'' twoBitsUniform (hm _) hmZ,
      chain_rule'' twoBitsUniform (hm _) (Measurable.of_discrete),
      hFZ, entropy_bitIntSum, hFSZ, hSZ]
    linarith
  · rw [mutualInfo_eq_entropy_sub_condEntropy (hm _) (hm _),
      chain_rule'' twoBitsUniform (hm _) (hm _), hFS, hS, hF]
    linarith


end AISafetyAtlas.Examples.InformationTheory
