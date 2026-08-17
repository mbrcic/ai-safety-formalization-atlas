module

public import PFR.ForMathlib.Entropy.Basic
public import Mathlib.Analysis.SpecialFunctions.BinaryEntropy

/-!
# Fano's inequality

Cover & Thomas (2nd ed.) give this in three pieces, and the split is exactly
where the content is. **Theorem 2.10.1** bounds `H(X|X̂)` by
`H(Pe) + Pe·log|𝒳|` for an estimator with `X → Y → X̂`, deliberately *not*
restricting `X̂`'s alphabet. An unnumbered **corollary** (their 2.139) drops the
Markov and functional hypotheses entirely — "let `X̂ = Y` in Fano's inequality" —
but keeps the weaker constant `log|𝒳|`. A second unnumbered **corollary** (their
2.140) recovers the sharp `log(|𝒳| − 1)`, at the price of requiring the estimator
to be a function `X̂ : 𝒴 → 𝒳` landing in `X`'s own alphabet.

Both constants are proved here, from one lemma. `fano_of_log_le` isolates the
only thing either constant depends on — how many values the truth can still take
once the estimate is known to be wrong — and everything else is an instance:

| statement | estimate | constant | printed as |
|---|---|---|---|
| `fano_of_log_le` | arbitrary | any `L` dominating `log \|A.erase (X' ω)\|` | — |
| `fano` | confined to `A` | `log(\|A\| − 1)` | the constant of 2.140 |
| `fano_unrestricted` | arbitrary | `log \|A\|` | 2.10.1, 2.139 |
| `fano_of_embedding` | **in another type**, via an injection | `log \|A\|` | 2.10.1 |

Against the source, on each axis:

| | printed source | this module |
|---|---|---|
| estimate | 2.10.1/2.139 arbitrary at `log \|𝒳\|`; sharp constant only for a *function* `X̂ : 𝒴 → 𝒳` | both, and the sharp case needs no functional and no Markov hypothesis — only that the estimate lands in `A` |
| alphabet | the full ambient `𝒳` | **any** `Finset A` containing `X`, so `A` may be the union of the ranges |

The last row is a real sharpening and not bookkeeping: `log(|A| − 1)` with
`A` the union of the ranges is strictly smaller than `log(|𝒳| − 1)` whenever the
variables do not exhaust the alphabet.

**Why the sharp constant needs an alphabet hypothesis.** The `−1` is exactly the
value `X̂` rules out. If `X̂` takes a value outside `A`, conditioning on the error
event removes nothing and the constant is `log |A|` — which is `fano_unrestricted`,
and is why Cover & Thomas's sharp corollary requires `X̂ : 𝒴 → 𝒳`. The hypothesis
here is theirs in the weakest form that still supports the constant: not that the
estimate is a function into the alphabet, only that it lands in `A`.

## Downstream

`fano_le_log_two_add` and `le_errorProb` carry the constants of the two
weakenings the source records next to the theorem, (2.131) and (2.132). Like
(2.140), both printed statements bound `H(X|Y)` rather than `H(X|X̂)`, so the
declarations that *are* (2.131) and (2.132) are their chained forms in
`AISafetyAtlas.Examples.InformationTheory`. `entropy_le_fano` is the remark about
estimating with no observation at all. The chained readings, which need the
data-processing inequality, are in `AISafetyAtlas.Examples.InformationTheory`.

## The right-hand side

`Mathlib.Analysis.SpecialFunctions.BinaryEntropy` defines

```
qaryEntropy q p = p * log (q - 1 : ℤ) + binEntropy p
```

at natural logarithm, which *is* Fano's bound, and `binEntropy` is used here
directly. The conclusion is nevertheless written out as
`P_e * log (|A| - 1) + binEntropy P_e` rather than as `qaryEntropy |A| P_e`,
because `qaryEntropy`'s body is not exposed outside its own module: neither
`rfl`, `unfold` nor `simp` can see through it, and Mathlib exports no
`qaryEntropy_def`. The two are definitionally equal; only the rewriting is
blocked. Should that definition ever be exposed, the statement can be restated
against it without touching the proof.

## The alphabet hypotheses are pointwise

`hXA : ∀ ω, X ω ∈ A` quantifies over all of `Ω`, including `μ`-null sets, and
the same holds of every alphabet hypothesis below. That is strictly stronger than
the almost-everywhere condition the proofs would tolerate, and it is what a
consumer must discharge. It is not a defect against Cover & Thomas, whose
variables are finitely supported, but the statements should not be read as a.e.
conditions.

## Provenance of the entropy layer

`H[· ; ·]`, `H[· | · ; ·]` and the chain rules are PFR's
(`PFR.ForMathlib.Entropy.Basic`), also at natural logarithm. The atlas's own
`AISafetyAtlas.Inference.entropyOn` is a separate development built for Wolpert's
section 8; it is **not** migrated and nothing here depends on it. A transport
between the two belongs in its own module.
-/

namespace AISafetyAtlas.InformationTheory

open MeasureTheory ProbabilityTheory Real Function

universe uΩ uS uT

variable {Ω : Type uΩ} {S : Type uS}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]
variable [Countable S] [DecidableEq S]

/-! ## The error event -/

/-- The error indicator of an estimate: `true` exactly where `X'` misses `X`. -/
@[expose] public def errorIndicator (X X' : Ω → S) : Ω → Bool :=
  fun ω => decide (X ω ≠ X' ω)

/-- The error probability `P_e = μ(X ≠ X')`. -/
@[expose] public noncomputable def errorProb (μ : Measure Ω) (X X' : Ω → S) : ℝ :=
  (μ {ω | X ω ≠ X' ω}).toReal

-- `FiniteRange (errorIndicator X X')` needs no instance here: the indicator is
-- `Bool`-valued and PFR already derives `FiniteRange` from a finite codomain.

/-- The error indicator is measurable whenever both maps are. -/
public theorem measurable_errorIndicator {X X' : Ω → S}
    (hX : Measurable X) (hX' : Measurable X') : Measurable (errorIndicator X X') :=
  (Measurable.of_discrete (f := fun p : S × S => decide (p.1 ≠ p.2))).comp (hX.prodMk hX')

omit [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] in
/-- Pairing a value with the error bit it induces is injective in that value:
the first coordinate recovers it. This is what lets the error bit be adjoined to
`X` without changing the conditional entropy. -/
private theorem injective_pairError (y : S) :
    Injective (fun x : S => (x, decide (x ≠ y))) := by
  intro a b hab
  exact congrArg Prod.fst hab

/-! ## Step 1 — adjoining the error bit is free -/

/--
Conditioned on the estimate, adjoining the error bit to `X` changes nothing:
the bit is a function of `X` and the conditioner, so it carries no information
beyond them.
-/
public theorem condEntropy_pair_errorIndicator (μ : Measure Ω) [IsFiniteMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X') [FiniteRange X'] :
    H[⟨X, errorIndicator X X'⟩ | X' ; μ] = H[X | X' ; μ] :=
  condEntropy_of_injective μ hX hX' (fun y x => (x, decide (x ≠ y))) injective_pairError

/-! ## Step 2 — splitting off the error bit -/

/--
**The Fano decomposition.** Conditional uncertainty about `X` given the estimate
splits into the uncertainty of the error bit and the residual uncertainty once
the error bit is known.
-/
public theorem condEntropy_eq_error_split (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange X'] :
    H[X | X' ; μ]
      = H[errorIndicator X X' | X' ; μ]
        + H[X | ⟨errorIndicator X X', X'⟩ ; μ] := by
  rw [← condEntropy_pair_errorIndicator μ hX hX']
  exact cond_chain_rule μ hX (measurable_errorIndicator hX hX') hX'

/-- The error bit conditioned on the estimate is no more uncertain than the bit
itself. -/
public theorem condEntropy_le_error_bound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange X'] :
    H[X | X' ; μ]
      ≤ H[errorIndicator X X' ; μ] + H[X | ⟨errorIndicator X X', X'⟩ ; μ] := by
  rw [condEntropy_eq_error_split μ hX hX']
  gcongr
  exact condEntropy_le_entropy (μ := μ) (measurable_errorIndicator hX hX') hX'

/-! ## Step 3 — the error bit's entropy is the binary entropy of `P_e` -/

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] in
/-- The error indicator's fibre over `true` is the error event. -/
public theorem preimage_errorIndicator_true (X X' : Ω → S) :
    errorIndicator X X' ⁻¹' {true} = {ω | X ω ≠ X' ω} := by
  ext ω
  simp [errorIndicator]

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] in
/-- The error indicator's fibre over `false` is the agreement event. -/
public theorem preimage_errorIndicator_false (X X' : Ω → S) :
    errorIndicator X X' ⁻¹' {false} = {ω | X ω = X' ω} := by
  ext ω
  simp [errorIndicator]

/-- **The error bit carries exactly the binary entropy of the error probability.** -/
public theorem entropy_errorIndicator (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X') :
    H[errorIndicator X X' ; μ] = binEntropy (errorProb μ X X') := by
  have hE := measurable_errorIndicator hX hX'
  have hmeas : MeasurableSet {ω | X ω ≠ X' ω} := by
    rw [← preimage_errorIndicator_true X X']
    exact hE (measurableSet_singleton true)
  have htrue : (μ.map (errorIndicator X X')).real {true} = errorProb μ X X' := by
    rw [Measure.real, Measure.map_apply hE (measurableSet_singleton true),
      preimage_errorIndicator_true, errorProb]
  have hfalse : (μ.map (errorIndicator X X')).real {false} = 1 - errorProb μ X X' := by
    rw [Measure.real, Measure.map_apply hE (measurableSet_singleton false),
      preimage_errorIndicator_false, errorProb]
    have hcompl : {ω | X ω = X' ω} = {ω | X ω ≠ X' ω}ᶜ := by
      ext ω; simp
    rw [hcompl, prob_compl_eq_one_sub hmeas]
    rw [ENNReal.toReal_sub_of_le (prob_le_one) (by simp)]
    simp
  rw [entropy_eq_sum, tsum_bool, htrue, hfalse,
    binEntropy_eq_negMulLog_add_negMulLog_one_sub, add_comm]

/-! ## Step 4 — averaging a fibrewise bound -/

omit [MeasurableSingletonClass S] [Countable S] [DecidableEq S] in
/--
A fibrewise bound on conditional entropy averages. Stated for an arbitrary
conditioner because it is the generic shape, not anything about errors.
-/
public theorem condEntropy_le_sum_of_fibre_le {T : Type*} [MeasurableSpace T]
    [MeasurableSingletonClass T] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} {W : Ω → T} (hW : Measurable W) [FiniteRange W]
    (c : T → ℝ) (h : ∀ w ∈ FiniteRange.toFinset W, H[X | W ← w ; μ] ≤ c w) :
    H[X | W ; μ] ≤ ∑ w ∈ FiniteRange.toFinset W, (μ.map W).real {w} * c w := by
  rw [condEntropy_eq_sum X W μ hW]
  refine Finset.sum_le_sum fun w hw => ?_
  exact mul_le_mul_of_nonneg_left (h w hw) measureReal_nonneg

/-! ## Step 5 — the two fibres of the error bit -/

/-- The conditioner used throughout: the error bit paired with the estimate. -/
@[expose] public def errorPair (X X' : Ω → S) : Ω → Bool × S :=
  fun ω => (errorIndicator X X' ω, X' ω)

public theorem measurable_errorPair {X X' : Ω → S}
    (hX : Measurable X) (hX' : Measurable X') : Measurable (errorPair X X') :=
  (measurable_errorIndicator hX hX').prodMk hX'

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S] in
/-- The error pair inherits finite range from the estimate: its first coordinate
is `Bool`. Supplied so callers of `fano` need only `FiniteRange X'`. -/
public instance instFiniteRangeErrorPair (X X' : Ω → S) [FiniteRange X'] :
    FiniteRange (errorPair X X') where
  finite := by
    refine Set.Finite.subset
      ((Set.finite_univ (α := Bool)).prod (FiniteRange.finite (X := X'))) ?_
    rintro _ ⟨ω, rfl⟩
    exact ⟨Set.mem_univ _, ⟨ω, rfl⟩⟩

/--
**On an error fibre, `X` avoids the estimate.** Conditioned on `X' = y` and an
error having occurred, `X` lives in `A.erase y`, one value smaller than the
alphabet. This is where Fano's `−1` comes from.
-/
public theorem entropy_cond_errorPair_true_le {A : Finset S} (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A) (y : S) :
    H[X | errorPair X X' ← (true, y) ; μ] ≤ log ((A.erase y).card : ℝ) := by
  refine entropy_le_log_card_of_mem hX ?_
  refine ae_cond_of_forall_mem (measurable_errorPair hX hX' (measurableSet_singleton _)) ?_
  intro ω hω
  simp only [Set.mem_preimage, Set.mem_singleton_iff, errorPair, errorIndicator,
    Prod.mk.injEq, decide_eq_true_eq] at hω
  exact Finset.mem_erase.mpr ⟨hω.2 ▸ hω.1, hXA ω⟩

/--
**On an agreement fibre there is nothing left to learn.** Conditioned on `X' = y`
and no error, `X` equals `y` outright, so the fibre contributes no entropy.
-/
public theorem entropy_cond_errorPair_false (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X') (y : S) :
    H[X | errorPair X X' ← (false, y) ; μ] = 0 := by
  have hconst : X =ᵐ[μ[|errorPair X X' ⁻¹' {(false, y)}]] (fun _ => y) := by
    refine ae_cond_of_forall_mem
      (measurable_errorPair hX hX' (measurableSet_singleton _)) ?_
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, errorPair, errorIndicator,
      Prod.mk.injEq, decide_eq_false_iff_not, not_not] at hω
    exact hω.2 ▸ hω.1
  rw [entropy_congr hconst]
  exact entropy_const y

/-! ## Step 6 — the `true` half of the pair carries exactly `P_e` -/

/-- The mass the error pair puts on its `true` half is the error probability. -/
public theorem sum_errorPair_true (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X')
    [FiniteRange (errorPair X X')] :
    ∑ w ∈ (FiniteRange.toFinset (errorPair X X')).filter (fun w => w.1 = true),
        (μ.map (errorPair X X')).real {w}
      = errorProb μ X X' := by
  classical
  set W := errorPair X X' with hW
  set F := (FiniteRange.toFinset W).filter (fun w => w.1 = true) with hF
  have hWm : Measurable W := measurable_errorPair hX hX'
  have hpre : W ⁻¹' (F : Set (Bool × S)) = {ω | X ω ≠ X' ω} := by
    ext ω
    simp only [Set.mem_preimage, hF, Finset.coe_filter, Set.mem_setOf_eq]
    constructor
    · rintro ⟨-, h⟩
      simpa [hW, errorPair, errorIndicator] using h
    · intro h
      exact ⟨FiniteRange.mem W ω, by simpa [hW, errorPair, errorIndicator] using h⟩
  have hsum : ∑ w ∈ F, (μ.map W) {w} = (μ.map W) (F : Set (Bool × S)) :=
    sum_measure_singleton
  have : ∑ w ∈ F, (μ.map W).real {w} = ((μ.map W) (F : Set (Bool × S))).toReal := by
    rw [← hsum, ENNReal.toReal_sum (fun w _ => measure_ne_top _ _)]
    rfl
  rw [this, Measure.map_apply hWm F.measurableSet, hpre, errorProb]

/-! ## Fano's inequality -/

/--
**Fano's inequality, master form.**

The only thing the constant ever depends on is how many values `X` can still
take once the estimate is known to be wrong: on the error fibre over `X' = y`,
the truth lives in `A.erase y`. So the hypothesis carried here is exactly that,
and nothing else — any `L` dominating `log |A.erase (X' ω)|` pointwise works.

Both printed constants are instances. If the estimate is confined to `A` then
`|A.erase y| = |A| − 1` and `L = log(|A| − 1)` is admissible, giving `fano`;
with no constraint on the estimate `|A.erase y| ≤ |A|` still holds and
`L = log |A|` is admissible, giving `fano_unrestricted`.

No sign or size condition on `L` is needed: the averaging step over the two
fibres of the error bit is an equality, not an inequality.
-/
public theorem fano_of_log_le {A : Finset S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A) {L : ℝ}
    (hL : ∀ ω, Real.log ((A.erase (X' ω)).card : ℝ) ≤ L)
    [FiniteRange X] [FiniteRange X'] [FiniteRange (errorPair X X')] :
    H[X | X' ; μ]
      ≤ errorProb μ X X' * L + binEntropy (errorProb μ X X') := by
  classical
  set W := errorPair X X' with hWdef
  have hWm : Measurable W := measurable_errorPair hX hX'
  -- the fibrewise bound
  have hfibre : ∀ w ∈ FiniteRange.toFinset W,
      H[X | W ← w ; μ] ≤ (if w.1 then L else 0) := by
    intro w hw
    obtain ⟨b, y⟩ := w
    cases b
    · simpa using le_of_eq (entropy_cond_errorPair_false μ hX hX' y)
    · simp only [if_true]
      obtain ⟨ω₀, hω₀⟩ := (FiniteRange.mem_iff W (true, y)).mp hw
      have hy : X' ω₀ = y := by
        have hsnd := congrArg Prod.snd hω₀
        simpa [hWdef, errorPair] using hsnd
      refine le_trans (entropy_cond_errorPair_true_le μ hX hX' hXA y) ?_
      rw [← hy]
      exact hL ω₀
  -- average it
  have havg := condEntropy_le_sum_of_fibre_le μ (X := X) hWm (fun w => if w.1 then L else 0) hfibre
  -- the average collapses to `P_e · L`
  have hcollapse :
      ∑ w ∈ FiniteRange.toFinset W, (μ.map W).real {w} * (if w.1 then L else 0)
        = errorProb μ X X' * L := by
    have hterm : ∀ w : Bool × S,
        (μ.map W).real {w} * (if w.1 then L else 0)
          = if w.1 = true then (μ.map W).real {w} * L else 0 := by
      intro w
      by_cases h : w.1 = true <;> simp [h]
    rw [Finset.sum_congr rfl (fun w _ => hterm w), ← Finset.sum_filter, ← Finset.sum_mul,
      sum_errorPair_true μ hX hX']
  rw [hcollapse] at havg
  -- assemble
  have hsplit := condEntropy_le_error_bound μ hX hX'
  rw [entropy_errorIndicator μ hX hX'] at hsplit
  have : H[X | ⟨errorIndicator X X', X'⟩ ; μ] = H[X | W ; μ] := rfl
  rw [this] at hsplit
  linarith [havg, hsplit]

/--
**Fano's inequality.**

For any two measurable finite-range maps `X` (the truth) and `X'` (the estimate)
that take values in a common finite alphabet `A` — pointwise, not merely almost
surely; see the note on hypotheses below — the conditional
entropy of the truth given the estimate is bounded by Mathlib's `qaryEntropy` at
the error probability:

`H[X | X' ; μ] ≤ P_e · log (|A| − 1) + binEntropy P_e`.

No hypothesis relates `X'` to any observation: it need not be a function of one,
and no Markov chain is assumed.

**This is not (2.140).** The printed corollary bounds `H(X|Y)` — the uncertainty
given the *observation* — and this bounds `H(X|X̂)`. Getting from one to the other
needs the data-processing step, so the declaration that is (2.140) is
`Examples…fano_of_estimator_chain`; `fano` supplies its constant. Cover & Thomas's
Theorem 2.10.1, which leaves the estimate's alphabet free, is `fano_unrestricted`
instead — that generality costs the `−1`, here as there.
-/
public theorem fano {A : Finset S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A) (hX'A : ∀ ω, X' ω ∈ A)
    [FiniteRange X] [FiniteRange X'] [FiniteRange (errorPair X X')] :
    H[X | X' ; μ]
      ≤ errorProb μ X X' * Real.log ((A.card : ℝ) - 1)
        + binEntropy (errorProb μ X X') := by
  refine fano_of_log_le μ hX hX' hXA fun ω => le_of_eq ?_
  rw [Finset.card_erase_of_mem (hX'A ω)]
  congr 1
  have h1 : 1 ≤ A.card := Finset.card_pos.mpr ⟨X' ω, hX'A ω⟩
  push_cast [h1]
  ring

/--
**Fano's inequality with the estimate unconstrained** — Cover & Thomas's
Theorem 2.10.1 and their corollary (2.139).

Nothing at all is assumed about `X'`: it may take values outside `X`'s alphabet
`A`, which is precisely the generality Theorem 2.10.1 is stated in. The price is
the printed constant `log |A|` in place of the sharp `log(|A| − 1)`, and that
price is real rather than an artefact — an estimate landing outside `A` rules
out none of `A`'s values.

Wider than the source on two axes: `A` any `Finset` containing `X`'s range
rather than the ambient type, and no Markov or functional hypothesis on `X'`. The
ambient space is **not** a third: the variables are `FiniteRange`, so they push
forward to a pmf on the printed alphabet and the statements are inter-derivable.
See the sample-space note in `docs/provenance/source-coverage-audit.md`.
-/
public theorem fano_unrestricted {A : Finset S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A)
    [FiniteRange X] [FiniteRange X'] [FiniteRange (errorPair X X')] :
    H[X | X' ; μ]
      ≤ errorProb μ X X' * Real.log (A.card : ℝ)
        + binEntropy (errorProb μ X X') := by
  refine fano_of_log_le μ hX hX' hXA fun ω => ?_
  have hA : (1 : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr ⟨X ω, hXA ω⟩
  rcases Nat.eq_zero_or_pos (A.erase (X' ω)).card with h0 | hpos
  · rw [h0, Nat.cast_zero, Real.log_zero]
    exact Real.log_nonneg hA
  · refine Real.log_le_log (by exact_mod_cast hpos) ?_
    exact_mod_cast Finset.card_erase_le

/-! ## The estimate in a genuinely different alphabet -/

omit [DecidableEq S] in
/--
**Fano's inequality across alphabets.**

Cover & Thomas allow the estimate `X̂` to range over an alphabet `𝒳̂` unrelated
to `X`'s. Their error event `X ≠ X̂` presupposes some ambient set holding both,
and this is that statement with the ambient made explicit: `X` lands in `A`, an
injection `ι` carries `X`'s alphabet into the estimate's, and the error is
`ι ∘ X ≠ X'`.

The bound is `log |A|` — the sharp `−1` is unavailable and *should* be, since a
value of `X'` outside the image of `ι` excludes nothing.

`H[X | X' ; μ]` on the left is the entropy of `X` itself, not of its image:
`ι` is injective, so the two agree, and the conclusion is about the original
variable.
-/
public theorem fano_of_embedding {T : Type uT} [MeasurableSpace T]
    [MeasurableSingletonClass T] [Countable T] [DecidableEq T]
    {A : Finset S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} {X' : Ω → T} {ι : S → T} (hι : Function.Injective ι)
    (hX : Measurable X) (hX' : Measurable X') (hXA : ∀ ω, X ω ∈ A)
    [FiniteRange X] [FiniteRange X'] [FiniteRange (errorPair (ι ∘ X) X')] :
    H[X | X' ; μ]
      ≤ errorProb μ (ι ∘ X) X' * Real.log (A.card : ℝ)
        + binEntropy (errorProb μ (ι ∘ X) X') := by
  classical
  have hιX : Measurable (ι ∘ X) := (Measurable.of_discrete (f := ι)).comp hX
  have hkey := fano_unrestricted (A := A.map ⟨ι, hι⟩) μ hιX hX'
    (fun ω => Finset.mem_map_of_mem _ (hXA ω))
  rw [Finset.card_map] at hkey
  have hcomp : H[ι ∘ X | X' ; μ] = H[X | X' ; μ] :=
    condEntropy_of_injective μ hX hX' (fun _ => ι) (fun _ => hι)
  rwa [hcomp] at hkey

/-! ## The two weakenings Cover & Thomas record alongside -/

/--
**The one-bit weakening**, Cover & Thomas (2.131).

Their `1 + Pe·log|𝒳|` is at logarithm base 2; at natural logarithm the same
statement reads `log 2 + Pe·log|A|`, since `binEntropy ≤ log 2` is exactly
"a binary entropy is at most one bit".
-/
public theorem fano_le_log_two_add {A : Finset S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A)
    [FiniteRange X] [FiniteRange X'] [FiniteRange (errorPair X X')] :
    H[X | X' ; μ] ≤ Real.log 2 + errorProb μ X X' * Real.log (A.card : ℝ) := by
  have h := fano_unrestricted μ hX hX' hXA
  have hb : binEntropy (errorProb μ X X') ≤ Real.log 2 := binEntropy_le_log_two
  linarith

/--
**The error probability is bounded below**, Cover & Thomas (2.132) — the form
in which Fano is actually used to prove converses.

`2 ≤ |A|` is what makes `log |A|` positive, and the printed statement needs it
too: dividing by `log|𝒳|` presumes it nonzero.
-/
public theorem le_errorProb {A : Finset S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X X' : Ω → S} (hX : Measurable X) (hX' : Measurable X')
    (hXA : ∀ ω, X ω ∈ A) (hA : 2 ≤ A.card)
    [FiniteRange X] [FiniteRange X'] [FiniteRange (errorPair X X')] :
    (H[X | X' ; μ] - Real.log 2) / Real.log (A.card : ℝ) ≤ errorProb μ X X' := by
  have hlog : 0 < Real.log (A.card : ℝ) := by
    refine Real.log_pos ?_
    exact_mod_cast hA
  rw [div_le_iff₀ hlog]
  have := fano_le_log_two_add μ hX hX' hXA
  linarith

/-! ## Fano with no observation at all -/

/--
**Fano against a fixed guess**, the remark Cover & Thomas make about estimating
`X` with no observation to condition on.

Taking the estimate constant collapses the conditional entropy to `H[X]`, and
the sharp constant survives because a fixed guess *is* a value of `A`.
-/
public theorem entropy_le_fano {A : Finset S} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} (hX : Measurable X) (hXA : ∀ ω, X ω ∈ A) {y₀ : S} (hy₀ : y₀ ∈ A)
    [FiniteRange X] :
    H[X ; μ]
      ≤ errorProb μ X (fun _ => y₀) * Real.log ((A.card : ℝ) - 1)
        + binEntropy (errorProb μ X (fun _ => y₀)) := by
  have hcm : Measurable (fun _ : Ω => y₀) := measurable_const
  have hconst : H[X | (fun _ : Ω => y₀) ; μ] = H[X ; μ] := by
    have h0 := mutualInfo_const (μ := μ) hX y₀
    have h1 := mutualInfo_eq_entropy_sub_condEntropy hX hcm μ
    rw [h0] at h1
    linarith
  have hkey := fano (A := A) μ hX hcm hXA (fun _ => hy₀)
  rwa [hconst] at hkey

end AISafetyAtlas.InformationTheory
