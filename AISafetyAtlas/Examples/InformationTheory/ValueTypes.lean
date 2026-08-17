module

public import AISafetyAtlas.Examples.InformationTheory.ContinuousSampleSpace

/-!
# Two objects Cover & Thomas's statements cannot hold

Both vary a **value type** past what §2.8 and §2.10 fix, which is where the
atlas theorems are genuinely more general than the printed ones. Varying the
ambient space is not: finite-range variables push the measure forward to a pmf
on finite alphabets, and the printed theorem then applies to that pmf and
returns the same conclusion. `Examples.InformationTheory.ContinuousSampleSpace`
works that case out.

## The value types, not the space

Cover & Thomas §2.8 is about discrete random variables: the objects are joint
pmfs, and every variable in sight takes countably many values.
`isMarkovChain_iff_measure_factorizes` fixes nothing about the outer two —
only `Y` need be measurable, and `S` and `U` need neither countability nor
measurable singletons, because the conditioning happens on `Y`'s fibres and
nothing else in the proof looks at them.

`realValuedMarkovChain` is that gap occupied. `X` is the identity on `ℝ`, so it
takes uncountably many values and has no pmf at all; the printed statement cannot
be written down here, let alone proved. The atlas one is proved.

The chain is deliberately the simplest that exists — a constant third variable —
because what carries the point is the **type** of `X`, not the chain. Every
downstream theorem in that module that does need countability is out of reach at
these types, which is the honest shape of the claim.

## An estimator that may abstain

Fano's inequality is usually read with the estimate ranging over the same
alphabet as the thing estimated. Print says otherwise for the first inequality —
*"we will not restrict the alphabet X̂"* — so a bigger alphabet is not the axis.
`fano_of_embedding` varies something else: the estimate lives in a **different
type**, related to `X`'s by an injection rather than by inclusion in a common
ambient.

`Verdict` is `Fin 3` with an extra value that is not a guess at all, and
`fano_of_verdict` is Fano against an estimator that uses it. Abstention is not a
value of `X`'s alphabet under any relabelling, so this is not the printed
statement at a larger alphabet; it is the printed statement at a type the printed
statement has no way to name. That is also why the sharp `− 1` is unavailable and
`fano_of_embedding` does not claim it: a verdict outside the image of the
injection excludes nothing.

## Explicit non-claims

- **Not** new mathematics. Both are existing theorems applied once. What they
  supply is an object at types the printed statements cannot name.
- **Not** a claim about the rest of §2.8 and §2.10. Where else the atlas
  statements outrun the printed ones, and where they only look as though they
  do, is recorded in `docs/provenance/source-coverage-audit.md`.
- **Not** a continuous-entropy development. `realValuedMarkovChain` states a
  measure factorization; no entropy of a real-valued variable is taken, and none
  is available.
-/

namespace AISafetyAtlas.Examples.InformationTheory

open MeasureTheory ProbabilityTheory
open AISafetyAtlas.InformationTheory

/-! ## A Markov chain whose outer variables have no pmf -/

/-- The third variable, constant. Its only job is to make the chain hold; the
witness is in the type of the first. -/
@[expose] public noncomputable def noSignal : ℝ → ℝ := fun _ => 0

/--
**A Markov chain at value types print cannot use.** `X` is the identity on `ℝ`
and `Z` is real-valued too, so neither has a probability mass function and Cover
& Thomas's §2.8 objects do not exist here. Only `Y` is finite-range, which is all
`isMarkovChain_iff_measure_factorizes` asks of anything.
-/
public theorem realValuedMarkovChain :
    IsMarkovChain (id : ℝ → ℝ) lowHalf noSignal unitMeasure := by
  rw [isMarkovChain_iff_measure_factorizes measurable_lowHalf]
  intro y s t _ _
  by_cases h : (0 : ℝ) ∈ t
  · rw [show noSignal ⁻¹' t = Set.univ from Set.preimage_const_of_mem h]
    simp [mul_comm]
  · rw [show noSignal ⁻¹' t = (∅ : Set ℝ) from Set.preimage_const_of_notMem h]
    simp

/-! ## Fano against an estimator that may abstain -/

/-- `Fin 3` with one more value, which is not a guess. -/
@[expose] public def Verdict := Option (Fin 3)

public instance : MeasurableSpace Verdict := ⊤
public instance : MeasurableSingletonClass Verdict := ⟨fun _ => trivial⟩
public instance : DecidableEq Verdict := inferInstanceAs (DecidableEq (Option (Fin 3)))
public instance : Fintype Verdict := inferInstanceAs (Fintype (Option (Fin 3)))
public instance : Countable Verdict := inferInstanceAs (Countable (Option (Fin 3)))

/-- The injection carrying a value of `X`'s alphabet to the verdict that guesses
it. Nothing maps to abstention, which is the point. -/
@[expose] public def guess : Fin 3 → Verdict := fun i => (some i : Option (Fin 3))

public theorem injective_guess : Function.Injective guess :=
  fun _ _ h => Option.some_injective _ h

/-- Which third of the unit interval the draw landed in. -/
@[expose] public noncomputable def third : ℝ → Fin 3 :=
  fun x => if x ≤ 1 / 3 then 0 else if x ≤ 2 / 3 then 1 else 2

/-- An estimator that guesses on the lower half and abstains on the upper. -/
@[expose] public noncomputable def hedged : ℝ → Verdict :=
  fun x => if x ≤ 1 / 2 then (some 0 : Option (Fin 3)) else (none : Option (Fin 3))

public theorem measurable_third : Measurable third := by
  unfold third
  exact Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
    (Measurable.ite (measurableSet_le measurable_id measurable_const) measurable_const
      measurable_const)

public theorem measurable_hedged : Measurable hedged := by
  unfold hedged
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

/--
**Fano against an abstaining estimator.** The estimate lives in `Verdict`, which
is not `Fin 3` and is not a superset of it inside a common ambient — abstention
is not a value of `X`'s alphabet under any relabelling. The printed statement has
no way to name this estimator; `fano_of_embedding` states the bound for it.
-/
public theorem fano_of_verdict :
    H[third | hedged ; unitMeasure]
      ≤ errorProb unitMeasure (guess ∘ third) hedged
          * Real.log ((Finset.univ : Finset (Fin 3)).card : ℝ)
        + Real.binEntropy (errorProb unitMeasure (guess ∘ third) hedged) :=
  fano_of_embedding (A := (Finset.univ : Finset (Fin 3))) unitMeasure injective_guess
    measurable_third measurable_hedged (fun _ => Finset.mem_univ _)

end AISafetyAtlas.Examples.InformationTheory
