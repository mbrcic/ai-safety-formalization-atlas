module

public import AISafetyAtlas.InformationTheory.DataProcessing
public import AISafetyAtlas.InformationTheory.Fano
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Finite variables on a space that is not finite

**This is not a scope witness**, and the section below says why not — the
tempting reading of it does not hold. What it does show is stated after that.

`Ω` here is the real line with Lebesgue measure restricted to `[0,1]`:
uncountable, with no discrete structure. The variables on it are finite-range, as
the theorems require. Three printed Cover & Thomas statements are instantiated
over it — the unnumbered corollary to Theorem 2.8.1, its entropy form, and Fano's
converse (2.132).

## Why this does not witness the `Wider` grade

Several audit rows are graded `Wider` because the atlas takes an arbitrary sample
space where the book fixes a discrete one. It is tempting to read this file as
exhibiting an object in that gap. It does not.

Cover & Thomas do not quantify over a sample space at all. Their theorems are
statements about a **joint pmf** on finite alphabets. The variables here are
finite-range, so they push `unitMeasure` forward to a pmf on `Fin 2 × Fin 2`, and
the printed theorem applies to that pmf and yields the same inequality. Nothing
here is outside print's reach; it is a different *presentation* of something
print already covers.

A witness has to exhibit an object that **cannot be stated at the printed
hypotheses**. Continuity of the ambient space is invisible to a statement whose
hypotheses are about the pushforward, so continuity cannot be that object while
the variables stay finite-range. Where the atlas is genuinely wider on these
sections is elsewhere — `isMarkovChain_iff_measure_factorizes` drops countability
on the value types, and `fano_of_embedding` changes the estimate's type — and
neither is what this file does.

## What it does show

That the atlas statements are **presentation-independent**: they are proved about
variables on a space, not about a pmf, so they apply directly wherever the
variables live without a reader first constructing the pushforward. That is a
real property and a convenience for a consumer whose model is not born discrete.
It is an engineering fact about the encoding, not a claim about coverage, and it
buys no scope grade.

## Explicit non-claims

- **Not** a witness for any `Wider` verdict. See above.
- **Not** a new result. Every statement below is an existing theorem applied to
  one instance.
- **Not** a continuous-entropy development. The variables take finitely many
  values; only the space beneath them is continuous. Differential entropy does
  not appear.
-/

namespace AISafetyAtlas.Examples.InformationTheory

open MeasureTheory ProbabilityTheory
open AISafetyAtlas.InformationTheory

/-! ## A genuinely continuous probability space -/

/-- Lebesgue measure on the unit interval: a probability measure on an
uncountable space with no discrete structure. -/
@[expose] public noncomputable def unitMeasure : Measure ℝ :=
  volume.restrict (Set.Icc 0 1)

public instance : IsProbabilityMeasure unitMeasure := by
  constructor
  simp [unitMeasure]

/-- Did the draw land in the lower half? -/
@[expose] public noncomputable def lowHalf : ℝ → Fin 2 := fun x => if x ≤ 1 / 2 then 0 else 1

/-- Did it land in the lower quarter? -/
@[expose] public noncomputable def lowQuarter : ℝ → Fin 2 := fun x => if x ≤ 1 / 4 then 0 else 1

public theorem measurable_lowHalf : Measurable lowHalf := by
  unfold lowHalf
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

public theorem measurable_lowQuarter : Measurable lowQuarter := by
  unfold lowQuarter
  exact Measurable.ite (measurableSet_le measurable_id measurable_const)
    measurable_const measurable_const

/-! ## Data processing, on that space

`mutualInfo_comp_le` is Cover & Thomas's unnumbered corollary to Theorem 2.8.1,
applied directly to variables on `ℝ`. The book's version reaches the same
conclusion through the pushforward pmf, so this is the same fact with one less
step for the reader, not a wider one.
-/

/-- Post-processing cannot create information, stated directly about variables on
`ℝ`. The printed corollary covers this case through the pushforward pmf; what is
saved is the pushforward, not the coverage. -/
public theorem mutualInfo_comp_le_on_reals (g : Fin 2 → Fin 2) :
    I[lowHalf : g ∘ lowQuarter ; unitMeasure] ≤ I[lowHalf : lowQuarter ; unitMeasure] :=
  mutualInfo_comp_le unitMeasure measurable_lowHalf measurable_lowQuarter
    (measurable_of_countable g)

/-- The entropy form, also stated directly on `ℝ`: a coarsening leaves at least as
much uncertainty as what it coarsened. -/
public theorem condEntropy_le_condEntropy_on_reals (g : Fin 2 → Fin 2) :
    H[lowHalf | lowQuarter ; unitMeasure] ≤ H[lowHalf | g ∘ lowQuarter ; unitMeasure] :=
  condEntropy_le_condEntropy_of_isMarkovChain unitMeasure measurable_lowHalf
    measurable_lowQuarter ((measurable_of_countable g).comp measurable_lowQuarter)
    (isMarkovChain_comp unitMeasure measurable_lowHalf measurable_lowQuarter
      (measurable_of_countable g))

/-! ## Fano, on that space

The same point for §2.10. `le_errorProb` is the converse form, Cover & Thomas
(2.132). Its printed setting is a finite alphabet, which is kept here; the space
beneath the variables is not part of that setting either way.
-/

/-- Fano's converse bound, stated directly about variables on `ℝ`. The alphabet is
finite, as printed. -/
public theorem le_errorProb_on_reals :
    (H[lowHalf | lowQuarter ; unitMeasure] - Real.log 2) / Real.log ((2 : ℕ) : ℝ)
      ≤ errorProb unitMeasure lowHalf lowQuarter := by
  have h := le_errorProb (A := (Finset.univ : Finset (Fin 2))) unitMeasure
    measurable_lowHalf measurable_lowQuarter (fun _ => Finset.mem_univ _) (by decide)
  simpa using h

end AISafetyAtlas.Examples.InformationTheory
