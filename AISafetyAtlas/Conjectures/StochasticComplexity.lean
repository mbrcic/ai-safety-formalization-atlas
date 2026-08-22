module

public import AISafetyAtlas.Inference

/-!
# Is the no-null-point hypothesis of the `ε = 1` collapse necessary?

Wolpert 2008 §8 states, in running prose, that *"if `P` is proportional to `dμ`
across the support of `P` and `C > Γ`, then for `ε = 1`,
`C̄_ε(Γ ∣ C) = 𝒞(Γ ∣ C)`."*

`stochasticInferenceComplexity_eq` proves it, with the proportionality condition
rendered in the atlas's single-measure model as *no point of a fibre is null*.
The `≤` direction (`stochasticInferenceComplexity_le`) needs no such hypothesis.

Whether the hypothesis is **necessary** was asserted when that theorem landed and
never proved. The argument for it is that accuracy `1` says the disagreeing part
of a fibre has measure zero while exact answering says it is empty, so a device
that answers a probe wrongly at a null point should separate the two quantities.
That is a plausible construction, not a proof: the two complexities are *minima*
over the two sets, and a set can grow without its minimum moving.

Nothing here is asserted. This module is not on the atlas root import.
-/

namespace AISafetyAtlas.Conjectures.StochasticComplexity

open AISafetyAtlas.Inference MeasureTheory

/--
**CONJ-002.** Dropping the no-null-point hypothesis from
`stochasticInferenceComplexity_eq` makes it false.

This is `stochasticInferenceComplexity_eq` with `hatom` deleted and **nothing
else changed** — same general target type `G`, same `hagree`, same `hpos` —
negated. That exactness is the whole content of the conjecture. A
version that also dropped `hagree` would be refutable by a device whose agreement
function is non-measurable, which says nothing about whether null points matter;
a version that fixed `G := Bool` or bolted on `WeaklyInfers` would be asking
about a different theorem. The ledger records that all three deviations
were present until 2026-08-20.

The one thing that is pinned rather than mirrored is the universe: the theorem is
polymorphic and this reads it at `Type 0`. That is Lean bookkeeping and not a
mathematical restriction — a counterexample lives in an ordinary set, and
refuting the `Type 0` instance refutes the polymorphic theorem. It is pinned here
because a universe-polymorphic `Prop` cannot be named by the generated
`example : Prop := …` in `Checks.lean` without universe metavariables.

A refutation is a proof that the hypothesis was never needed and the theorem can
simply be strengthened.
-/
public def eq_needs_no_null_points : Prop :=
  ¬ ∀ {U : Type} [MeasurableSpace U] (μ : Measure U) [IsProbabilityMeasure μ]
      (C : InferenceDevice.{0, 0} U) [DecidableEq C.Setup] [FiniteRange C.setup]
      [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup],
      Measurable C.setup → ∀ (ℓ : C.Setup → ℝ) {G : Type} [DecidableEq G]
        (Γ : U → G) [FiniteRange Γ],
      (∀ f : G → Bool, Measurable fun u => C.concl u == f (Γ u)) →
      (∀ x : C.Setup, x ∈ realizedSetups C → massOn μ C.setup x ≠ 0) →
      stochasticInferenceComplexity μ C ℓ Γ 1 = inferenceComplexityTotal C ℓ Γ

end AISafetyAtlas.Conjectures.StochasticComplexity
