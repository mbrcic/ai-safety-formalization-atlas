module

public import AISafetyAtlas.Fairness.RiskAssignment

/-!
# The form of Kleinberg–Mullainathan–Raghavan that people actually cite

`AISafetyAtlas.Fairness.RiskAssignment` proves print's Theorem 1.1 as print
states it: calibration together with both balance conditions implies **perfect
prediction or equal base rates**.

That is a disjunction of two conclusions. The way the result is used is the
contrapositive: *you cannot have all three*. Those are the same theorem and they
are not the same sentence, and the second is the one a practitioner is deciding
against — because the two escape hatches, perfect prediction and equal base
rates, are properties of the **population**, fixed before any classifier is
built.

`cannot_have_all_three` is that reading. It takes the two escapes as refuted
hypotheses and concludes that no risk assignment on this instance satisfies the
three conditions together.

## Why this is worth a declaration rather than a remark

The disjunctive form invites a reader to hope one disjunct is arrangeable. It is
not: at a population with unequal base rates and no perfect predictor, the
conclusion is that the three fairness conditions are jointly unsatisfiable, and
the quantifier is over **every** risk assignment — not over the ones anyone has
tried. Stating that separately is the difference between a theorem the reader has
to transform and one they can cite.

## What is not claimed

Nothing here says any real population has unequal base rates, or that perfect
prediction is unavailable for any real task. Both are hypotheses, and supplying
them is an empirical claim about a deployment that this repository does not make.

Nor is this an argument that the three conditions are the right ones. It is an
argument that *these three* cannot be had together, which is a fact about them
and not a recommendation about which to drop — that choice has a normative
content the mathematics is silent on.
-/

namespace AISafetyAtlas.Fairness

variable {F B : Type*} [Fintype F] [Fintype B]

/--
**The citation form: the three conditions are jointly unsatisfiable.**

At an instance with strictly positive and non-exhaustive positive classes, no
perfect predictor and unequal base rates, **no** risk assignment is calibrated
within groups and balanced for both classes.

The quantifier is the content. This is not a statement about the assignments
anyone has constructed; it says the set of assignments meeting all three is
empty, so the design question is which condition to give up and not how to
search harder.
-/
public theorem cannot_have_all_three (I : Instance F)
    (hμ : ∀ t, 0 < I.μ t) (hμN : ∀ t, I.μ t < I.N t)
    (hperfect : ¬ PerfectPrediction I) (hbase : ¬ EqualBaseRates I) :
    ∀ R : RiskAssignment F B,
      ¬ (Calibrated I R ∧ BalancedNegative I R ∧ BalancedPositive I R) := by
  rintro R ⟨hA, hB, hC⟩
  rcases perfect_prediction_or_equal_base_rates I R hμ hμN hA hB hC with h | h
  · exact hperfect h
  · exact hbase h

/--
**And one of the two escapes has to be a fact about the population.**

Stated as the contrapositive of the above so that the escape route is visible in
the type: if some assignment does meet all three, then the population either
admits a perfect predictor or already has equal base rates. Neither is something
a classifier can be built to achieve — both are settled before the classifier
exists.
-/
public theorem population_escape_of_all_three (I : Instance F)
    (hμ : ∀ t, 0 < I.μ t) (hμN : ∀ t, I.μ t < I.N t)
    (R : RiskAssignment F B)
    (h : Calibrated I R ∧ BalancedNegative I R ∧ BalancedPositive I R) :
    PerfectPrediction I ∨ EqualBaseRates I :=
  perfect_prediction_or_equal_base_rates I R hμ hμN h.1 h.2.1 h.2.2

end AISafetyAtlas.Fairness
