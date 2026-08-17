module

public import AISafetyAtlas.Control.ChannelRate
public import AISafetyAtlas.Control.OpenLoopAttainment

/-!
# Ashby's own worked chain, checked against his printed numbers

W. R. Ashby, *An Introduction to Cybernetics*, §9/12 and §9/15, the three-state
insect chain. This is the example that decides whether
`AISafetyAtlas.Control.chainRate` is the quantity Ashby means, and it is the
reason §11/11's earlier `Yes` grade was wrong: the alphabet ceiling `log₂ 3 ≈
1.585` bits per step is not the `0.84` Ashby computes.

The printed transition matrix, columns summing to one:

```
      ↓    B     W     P
   B  1/4  3/4  1/8
   W  3/4   0    3/4
   P   0   1/4  1/8
```

with printed column entropies `0.811, 0.811, 1.061` and printed equilibrial
proportions `0.449, 0.429, 0.122`, giving

> 0.449 × 0.811 + 0.429 × 0.811 + 0.122 × 1.061 = 0.842 bits

and then, at twenty seconds per step, `2.53` bits per minute.

**Ashby's proportions are decimals of exact rationals.** Solving the balance
equations gives `(22/49, 21/49, 6/49)`, whose decimals are
`0.4490, 0.4286, 0.1224` — his three figures, rounded.
`ashbyInsect_stationary` proves the balance equations exactly and
`ashbyInsect_proportions_match_print` checks the rounding, both over `ℚ`, so no
floating point enters.

`ashbyInsect_rate_eq` evaluates `chainRate` at this chain and gets the printed
weighted average, as a closed form. `ashbyInsect_perMinute` is §9/15's own
conversion sentence: three steps to the minute multiplies the rate by three.
-/

namespace AISafetyAtlas.Examples.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.Control AISafetyAtlas.InformationTheory

/-- Ashby's three insect locations, in his order `B, W, P`. -/
public abbrev Loc := Fin 3

/-- The printed transition matrix: `ashbyInsectStep s t` is the probability of
moving to `t` from `s`, so `ashbyInsectStep s` is the column headed `s`. -/
@[expose] public noncomputable def ashbyInsectStep : Loc → Loc → ℝ
  | 0 => ![1/4, 3/4, 0]
  | 1 => ![3/4, 0, 1/4]
  | _ => ![1/8, 3/4, 1/8]

/-- The equilibrial proportions, exactly. Ashby prints their decimals. -/
@[expose] public noncomputable def ashbyInsectEquilibrium : Loc → ℝ := ![22/49, 21/49, 6/49]

public theorem ashbyInsectStep_mem_stdSimplex (s : Loc) :
    ashbyInsectStep s ∈ stdSimplex ℝ Loc := by
  constructor
  · intro t
    fin_cases s <;> fin_cases t <;> norm_num [ashbyInsectStep]
  · fin_cases s <;> simp [ashbyInsectStep, Fin.sum_univ_three] <;> norm_num

public theorem ashbyInsectEquilibrium_mem_stdSimplex :
    ashbyInsectEquilibrium ∈ stdSimplex ℝ Loc := by
  constructor
  · intro t; fin_cases t <;> norm_num [ashbyInsectEquilibrium]
  · simp [ashbyInsectEquilibrium, Fin.sum_univ_three]; norm_num

/--
**Ashby's equilibrial proportions solve the balance equations exactly.** He prints
`0.449, 0.429, 0.122`; the chain's actual equilibrium is `(22/49, 21/49, 6/49)`.
-/
public theorem ashbyInsect_stationary (t : Loc) :
    ∑ s, ashbyInsectEquilibrium s * ashbyInsectStep s t = ashbyInsectEquilibrium t := by
  fin_cases t <;>
    simp [ashbyInsectEquilibrium, ashbyInsectStep, Fin.sum_univ_three] <;> norm_num

/-- **The printed decimals are those rationals, rounded.** -/
public theorem ashbyInsect_proportions_match_print :
    |ashbyInsectEquilibrium 0 - 0.449| < 0.0005 ∧
      |ashbyInsectEquilibrium 1 - 0.429| < 0.0005 ∧
      |ashbyInsectEquilibrium 2 - 0.122| < 0.0005 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [ashbyInsectEquilibrium, abs_lt] <;> norm_num

/-- The chain as a Markov kernel, each column drawn from its printed weights. -/
@[expose] public noncomputable def ashbyInsectKernel : Kernel Loc Loc :=
  ⟨fun s => ofWeights (ashbyInsectStep s), Measurable.of_discrete⟩

public instance : IsMarkovKernel ashbyInsectKernel :=
  ⟨fun s => isProbabilityMeasure_ofWeights (ashbyInsectStep_mem_stdSimplex s)⟩

/-- The equilibrium law as a measure. -/
@[expose] public noncomputable def ashbyInsectLaw : Measure Loc :=
  ofWeights ashbyInsectEquilibrium

public instance : IsProbabilityMeasure ashbyInsectLaw :=
  isProbabilityMeasure_ofWeights ashbyInsectEquilibrium_mem_stdSimplex

/--
**`chainRate` at Ashby's chain is his printed weighted average.** The three column
entropies appear as `negMulLog` sums and the weights are the equilibrial
proportions — the §9/12 calculation, evaluated.

Stated as a closed form rather than as `0.842`: PFR's `Hm` is a natural-logarithm
entropy while Ashby's figures are bits, and the printed decimals are rounded. What
is checked here is that the *quantity* is his, term by term.
-/
public theorem ashbyInsect_rate_eq :
    chainRate ashbyInsectLaw ashbyInsectKernel
      = ∑ s, ashbyInsectEquilibrium s * ∑ t, Real.negMulLog (ashbyInsectStep s t) := by
  rw [chainRate]
  refine Finset.sum_congr rfl fun s _ => ?_
  congr 1
  · rw [ashbyInsectLaw,
      show (ofWeights ashbyInsectEquilibrium).real {s} = ashbyInsectEquilibrium s from
        congrFun (weights_ofWeights ashbyInsectEquilibrium_mem_stdSimplex) s]
  · exact measureEntropy_ofWeights (ashbyInsectStep_mem_stdSimplex s)

/--
**§9/15's conversion sentence.** *"as each 20 seconds produces 0.84 bits, 60
seconds will produce (60/20)0.84 bits"*: with three steps to the minute, the
per-minute capacity is three times the per-step rate. This is `2.53 = 3 × 0.842`.
-/
public theorem ashbyInsect_perMinute (rate : ℝ) :
    ashbyCapacity rate (1 / 3) = 3 * ashbyCapacity rate 1 := by
  rw [ashbyCapacity, ashbyCapacity]
  ring

end AISafetyAtlas.Examples.Control
