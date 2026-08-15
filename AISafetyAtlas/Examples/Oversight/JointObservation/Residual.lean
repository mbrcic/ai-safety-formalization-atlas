module

public import AISafetyAtlas.Oversight.JointObservation
public import AISafetyAtlas.Examples.Oversight.JointObservation.Portfolio

/-!
# Cost-optimal is not residual-optimal

`Portfolio.lean` proves that the three-principal instance has **two** covering,
inclusion-minimal portfolios, and that only the narrow one is cost-optimal:

```text
kNarrow = {qCD, qDE}   reports (a && b, b xor c)   cost 6   cost-optimal
kBroad  = {qCDE}       reports (a, b, c)           cost 7   not cost-optimal
```

Coverage and cost are the only two axes there, and on both of them the narrow
portfolio is at least as good. This module adds the axis that separates them.

## What this example shows

Against the **execution itself** as target — "what actually happened", not merely
"did a declared hazard fire" — the two portfolios are not equivalent:

| Portfolio | covers both hazards | cost | worst-case residual |
|---|---|---:|---:|
| `kNarrow` | yes | 6 | **3** |
| `kBroad` | yes | 7 | **1** |

The narrow report `(false, false)` is produced by three different executions —
`σ000`, `σ011`, `σ100` — and nothing in the reports separates them. The broad
report is injective, so its residual is `1` everywhere.

**The cheaper portfolio buys its saving with residual ambiguity 3, and the
coverage predicate cannot see the difference.**

## Why that matters, stated exactly

Two consequences follow, and only the first is proved here.

* **Attribution.** "Was `C` dirty?" is a function of the execution like any other.
  `narrow_not_knowable_bitC` shows the narrow portfolio cannot answer it;
  `broad_knowable_bitC` shows the broad one can. A residual above `1` means some
  state-attribution question is open, and the fibre says which.
* **Robustness to a later hazard.** A hazard family added after the portfolio was
  chosen is again just a function of the execution, so residual `1` is exactly the
  condition under which *every* future hazard is already covered. That is a reading
  of the same two theorems, not an extra result.

## Explicit non-claims

**No probability.** Residual counts executions; it does not weigh them. There is
no prior here, and no claim that the three executions in the ambiguous fibre are
equally likely or that the ambiguity is small "on average".

**Not accountability.** Everything is under the truthful mechanism `M0`. Nothing
here detects or attributes a dishonest report, and the narrow portfolio's
overlapping coalitions do **not** give it lie-detection: its joint report map is
surjective onto all four output pairs, so no combination of reports is ever
inconsistent. Detecting deception needs a strategic reporting layer this example
does not have.

**Not a claim that broad is better.** It is dearer, and it learns every private
bit — maximal residual reduction is also maximal disclosure. The example exhibits
a tradeoff; it does not rank the two portfolios.
-/

namespace AISafetyAtlas.Examples.Oversight.JointObservation.Residual

open AISafetyAtlas.Knowledge
open AISafetyAtlas.Oversight.JointObservation
open AISafetyAtlas.Examples.Oversight.JointObservation.Portfolio

/-! ## The two portfolios as joint report maps -/

/--
What the narrow portfolio reports: the pair of its two selected candidates'
outputs. This is the portfolio-level observation `PortfolioIndistinguishable`
quantifies over, made explicit as a function so it can be counted.
-/
@[expose] public def narrowReport : Exec → Bool × Bool :=
  fun σ => (qCD.observe σ, qDE.observe σ)

/-- What the broad portfolio reports: the grand coalition's triple. -/
@[expose] public def broadReport : Exec → Bool × Bool × Bool :=
  fun σ => qCDE.observe σ

/-! ## Residual against the execution -/

/--
Three executions survive the narrow portfolio's most ambiguous report.

`σ000`, `σ011` and `σ100` all report `(false, false)`: no dirty `C`-and-`D` pair,
and `D`, `E` in agreement.
-/
public theorem narrow_worstResidual_execution :
    worstAmbiguity narrowReport (id : Exec → Exec) = 3 := by decide

/-- The broad portfolio's report determines the execution exactly. -/
public theorem broad_worstResidual_execution :
    worstAmbiguity broadReport (id : Exec → Exec) = 1 := by decide

/-- The two portfolios are separated by residual, though not by coverage. -/
public theorem broad_worstResidual_lt_narrow :
    worstAmbiguity broadReport (id : Exec → Exec)
      < worstAmbiguity narrowReport (id : Exec → Exec) := by decide

/-! ## The attribution reading -/

/--
**The cost-optimal portfolio cannot attribute.** "Was `C` dirty?" is not
answerable from the narrow reports: the ambiguous fibre contains executions with
`bitC` both true and false.
-/
public theorem narrow_not_knowable_bitC : ¬ Knowable narrowReport bitC := by
  refine not_knowable_of_one_lt_ambiguity (i := (false, false)) ?_
  decide

/-- The broad portfolio answers every state question, attribution included. -/
public theorem broad_knowable_bitC : Knowable broadReport bitC :=
  (knowable_iff_ambiguity_le_one broadReport bitC).mpr (by decide)

/--
The same holds for the other two principals' bits, which is the general fact:
residual `1` fixes *every* function of the execution.
-/
public theorem broad_knowable_bitD : Knowable broadReport bitD :=
  (knowable_iff_ambiguity_le_one broadReport bitD).mpr (by decide)

/-- Narrow does fix `b xor c`; it is the declared hazard it was selected for. -/
public theorem narrow_knowable_hDE : Knowable narrowReport hDE :=
  (knowable_iff_ambiguity_le_one narrowReport hDE).mpr (by decide)

end AISafetyAtlas.Examples.Oversight.JointObservation.Residual
