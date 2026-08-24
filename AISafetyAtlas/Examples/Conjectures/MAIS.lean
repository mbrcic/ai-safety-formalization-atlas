module

public import AISafetyAtlas.Examples.Conjectures.MAIS.Common
public import AISafetyAtlas.Examples.Conjectures.MAIS.O23
public import AISafetyAtlas.Examples.Conjectures.MAIS.O34
public import AISafetyAtlas.Examples.Conjectures.MAIS.O29
public import AISafetyAtlas.Examples.Conjectures.MAIS.O31
public import AISafetyAtlas.Examples.Conjectures.MAIS.O31Measure
public import AISafetyAtlas.Examples.Conjectures.MAIS.Rates
public import AISafetyAtlas.Examples.Conjectures.MAIS.O25
public import AISafetyAtlas.Examples.Conjectures.MAIS.O26
public import AISafetyAtlas.Examples.Conjectures.MAIS.O27

/-!
# Non-vacuity checks for the MAIS statement layer

The source conjectures remain unproved. This module discharges the two registered
negatives on the real chart, checks `def:margin`'s `K` on the two-variable
skeleton, and checks the `⊤` discipline that keeps *"no budget suffices"* from
satisfying a budget bound.

**One of the two non-vacuity obligations is discharged and the other is not.**
`ExactClassAssumptions`, MAIS-O25's antecedent, is inhabited below by
`exactClassAssumptions_nonempty`. `O26ClassAssumptions` is not, and the reason is
structural rather than a shortfall of effort: this module used to inhabit it with
an explicit genericity witness — an indicator quantity, plus two further
witnesses showing the tightness clause was neither vacuous nor forced to be an
indicator — and all of that policed an *arbitrary supplied witness*, which
`conj:exact` does not have. Its class is cut by an `O24Solution`'s own polynomial
list. The witnesses went with the stand-in they policed, and inhabiting
`O26ClassAssumptions` now needs a solution, hence an answer to `prob:effective`,
which is an open construction problem.

This module is now an aggregate: each printed problem's proofs have their own
file under `AISafetyAtlas/Examples/Conjectures/MAIS/`, mirroring the statement
split under `AISafetyAtlas/Conjectures/MAIS/`. Every declaration keeps the
`AISafetyAtlas.Examples.Conjectures.MAIS` namespace it had before.
-/
