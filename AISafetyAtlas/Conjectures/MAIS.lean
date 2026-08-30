module

public import AISafetyAtlas.Conjectures.MAIS.Common
public import AISafetyAtlas.Conjectures.MAIS.O23
public import AISafetyAtlas.Conjectures.MAIS.O34
public import AISafetyAtlas.Conjectures.MAIS.O31Chart
public import AISafetyAtlas.Conjectures.MAIS.O31
public import AISafetyAtlas.Conjectures.MAIS.O29
public import AISafetyAtlas.Conjectures.MAIS.O29Experiment
public import AISafetyAtlas.Conjectures.MAIS.O27
public import AISafetyAtlas.Conjectures.MAIS.Rates
public import AISafetyAtlas.Conjectures.MAIS.O25
public import AISafetyAtlas.Conjectures.MAIS.O26
public import AISafetyAtlas.Conjectures.MAIS.O38
/-!
# Statement layer for the MAIS agenda questions

**This module declares nothing.** It is the aggregate import of the statement
layer, kept so existing import paths and permalinks keep resolving. Each printed
problem has its own module beside this one, and a reviewer checking one problem
should open that file rather than this one:

| printed | label | module |
|---|---|---|
| MAIS-O23 | `q:ident` | `MAIS/O23.lean` |
| MAIS-O25 | `prob:exact` | `MAIS/O25.lean`, rate predicates in `MAIS/Rates.lean` |
| MAIS-O26 | `conj:exact` | `MAIS/O26.lean`, rate predicates in `MAIS/Rates.lean` |
| MAIS-O27 | `prob:floor` | `MAIS/O27.lean` |
| MAIS-O29 | `prob:boltzmann` | `MAIS/O29.lean`, sampled experiment in `MAIS/O29Experiment.lean` |
| MAIS-O31 | `q:chain` | `MAIS/O31.lean`, chart and transport in `MAIS/O31Chart.lean` |
| MAIS-O34 | `prob:starter-set` | `MAIS/O34.lean` |

One problem here is **not** from A2. MAIS-O38 is A3's `prob:samples`, a
dictionary-learning uniqueness question with no causal content, and it shares
none of this layer's vocabulary:

| printed | label | agenda | module |
|---|---|---|---|
| MAIS-O38 | `prob:samples` | A3 | `MAIS/O38.lean` |

Shared vocabulary is in `MAIS/Common.lean`. Every declaration keeps the
`AISafetyAtlas.Conjectures.MAIS` namespace it had before the split, so no name
downstream changed.

This is primarily the proposition layer, together with the transcription
theorems needed to connect its dedicated charts to the causal kernel and the
printed margin class. Defining a proposition below asserts nothing about its
truth; resolved rows are proved separately in `Examples/Conjectures/`. No
declaration uses `sorry` or an added axiom.

The source is MAIS-A2 — and, for `MAIS/O38.lean` alone, MAIS-A3 — at the revision
pinned in `docs/provenance/mais-source-pin.md`. A conjecture is what gets doubted and
proved, so a specialization must not be baked into its statement. Witnesses may
be as narrow as the prover likes, and where a witness is narrower than the
statement, the resolution field in `conjectures.yaml` says so.

**Grading rationale lives at the declaration it is about, not here.** Each
statement's scope axes and the obligations still owed are recorded in the
docstring of the `Prop` or definition that carries them, and the per-row verdicts
are in `conjectures.yaml`. Narrating those facts here instead puts them one
import away from the declarations they describe, which is how a summary and its
subject come to disagree.

Two facts are about the layer as a whole rather than about any one problem, and
so stay here.

**Coverage is deliberately partial and nothing stands in for what is missing.**
O23 and O29(a) quantify over an arbitrary skeleton; O34 is stated on
`def:twovar`'s two-variable family `MM2(lam)`, which is print's own restriction;
dedicated real charts carry the O34(a) fibre criterion and the O31 chain
classification. Sampled-action, average-case, and controlled-Markov questions are
**not** represented by placeholders here — a question the atlas does not reach
has no declaration, rather than a weakened one.

**Not every printed problem can have a ledger row.** `prob:effective` (O24) and
`prob:floor` (O27) read *"exhibit …"* and *"determine …"* with no truth-valued
clause, and no `Prop` is `Same` as a demand to construct something. Their targets
are formalized as definitions — `Causal.O24Solution` and `o27RealProblemTargets`,
both at print's own quantifier — and a row for either would have to be graded
against a candidate submitted to MAIS, which is the route CONJ-009 and CONJ-010
take. Two of O27's three clauses do carry a truth-valued *decide* sub-clause and
both are refuted at one skeleton, in `Examples/Conjectures/MAIS/O27.lean`.
-/
