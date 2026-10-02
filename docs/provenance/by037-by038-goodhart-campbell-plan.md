# BY-037 and BY-038 — the specification-problem cluster, decided

Written 2026-09-10 on branch `specification-problem`. This file decides four
questions the two rows have carried since intake: whether Goodhart and Campbell
are one statement or two, which theorem the informal claim actually reaches,
what to build first, and what to do about the one reproduced external Lean body
in this neighbourhood.

Sources read for this file are pinned, with hashes and per-document metadata, in
the private manifest of 2026-09-10
(outside this repository, in the notes tree). The survey that sits behind the
decisions is a private note.
Every statement quoted below was read in the document, not in an index.

Nothing here writes a coverage row. Both rows stay as they are until
`wireheading-precision` and this branch merge; the rows this file proposes are
proposals.

## The four decisions

| # | Question | Decision |
|---|---|---|
| D1 | Do BY-037 and BY-038 collapse into one formal statement? | **No. They stay distinct**, and the axis is Campbell's second conjunct. |
| D2 | Which theorem does "Goodhart's law" actually reach? | **Zhuang & Hadfield-Menell Theorem 1** for Strathern's sentence and **Hennessy & Goodhart Proposition 1** for Goodhart's own. **Nothing** formalizes BY-038; the nearest is Hennessy & Goodhart, and it is not close enough. |
| D3 | What is the first buildable target? | **Zhuang & Hadfield-Menell Theorem 1**, then Hennessy & Goodhart Proposition 1, then Zhuang & Hadfield-Menell Theorem 2, then Skalse Theorem 1. |
| D4 | audieleon/goodhart — port, depend, or ignore? | **Neither port nor depend: cite as a reproduced reference body.** |

A fifth finding, not a decision but a correction, is in
[Two metadata claims that do not survive the documents](#two-metadata-claims-that-do-not-survive-the-documents).

## D1 — the two rows stay distinct

**Corroboration found 2026-09-10.** Manheim & Garrabrant's footnote 1 records, in
passing, that Campbell's law *"arguably has scholarly precedence"* over Goodhart's.
That is an independent voice for treating the two as separate claims with separate
lineages rather than one law with two names, and it is consistent with the
decision below, which was taken from Campbell's own text.

The temptation to collapse them is well supported by the secondary literature and
is wrong on the primary source.

**What the secondary literature does.** Manheim & Garrabrant (2018) place a row
named "Campbell's Law" inside their §4 *Adversarial Goodhart*, and reduce it to
one clause: "Agents select a metric knowing the choice of regulator metric …
This further reduces the usefulness of selection using the metric for acheiving
the original goal." Their footnote 5 quotes Campbell's sentence in full and then
narrows it: "In this case, the choice of measurement affects the outcome because
agents attempt to corrupt **the measure**." Their footnote 6 declines the other
route explicitly — "They could instead alter causal structure to create the same
effect. It seems unclear that this difference is critical to the dynamics
considered." Ashton (2020) goes further and merges the names, writing throughout
of "Campbell-Goodhart's law", quoting Strathern for the wording, and classifying
his own worked problem as *Causal Goodhart (metric manipulation)* in Manheim &
Garrabrant's scheme.

**What Campbell wrote.** From the Occasional Paper the row cites, page 34 of the
2011 reprint, read from a rendered page image because the two-column text layer
interleaves:

> … I come to the following pessimistic **laws** (at least for the U.S. scene):
> The more any quantitative social indicator is used for social decision-making,
> the more subject it will be to corruption pressures and the more apt it will be
> to distort and corrupt the social processes it is intended to monitor. Let me
> illustrate these **two laws** with some evidence which I take seriously,
> although it is predominantly anecdotal.

Campbell counts two laws, not one, and the next paragraph separates them by
example: Skolnick's clearance-rate work shows "both corruption of the indicator
itself **and** a corruption of the criminal justice administered."

So the axis is not a matter of taste. Campbell's first conjunct is a claim about
the indicator — it stops tracking. His second is a claim about the world — the
monitored process is itself deformed by being monitored. The ledger already
carries both: BY-038's informal claim reads "creates pressure that corrupts the
indicator **and represented process**". Collapsing BY-038 into BY-037 would drop
the second conjunct and put the row below its printed scope, which the scope rule
forbids; and the two papers that make the collapse look attractive are exactly
the two that drop that conjunct in the act of collapsing.

**What the distinction costs formally.** BY-037's content is a statement about
a *map*: two orderings of a fixed set of outcomes come apart under optimization.
Every theorem in the surveyed corpus is of that shape. BY-038's second conjunct
is a statement about an *intervention*: using the indicator for decisions changes
the process that generates it, so the pre-measurement and post-measurement
data-generating processes are different objects. No theorem in the corpus states
that. It is not statable at all without a layer in which "the world before the
indicator was used for decisions" and "the world after" are distinct and
comparable — which is what a structural causal model with interventions buys.

**Consequence for the ledger.** BY-037 moves from `CANDIDATE_LEAD` to a target
with a named theorem (D2, D3). BY-038 stays uncovered, but stops being
`UNTRIAGED`: it becomes a *stated gap with a requirement*, namely that any
candidate must carry an interventional layer distinguishing the process before
and after the indicator enters the decision rule. The nearest substrate in the
atlas is the causal layer arriving on `wireheading-precision`
(`AISafetyAtlas.Causal.StructuralModel` and `AISafetyAtlas.Causal.Incentive`).
Propose the row after that merge, not before.

## D2 — the requirement-to-theorem arrows

BY-037's printed claim: *When a measure becomes a target, optimization pressure
can destroy its value as a measure.*

**Amended 2026-09-10, after reading both named sources and re-reading
Manheim & Garrabrant.** An earlier version of this section claimed the three
literatures name three different *objects* -- a relation, a map's image, a pair of
orders. **That was wrong at the top level, and the error is worth naming because
it is the one this whole row invites.**

Every one of them is a claim about **two** quantities: a goal the optimiser
intends, and a proxy standing in for it. Manheim & Garrabrant make it
constitutive in their opening definition:

> As used in this paper, a Goodhart effect is when optimization causes a collapse
> of the statistical relationship between **a goal which the optimizer intends and
> the proxy used for that goal**.

Goodhart's monetary aggregate is an intermediate target standing in for nominal
income. Strathern's grade is a proxy for *"individual performances"* -- her own
words, in the sentence itself. The reward-hacking literature says it outright.

So what differs across the sources is not the objects but **the failure mode of
the proxy--goal link**:

| Source | How the proxy--goal link fails | Needs an intervention? |
|---|---|---|
| Goodhart 1975 | the observed statistical regularity between them collapses | yes -- "pressure … for control purposes" |
| Strathern 1997 | the proxy's resolution collapses, so it can no longer separate what it measures | no -- an expectation forming is enough |
| Manheim & Garrabrant, Regressional | selecting on the proxy selects on the proxy--goal *difference* | no |
| Manheim & Garrabrant, Extremal | selection moves the state out of the region where the link was observed | no |
| Manheim & Garrabrant, Causal | the regulator's intervention changes the causal path | yes |
| Skalse, Zhuang--Hadfield-Menell | the induced orderings of outcomes diverge | no |

**The consequence for this row is a constraint, not an arrow: any rendering of
BY-037 carrying only one function is a category error.** That is the arity point
an earlier review made against arrow E, and it applies to more than arrow E -- see the
amendment to arrow G, where this document made the same mistake.

The ledger's own wording -- *"optimization pressure can destroy its value as a
measure"* -- paraphrases Strathern, and is not Goodhart's.

**On Strathern.** That claim is the ledger's
paraphrase. Strathern's own sentence, p. 308, is *"When a measure becomes a
target, it ceases to be a good measure"*, and the illustration she attaches to it
is narrower than "destroy its value": *"The more a 2.1 examination performance
becomes an expectation, the poorer it becomes as a **discriminator of individual
performances**."* That is loss of resolution in one measure, not divergence
between a proxy and a truth. Arrow G below is the consequence, and it reopens
ground arrow E closed.

The claim is a "can" statement, so it is satisfied vacuously by any existence
theorem — which is precisely why two of the four catalogued Lean leads on the row
were rejected. An arrow only survives if the target theorem is universally
quantified over proxies: *every* proxy of the relevant kind fails, not *some*
proxy fails somewhere.

### Arrow A — Zhuang & Hadfield-Menell Theorem 1. **Survives.**

> Theorem 1 For any continuous strictly increasing proxy utility function based
> on `J < L` attributes, if `s(t)` converges to some point `s*`, then `s*ₖ = bₖ`
> for `k ∈ K`.

`K` is the complement of the proxy attributes and `bₖ` is attribute `k`'s lower
bound. The quantifier is right: *any* proxy defined on a strict subset of the
attributes the principal values drives *every* unmentioned attribute to its floor
under complete optimization. The requirement — "the measure becomes a target and
its value as a measure is destroyed" — maps onto "the proxy attains its supremum
while the attributes it omits sit at their minimum", so the proxy's value as a
report about `U` is destroyed exactly by the optimization that maximized it. No
step of that mapping is a pun. Their Theorem 2 then gives the conditions under
which the loss is not merely a floor but unbounded below.

### Arrow B — Skalse Theorem 1, with Corollary 1. **Survives, at a higher price.**

> Theorem 1. In any MDP\R, if `Π̂` contains an open set, then any pair of reward
> functions that are unhackable and non-trivial on `Π̂` are equivalent on `Π̂`.

Contrapositive: every non-trivial proxy that is not exactly order-equivalent to
the true reward is hackable — there are two policies whose true ordering the
proxy reverses. That is universally quantified over proxies and is the atlas's
own register, an impossibility. Corollary 1 discharges the hypothesis for the set
of all stationary policies. The price is that the printed statement quantifies
over MDPs and policy sets, so scope-at-print needs the occupancy-measure
reduction (their Propositions 1–2 and Lemma 1), which no existing atlas module
supplies. See D3.

### Arrow C — Manheim & Garrabrant's four variants. **Refuted as a target.**

The paper has no numbered statement of any kind — no theorem, proposition, lemma
or corollary in ten pages. Its "Simple Model" blocks are two-line generative
specifications with an asserted consequence and no proof, and at least one of
them is stated loosely: the Campbell model `MR = GR + X`, `MA = GA · X` asserts
"the correlation between `GA` and `MA` is zero over the full set of states",
which needs `E[X] = 0`, while the text writes `X ∼ normal(μ, σ²)` with `μ` free.
It is a taxonomy, and a good one; the ROADMAP_IDEAS §4.6 "Goodhart as finks and
masks" bridge would be a bridge onto a taxonomy, not onto a theorem. Keep it as
vocabulary for the survey and for grading other rows. Do not make it a target.

### Arrow D — Ashton's causal Campbell. **Refuted as a target.**

Seven pages, no numbered statement, and the content is an experiment: a toy
"dog barometer" MDP in which an off-policy learner (DQN) is fooled by
intervening on a predictive variable while an on-policy learner (PPO) is not.
It is evidence that the phenomenon reaches deep RL. It is not a formalization,
and — as noted in D1 — it does not separate Campbell from Goodhart; it fuses
them.

### Arrow E — the proxy collapse and `AISafetyAtlas.Sovereignty.Arena`. **Refuted.**

The resemblance is real at the word. `AISafetyAtlas.Sovereignty.Arena.collapse`
is the set of outcomes a control choice still admits, indexed by the residue;
a degenerate proxy is a view that admits one value. But the two collapses are of
different arities. The arena's collapse is the spread of *one* map's image over
the residue; Goodhart's collapse is a divergence between *two* orderings of the
same outcome set, and the arena has no second ordering to diverge from. The only
map that typechecks sends a trivial proxy to a constant view, and
`AISafetyAtlas.Sovereignty.Arena.sovereign_const` already proves every arena
sovereign over a constant boundary — which is the module's own way of saying that
this is the degenerate corner, not a result. Write no bridge here.

**Amendment, 2026-09-10.** This refutation stands *for the reading it tested* --
Goodhart-as-divergence-between-two-orderings does not map onto the arena. What it
did not test is whether that reading is Strathern's. It is not. See arrow G.

### Arrow F — Hennessy & Goodhart Proposition 1. **Survives, and it is the only one aimed at Goodhart's own sentence.**

Under quadratic manipulation costs and a naive Ridge regression, the Goodhart
bias in the prediction is exactly the Ridge tuning parameter divided by the
manipulation cost — a closed form, and one that says the bias grows with the
penalization the statistician chose. The requirement it discharges is not
Strathern's "ceases to be a good measure" but Goodhart's "any observed
statistical regularity will tend to collapse once pressure is placed upon it for
control purposes": the regularity is the fitted model, the pressure is the
agents' best response to it being used, and the collapse is quantified. The
quantifier is over the model's own parameters rather than over all proxies, so
it is a weaker shape than Arrow A — but it is aimed at the sentence BY-037's
first cited source actually contains, which no other candidate is.

**Net:** three arrows survive — A at low cost, F at low cost and closer to the
row's own citation, B at a higher price — and three are refuted.

### Arrow G — Strathern's discriminator collapse. **Reopened, and not yet established.**

Added 2026-09-10, on reading the source that names this row.

Strathern's mechanism is not the one the reward-hacking literature formalizes.
Her measure does not diverge from a truth; it stops **separating** the things it
was measuring. As a 2.1 becomes the expectation, more students receive it, so the
grade sorts fewer individuals. The formal content is that the measure's image
shrinks, or equivalently that its fibres coarsen: one function losing
discriminating power over a population.

Every candidate currently on BY-037 has the wrong shape for that. Skalse
unhackability is a disagreement between **two** orderings. Zhuang &
Hadfield-Menell Theorem 1 is about the **omitted** attributes running to their
floor -- it says nothing about the retained proxy's resolution. Neither is a
statement about a measure ceasing to discriminate.

The atlas does already carry that shape, and carries it twice:
`AISafetyAtlas.Sovereignty.Arena.collapse` is the image of one map over a
residue, and `AISafetyAtlas.Sovereignty.Arena.decisive_iff_collapse_subsingleton`
says precisely that a collapse being a subsingleton is the map having stopped
discriminating. `AISafetyAtlas.Oversight.collapse` is the same object on the
intervention side.

**Why this is a candidate and not a decision.** The arrow is missing its verb.
Strathern's sentence is dynamic -- *becomes* a target, *becomes* an expectation --
and `collapse` is static. Nothing above supplies the optimization pressure that
makes the image shrink, and without it the correspondence is a resemblance
between two uses of one English word, which is the error arrow E was written to
avoid. What would settle it is a statement of the form *"under pressure toward a
threshold, the image of the measure is non-increasing, and strictly decreasing
under a stated condition"*, with the pressure an explicit dynamic rather than a
gloss.

**Second amendment, later the same day: this arrow has arity trouble of its own,
and it is the same trouble arrow E was refuted for.** `Arena.collapse` and
`Oversight.collapse` are objects built from **one** map. Strathern's measure does
not merely lose resolution in the abstract -- it becomes *"the poorer … as a
discriminator of individual performances"*, and the performances are the goal the
grade proxies for. Drop them and what is left is a function with a small image,
which is not a Goodhart claim about anything. So this arrow needs `G` and `M` and
their relation, exactly as arrow E did, and the version written above quietly
carried only `M`. Recorded as an error of this document rather than repaired,
because repairing it means choosing the second object, and that is the same
missing-verb problem in a new place.

So: do not write this bridge yet either. Write it after the pressure has a
definition **and the goal has a name**, and grade it then. Recorded here so the next pass tests it instead of
rediscovering it, and so that the ranking in D3 is read as ranking the *available*
targets rather than the best conceivable one.

### Arrow H — Goodhart's sentence as conditioning mistaken for intervening. **Retracted as stated; survives only as one variant.**

Added 2026-09-10 on reading `survey-ref-074`, and **corrected the same day, after
the maintainer asked for the connection in the literature and observed that
Goodhart is more than conditioning and `do`.** Both objections hold. The section
below is kept because the reduced claim is still useful, but two things it
originally said are withdrawn.

**Withdrawn: that this reading is new.** It is Manheim & Garrabrant's third
category, stated as such:

> **Causal Goodhart** -- When the causal path between the proxy and the goal is
> indirect, intervening can change the relationship between the measure and
> proxy.

They give it three sub-cases -- shared-cause intervention, intermediary
intervention, and metric manipulation. Ashton 2020, already pinned, is the
reinforcement-learning treatment of the same reading. And their footnote 1 names
**the Lucas critique** as a closely related formulation. The connection is in the
literature, and it has been since 2018.

**Withdrawn: that it is Goodhart's sentence.** It is one of four categories, and
two of the other three need no intervention at all. Manheim & Garrabrant say so
directly, immediately before introducing the causal case:

> In the above cases of regressional and extremal Goodhart, there are issues with
> selection pressure for even simple systems when proxies are used. **These two
> classes require selection pressure, but do not involve an intervention on the
> part of the regulator.**

Their own footnote 1 then closes the door on booking any of their categories as a
formalization of the original:

> Because none of the terms were laid out formally, **the categories proposed do
> not match what was originally discussed.** A separate forthcoming paper intends
> to address the relationship between those formulations and the categories more
> formally explained here.

**What survives.** The non-identifiability witness described below remains a
sensible target *for Causal Goodhart specifically*, with two caveats now rather
than one: it gives possibility rather than tendency, **and it is one quarter of
the phenomenon rather than the sentence**. It should be booked under a Causal
Goodhart row if one is ever opened, never under BY-037's headline claim.

Goodhart's claim has a precise formal shape and it is not the reward-hacking one.
An association is *observed* -- estimated from data generated under one regime --
and is then *used for control*, which is to say the controlled variable is set
rather than watched. The claim is that the association then fails. Stripped of
monetary economics, that is the difference between the observational
distribution and the interventional one: what `P(y ∣ x)` licenses is not what
`P(y ∣ do(x))` licenses, and a regularity read off the first is not preserved by
the second.

Chapter III supplies the mechanism at length and it is the standard one --
liability management, disintermediation, banks inventing instruments outside the
targeted aggregate. Strathern's report of Goodhart, via Hoskin, is a report of
exactly this mechanism rather than of his sentence.

**The atlas already has the substrate**, which is why this arrow is worth more
than arrow G. `AISafetyAtlas.Causal.BayesianNetwork` carries the interventional
semantics: `AISafetyAtlas.Causal.Model.interventionalFamily` is the family of
distributions under each hard intervention, and
`AISafetyAtlas.Causal.eq_family_of_isCausalBayesNetwork` is Pearl's equation
(1.37), the statement that the graph and the mechanisms determine that family.

**What is missing is the separation, and the module says so in prose.** Its header
states that not every interventional distribution is determined by the
observational one, *and that no claim in it says otherwise* -- it even names where
the slack lives: a parent configuration carrying zero observational mass leaves
its child's mechanism unconstrained by the observational distribution, while
`do(pa)` still reads it. So the arrow needs one thing that does not yet exist:
**two models agreeing observationally and disagreeing interventionally**, which
is a witness, not a theory. The module's own header names the construction.

That is a smaller and better-specified obligation than arrow G's missing verb,
and unlike arrows A, B and F it does not need a new source formalized -- it needs
a witness against machinery the atlas has already built and pinned.

**Caveat before anyone writes it.** A non-identifiability witness would formalize
*"a regularity read observationally need not survive intervention"*. Goodhart says
something stronger and vaguer: *"will tend to collapse"*. The witness gives the
possibility, not the tendency, so it would grade **Narrower** against print unless
the tendency is separately argued. Record that when the row is written; do not
let the witness be booked as the whole sentence.

## D3 — the ranking, and the first target

**Amended 2026-09-10.** The ranking below stands as a ranking of *coverage*
targets. What it did not settle, and what the day's reading forces, is a prior
question about shape.

### The constraint, which is now the load-bearing decision on this row

**BY-037 is a two-variable claim. Every one-variable rendering of it is a category
error, and this document made that error twice before catching it.**

Manheim & Garrabrant's definition makes the goal and the proxy constitutive, and
each of the four variants is a different way their *link* fails. An earlier review
refuted arrow E on precisely this ground -- `Arena.collapse` is one map's image,
and there is no second object for it to come apart from. Arrow G was then written
with the same defect and has been amended rather than repaired. So the constraint
is worth stating as a decision rather than leaving implicit in three refutations:

> Nothing is a formalization of BY-037 unless it carries a goal `G`, a proxy `M`,
> and a relation between them that the statement is about. A theorem about one
> function, however suggestive its name, is not a candidate.

### The consequence: build the carrier from the simplest two-variable model

The minimal two-variable model in any pinned source is Manheim & Garrabrant's
equation (1), the whole of Regressional Goodhart:

> `M = G + normal(μ, σ²)`

and their reading of it: *"when `M` is large, you can expect `G` to be predictably
smaller than `M`"*, which they call the simplest Goodhart effect and also *"the
most fundamental: it cannot be avoided. No matter what measure is chosen for
optimization, an inexact metric necessarily leads to a divergence between the
goal and the metric in the tail."*

The provable content, stated so that it can be checked rather than gestured at:

> For independent real random variables `G` and `N` with `N` integrable, write
> `M = G + N`. For any threshold `c` with `0 < P(M > c) < 1`,
> `E[M − G ∣ M > c] ≥ E[M − G]`, strictly when `N` is non-degenerate.

That is *selection on the proxy inflates the proxy--goal gap above its
unconditional value* -- "tails come apart" with both variables present and no
`do`-operator anywhere. The mechanism is a covariance inequality: `N` and the
indicator of `M > c` are positively associated because `M` is increasing in `N`.

**Two things to note before anyone writes it.** First, this is **wider than
print**: it needs independence and integrability, not Gaussianity, so Manheim &
Garrabrant's normal noise is one instance. Widening is welcome under the standing
rule, but the *printed* Gaussian case must still be recoverable, and
`ProbabilityTheory.gaussianReal` is the pinned Mathlib carrier for it. Second,
whether Mathlib already has the association inequality in usable form is
**unchecked** -- do not plan around it until it has been searched by declaration
shape.

### Amended 2026-09-10, on building it: `AISafetyAtlas.Goodhart.Regressional`

The carrier is built. Three things this section left open are now closed, and one
of them was closed by finding this section wrong.

**The Mathlib question, answered: no, and it was not close.** Searched by
declaration shape (`(∫ _, _ ∂_) * (∫ _, _ ∂_) ≤ ∫ _, _ * _ ∂_`, which returns
nothing), by natural language for the association and Chebyshev-correlation
inequalities, and by name over the whole pinned tree. The association family in
Mathlib is `Mathlib.Combinatorics.SetFamily.FourFunctions` -- the four-functions
theorem and FKG over a finite distributive lattice, with `Finset` sums -- and
`Mathlib.Algebra.Order.Chebyshev`, Chebyshev's sum inequality, also over a
`Finset`. Neither reaches a measure on the line. Nothing under
`Mathlib/MeasureTheory` or `Mathlib/Probability` mentions monovariance,
antivariance, positive association, Harris or FKG at all. So the one-dimensional
core is the atlas's own, proved directly from the split at the threshold, and it
is routed under `lean-routing.md` as generic mathematics kept here with the
upstream offer named but not opened.

**The strictness clause above is false, and the module does not carry it.** "For
any threshold `c` with `0 < P(M > c) < 1` ... strictly when `N` is
non-degenerate" fails on a two-point example: let `G` be uniform on `{0, 10}`,
let `N` be uniform on `{0, 1}`, and take `c = 5`. Then `M > c` holds exactly when
`G = 10`, so `P(M > c) = 1/2`, the noise is non-degenerate, and yet the selection
event is independent of `N` -- the conditional and unconditional expected gaps
are both `1/2` and the inequality is an equality. A threshold that only the goal
decides filters no noise. What strictness actually needs is that the threshold
cuts the noise law on a set of goal values of positive mass, and that is the
hypothesis `gap_selection_gt` takes. It is discharged automatically in print's
Gaussian case, where every threshold cuts a Gaussian, which is why the
one-line form of the claim survives for the case the paper actually states.

**Print's Gaussian case is recoverable, at one implicit hypothesis.** At variance
zero `ProbabilityTheory.gaussianReal` is a Dirac measure: there is no noise, and
no inequality is strict. The corollary therefore asks for a nonzero variance --
the same kind of move as the nonempty proxy-attribute set the Zhuang &
Hadfield-Menell transcription owes, and recorded the same way, in the module.

**One further discrepancy inside the paper, recorded where the statement is.**
The setup paragraph writes the permissible region as `M(s) >= c`; section 1, the
sentence being formalized, writes "the values of `G` when `M > c`". The strict
reading is section 1's and is the one the module takes. The proof uses only that
the selected slice lies above the threshold and its complement below, so the
non-strict selection event is the same argument.

**No ledger row is written.** As this document says at the top, nothing here
writes a coverage row, and this module is not coverage of Manheim & Garrabrant
in any case -- they number nothing. The module is routed as atlas-original work
citing them for the model, and its provenance lives in its own header.

> **Amended 2026-09-11.** A ledger row now exists:
> `LAND-GOODHART-SELECTION-001`, hosting both
> `AISafetyAtlas.Goodhart.Regressional` and `AISafetyAtlas.Goodhart.Extremal`,
> and the paper is graded in section 17 of
> `docs/provenance/source-coverage-audit.md`. **The routing above is unchanged
> and the row states it explicitly** -- the model is print's, the theorems are
> this atlas's, and nothing is booked as coverage of a printed result, because
> there is no printed result. Two things forced the row. The reason given at the
> top of this document for writing none was that `registry.yaml`,
> `AISafetyAtlas.lean`, `docs/status/` and the source-coverage audit were *in
> flight on two other branches*; they merged on 2026-09-10 and that reason
> expired. And `scripts/check_coverage_audit.py` couples the two structurally:
> a section that names a target module must have a row hosting it, and a graded
> section that names no target module is itself flagged. So the source could not
> be graded at all while the modules held no row. If the maintainer prefers the
> row withdrawn, the section goes with it and both modules return to the audit's
> module-ledger block as ungraded debt.

### So does Regressional outrank Zhuang & Hadfield-Menell as first target?

**For the statement, yes. For the ledger, no. They are different jobs and both
should be done, in that order.**

Regressional is the better *object*: two variables, one line, no `ℝ^L`, no MDP,
no causal apparatus, and it is the variant its own authors call unavoidable. It is
also the reading closest to Goodhart's own sentence once the proxy framing is
restored -- a regularity fitted on the bulk and then exploited in the tail, where
it was never estimated.

It is the worse *citation*, and the reason is that review's original refutation
of arrow C, which stands: Manheim & Garrabrant number nothing. The statement above
is this atlas's sharpening of their prose, not a transcription of a printed
theorem, and the ledger's conventions do not let an unnumbered gloss be booked as
coverage of a source's result.

The resolution is to stop treating those as the same question:

1. **Build the carrier first, from Regressional.** `G`, `M`, the gap, and the
   selection event, with the inequality above as its first theorem. Route it as
   atlas-original work citing Manheim & Garrabrant for the model, graded on its
   own terms rather than as coverage of them.
2. **Then book coverage from Zhuang & Hadfield-Menell Theorem 1**, which is a
   numbered theorem in a published venue and already has its missing nonemptiness
   hypothesis recorded on this branch. It should be stated *against the carrier*
   rather than beside it.

That ordering also settles what to do with the causal reading: a Causal Goodhart
row, if opened, sits on the same carrier with an intervention added, which is the
honest place for the retracted arrow H to land.

### Amended 2026-09-10, on executing step 2: `AISafetyAtlas.Goodhart.Overoptimization`

Step 2 above says the theorem "should be stated *against the carrier* rather
than beside it". It is stated beside it, and the instruction was wrong. The
check is below, because a negative that is not shown is indistinguishable from
one that was not looked for.

**They do not share an object.** Three things were compared, in this order.

1. *Type.* The carrier's `goal`, `gap`, `proxy` elaborate at `ℝ × ℝ → ℝ` and
   `selected` at `Set (ℝ × ℝ)`. The arity is two real variables and is fixed in
   the definitions, not a parameter. Zhuang & Hadfield-Menell's state is an
   arbitrary `Fin L → ℝ` with the proxy attributes an arbitrary strict subset.
   Nothing instantiates the first at the second.
2. *Modality.* Every theorem on the carrier is about `μ.prod ν`, and what they
   assert is an inequality between integrals; the independence of the goal and
   the gap is the content, not scaffolding. Theorem 1 carries no measure and no
   randomness at all, and its selection is a maximum over a constraint set, not
   a superlevel set of the proxy. There is no measure to put on the attribute
   space that would make one the other.
3. *Orientation, which is the interesting one.* At `L = 2` with one proxy
   attribute the two look as though they might coincide, and the linear map
   `(s₀, s₁) ↦ (s₀ + s₁, −s₁)` even carries one triple's `proxy = goal + gap`
   onto the other's. But it carries them the wrong way round. On the carrier the
   proxy is the sum and the goal is a coordinate; in Theorem 1 the proxy is a
   coordinate and the goal is a function of all of them. Reading the resemblance
   as an instantiation would have swapped the goal and the proxy — which is the
   arity mistake this document has now made three times, in a fourth costume.

**The right shared object, if a third consumer ever appears.** A state space
`X`, two functions `goal proxy : X → ℝ` on it, the gap `proxy − goal`, and a set
`sel : Set X` of the states selection can produce. Regressional instantiates
`sel` as a superlevel set of the proxy and reads the conclusion in expectation
under a product measure; Theorem 1 instantiates `sel` as the proxy's argmax over
a feasible set and reads it pointwise. Both would then be instances of "the gap
on `sel` exceeds the gap off it". That abstraction is not built: it would have
exactly two consumers, in different files, and neither would get shorter. It is
recorded here so the next row on this cluster can decide with the comparison in
front of it rather than repeating it.

**What was built instead.** `AISafetyAtlas.Goodhart.Overoptimization`, standing
on its own imports, with the comparison in its header and no import of
`AISafetyAtlas.Goodhart.Regressional` — an import would have put a dependency
edge in the generated graph asserting exactly the relation this section denies.
The bridge is at the level of vocabulary rather than of definitions:
`gap_le_of_unmentioned_eq_lowerBound` states Theorem 1's consequence in the
carrier's three words, pointwise. Optimizing the proxy does not merely fail to
raise the goal; it lands on the point of maximal proxy--goal gap within its own
proxy level set.

**Five hypotheses the printed statement leaves implicit.** Each is in the module
header; two of them are new to this document.

* *The proxy attribute set must be nonempty.* Already recorded below and now
  discharged: it is a binder, and the example file inhabits every other
  hypothesis of the core lemma at an empty proxy set and exhibits the failing
  conclusion. The other half of print's `J < L`, that the proxy omits something,
  is not carried: dropping it is a vacuous-true widening, since a proxy over
  every attribute leaves the conclusion quantifying over nothing.
* *The lower bounds are a second constraint.* Print says the feasible set is
  `{s : C s ≤ 0}` for a `C` strictly increasing in each attribute, and
  separately that each attribute is bounded below. **Those two sentences are
  jointly unsatisfiable for a nonempty feasible set**: lowering a coordinate
  lowers `C`, so the sublevel set is unbounded below in every coordinate. The
  transcription carries the box as its own constraint. This is new; it was not
  noticed when the row was ranked.
* *Print's proof leaves out the step where the lower bound enters.* It justifies
  the feasibility of its perturbed state with "since `C` is strictly
  increasing", which covers the constraint half of feasibility and says nothing
  about the box half -- and the box is the only place the `bₖ` in the conclusion
  is used at all. The transcription supplies the step by taking the whole
  distance to the floor as `ε`. Also new.
* *Complete Optimization equates two reals, so the proxy is bounded above on the
  feasible set.* Carried as an upper-bound hypothesis rather than as a term.
  Writing it with Lean's indexed supremum instead would make the theorem
  **false**, and the refutation is concrete rather than a worry about junk
  values. Take two attributes, `C s = arctan (s 0) + arctan (s 1) - 3`, both
  floors at `0`, the first attribute as the proxy and the identity as the proxy
  utility. `C` is continuous and strictly increasing in each attribute, and the
  proxy is unbounded above on the feasible set, since `(x, 0)` is feasible for
  every `x ≥ 0`. So the indexed supremum returns `0`. The constant sequence at
  `(0, 5)` is feasible, converges, and its proxy limsup is `0`, so it would
  satisfy Complete Optimization written that way -- and its unmentioned
  attribute sits at `5`, not at its floor `0`.
* *Closedness of the feasible set is derived, not assumed.* Print assumes it;
  under the repair above it follows from continuity of `C`.

**What the printed hypotheses buy, measured.** The ranking below predicted that
the optimization sequence would be inert, and it is: the rate function, its
continuity, the initial state and the integral representation are carried in the
binders and unused. What the proof consumes is feasibility along the sequence,
its convergence, Complete Optimization, and continuity of the proxy, which is
what carries the limit through. The two binders the proof does not touch are
named with a leading underscore, so the finding is visible in the statement
rather than only in prose.

**The witness.** Two attributes on a unit budget, the first of them the proxy,
both floored at zero, the principal's utility weighting the unmentioned
attribute twice. The optimization sequence is
`![1 - Real.exp (-t), Real.exp (-t)]`, generated by an exponentially decaying
rate function, feasible throughout, converging to `![1, 0]`. Every binder of the
printed theorem is inhabited, including the integral representation and Complete
Optimization. The conclusion is not true where the sequence started, and what
the optimization cost is exact and strict: the principal's utility falls from
`2` to `1` and the proxy--goal gap rises from `-2` to `0`.

**The coverage row is proposed, not written.** `source-coverage-audit.md` is
contested by two other branches and coverage for BY-037 is parked until they
merge. The row to paste, in that file's six columns, under a new section
`## Zhuang & Hadfield-Menell, *Consequences of Misaligned AI* →
AISafetyAtlas.Goodhart.Overoptimization`:

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Thm 1 | for any continuous strictly increasing proxy utility based on `J < L` attributes, if `s(t)` converges to `s*` then `s*ₖ = bₖ` for `k ∈ K` | `zhuang_hadfield_menell_theorem_one`, core `proxyMax_unmentioned_eq_lowerBound` | Yes | **Same** | at print's binders, including the rate function and the integral representation of the optimization sequence, which the proof does not consume — recorded rather than dropped. Five hypotheses print leaves implicit are carried and named in the module header: the proxy attribute set is nonempty, without which the conclusion is false and `Examples…empty_proxyAttrs_breaks_the_conclusion` says so; the attribute lower bounds are a second constraint rather than a property of the first, which as printed is unsatisfiable; print's proof justifies the feasibility of its perturbation by monotonicity of `C` alone and leaves out the box step, which is the only place the conclusion's `bₖ` enters; Complete Optimization's supremum is carried as an upper-bound hypothesis, since the indexed-supremum notation would make the statement false at an unbounded proxy, refuted at an arctangent budget in the plan document; and closedness of the feasible set is derived from continuity rather than assumed. The core `proxyMax_unmentioned_eq_lowerBound` is **Wider** — arbitrary attribute type, no finiteness, and the maximizing property in place of the sequence that delivers it. Witnessed by `Examples…unmentioned_at_floor`, where the unmentioned attribute is driven from `1` to its floor and the principal's utility strictly falls |

Three results ride with it and are not coverage of anything printed:
`le_of_unmentioned_eq_lowerBound`, `gap_le_of_unmentioned_eq_lowerBound`, and
`monotone_of_strictMonoCoord`, which derives the coordinatewise order's
`Monotone` from print's coordinatewise strict increase at a finite attribute set
and is what lets the gap corollary ask for the weaker of the two.


Ranked by the three discriminators the atlas actually uses: transcribable at
print scope against the pinned Mathlib; in the impossibility register; and
checkable against an existing reproduced proof.

| Rank | Target | Print scope reachable | Register | External check | Substrate cost |
|---|---|---|---|---|---|
| 1 | Zhuang & Hadfield-Menell Theorem 1 | yes | forced degradation | none | none — `Fin L → ℝ`, one constraint function |
| 2 | Hennessy & Goodhart Proposition 1 | yes | closed-form bias | none | a quadratic best response and a Ridge constraint |
| 3 | Zhuang & Hadfield-Menell Theorem 2 | yes | iff-characterization | none | compactness of upper contour sets ∩ feasible set |
| 4 | Skalse Theorem 1 + Corollary 1 | only with the occupancy reduction | impossibility | yes | a fourth MDP object, or reuse of the one arriving on `wireheading-precision` |
| 5 | Skalse Theorem 2's off-by-one, stated and refuted | yes, once rank 4 exists | refutation | yes | shares rank 4's |
| 6 | Karwowski et al. Theorem 1 (optimal stopping) | yes in principle | quantitative bound | none | occupancy geometry, projected angles, Boltzmann policies |
| — | El-Mhamdi & Hoang; Majka & El-Mhamdi | not at pinned Mathlib | asymptotic | none | regular variation and tail asymptotics Mathlib does not carry |
| — | Manheim & Garrabrant; Ashton; Maier et al.; Talyigás et al.; Pan et al.; Gao et al. | no statement to transcribe | — | — | — |

**First target: Zhuang & Hadfield-Menell Theorem 1.** Three reasons, in order.

*It is small, and smaller than it looks.* The printed setup carries a rate
function, an integral and a limit, but the conclusion needs only two consequences
of them: that the limit point is feasible (their `S` is closed) and that the
proxy attains its supremum there (their Complete Optimization assumption plus
continuity of the proxy). The proof is then four lines of mathematics: if some
unmentioned attribute sat strictly above its floor, lower it — the constraint
function is strictly increasing in every attribute, so this frees slack — then
raise a proxy attribute by a continuity argument, and the proxy exceeds its own
supremum. Everything in it is `Fin L → ℝ`, continuity, and monotonicity: pinned
Mathlib carries all of it and nothing else is needed.

*It is the arrow that survives at the lowest price.* Arrow A above, in one
theorem, with no bridging lemma between the statement and the requirement.

*It leaves the expensive question honest.* Stating it at print scope means
carrying the optimization sequence in the binders even though the proof does not
consume it. That is the right way round: the statement is the printed one, and
the fact that the proof uses two of its hypotheses is a finding to record, not a
licence to drop them. Record it; do not narrow the statement.

The worked model the example rule requires is small: `L = 2`, `J = {0}`,
`C s = s 0 + s 1 - 1`, both lower bounds `0`, proxy `s ↦ s 0`. The supremum is
attained at `(1, 0)` and the unmentioned attribute sits at its floor.

*One edge case the transcription must decide.* The printed hypothesis is a proxy
"based on `J < L` attributes", and the paper's setup takes the proxy attributes
to be a subset of `{1, …, L}` without excluding the empty one. At `J = 0` the
proxy is a constant, "strictly increasing" is vacuously true of it, every
feasible state attains its supremum, and the conclusion is false — nothing
pushes the omitted attributes anywhere. So the Lean statement owes a nonempty
proxy-attribute set. That is a hypothesis the printed statement leaves implicit,
not a narrowing: adding it is the reading under which the sentence is true, and
the strict inequality in `J < L` shows the authors were counting a proper
nonempty subset. Say so where the statement is transcribed.

*Discharged 2026-09-10.* It is a binder of
`zhuang_hadfield_menell_theorem_one`, it is named in that module's header, and
the example file inhabits every other hypothesis of the core lemma at an empty
proxy attribute set and exhibits the failing conclusion. See the amendment
above.

**Rank 4 and the substrate question.** Skalse Theorem 1 at print scope needs
policies, occupancy measures, and the fact that the occupancy image of an open
policy set is open in the affine subspace it spans. That is a fourth MDP object
if built here — the atlas already has the corrupted-reward model behind
`AISafetyAtlas.Wireheading.CRMDP.Model.everitt_theorem_eleven`,
`wireheading-precision` is bringing a stochastic one, and audieleon carries a
third in the wild. Do not build a fourth. Rank 4 waits for the merge and then
asks whether the stochastic model on that branch can carry occupancy measures;
if it cannot, that is a costed answer, not a reason to start over.
**Answered 2026-09-13 in `source-coverage-audit.md` section 26**, and the answer
was the costed no this paragraph anticipated: `vPi_isFixedPt` graded
Partial/Narrower, and the audit stated that the atlas had no object of this kind
at all — an occupancy embedding, and value as a linear functional of the reward —
so nothing at print scope was statable without them. **The cost was then paid, on
2026-09-20**: `AISafetyAtlas.Decision.Occupancy` builds the occupancy layer from
the transition kernel, the initial distribution and the discount, and
`AISafetyAtlas.Goodhart.Hackability` states Definitions 1 and 2 on it. It is a
*fifth* value computation in the sense this paragraph warned about, and the
warning is answered rather than ignored: it is the only one that is a linear
functional of the reward, nothing was removed, and the missing bridge to `vPi`
is recorded in section 26 and in the module docstring instead of being left
silent. This paragraph is left standing because it records what was asked; it is
no longer a task. The row is
numbered 4 rather than 3 because Hennessy & Goodhart, added after the table was
first drawn, is cheaper than both of the results above it in cost and closer to
the row's own citation; see the section below.

### Amended 2026-09-10, on the second Manheim & Garrabrant variant: `AISafetyAtlas.Goodhart.Extremal`

Arrow C stands: the paper numbers nothing, and this module is not coverage of it.
It is booked exactly as `AISafetyAtlas.Goodhart.Regressional` is — atlas-original
work citing the paper for the model, with its provenance in its own header and no
ledger row. Section 2's two sub-variants, *Model Insufficiency* (equation (2)) and
*Change in Regime* (equation (3)), were read from a rendered image of page 3.

**Both sub-variants are the same statement, and print says so.** Section 2's own
framing is that extremal Goodhart "can occur in two ways": either the proxy was
simplified on too few observations, or the generating process differs off the
observed region. Both are the claim that the goal–proxy relationship was *fitted
on one region and used on another*. The module therefore states it once —
agreement with a learned relationship on the observed region does not constrain
the goal on the selection event — and instantiates it twice.

**What print does not fix, and had to be chosen.** Three things, each recorded in
the module header rather than only here.

* Equation (2) writes `M = G(sᵢ) + G'(sᵢ)` and never says what `G'` is. The
  reading taken — model error, small where the fit was made — comes from the
  paragraph under it, not from the equation.
* Print never says the fit is *quantitatively* accurate on the observed region.
  Without a tolerance the sub-variant is a mood rather than a hypothesis, so the
  module carries one, `ε`, and the statement is trivial at `ε` large.
* The learned relationship is carried as a parameter `f : ℝ → ℝ`. That is the
  one place where a careless rendering would have introduced the third object
  this document has now warned against four times. It does not: `f` relates the
  two objects the paper's own definition makes constitutive, and the two printed
  models are the two values `f = id` and `f = (· + x)`.

**The escape is a hypothesis, not a theorem, and that is deliberate.** Print
asserts that selection moves the state off the observed region. The collapse
theorem takes that assertion as its hypothesis, so a reader with a different
reason for the escape may use it; boundedness of the proxy on the observed region
is offered separately as one sufficient condition. Taking the escape as a
hypothesis is wider than deriving it, which is why it is stated that way round.

**What is not proved, and is print's word.** Print says selection *causes* the
collapse. Nothing in the module is causal. What is proved is that selection lands
outside the fitted region and that the fitted region's evidence is silent there.
A statement in which the act of selecting changes the relationship is the paper's
*third* category, and the retracted arrow H above is where it belongs.

## D4 — audieleon/goodhart: cite it, do not vendor it

Cloned again on 2026-09-10; `HEAD` is still
`29128f3f9bcafb30d019682b63c1b582bcadf7b9`, the revision the row pins. The
statement-match reading is in
[docs/provenance/external-formalizations.md](external-formalizations.md); the
short form:

- Its Theorem 1 file is a faithful rendering of the *linear-algebraic core* of
  Skalse Theorem 1 — an open set of value vectors, values as inner products, and
  the conclusion that a non-trivial unhackable pair is equivalent. What it does
  not carry is the reduction from an MDP to that setting, which is where the
  printed theorem's quantifier over MDPs lives.
- Its Theorem 3 file assumes the paper's linear-algebra content as a hypothesis
  rather than deriving it, so the file's headline names promise more than the
  statements deliver.
- Its two general "existence" theorems produce witnesses that are trivial on the
  policy set, and the paper's Theorem 2 excludes exactly those. They are not
  Theorem 2.
- Its `two_policy_nontrivial_impossible` and `two_policy_strong_impossible` are
  the interesting part, and they are a **refutation of the printed Theorem 2**.

**Depend: no.** The version skew is fatal on its own — the repository pins Lean
`v4.30.0-rc2` against Mathlib `9268b22206b0425419498769f780a91dee03bcf3`; the
atlas pins `v4.33.0` against `db584cd6d46c92f209a44c0f1c829460d327499d`. Beyond
that, the companion paper the repository cites has no public URL at all: its
`CITATION.cff` names *Catching Goodhart's Law Before Training: Static Reward
Analysis with Formal Guarantees*, Sheridan, 2026, with no venue, DOI or link, and
a search finds no such paper. Two of its own READMEs contradict each other about
whether Skalse is formalized at all.

**Port: no, and not because of the licence.** Both projects are Apache-2.0, the
upstream carries no `NOTICE` file, so a port would incur §4(a)–(c) — keep the
licence text, keep the notices, state the changes — and no §4(d) obligation.
The reason not to port is that only about 230 of its 1,351 Skalse lines say what
their names claim, and porting a file whose headline theorem assumes its own
content would import a fidelity defect into a tree whose whole discipline is
catching those.

> **Scoped 2026-09-11. This verdict covers `proofs/GoodhartProofs/Skalse/` and
> nothing else.** Read as written it says "do not port this repository", and it
> has been cited that way. But every reason it gives is about the Skalse files:
> the line count is *"230 of its 1,351 **Skalse** lines"*, the fidelity defect is
> a Skalse theorem file that assumes its own content, and the two general
> existence theorems are Skalse Theorem 2 candidates. **None of that is evidence
> about `proofs/GoodhartProofs/MDP/`**, which is a different subtree —
> `Defs.lean`, `Bellman.lean`, `Shaping.lean`, `Undiscounted.lean` — carrying a
> sorry-free `ContractingWith` route to `vPi` and `vStar` and no Skalse content
> at all. It is the nearest external match to
> `AISafetyAtlas.Decision.DiscountedValue`, fourteen of whose twenty-two
> declarations correspond to one of its name for name, and it was left out of
> that module's reuse survey on the strength of this paragraph. The MDP subtree
> is **not adjudicated**; costing it is item 3.1 of the integration plan. The
> version skew under **Depend: no** above is repository-wide and does stand for
> both subtrees.

**Cite: yes.** It is the only `REPRODUCED` Lean lead outside the six pinned
corpora and had no section in the external-formalizations narrative; this branch
adds one. When the atlas builds rank 4, use its Theorem 1 file as a *reference
proof to read against*, and its two-policy theorems as a cross-check on the
refutation — but the refutation itself does not depend on it, because the
off-by-one is visible in the paper's own printed proof.

## The Theorem 2 defect, since a later reader will want the argument

Skalse Theorem 2 claims that for any finite policy set containing two policies
with distinct occupancy measures, and any `R₁`, a **non-trivial** `R₂` exists
that is unhackable with `R₁` and not equivalent to it. The printed proof walks a
path from `R₁` to `−R₁` and takes the first reward at which an inequality
becomes an equality; for the witness to be non-trivial the path must avoid the
set of rewards that are trivial on the policy set. The dimension count is:

> if `F(Π̂)` has at least `d` linearly independent vectors, then the set of all
> such vectors `R` forms a linear subspace with at most `|S||A| − d` dimensions

Being trivial on `Π̂` means all the inner products are *equal*, not that they are
*zero*, so `d` independent vectors impose `d − 1` independent equations and the
trivial set has dimension `|S||A| − (d − 1)`. At `d = 2` — the paper's own
hypothesis, two policies with distinct occupancy measures — that is a hyperplane,
`|S||A| − 1`, which is exactly the dimension the proof then argues cannot occur
("only a hyperplane … can split `R^{|S||A|}` into two disconnected components").
`R₁` and `−R₁` lie on opposite sides of it whenever `R₁` is non-trivial, so every
path crosses it and the construction cannot avoid a trivial witness. The
conclusion is not merely unproved but false on the natural reading: on a
two-element policy set, `R₂` non-trivial and unhackable with a non-trivial `R₁`
forces equivalence.

Corollary 3 fails at the same place, and — **checked directly on 2026-09-10,
against a rendered image of page 8** — it does not need Theorem 2's dimension
count at all. Its printed statement is:

> **Corollary 3.** For any finite set of policies `Π̂`, any environment, and any
> reward function `R`, if `|Π̂| ≥ 2` and `J(π) ≠ J(π')` for all `π, π' ∈ Π̂` then
> there is a non-trivial simplification of `R`.

Take `Π̂ = {π, π'}` with `J(π) ≠ J(π')`. Definition 2 requires a simplification
to equate some pair that `R` separates, and `{π, π'}` is the only pair there is,
so any simplification has `J₂(π) = J₂(π')` and is therefore constant on `Π̂` —
trivial, by the convention Definition 1's paragraph sets. So no non-trivial
simplification exists, from Definition 2 alone.

**Three refinements to the paragraph above, from re-deriving it rather than
restating it.**

* **The refutation of Theorem 2 needs `R₁` non-trivial on `Π̂`, and print does
  not ask for that.** If `J₁(π) = J₁(π')` then unhackability is vacuous — it
  needs a strict `J₁` inequality to bite — and any `R₂` separating the two
  policies is unhackable with `R₁` and not equivalent to it. So the printed
  statement is *true* at `|Π̂| = 2` when `R₁` happens to be trivial on `Π̂`, and
  false otherwise. `F(π) ≠ F(π')`, print's only hypothesis, does not decide
  which.
* **The correction is not `|Π̂| ≥ 3` for Theorem 2.** Trivial-on-`Π̂` is the
  linear subspace `{R : ⟨R, F(π) − F(π₀)⟩ = 0 for all π ∈ Π̂}`, whose codimension
  is the dimension of the affine hull of `F(Π̂)`. The complement of a subspace is
  connected exactly when that codimension is at least `2`, so what the path
  argument needs is `dim aff F(Π̂) ≥ 2` — three policies whose occupancy measures
  are **affinely independent**. Three policies with pairwise distinct occupancy
  measures that happen to be collinear still leave a hyperplane, and the path
  still has to cross it. `|Π̂| ≥ 3` is the right correction for Corollary 3,
  where the obstruction really is cardinality; it is not the right correction
  here.
* **Theorem 3's own criterion contradicts Definition 2 at the same instance, so
  the reading question cannot be localized to Theorem 2.** At `Π̂ = {π, π'}` with
  `J` distinct, both cells of Theorem 3's partition are singletons, so
  `Z₁ = Z₂ = {0}` and `dim(Z₁ ∪ Z₂) = 0`. Discounted occupancy vectors all have
  coordinate sum `1/(1−γ)`, so two *distinct* ones are automatically linearly
  independent and `dim(F(Π̂)) = 2`. Theorem 3's condition
  `dim(Z₁ ∪ ⋯ ∪ Zₘ) ≤ dim(F(Π̂)) − 2` reads `0 ≤ 0`, and the theorem therefore
  asserts a non-trivial simplification exists — which Definition 2 has just
  forbidden. The three statements are consistent only if "trivial" is read
  globally in Theorems 2–3 and Corollary 3 while being read relative to `Π̂` in
  Definition 1, Theorem 1 and Corollary 1. **A formalization has to choose, and
  the choice is not free**: on the relative reading Theorems 2–3 and Corollary 3
  are false at their smallest instances, and on the global reading they are true
  and carry no hackability content, because a reward that is globally
  non-constant may still be constant on `Π̂`.

Two readings of "non-trivial `R₂`" are available, since Theorem 2 omits the
"on `Π̂`" the surrounding statements carry. Read as trivial-on-`Π̂`, consistent
with Definition 1's convention, the theorem is false at `|Π̂| = 2`. Read as
globally non-constant, it is true and vacuous. The repository's own README
records the first reading and the `|Π̂| ≥ 3` correction; this branch reached the
same conclusion from the printed proof independently. Nothing here touches the
paper's substance, which is about large policy sets — but the atlas grades
statements, so if rank 4 is ever built the statement to carry is the corrected
one, with the defect recorded.

## Skalse et al. 2022, graded statement by statement (2026-09-10)

What the atlas can state today, and what each remaining statement is waiting on.
The document graded is the camera-ready pinned at
the private literature store,
sha256 `634ffa7ccb0225296482ef2961a38ba175bd8c1b97b998556a6bcfa7ad560210`.
Definitions 1–4 and Theorems 1–3 with their corollaries were read from rendered
images of pages 5–8, not from extracted text. This grades the *paper*; the
statement-by-statement grading of the one external Lean body that formalizes it
is separate, in
[`external-formalizations.md`](external-formalizations.md).

| Statement | Grade | What it is waiting on |
|---|---|---|
| Definition 1 (hackable / unhackable) | **Statable now** | Nothing. Two real-valued functions on an arbitrary set and one existential over a pair. No MDP, no measure, no topology. |
| Definition 2 (simplification), "equivalent on `Π`", "trivial on `Π`" | **Statable now** | Nothing. Same substrate. The "trivial simplification" clause needs the reading decision recorded above to be made explicitly and carried in the name. |
| Definitions 3–4 (`ε`-suboptimal, `δ`-deterministic) | **Statable now, useless alone** | Nothing to build; they are only interesting as hypotheses of Corollary 2, which is blocked. |
| **Theorem 1, linear core** | **Statable now, and this is the buildable target** | Nothing. See the shape below. |
| Theorem 1, at print scope | **Blocked** | An MDP with discounted occupancy measures, plus Lemma 1 and Propositions 1–2, which carry a policy set into `ℝ^{\|S\|(\|A\|−1)}` and make `F` a homeomorphism onto its image. D3 rank 4: do not build a fourth MDP object; wait for `wireheading-precision` and ask whether its stochastic model carries occupancy measures. |
| Lemma 1 | **Blocked, same reason** | It *is* the reduction; it is what Theorem 1 at print scope owes. |
| Corollary 1 | **Blocked** | Theorem 1 at print scope, plus the geometric fact that the policies taking every action with positive probability form an open subset of the stationary policies. |
| Corollary 2 | **Blocked** | Corollary 1, plus openness of the `ε`-suboptimal and `δ`-deterministic sets. |
| Theorem 2 | **Do not state as printed** | It is false at its smallest instance on the reading its own proof sketch uses. If it is ever built, state it at `dim aff F(Π̂) ≥ 2` and ship the two-policy refutation in the same module as the witness that print's hypothesis is not enough. |
| Theorem 3 | **Do not state** | Expensive, reading-dependent, and inconsistent with Definition 2 at `\|Π̂\| = 2` (above). Its content is a dimension criterion over the occupancy geometry, so it is blocked behind the same reduction as Theorem 1 and buys less. |
| Corollary 3 | **Do not state as printed** | False at `\|Π̂\| = 2` from Definition 2 alone. The corrected hypothesis is `\|Π̂\| ≥ 3`. |

### The one thing worth building, and its exact shape

Theorem 1's proof works in the coordinates the reduction produces, and that part
of it needs no MDP at all. Stripped of the reduction it is a statement about two
linear functionals on an open set:

> Let `U` be a nonempty open subset of a real normed space, and let `f, g` be
> continuous linear functionals. Say the pair is *unhackable on `U`* if there are
> no `x, y ∈ U` with `f x < f y` and `g x > g y`, and *non-trivial on `U`* if
> neither is constant on `U`. Then `g = λ • f` for some `λ > 0`.

State the conclusion that way rather than as "`f` and `g` induce the same strict
ordering on `U`". The proportionality is what the argument actually produces, it
holds on the whole space rather than on `U`, and it is what print needs:
Theorem 1 concludes equivalence on `Π̂`, not on the open subset `Π̇` inside it, so
a conclusion confined to `U` would owe a transfer step that the proportional form
does not.

The argument is three lines and uses openness exactly once. Unhackability says
`f x < f y → g x ≤ g y`. If `ker f ⊄ ker g`, pick `v` with `f v = 0` and
`g v ≠ 0`, and `w` with `f w ≠ 0`; take `x ∈ U` and, by openness, small `t, s`
with `x + t v ∈ U`, `x + s w ∈ U`, `g (x + t v) > g x` and `f (x + s w) > f x`
with `s` small enough that `g (x + s w) < g (x + t v)`. That pair is a hack. So
`ker f ⊆ ker g`, hence `g = λ f + c`; unhackability gives `λ ≥ 0` and
non-triviality of `g` gives `λ ≠ 0`.

Two things recommend it. It is the **contrapositive** BY-037 wants — every
non-trivial proxy that is not exactly order-equivalent to the true reward is
hackable — with the universal quantifier over proxies that this document's D2
says an arrow on this row must have. And it is honest about its scope: it states
the linear core and *names* the reduction as absent, which is exactly the grade
`external-formalizations.md` gives `audieleon/goodhart`'s Theorem 1 file. The
atlas would be building the same core; the difference is that the atlas would
say so in the header.

The paper's own second core is cheaper still and is worth recording beside it:
the paragraph before Lemma 1 argues that on the set of *non-stationary* policies
the result is "relatively straightforward", because mixing a reward-maximising
and a reward-minimising policy sweeps out a segment on which both values are
affine. That is a convexity argument with no topology in it, and it is a second
MDP-free statement of the same impossibility.

### One conjecture about the defect, offered as a lead and not as a fix

The two off-by-ones above may be one. Theorem 3's `Zᵢ` are *difference* vectors,
so `dim(Z₁ ∪ ⋯ ∪ Zₘ)` is an affine dimension; `dim(F(Π̂))` on the right of the
same inequality counts the occupancy vectors themselves, which is a linear
dimension and — because they all lie on the hyperplane of coordinate sum
`1/(1−γ)` — exactly one more than the affine dimension of `F(Π̂)`. Substituting
the affine dimension on the right makes Theorem 3's criterion read `0 ≤ −1` at
`|Π̂| = 2`, which agrees with Definition 2 instead of contradicting it; and the
same substitution is what Theorem 2's path argument needs, since the codimension
of the trivial subspace is the affine and not the linear dimension. So a single
linear-for-affine slip would account for both.

**This is a lead, not a verified correction.** It has been checked only at
`|Π̂| = 2`; whether the substituted criterion is the right one for Theorem 3 in
general has not been checked, and Theorem 3's proof is in the arXiv appendix,
which was not read for this grading.

### Resolved 2026-09-11: the appendix was read, and the slip is one proof step

The arXiv appendix, `d9a8567f6d5bc9fa23754b93…`, rendered pages 18 and 19, was
read. **The conjecture above is right, both off-by-ones are the same one, and it
sits in a single sentence.**

**The step.** Theorem 3's proof sets `D = dim(F(Π̂))`, treats `F(Π̂)` as a set of
vectors in `ℝᴰ`, and represents a reward by the `D`-dimensional vector `R⃗` that
fixes the *ordering* it induces — print is explicit that the *values* would need
`D + 1` parameters and that the height is dropped. It then writes:

> Next, note that `R₂` is trivial on `Π̂` if and only if `R⃗₂` is the zero vector `0⃗`.

**That is false.** Trivial on `Π̂` means `L₂` is *constant* on `F(Π̂)`, which is
`(F(π) − F(π')) · R⃗₂ = 0` for every pair — a condition of codimension equal to
the **affine** dimension of `F(Π̂)`, not the condition `R⃗₂ = 0⃗`. The two coincide
only when the origin lies in the affine hull of `F(Π̂)`, and it never does: every
discounted state-action occupancy has coordinate sum `1/(1−γ)`, so `F(Π̂)` lies on
a hyperplane missing the origin. The trivial rewards are a **line** in `ℝᴰ`, not a
point. That is the linear-for-affine substitution conjectured above, and this is
where it enters.

**Why it produces both defects.** Both Theorem 2 and Theorem 3 are proved by
walking a path from `R⃗₁` to `−R⃗₁` that avoids the rewards trivial on `Π̂`, and both
rely on that set failing to disconnect the space — Theorem 2's proof says so
outright, that the trivial set has *"at most `|S||A| − 2` dimensions"* and that
*"only a hyperplane … can split `ℝ^{|S||A|}` into two disconnected components"*.
The trivial set has codimension equal to the affine dimension of `F(Π̂)`. **At
`|Π̂| = 2` that affine dimension is `1`, so the trivial set is exactly a
hyperplane, it does disconnect, and both path arguments fail at the same
instance.** One slip, two broken theorems, which is what the conjecture above
guessed.

**Corollary 3's proof confirms the reading rather than avoiding it.** It argues
that singleton classes give `dim(Z₁ ∪ ⋯ ∪ Z_m) = 0`, that two policies with
`J(π) ≠ J(π')` give `F(π) ≠ F(π')`, and hence *"this means that `dim(F(Π̂)) ≥ 2`.
Thus the conditions of Theorem 3 are satisfied."* At `|Π̂| = 2` that is `0 ≤ 2 − 2`,
so print's own proof asserts a non-trivial simplification exists — while
Definition 2 forbids one, since with only one pair available any simplification
must set `J₂(π) = J₂(π')` and is therefore trivial. So this is **not** a typo in
the displayed criterion that the proofs silently work around: the proof derives
the false instance from the linear reading, deliberately.

**The corrected criterion, and what is not verified.** Carrying the correction
through: the equality-preserving space has dimension `D − D'`, it contains the
trivial line, and a path avoiding a line needs ambient dimension at least three,
so the condition becomes `D − D' ≥ 3`, that is

> `dim(Z₁ ∪ ⋯ ∪ Z_m) ≤ dim(F(Π̂)) − 3`,

equivalently print's own `− 2` with the **affine** dimension of `F(Π̂)` on the
right, since that affine dimension is `D − 1`. This agrees with the conjecture
above, derived independently from the proof rather than fitted to `|Π̂| = 2`.
Checked at two instances: at `|Π̂| = 2` it gives `0 ≤ −1`, correctly refusing,
where print gives `0 ≤ 0`; at `|Π̂| = 3` with distinct values and affinely
independent occupancies it gives `0 ≤ 0`, correctly permitting, and print agrees.
**Not verified:** that the corrected criterion is right in general, and in
particular the claim that avoiding the trivial line is the only obstruction the
path argument faces. Nothing here is machine-checked, and none of it is built.

**What this changes for the ledger.** Nothing yet — there is still no Lean for
Skalse, and D3's ranking is unchanged. What it changes is the price of Theorem 2
and Theorem 3 if they are ever stated: both need the corrected hypothesis, and
the two-policy instance is a witness that print's is not enough. The linear core
recommended above is untouched by all of this — it is Theorem 1's argument, which
does not use the path construction.

**Neither core is built here.** This section grades; D3's ranking still puts Zhuang &
Hadfield-Menell and Hennessy & Goodhart ahead of it, and the linear core has no
consumer in the tree yet.

## Two metadata claims that do not survive the documents

**The paper is titled "Reward Hacking", not "Reward Gaming".** The NeurIPS 2022
proceedings landing page carries the title *Defining and Characterizing Reward
Gaming*, and that index title is where the name comes from. The PDF the same
record links to was re-fetched from `proceedings.neurips.cc` on 2026-09-10 and
is **byte-identical** to the copy in the literature directory
(`sha256 634ffa7c…`), so the copy graded here is the proceedings document and
not a variant. It is titled *Defining and Characterizing Reward Hacking*, its
abstract says "reward hacking" and "unhackable", and the ACM Digital Library
record for the same proceedings also reads "hacking".

The interesting part is the residue. "Hacking" and "unhackable" occur 53 times
in that PDF; "gaming" and "gameable" occur four, and one of the four is a
**figure axis label** — "(a) `r_proxy` is gameable / (b) `r_proxy` is not
gameable" — with the other three a body sentence distinguishing tampering from
"reward gaming" and a citation to Legg's *Specification gaming*. A figure label
is exactly what a global rename misses. So the edit ran gaming → hacking, the
proceedings record was created before it and kept the old title in its title
field, and the document under that record is the later text. Published-is-
canonical points at the document. **The atlas keeps "reward hacking"**, and
records the index discrepancy rather than following it. **Corrected 2026-09-10,
later the same day:** an earlier version of this paragraph said the file in the
literature directory is still named `…-reward-gaming.pdf`. It is not; both the
camera-ready and the arXiv copy were renamed to `…-reward-hacking.pdf` when the
manifest entry was written, and the manifest records the rename. The sentence
described the state before the rename and was left standing after it.

**The two versions do not differ in the numbered statements.** Definitions 1–4,
Lemma 1, Theorems 1–3 and Corollaries 1–3 appear with identical wording and
identical numbering in the twelve-page camera-ready and in arXiv v2. The arXiv
version adds the appendix carrying the proofs and Propositions 1–4. There is no
version fork to adjudicate.

## Goodhart's own sentence, and what it changes

Goodhart 1975 could not be obtained (see the manifest). What was obtained is
Hennessy & Goodhart, *International Economic Review* 64(3), 2023 — Goodhart's
own return to the subject, peer reviewed, with Goodhart as second author — and
it quotes the law in its introduction as Goodhart states it:

> Any observed statistical regularity will tend to collapse once pressure is
> placed upon it for control purposes.

That is not the sentence BY-037 records. The row's informal claim — "when a
measure becomes a target, optimization pressure can destroy its value as a
measure" — is **Strathern's** rendering, which is consistent with the row citing
both sources but means the row has been graded against the more famous
paraphrase rather than the original. Goodhart's own statement is about a
*statistical regularity collapsing under control pressure*: the fitted relation
between the indicator and the target stops holding once the indicator is used to
control. Arrow A discharges Strathern's sentence well and Goodhart's only by
analogy; a reader who wants Goodhart's should be sent somewhere else.

**Somewhere else is the same paper.** Hennessy & Goodhart put a statistician in
Stackelberg leadership over a future cohort who manipulate their covariates at
known cost, and derive (Lemma 1, Propositions 1–4) that a naive penalized
regression carries a *Goodhart bias* proportional to the penalization — under
quadratic costs and naive Ridge, exactly the Ridge tuning parameter over the
cost — together with a coefficient adjustment that makes prediction
manipulation-proof. It is closed-form algebra over a best response, and it is
the only theorem found in this cluster that formalizes Goodhart's own wording
rather than Strathern's.

It also bears on BY-038, and qualifies this file's claim that nothing reaches
that row. In their model the agents change their *actual covariates*, not their
reports: the process the indicator measures is deformed by the indicator being
used, which is Campbell's second law in miniature. It is not a formalization of
Campbell — there is no monitored social process, and the deformation is
individually rational rather than a corruption of a measuring institution — but
it is the nearest thing in the corpus, and it sits in the strategic-
classification register the survey names as the place to look next.

**Ranking effect.** Insert Hennessy & Goodhart Proposition 1 at rank 2, ahead of
Zhuang & Hadfield-Menell Theorem 2: it is smaller than Theorem 2, it discharges
the other half of BY-037's source pair, and it is the only candidate with an
author in common with the row's own citation. Its cost is a quadratic best
response and a Ridge constraint — convex optimization the pinned Mathlib
supports — against Theorem 2's compactness characterization.

## What this branch does not do

- No coverage row for BY-037 or BY-038, by instruction: `registry.yaml`,
  `AISafetyAtlas.lean`, `docs/status/` and the source-coverage audit are all in
  flight on two other branches.
- ~~No Lean.~~ **Superseded 2026-09-10.** Rank 1 is built
  (`AISafetyAtlas.Goodhart.Overoptimization`), and so are both Manheim &
  Garrabrant variants that need no new substrate
  (`AISafetyAtlas.Goodhart.Regressional`, `AISafetyAtlas.Goodhart.Extremal`),
  each as atlas-original work rather than as coverage. Ranks 2–4 are not
  started.
- Strathern 1997 and Goodhart 1975 remain unread. Both rows' original source
  references are therefore still ungraded against their sources; the manifest
  records the routes.
