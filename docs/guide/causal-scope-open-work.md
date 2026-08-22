# Causal layer: open scope work, and what each axis would cost

**This is a planning note, not provenance.** It prices refactors the atlas has
not done, so that the coverage audit's standing rule — a `Narrower` row is a
defect until discharged, proved unclosable, or **costed** — has somewhere to
point for the third option. What the causal layer *does* state, and how faithful
each statement is to its printed source, is in
[`source-coverage-audit.md`](../provenance/source-coverage-audit.md) sections 6,
7 and 8, and in the `LAND-CAUSAL-*` notes in `registry.yaml`. Those are the
provenance; this is the backlog behind them.

It was filed under `docs/provenance/` as `causal-narrowing-triage.md` until
2026-08-22, which was a category error: the `*-triage.md` notes there are
statement-level assessments of *upstream candidate formalizations*, and this
note assesses work the atlas would do itself.

Date: 2026-08-22. Grades as of `source-coverage-audit.md` sections 6 and 8.

> **Status: axes C and D were executed after this was written, and doing them
> corrected the note.** They are not two axes that happened to be cheaper
> together; they are **one** axis, and `wellFounded_iff_exists_rank` proves it —
> while `parents` was a `Finset`, well-foundedness and an `ℕ`-valued rank
> admitted exactly the same models, so D alone was not a generalization at all.
> **And they closed one row, not three.** This note predicted Definitions 3, 4
> and 5. Only Definition 3 closed. Definitions 4 and 5 keep a field print does
> not write — well-foundedness of the parent relation — and that axis is now
> labelled *provably not closable* with a Lean witness rather than closed —
> **and that label was itself retracted**, because the witness is
> about totalising `eval` and not about the class the audit grades. What D
> shrank to became **axis E**, which was executed and closed
> Definition 4 — the second and last row Definitions 1 to 5 give up. The
> prediction that the `Mixed` policy row would become plainly `Wider` was wrong
> too; see the correction at the end. What survives is the pricing of A and B,
> and the finding that no axis here blocks a theorem.

**Five `Narrower` rows and two `Mixed`, as of 2026-08-22.** This paragraph read
*"seven `Narrower` and one `Mixed`"* until then, and both halves went stale on
together: Definitions 3 and 4 closed, and a printed sentence that had never been
rowed was added and graded `Mixed`. The live set is RE24 §2.2's value and
regret, Everitt Definitions 1, 2 and 5, and the two `Mixed` rows — the policy
paragraph and the policy-invariance sentence.

**One of the two `Mixed` rows is not a definition**, which breaks a line this
note and the audit both carried: that every `Narrower` or `Mixed` row is a
definition and no printed theorem is narrower. The invariance row is a printed
*assertion of a fact*. Both `Mixed` labels end in *"(asserted after Def. 4)"*, so
anything that classifies rows by matching `Def.` in the label will put the
assertion in the definition bucket.

They are **not seven independent problems**: they are four axes as
first written, five after D split, and six once the expectation layer's
`[Fintype V]` was adjudicated on 2026-08-22. Every upward revision of that count
was a row carrying an axis this note had not enumerated, which is why axes are
now read off the declarations' binders rather than off the printed object. Most rows carry an axis they inherit rather than one they
introduce.
This note prices each axis, because the standing rule says a narrowing must be
discharged, proved unclosable, or **costed**, and until now only the first two
states had been used.

| axis | rows it makes `Narrower` | introduced by | closable? |
|---|---|---|---|
| **A** unmediated projection | RE24 §2.2 value, §2.2 regret | `Causal.Model` having no decision or utility vertices | yes, by construction |
| **B** finite domains | Everitt Defs. 1–2 | `dom edom : V → ℕ` on `SCM` | yes, by refactor — **still open** |
| **C** finite indegree | Everitt Defs. 1–5 | `parents : V → Finset V` on `SCM` and `CID` | **CLOSED 2026-08-22** |
| **D** `ℕ`-ranked acyclicity | Everitt Defs. 1–5 | `acyclic : ∃ rank : V → ℕ` on `SCM` and `CID` | **CLOSED 2026-08-22** |
| **E** well-foundedness of the parent relation | Everitt Defs. 1, 2, 4, 5 | `SCM.wellFounded` and `SCIM.graph_wellFounded` — what D shrank to | **CLOSED 2026-08-22**, by moving the field to a class |
| **F** the expectation layer is a finite sum | Everitt Def. 1, Def. 5, policy row | `[Fintype V]` on `exoJoint`, `jointProb`, `expectedUtility` | yes in principle, by a measure — **open, and costed, and not recommended** |

Definitions 3, 4 and 5 introduce **nothing**: they are `Narrower` purely through
C and D, reached via `CID` and `SCIM.graph`. Closing C and D moves four rows at
once. Definition 2 introduces nothing either — it copies Definition 1's fields.

---

## Axis A — decision and utility are not graph vertices

**What print says.** RE24 §2.2 writes expected utility and regret over a causal
influence diagram, where the decision and the utility are vertices of the graph
and the equation is over that diagram.

**What the atlas has.** `Causal.Model` is a causal Bayesian network with no
decision or utility vertex. `Model.value` and `Model.regret` are the *unmediated
projection*: the same arithmetic, over a policy applied to a chance network.

**Cost.** A construction, not a refactor, and the object at the far end is
already built — but it is `Causal.DecisionNetwork`, not `Causal.SCIM`. An
earlier draft of this paragraph named the SCIM and a bridge from a SCIM decision
vertex; that is the wrong endpoint. RE24 §2.2 is stated on `DecisionNetwork`,
which is RE24's own Definition 4 over `Causal.Model`, and the missing theorem is
`DecisionNetwork.expectedUtility = Model.value` under `IsUnmediated`. Estimate: a
new module, on the order of `Causal.Decision` (809 lines), most of it the
agreement theorem, and two obstacles are known before the first lemma. **The
decision sits in different places on the two sides** — a coordinate of
`Assignment C dim` on the diagram, a separate summation index for `Model.value`
— so the core step is an `Assignment C dim ≃ Assignment (C \ {D}) dim ×
Fin (dim D)` reindexing rather than a rewrite. And **`Skeleton` bounds its
utility to `[0,1]`** (`utility_mem_unitInterval`) while `DecisionNetwork.uval`
does not, so the bridge needs RE24 Appendix A.2's normalisation or an explicit
hypothesis that the diagram's utility is already normalised. Do not drop that
bound silently.

**Benefit.** Two rows move `Narrower → Same`. It is also *a* prerequisite for the
four `No` rows — Everitt's Theorems 9, 14, 16 and 18 — because those are
statements about incentives on a diagram, and the atlas had the diagram and the
value function in different objects that no theorem connects.

**A claim this paragraph made and this note now withdraws.** It said A *unblocks*
those four theorems. It does not: they also need `d`-separation, Everitt's
Definition 6, which is independently absent and is listed as such in the §8 row
for it. A is **one blocker of two**. The ranking below is unaffected — A is still
first — but the reason is that it closes two rows and removes a blocker, not that
it makes four theorems provable.

**Partly done, 2026-08-22.** `Causal.DecisionNetwork` is RE24 Definition 4 with
the decision and the utility as vertices, with Section 2.2's expected utility,
optimality and regret stated on it, Assumption 1 stated and **inhabited** on
print's Figure 1, and the graph step of Appendix A.1 Lemma 1(iii) proved. Three
new rows, all `Same`. **The two `Narrower` rows did not close**, because the
agreement theorem between that object and `Model.value` is not written -- the two
renderings sit in different vertex types, so it is a translation rather than a
rewrite. The axis moved from *not closable* to *open and costed*, which is the
honest gain.

**Verdict: highest benefit per unit cost, and the only axis that unblocks
anything else.** Do this one first if any.

---

## Axis B — finite domains on Definitions 1 and 2

**What print says.** Definition 1 writes `dom(V)` with no cardinality condition.
Finiteness first appears at Definition 4, where *"finite-domain variables"* is
print's own phrase — so **this axis does not exist from Definition 4 onward**.

**What the atlas has.** `dom edom : V → ℕ` on `SCM`, so every variable's domain
is `Fin (dom v)`.

**Cost.** A type-level refactor. `dom` becomes a family of types with a
`Fintype`/`DecidableEq` instance where needed; 19 sites read `Fin (dom v)` or
`Fin (edom v)` today, plus `Assignment`, `ExoAssignment`, the structural
functions, and every `Finset.sum` and `Finset.prod` in the joint-probability
layer. The evaluation layer is unaffected in shape but every signature moves.

**Under-priced until 2026-08-22, and here is the part that was missing.**
`SCM.exoProb_sum` is `∀ v, ∑ e : Fin (edom v), exoProb v e = 1`, a `Finset` sum
over the exogenous domain. Turn `edom` into a family of types and that field
stops typechecking: it needs either `[Fintype (edom v)]`, which relabels the
restriction rather than lifting it, or a summation over an arbitrary index. So
B's true price includes a decision about how print's *"probability distribution
`P(ε)`"* is rendered, which the paragraph above never mentioned. Two routes, and
both exist at the pinned Mathlib: `∑' e, exoProb v e = 1` with `tsum`, which
admits arbitrary exogenous domains carrying a countably-supported distribution;
or a measure, which is axis F. The `tsum` route is the cheap one and is enough
for **this** axis, because `exoProb_sum` is the only place Definition 1's own
tuple sums over a domain. `tprod` and `Multipliable` are needed only by
`exoJoint`, which belongs to F rather than to B.

**Benefit, measured rather than recalled.** `#check` on Definition 2's four
declarations: `submodel` and `softIntervention` carry `[DecidableEq V]`;
`submodel_eval` and `submodel_eval_notMem` carry `[DecidableEq V]` and
`[M.IsWellFounded]`. **None carries `[Fintype V]`**, which is the axis at issue.
The `IsWellFounded` instance is axis E's residue and not a narrowing — it is a
class the recursion asks for, not a field of the structure, and the §8 preamble
adjudicates why print's own sentence needs it. An earlier draft of this
paragraph said *"`[DecidableEq V]` and nothing else"*, which was wrong about the
eval pair.
With C, D and E closed, **domains are the only axis left on that row, so B
closes Definition 2 outright.** Definition 1 does not follow: `SCM.jointProb`
and `SCM.exoJoint_mul_prod` do carry `[Fintype V]`, so that row needs F as well.

**Verdict: worth paying now, and it buys one row.** The earlier verdict — *"do
not do this alone ... then it closes Definitions 1 and 2 outright"* — was right
about the ordering and wrong about the yield, on the same miscount as before: it counted the axes
this note enumerated rather than the binders the row's declarations carry.

---

## Axis C — finite indegree

**What print says.** *"endogenous parents `Pa_V ⊂ V`"*, with no cardinality
bound, and Definition 3 is *"a directed acyclic graph"* with no condition at all.

**What the atlas has.** `parents : V → Finset V` on both `SCM` and `CID`, which
forces every vertex to have finitely many parents.

**Cost.** `parents : V → Set V` plus a separate finiteness hypothesis wherever a
sum or product over parents is taken. 15 sites read `.parents`; `f_parents` and
`withPolicy`'s parent-agreement obligation change shape; the joint-probability
products need the hypothesis threaded. Moderate — smaller than B, larger than D.

**Benefit.** On its own, no row becomes `Same` — Definitions 1 and 2 still have B,
Definitions 3 to 5 still have D. **Paired with D it closes Definitions 3, 4 and 5
outright**, which is three rows.

**What it actually cost, 2026-08-22.** Less than this estimate. No sum in the
layer runs over parents, so no finiteness hypothesis had to be threaded
anywhere; `f_parents` and `withPolicy`'s obligation only quantify over the set
and were unchanged. `SCM.eval` shed `[Fintype V]` as a side effect. The one
real cost was unforeseen: a policy's defining property quantifies over
`graph.parents`, so with a `Set` it stopped being decidable and `Fintype
SCIM.Policy` had to become a classical instance. Blast radius was two files.

---

## Axis D — `ℕ`-ranked acyclicity

**What print says.** *"these functional dependencies are acyclic"*.

**What the atlas has.** `acyclic : ∃ rank : V → ℕ, ∀ v, ∀ p ∈ parents v,
rank p < rank v`. On infinite `V` this is **strictly stronger** than acyclicity:
`V = ℤ` with `parents n = {n-1}` has no directed cycle and admits no such rank.

**Cost.** A rewrite of one mechanism, not a change to every signature. The rank
is what makes `eval` terminate — it is `evalIter ε (Fintype.card V)`, justified by
`exists_rank_lt_card`. Replacing it means well-founded recursion on the parent
relation, with `eval_eq_f` reproved as the fixed-point property of that recursion.
Roughly 33 lines in `StructuralModel.lean` mention the rank or acyclicity, and
the two private lemmas `exists_rank_lt_card` and `evalIter_succ_of_rank_lt`
disappear.

**Benefit.** Same as C: closes nothing alone, closes Definitions 3–5 when paired
with C.

**Verdict at the time: cheapest of the three Everitt axes, and the one that
removes a genuine mathematical restriction rather than a presentation choice.**

**Corrected, 2026-08-22.** The second half of that is wrong while C stands.
`wellFounded_iff_exists_rank` proves that under finite indegree the `ℕ`-rank and
well-foundedness are *equivalent*: the rank is rebuilt by well-founded recursion
as one more than the largest rank among the parents, and that step is exactly
where the parent set's finiteness is spent. So D removes no restriction at all
until C goes with it, and the honest table entry is one axis, not two.

**And it did not close to print's word, except at `CID`.** `CID` evaluates
nothing, so it now carries print's *"directed acyclic graph"* verbatim, and
Definition 3 closes. `SCM` and `SCIM` carry **well-foundedness**, which is
strictly stronger — the `ℤ` chain above is acyclic and excluded — so
Definitions 1, 2, 4 and 5 stay `Narrower`.

They stay `Narrower`. An intermediate draft graded them `Same` with `Bridged`
fidelity; the audit table has no fidelity column, so that was a grade
constructed in prose, and a field print does not write makes a row `Narrower`
however good the argument for the field. `chainParents` on `ℤ` is acyclic, is
not well-founded, and admits **two** solutions of the equation `eval_eq_f`
asserts, so print's *"the value ... given by recursive application of the
structural functions"* names nothing unique there.

**A second retraction.** This paragraph went on to say that
widening the class would keep `eval_eq_f` provable by choice but stop it
pinning `eval` down, *"so there is no version of the refactor that widens and
keeps the theorem meaning what it says. That is what makes the axis not
closable rather than expensive."* There is such a version, and it is now
**axis E** in the table above: the field comes off `SCM` and `SCIM`, print's own
`acyclic` goes on in the `Relation.TransGen` form `CID` already carries, and
well-foundedness becomes a **hypothesis** on `eval` and its consumers. The class
widens to print's, `eval` is undefined exactly where print's sentence names
nothing, and `eval_eq_f` still pins down what it does define. The retracted
argument was about totalising `eval`, which is not what this table grades.

The axis did **shrink**, and that part is real: an `ℕ`-rank is strictly stronger
than well-foundedness once parent sets may be infinite, so the admitted class
genuinely widened. It did not reach print.

---

## Axis E — well-foundedness as a field rather than a hypothesis

**What print says.** *"these functional dependencies are acyclic"*, and nothing
else. Definition 3 is *"a directed acyclic graph"*.

**What the atlas had.** `SCM.wellFounded : WellFounded fun p v ↦ p ∈ parents v`
and `SCIM.graph_wellFounded`, the same for the diagram. On infinite `V` that is
strictly stronger than acyclicity — `chainParents n = {n-1}` on `ℤ` is acyclic
and was excluded.

**What the atlas has now, 2026-08-22.** `SCM.acyclic` in the same
`Relation.TransGen` form `CID` carries, with well-foundedness in two classes:
`SCM.IsWellFounded` and `CID.IsWellFounded`. `eval`, `eval_eq_f`, `eval_congr`,
`jointProb` and its two lemmas, `submodel_eval`, `submodel_eval_notMem`,
`expectedUtility`, `IsOptimalPolicy`, `optimalValue`,
`expectedUtility_le_optimalValue`, `exists_isOptimalPolicy` and `IsMaterial` ask
for the instance; `instIsWellFoundedSubmodel`, `instIsWellFoundedSoftIntervention`,
`instIsWellFoundedWithPolicy` and `instIsWellFoundedRemoveInfoLink` carry it
across the four constructions, so no statement asks for it twice and
`IsMaterial` needs it once rather than at each side of print's inequality.

**Cost.** One module and its examples. `AISafetyAtlas/Causal/StructuralModel.lean`
has **no library-module importer**: only its own example file and the root
`AISafetyAtlas.lean` import it, and `Examples/Registry.lean` names three of its
declarations. Nothing in `DecisionNetwork`, `Decision`, `Query` or the
conjecture layer reads it, so the axis does not cascade. What it does move is
the public-API pin — `docs/status/public-api.txt` carries 56 `StructuralModel`
names, `eval`, `withPolicy`, `expectedUtility` and `optimalValue` among them.
The declarations that gain the hypothesis are `eval`, `eval_eq_f`, `eval_congr`,
`jointProb` and its two lemmas, `submodel_eval`, `submodel_eval_notMem`,
`softIntervention`, then `withPolicy` and everything downstream of it —
`expectedUtility`, `IsOptimalPolicy`, `optimalValue`,
`exists_isOptimalPolicy`, `removeInfoLink`, `IsMaterial`. Threading a proof term
through all of them makes `IsMaterial` a five-argument predicate; carrying it as
a `class SCM.IsWellFounded` instead leaves the bodies alone and adds
`[M.IsWellFounded]` to the signatures, which is the version to write.

**Benefit.** **Definition 4 closes on this alone** — its atlas column is
`Causal.SCIM` and nothing else, so once the field is off the structure there is
no second declaration in that cell. Definitions 1, 2 and 5 do not close: 1 and 2
keep domains, and 1 and 5 keep axis F. E is also the **prerequisite for B** —
until it lands, closing domains changes no grade at all.

**Verdict: cheapest Lean per closed row, lowest risk, and the gate on B.**

**What it cost, 2026-08-22.** Less than the estimate. `eval_eq_f`'s proof is
unchanged — the concern that moving the proof into an instance would change what
`WellFounded.fix_eq` rewrites against did not materialise, because `eval` is
written as `hM.wf.fix` with the instance binder named rather than through
`inferInstance`. Two proofs needed a line each: `instIsWellFoundedSubmodel` and
the two example instances now have to unfold the construction before `simp_all`
closes the rank obligation, because the goal is a projection of a built
structure rather than the field being defined. One thing instance search could
not do on its own: `figCut` is a *definition* equal to a `removeInfoLink`
application, so the derived instance does not fire through the name and the
example declares it explicitly.

**And it did not close Definitions 1, 2 or 5**, which is what the pricing above
already said. Definition 4 closed, alone, and for the reason given: its column
is `Causal.SCIM` and nothing else.

---

## Axis F — the expectation layer is a finite sum

**What print says.** Definition 1 gives *"a distribution `P(ε)` under which the
exogenous variables are mutually independent"*, with no cardinality condition on
`V`. Mutual independence denotes at unbounded `V`: it is the product measure.

**What the atlas has.** `exoJoint` is `∏ v : V`, `jointProb` sums over
`ExoAssignment V edom`, `expectedUtility` sums over the same, and `optimalValue`
is a `Finset.sup'` of `expectedUtility`. Every one of these is a `Finset`
operation that exists only at `[Fintype V]`.

**Cost.** A different kind from every other axis here, because it is not a
refactor of the atlas — it is a change of mathematical register. The finite
product would become an infinite product measure and the sums would become
integrals, which means the elementary Everitt layer stops being elementary. At
the pinned Mathlib the pieces are not obviously in place: there is
`MeasureTheory.projectiveFamilyContent` — a *content* on cylinders, not a
measure — and Ionescu-Tulcea in `Probability/Kernel/IonescuTulcea`, which builds
trajectory measures over an `ℕ`-indexed family rather than a product over an
arbitrary index type. A Kolmogorov extension at arbitrary `V` would have to be
established or worked around first. **This has not been scoped further than
that**, and the estimate above is a reading of the pinned tree rather than a
plan.

**Benefit.** Definition 1 loses one of three axes; Definition 5 loses one of
two; the policy row's narrowing half goes and it becomes plainly `Wider`. So one
grade moves, and only if F is done alone — Definitions 1 and 5 need B and E as
well.

**Verdict: costed, expensive, and not next — but not for the reason an earlier
draft gave.** That draft said the Everitt layer is *elementary by design* and
that paying F would change the artifact's mathematical register. **The second
half is false about the atlas** and the claim is withdrawn. 46 modules already
import `MeasureTheory`, `ProbabilityTheory` or `MeasurableSpace`: `Control.*`
runs on Markov kernels over a `Measure Ω`, `InformationTheory.Fano` and
`DataProcessing` are stated on arbitrary probability spaces, and the causal layer
itself is not finite-sum-only — `ParameterChart` uses Lebesgue `volume` on
`ChartIndex G → ℝ`, `EffectiveGenericity` quantifies over almost every `u`, and
`Causal.Query` is built on `PMF`, `ProbabilityMeasure` and Bochner integrals.
All of it sits on the same three axioms. So measure theory is not a register the
atlas would be entering; it is one the atlas is already in.

**What is actually finite is one thing, and it is worth naming precisely.** The
*joint of a fixed model* is finite categorical — `dim : V → ℕ`, `exoJoint` a
product over `V`, `jointProb` and `expectedUtility` `Finset` sums. The *space of
models*, the chart and the estimator layer are not. F is the first of those, not
the second, and paying it means `P(ε)` as a product measure over a possibly
infinite vertex set with `Eπ[U]` an integral against it — Ionescu-Tulcea over an
arbitrary index, where the pinned Mathlib has `projectiveFamilyContent` and an
`ℕ`-indexed construction. `tsum` over `ExoAssignment` helps only when that type
is countable, which needs countable `V` and finite `edom` — a different
restriction, not Everitt's class.

**And F does not buy continuous variables.** Gaussian noise, continuous actions
and infinite state spaces on the kernel need `dim : V → ℕ` to go, which is axis
B taken to its limit, not F. Anyone selling F as *"add measure theory"* or as
*"support continuous models"* is selling two other things.

So: expensive, one cell, and behind A and B in any ordering. Disclosed as a
limit of these definitions — not as a limit of the atlas, which it is not.

---

## What already exists in Lean, and what it does to axes B and F

**Added 2026-08-22.** B and F are priced above as work to be done. They should
not be done by hand. [`Jiyuan-Tan/CausalForge`](https://github.com/Jiyuan-Tan/CausalForge)
(Lean package `Causalean`, Apache-2.0) already has the object: an `SCM` over a
finite index set with **arbitrary measurable domains** and **measure-valued**
exogenous distributions — axis B and axis F both paid, in the shape
Bongers–Forré–Peters–Mooij Definition 2.1 asks for. It also has
`Causalean/SCM/Do/`: do-calculus, local and global Markov, and `CutsetDSep`, so
*d*-separation implying conditional independence — Everitt's Definition 6 and the
standing blocker on Theorems 9, 14, 16 and 18.

**On *d*-separation specifically, defer to
[`d-separation-build-or-depend.md`](../provenance/d-separation-build-or-depend.md), which
assesses it on its own terms and reaches a different verdict.** Its conclusion is
*build the fragment*, and the reasons do not apply to the axes priced here.
*d*-separation is a predicate on a **finite** graph, so none of the measurable
generality that settles B and F is relevant to it; `Causalean.DAG` carries
`[Fintype V]` exactly as `CID` does. And a dependency would supply the predicate
and nothing else: `Causalean` has no decision/utility partition, so none of the
value-of-information or control-incentive machinery, and each of Theorems 9, 14,
16 and 18 is *complete* as well as sound — completeness being a construction of a
witnessing SCIM, which is this repository's object either way. The realistic
saving is the soundness direction of four theorems plus the shared path lemmas,
against 5,086 lines under `Graph/DSep/` and a carrier bridge. That is a different
trade from the one below, and it is made in that note.

**The blocker is the toolchain.** `Causalean` is on `v4.33.0` / Mathlib
`db584cd6`; this atlas is on `v4.31.0` / `fabf563a`, with PFR and Foundation
pinned to match. Four Mathlib-sized packages would have to agree on one revision.

**It is a `require`, not a vendored subtree.** `AISafetyAtlas/Upstream/` carries
ported forks at 97, 1780 and 3428 lines. `Causalean` is 1053 files; its `SCM/`
subtree alone is 88 files and ~37k lines and does not cut cleanly. That scale is
a dependency, like Mathlib and PFR.

**And it is additive, not a substitution.** `Causal.Model` stays — it is
finite-domain because RE24's setup is, and the margin, query and MAIS layers are
stated over it. `Causal.StructuralModel` stays — §8 grades it against *Everitt's*
Definitions 1–5, and `Causalean.SCM` is a different object, so swapping it in
would leave those rows grading a foreign one. What is worth borrowing is the part
the atlas does not have: one adapter module mapping `Causal.Model` into a
`Causalean.SCM` (finite domains are standard measurable spaces) and transporting
*d*-separation back. Same shape as axis A.

**So B and F are restated**: the general object exists in Lean under a compatible
licence, and the open question is toolchain compatibility rather than
mathematics. Neither should be paid by hand until that is settled. **Axis A is
unaffected** — it is a bridge between two objects inside this tree, and nothing
external supplies it. It stays first.

---

## The order that buys the most

1. **A** — two rows to `Same`, and the only remaining **working-stack**
   narrowing: the margin, query and MAIS layers are all stated over
   `Model.value`'s unmediated projection, so a mediated diagram gets the
   definition and none of the results. It is a loss of *transfer*, not of
   syntax — `DecisionNetwork` states RE24 §2.2 with the decision and utility as
   vertices, and `IsUnmediated` is a hypothesis on it rather than a field, so a
   diagram with `Desc_D ∩ Anc_U ≠ ∅` is one the atlas writes down and evaluates.
   It also removes one of two blockers on the four `No` incentive theorems; the
   other is `d`-separation, so it does not make them provable. **Still open.**
2. ~~**C + D together**~~ — **done 2026-08-22, and it bought one row, not
   three.** Definition 3 is `Same`. Definitions 4 and 5 stay `Narrower` on
   what D shrank to, now **axis E**; Definitions 1 and 2 keep that and domains
   as well.
3. ~~**E**~~ — **done 2026-08-22, and it bought the one row it was priced to
   buy.** Definition 4 is `Same`. Definitions 1, 2 and 5 keep the axes they had.
   The prerequisite for B is discharged.
4. **B** — Definitions 1 and 2 lose domains. Most expensive of the closable
   ones. With **E** discharged it now closes **Definition 2 outright**;
   Definition 1 keeps **F**, named on 2026-08-22, so that row needs both.
5. **F** — the expectation layer's `[Fintype V]`. Priced above and **not
   recommended**: it changes the layer's mathematical register and buys one
   cell.

   **A claim this list made on 2026-08-22 and now retracts.** It read: *"It is
   now the **only** open axis in §8, and with C and D closed it is the one thing
   keeping Definitions 1 and 2 off `Same`, so the 'changes no grade' caveat has
   expired: closing it now closes both rows outright."* False as written.
   Well-foundedness stands on `SCM`, so Definitions 1 and 2 keep **two** axes,
   and B on its own still changes no grade. The caveat expires only after E. The
   sentence was wrong the moment it was committed, for the same reason the
   original *"closes 3 rows"* prediction was: it counted the axes it had
   enumerated rather than the axes the rows carry.

**A prediction this note made, and got wrong.** It said the `Mixed` policy row's
*"narrowing half is exactly C and D, so closing those makes it plainly
`Wider`"*. C and D are closed and the row is still `Mixed`. The graph half of
its narrowing did go, but a third narrowing survives, and the row's own note in
the audit had already named it: `expectedUtility` sums over
`ExoAssignment V edom` and `exists_isOptimalPolicy` needs the policy type
finite, so `[Fintype V]` is present in that row's operations even though it is
absent from `SCIM`. The error was counting one half of a narrowing this note had
not itself enumerated — which is the argument for pricing an axis against the
declarations rather than against the printed object.

## What none of this buys

No axis here is blocking a **theorem**. Every printed theorem the atlas states is
graded `Same`, `Wider` or `Beyond`; the seven `Narrower` rows are all
**definitions**. Closing them makes the atlas's objects match print's objects,
which matters for anyone building on the definitions and for the claim that a
statement graded against Everitt is a statement about Everitt's diagrams. It does
not change the truth of anything already proved.
