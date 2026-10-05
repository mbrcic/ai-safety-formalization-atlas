# Source coverage audit

Every statement in the sections of the thirteen sources the atlas formalizes from,
checked one by one against the Lean and against the published text of each; last
revised 2026-09-09. The four wireheading sources — Everitt, Krakovna, Orseau,
Hutter and Legg 2017, Everitt, Filan, Daswani and Hutter 2016, Ring and Orseau
2011, and Everitt and Hutter 2016 — were graded for the first time on
2026-09-09, in sections 9 to 12. A fifth, Orseau and Ring 2011, was graded for
the first time on 2026-09-10, in section 13; it was pinned on 2026-09-09 and
left ungraded, and section 11 used to say so. Before that the whole `AISafetyAtlas.Wireheading`
cluster — seven modules and four registry rows — was outside this ledger, so
none of its scope claims was checked by anything. The causal sources — Richens & Everitt 2024, Pearl §1.3,
and Everitt et al. 2021 — were graded for the first time on 2026-08-20. Those three had been
covered only by hand-written prose in `mais-a2-causal-collision.md`, which no
script read; six of its scope claims had gone stale through four commits with
every gate green. Sections 6 to 8 exist so that cannot recur.

## Outside this ledger, as of 2026-09-10

Three clusters formalize from printed sources and are graded by **nothing in this
file**: the Sovereignty cluster (8 modules), the Goodhart cluster (3) and the
Decision cluster (3). Fourteen modules. They also hold **zero rows in
`registry.yaml`** — every other cluster holds between 25 and 207 mentions there,
and the wireheading cluster holds 39 — so their scope claims live only in module docstrings,
which no script checks against a source.

The sources they formalize from, none of which has a section below:

| source | cluster | where it is graded today |
|---|---|---|
| Pauly, *A Modal Logic for Coalitional Power in Games*, 2002 | Sovereignty | **section 15 below, since 2026-09-10**, with `LAND-SOV-PLAYABILITY-001` hosting both modules |
| Goranko, Jamroga & Turrini, JAAMAS 26: 288-314, 2013 | Sovereignty | **section 14 below, since 2026-09-10**, with `LAND-SOV-TRULYPLAYABLE-001` hosting the module |
| Turner & Tadepalli, arXiv:2206.13477v2 | Sovereignty, Decision | **section 16 below, since 2026-09-10**, with `LAND-SOV-RETARGETABLE-001` hosting two modules and `LAND-DEC-MDP-001` the carrier |
| Manheim & Garrabrant 2018 | Goodhart | **section 17 below, since 2026-09-11**, with `LAND-GOODHART-SELECTION-001` hosting both modules. That paper numbers nothing, so the modules are routed as atlas-original citing it for its model |
| Zhuang & Hadfield-Menell, NeurIPS 2020 | Goodhart | **section 18 below, since 2026-09-11**, with `LAND-GOODHART-OVEROPT-001` hosting the module |
| Skalse et al., NeurIPS 2022 | Goodhart | **section 26 below, since 2026-09-13**, hosted by `LAND-GOODHART-HACKABILITY-001`; graded 5 Yes, 0 Partial, 13 No after the 2026-09-20 regrade |

**A fourth blind spot, found 2026-09-11, and it is not the same one.** The three
clusters above were found by a heuristic — *a cluster with no registry rows has
no scope claims to check, so it is silently compliant*. **Armstrong & Mindermann,
NeurIPS 2018** fails that heuristic and was outside the ledger anyway. The
`AISafetyAtlas.Preference` cluster holds six modules, a registry row (`BY-011`),
a landmark row, a published "6/8" coverage count, and a **25-row statement map**
in `docs/provenance/a1-a3-b1-b3-b7-statement-maps.md`. It had no section here,
no manifest entry, and **no copy of the paper in the literature directory at
all** — so a quarter of a hundred recorded claims about a printed source stood
against a document nobody had pinned. It is now **section 20 below**, pinned in
the private manifest of 2026-09-11. The lesson for the next pass:
registry rows are not a pinned source, and a statement map is not a grade. The
only check that catches this is asking, of each source named anywhere in the
repository, whether it has a section here.

**This is the failure this file exists to prevent, recurring.** The opening
paragraph records that the wireheading cluster was once outside the ledger and
that six of the causal cluster's scope claims went stale through four commits with
every gate green; sections 6 to 8 and 9 to 13 were written so that could not
happen again. It has happened again, to three clusters at once, because they grew
on three separate worktrees under a build lock and were merged only on 2026-09-10.
Nothing in the gate notices: a cluster with no ledger rows has no scope claims to
check, so it is silently compliant.

The debt is stated here rather than discharged because grading six sources
statement by statement is a pass of its own, and an ungraded source recorded as
ungraded is honest where an ungraded source omitted is not. That paragraph was
written on 2026-09-10, when the totals counted thirteen sources. **Five of the
six named above have since been graded** — sections 14 to 18 — and the totals now
count **twenty** sources. **Skalse et al. was the last of the six and is graded
in section 26 as of 2026-09-13, so this debt is discharged.** Its grade is 0
Yes, 1 Partial, 15 No — the atlas covers no printed claim in that paper, and
section 26 says why that is structural rather than neglect.

**And the count above was wrong in both directions, which is why the block below
replaces it (2026-09-10).** It said fourteen modules. Counting every module the
root file imports outside `Examples`, `Upstream` and `Conjectures`, **forty-one**
hold no registry row; **eleven** of those formalize from a pinned printed
source, and the other thirty have no printed statement to point a row at. It was
forty-seven and seventeen before 2026-09-10: section 16 gave rows that day to
`AISafetyAtlas.Sovereignty.Retargetable`, `AISafetyAtlas.Sovereignty.EUDetermined`
and `AISafetyAtlas.Decision.MDP`, and section 17 on 2026-09-11 to
`AISafetyAtlas.Goodhart.Regressional` and `AISafetyAtlas.Goodhart.Extremal`, and section 18 to
`AISafetyAtlas.Goodhart.Overoptimization`. Three of the fourteen —
`AISafetyAtlas.Causal.DSep`, `AISafetyAtlas.Causal.Requisite`
and `AISafetyAtlas.Causal.Incentive` — are graded in section 8 of this file and
were still missing a row, because the existing registry-row check runs from a
section's *target* module and section 8's target is
`AISafetyAtlas.Causal.StructuralModel`. That is the same blind spot in a second
place, and it is what let `LAND-CAUSAL-STRUCTURAL-001` keep saying Definition 6
and Theorem 18 were not here.

### The module ledger, checked (2026-09-10)

The prose above counts clusters. This block names **modules**, and
`scripts/check_coverage_audit.py` reads it: every module imported in the
root file outside `Examples`, `Upstream` and `Conjectures` must
either host an `IN_TREE` registry row or appear below. A new cluster that
lands with neither fails the gate, which is what did not happen on
2026-09-10 and is the whole reason this block exists.

**The blind spot this check keeps.** It reads the root file's import list, so a
module that exists and is *not yet imported at the root* is invisible to it —
the same gap that makes the generated dependency graph report an unregistered
cluster as empty. Registering a new module at the root is what brings it under
every ledger check at once, and that is why it comes first rather than last.

**Unrowed, and the live debt is now zero.** The eight modules below formalize
from a pinned printed source and hold no registry row, and **every one of them is
graded in a section of this file and is listed with that reason** — the
`AISafetyAtlas.Causal.DSep` precedent, where a section grades a cluster through
one target module and the siblings ride on it. Nothing in this list is unchecked
prose any more.

**Updated 2026-09-11**, five times. Section 20 took
`AISafetyAtlas.Preference.Regret` and corrected the source its line here named.
Section 21 took `AISafetyAtlas.Sovereignty.Mandate` and
`AISafetyAtlas.Sovereignty.Separations`, and both left this list entirely,
because `LAND-SOV-POWER-001` now hosts them as IN_TREE formalizations —
the first registry row either has ever had. **`Separations` is graded only for
its Peleg content.** Its `ActualPower` section renders Chen, Ju and Ågotnes,
arXiv:2607.10567, which **is now section 23 below**, graded the same day. The
list went 11 → 9 and the live debt 4 → 2; section 22 then took
`AISafetyAtlas.Sovereignty.Independence`, leaving 8 and 1; and **section 24 took
`AISafetyAtlas.Verification.AgentBehavior`, leaving 7 and 0.** That module left
the list for a different reason from the rest: it was reported unrowed because
the check reads `formalizations` module fields and `BY-012` named its theorem in
a Lean-artifact declaration list instead — see the paragraph after this list.
`LAND-VERIF-AGENTBEHAVIOR-001` now hosts it properly.

* `AISafetyAtlas.Causal.DSep` — Everitt et al., AAAI 2021, Definition 6, after Verma and Pearl 1988 — graded in section 8 above, but section 8's target module is `AISafetyAtlas.Causal.StructuralModel`, so no row is required of this one
* `AISafetyAtlas.Causal.Incentive` — Everitt et al., AAAI 2021, Definition 17 and Theorem 18 — graded in section 8, same reason
* `AISafetyAtlas.Causal.Requisite` — Everitt et al., AAAI 2021, Definition 7, after Lauritzen and Nilsson 2001 — graded in section 8, same reason
* `AISafetyAtlas.Decision.DiscountedValue` — the discounted value layer above that carrier; states no printed theorem, and says so
* `AISafetyAtlas.Knowledge.Check` — the decision layer over the Breuer obstructions — **graded in section 19 below**, as that section's `Beyond` row, and section 19's target module is `AISafetyAtlas.Knowledge.Embedded`, so no row is required of this one. Its former line here read *"Breuer, Definition 3, on a finite device"*; **Breuer has no Definition 3**, and this module states no printed statement at all — it carries a search, its agreement theorems, and four `Decidable` instances
* `AISafetyAtlas.Knowledge.Embedded.Finite` — Breuer, Proposition 1 specialised to a finite cardinality gap — **graded in section 19 below**, same reason: that section's target is `AISafetyAtlas.Knowledge.Embedded`
* `AISafetyAtlas.Sovereignty.Representation` — Peleg 1998, Theorem 3.5's sufficiency direction — **graded in section 21 below**, on that section's Theorem 3.5 row; section 21's target module is `AISafetyAtlas.Sovereignty.Mandate`, so no row is required of this one. It states one printed theorem and nothing else
* `AISafetyAtlas.Preference.Regret` — **graded in section 20 below**, and its line here was
  wrong. It read *"Everitt et al., IJCAI 2017, Theorem 11 certificate"*; that is the module's
  **hypothesis**. What it states is the closing sentence of Armstrong and Mindermann's §4.1.2,
  and section 20's target module is `AISafetyAtlas.Preference`, so no row is required of this one

**A third place the module-ledger check does not look (2026-09-11).** The check
that produces the list above reads each registry row's `formalizations[].module`.
`AISafetyAtlas.Verification.AgentBehavior` was listed above as unrowed while
being named in `BY-012` — in that row's Lean-artifact declaration list, as
`no_behavioral_safety_verifier`. That row's module entries are Mathlib's and
Isabelle's, because `BY-012` is an upstream-reuse row for Rice's theorem, so the
check found no atlas module there and reported the consumer as unrowed. This is the same
shape as the section-8 blind spot recorded above — a row that does name the
module, in a field the check does not read — and it is the third such place.
**Settled 2026-09-11, in section 24 below.** Both works are real and the
module's header had their roles reversed: Melo et al. state, in prose, the claim
the theorem renders, and Rice's theorem is the *proof route*, reached through
Mathlib. So `BY-012` was never the statement row — it is an upstream-reuse row
for the route — and the check could not have found a statement row that did not
exist. `LAND-VERIF-AGENTBEHAVIOR-001` is now that row, and the module's line has
left the list above. **The declaration moved with it.** The registry forbids two
rows owning one Lean artifact, and a theorem's owner should be the row for the
statement it makes, so `no_behavioral_safety_verifier` left `BY-012` for the new
row; `BY-012` keeps the three declarations that are the Rice packaging itself.
That move is what makes this blind spot stop mattering rather than merely being
recorded: **no row now names an atlas module it does not host**, so the check
reading only the module fields can no longer miss one this way.

**No printed source to grade** — 35 modules that state atlas definitions,
shared laws or cluster facades rather than a printed statement. A row would
have nothing to point at. These are exempt, not owed:

* `AISafetyAtlas.Analysis.MaximalMinor`
* `AISafetyAtlas.Analysis.NullImage`
* `AISafetyAtlas.Analysis.PolynomialGenericity`
* `AISafetyAtlas.Analysis.Semialgebraic`
* `AISafetyAtlas.Causal.ControlledProcess`
* `AISafetyAtlas.Causal.Corruption`
* `AISafetyAtlas.Causal.EffectiveGenericity`
* `AISafetyAtlas.Causal.Goal`
* `AISafetyAtlas.Causal.GoalDynamics`
* `AISafetyAtlas.Causal.MarginClass`
* `AISafetyAtlas.Causal.ModelSpace`
* `AISafetyAtlas.Causal.ParameterChart`
* `AISafetyAtlas.Causal.Query`
* `AISafetyAtlas.Combinatorics.Cascade`
* `AISafetyAtlas.Combinatorics.CascadeFamily`
* `AISafetyAtlas.Combinatorics.KruskalKatona`
* `AISafetyAtlas.Combinatorics.PermInvariance`
* `AISafetyAtlas.Composition`
* `AISafetyAtlas.Compositional`
* `AISafetyAtlas.Computability`
* `AISafetyAtlas.Control`
* `AISafetyAtlas.Decision.Expect`
* `AISafetyAtlas.Explainability`
* `AISafetyAtlas.InformationTheory.ChannelCapacity`
* `AISafetyAtlas.InformationTheory.Determinism`
* `AISafetyAtlas.InformationTheory.PrefixCode`
* `AISafetyAtlas.Logic`
* `AISafetyAtlas.Order.FinsetRefinement`
* `AISafetyAtlas.Oversight.VarietyCheck`
* `AISafetyAtlas.SocialChoice`
* `AISafetyAtlas.SocialChoice.Utility`
* `AISafetyAtlas.Sovereignty.Arena`
* `AISafetyAtlas.Sovereignty.Boundary`
* `AISafetyAtlas.Verification`
* `AISafetyAtlas.Wireheading`


**Coverage** is semantic rather than name-based: can a competent reader derive
the printed statement from the cited kernel-checked declarations? `Yes` permits
ordinary specialization, definitional unfolding, algebraic rearrangement, and
an explicitly described representation isomorphism. `Partial` means that a
substantive source conclusion, quantifier, or bridge is still unproved; `No`
means that no part of the printed statement is obtained.

**The object rule.** Notation need not be mirrored, and a definition need not
occur as a separately named declaration — *unless the printed statement is
about that object*. When the source constructs something and then asserts a
property **of the construction** — a minimum over a named family, a maximum
over a named family, a specific feasible set, a specific capacity — then a
proxy for that object does not cover the claim, however close the proxy is and
however safe the inequality between them happens to point. Build the object or
grade `Partial`.

Three rows turn on it, and each names the object the rule required:

* Touchette–Lloyd Theorem 2's *equality case* is about a **minimizer** of eq.
  (28). A realized-policy infimum is a proxy for it;
  `kernelMinControlLoss` declares the printed minimum over `{p(c\|x)}` and the
  two are proved equal. `Yes`.
* Touchette–Lloyd Theorem 10 is about the **maximum** of eq. (48) over an
  arbitrary transition kernel family. A supremum over an independent-noise
  family `F(X,C,Z)`, with no realization theorem connecting the two, is a proxy
  on two counts — family and `max`. Both are closed rather than argued away:
  `AISafetyAtlas.Control.Purification` proves every Markov kernel is `F(x,c,Z)`
  for an exogenous seed and `openLoopMax_purifyMap` proves the two families
  generate the *same set* of reductions, while `isGreatest_kernelOpenLoopMax`
  proves the supremum attained, so `sSup` *is* the printed `max`. The row is
  `Yes`. The rule earns its place here: it named two specific objects to build,
  and both are built.
* Ashby §11/11 is about Ashby's **capacity**. `channelCapacity O = log \|O\|` is
  the noiseless alphabet ceiling, not the §9/15 entropy rate — a proxy. That is
  now closed the way the rule says to close it: `chainRate` declares §9/12's
  printed quantity, `ashbyCapacity` §9/15's rate, and
  `entropy_outcome_ge_sub_chainEntropy` states the row's claim against it. `Yes`.
  All three rows the rule was written for are now `Yes`, and none of them moved
  on a re-reading.

An unproved equality or attainment claim about two infima is likewise not an
ordinary representation change.

**Stability.** A row moves on new Lean, or on source evidence that a quotation
here is wrong. **A row does not move on a re-reading of a text already read.**
Where a grade has been contested, its note names the rendered page that settles
it, so the next reader argues with the page and not with the grade. This rule
exists so that a grade is argued against the page, not re-argued from memory.

No row is held by anything except its own evidence. Every row stands or falls on
the same reading — whether the atlas statement implies the printed one.

**Scope** — how the atlas statement compares in generality:

| verdict | meaning |
|---|---|
| **Wider** | the atlas statement implies the printed one, and not conversely |
| **Same** | they are the same statement |
| **Narrower** | the printed statement implies the atlas one, and not conversely |
| **Mixed** | wider on one axis, narrower on another — the interesting case, always explained |
| **Beyond** | the atlas proves something the source does not state at all |

**The standing rule: scope ≥ print wherever that is achievable.** A `Narrower`
or `Mixed` row is a defect unless the narrowing is discharged, so every narrower
axis must be labelled with which of three states it is in:

* **not a narrowing** — a units restatement or a representation change, with the
  converting lemma named. Regrade it rather than carrying it.
* **provably not closable** — with the witness that proves it. **None on this
  table.** One was claimed on 2026-08-22 — the well-foundedness of the parent
  relation that `SCM` and `SCIM` ask for where print writes only *"acyclic"* —
  and it was **retracted, then closed**. The witness proves that `eval` cannot be totalised over print's class; it does not
  prove that the structure must carry the field. `SCM` and `SCIM` now carry
  print's `acyclic` and the recursion's hypothesis lives in `SCM.IsWellFounded`
  and `CID.IsWellFounded`, which is the refactor the retracted paragraph said
  did not exist. The retraction is left visible in the §8 preamble rather than
  deleted.
  The conjecture ledger grades on a dimension this table does not have, so this
  phrase is not a claim about both documents.
**How to read a `Narrower` cell.** The grade is a statement about *classes*: the
atlas admits fewer objects than the printed words do. It is **not** a statement
about whether anything downstream lost a theorem, and the two come apart. Two
kinds occur in this table, and each row now says which it is.

* **Source-class.** The narrowing is against one paper's phrasing, in a module
  nothing else in the tree imports. Everitt Definitions 1, 2 and 5 are this:
  `AISafetyAtlas.Causal.StructuralModel` has **no library-module importer**, so
  no result stated elsewhere is weakened by it. The cost is borne by a future
  consumer who wants to instantiate that module outside the admitted class, not
  by anything already proved.
* **Working-stack.** The narrowing is on an object the rest of the tree is
  stated over, so existing theorems do not transfer to objects outside it. RE24
  §2.2's value and regret were this until 2026-09-20: the margin, query and MAIS
  layers are all stated over `Model.value`'s unmediated projection, so a mediated
  diagram — which the atlas *can* write down, as `DecisionNetwork` — cannot use
  them. That is still true of mediated diagrams, but the §2.2 rows themselves
  closed, because print takes the same projection under Assumption 1 and
  `DecisionNetwork.expectedUtility_eq_value` proves the two agree there.

The standing rule applies to both without discount: a `Narrower` cell is a
defect until discharged, proved unclosable, or costed. The distinction says
which ones to pay first, not which ones to stop counting.

* **open, and costed** — with what it would take. Every open axis is priced
  in [`causal-scope-open-work.md`](../guide/causal-scope-open-work.md), which also says
  which of them close a row on their own and which do not. **Two of the three
  §8 axes this paragraph used to enumerate are closed.** Everitt's finite domains
  on Definitions 1 and 2 closed on 2026-09-20 — the domains are a family of types
  and every finiteness condition sits on the operation that needs it — and the
  expectation layer's `[Fintype V]`, named on the policy row and denied on
  Definition 5 until 2026-08-22, closed at Definition 5 on 2026-09-20. What
  survives in §8 is conditioning, at Definition 17 and Theorem 18. **Every
  upward revision of this number has been a row carrying an axis this
  list had not enumerated**, which is why axes are now read off the declarations'
  binders rather than off the printed object.
  The other is in §6 and is a different kind: RE24 §2.2's value and regret rows
  are the unmediated projection, because the decision and the utility are not
  vertices of the graph those declarations are stated over. It is not closable by
  generalising anything — it needs a construction — and **half of that
  construction landed on 2026-08-22**. `Causal.DecisionNetwork` is RE24
  Definition 4 with the decision and the utility as vertices, and print's
  expected utility, optimality and regret are stated on it. The other half, the
  theorem that the projection agrees with it under Assumption 1 (a translation
  between vertex types rather than a rewrite), **landed on 2026-09-20** as
  `DecisionNetwork.expectedUtility_eq_value` and `regret_eq_value_regret`, and
  the two rows are `Same`. §6's own prose carries the detail; this list said "all in
  §8" and was wrong to. Two further axes were open until 2026-08-20 and are closed
  rather than re-argued. The decision
  layer's rational instantiation is closed by the field-parametrization work; its stated obstruction turned
  out not to exist, because `LinearOrder` already bundles the decidable strict
  order that `preferredDecision` needs. The binary-decision restriction in §6's
  eq. (2) row is closed by `Skeleton.realizable_iff_general`, and closed in the
  strong sense this list asks for — the old binary lemma is *derived from* the
  general one rather than left beside it. The former
  Cover & Thomas Theorem 2.5.2 arity
  gap was closed by `observationVector`, `observationPrefix`, and
  `mutualInfo_chain_rule_fin`; the atlas now contains the required measurable
  finite-prefix machinery rather than leaving the printed general `n` theorem
  at its `n = 2` instance.

## Readings that are not transcriptions

**Scope is not the only axis, and this table only grades scope.** A row can be
`Same` — asserting exactly what print asserts — while the *rendering* of a
printed phrase is a choice the atlas made rather than a transcription. The
conjecture ledger records that as a `Bridged` fidelity tag; this table has no
fidelity column, so the readings are listed here instead of being left in the
prose of three long notes. **Nothing below changes a scope grade.** Each is a
place where a reader checking the atlas against print will find a decision, and
should be able to find it in one place.

* **Pearl Def. 1.3.1, conditions (ii) and (iii): tables, where print writes
  conditionals.** Print states (iii) as *P_x(v-i given pa-i) = P(v-i given pa-i)*, a
  quotient. `IsCausalBayesNetwork` states it as equality of *tables*. The two
  differ exactly on parent configurations of probability zero, where the quotient
  is undefined and the table equality still binds. The atlas reading is the
  stronger one, and deliberately: `Causal.MarginClass`'s margin conditions exist
  because null parent fibres are reachable, so a quotient rendering would go
  vacuous precisely where a degenerate mechanism needs constraining. It is a
  choice about behaviour print does not legislate.
* **MAIS-O24 size bounds: one polynomial, chosen before the diagram shape.**
  Print requires *"the list length, degrees, coefficient bit lengths, and
  construction time to be polynomial in `S`"*. That sentence does not say whether
  one polynomial serves every shape or each shape may have its own.
  `HasPolySizeAt` takes the uniform reading, quantifying the polynomial before
  the shape and the graph. The argument for it is that print names `(m, S)` for
  the constants `a, b` and names no `m` for the size quantities — a good
  argument, and an argument is a reading. The uniform reading is the stronger
  one, so it admits fewer solutions.

**One candidate reading was checked and is not one.** `Causal.ShiftedQuery`'s
observation field is a full `Assignment C dim` where print writes its observation in *dom(O'-t)*, an assignment
to the visible subset alone. That looks like a wider query, and a wider query
would make the analyst more powerful than print's and weaken every bound phrased
over `N(ε)`. It is not: `Causal.Policy` carries that constraint as a **structure
field** requiring a policy to agree wherever the visible variables agree, so no policy can read a hidden coordinate, and
`exactPolicyAnswer_congr_observation` derives the consequence at the query level.
The invariant is enforced by the type rather than by a lemma anything could
forget to apply.

**The sample space is not a scope axis.** Taking an arbitrary measurable space
where the source fixes a discrete one is not a widening. The atlas variables are
`FiniteRange`, so they push the measure forward to a pmf on finite alphabets, the
printed statement applies to *that* pmf and returns the same conclusion, and the
atlas statement at `(Ω, μ, X, …)` **is** the printed statement at the pushforward.
The two are inter-derivable, so the space is a presentation and not a generality.
Both sources this bears on — Cover & Thomas §2.8/§2.10 and Touchette–Lloyd —
state their theorems for discrete distributions on finite alphabets, which is the
hypothesis the argument needs; the Touchette–Lloyd setting is recorded in
`touchette-lloyd-control.md` against the published text.
`AISafetyAtlas.Examples.InformationTheory.ContinuousSampleSpace` works the case
out at concrete data.

Two things follow, and neither is a widening either. Proving something a source
asserts without proof is **coverage**. Bringing a `sSup` up to a printed `max`
brings the atlas level with print rather than past it. Both belong in a row's
note, not in its scope cell.

The one object genuinely outside print's reach is the **zero** measure admitted
by `IsZeroOrProbabilityMeasure`, where every entropy is `0` and every inequality
here is `0 ≤ 0`. That is vacuity, it is graded as nothing, and it does not
license a `Wider`.

**Exercises are not graded statements.** What gets a row is what a source
*argues* — theorems, lemmas, corollaries, and the remarks and worked examples
an author asserts in the body. Exercises set for the reader do not, and no
exercise is a graded row anywhere in this audit. The reason is reuse: a theorem
is an object something downstream can be built on, an exercise is a one-off,
and grading the latter lets a puzzle answer set a scope verdict for a section
whose actual claims are covered. Ashby §11/14 was the one row that broke this
and it read `Mixed` for it. Exercises still earn their keep as **checks** —
`Examples…ashbyInsect_rate_eq` evaluates Ashby's own arithmetic term by term,
and `Examples…ashbyControl_capacity_lt_sum` records that his Ex. 4 answer does
not follow from the diagram alone — they just do not grade anything.

The rule licenses dropping a hypothesis the proof does not use. It does **not**
license restating a printed claim as a different one that happens to grade
better — a conditional theorem under an added hypothesis proves something print
did not say, and belongs in a `Beyond` row or nowhere.

Representation alone does not change scope. Replacing `{1, …, n}` by the
order-isomorphic type `Fin n`, changing notation, or exposing an implicit
parameter is `Same`. `Wider` and `Narrower` require a strict logical change in
hypotheses or conclusions, not merely a different encoding.

**Counting.** A row is counted in exactly one column. `Beyond` rows are the ones
whose Coverage cell is `—`: they record something the atlas proves that the
source does not state, so there is no printed statement to grade. A row that
covers a printed statement is counted under `Yes`/`Partial`/`No` even when its
scope verdict is `Beyond`.

A `No` row is not a defect. These are papers, and the atlas formalizes targeted
results from them, not the papers. The point of listing every `No` is that a
reader can see the boundary without having to reconstruct it.

**When a Scope cell is `—`, and the seventy-two cells that disagreed until
2026-09-18.** The five-value vocabulary above was written for rows the atlas
covers. It says nothing about the scope cell of a `No` row — and a `No` row has
no atlas statement, so there is no second statement to compare the printed one
against. `Same` means *they are the same statement*; on a row whose Atlas cell
is `—` that is not a weaker claim than the others, it is a claim about a
statement that does not exist. **So the rule, stated here for the first time:
a row whose Atlas cell is `—` carries `—` in the Scope column.** The converse
does not hold — a `No` row that names related but non-covering declarations may
still be ungraded, and six are, each saying in its note what the named
declarations do instead.

The file did not follow its own unwritten rule, and the split was exact. Of the
235 `No` rows, **163 carried `—` and 72 carried `Same`**, and the 72 were
**every `No` row of the five wireheading sections 9 to 13** — 25, 18, 16, 9 and
4 — with **no `No` row of the other twenty-one sections graded that way, and
none of those 72 naming any atlas declaration**. That was a per-section
convention introduced when those five sections were graded on 2026-09-09 and
2026-09-10, not a judgement made row by row: no row in them was reached by a
different reading from its neighbours, and the 72 notes say the same thing the
163 notes say — that nothing in the atlas represents the printed statement.

**The 72 were rewritten to `—` on 2026-09-18, in one pass, by the rule above.**
This is not a re-reading of those rows, and the stability rule is not in play:
no grade moved, no reading changed, and no note was touched. What changed is the
spelling of a cell that was asserting a comparison against a statement that does
not exist. Its effect on the published tally is one number and its complement:
`Same` moves **207 → 135** and ungraded moves **163 → 235**, which is exactly
the 72. **Nothing about coverage moves** — the Yes/Partial/No/Beyond totals are
untouched by which spelling those cells carry, which is why every arithmetic
check in `check_coverage_audit.py` passed both before and after, and why this
went unnoticed for nine days. The owed count is unchanged at 43: a `Same` cell
was never debt and a `—` cell is not debt either.

**What the 164 ungraded cells were not.** On 2026-09-18 the scope statistics
reported 164 ungraded cells beside 43 owed ones, and the larger number was read
as the larger debt. It was not a debt. All 164 were then read one by one: 157
are `No` rows with an empty Atlas cell, where `—` is the only honest value; six
are `No` rows whose notes say what their named declarations cover instead —
Richens & Everitt's identification rows, Pauly's refuted converse, Ashby's
Table; **one was a real gap**, §17's `§2 definition` row, the only `Partial` row
in the file that carried no scope cell, now graded `Wider` with the axis named
in its note. The count then rose to 235 because 72 cells that were never
gradeable stopped claiming to be. **The scope debt this file owes is the 43
`Narrower` and `Mixed` cells, and it was already counted before any of this.**

---

## 1. Cover & Thomas, §2.8 → `AISafetyAtlas.InformationTheory.DataProcessing`

**Which text.** *Elements of Information Theory*, **second edition**, sha256
`fed9b82d0904c75b47027524e11a12b6dbac31cf4f25319414679050d125dd6f`, 774 pp.
Edition and numbering read from the document: its front matter reads *Second
Edition* and *Copyright 2006 by John Wiley & Sons*, and its contents list
**§2.8 *Data-Processing Inequality* at book p. 34** and **§2.10 *Fano's
Inequality* at book p. 37**, both of which carry those headings in the body.
The edition matters and is not decoration: the first edition numbers these
sections differently, so a row graded against §2.8 is graded against a
different statement there. A copy is also held as an EPUB of the 2012
printing, which is **not** the file these grades were read from.
*Hash recorded 2026-09-13; before that this section pinned no document.*

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| (2.117) | `p(x,y,z) = p(x) p(y\|x) p(z\|y)` defines `X → Y → Z` | `isMarkovChain_iff_measure_factorizes_singleton`, `measure_factorizes_of_isMarkovChain` | Yes | **Wider** | the factorization cleared of denominators, `p(y)·p(x,y,z) = p(x,y)·p(y,z)`, so no positivity side condition and the right answer on null fibres of `Y`. `isMarkovChain_iff_measure_factorizes` additionally widens it to arbitrary measurable `s`, `t`, needs only `Y` measurable, and drops countability and measurable singletons on `S` and `U`. Witnessed by `Examples…realValuedMarkovChain`: a chain whose outer two variables are **real-valued**, so neither has a probability mass function and the printed statement cannot be written down at these types, let alone proved |
| (2.118) | `X → Y → Z` **iff** `X` and `Z` are conditionally independent given `Y` | `IsMarkovChain`, `isMarkovChain_iff_measure_factorizes_singleton`, `isMarkovChain_iff_condMutualInfo_eq_zero` | Yes | **Wider** | the atlas *defines* `IsMarkovChain X Y Z μ := CondIndepFun X Z Y μ`, taking (2.118)'s right-hand side where the book takes (2.117), so the equivalence has to be earned rather than assumed — and it is, at the printed hypothesis in both directions. `measure_preimage_inter_eq_tsum` is what carries the reverse direction from point masses to measurable sets, by countable additivity in `X` and in `Z`. Wider than print in also giving the set-level form, and in the operative form 2.8.1's proof uses, conditional independence iff `I(X;Z\|Y) = 0` |
| §2.8 | `X → Y → Z` implies `Z → Y → X` | `IsMarkovChain.symm` | Yes | Same | |
| §2.8 | `Z = f(Y)` implies `X → Y → Z` | `isMarkovChain_comp` | Yes | Wider | any measurable `g`, arbitrary measurable spaces |
| Thm 2.8.1 | `X → Y → Z` ⟹ `I(X;Y) ≥ I(X;Z)` | `mutualInfo_le_of_isMarkovChain` | Yes | Same | the variables are countable of finite range, so they push `μ` forward to a pmf on finite alphabets and the printed theorem applies to *that* pmf, returning the same inequality. The atlas statement at `(Ω, μ, X, Y)` is the printed statement at the pushforward, so the two are inter-derivable and the space is a presentation, not a generality. See `AISafetyAtlas.Examples.InformationTheory.ContinuousSampleSpace`, which records the failed witness that settled this. The one object outside print's reach is the **zero** measure admitted by `IsZeroOrProbabilityMeasure`, where every entropy is `0` and the inequality is `0 ≤ 0`; that is vacuity and is not graded as scope |
| 2.8.1 proof | equality iff `X → Z → Y` | `mutualInfo_eq_iff_isMarkovChain` | Yes | Same | as the row above: the space is a presentation, not a generality. That the source asserts this mid-proof without proving it is a **coverage** fact and is why `Cov.` is `Yes`; it is not a scope axis |
| 2.8.1 proof | "similarly, one can prove `I(Y;Z) ≥ I(X;Z)`" | `mutualInfo_le_of_isMarkovChain'` | Yes | Same | as two rows above: the space is a presentation, not a generality. That the source says "similarly, one can prove" and does not is **coverage**, not scope |
| Cor. (unnum.) | `I(X;Y) ≥ I(X;g(Y))` | `mutualInfo_comp_le` | Yes | Wider | |
| Cor. (unnum.) | `X → Y → Z` ⟹ `I(X;Y\|Z) ≤ I(X;Y)` | `condMutualInfo_le_mutualInfo` | Yes | Wider | |
| Thm 2.5.2, used at `n = 2` inline as (2.119)/(2.120) | `I(X₁,…,Xₙ;Y) = Σᵢ I(Xᵢ;Y\|X_{<i})` | `mutualInfo_chain_rule_fin`; `mutualInfo_chain_rule`, `mutualInfo_chain_rule'`, `mutualInfo_sub_eq` at n = 2 | Yes | **Same** | `mutualInfo_chain_rule_pi` is the printed arbitrary finite-family statement, with **one alphabet per index** as the source has it. `mutualInfo_chain_rule_fin` is the same identity at a single shared codomain, and the first is derived from it by tagging each variable with its index. That reduction used to be this row's justification in prose — differently typed finite alphabets embed injectively in one tagged disjoint union — and is now the proof of an exported theorem, so the uniform `V` is provably a representation rather than a restriction. The two-component declarations remain the direct forms used by §2.8, and `mutualInfo_sub_eq` is their difference identity |
| Remark + example | conditioning **can** increase `I` off a Markov chain: `X, Y` fair bits, `Z = X+Y`, `I(X;Y) = 0` but `I(X;Y\|Z) = ½` bit | `Examples…condMutualInfo_eq_half_bit_of_intSum`, `…condMutualInfo_gt_mutualInfo_of_parity` | Yes | **Wider** | the first is the printed example at the printed numbers — `Z` the **integer** sum, three-valued, and `I(X;Y\|Z) = ½` bit, which is what the printed `P(Z=1)` factor requires. The second replaces `Z` by `X ⊕ Y` and gets a full bit, a strictly larger gap. Either makes the Markov hypothesis of `condMutualInfo_le_mutualInfo` load-bearing rather than assumed to be |

**11 Yes, 0 Partial, 0 No.** Section fully formalized, counterexample included, and nothing left in the `Beyond` column. The row that sat there is printed content — Theorem 2.5.2 at `n = 2` — and `mutualInfo_sub_eq` is those two expansions subtracted, so it shares that row.

There are no `Narrower` or `Mixed` rows in this source section. The first two
rows are the section's definitional pair. `IsMarkovChain X Y Z μ`
is `CondIndepFun X Z Y μ`, which is (2.118)'s right-hand side, while the book
starts from the factorization (2.117). Both are graded, and the equivalence
between them is proved at the printed point-mass hypothesis rather than at the
stronger set-level one.

`isMarkovChain_iff_measure_factorizes_singleton` closes it. Both directions now
run at the printed strength:

* **Markov ⟹ factorization** at the printed point masses
  (`measure_factorizes_of_isMarkovChain`), and in fact at every measurable `s`,
  `t`.
* **Factorization ⟹ Markov** from point masses alone, via
  `measure_preimage_inter_eq_tsum` — a measurable slice of a countable-valued
  variable splits over its point masses — applied once in `X` and once in `Z`.

So the choice of definition is a presentation detail and not something the rest
of the section trades on.

The counterexample — `X, Y` fair bits, `Z = X + Y`, where conditioning *raises*
mutual information — is now `condMutualInfo_gt_mutualInfo_of_parity`. Until it
landed, `DataProcessing.lean` asserted in prose that the Markov hypothesis of
`condMutualInfo_le_mutualInfo` is load-bearing and nothing checked it, which is
the standard `nfl_fails_off_permInvariant`, `not_openLoopBound_erase` and
`entropy_eq_fano_of_witness` exist to meet. Every entropy in it is read off a
cardinality: the single bits are uniform, and each pairing of two of the three
variables is an injective recoding of the whole state, so carries `log 4`.

---

## 2. Cover & Thomas, §2.10 → `AISafetyAtlas.InformationTheory.Fano`

**Which text.** *Elements of Information Theory*, **second edition**, sha256
`fed9b82d0904c75b47027524e11a12b6dbac31cf4f25319414679050d125dd6f`, 774 pp.
Edition and numbering read from the document: its front matter reads *Second
Edition* and *Copyright 2006 by John Wiley & Sons*, and its contents list
**§2.8 *Data-Processing Inequality* at book p. 34** and **§2.10 *Fano's
Inequality* at book p. 37**, both of which carry those headings in the body.
The edition matters and is not decoration: the first edition numbers these
sections differently, so a row graded against §2.8 is graded against a
different statement there. A copy is also held as an EPUB of the 2012
printing, which is **not** the file these grades were read from.
*Hash recorded 2026-09-13; before that this section pinned no document.*

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Thm 2.10.1, 1st ineq. | `H(Pe) + Pe·log\|𝒳\| ≥ H(X\|X̂)`, `X̂` alphabet **unrestricted** | `fano_unrestricted`, `fano_of_embedding` | Yes | **Wider** | print says as much (*"we will not restrict the alphabet X̂"*), so that is not the axis. `fano_of_embedding` takes it in a genuinely different *type*, via an injection carrying `X`'s alphabet into it, so "different alphabet" is literal rather than covered through a common ambient. Witnessed by `Examples…fano_of_verdict`, Fano against an estimator that may **abstain**: its extra value is not a value of `X`'s alphabet under any relabelling, so this is not the printed statement at a larger alphabet but at a type the printed statement has no way to name. It is also why the sharp `− 1` is unavailable here — a verdict outside the injection's image excludes nothing |
| Thm 2.10.1, 2nd ineq. | `H(X\|X̂) ≥ H(X\|Y)` under `X → Y → X̂` | `condEntropy_le_condEntropy_of_isMarkovChain` | Yes | Wider | lives in the DataProcessing module |
| Thm 2.10.1, chained | both inequalities together | `Examples…fano_of_markov_unrestricted`, `Examples…fano_of_markov_embedding` | Yes | **Wider** | an arbitrary Markov chain rather than `X̂ = g(Y)`, so randomised estimators are covered; and the estimate may change type |
| Cor. (2.139) | any two r.v.s, `H(p) + p·log\|𝒳\| ≥ H(X\|Y)` | `fano_unrestricted` | Yes | **Wider** | `A` is any `Finset` containing `X`'s range, so the constant is `log\|A\|`, at most the printed `log\|𝒳\|` |
| Cor. (2.140) | `X̂ : 𝒴 → 𝒳` a function ⟹ `H(Pe) + Pe·log(\|𝒳\|−1) ≥ H(X\|Y)` | `Examples…fano_of_estimator_chain`, `…fano_of_markov` | Yes | **Wider** | the printed conclusion bounds `H(X\|Y)`, not `H(X\|X̂)`, so the chained form is the one that matches. `fano_of_estimator_chain` keeps the printed "function of `Y`"; `fano_of_markov` is what drops it, taking an arbitrary Markov chain and so covering randomised estimators. Both carry the sharp constant, and `A ⊊ 𝒳` is allowed |
| (2.131) | `1 + Pe·log\|𝒳\| ≥ H(X\|Y)` | `Examples…fano_le_log_two_add_of_markov` (from `fano_le_log_two_add`) | Yes | **Wider** | the printed weakening bounds `H(X\|Y)`, so the chained form is the one that matches — the same correction row (2.140) received. Printed `1` is one bit; at natural logarithm that is `log 2`, a units restatement and not an axis. `Wider` on one axis only: `A` may be a proper subset of `𝒳`, which is a real sharpening. The sample space was formerly claimed here too and is struck — see the §2.8 regrades |
| (2.132) | `Pe ≥ (H(X\|Y) − 1)/log\|𝒳\|` | `Examples…le_errorProb_of_markov` (from `le_errorProb`) | Yes | **Wider** | the form converses use, and it too bounds `H(X\|Y)`. `2 ≤ \|A\|` is the source's own implicit hypothesis — it divides by `log\|𝒳\|` |
| Remark | no-observation form `H(Pe) + Pe·log(m−1) ≥ H(X)` | `entropy_le_fano` | Yes | Wider | the sharp constant survives, because a fixed guess is a value of the alphabet |
| Example | "Fano's inequality is sharp" | `Examples…entropy_eq_fano_of_witness` | Yes | Same | the printed family: mass `1−p` on the guess, the rest uniform. Equality at **every** `p ∈ [0,1]`, so both coefficients are pinned |
| — | the constant as a parameter | `fano_of_log_le` | — | **Beyond** | any `L` dominating `log\|A.erase (X' ω)\|`; both printed constants are instances, and the proof is written once |
| Lemma 2.10.1 | `Pr(X = X') ≥ 2^(−H(X))` for i.i.d. copies | — | No | — | **not Fano.** A collision-probability bound, printed at the end of §2.10 as a separate lemma with its own proof by Jensen. Nothing in the atlas wants it: no row bounds a probability of agreement between independent draws, and the Fano cluster does not route through it |
| Cor. (2.149)–(2.150) | `Pr(X = X') ≥ 2^(−H(p)−D(p‖r))` and the same with `p` and `r` exchanged, for draws from different distributions | — | No | — | the KL form of the lemma above, and absent for the same reason. It is the only place in either graded section where a divergence appears in a conclusion |

**9 Yes, 0 Partial, 2 No, 1 Beyond.** The **Fano cluster** is complete, at both
printed constants — which is the claim worth making, and is not the same as the
section being complete, and the two rows above are why. Lemma 2.10.1 and
its corollary are printed inside §2.10, they are theorems with proofs, and they
are not in the tree. They are also not Fano, so their absence is not a gap in the
Fano work — same shape as the two `No` rows under Touchette & Lloyd, which are
printed results nothing downstream wants.

Closing it took one observation. The two printed constants differ only in how
many values the truth can still take once the estimate is known wrong: on the
error fibre over `X' = y` that is `A.erase y`, which has `|A|−1` elements when
the estimate is confined to `A` and at most `|A|` when it is not.
`fano_of_log_le` takes that bound as a parameter, so `fano` and
`fano_unrestricted` are both instances of one proof rather than two proofs.

---

## 3. Ashby, *Introduction to Cybernetics* ch. 11 → `AISafetyAtlas.Control.RequisiteVariety`

**Which text.** `ashby-1961-introduction-to-cybernetics.pdf`, sha256
`26bd434d9b5d8e430c9b6aea107983249a7196b438502d4624847ab7b8c15da6`, 156 PDF pp.
Its contents list gives **11: REQUISITE VARIETY at book p. 202**, and §11/1
opens the chapter in the body. The page references below are book pages; the
PDF is offset from them, and §9/15's row already records both numbers for the
one page it quotes.
*Hash recorded 2026-09-13; the filename was already cited, the digest was not.*

| § | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| 11/5 | `r` rows, `c` cols, no repeat in a column ⟹ outcome variety `≥ r/c` | `ashby_variety_ge`, `card_ceilDiv_le_admittedOutcomes` | Yes | **Wider** | any `Fintype`; and the bound is proved in its **integer** form `⌈\|D\|/\|R\|⌉`, which is what a count of outcomes can attain — the printed rational `r/c` is not attainable when `c ∤ r` |
| 11/5 gen. | the multiplied form | `card_le_mul_card_admittedOutcomes` | Yes | Wider | any `Finset` of disturbances; and **`Set.InjOn` on the fibre the strategy visits** rather than the whole column. The derived statements still take full column injectivity, because they quantify over strategies |
| 11/6 | `n` moves ⟹ variety reducible to `1/n`, "but not lower" | `card_ceilDiv_le_admittedOutcomes`, `ashby_variety_ge_isSharp` | Yes | **Wider** | both halves, at every shape `(r, c)` — no divisibility assumed. What is attained is `⌈r/c⌉`; the rational `r/c` is **not** attainable when `c ∤ r`, which the source's prose does not distinguish. Existence of one such table, not a claim about every table: `T d r = d` has injective columns and admits everything |
| 11/7 | `V_O ≥ V_D − V_R` | `ashby_logVariety_ge` | Yes | Wider | |
| 11/8 | `H(E) ≥ H(D) + H_D(R) − H(R)` | `entropy_ge_of_condEntropy_ge` | Yes | Wider **(repaired)** | the printed conclusion misprints `H_D(E)` for `H_D(R)` |
| 11/8 hyp. | `H_R(E) ≥ H_R(D)` — *assumed* by the source | `condEntropy_outcome_eq` | Yes | **Wider** | atlas **derives** it, and as an equality, from the column condition |
| 11/8 | headline `H(E) ≥ H(D) − H(R)` for determinate `R` | `entropy_outcome_ge_of_strategy` | Yes | Wider | |
| 11/9 | `k` repeats; entropy slack `K`; printed `V_O ≥ V_D − log k − log V_R`, where `V_R` is already logarithmic | `card_le_mul_card_admittedOutcomes_mul`, `ashby_logVariety_ge_mul`, `entropy_ge_of_condEntropy_ge` | Yes | Wider **(repaired)** | `k` and `K` are parameters of the 11/5 statements, not a second argument; `ashby_logVariety_ge` is the case `k = 1`. The printed line carries a second slip of the same kind as 11/8's: `log V_R` where 11/7 has already made `V_R` logarithmic, and `ashby_logVariety_ge_mul` states the corrected form — hence `(repaired)`, on the same footing as 11/8, which is why the marker was added here. (The scan renders `≥` as `>` throughout, so the relation is transcribed as `≥` here and in 11/7's row alike.) Recorded in the provenance note |
| 11/10 | "the law states that certain events are impossible" — the methodological reading | `two_le_card_admittedOutcomes` | Yes | **Wider** | the section is about the law's status (it "owes nothing to experiment"), and the impossibility it points back to is 11/5's. The atlas states the operative form: below a threshold of regulator variety, two outcomes must occur |
| 11/11 | *"R's capacity as a regulator cannot exceed R's capacity as a channel of communication"* | `chainRate`, `chainRate_eq_condEntropy`, `entropy_traj`, `ashbyCapacity`, `entropy_outcome_ge_sub_chainEntropy`, `channelCapacity`, `entropy_outcome_ge_sub_channelCapacity`, `entropy_le_channelCapacity_of_complete` | Yes | **Wider** | Ashby's capacity here is §9/15's **entropy rate**, and the atlas declares that rate rather than proxying it. `chainRate` is §9/12's printed definition — *"the average of these entropies, each being weighted by the proportion in which that state … occurs when the sequence has settled to its equilibrium"* — written from an equilibrium law and a kernel with no sample space, and `chainRate_eq_condEntropy` identifies it with `H[X₁ \| X₀]`. `ashbyCapacity` is §9/15's per-unit-time rate and `ashbyCapacity_rescale` is its conversion sentence. `entropy_outcome_ge_sub_chainEntropy` is this row's claim against that capacity. `Wider` for two reasons. §9/15 *asserts* that *"the entropy of a length of Markov chain is proportional to its length"*; `entropy_traj` proves it, and sharpens it — the identity is `H[X₀ … Xₙ] = H[X₀] + n · rate`, **affine** and not linear, the two agreeing exactly when `H[X₀]` equals the rate, which is what happens in the spun-coin case Ashby checks it against. Same class of printed slip as §11/8's `H_D(E)` — but this one is **§9/15's**, not this row's own printed sentence, so the row is plain `Wider` and not `Wider (repaired)`, which is reserved for a row that repairs a slip in the very statement it grades. Note also which direction the correction runs: `H[X₀] + n · rate` is a *larger* budget than `n · rate`, so the affine form makes `H[E] ≥ H[D] − budget` a weaker conclusion — a bare capacity-times-time budget is not an upper bound on what a regulator can carry, because the initial state has entropy of its own. And both capacities are kept: the alphabet ceiling is still the sharp form for the four exercises, which count signals. **The definition is checked against Ashby's own arithmetic**, which is what earlier gradings lacked: his chain has the exactly rational equilibrium `(22/49, 21/49, 6/49)`, decimals `0.4490, 0.4286, 0.1224` against his printed `0.449, 0.429, 0.122`. `Examples…ashbyInsect_stationary` proves the balance equations, `…ashbyInsect_proportions_match_print` the rounding, `…ashbyInsect_rate_eq` evaluates `chainRate` to his weighted average term by term. Noisy Shannon capacity `sup I(in ; out)` is still not modelled and is not needed: §9/15 defines capacity by the rate |
| 11/11 | the homology with **Shannon's Theorem 10**: *"the law of Requisite Variety can be shown in exact relation to Shannon's Theorem 10, which says that if noise appears in a message, the amount of noise that can be removed by a correction channel is limited to the amount of information that can be carried by that channel"*, with the dictionary *"his 'noise' corresponds to our 'disturbance', his 'correction channel' to our 'regulator R', and his 'message of entropy H' becomes … a message of entropy zero"* | — | No | — | a printed correspondence claim, book p. 211, PDF p. 112 of `ashby-1961-introduction-to-cybernetics.pdf`, and **not** covered by the row above. Formalizing it needs Shannon's Theorem 10 stated and the atlas's bound identified with its image under Ashby's own dictionary; the noisy Shannon capacity that Theorem 10 is about is not modelled. Ashby writes *"can be shown"* and then gives the dictionary rather than an argument, so print does not prove it either. Split out on 2026-08-17 after being folded into §11/11's `Yes`, which was the audit being generous to itself |
| 11/1–11/4 | regulation restated; play and outcome; the Table | the `admittedOutcomes` model of the Table | No | — | setup and definitions. The Table is transcribed as the model everything else is stated over, but there is no printed statement here to grade |
| 11/14 | **control**: *"perfect regulation of the outcome by R makes possible a complete control over the outcome by C"*, and the compound channel | `IsPerfectRegulator`, `outcome_eq_comp`, `exists_strategy_forcing`, `seq_outcome_eq`, `admittedOutcomes_of_isPerfectRegulator`, `card_disturbance_le_card_regulator`, `card_controller_le_card_regulator`, `FactorsThrough`, `channelCapacity_controller_le_channel`, `channelCapacity_disturbance_le_channel`, `max_channelCapacity_le_channelCapacity_regulator`, `condEntropy_outcome_controller`, `entropy_outcome_eq_entropy_controller`, `mutualInfo_outcome_disturbance_eq_zero` | Yes | **Wider** | `outcome_eq_comp` is the section's first half entire — under perfect regulation the outcome is a function of `C` **alone**, `D` eliminated rather than bounded — with complete control `exists_strategy_forcing` and the printed compound target `a, b, a, c, c, a` `seq_outcome_eq`. The compound-channel picture is both clauses: `entropy_outcome_eq_entropy_controller` is *"transmits fully from C"*, `condEntropy_outcome_controller` is *"transmitting nothing from D"* and needs **no hypothesis on the disturbance's law**, with `mutualInfo_outcome_disturbance_eq_zero` the form under Ashby's own *"D's values and C's not correlated"*. **Wider** on the second half: *"the achievement of control may thus depend necessarily on the achievement of regulation"* is qualitative in print and here is a count, and a count derived from §11/10's own impossibility theorem rather than a fresh argument — perfect regulation collapses `admittedOutcomes` to a singleton, which `two_le_card_admittedOutcomes` forbids below a threshold, giving `\|D\| ≤ \|R\|` and `\|C\| ≤ \|R\|`. Requisite variety charged twice, once per input. **No narrower axis on the graded statement.** The four capacity exercises used to pull this row to `Mixed`; they are **exercises set for the reader**, not claims the section argues, and no exercise is a graded row anywhere in this audit — the printed body is what the scope cell grades. Three clauses were previously listed as narrowings and none of them is one. *Units*: the exercises are quoted in bits per second and these are capacities per use, but that is a restatement the atlas already proves — `ashbyCapacity` divides a rate by a step duration, `ashbyCapacity_rescale` is §9/15's own conversion sentence, and `ashbyCapacity_mul` recovers the entropy from rate times time. *`FactorsThrough`*: Ashby **assumes** the two-input diagram rather than deriving it — he writes *"then a suitable regulator R, taking information from both C and D, and interposed between C and T"*, draws it, and opens Ex. 2 with *"If, in the last diagram of this section…"*, so all three exercises are explicitly conditional on it. Taking it as a hypothesis is what print does, which is `Same`. *Ex. 4*: **recorded because the result is worth knowing, not because it grades the row.** Its printed answer **adds** the two loads, *"as these two are independent (D's values and C's not correlated), the capacity must be at least 22 bits/sec"*; what the model forces is the **maximum**, `max_channelCapacity_le_channelCapacity_regulator`. Additivity is a property of the table, not of the diagram: `Examples…ashbyControl_capacity_lt_sum` runs on Ashby's own answer to Ex. 1 — a perfect regulator on Table 11/3/1 with a repertoire of `log 3` where the additive reading demands `log 9`. This is a limit on what the general model implies and **not** a correction to his arithmetic, since Ex. 4 inherits Ex. 2's attenuating `T` while Table 11/3/1 attenuates nothing. `channelCapacity_prod` is the lemma that would license the sum where the `R → T` link really is two independent sub-channels. **Ashby's answers are not in the pinned scan** — that copy jumps book p. 273 to p. 289, omitting *Answers to Exercises* — so they are read from the Martino Fine Books (2015) reprint, book p. 285, and the reprint is named at every quotation |
| 11/12–11/13, 11/15 | the diagram of immediate effects and Sommerhoff's directive correlation; the biological reading; *"constant" and "varying" often depend on the exact definition of what is being referred to* | — | No | — | §11/12 and §11/13 are the law's application to the gene-pattern and to survival; §11/15 argues that treating every target as *"keep the outcome constant at a"* costs no generality, since a regulator holding `x − y` at zero is forcing `x` to copy `y`. Methodological rather than mathematical: there is no printed statement here to grade. These stay `No` because nothing in them is formalized, not because the means are missing |
| 11/16–11/21 | *Some variations*: compound disturbance, noise, initial states, compound target, internal complexities | — | No | — | §11/16 introduces the part; the five cases argue the basic formulation already covers them by vectorising — `D` for compound disturbance and noise, **`E`** for compound target — which the atlas's arbitrary `D` and `E` permit. No new statement |

**11 Yes, 0 Partial, 4 No.** Chapter 11 runs §11/1–§11/21 over printed pp. 202–218,
and all twenty-one sections are accounted for. The `No` rows cover the setup
(§11/1–11/4), the applications other than §11/14 (§11/12–11/13, §11/15) and the
whole closing part headed *Some variations* (§11/16–11/21). §11/14 is the one
among them carrying a statement rather than a gloss, and it is formalized in
`AISafetyAtlas.Control.CompleteControl`; the remaining `No` rows are setup,
methodology and the closing part's five arguments that the basic formulation
already covers their cases.

**The source page for §11/11's capacity.** §9/15 was rendered and read at book
p. 180, PDF p. 97 of `ashby-1961-introduction-to-cybernetics.pdf`, and the quoted
sentence is recorded verbatim there. That page, not any summary of it, is what
this row's grade answers to.

One gloss offered in review and *not* adopted, because the page refutes it:
that Ashby "then applies Shannon's theorem — any channel with this capacity can
carry the report". No such sentence appears in §9/15. The section ends with the
behavioural definition of "channel" and runs into §9/16 *Redundancy*. Ashby is
measuring capacity by the rate, as printed.

**Why this row needs its own note.** Ashby bounds the regulator by a *capacity*
in bits per second. `entropy_ge_of_sensor` bounds by the entropy of one reading,
and the §11/11 exercises are arithmetic over noiseless signal counts, so neither
is the printed quantity: any grade resting on those alone rests on a reading of
§9/15 rather than on what §9/15 declares.
`AISafetyAtlas.Control.ChannelRate` declares the entropy-rate capacity itself,
and `Examples…ashbyInsect_rate_eq` checks that declaration against Ashby's own
arithmetic, which is what puts this row on the page instead.

Why the reading settled where it did. The sentence about capacity follows a
worked three-state Markov example: Ashby computes its
probability-weighted entropy as `0.842` bits per step, converts it to `2.53` bits
per minute, and calls *such a rate* the natural measure of channel capacity. The
alphabet ceiling would instead be `log₂ 3` bits per step. The later phrase
"variety available at each step" therefore cannot honestly be read as defining
capacity to be the alphabet cardinality in all cases.

The four §11/11 exercises do use noiseless signal counts, so `channelCapacity O
= log |O|`, `channelCapacity_fun`, and `channelCapacity_prod` reproduce their
arithmetic. That established a real partial result and not the general claim,
which is what kept this row `Partial` for six gradings. The general claim is now
covered too: `chainRate` is §9/12's entropy of one step, `ashbyCapacity` is
§9/15's per-unit-time rate, and `entropy_outcome_ge_sub_chainEntropy` is §11/11's
bound against it. Noisy Shannon capacity `sup I(in ; out)` is still not modelled,
and §9/15 does not ask for it — it defines capacity by the rate.

`channelCapacity` closes the exercises' noiseless case.
`entropy_outcome_ge_sub_channelCapacity` is an alphabet-ceiling consequence and
`entropy_le_channelCapacity_of_complete` is the form the exercises use, that
complete regulation *requires* capacity at least the disturbance entropy. Three
of the four printed exercises are worked at Ashby's own numbers: the insect's
optic nerve carries `2000 log 2` a second against ten dangers at `10 log 2`; the
ship's telegraph and wheel together carry `log 9 + 5 log 50` in five seconds,
which is the upper limit on disturbances Ex. 2 asks to be estimated; and the
general's ten signallers carry `576000 log 2` a day against ten divisions at
`10^7 log 2`.

**Two limits stated rather than glossed, one of them since removed.** The
the exercises' noiseless `log |O|` ceiling is the sharp form for those four;
`AISafetyAtlas.Control.ChannelRate` now supplies the general entropy-rate reading
as well, leaving only noisy Shannon capacity unmodelled. And every statement here
is a **necessary**
condition — Ex. 1 asks whether a channel is "sufficient to enable it to defend
itself", and what is proved is only that the constraint does not bind. Ex. 3 asks
in the direction the law settles, and there the conclusion is a real
impossibility.

11/6 was the last `Partial`. Its *"but not lower"* half had been proved in
general while the *achievability* half existed only as a 4×2 example, which made
the row narrower than a source that states the reduction for any number of
moves. `ashby_variety_ge_isSharp` supplies the general witness: a disturbance is
a pair, the regulator's move shifts the second coordinate, and playing that
coordinate cancels it. The regulator absorbs exactly as much variety as it has
moves — matching `ashby_variety_ge` with equality at every shape.

---

## 4. Igel–Toussaint 2004 and Schumacher–Vose–Whitley 2001 → `AISafetyAtlas.Learning.Sharp`

**Which texts — two, and the rows below are graded against both.**
`igel-toussaint-2004-published-nfl-non-uniform-distributions.pdf`, sha256
`6117e3515bd66b60a3d3d33939ef479c136708b678a83924696f0e83d520e0e8`; its own
first page reads *Journal of Mathematical Modelling and Algorithms 3: 313-322,
2004*, so this is the published version and not a preprint. And
`schumacher-vose-whitley-2001-nfl-and-problem-description-length.pdf`, sha256
`3bf60560a1fd90052374e1cfdb966f67900fa48e9c8672f2e2a499f1e8bcd893`, titled *The
No Free Lunch and Problem Description Length*. Three further Igel-Toussaint
papers are held — 2001, 2003 and 2014 — and **none of them is this source**.
*Hashes recorded 2026-09-13; before that this section pinned no document.*

Both papers quantify over **non-repeating black-box** search algorithms, which
choose each query from the costs already seen. That class is `AdaptiveRule` plus
`∀ c, Injective (ruleVisit r c)`, and every row below is stated over it.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| IT Thm 1 | uniform NFL | `no_free_lunch_adaptive_of_sharp`, `no_free_lunch_stochastic_of_sharp`, `nfl_mixture_of_permInvariant` | Yes | **Wider** | print quantifies over *any* performance measure `c` and over `m ∈ {1,…,\|X\|}`, and dropping `m ≤ \|X\|` adds only instances where the no-revisit hypothesis is unsatisfiable, so that is not a widening. **The algorithm class was where it lost, and no longer does.** Print says *"any two (deterministic or stochastic, cf. [1]) algorithms `a` and `b`"*, citing Droste–Jansen–Wegener, and `AdaptiveRule` is deterministic. Igel's own later survey defines what the citation buys: *"a randomized search algorithm a can be described by a probability distribution pₐ over deterministic search behaviors [6]"*, with the performance written as *E{c(Y(f, m, a))} = ∑ over a′ ∈ A of pₐ(a′)·c(Y(f, m, a′))*. `mixtureTrace` **is** that equation and `nfl_mixture_of_permInvariant` is the theorem over it, so the quantifier is now met at the source's own definition rather than at a proxy for it. **Wider on the mixture weight.** DJW write *"a probability distribution p = (p₁, …, p_m)"*; `nfl_mixture_of_permInvariant` takes `p q : AdaptiveRule X Y m → ℝ` with neither nonnegativity nor normalization, requiring only equal total mass, so signed mixtures are admitted. Same widening as the signed objective weights already credited on IT Thm 5, one level up — there on the weight over objectives, here on the weight over algorithms. `nfl_stochastic_of_permInvariant` widens the choice-sequence form the same way |
| IT Thm 2 | sharpened NFL: NFL over a **set** `F` iff `F` c.u.p. | `nfl_adaptive_of_closedUnderPermutation`, `closedUnderPermutation_of_nfl`, `nfl_mixture_of_permInvariant` | Yes | **Wider** | necessity needs the hypothesis only for **schedules** at one length, a strictly smaller family than the source assumes it for. Sufficiency now holds at the source's stochastic class as well as its deterministic one, by `nfl_mixture_of_permInvariant`, so the algorithm axis is met at the source's own definition rather than argued away |
| IT Thm 5 | non-uniform sharpened NFL, for a distribution `p` | `nfl_adaptive_iff_permInvariant`, `nfl_mixture_of_permInvariant` | Yes | **Wider** | weight class wider: any real weight, with neither nonnegativity nor normalization — including **signed** weights, differences of two priors, for which SVW's NFL4 explicitly declines to state anything and "distribution" is the wrong word. `nfl_mixture_of_permInvariant` carries the same widening on the algorithm axis as IT Thm 2, and the `iff`'s sufficiency direction no longer loses on it |
| IT Lemma 1(1)+(2) | c.u.p. sets are unions of basis classes; `B_h` **is** the orbit | `eq_iUnion_permOrbit`, `basisClass_histogram_eq_permOrbit` | Yes | Same | part (2) is the half with content — `histogram` and `permOrbit` are defined independently, and the lemma says they cut the objectives the same way. Without it, `PermInvariant` (orbits) and the source's Theorem 5 hypothesis (histograms) are not known to be the same condition |
| SVW Theorem | trace of a permuted algorithm, points **and** costs | `ruleVisit_permRule`, `observed_permRule` | Yes | Same | the trace has two coordinates; `ruleVisit_permRule` is the points, `observed_permRule` the costs. Stating only the second would cover half the printed conclusion |
| SVW Cor. (Duality) | `V(A, σf) = V(σA, f)` | `observed_permRule` | Yes | Same | the same identity, read the other way |
| SVW Lemma 1 | c.u.p. ⟹ NFL | `nfl_adaptive_of_closedUnderPermutation` | Yes | **Wider** | an indicator instance of the arbitrary-weight statement |
| SVW Lemma 2 | NFL ⟹ c.u.p. (a **set**, not a weight) | `closedUnderPermutation_of_nfl` (via `permInvariant_of_nfl`) | Yes | **Wider** | hypothesis weaker on three axes: schedules rather than the whole algorithm class, one sample length, and **indicator** measures only — which is exactly Igel–Toussaint's `δ(k, c(Y))` form, so no linearity bridge is needed |
| IT Thm 3, count | non-empty c.u.p. subsets of `Y^X` number `2^C(\|X\|+\|Y\|−1, \|X\|) − 1` | `spectrum`, `spectrum_eq_iff_histogram_eq`, `spectrum_eq_iff_mem_permOrbit`, `surjective_spectrum`, `preimage_image_spectrum`, `closedUnderPermutationEquivSet`, `closedUnderPermutationNonemptyEquivSet`, `card_closedUnderPermutation`, `card_closedUnderPermutation_nonempty` | Yes | Same | the count print states, at print's finite alphabets. The content is `closedUnderPermutationEquivSet`: a permutation-closed set is a set of orbits, an orbit is a basis class by their Lemma 1 — already proved here as `basisClass_histogram_eq_permOrbit` — and a basis class is fixed by the multiset of cost values, so the orbits **are** `Sym Y \|X\|` and Mathlib's `Sym.card_sym_eq_choose` finishes it. Stated as `card + 1 = 2^C(…)` so no truncated subtraction appears. Igel–Toussaint attribute the result to their own earlier paper and prove it there, so this transcribes rather than supplies a proof |
| IT Thm 3, fraction | the fraction of non-empty subsets that are c.u.p. | `card_nonempty_set_objective`, `fraction_closedUnderPermutation` | Yes | Same | the second displayed equation, as an equation in `ℚ`. `Examples…fraction_cup_boolean` evaluates it at their own example — Boolean objectives on four points, `31 / 65535` |
| IT Thm 3, asymptotics | *"converges to zero double exponentially fast"* for `\|Y\| > e\|X\|/(\|X\|−e)` | — | No | — | the claim the section exists to make, and the one thing here that is not a count. It needs an asymptotic estimate on binomial coefficients against `\|Y\|^{\|X\|}`; the two counts above are its inputs, not the claim itself. Split out rather than absorbed into the rows that *are* covered |
| IT Thm 4 | non-trivial neighbourhood is not permutation-invariant | `exists_perm_rel_not_iff`, `forall_rel_of_permInvariant`, `rel_diag_iff_of_permInvariant`, `exists_perm_adj_not_iff`, `forall_adj_or_forall_not_adj_of_permInvariant` | Yes | **Wider** | the "why NFL is vacuous in practice" argument. Print, p. 318: *"A neighborhood relation on X is a **symmetric** function n: X × X → {0,1}"*, non-trivial when some pair of **distinct** points neighbours and some pair of distinct points does not. `exists_perm_rel_not_iff` is that statement and its equation (6), **with symmetry dropped**: the argument never uses it, so it is not assumed, and the diagonal is left free. `forall_rel_of_permInvariant` is the content — one instance at a pair of distinct points forces every pair — proved by two-transitivity, a permutation assembled from two transpositions. **And print does not prove Theorem 4**: p. 318 reads *"THEOREM 4 ([6])"*, the same self-citation as Theorem 3, and no proof appears in the text — so unlike the Theorem 3 rows, which transcribe a printed count, this row *supplies* a proof the source delegates. `rel_diag_iff_of_permInvariant` is the diagonal half: an invariant relation is all-or-nothing off the diagonal and all-or-nothing on it, the two independently. The graph forms are corollaries kept for discoverability, and looplessness removes the diagonal degree of freedom. `Examples…oneEdge_not_permInvariant` is one edge on three points; `Examples…loopedEdge_not_permInvariant` is that edge plus every self-loop — non-trivial in print's sense, legal under print's definition, and not a simple graph, so the graph form cannot be *instantiated* at it. That is applicability and not strength: `loopedEdge` is symmetric, and for symmetric `r` the relation `fun a b => a ≠ b ∧ r a b` is a legal `SimpleGraph` carrying both non-triviality clauses, so the conclusion stays derivable from the graph form. **The axis that buys strength is symmetry**, and `Examples…arrowRel_not_permInvariant` is its witness: a single arrow on two points, non-symmetric (`Examples…arrowRel_not_symmetric`), where print's theorem cannot be posed at all since no symmetric relation on a two-element type meets both clauses; `Examples…top_permInvariant` and `Examples…bot_permInvariant` occupy both branches of the graph dichotomy; `Examples…eq_permInvariant` is the diagonal, invariant but *trivial* in print's sense, recorded to show the diagonal is a live degree of freedom rather than as a case Theorem 4 covers |
| SVW NFL1 | equal performance under any overall measure | `no_free_lunch_adaptive_of_sharp` | Yes | **Wider** | the atlas gives the sum for an arbitrary `Ψ`, from which any overall measure follows |
| SVW NFL2 | for any two algorithms and any `f` there is a `g` with `V(A;f) = V(B;g)` | `exists_observed_eq` | Yes | Same | the witness is explicit — relabel by the permutation carrying one trajectory to the other |
| SVW NFL3 | every algorithm generates the same collection of performance vectors | `card_observed_eq` | Yes | **Wider** | at an **arbitrary** sample length `m`, where the source states NFL3 for the complete trace. At full length SVW note the collections are already sets, so counts and supports coincide there — the multiplicity `\|Y\|^{\|X\|−m}` is only visible at partial length |
| — | the adaptive class is strictly larger | `Examples…probeRule_not_schedule`, `…nfl_probeRule_over_orbit` | — | **Beyond** | a branching rule no schedule reproduces, for which NFL still holds over a **non-constant** permutation orbit. The orbit matters: over the constant objectives every rule observes the same sequence, so an equality there would be two identical sums. `observed_probeRule_ne` rules that out |

**14 Yes, 0 Partial, 1 No, 1 Beyond.** The one `No` is the
asymptotic, which is an estimate on binomial coefficients rather than a
statement about search, and is deliberately left.

**NFL4 has no row of its own.** Its declining remark — that a weighted overall
measure is not generally subject to NFL except under equal weighting — is
recorded on the signed-weights row, which is where the atlas exceeds it.

**The two papers do not draw the same algorithm class.** Igel–Toussaint state
Theorem 1 for *"any two (deterministic or stochastic, cf. [1]) algorithms"*;
Schumacher–Vose–Whitley open §2 with *"a framework for the analysis of
**deterministic** non-repeating blackbox search algorithms"*, which is exactly
`AdaptiveRule`. So the stochastic gap is Igel–Toussaint's alone; no SVW row is
affected by it.

**The stochastic axis is what three of the Igel–Toussaint rows turn on**, and it
is charged in the scope column rather than only stated as a non-claim in
`Learning/Sharp.lean` and [`lean-wolpert-nfl.md`](lean-wolpert-nfl.md): a stated
non-claim is not a scope verdict. The source-definition mixture proof closes the
axis, which is what carries all three rows to `Wider`.

Closing it turns on reading what the citation to Droste–Jansen–Wegener actually
buys, which Igel's own later survey spells out: *"a randomized search algorithm
*a* can be described by a probability distribution *pₐ* over deterministic
search behaviors"*, performance being *∑ over a′ ∈ A of pₐ(a′)·c(Y(f, m, a′))*,
with *A*
all deterministic behaviours. **The mixture picture is the source's definition of
a stochastic algorithm, not a proxy for it** — which is the opposite of the usual
situation elsewhere here, where a family standing in for a printed object is the
defect. `mixtureTrace` is that equation, `nfl_mixture_of_permInvariant` the
theorem over it, and `mixtureTrace_pointMass` the survey's *"deterministic
algorithms as a subset … having degenerated probability distributions"*.

`stochasticTrace` is the survey's alternative view in the same paragraph —
*"drawing all realizations … at once prior to the search process"* — kept because
it is the more general object, with `surjective_induced_playChoice` recording
that its finite choice alphabet reaches all of `A`.

**The primary source has now been read, and it is more explicit than the
survey.** Droste–Jansen–Wegener, *Optimization with randomized search heuristics
— the (A)NFL theorem, realistic scenarios, and difficult functions*,
**Theoretical Computer Science 287 (2002) 131–144**, is Igel–Toussaint's
reference [1]. Its Theorem 1 is stated for *"an arbitrary (randomized or
deterministic) search heuristic"*, and the randomized half of the proof, at
book p. 134, is this:

> *"The number of different deterministic search strategies is **finite**. Let m
> be its number. A randomized search strategy is a probability distribution
> p = (p₁, …, p_m) and chooses the ith deterministic strategy with probability
> p_i. … the expected cost of a randomized search heuristic is the weighted
> average of the cost of the deterministic search heuristics. Since all
> deterministic search heuristics have the same cost, this also holds for all
> randomized search heuristics."*

Three things fall out, and each retires a worry recorded earlier on this row.
The mixture model is DJW's **definition** of a randomized strategy, not a
rendering of one. Finiteness of the strategy set is **DJW's own observation**, so
`Fintype (AdaptiveRule X Y m)` is print's setting rather than an atlas
restriction. And *"since all deterministic search heuristics have the same cost,
this also holds for all randomized"* is `mixtureTrace_eq_sum_mul` — the atlas
proof follows the printed one step for step. Scenario 1 also fixes `A` and `B`
finite, and the paper normalizes to non-revisiting explicitly: *"Many popular
search heuristics evaluate certain points more than once but this can be avoided
by using a dictionary."*

Five rows rest on the algorithm class. `nfl_adaptive_of_permInvariant`
proves the sufficient direction over the printed class by a fibre argument: for
a fixed cost sequence `c`, the two rules unroll two schedules from `c`, and a
permutation carrying one to the other maps the fibre of one rule over `c`
bijectively onto the fibre of the other. The permutation is built from `c` alone,
which is why it can reindex the sum over objectives; permutation-invariance says
it leaves the weights alone.

`permInvariant_of_nfl` is graded `Wider` for a reason worth stating explicitly,
since it inverts the usual direction: the algorithm class appears in its
*hypothesis*, so assuming schedule-independence over a **smaller** class makes
the theorem **stronger**, not weaker.

**Why the graded statement is a bare relation and not a graph.** Print's
neighbourhood relation is symmetric and nothing more; `SimpleGraph` is symmetric
*and* irreflexive, so modelling it that way would assume a hypothesis print does
not state. The proof uses neither symmetry nor irreflexivity, so the row's
primary declaration quantifies over an arbitrary binary relation on an arbitrary
type, and the graph forms are corollaries kept because that is the form a reader
looking for graph automorphisms would search for.

**What each axis buys, stated precisely.** `Examples…loopedEdge_not_permInvariant`
is an edge plus every self-loop: legal under print's definition, non-trivial in
print's sense, and not a `SimpleGraph`, so the graph form cannot be
*instantiated* at it. That is applicability rather than strength — `loopedEdge`
is symmetric, and for symmetric `r` the graph `fun a b => a ≠ b ∧ r a b` carries
both non-triviality clauses, so the conclusion stays derivable from the graph
form. The axis that buys **strength** is symmetry, witnessed by
`Examples…arrowRel_not_permInvariant`, where print's theorem cannot be posed at
all. The diagonal witnesses neither: it relates no two distinct points, so it
fails print's first non-triviality clause and Theorem 4 does not speak about it.
`Examples…eq_permInvariant` records it only as a degree of freedom
`forall_rel_of_permInvariant` does not constrain, which is why
`rel_diag_iff_of_permInvariant` is a separate fact.

One sentence of print cuts against the reading here and is quoted rather than
stepped around. Immediately after the definition: *"There are only two trivial
neighborhood relations, either every two points are neighbored or no points are
neighbored."* Print says **two**; leaving the diagonal free gives more. The
reconciliation is that print counts off-diagonal behaviour and treats `n(x, x)`
as immaterial rather than as a parameter. That does not undo the widening — the
looped witness above is a relation print's own definition admits — but the
reading is an inference from a definition that omits the diagonal, not something
print asserts.

The asymptotic row stays `No` on a real judgement rather than a wrong one. It is
an estimate on binomial coefficients — the object is `Nat.choose`, not search —
and it is an endpoint: nothing else in the atlas would use it.

---

## 5. Touchette & Lloyd 2004 → `AISafetyAtlas.Control.InformationLimits`

**Which text.** `touchette-lloyd-2004-published-physica-a-information-theoretic-control.pdf`,
sha256 `1beaa6388edb38c17ffb172dcc7bd69528e09b42371d9bdcf4c9c273057ebb2a`. Its
running head reads *Physica A 331 (2004) 140-172* and its face gives *Received 3
June 2003*, so this is the published paper. **The 2003 arXiv v2 is also held and
is not what these rows are graded against**; equation numbers, including the eq.
(28) this section turns on, are the published ones.
*Hash recorded 2026-09-13; before that this section pinned no document.*

Governing fact for every row: **the source defines `L_C` with a minimization
over `{p(c|x)}`** — eq. (28), the minimization being there, in the paper's words,
"to ensure that `L_C` reflects the properties of the actuation channel, and does
not depend on one's choice of control inputs". So the source law of `X`, the
noise `Z` and the actuation channel are held fixed and the *controller* varies.

Both readings are now in the atlas. `controlLoss` is the loss of one controller;
`minControlLoss` is an infimum over a set `P` of controllers sharing one plant
(`IsPlant`), which is what the source holds fixed — the actuation channel, with
the source law and the noise — while the policy varies.

**Which `P` is the printed one.** Eq. (28) minimizes over `{p(c|x)}`: channels
from the *state*, which carry nothing about the noise the state does not already
carry. That is `inputPolicies`, defined as conditional independence of `C` and
`Z` given `X`, and `minControlLoss μ F X Z (inputPolicies μ X Z)` is the atlas's
represented-policy rendering of the source constraint on the current `Ω`, and for
finite alphabets it is now *proved equal* to the all-kernel minimum.

The equality is a theorem and not an identification by fiat, which matters
because the represented infimum and the printed `L_C` quantify over different
objects — one over random variables on the ambient `Ω`, the other over channels.
`kernelMinControlLoss` declares eq. (28)'s
own object — an infimum over Markov kernels `S → K` — and
`minControlLoss_inputPolicies_eq_kernelMin` proves the two equal under
`[Fintype S] [Fintype K]`, the printed setting. No realization construction is
involved: eq. (28)'s second displayed line is *linear* in `p(c|x)`, so its
minimum is at a vertex, and the vertices are deterministic state feedbacks, which
need no auxiliary randomness and therefore exist on every sample space. The
pointwise theorems remain the sharper ones and still carry the rows that do not
need a minimizer; the bridge is what the *minimizer-sensitive* row needed.
`Set.univ` is **not** it, and the difference is not bookkeeping: a bare map
`Ω → K` may read the actuation noise, which no `p(c|x)` can, and cancel it.
`Examples…minControlLoss_univ_lt_inputPolicy` exhibits exactly that — a plant
where the noise-reader drives the loss to `0` while the constant controller, an
input policy, loses `log 2` — and `…not_isInputPolicy_noiseReader` checks the
reader is excluded from eq. (28)'s feasible set. Every theorem here is stated for
an arbitrary `P`, so each represented-family statement is available without
depending on this particular `Ω`.

`P` is **not** the printed constraint set, and `Set.univ` is not "the
unconstrained minimum": the atlas set is too *large*, not too small, and the
rows below are graded on that reading.

Each pointwise result is the stronger statement — it holds at *every* controller
— and the printed one is read off the infimum.
`Examples…minControlLoss_lt_controlLoss_gate` exhibits a plant and two
controllers whose losses are `0` and `log 2`, so the minimization is not a
formality either.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Thm 2, ineq. | `L_C ≤ H(Z)` | `minControlLoss_le_entropy_noise`, `controlLoss_le_entropy_noise` | Yes | **Wider** | the printed `L_C` and the pointwise form both. `Wider` on one axis: purification is asked at *one* admitted controller rather than across the family, since an infimum is already capped by a single member. A second axis — an arbitrary sample space — was claimed here and is struck; see the §2.8 regrades, which apply verbatim, this source's setting being discrete distributions on finite alphabets and its atlas variables `FiniteRange` |
| Thm 2, equality case | equality iff `H(Z\|X',X,C) = 0` | `minControlLoss_eq_entropy_noise_iff_of_attained`, `controlLoss_eq_entropy_noise_iff`, `minControlLoss_inputPolicies_eq_kernelMin`, `minControlLoss_inputPolicies_attained` | Yes | **Wider** | the obstruction the kernel bridge clears is that the represented infimum might have exceeded the source's minimum over `{p(c\|x)}`, so a minimizer of one need not minimize the other; `kernelMinControlLoss` now declares the source's object and `minControlLoss_inputPolicies_eq_kernelMin` proves the two equal. Attainment is a conclusion rather than a hypothesis: `minControlLoss_inputPolicies_attained` exhibits the minimizer. `Wider` in holding pointwise at every controller. The sample space was claimed as a second axis and is struck; the finite alphabets are the printed setting and the atlas variables are `FiniteRange`, so the space is a presentation |
| Thm 2, proof (30)+(31) | `H(X';Z\|X,C) = H(Z)` and `H(X';Z\|X,C) = L_C + H(Z\|X',X,C)` | `entropy_noise_sub_controlLoss` | Yes | Same | the atlas states their combination `H(Z) − L_C = H(Z\|X',X,C)` on one line. Both printed halves of Theorem 2 are corollaries of it, so neither needs its own argument — but the identity is one substitution from two consecutively displayed printed equations, not something the source omits |
| Thm 3 | `L_C = I(X';Z\|X,C)` | `minControlLoss_eq_sInf_condMutualInfo`, `controlLoss_eq_condMutualInfo` | Yes | **Wider** | the two quantities are equal at every admitted controller, so their images coincide and so do their infima — the printed equality between minima follows without a minimizer. `Wider` in holding off the minimum as well as at it; the sample space was claimed as a second axis and is struck |
| Thm 4 | `L_C = I(X';X,C,Z) − I(X';X,C)` | `minControlLoss_eq_sInf_mutualInfo_sub`, `controlLoss_eq_mutualInfo_sub` | Yes | **Wider** | as Theorem 3: `Wider` in holding off the minimum as well as at it, with the sample-space claim struck there and here |
| Thm 10 | `ΔH_closed ≤ ΔH_open^max + I(X;C)` | `kernelEntropyReduction_le_kernelOpenLoopMax`, `exists_kernelEntropyReduction_le_at_max`, `isGreatest_kernelOpenLoopMax`, `entropyReduction_le_openLoopMax`, `entropyReduction_le_of_condEntropy_ge`, `entropyReduction_le_of_openLoopBound` | Yes | Same | the paper's stated main result, at print's own scope, closed in two steps. **Family.** `kernelEntropyReduction_le_kernelOpenLoopMax` states it with no `F` and no `Z` — only a joint law `ρ` for `(X,C)` and a Markov kernel `κ` playing `p(x'\|x,c)`. What closed it is the paper's own §2: *"any non-deterministic channel … can be represented abstractly as a randomly selected deterministic channel"*, with (i) determinism given `(c,z)` and (ii) *p(x'\|x,c) = ∑_z p(x'\|x,c,z) p_Z(z)*. `isPurification_purifyMap` proves it; `openLoopMax_purifyMap` shows the two renderings of eq. (48) generate the **same set**. **The word `max`.** Print writes a maximum and the atlas had `sSup` plus boundedness, which is formally weaker since `max ≤ sSup`. `isGreatest_kernelOpenLoopMax` closes it: a probability measure on a finite state space is a point of Mathlib's standard simplex and conversely, the reduction in those coordinates is a finite sum of *negMulLog* terms whose inner argument is *linear* in the weights, so continuity of *negMulLog* plus compactness of the simplex plus finiteness of `K` give attainment. `exists_kernelEntropyReduction_le_at_max` then states Theorem 10 with the bound realized by an explicit input law and action. **`Same`, and formerly `Wider`.** The only widening ever claimed here was that the `F`-form results additionally hold over an arbitrary sample space, and the §2.8 regrades establish that this is a presentation rather than a generality. Nothing else on this row is a scope axis: the kernel form states print's *own* object, closing `max` against `sSup` brings the atlas **up to** print rather than past it, and proving §2's asserted purification is **coverage**. So the atlas statement and the printed one are inter-derivable, which is what `Same` means — it is not a demotion of the work, and `Cov.` stays `Yes`. Note that §2 assumes purification for *any* channel, globally, not only inside Theorem 2 |
| Thm 9 | `ΔH_open ≤ max over c of ΔH_open^c`, with equality attainable | `kernelEntropyReduction_le_iSup_kernelOpenLoop`, `exists_kernelEntropyReduction_dirac_eq_iSup`, `entropyReduction_le_iSup_openLoopReduction`, `exists_entropyReduction_const_eq_iSup_openLoopReduction` | Yes | Same | `Yes` on the object rule, applied uniformly: `kernelEntropyReduction_le_iSup_kernelOpenLoop` states both `ΔH_open` and `ΔH_open^c` from the printed data alone — an input law *ν*, an action law *p_C*, and an arbitrary kernel `κ` — with no plant model in the statement. The `Partial` verdict rested on a sentence that was **false**: that the source does not assume purification in the open-loop section. §2 states it for *any* channel before Section 3, and `isPurification_purifyMap` now proves it besides. The printed attainment clause is separate and proved: `exists_kernelEntropyReduction_dirac_eq_iSup` exhibits a **pure** controller — a Dirac action law at the paper's *ĉ* — whose closed-loop reduction equals the supremum. That supremum is over the finite `K`, so attainment is immediate; eq. (48)'s supremum over all input laws needs compactness and is proved attained separately by `isGreatest_kernelOpenLoopMax`. **`Same`, and formerly `Wider`**, on two grounds now withdrawn. The first was that the `F`-form holds over an arbitrary sample space — a presentation, per the §2.8 regrades. The second was that Lemma 8, which the proof leans on, needs no open-loop hypothesis at all: that is true and is graded on **Lemma 8's own row**, but a scope cell compares *this* row's atlas statement with *this* row's printed one, and the generality of a lemma used in the proof is not an axis of the statement proved. `kernelEntropyReduction_le_iSup_kernelOpenLoop` is stated from the printed data alone, so it is the printed statement |
| Lemma 8 | `ΔH_open ≤ ΔH_open^C` | `entropyReduction_le_condEntropy_form`, `entropyReduction_eq_condEntropy_form_iff` | Yes | **Wider** | wider in a way worth naming: the atlas proves it with **no** open-loop assumption at all. The source states it inside the open-loop section, but its printed proof uses only that conditioning does not raise entropy, so the inequality holds at every controller, observing or not. The equality case at `I(X';C) = 0` is proved too |
| Thm 1 | perfect controllability iff | — | No | — | **not interesting for this atlas, and expensive.** The statement is an existential over conditional distributions `p(c\|x)` satisfying two conditions — a reachability clause and a determinacy clause — so it needs the kernel object as a *quantified witness* rather than as an infimum. It also characterizes reachability, which is not an information limit and nothing downstream consumes |
| Thm 5 | perfect observability iff `H(X\|C) = 0` | `perfectlyObservable_iff_sensorLoss_eq_zero`, `entropy_eq_zero_iff` | Yes | Same | `perfectlyObservable_iff_sensorLoss_eq_zero` carries `[IsProbabilityMeasure μ]` and `[FiniteRange X] [FiniteRange C]`, so the variables push forward to a pmf on finite alphabets — this source's printed setting — and the two statements are inter-derivable. Not even the zero-measure remainder applies, the hypothesis here being a probability measure outright. That the source declines to prove it — *"we omit the proof which readily follows from well-known properties of entropy"* — is **coverage**, and `entropy_eq_zero_iff` not being in the entropy layer is a **dependency** fact; neither is a scope axis |
| Thm 6 | observable ⟹ `I(X;Z\|C) = 0` | `condMutualInfo_eq_zero_of_sensorLoss_eq_zero` | Yes | Same | as Theorem 5's row — `condMutualInfo_eq_zero_of_sensorLoss_eq_zero` carries `[IsProbabilityMeasure μ]` and `FiniteRange` on all three variables. The source's three-line proof, mechanized. The source notes the converse fails and it is not claimed |
| Cor. 7 | `L_S = 0` ⟹ `I(X;C,Z) = I(X;C)` | `mutualInfo_prod_eq_of_sensorLoss_eq_zero` | Yes | Same | as Theorem 5's row — `mutualInfo_prod_eq_of_sensorLoss_eq_zero` carries `[IsProbabilityMeasure μ]` and `FiniteRange` on all three variables. The comma is checked: the published page and the arXiv TeX both give `I(X;C,Z)`, not a three-way information |
| Thm 11 | closed-loop optimal iff `I(X';C) = 0` | — | No | — | **not interesting for this atlas.** It holds only under the constancy condition `ΔH_open^c = ΔH_closed^c = ΔH` for all `c`, and needs a notion of closed-loop *optimality* the atlas does not define. The conclusion it reaches — that gathering information you cannot use is worthless — is already carried by Theorem 10 without the extra model |
| below (50) | *"each conditional distribution `p(x\|c)` is a legitimate input distribution … an element of `P`"*, with the fixed actuation subdynamics inherited | `condEntropy_ge_of_openLoopMax`, `isPurification_purifyMap`, `map_prodMk_cond_eq_prod` | Yes | Same | the recorded defect was that the atlas had no realization theorem showing its `F,η` model covers every printed transition kernel, so the membership argument was mechanized only inside a narrower family. `isPurification_purifyMap` supplies exactly that theorem, and `openLoopMax_purifyMap` shows the induced reduction sets coincide, so the conditional law `p(x\|c)` is an element of eq. (48)'s own `P` for every printed kernel. This is an argument the paper gives in one sentence, now mechanized at the scope the paper gives it |

**12 Yes, 0 Partial, 2 No.** This section was `6 Yes, 1 Partial, 7 No` until the
kernel bridge and the open-loop and sensor axes landed, `9 Yes, 3 Partial, 2 No`
until purification was proved, and `11 Yes, 1 Partial, 2 No` until eq. (48)'s
maximum was proved attained; what changed and why is recorded per row above
rather than only in the totals. **Every graded row from this source is now
covered.** The two `No` rows are results nothing downstream wants, and their rows
say so.

Those three `Partial` rows were one defect, named once by the **object rule**
and then applied uniformly: Theorems 9 and 10 are printed about an arbitrary
actuation kernel `p(x'|c,x)`, while the atlas stated them inside the
independent-noise realization `X' = F(X,C,Z)` with no theorem realizing every
such kernel that way.

**Two things were wrong with that diagnosis, and only one of them was the
atlas's.** The blame was put on the source — the note said the open-loop section
does not assume purification, so the `F`-model was an added hypothesis rather
than the paper's own. That is **false**. §2, in the paragraph introducing Fig. 2
and eq. (7), states purification as a global modelling move for *any* channel,
before Section 3 and long before the open-loop section, in the paper's own
words: *"any non-deterministic channel modeling a source of noise at the level
of actuation or estimation can be represented abstractly as a randomly selected
deterministic channel"*, with condition (i) determinism given `(c,z)` — the
atlas's `IsPlant` — and condition (ii) *p(x'|x,c) = ∑_z p(x'|x,c,z) p_Z(z)* with
*p_Z* and not *p(z|x,c)* — the atlas's `IndepFun ⟨X,C⟩ Z`. The mistake was
reading where purification is *used* rather than where it is *introduced*.

What was genuinely the atlas's is that the paper **asserts** the representation
and never constructs it, and neither did the tree. `AISafetyAtlas.Control.Purification`
constructs it, following the paper's phrase literally: a *randomly selected
deterministic channel* is a random element of `S × K → T`, finite when the
alphabets are, so the seed needs no continuum. So the atlas now proves what print
asserts, which is a better outcome than winning the grading argument would have
been.

Theorem 9 and the step-(50) row move to `Yes` on that. Theorem 10's note named
**two** residuals, and the second — eq. (48) writing `max` where the atlas had
`sSup` — is closed separately by `AISafetyAtlas.Control.OpenLoopAttainment`:
probability measures on a finite state space are exactly the points of the
standard simplex, the reduction is continuous in those coordinates because the
outcome law is linear in them, and a continuous function on a compact simplex
attains its maximum. Lemma 8 and the sensor results were never affected, being
proved for arbitrary variables with no plant model — which is also why Lemma 8
is `Wider`.

Theorem 2 still takes two rows, because its two halves are proved by different
routes — the inequality by capping an infimum with one member, the equality case
by exhibiting the minimizer. It no longer takes two *grades*: the minimizer is
constructed, so the printed equality case is unconditional.

The two remaining `No` rows are the ones nothing downstream wants. Theorem 1
quantifies existentially over conditional distributions and characterizes
reachability rather than an information limit; Theorem 11 needs a notion of
closed-loop optimality the atlas does not define, and its conclusion is already
carried by Theorem 10. Both notes say so on the row.

Theorem 10 is `Yes | Wider`; its row and the totals section say what closed it.
Along the way two claims **about the source** were made here and turned out to be
wrong, and they are recorded rather than quietly dropped.

*"The source writes `ΔH_open^max` without saying which ensemble the maximum is
over."* False. Equation (48) and the sentence under it say it exactly: the
maximum is *"over any input distribution chosen in the set `P` of all probability
distributions"*. There was no implicit uniformity to repair.

*"The source states step (50) in prose and never proves it."* False. The
paragraph below the step gives the argument in one sentence — *"each conditional
distribution `p(x|c)` is a legitimate input distribution for the initial state of
the controlled system. It is, in any cases, an element of `P`"* — which is
exactly the argument the atlas mechanizes. That observation removed a mistaken
`Beyond` reading; what it did **not** do, and was once claimed to do, is supply
the realization bridge from arbitrary transition kernels or turn a bounded
supremum into an attained maximum. Those two are closed by
`isPurification_purifyMap` and `isGreatest_kernelOpenLoopMax`, not by reading the
paper more carefully.

The row is `Yes` on `exists_kernelEntropyReduction_le_at_max`, which is stated
against the printed maximum and does not go through `OpenLoopBound` at all.
`OpenLoopBound` is not eq. (48) and is kept for its incomparable hypothesis — a
fact about that definition, recorded once under *Reading the totals*, not a gap
in a graded claim.

**The minimization, and the one place it still bites.** `minControlLoss` is the
represented-policy infimum, and the printed Theorem 2 inequality together with
the printed Theorems 3 and 4 are obtainable from the arbitrary-`P` statements.
Each follows from the pointwise form without assuming a minimizer — for the
equalities because two functions equal at every point have equal infima, and for
the inequality because an infimum is capped by any single member. The kernel
object is declared rather than silently identified with `inputPolicies` on one
fixed `Ω`, and the identification is proved.

Theorem 2's **equality condition** was the one statement that needed more than the
transfer, since "equality holds iff `H(Z|X',X,C) = 0`" describes a *minimizer*.
`minControlLoss_eq_entropy_noise_iff_of_attained` takes "some admitted controller
realizes the represented infimum" as a hypothesis; what was missing was any
reason to think such a controller exists, or that it minimizes the source's
quantity rather than the represented one. Both are now supplied — the two minima
are equal, and `minControlLoss_inputPolicies_attained` exhibits the minimizer —
so the hypothesis is dischargeable and the row is `Yes`.

Note what does the work here: not a realization construction, and not the
compactness hypothesis the paper does not state, but the observation that eq.
(28)'s displayed objective is **linear**, so the optimum is a vertex and vertices
are realizable everywhere.

---

## 6. Richens & Everitt, ICLR 2024, §2–3 and Appendices A–B → `AISafetyAtlas.Causal.Model`

**Which text grades these rows.** The published ICLR proceedings PDF, sha256
`143d458cbee2f4f5d04d7380f6741e8105965d1ee94834e1ddb3bd231722a0e7`. The atlas
also stores the arXiv working text
(`b25a2c7e8fe27d1dfd00299166197d8f3bd2ac8af7102f3b2a07585cfd6743b2`), and
`mais-a2-causal-collision.md` pinned *that* one. Every numbered statement carries
the same number in both, checked one by one, with a single difference: the
working text adds **Corollary 1** — the regret-bounded-agent restatement of
Theorem 2 — after Theorem 3, and the proceedings has no corollary at all. It is
graded below as a working-text row so that the difference is on the record rather
than resolved silently. The source also numbers two distinct appendix lemmas
"Lemma 4"; the second, in Appendix D, is referred to here as D's Lemma 4.

**What gets a row here.** The printed statements the paper argues, plus the
displayed formulas it introduces definitionally and the atlas transcribes as
theorems — eq. (1), the truncated factorisation, eq. (2), eq. (3). A definition
with no transcribed content is not a row.

**The standing narrowing.** `AISafetyAtlas.Causal.Model` and
`AISafetyAtlas.Causal.MarginClass` carry their value field as a parameter, so the
printed real case is reachable, and it is the case any statement over these
objects is stated at. `AISafetyAtlas.Causal.Decision` was the exception until the
field-parametrization work, and is no longer: it too carries
`𝕜`, including `InIdentifiedSet`'s tolerance. **No row below is narrow on the
value field.** The `Narrower` rows are narrow on structure: their declarations
are the Assumption-1 projection, with the decision and the utility outside the
graph.

**That sentence used to end "and that is not an axis a generalisation closes",
which was wrong twice over.** It is not a generalisation that closes it — it is a
construction — and on 2026-08-22 the construction landed:
`AISafetyAtlas.Causal.DecisionNetwork` is Definition 4 with the decision and the
utility as **vertices**, and Section 2.2's three sentences are stated on it at
print's own quantifiers. The axis therefore moves from *not closable* to **open,
and costed**, which is the state the standing rule actually provides for. What it
costs is named in the two `Narrower` rows below and priced in
[`causal-scope-open-work.md`](../guide/causal-scope-open-work.md).

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §2.1 truncated factorisation | product of unintervened CPDs when the value is consistent with the forced one, else zero | `hardInterventionProfile`, `Model.jointProb_hardInterventionProfile`, `fixProfile`, `Model.jointProb_fixProfile` | Yes | **Wider** | print states it for hard `do` only; the atlas proves the product form for *every* profile of arbitrary local maps, and the printed case is the constant-map instance. Intervened factors become consistency indicators exactly as printed. Witnessed by `Examples…jointProb_sum_shiftCollapse`, which runs a translation modulo three composed with a non-injective child map — neither is a hard intervention, and neither is expressible in the printed formula |
| Def. 2, eq. (1) | a local intervention transforms the CPD to the preimage sum over states mapping to the realized one | `Model.factor`, `Model.factor_eq_re24` | Yes | Same | `factor_eq_re24` is the literal preimage sum and closes by `rfl`. The printed map is any `f`, and so is the atlas's `LocalIntervention`; the four-map Boolean case is derived, not built in |
| Def. 3 mixture formula | a mixed intervention performs each component with its weight, and the joint is the weighted sum | `Mixture`, `ProbMixture`, `IsProbabilityMixture`, `Model.jointProbMix` | Yes | **Wider** | the simplex is over whichever value field a statement picks, so at the reals it is the printed object. The ambient `Mixture` drops the simplex constraint entirely and carries the linear lemmas. Witnessed by `margin_class_not_identifiable`, which inhabits the rational field, where the printed statement has no reals to quantify over |
| Def. 4 causal influence diagram | a single-decision, single-utility CID is a CBN whose variables are partitioned into decision, utility and chance, with the utility a real-valued function of its parents | `Causal.DecisionNetwork`, `Causal.DecisionPolicy`, `Model.withPolicy`, `Model.withPolicy_parents`, `DecisionNetwork.IsDeterministicUtility`, `DecisionNetwork.exists_utilityFunction`, `Model.cpt_eq_one_unique` | Yes | **Same** | **New on 2026-08-22; this definition had no row before, under this section's rule that a definition with no transcribed content is not one.** Print says a CID *is a CBN* with partitioned variables, so `DecisionNetwork` is built on `Causal.Model` rather than on the structural layer, and the decision and the utility are **vertices**. Distinctness of the decision and utility vertices is the whole of the partition condition a two-element distinguished part needs. **Print's *do(D = π(pa_D))* is rendered as a soft intervention**: `Model.withPolicy` keeps the parent set and swaps the table, and `withPolicy_parents` records it. That is forced by print itself — RE24 Def. 2 severs a hard-intervened vertex's incoming edges, and a policy *reads* its observations, so a hard reading would delete them. **One disclosed widening, with print's case pinned.** Print's clause that the utility is a real-valued function of its parents is carried as `IsDeterministicUtility`, a hypothesis rather than a field, so the atlas defines expected utility on a strictly larger class than print's; `exists_utilityFunction` recovers print's *U(pa_U)* as an actual function wherever the hypothesis holds, which is the same disclosure pattern this section already uses for single-decision restrictions. The widening is in the permitted direction and is why the cell is `Same` rather than `Narrower`. Inherited from `Causal.Model` and graded on its rows, not restated here: a finite vertex set, a `Finset` parent map, and an ℕ-ranked acyclicity witness |
| §2.2 expected utility and optimality | expected utility of a policy, and a policy is optimal if it maximises it | `Model.value`, `Model.value_eq`, `Model.bestPolicy`, `Model.value_bestPolicy`, `DecisionNetwork.expectedUtility_eq_value` | Yes | **Same** | **Working-stack narrowing** — the kind that costs transfer rather than syntax. One axis, and a structural one. These declarations are the unmediated Assumption-1 projection rather than the printed CID equation: their decision and utility are not graph vertices. **The atlas can state a mediated decision task**, and a sentence in an earlier pass of this note said otherwise: `DecisionNetwork` carries the decision and the utility as vertices, Assumption 1 is `IsUnmediated`, a **hypothesis** rather than a field, and a diagram with `Desc_D ∩ Anc_U ≠ ∅` is a `DecisionNetwork` the atlas writes down and evaluates. What does not transfer is everything stated over the projection — the margin layer, the query layer and the MAIS Props all sit on `Model.value` — so a mediated diagram gets the definition and none of the results. **The axis changed state on 2026-08-22 without closing.** The printed CID equation now exists in the tree -- `DecisionNetwork.expectedUtility` and `DecisionNetwork.IsOptimal`, on a diagram whose decision and utility *are* vertices, graded `Same` on the Definition 4 row above. What is still missing, and what this row is graded on, is the theorem tying the two together: nothing yet proves that this projection agrees with `DecisionNetwork.expectedUtility` on a diagram satisfying Assumption 1. **The mediated declarations are deliberately not listed in this row's atlas column.** Adding them beside the projection would give the row a declaration that is print's object while four others are not, and this section grades a row on *every* declaration in its column -- the convention exists precisely so a row cannot be graded on its best declaration. The axis is now **open, and costed**: the agreement theorem needs the joint over the diagram split at the decision and utility coordinates, and the two renderings live in different vertex types, so it is a translation and not a rewrite. The value field is *not* an axis: Stage 3 made `Causal.Decision` generic like the rest of the causal layer, so the printed real case is an instance. `bestPolicy` maximises each visible fibre and `value_bestPolicy` proves it attains the optimum, with ties unconstrained **Closed on 2026-09-20.** `DecisionNetwork.expectedUtility_eq_value` proves that on a diagram satisfying Assumption 1 the printed CID equation and these declarations are the same number, so the structural axis is gone and the row is `Same`: `Model.value` *is* print's *E^π[U]*, on the projection print itself takes. The proof is `Model.sum_jointProb_mul_of_parentClosed` applied twice and split each time by `Model.sum_image_fibreRep_erase`. Taking the utility's coordinate out of *Anc_U* replaces the readout by `DecisionNetwork.utilityMean`, the utility vertex's conditional expectation; taking the decision's coordinate out of what remains replaces the decision's table by the policy, and the surviving factors do not see the change because `decision_notMem_parents_of_isUnmediated` — which is the single place Assumption 1 enters, as `parentClosed_chanceContext`. **One claim in the previous pass of this note was wrong and is retracted.** It said the agreement needs print's Definition 4 restriction `IsDeterministicUtility`, on the ground that the projection's utility is a *function* of the decision and the environment while the diagram's is a random coordinate. A `Skeleton`'s utility is a **number**, not a state, so what the projection needs is the utility vertex's conditional *expectation*, and that exists at every diagram; print's *U(pa_U)* is the special case, recorded as `DecisionNetwork.utilityMean_eq_uval_of_isDeterministicUtility`. The hypotheses actually used are Assumption 1 and the Appendix A.2 range `0 ≤ uval ≤ 1`, both print's own and both graded on their own rows. Witnessed on print's Figure 1 by `Examples…figExpectedUtility_eq_value`, and `Examples…figAlwaysOne_expectedUtility_eq_value` runs it at a second policy. |
| §2.2 regret | the decrease in expected utility against an optimal policy | `Model.regret`, `Model.HasRegretAtMost`, `Model.regret_decomp`, `Model.regret_eq_zero_iff`, `DecisionNetwork.regret_eq_value_regret` | Yes | **Same** | **Working-stack narrowing**, exactly as the row above. The inequality is the printed one within this representation, with no added zero-regret sign clauses. Same single structural axis as the row above, and **closed with it on 2026-09-20**: `DecisionNetwork.regret_eq_value_regret` is print's δ on a diagram with the decision and the utility as vertices, equal to `Model.regret` on this projection, against any optimal diagram policy. It needs one thing the value agreement does not, and the note records it because it is the only place the two optimality notions meet: `Model.optimalValue` maximises over policies *outside* the graph while `IsOptimal` maximises over the decision vertex's tables, and `DecisionNetwork.optimalValue_eq_expectedUtility` identifies the two because `DecisionNetwork.liftPolicy` inverts `projectedPolicy`, so the two ranges coincide. Same non-axis as the row above too: the value field is a parameter. `regret_eq_zero_iff` is an atlas converse print does not state: zero regret is exactly positive support on the fibrewise argmax. Witnessed on print's Figure 1 by `Examples…figRegret_eq_value_regret`, whose optimality hypothesis is discharged rather than assumed — `Examples…figIsOptimal`, which rests on `figExpectedUtility_const`. **That witness corrected a docstring, and the fact behind it is recorded here so nobody reads `figIsOptimal` as informative:** `figParents` declares the edge `X → Y`, but `figCpt` gives `Y` the constant table `1/2`, so on the diagram as written `Y` is a fair coin independent of everything the decision can read and *every* policy scores `1/2`. **The diagram is not defective** — it is a legitimate CID, the edge does the structural work the Assumption 1 and Lemma 1(iii) rows use it for, and every statement graded on it holds. What it does not do is separate policies, so optimality on it is trivial, and a docstring that claimed the copying policy matches the utility's target was wrong and has been corrected. |
| Assumption 1 unmediated decision task | the decision's proper descendants and the utility's proper ancestors are disjoint | `DecisionNetwork.IsUnmediated`, `Model.properAncestors`, `Model.properDescendants`, `Model.mem_properAncestors_iff`, `Model.mem_properDescendants_iff`, `DecisionNetwork.decision_notMem_parents_of_isUnmediated` | Yes | **Same** | **New on 2026-08-22.** **The notation had to be read before the assumption could be stated.** Print's Appendix notation paragraph says *"Anc_i and Desc_i refer to proper ancestors and descendants"*, and the reading matters: on print's own Figure 1 the decision is a parent of the utility, so an improper reading puts the decision in both sets and makes the assumption **unsatisfiable**. Read properly it says the decision's only route to the utility is the direct edge, which is what print's own Appendix argument uses. `decision_notMem_parents_of_isUnmediated` is that content in the form the analysis consumes: no proper ancestor of the utility reads the decision. **Inhabited, not merely defined**: `Examples…figIsUnmediated` discharges it on print's Figure 1 training diagram, without which every theorem conditional on it would be vacuous |
| App. A.1, Lemma 1(iii), graph step | *"D ∈ Anc_U which with Desc_D ∩ Anc_U = ∅ implies D ∈ Pa_U"* | `DecisionNetwork.mem_parents_utility_of_isUnmediated` | Yes | **Same** | **New on 2026-08-22, and it is a slice of Lemma 1, not the lemma.** Print's clause is one sentence and the atlas theorem is that sentence: the decision being a proper ancestor of the utility, together with Assumption 1, forces the direct edge. The proof is the expansion print compresses — any intermediate vertex on a route from the decision to the utility would be a proper descendant of the one and a proper ancestor of the other at once. Formally the utility's ancestor closure minus the decision and its proper descendants is parent-closed and contains the utility, hence contains the whole closure, hence contains the decision, which it does not. **The rest of Lemma 1 is not covered and its own row still says so**: clauses (i) and (ii), and the first half of (iii), run through Assumption 2 (domain dependence), which is not formalized. Slicing a printed statement is this table's existing practice — see the Cover and Thomas Thm. 2 rows |
| App. A.2, eq. (2) | normalise the utility to `[0,1]` by subtracting its minimum over parent states and dividing by its range | `Skeleton.normalizeUtility`, `Skeleton.utilityLo`, `Skeleton.utilityHi`, `Skeleton.normalizeUtility_mem_unitInterval`, `Skeleton.ofUtility`, `Skeleton`, `Skeleton.realizable_iff_general`, `Skeleton.realizable_iff` | Yes | **Wider** | the normalising map is now built, not only its output. `normalizeUtility` is the printed quotient over the utility node's parents — the decision together with the utility parents — and `ofUtility` carries an arbitrary `𝕜`-valued utility into a `Skeleton`, which is what was missing while this row read `Partial`: no unnormalized utility could be written down and then rescaled. On a constant utility the range is zero and the quotient is `0`, still in `[0,1]`, so the invariant is unconditional where print states eq. (2) only for the non-degenerate case. The widening is the converse print does not state: `realizable_iff_general` proves a decision family is realized, up to a fibrewise shift, by a normalized utility exactly when its fibrewise spread is bounded by one, at **any** finite decision arity. The former binary restriction is gone and is not merely claimed gone — `realizable_iff` is now *proved from* the general form via `sup'_sub_inf'_bool`. Witnessed by `Examples…ternaryGap_realizable`, a three-decision family the binary lemma cannot state at all |
| App. A.2, invariance of the optimum under eq. (2) | a positive affine transformation of the utility leaves the set of optimal policies invariant, so regret bounds rescale | — | No | — | the atlas normalises by construction and never states the invariance. Nothing downstream needs it, because no atlas statement transports a regret bound across a rescaling |
| App. B, eq. (3) | expected-utility difference between the two decisions under a hard intervention, as a weighted sum of utility differences | `Model.value_const_sub` | Yes | **Wider** | print gives one two-variable hard-`do` instance with the opposite sign ordering; `value_const_sub` proves the identity for every probability mixture, every visible set, and every model, and the printed instance is a Dirac profile. The sign is an ordering convention, not an axis. Witnessed by `Examples…margin_class_not_identifiable_shared_optimal`, which needs the identity at *every* probability mixture and visible set to place two models in one identified set; print's single hard-`do` instance does not reach it |
| App. A.1, Lemma 1 (clauses (i), (ii), and the Assumption-2 half of (iii)) | domain dependence implies no dominant decision, that the observed parents are a proper subset of the utility ancestors, and that the decision is a utility parent | — | No | — | domain dependence is nowhere in the atlas. It is a hypothesis about the existence of two environment distributions with different optima, and the atlas's margin conditions replace that role with explicit inequalities rather than deriving it |
| App. A.2, parameter space | the CID parameters lie in `[0,1]` and are logically independent, so they define a parameter chart | — | No | — | **no chart over the CID parameters exists**, which is the narrower claim this row used to make as a blanket one. `ChartIndex` with `Model.chartOn` is a real chart, with `K(G)` proved against `def:margin`'s formula by `card_chartIndex`, and MAIS-O24's conclusion (c) carries a Lebesgue estimate over it — but both are charts of the *chance-variable* tables of MAIS's unmediated skeleton, where `D` and `U` are not vertices. RE24's parameter space is over a full CID's parameters, including the decision and utility mechanisms, so it is a different object and this row stays `No`. Its absence is why the four rows below are `No` rather than `Partial` |
| App. A.2, Lemma 2 (Okamoto) | the solutions of a nontrivial polynomial are Lebesgue measure zero in its parameters | — | No | — | cited by the source, not proved by it. The atlas has no measure on a parameter space and no polynomial encoding of a constraint |
| App. A.3, reachability of distributions | mixtures of interventions reach any distribution over the environment variables | `ProbMixture.dirac` | No | — | the atlas has the deterministic profiles print mixes over, and the mixture-to-profile reduction lemma proves that mixture-wise equality is profile-wise equality — but it never states that the mixtures *reach* an arbitrary distribution, which is the printed claim |
| Def. 5, policy oracle | a map from each domain to a policy achieving expected utility within the tolerance of optimal | `InIdentifiedSet`, `not_inIdentifiedSet_of_neg` | No | — | the atlas packages *shared* admissible families rather than a map from domains to policies, so no declaration is the oracle. `InIdentifiedSet` accepts every tolerance in the value field and `not_inIdentifiedSet_of_neg` proves the extension below print's domain is empty, which bounds the packaging but does not build the oracle |
| Thm. 1 | for almost all CIDs, the graph and the joint over the utility ancestors are identifiable from optimal policies across all mixtures of local interventions | — | No | — | needs the parameter chart, the almost-every quantifier, and the oracle — all three absent. The atlas's `Model.ancestors_eq_univ_iff` supplies only the ancestor-closure bookkeeping the statement is phrased over |
| Thm. 2 | for almost all CIDs, a regret-bounded policy family identifies an approximate model whose parameter error is bounded by a function vanishing linearly at zero regret | `InIdentifiedSet`, `modelError`, `IsRadius`, `inIdentifiedSet_zero_of_behaviorEq` | No | — | the atlas objects are **related packaging**, not a transcription: there is no recovered subgraph and no error function. What is machine-checked is one direction of the bridge the theorem's proof uses — `inIdentifiedSet_zero_of_behaviorEq` shows equal masked transforms put two models in the identified set at zero tolerance. The converse, reconstructing the numerical query from an arbitrary optimal-policy oracle, is the printed step and is not formalized |
| Thm. 3 | a causally sufficient model identifies optimal policies for every soft intervention, and an approximate model identifies regret-bounded policies with regret linear in the error | `Model.regret_signPolicy_eq_zero`, `Model.signPolicy_eq_of_behaviorEq` | No | — | the sufficiency direction. The atlas proves a sign policy is optimal and that equal transforms give a shared one, which is the zero-error corner of the printed claim; the linear-in-error statement needs the approximate model the row above lacks |
| §3 remark | Theorems 2 and 3 together make an approximate causal model necessary and sufficient for regret-bounded policies | — | No | — | a conjunction of two `No` rows |
| §3 finely-tuned example | a chain where intervening changes only the variance of the utility, leaving the optimum fixed | — | No | — | print's illustration of why almost-every is needed. It is about a continuous latent, which the finite categorical kernel cannot state |
| App. C–D, Lemmas 3, 4, 5, D's Lemma 4, 6 | a unique deterministic optimum almost everywhere; the query identifiable from an optimal oracle; its point estimate and two-sided bounds from a tolerant oracle; and their expansion at small regret | — | No | — | the identification algorithm. Every one of them quantifies over the parameter chart or the oracle, and grouped as one row because they stand or fall together |
| Cor. 1 (**working text only**) | Theorem 2 restated for an agent meeting a regret bound, obtained by substituting its policy for the oracle's | — | No | — | absent from the published proceedings. Recorded so that a reader working from the arXiv text does not read its absence here as an oversight |
| — | margins in place of the almost-every exception | `Skeleton`, `Skeleton.MarginClass`, `Skeleton.ValidMargin` | — | **Beyond** | the six margin conditions are an explicit-inequality replacement for print's measure-zero exclusion. Print never states them; Uhler et al. motivates the *move* but its object is a partial-correlation bound, not these CPT inequalities |
| — | a margin class does not determine behaviour | `Examples…margin_class_not_identifiable_real`, `Examples…margin_class_not_identifiable_two_graphs_real` | — | **Beyond** | two models in one margin class, over the reals, with opposite one-edge graph shapes and equal complete masked behaviour. Print asserts identifiability for almost all parameters; this exhibits a margin-class pair where it fails, which print does not state either way |
| — | equal behaviour forces one shared optimal policy family | `Examples…margin_class_not_identifiable_shared_optimal` | — | **Beyond** | the bridge applied to the collision: one policy family with zero regret in two distinct models |
| — | rational witnesses transport to any characteristic-zero ordered field | `Model.mapRat`, `Skeleton.marginClass_mapRat`, `Skeleton.behaviorEq_mapRat` | — | **Beyond** | print works over the reals and has no reason to state this. It is what lets a witness be *computed* on rational literals and then hold at print's generality; it is not a cast of its hypothesis, since real mixtures are not images of rational ones |

**10 Yes, 0 Partial, 13 No, 4 Beyond**, up from 7 Yes on 2026-08-22, when
Definition 4, Assumption 1 and the graph step of Lemma 1(iii) gained rows and
`Causal.DecisionNetwork` to sit in. The shape is worth stating plainly: the
atlas covers RE24's **setup** completely, and none of its **results**. The one
gap inside the setup was eq. (2) — the normalised utility carried as an invariant
with no map producing it — and `Skeleton.normalizeUtility` / `Skeleton.ofUtility`
closed it on 2026-08-20.
Every `No` row above fails for one of two reasons, and both are named — there is
no chart over a *CID's* parameters, so no almost-every statement about one can be
phrased; and there is no policy oracle, so no identification claim can be
phrased. Theorems 1 to 3 need both. The first reason is narrower than it was
before 2026-08-21: a real parameter chart now exists for MAIS's unmediated
chance-variable tables, with a Lebesgue estimate over it. What is missing is a
chart of a CID, which needs `D` and `U` as graph vertices — the same object the
`Decision.lean` scope fence names.

That is not a gap left open by neglect. The atlas's causal increment is the
MAIS-A2 composite, whose whole point is to replace the measure-zero exception
with margins, and margins are what the four `Beyond` rows record. The two
rows that were `Narrower` were all one thing — the unmediated projection — and it
was not closable by generalisation. **It closed by construction on 2026-09-20**:
`Causal.DecisionNetwork` has decision and utility vertices, and
`expectedUtility_eq_value` and `regret_eq_value_regret` prove the projection is
the printed CID equation under Assumption 1, so both rows are `Same`. The map from
a `Causal.SCIM` decision vertex to `Model.value` is still unwritten; nothing in
this section needs it.

---

## 7. Pearl, *Causality* 2nd ed. §1.3 → `AISafetyAtlas.Causal.BayesianNetwork`

**Which text.** `pearl-2009-causality-second-edition.pdf`, sha256
`0c1e7bd1676260feb5ec909839b01f1ff16538febfe23755192e565895202e4c`, 487 pp. Its
title page reads *Second Edition* and its contents list gives **§1.3 *Causal
Bayesian Networks* at book p. 21**, which is where Definition 1.3.1 sits. A
second copy is held under a different filename and is **byte-identical** — same
digest — so the two names are one document and either resolves here.
*Hash recorded 2026-09-13; before that this section pinned no document.*

**Where these declarations live.** Equation (1.37) and the interventional
profile are in `Causal.Model`; Definition 1.3.1 itself — the compatibility
condition, its truncated-product consequence and the counter-witness — is in
`Causal.BayesianNetwork`, hosted by `LAND-CAUSAL-PEARLCBN-001` since 2026-08-22.
Before that row existed this section graded a module no registry row carried, so
the grade was invisible on every generated status page.

Pearl grounds the interventional reading, and nothing else. Definition 1.3.1 is a
*semantic* condition — a DAG is a causal Bayesian network compatible with a whole
family of interventional distributions if three conditions hold for every member.
The atlas kernel is constructive data, a graph together with tables, so it does
not state that condition; it certifies the consequence Pearl derives from it.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| eq. (1.37) | the interventional distribution is the product of unintervened CPDs over values consistent with the forced ones | `hardInterventionProfile`, `Model.jointProb_hardInterventionProfile` | Yes | **Wider** | Pearl derives this from Definition 1.3.1's three conditions; the atlas builds it and proves it, for arbitrary local maps rather than hard interventions only. Same declarations as RE24's truncated-factorisation row, because it is the same formula, and the same witness: `Examples…jointProb_sum_shiftCollapse` runs a translation composed with a non-injective map, neither of which eq. (1.37) can express |
| eq. (1.37) full-profile corollaries | forcing every variable leaves a point mass, and an outcome function is then evaluated at the forced value | `fixProfile`, `Model.jointProb_fixProfile` | Yes | Same | Pearl states the truncated product and does not separately assert this consequence of it. By the rule above that is coverage and not a widening, so the cell stays `Same`; the corollaries are proved for every finite acyclic variable set, which is the printed generality |
| Def. 1.3.1 | a DAG is a causal Bayesian network compatible with a family of interventional distributions iff Markov relative to the graph, forced values have probability one, and unintervened CPDs are invariant | `InterventionalFamily`, `ConditionalTables`, `IsCausalBayesNetwork`, `eq_family_of_isCausalBayesNetwork`, `isCausalBayesNetwork_iff`, `Model.interventionalFamily`, `Model.isCausalBayesNetwork` | Yes | **Same** | built on 2026-08-21, and the row's own diagnosis was the design: the missing object was the family. `InterventionalFamily` is `P_*` at Definition 1.3.1's own index set, hard interventions, so a statement about it grades against the definition rather than past it. Conditions (ii) and (iii) are stated on **tables** rather than on conditionals, deliberately: print writes (iii) as *P_x(v_i given pa_i) = P(v_i given pa_i)*, a quotient, and a parent configuration of zero probability is reachable — the margin conditions of `Causal.MarginClass` exist to exclude it — so a quotient rendering would go vacuous exactly on the fibres where a degenerate mechanism needs constraining. The existential is hoisted once, one observational `q` with each member's own `r` agreeing off the intervened set; `Examples…not_isCausalBayesNetwork_badFamily` witnesses that this constrains, exhibiting a family whose two members are each truncated products and which is still not a causal Bayesian network. The truncated product is **not** part of the definition: `eq_family_of_isCausalBayesNetwork` derives it, as print does |
| Property 1, eq. (1.38) | the conditional given the parents equals the effect of setting the parents by external control | `Model.marginal`, `Model.marginal_insert_parents`, `Model.marginal_eq_sum_ancestral` | Yes | **Same** | the printed identity is *P(v_i given pa_i) = P_pa(v_i)*; the atlas states it multiplied out, as *P(v_i, pa) = P(pa) · P_pa(v_i)*, for the null-fibre reason in the Def. 1.3.1 row. It compares two *marginals* of the family, which is why it needed the marginalization layer and not just the family. The proof marginalizes both sides through the ancestral closure of `{c} ∪ Pa(c)`: erasing `c` from that closure leaves a parent-closed set — no ancestor of `c` has `c` as a parent, by acyclicity — so both marginals run over the same index set and differ by the single factor the printed conditional names |
| Property 2, eq. (1.39) | once the direct causes are controlled, no further intervention on a disjoint set changes the child's probability | `Model.marginal_singleton_do_parents`, `Model.marginal_union_targets` | Yes | **Same** | **This cell read `Wider` from 2026-08-21 until 2026-08-22, and it is retracted rather than re-argued.** Print states the property for a set disjoint from the variable *and its parents*; the atlas hypothesis names only the variable, so `extra` may name a parent. That is a weaker **binder** and not a wider statement. Both sides read `extra` only through the forced set `Pa_c ∪ extra`, and `Pa_c ∪ extra = Pa_c ∪ (extra \ Pa_c)`, so every instance the weaker binder admits is print's own instance at `extra \ Pa_c` — print implies the atlas statement, and `Wider` on this table requires that implication to fail. The retracted cell rested on the rule that a weaker hypothesis with the same conclusion widens a row, which is a fact about how a statement is bound where this column grades which statements are admitted; it is the same substitution the §8 preamble retracts twice on the other side. **The disclosure the note carried is kept**, because it is what a reader checking the Lean needs: the theorem is stated for any `extra` not containing the variable, the marginal is the variable's own mechanism whatever else is forced, and disjointness from the *parents* is neither needed nor assumed. `marginal_union_targets` is in this row's column for what it does inside the proof — enlarging the conditioning set from `{c}` to `{c} ∪ Pa_c` — not as the reason the binder can be weak; the union above is that reason. **The stability rule is not in play**: this moves on a corrected derivation about the atlas statement, not on a re-reading of Pearl |
| — | normalisation of the constructed joint | `Model.jointProb_sum`, `jointProb_sum_two` | — | **Beyond** | that the acyclic product of stored simplexes is a probability distribution is assumed in print, not argued. Proved here for every finite acyclic variable set, every positive dimension vector, and every intervention profile |

**5 Yes, 0 Partial, 0 No, 1 Beyond**, revised on 2026-08-21. The three `No` rows
were the same absence three times — no object representing the family of
interventional distributions — and `AISafetyAtlas.Causal.BayesianNetwork` is that
object. The boundary has moved: the atlas now takes Pearl's *definition* as well
as his formula, and derives the formula from it. What remains outside §1.3 is
identification — do-calculus, the back-door criterion, d-separation — which needs
a `do`-expression language rather than another distribution.
The layer was built to a written scope contract, which records what it
deliberately does not claim — notably that the observational member does not
determine the family.

---

## 8. Everitt, Carey, Langlois, Ortega & Legg, AAAI 2021 → `AISafetyAtlas.Causal.StructuralModel`

Implementation handoff (2026-09-14): [CIDs and Ring–Orseau unblocking](cid-ring-unblocking.md) records the new probability-law and value-recursion bridges, their verified witnesses, and the still-open consumer obligations. It changes no grade in this table.

**Which text.** Everitt, Carey, Langlois, Ortega and Legg, *Agent Incentives: A
Causal Perspective*, read from the pinned PDF
`everitt-etal-2021-aaai-ojs.pdf`, sha256
`31d4a4b277c562b82000c4d2b81660e89464877ec0cad3549a9375c6d4492598`. Confirmed on
2026-09-13 from the document's own first page, rendered as an image: the title
above, those five authors, *"The Thirty-Fifth AAAI Conference on Artificial
Intelligence (AAAI-21)"*, page 11487. This is the text Definitions 1 to 5 are
transcribed from.

**This paragraph was owed, and its absence had a consequence.** Until 2026-09-13
this section pinned no digest for its own source, while pinning digests for two
works it only *compares* itself against — Pearl, below, and Bongers et al.,
further below. A reader or a tool taking the first digest in the section got
Bongers's, which is the general-SCM paper and not the text any row here is
graded against. A hash join proves byte identity, never bibliographic identity;
the corroboration is the rendered title page, not the filename and not the
digest.

This source supplies the causal influence diagram the decision layer is a
projection of, and its own results are graphical incentive criteria. The atlas
formalizes the setup — Definitions 1 to 5, in `AISafetyAtlas.Causal.StructuralModel`
— and none of the criteria. The section is graded so that the boundary is visible, which is the reason the audit
lists `No` rows at all.

**Four narrowing axes ran through this section; three are closed and one
remains.** They are not repeated in each note. Print bounds no cardinality anywhere in Definitions 1 to 3: Definition 1
writes `dom(V)` with no condition on it and `Pa_V ⊂ V` with no condition on it,
and Definition 3 is *"a directed acyclic graph"*, full stop. Definition 4 is the
first place finiteness appears, and it restricts the **domains** — not how many
variables there are, not how many parents a variable has, and not the shape of
the acyclicity.

**The source was re-read for a global bound on 2026-08-21 and does not carry
one.** In the pinned PDF *"finite"* occurs exactly twice, both as
*"finite-domain"*, both inside Definition 4; *"discrete"*, *"finitely many"*,
*"countable"* and *"infinite"* do not occur anywhere. There is no preliminaries
sentence, footnote or `throughout`-clause declaring finiteness globally, so the
four axes below were the atlas's and not print's. Three of the four have since
been closed against that reading; the dates are on the bullets.

* **Finitely many variables — CLOSED on 2026-08-21.** `[Fintype V]` was on
  `SCM`, `CID` and `SCIM` alike. It is on none of them now. The constraint moved
  onto the operations that genuinely need it — the `Finset` accessors
  `decisions` / `utilities` / `structureNodes`, and the expectation layer — and
  `CID.IsDecision` / `CID.IsUtility` read print's *"the vertex set is partitioned
  into `X`, `D`, `U`"* as a property of each vertex, which is what a partition
  is. `mem_decisions_iff` and `mem_utilities_iff` recover the `Finset` forms
  whenever `V` happens to be a `Fintype`. Relocating a constraint from a
  definition to its use sites relaxes the definition against its own previous
  form; it is not a hypothesis added to a theorem, and it is not the laundering
  the scope rule forbids.
* **Finite domains — CLOSED 2026-09-20, on Definitions 1 and 2.** The domains
  were `V → ℕ` on `SCM` and `SCIM`, never on `CID`, whose four fields are the
  parent map, the acyclicity condition, the vertex kind and the childlessness of
  utility vertices — no domains at all. On Definitions 1 and 2 that restriction
  had no printed counterpart; from Definition 4 on it is print's own and costs
  nothing. The domains are now a family of **types**, the marginal-sum field is
  unconditional, and every finiteness condition sits on the derived operation
  that needs it: the finite sums of `jointProb` and `marginal`, the maximum over
  policies at Definition 5, and the singleton masses in the measure layer. That
  is the same move the vertex set made on 2026-08-21, and the section's own
  criterion for it — relaxing the definition against its previous form rather
  than adding a hypothesis to a theorem — is met.
* **Finite indegree — CLOSED on 2026-08-22.** `parents : V → Set V` on both
  `SCM` and `CID`, so a vertex may have infinitely many parents, which is
  print's `Pa_V ⊂ V` at Def. 1 and print's silence at Def. 3. The
  parent-reading obligation on the structural functions quantifies over the set;
  nothing in this section sums over parents, so no finiteness hypothesis was
  needed anywhere. One visible cost: a policy's defining property is no longer
  decidable, so `Fintype SCIM.Policy` is now the classical instance
  `SCIM.instFintypePolicy`. Finiteness of the policy space is unaffected, and
  nothing computes with it.
* **ℕ-ranked acyclicity — CLOSED on 2026-08-22, and the two closures are one
  closure.** `CID.acyclic` is now print's condition and nothing more:
  `∀ v, ¬ Relation.TransGen (` `· ∈ parents ·` `) v v`, no vertex reachable
  from itself. `SCM` and `SCIM` ask instead that the parent relation be
  **well-founded**. That is a genuine strengthening of print's bare word, and
  this audit states it rather than hides it: `V = ℤ` with `parents n = {n-1}`
  is acyclic and is excluded.

  **It was a narrowing, it was graded as one, and it closed on 2026-08-22.**
  An earlier draft of this preamble called it `Same` on the argument that print
  must have meant the narrower class. That is the laundering the standing rule
  forbids, and this table has no fidelity dimension in which to park it: the
  scope cell is the only cell, so a field print does not write makes the row
  `Narrower`. Definitions 1, 2, 4 and 5 read `Narrower` for this reason.

  **The witness.** `chainParents n = {n-1}` on `ℤ` satisfies `CID.acyclic`
  (`chainParents_acyclic`) and fails `SCM.wellFounded`
  (`chainParents_not_wellFounded`). On it, with two states per vertex and the
  structural function that copies the parent, the equation `eval_eq_f` asks for
  is `W v = W (v-1)`, which has **two** solutions —
  `chainParents_fixedPoint_not_unique`. Print's Definition 1 says the value is
  *"given by recursive application of the structural functions"*: one value,
  *the* value. On a diagram print's own words admit, print's own words name no
  unique assignment.

  **Retracted: this axis was labelled *provably not closable*, and the label was
  wrong.** The paragraph that carried it is kept here rather than deleted:

  > **Why that makes the axis not closable rather than merely expensive.** A
  > total `eval` could still be produced on the wider class by choice, and it
  > would even satisfy `eval_eq_f`; what it would lose is that `eval_eq_f` pins
  > it down. The atlas would then be asserting a determinacy Definition 1 does
  > not have. There is no version of this refactor that widens the class and
  > keeps the theorem meaning what it says, which is what *provably not
  > closable* is for.

  Every sentence there is true, and not one of them is about the class this
  table grades. They are about a **total** `eval`, and a total `eval` is not the
  only refactor on offer. Take `SCM.wellFounded` off the structure and `SCIM.graph_wellFounded`
  off its own; give both print's own condition in the `Relation.TransGen` form `CID`
  already carries; pass well-foundedness as a **hypothesis** to `eval` and to
  the declarations that consume it. The admitted class is then print's class
  exactly, `eval` is simply not defined where print's *"recursive application"*
  names nothing, and `eval_eq_f` still pins down what it does define. That is
  the version the old paragraph asserted does not exist. Calling the axis
  unclosable collapsed *"`eval` cannot be totalised over print's class"* into
  *"the structure must carry the field"*, and those are different claims —
  the same collapse, one dimension over, as the `Bridged` grade this preamble
  already retracts below.

  **Done.** `SCM.wellFounded` and `SCIM.graph_wellFounded` are
  gone; `SCM.acyclic` is print's word in the same form `CID` carries it; and the
  recursion's requirement is `SCM.IsWellFounded` and `CID.IsWellFounded`, two
  classes that `eval`, `jointProb`, `expectedUtility`, `optimalValue` and
  `IsMaterial` ask for. Instances carry it across `submodel`, `softIntervention`,
  `withPolicy` and `removeInfoLink`, so no statement asks for it twice.
  **Definition 4 closes**, because its column is the structure alone. Definitions
  1, 2 and 5 do not, on axes that have nothing to do with this one.

  **Why the hypothesis on the operations is not a new narrowing.** Print's
  Definition 1 asserts *"the value ... given by recursive application"* — one
  value — and `chainParents_fixedPoint_not_unique` proves print's own words name
  two on an acyclic chain. The instance is what makes print's sentence denote,
  which is the same test this preamble applies to finite `V` at Definition 5's
  maximum, and the opposite of the test it fails at the expectation layer's sum,
  where print's object denotes without the instance.

  **The witness keeps its job and loses its title.** `chainParents` and its three
  theorems are not evidence that the field belongs on the structure. They are a
  theorem about *print*: on a diagram print's own word admits, print's own words
  name no unique assignment. That is why `eval` asks for `SCM.IsWellFounded`
  wherever it is stated, and none of it is retracted.

  Definition 3 closed first and needed nothing: `CID` evaluates nothing, so it
  never carried well-foundedness and has always had print's word unmodified.
  Definition 4 closed second, once the field moved off `SCIM`.

  **Why this could not be done alone.** `wellFounded_iff_exists_rank` proves
  that while `parents` was a `Finset`, well-foundedness and an `ℕ`-valued rank
  were *equivalent* — the rank is rebuilt by well-founded recursion as one more
  than the largest rank among the parents, and that step is exactly where the
  finiteness of the parent set is spent. Dropping the rank without also dropping
  the `Finset` would have admitted precisely the same models and generalized
  nothing. The triage priced these as two axes that were cheaper together; they
  are one axis, and the note there is corrected.

**Both of the two axes above were missed when the vertex-set axis closed**, and
the Def. 1 row asserted for one day that domains were the only axis left. They
were restrictions in the structure, visible in the field types, with no printed
counterpart. They are recorded here because the miss is the reason this section
now grades on the artifact rather than on the printed object's nearest
counterpart.

**A claim this section used to make, and what replaced it.** It said the vertex
axis was "an implementation choice, not a theorem of the source", because
well-founded recursion on the acyclicity rank would evaluate an infinite diagram
whose nodes all have finite rank. The conclusion was right and the reason was
wrong about the code: `SCM.eval` was an iteration stopped after `Fintype.card V`
applications, so rank recursion was a **rewrite**, not a relabelling. The axis
closed without that rewrite, because the structures' own fields never needed the
instance — only their derived operations did.

**`[Fintype V]` on the derived operations does three jobs, and they do not get
the same verdict.** This paragraph used to give only the first two and conclude
that the instance was print's throughout; that conclusion was applied at
Definition 5 and denied at the policy row two rows apart, which is a
contradiction a reader meets without looking for it. Adjudicated once, on
2026-08-22:

1. **The maximum over policies is attained.** Print writes `V*(M)` as the
   *maximum* of `E_π[U]` over policies, not a supremum, and states no condition
   delivering one; over an infinite policy space it need not be attained. Finite
   `V` delivers it. **Transcribes print** — `optimalValue` as a `Finset.sup'`
   with `exists_isOptimalPolicy` exhibiting the attaining policy is print's own
   sentence made to denote, not a class cut below print's.
2. **The utility total converges.** `E_π[U]` sums over utility vertices, which
   print never bounds; at infinitely many the sum need not converge.
   **Transcribes print**, for the same reason.
3. **The expectation is a finite sum.** `exoJoint` is `∏ v : V`, `jointProb`
   sums over `ExoAssignment V edom`, and `expectedUtility` sums over the same —
   each a `Finset` operation that exists only at `[Fintype V]`. **This one
   cuts.** Print's `P(ε)` is a distribution under which the exogenous variables
   are *mutually independent*, and mutual independence denotes at unbounded `V`:
   it is the product measure, which exists. The atlas renders it as a finite
   product and a finite sum. That is the atlas's elementary choice, not print's
   silence being filled, and it is a **narrowing** — the same one the policy row
   has named all along.

**Which rows carry job 3.** Definition 1, through `jointProb`, `jointProb_sum`
and `exoJoint_mul_prod`; Definition 5, through `optimalValue`, which is a
`Finset.sup'` **of** `expectedUtility` and so inherits its summation; and the
policy row, which named it first. **Definition 2 does not** — `submodel`,
`submodel_eval`, `submodel_eval_notMem` and `softIntervention` every one carry
`omit [Fintype V]`, so that column is instance-free. **Definition 4 does not** —
its column is `Causal.SCIM`, a structure that has carried no `[Fintype V]` since
2026-08-21.

**Job 3 closed on 2026-09-20, and the argument is the one Definition 6 had just
established.** `SCM.exoLaw` — print's `P(ε)` as the product measure, built on
2026-09-14 over an arbitrary vertex type — had never been read by the
expectation layer, which went on summing. It is read now.
`SCIM.expectedUtilityLaw` is `Eπ[U]` as an integral against it at an unbounded
vertex set, `SCM.endoLaw` is print's *"this induces a joint distribution"* as a
distribution, and `SCIM.expectedUtilityLaw_eq` and `SCM.endoLaw_singleton` prove
the finite sums **compute** them. So the `Finset` operations are the
computation, not the reading, in exactly the sense `CID.DSep` is the computation
of `CID.DSepPath`: an unbounded rendering exists and a converting lemma connects
it, which is what this table's own precedent — `CID.decisions` with
`mem_decisions_iff` — was set up to license.

**The distinction this turns on, since it reverses a verdict above.** Job 3 was
adjudicated as cutting and jobs 1 and 2 as transcribing, and that adjudication
stands unchanged: what made job 3 cut was that print's object denoted at
unbounded `V` and the atlas had no rendering of it. Now it has one. Jobs 1 and 2
are still not narrowings and still have no unbounded rendering, because there is
nothing to render — print's *maximum* over an unbounded policy space and print's
*sum* over an unbounded `𝐔` do not denote, and finiteness is what makes print's
own sentences mean something. `SCIM.IsOptimalPolicyLaw` is where that line falls
inside Definition 5's own sentence: *"any policy that maximises `Eπ[U]`"* is a
comparison and generalises, while *a maximiser exists* is
`SCIM.exists_isOptimalPolicy` and does not.

**Two hypotheses are carried and neither is a bound on `V`.** `𝐔` is a `Fintype`
on the subtype rather than a consequence of a finite vertex set — that is job 2,
named and made explicit. And measurability is a hypothesis, because an
evaluation reading infinitely many parents need not be measurable and a Bochner
integral of a nonmeasurable function is **silently zero**; it is the hypothesis
`SCM.observableLaw` already carried, discharged by `SCM.measurable_exo` wherever
`V` is finite, so nothing print asserts is bought with a condition print lacks.

**What job 3's closure does not reach: Definition 17's conditioning, and that is
a finding rather than a remainder.** `SCIM.condExp` is a ratio of two sums over
`SCIM.contextFiber`, a filtered `Finset.univ`, so Definitions 17 and Theorem 18
keep a `[Fintype V]` that the expectation layer's closure does not touch. It is
not the same axis wearing a new name. Print's `E_{π*}[· | pa^D]` conditions on
the event `Pa^D = pa^D`, and once `Pa^D` may be infinite — which Definition 3
permits and this section's finite-indegree closure of 2026-08-22 made real —
that event can have measure zero under `SCM.exoLaw`, where print's conditional
expectation names nothing at all. Print writes `Pr(pa^D) > 0` at Definition 13
and writes no condition at Definition 17. So generalising `condExp` is not a
transcription job: it needs a conditional expectation given a σ-algebra, and it
needs a reading of Definition 17 that print does not supply. Those two rows are
costed on that, separately, below.

**What this costs, stated plainly: it adds an axis to two rows and closes
none.** Definitions 1 and 5 each gain a third named axis and neither grade
moves, because both were already `Narrower`. The policy row keeps `Mixed` and
gains a sharper reason. The alternative reading — job 3 also transcribes — would
have moved the policy row to `Wider` and gained a cell, and it is the reading
this adjudication rejects.

**The source Definitions 1 and 2 are attributed to, read at last — 2026-08-22.**
Print heads them *"Structural causal model; Pearl 2009, Chapter 7"* and
*"Submodel; Pearl 2009, Chapter 7"*. This section grades against Everitt's
statement of them, because that is the text transcribed, and that convention
stands. But nothing in this audit had ever opened Pearl 7.1.1, and it says three
things that change how the axes here should be read.

* **Pearl's endogenous set is finite.** *"`V` is a set `{V₁, V₂, …, Vₙ}` of
  variables"*, with the structural functions indexed `i = 1, …, n`. So the
  `[Fintype V]` this section removed on 2026-08-21 — as a narrowing against
  Everitt, who never bounds the vertex set — was **Pearl's own condition**.
  Dropping it did not repay a debt; it widened the atlas past *both* sources.
  That is `Wider`, which the standing rule permits, and it is worth saying
  plainly rather than leaving on the books as a closed narrowing.
* **Pearl bounds no domain**, and neither does Everitt before Definition 4. Axis
  B is a narrowing against both, and it is the one axis here that both sources
  agree the atlas invented.
* **Pearl requires unique solvability, in the definition.** Clause (iii) ends
  *"and the entire set `F` has a unique solution `V(u)`"*, with a footnote:
  *"Uniqueness is ensured in recursive (i.e., acyclic) systems. Halpern (1998)
  allows multiple solutions in nonrecursive systems."* So determinacy is part of
  the object for Pearl, and acyclicity is offered as a *sufficient condition* for
  it rather than as the content.

**That third point re-reads this section's largest argument.** `chainParents`
was written as a witness that Everitt's *"acyclic"* fails to name a unique
`W(ε)` at an unbounded vertex set. It is that. But against Pearl it says
something sharper: Everitt's paraphrase **dropped a clause its own cited source
carries**, and the clause it dropped is exactly the one `SCM.IsWellFounded`
restores. Pearl's footnote even anticipates the failure — uniqueness is ensured
in *recursive* systems, which at finite `V` is what acyclicity delivers and at
unbounded `V` is not. So the atlas's shape here — print's `acyclic` as a field,
solvability as a property asked for where the recursion is used — is **not** a
strengthening of the source-of-record. It is the source-of-record's own clause,
carried where it can be discharged rather than assumed everywhere.

**And the treatment that pushes this object as far as it goes — 2026-08-22.**
Bongers, Forré, Peters and Mooij, *Foundations of structural causal models with
cycles and latent variables*, Annals of Statistics 49(5), 2885–2915, read from
the pinned PDF `2021 foundations of structural causal models with cycles and
latent variables.pdf`, sha256
`6ce97700deb27a6e6fc680d0bd8cbfd053f1f67392979afca8e67d9f289a6d31`. It is the
mathematicians' general version — cycles allowed, latent variables, arbitrary
domains — so it is the right place to ask which of this section's axes the field
actually cares about. Definition 2.1 makes an SCM a tuple
`⟨I, J, 𝒳, ℰ, f, P_ℰ⟩` where:

* **`I` is a finite index set of endogenous variables**, and `J` a disjoint
  finite index set of exogenous ones. The most general published treatment of
  this object keeps the vertex set finite, exactly as Pearl does and as Everitt's
  paraphrase does not. **So the `[Fintype V]` this section removed on 2026-08-21
  was a debt to nobody.** It is a `Wider` cell rather than a repaid narrowing,
  and the honest note is that the widening is free and has no known consumer.
* **Domains are arbitrary standard measurable spaces**, `𝒳 = ∏_{i ∈ I} 𝒳_i`, and
  `f : 𝒳 × ℰ → 𝒳` is measurable. **This is where the literature generalizes**,
  and it is exactly axis B taken past `Fin (dom v)` — the axis this section
  carried longest and closed on 2026-09-20, and the one both Pearl and Everitt
  leave unbounded. The atlas's domains are arbitrary **types** rather than
  standard measurable spaces, so the measure layer still asks for a
  measurable-space instance on each where it needs one; that is less than Bongers and
  colleagues assume and more than print writes.
* **`P_ℰ` is a product measure.** Print's *"mutually independent"* rendered as a
  product is the general form, not a finite-sum convenience — what this section
  calls axis F is the difference between a product **measure** and a `Finset`
  product, not between independence and something weaker.
* **Acyclicity is not in the tuple.** *"Although it is common to assume the
  absence of cyclic functional relations, we make no such assumption here. In
  particular, we allow for self-cycles."* Definition 2.9 then defines *acyclic*
  as a property of the SCM's graph. And Definition 2.3 makes a **solution** a
  pair of random variables satisfying the structural equations almost surely,
  with Example 2.4 exhibiting one SCM with a continuum of solutions and one with
  none at all. Unique solvability is a **named condition** the theory carries
  where it needs it.

**That is the shape axis E produced, arrived at independently.** Solvability as
a property asked for where the recursion is used, rather than acyclicity as a
field standing in for it. The remaining difference is that `SCM` still carries
`acyclic` as a field where this treatment carries none — which is a further
widening available later, not a defect, since print does write the word.

**Where the rows stand after 2026-08-22.** **Definitions 3 and 4 close.**
Definition 4 closed last, when `SCIM.graph_wellFounded` came off and became
`CID.IsWellFounded` — a property asked for by the declarations that evaluate
rather than a field of the tuple. Definition 5 did not follow, and the reason is
the grading convention rather than the mathematics: its column also holds
`optimalValue` and `removeInfoLink`, so the expectation layer is graded there
and Definition 4's is the structure alone. Definitions 1 and 2 kept domains until
2026-09-20 and no longer do. **One open axis remains in this section** —
conditioning, at Definition 17 and Theorem 18 — and the well-foundedness axis is
closed rather than open, having been labelled *provably not closable* in an
intermediate revision. The expectation layer's `[Fintype V]` was the second of those until
2026-09-20 and is closed; what survives at Definition 17 is a different
obstruction and the job-3 paragraph below says why. A third ran at Definitions 6 and 7
between 2026-09-10 and 2026-09-20 and is closed: the d-separation module was
found to reopen the vertex-set axis, and the two parts of that — the `Finset`
carrier and the walk-versus-path reading — closed together on 2026-09-20, which
took Definition 6 to `Same` and Definition 7 to `Wider`. The policy row stays `Mixed`.

**This paragraph read "Definitions 3, 4 and 5 close" in an earlier revision**, on
the strength of a `Same`/`Bridged` grade that this table has no fidelity column
to express. The scope cell is the only cell, and a field print does not write
makes a row `Narrower` no matter how good the argument for the field is. The
argument was good and is kept — it is now the *witness* attached to a
`Narrower` axis rather than a reason to call the row `Same`, which is the state
the standing rule actually provides for.

What the refactor did buy on those four rows is real and smaller than claimed:
finite indegree closed outright, and the acyclicity axis **shrank** — an
`ℕ`-valued rank is strictly stronger than well-foundedness once parent sets may
be infinite, so the admitted class genuinely widened. It did not reach print.

The policy row does **not** close, and the triage predicted wrongly that it
would become plainly `Wider`. Its graph-axis half is indeed gone, but a third
narrowing survives and was already named in its own note: `expectedUtility` sums
over `ExoAssignment V edom` and `exists_isOptimalPolicy` needs the policy type
finite, so `[Fintype V]` is still present in that row's operations even though
it is absent from `SCIM` itself. Wider on the decision axis, narrower on the
vertex-set axis: still `Mixed`.

Each note below says only what its row adds to the axes above.

**The convention these rows are graded under, stated because it decides three of
them.** A row is graded on **every declaration in its atlas column**, not on the
printed object's nearest atlas counterpart alone. That is the atlas's existing
convention, written into `registry.yaml` as *"both are in the public types, so
the row is graded on the artifact"*. It matters because `CID.decisions`,
`CID.utilities` and `CID.structureNodes` are `Finset.univ.filter …` and need
`[Fintype V]` even though `CID` does not. Grading the structure alone would let
a row read `Same` while the operations it names are unavailable at the
generality the row claims.

The finiteness axis is **not** applied to Pearl §1.3, which is also formalized over a
`[Fintype C]` graph. That is deliberate and it makes the grading non-uniform:
Everitt's finiteness is load-bearing — `eval` needs it to terminate and
`optimalValue` needs it to be a maximum — whereas Pearl's displayed (1.37) is a
finite product over the graph's own vertices, so a finite index set is what the
printed equation already ranges over. A reader who disagrees should read this
paragraph as the whole of the disagreement.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Def. 1 structural causal model | a tuple `⟨E, V, F, P⟩` with one exogenous variable per endogenous one, structural functions `f^V : dom(Pa_V ∪ {E^V}) → dom(V)` with acyclic dependencies, and a `P(ε)` under which the exogenous variables are mutually independent | `Causal.SCM`, `SCM.eval`, `SCM.eval_eq_f`, `SCM.jointProb`, `SCM.jointProb_sum`, `SCM.exoJoint_mul_prod`, `SCM.endoLaw`, `SCM.endoLaw_singleton`, `Examples.Causal.StructuralModel.independentBits_endoLaw_first_zero`, `wellFounded_iff_exists_rank`, `chainParents`, `chainParents_acyclic`, `chainParents_not_wellFounded`, `chainParents_fixedPoint_not_unique`, `EndoAssignment`, `exoProb_sum_fintype`, `Examples.Causal.StructuralModel.boolFlip`, `Examples.Causal.StructuralModel.geometricCopy`, `Examples.Causal.StructuralModel.geometricCopy_eval` | Yes | **Same** | **The `Fintype V` axis closed on 2026-08-21.** Across the whole paper *"finite"* occurs exactly twice, both inside Def. 4 and both qualifying **domains**; the vertex set is never bounded. `SCM`, `CID` and `SCIM` therefore no longer carry `[Fintype V]`: the constraint moved onto the derived operations that genuinely need it — the `Finset` accessors and the expectation layer. That relaxes the definition against its own previous form rather than adding a hypothesis to a theorem, so it moves the row toward print rather than away. `CID.IsDecision` and `CID.IsUtility` read print's *"the vertex set is partitioned into `X`, `D`, `U`"* as a property of each vertex, which is what a partition is; `mem_decisions_iff` and `mem_utilities_iff` recover the `Finset` forms whenever `V` is a `Fintype`. **Source-class narrowing**: this module has no library-module importer, so nothing proved elsewhere in the tree is weaker for it, and the cost falls on a future consumer instantiating `SCM` outside the admitted class. **Two axes remained and both are now closed.** (i) Domains — **CLOSED 2026-09-20**: print writes `dom(V)` with no cardinality condition and imposes finiteness only at Def. 4, while `SCM` carried `dom edom : V → ℕ`. They are now a family of **types**. `EndoAssignment` and `ExoAssignment` are the assignment spaces at that carrier — `Assignment` keeps the `Fin`-indexed shape and belongs to section 6's decision layer, and the two layers do not meet, so no bridge between them is owed. The positivity field became a nonemptiness one, since what print's `dom(V)` being inhabited buys is that the structural functions are well-typed. The marginal-sum field became an **unconditional** sum, which says what print says at a domain of any size; `exoProb_sum_fintype` is its finite reading. Every finiteness condition moved onto the derived operation that needs it — the same move the vertex set made on 2026-08-21 — so `SCM` itself carries none, and `Examples.Causal.StructuralModel.geometricCopy` is a model with **infinite** domains that `eval` and `submodel` run on and no sum in this section can be written over. (ii) Finite indegree — CLOSED 2026-08-22: `parents : V → Set V`, print's unbounded `Pa_V ⊂ V`. (iii) Acyclicity — **CLOSED 2026-08-22, in two steps.** It was an `ℕ`-rank, then well-foundedness of the parent relation, and it is now `SCM.acyclic : ∀ v, ¬ Relation.TransGen (` `· ∈ parents ·` `) v v` — print's *"acyclic"* and nothing more, the same condition `CID` carries. Well-foundedness did not disappear; it moved to `SCM.IsWellFounded`, a class every declaration downstream of the recursion asks for. **That hypothesis is not a fourth axis**, on the criterion the preamble adjudicates: print's Definition 1 asserts *"the value ... given by recursive application of the structural functions"* — one value, *the* value — and `chainParents_fixedPoint_not_unique` proves that on an acyclic chain print's own words name **two**. So the instance is what makes print's sentence denote, exactly as finite `V` is what makes print's *maximum* denote at Definition 5. `chainParents` and its three theorems are the witness for the hypothesis; the earlier reading of them, that the axis was *provably not closable*, was retracted, and the preamble carries the retracted paragraph in full. **This row read `Same` in an intermediate revision** on a `Bridged` fidelity grade this table has no column for. `eval` no longer needs `[Fintype V]` either — it is well-founded recursion rather than an iteration run to a bound, and that iteration together with its two rank lemmas is deleted — so the sentence that graded the instance here no longer has a referent. `wellFounded_iff_exists_rank` is in this row's column because it is the witness that (ii) and (iii) were a single axis: while `parents` was a `Finset` the two acyclicity forms were equivalent. (iv) The expectation layer's `[Fintype V]` — **OPEN, and named here from 2026-08-22**: `jointProb`, `jointProb_sum` and `exoJoint_mul_prod` are `Finset` sums and products over `V`, which exist only at a finite vertex set, while print's `P(ε)` denotes at unbounded `V` because mutual independence gives a product measure. The preamble adjudicates this instance's three jobs and explains why attainment and utility-convergence transcribe print while summation does not. This row carried the axis unnamed until that adjudication; the policy row named it, and the two were graded inconsistently for as long as both existed. **The retracted sentence is left visible rather than deleted**: it once read *"One axis remains and it is domains"* while three remained. It is still not true — domains are the only *open* axis, but well-foundedness is a second axis in a different state, and collapsing the two is the same undercount that produced the retraction. **The expectation layer closed on 2026-09-20 and domains did not.** `SCM.endoLaw` is print's *"this induces a joint distribution"* as a distribution at an unbounded vertex set, and `SCM.endoLaw_singleton` proves `jointProb` is its singleton mass, so the `Finset` sum on this row is the computation of print's object rather than a reading of it; `Examples.Causal.StructuralModel.independentBits_endoLaw_first_zero` answers it at `V = ℕ`, where `jointProb` cannot be written at all. **The witnesses are what make the axis visible.** `boolFlip` has domains that are `Bool` rather than an index into `Fin 2` — a type print's `dom(V)` admits and a `Fin`-indexed family names only up to an isomorphism nobody supplied — and `boolFlip_jointProb_sum` shows Definition 4's finite layer still applies to it. `geometricCopy` has domains `ℕ` with a geometric exogenous law, evaluates by `geometricCopy_eval`, and admits print's Definition 2 by `geometricCopy_submodel_eval`. `Same` because the carrier is now print's and nothing was added to buy it. |
| Def. 2 submodel | `M_x := ⟨E, V, F_x, P⟩` with `F_x = {f^V \| V ∉ X} ∪ {X = x}`; more generally a soft intervention replaces `f^X` by a `g^X` on the same domain | `SCM.submodel`, `SCM.submodel_eval`, `SCM.submodel_eval_notMem`, `SCM.softIntervention`, `Examples.Causal.StructuralModel.geometricCopy_submodel_eval` | Yes | **Same** | print's construction, and **Source-class narrowing**, inherited: same module, same absence of importers. It inherited **one** of Def. 1's two remaining axes — domains — because `submodel` copies `parents` and the acyclicity field unchanged and alters only `f`, and it closed with Definition 1's on 2026-09-20; `geometricCopy_submodel_eval` is this construction at an infinite domain. It does **not** carry the expectation layer's `[Fintype V]`: all four of this column's declarations are `omit [Fintype V]`. Well-foundedness closed here with Definition 1 on 2026-08-22; `submodel` now builds print's `acyclic` by `Relation.TransGen.mono`, and `instIsWellFoundedSubmodel` carries the recursion's hypothesis across an intervention by `Subrelation.wf`, since forcing a variable only deletes edges. The vertex-set axis closed on 2026-08-21 and finite indegree closed on 2026-08-22, so neither is among them; `submodel` now inherits well-foundedness by `Subrelation.wf`, since forcing a variable only deletes edges. `submodel_eval` is *"the original functional relationships of `X ∈ 𝐗` are replaced with the constant functions `X = x`"* read off the evaluation. Domains was the last one and closed with Definition 1 above, so nothing is owed here. |
| Def. 3 causal influence diagram | a DAG whose vertex set is partitioned into structure, decision and utility nodes, where utility nodes have no children; `Pa_D` are the observations | `Causal.CID`, `CID.decisions`, `CID.utilities`, `CID.structureNodes`, `CID.observations`, `CID.decisions_disjoint_utilities`, `acyclic_of_rank` | Yes | **Same** | **The `Fintype V` axis closed on 2026-08-21.** Across the whole paper *"finite"* occurs exactly twice, both inside Def. 4 and both qualifying **domains**; the vertex set is never bounded. `SCM`, `CID` and `SCIM` therefore no longer carry `[Fintype V]`: the constraint moved onto the derived operations that genuinely need it — the `Finset` accessors and the expectation layer. That relaxes the definition against its own previous form rather than adding a hypothesis to a theorem, so it moves the row toward print rather than away. `CID.IsDecision` and `CID.IsUtility` read print's *"the vertex set is partitioned into `X`, `D`, `U`"* as a property of each vertex, which is what a partition is; `mem_decisions_iff` and `mem_utilities_iff` recover the `Finset` forms whenever `V` is a `Fintype`. **Def. 3 closed on 2026-08-22, having read `Same` wrongly for one day in between.** A CID carries no domains, so that axis was always absent here; the two that were present were `CID`'s own fields, and both are gone. `parents : V → Set V` is print's unbounded vertex subset. `acyclic` is now `∀ v, ¬ Relation.TransGen (` `· ∈ parents ·` `) v v` — no vertex reachable from itself, which is *"a directed acyclic graph"* and nothing more. **This is the only one of Definitions 1 to 5 that closes.** Definition 3 is a graph and evaluates nothing, so it needs no well-foundedness; that strengthening lives on `SCM` and `SCIM`, which do evaluate, and keeps those rows `Narrower` with the `chainParents` witness attached. `acyclic_of_rank` is in this column as the constructor a finite worked example uses. Under this section's stated convention the row also carries `decisions` / `utilities` / `structureNodes`, which are `Finset.univ.filter …` and need `[Fintype V]`; `IsDecision` and `IsUtility` are the unbounded forms and `mem_decisions_iff` / `mem_utilities_iff` are the bridge, so that part is a genuine relocation rather than a cut, but the two graph axes are not. Childlessness of utility nodes is a structure field with a worked counter-witness in the examples. |
| policy invariance off `Desc_D` (asserted after Def. 4) | *"We use `Pr^π` and `Eπ` to denote probabilities and expectations with respect to `Mπ`. For a set of variables `X` not in `Desc_D`, `Pr^π(x)` is independent of `π` and we simply write `Pr(x)`."* | `CID.IsDescendant`, `CID.NotDownstream`, `CID.not_isDecision_of_notDownstream`, `CID.notDownstream_of_mem_parents`, `SCM.eval_eq_of_f_agree`, `SCM.marginal`, `SCM.marginal_eq_sum_exo`, `SCIM.eval_withPolicy_eq_of_notDownstream`, `SCIM.marginal_withPolicy_eq_of_notDownstream`, `SCM.exoLaw`, `SCM.exoLaw_eq_pi`, `SCM.exoLaw_singleton`, `SCM.observableLaw`, `SCM.measurable_exo`, `SCIM.observableLaw_withPolicy_eq_of_notDownstream` | Yes | **Wider** | **New on 2026-08-22. This sentence had no row until then, and that is an inventory gap rather than a coverage one**: it is a printed assertion in the paragraph that introduces `Pr^π`, and this table's rule is that every printed claim gets a row whether or not the atlas covers it. It was missed because it sits in running prose between Definition 4 and Definition 5 rather than in a numbered environment. **Wider on two axes.** Print *asserts* it and proves nothing — the notation *"we simply write `Pr(x)`"* is well defined only if it holds — and the atlas proves it, which is one of this audit's six recognised widenings. And print writes `Desc_D` having already restricted to `𝐃 = {D}`, while `CID.NotDownstream` quantifies over every decision vertex, so the statement holds on the multi-decision diagrams where print states nothing; at print's own restriction it is print's condition exactly. **The third axis was Narrower and closed on 2026-09-14, by widening rather than by costing.** It read Narrower because `SCM.marginal` is a `Finset` sum over `Assignment V dom` carrying `[Fintype V]`, so print's sentence was carried only at a finite vertex set; the two `eval`-level declarations did not carry it — `eval_eq_of_f_agree` and `eval_withPolicy_eq_of_notDownstream` are `omit [Fintype V]` — but a row is graded on every declaration in its column. `SCIM.observableLaw_withPolicy_eq_of_notDownstream` now states print's sentence at an arbitrary vertex type and an arbitrary set of observables, through `SCM.exoLaw`: the independent exogenous draws as a product measure, which is a probability measure even where the assignment space is uncountable. **The finite case is recovered, not abandoned** — `SCM.exoLaw_eq_pi` and `SCM.exoLaw_singleton` identify it with the old joint weights, so the `Finset` statements are instances of the general one. **The price is named rather than hidden:** `SCM.observableLaw` takes a measurability hypothesis, because an arbitrary function of infinitely many parents need not be measurable. At print's own finite setting that hypothesis is free, discharged by `SCM.measurable_exo`, so nothing print asserts is bought with a condition print lacks. Inhabited at the law level on print's own figure by `figSCIM_observableLaw_opinion_policy_free`, and the product layer is inhabited outside the finite class by `Examples.Causal.StructuralModel.independentBits_first_zero` at countably many vertices. **`Desc_D` is read reflexively, on purpose.** The decision is its own descendant, so the invariance is not claimed at the decision; under a *proper* reading `D` would fall outside *Desc_D* and print's sentence would assert that `Pr^π(d)` does not depend on `π`, which is false. RE24's `Anc`/`Desc` **are** proper and `Model.properAncestors` / `Model.properDescendants` carry that reading — a different paper and a different sentence, and not a discrepancy to reconcile. **What the proof turns on.** `eval_eq_of_f_agree` is the content and says nothing about policies: two models with one parent map whose structural functions agree on an ancestor-closed set evaluate alike there. The complement of `Desc_𝐃` is such a set, and `Mπ` and `Mπ'` differ only at decision vertices. `marginal_eq_sum_exo` is what carries a statement about `W(ε)` to one about `Pr`, by summing `P(ε)` over the fibres of `eval` instead of summing the joint over assignments. Inhabited on print's own Figure 2a: `figCID_notDownstream_zero` puts the opinion outside `Desc_D` and `figSCIM_marginal_opinion_policy_free` is print's `Pr(x)` there |
| policy and optimal policy (asserted after Def. 4) | a policy is a structural function from the decision's observations together with an exogenous randomness variable to the decision; an optimal policy is any policy maximising expected utility | `SCIM.Policy`, `SCIM.withPolicy`, `SCIM.expectedUtility`, `SCIM.IsOptimalPolicy`, `SCIM.exists_isOptimalPolicy`, `SCIM.policy_ext_single`, `SCIM.isOptimalPolicy_iff_law`, `Examples.Causal.StructuralModel.figSCIM_isOptimalPolicyLaw_copy` | Yes | **Wider** | **This row has been regraded more than any other in the table, and the reason is the finding: the regrades turned on miscounts of the narrowing side rather than on new mathematics.** Two of the three narrowing halves really are gone. The vertex-set half closed when `SCIM` shed `[Fintype V]`: `Policy` is indexed by `{d // graph.IsDecision d}`, a subtype over a property, so the policy space is defined at unbounded `V`. The domain half was never the atlas's: this object is asserted **after** Def. 4, where *"finite-domain variables"* and *"finite-domain exogenous variables"* are print's own words, so `Fin (dom d)` and `Assignment V dom` transcribe print. What remains is the widening, which was disclosed all along: print writes a single `π` because it has *already* restricted to `𝐃 = {D}`, and the atlas carries one structural function per decision vertex, so it defines the object at multi-decision diagrams where print defines nothing. `policy_ext_single` proves that at print's own restriction the family is print's datum exactly. Indexing by the decision subtype rather than by a membership proof is what keeps `withPolicy` free of transports between `Fin (dom v)` and `Fin (dom d)`. `Eπ[U]` is taken **in `Mπ`**, which is where print defines `Eπ`, so it is print's definition rather than a formula that agrees with it. **What puts the row back to `Mixed` is the narrowing that was never counted.** `withPolicy` used to build an `SCM` from `M.graph.parents` and `M.graph.acyclic`, so every declaration in this row inherited `CID`'s finite indegree and ℕ-ranked acyclicity, which print's policy paragraph asks for neither of. **Both closed on 2026-08-22** and that half of the narrowing is gone: `withPolicy` now hands `SCM` print's own `CID.acyclic`, and `instIsWellFoundedWithPolicy` supplies the recursion's hypothesis from `CID.IsWellFounded` — a property of the diagram rather than a field of `SCIM`, which is what closed the Definition 4 row. `expectedUtility` additionally sums over `ExoAssignment V edom`, which is a `Fintype` only when `V` is — so the vertex-set constraint is still present in this row's operations even though it is gone from `SCIM` itself. **Sharpened 2026-08-22, and half of what this sentence used to say is withdrawn.** It also cited `exists_isOptimalPolicy` needing the policy type finite. That is not an axis: print writes `V*(M)` as a *maximum* and states no condition delivering one, so finiteness supplies print's own assertion rather than cutting below it, and the Definition 5 row has always graded it that way. What remains an axis is the summation alone — print's `P(ε)` denotes at unbounded `V` as a product measure and a `Finset` sum does not. The preamble adjudicates the instance's three jobs once and applies the result to this row and to Definition 5 together; **until that adjudication the two rows graded the identical hypothesis in opposite directions**, which is the finding rather than either verdict. Wider on the decision axis, narrower on the vertex-set axis: that is what `Mixed` is for, and it is still the honest grade. The triage predicted this row would go plainly `Wider` once the graph axes closed. That prediction was wrong, and it was wrong against information this row's own note already carried: it counted only the graph half of the narrowing. **`Causal.Decision`'s `Policy` keeps its own row and its own grade**: it is the unmediated projection of MAIS `def:cid`, an induced conditional law rather than a structural function, and nothing here widens it **The expectation layer was the one open axis and it closed on 2026-09-20.** `SCIM.isOptimalPolicy_iff_law` proves this row's *"maximises `Eπ[U]`"* is print's expectation and not a finite sum standing in for it, and `SCIM.IsOptimalPolicyLaw` states it at an unbounded vertex set, which is possible because optimality here is a comparison rather than an attainment claim — `exists_isOptimalPolicy` is the attainment and is job 1, adjudicated in the preamble as supplying print's own *max*. **With no narrowing axis left the row is `Wider`**, on the decision axis it has carried since it was written: print's policy paragraph is a single `π` under `𝐃 = {D}` and the atlas defines a family over the decision subtype, so it reaches multi-decision diagrams where print defines nothing, with `policy_ext_single` keeping that disclosed. It carries no narrowing and so is owed no state. |
| Def. 4 structural causal influence model | a CID with finite-domain variables whose utility domains are a subset of `ℝ`, one finite-domain exogenous variable per endogenous one, and structural functions on `𝐕 \ 𝐃` | `Causal.SCIM` | Yes | **Same** | **The `Fintype V` axis closed on 2026-08-21.** Across the whole paper *"finite"* occurs exactly twice, both inside Def. 4 and both qualifying **domains**; the vertex set is never bounded. `SCM`, `CID` and `SCIM` therefore no longer carry `[Fintype V]`: the constraint moved onto the derived operations that genuinely need it — the `Finset` accessors and the expectation layer. That relaxes the definition against its own previous form rather than adding a hypothesis to a theorem, so it moves the row toward print rather than away. `CID.IsDecision` and `CID.IsUtility` read print's *"the vertex set is partitioned into `X`, `D`, `U`"* as a property of each vertex, which is what a partition is; `mem_decisions_iff` and `mem_utilities_iff` recover the `Finset` forms whenever `V` is a `Fintype`. **Def. 4 does not close, and read `Same` twice on two different bad arguments.** Its own addition was always fine: the *domain* finiteness this definition introduces is print's own — *"a CID with finite-domain variables"*, *"finite-domain exogenous variables"* — so `dom edom : V → ℕ` transcribes print from here on and is **not** an axis at this row, which is the one point on which this section's grading is more forgiving than a naive one would be. The vertex-set axis is likewise gone, and what used to remain — Def. 3's finite indegree and ℕ-ranked acyclicity, inherited through `SCIM.graph` — closed with Def. 3. `F` is a function of a proof that the vertex is **not** a decision, which is `¬ IsDecision` rather than `Finset` non-membership. **Closed 2026-08-22 by axis E, and this time by moving Lean rather than prose.** What had kept it `Narrower` was `SCIM.graph_wellFounded`, a field asking the diagram's parent relation to be well-founded where `CID.acyclic` asks only for print's word. That field is **gone**. Definition 4 is where print first writes a model that gets **evaluated** — one definition later, `V*(M)` is the maximum of `Eπ[U]` over policies and runs `W(ε)` in `Mπ` — and that recursion determines a value exactly on well-founded diagrams, so the requirement is real; it is now `CID.IsWellFounded`, a **property of a diagram** that `expectedUtility`, `optimalValue` and `IsMaterial` each ask for, rather than a field of the tuple. `chainParents` and its three theorems keep their job as the witness that print's *"recursive application"* names nothing unique without it. **This row read `Same` twice before, on arguments rather than code** — once on a `Bridged` fidelity grade this table has no column for, once on a `provably not closable` label that confused *"`eval` cannot be totalised"* with *"the structure must carry the field"*. Neither is what closes it now: the class of tuples `SCIM` admits is print's class, which is what this table grades. **The two remaining fields print does not write in so many words, examined rather than assumed.** `SCIM.utilityValue_injective` is print's *"utility variable domains are a subset of `ℝ`"*: a subset of `ℝ` is exactly a set injected into `ℝ`, and the injection is the naming of the states, so this is a representation of print's clause with its own converting fact rather than an addition. `SCIM.dom_pos` asks every domain to be nonempty, which print does not write — and a tuple violating it has **no assignment at all**, so print's own Definition 1 assertion that `W(ε)` has a value is false there. It excludes exactly the tuples on which print's stated conditions cannot hold, which is not the same as excluding tuples that satisfy them; well-foundedness was the second kind, and that is why it had to move and this does not. |
| Def. 5 materiality | `V*(M)` is the maximum of `Eπ[U]` over policies, `M_{X↛D}` is `M` with the information link removed, and `X ∈ Pa_D` is material when `V*(M_{X↛D}) < V*(M)` | `SCIM.optimalValue`, `SCIM.removeInfoLink`, `SCIM.IsMaterial`, `SCIM.removeInfoLink_sub`, `SCIM.expectedUtilityLaw`, `SCIM.expectedUtilityLaw_eq`, `SCIM.IsOptimalPolicyLaw`, `SCIM.optimalValue_eq_sup'_law`, `Examples.Causal.StructuralModel.figSCIM_optimalValue_law` | Yes | **Same** | **Source-class narrowing**: `SCIM.optimalValue` and `SCIM.IsMaterial` are named nowhere outside this module and its examples. **Partly closed on 2026-08-21, and the part that closed is the part where the finiteness is print's own.** Print writes `V*(M)` as the maximum of `E_π[U]` over policies. Without a finite vertex set `U` is a sum over possibly infinitely many utility vertices that need not converge, and that maximum ranges over an infinite policy space and need not be **attained** — print writes a maximum, not a supremum, and states no condition delivering either. Finite `V` delivers both, so `optimalValue` as a `Finset.sup'` transcribes print's content instead of cutting below it; `exists_isOptimalPolicy` exhibits the attaining policy print presumes. `IsMaterial` now takes `IsDecision` rather than `Finset` membership. **That argument survives every pass, and from 2026-08-22 it is no longer the whole story.** It defends two of the three jobs `[Fintype V]` does here — the maximum being attained and the utility total converging — and says nothing about the third. `optimalValue` is a `Finset.sup'` **of** `expectedUtility`, which sums over `ExoAssignment V edom`; print's `P(ε)` denotes at unbounded `V` because mutual independence is a product measure, and a `Finset` sum does not. **So this row does carry the expectation layer's `[Fintype V]` as an axis**, exactly as the policy row two rows above has said all along — the two rows contradicted each other for as long as both existed, and the preamble now adjudicates it once. The consequence is that **this row does not close when well-foundedness does**: Definition 4's column is the structure alone, and this one's is not. **What kept the row `Narrower` until 2026-08-22 has now closed**: `removeInfoLink` and `optimalValue` are taken at a `SCIM` whose graph is a `CID`, and so used to inherit Def. 3's finite indegree and ℕ-ranked acyclicity. Neither survives — the parent map is a `Set` and the diagram's condition is print's own. `removeInfoLink` keeps both by `Subrelation.wf` and `Relation.TransGen.mono`, since deleting an information link only removes edges; `removeInfoLink_sub` is that one fact, used once for acyclicity and once for well-foundedness. **What kept the row `Narrower` here was Def. 4's field rather than anything this row adds**: `V*(M)` evaluates `Mπ`, so well-foundedness is what makes print's own maximum refer to a determinate quantity. **That axis closed on 2026-08-22**: `SCIM` no longer carries the field, `optimalValue` and `IsMaterial` ask for `CID.IsWellFounded` instead, and `instIsWellFoundedRemoveInfoLink` carries it across the deleted information link so print's inequality needs the hypothesis once rather than at each side. The hypothesis is not itself an axis, for the reason the preamble adjudicates: print's *"recursive application"* names nothing unique without it. **Unlike Definition 4, this row did not close when that axis did**, and the reason is the sentence above — Definition 4's column is the structure alone, this one's also holds `optimalValue` and `removeInfoLink`, so the expectation layer is graded here. **It read `Same` in an intermediate revision** on a fidelity grade this table has no column for. The classical `Fintype SCIM.Policy` instance the `Set` parent map forced changes no grade — it is the same finite policy space, decided classically.  **What closing the expectation layer would take, stated once here and referenced by the rows that share it**: the `Finset` sum over `ExoAssignment V edom` becomes an integral against a product measure over the exogenous family, so `Assignment` and `ExoAssignment` carry measurable structure, `jointProb` and `jointProb_sum` become that measure and its normalisation, and `expectedUtility`, `contextFiber` and `condExp` become integrals. Attainment does **not** come along: finite `V` currently supplies print's own *maximum* at `optimalValue`, so a supremum over an unbounded policy space needs an attainment argument print states no condition for, and that argument is the part this cost is not able to price from print. Scoped, not started. **That cost was paid on 2026-09-20, and the attainment fence it named turned out to be a line inside print's own sentence rather than a blocker.** `SCIM.expectedUtilityLaw` is `Eπ[U]` as an integral against `SCM.exoLaw` at an unbounded vertex set, and `SCIM.expectedUtilityLaw_eq` proves the finite sum computes it, so `optimalValue` is a maximum **of print's expectation** — `SCIM.optimalValue_eq_sup'_law` says exactly that, and it is why the `[Fintype V]` that remains on this column is doing only jobs 1 and 2, both of which the preamble adjudicates as making print's own sentences denote. The fence stands where it was put and is now a named object rather than a warning: `SCIM.IsOptimalPolicyLaw` is *"any policy that maximises `Eπ[U]`"* at an unbounded vertex set, because a comparison of expectations needs no attainment, while `SCIM.exists_isOptimalPolicy` is *a maximiser exists* and keeps the finite policy space print states no condition for. Splitting the sentence is what let the row close without pretending the attainment half had been settled. `contextFiber` and `condExp` are **not** in this column and did not come along either; they are Definition 17's, and the preamble says why they are a different axis. **The row is `Same`: no narrowing axis is left on it.** |
| Def. 6 d-separation | *"A path `p` is said to be d-separated by a set of nodes `Z` if and only if: 1. `p` contains a collider `X → W ← Y`, such that the middle node `W` is not in `Z` and no descendants of `W` are in `Z`, or 2. `p` contains a chain `X → W → Y` or fork `X ← W → Y` where `W` is in `Z`, or 3. one or both of the endpoints of `p` is in `Z`. A set `Z` is said to d-separate `X` from `Y` if and only if `Z` d-separates every path from a node in `X` to a node in `Y`"* | `CID.DSepPath`, `CID.dSepSet_iff_dSepPath`, `CID.dSepPath_iff_dSep`, `CID.Activated`, `CID.activated_of_mem`, `CID.not_activated_of_mem_parents`, `CID.IsActive`, `CID.not_blocked_iff_isActive`, `CID.DSepSet`, `CID.UAdj`, `CID.IsCollider`, `CID.IsChainOrFork`, `CID.IsWalk`, `CID.Blocked`, `CID.isChainOrFork_iff_not_isCollider`, `CID.blocked_collider_iff`, `CID.blocked_singleton_iff`, `CID.isWalk_singleton`, `CID.inter_subset_of_dSepSet`, `CID.dSepSet_iff_dSep`, `CID.not_blocked_iff`, `mem_bbZAncestors_iff`, `cidToDAG_uAdj`, `cidToDAG_isCollider`, `CID.DSep`, `CID.dSep_iff_bbReachable`, `CID.dSep_iff_causalean`, `CID.inter_subset_of_dSep`, `cidToDAG`, `cidToDAG_edge`, `hasActivePath_iff_not_disjoint`, `Examples.Causal.DSep.dSep_of_subset_conditioning`, `Examples.Causal.DSep.dSepSet_of_subset_conditioning`, `Examples.Causal.DSep.intChain`, `Examples.Causal.DSep.intChain_not_dSepSet`, `Examples.Causal.DSep.intChain_not_dSepPath`, `Examples.Causal.DSep.edgeCID_not_dSep_self` | Yes | **Same** | **Closed 2026-09-09, and the transcription above replaces a paraphrase.** The earlier text of this row was written from the surrounding prose and dropped the numbering; clause 3 in particular read as *"or an endpoint in `𝐙`"*, which is the right content but not the printed sentence. **Taken from a shared library and not rebuilt**: clauses 1 and 2 are `Causalean.DAG.IsActivePath`, whose collider condition is print's clause 1 negated and whose non-collider condition is clause 2 negated, and the Bayes-Ball computation of it is upstream's as well. What is built here is **clause 3, which upstream does not have**, and the equivalence carrying decidability. **The scope axis this row turns on is set overlap.** Upstream's `Causalean.DAG.dSep` puts `Disjoint X Y ∧ Disjoint X Z ∧ Disjoint Y Z` **inside the definition**, so it cannot be asked about overlapping sets at all; print's clause 3 answers instead of refusing, and print says so deliberately — footnote 5 reads *"Def. 6 defines d-separation for potentially overlapping sets"*. Grading upstream's predicate as Definition 6 would therefore have been **Narrower**, on an axis the source explicitly claims. `CID.DSep` removes `Z` from both endpoint sets, which is clause 3, and is `Same` as a result. **The difference is witnessed, not asserted**: `Examples.Causal.DSep.dSep_and_not_causalean_dSep` gives, at every diagram, a triple at which `CID.DSep` holds and `Causalean.DAG.dSep` fails, and `edgeCID_not_dSep` shows the definition is not vacuously true. `CID.dSep_iff_causalean` recovers upstream's predicate under the disjointness it assumes, so every upstream lemma about `Causalean.DAG.dSep` transfers by rewriting. **Clause 3 has two jobs and both are carried.** Against `Z` it removes `Z` from both endpoint sets. Against `X ∩ Y` it is the `Disjoint (X \ Z) (Y \ Z)` conjunct: for a shared node `x` the trivial path `[x]` runs from `X` to `Y`, clauses 1 and 2 are vacuous on it for want of a triple, and clause 3 blocks it exactly when `x ∈ Z`. **Print does not settle the length convention for the undirected paths of Definition 6** — *"of length at least zero"* is said of the *directed* notion on page 2 — and this is the reading the paper's own footnote forces: under the other one there is no path from `x` to itself, an unconditioned shared node would leave the sets d-separated, and footnote 5 would have no content at `X ∩ Y`. Upstream reads it the same way, which is why `CID.dSep_iff_causalean` needs only **two** disjointness hypotheses: `Disjoint X Y` is not assumed but shared, appearing as upstream's first conjunct and here as clause 3 on the trivial path. `edgeCID_not_dSep_self` and `edgeCID_dSep_self_of_conditioned` witness that pair, and `CID.inter_subset_of_dSep` is the sharpest corroboration: the classical side condition *"`X` d-separated from `Y` by `Z` implies `X ∩ Y ⊆ Z"*, normally imposed or left implicit, is **proved** here rather than assumed, and under the other reading it would be false. **One axis is open and named rather than closed**: `Causalean.DAG.IsActivePath` takes a `List V` with no `Nodup`, so it quantifies over *walks* where print says *path*. For a finite graph an active walk exists exactly when an active path does — the standard fact Bayes-Ball correctness already rests on — but it is formalized neither in this tree nor upstream, and since 2026-09-20 it is the only axis this row still carries. **Regraded Same to Narrower on 2026-09-10, on an axis this row never named, and that axis closed on 2026-09-20.** `AISafetyAtlas.Causal.DSep` opened its variable block with a `Fintype V` instance alongside decidable equality, and `CID.DSep` took its three arguments as `Finset V`, while print's Definition 6 quantifies over *a set of nodes* `Z` and a path in a graph whose vertex set it never bounds. That was a **reopened** axis rather than a new one: `LAND-CAUSAL-STRUCTURAL-001` records axis (i), finitely many variables, as CLOSED on 2026-08-21 -- `SCM`, `CID` and `SCIM` carry no `Fintype V` and the instance sits on the derived operations that need it -- and this module was a new derived operation that put it back. **It is off again, by the route this row named.** `CID.DSepSet` is Definition 6 on `Set V` at an unbounded carrier: `CID.UAdj` is the undirected edge, `CID.IsCollider` and `CID.IsChainOrFork` are the shapes clauses 1 and 2 name, `CID.IsWalk` is the path, `CID.Blocked` is the three clauses. Nothing in it asks for `[Fintype V]`; `[DecidableEq V]` stays because it is a parameter of `CID` itself and so is not an axis this definition could drop on its own. `CID.dSepSet_iff_dSep` proves the `Finset` predicate is what print's definition comes to on a finite carrier, so `CID.DSep` is the **computation** of Definition 6 rather than a second reading of it, and every consumer of it is a consumer of print's definition by rewriting along that lemma — which is the same shape Definition 1 used for `CID.decisions` and `CID.mem_decisions_iff` when its own vertex axis closed. `Examples.Causal.DSep.intChain` is the integer chain `Pa_n = {n-1}`, the diagram `chainParents_acyclic` is already stated for, and `Examples.Causal.DSep.intChain_not_dSepSet` answers Definition 6 on it in the negative — a diagram the Bayes-Ball half cannot be asked about at all, so the generality is exercised and not merely available. **Two findings came out of writing print's clauses rather than negating upstream's.** (i) Clause 1's *"the middle node `W` is not in `Z` and no descendants of `W` are in `Z`"* has a redundant first conjunct, because `CID.IsDescendant` is reflexive by design; `CID.blocked_collider_iff` is the collapse, and print's two conjuncts are transcribed anyway. (ii) Clause 2 is clause 1's complement **only because the diagram is acyclic**: a chain `X → W → Y` is also a collider when `Y → W` as well, which is a two-cycle. `CID.isChainOrFork_iff_not_isCollider` spends `CID.acyclic` on exactly that, and it is the step upstream's *"not a collider"* phrasing hides. The dependency decision, the fork it is pinned to and what it cost to measure are [`d-separation-build-or-depend.md`](d-separation-build-or-depend.md) §10. **The walk-versus-path axis closed on 2026-09-20 as well, and with it the row.** `CID.IsWalk` asks for no `p.Nodup`, so the statements above quantify over walks where print says *path*, and quantifying over more things makes the predicate hold of fewer triples — a narrowing, not a widening, and the last one this row carried. `CID.DSepPath` is print's word and `CID.dSepSet_iff_dSepPath` proves the two readings are the same predicate. One direction is free; the other is the splicing argument, and it is a theorem about print rather than a bookkeeping step. Delete the segment between two occurrences of a repeated vertex: exactly one triple of the result is new, and the case that is not immediate is where the repeated vertex `v` is unconditioned, unactivated, and a collider on the spliced path. Then neither old triple at `v` can be a collider, so `v` points forwards on both sides; `forward_of_not_activated` follows the deleted segment from `v` and reaches its far end with an edge pointing into `v`, which together with the spliced collider's other edge makes the far end's own triple a collider that the original path's activity forbids. `CID.Activated` is the predicate that argument pushes along an edge — `CID.not_activated_of_mem_parents` is the push — and `CID.not_blocked_iff_isActive` is Definition 6's clause 3 separated from clauses 1 and 2 so the splice can preserve them independently. Upstream supplied nothing: `Nodup` does not occur anywhere under `Causalean/Graph/`, so `Causalean.DAG.IsActivePath` is a walk predicate with no path counterpart, and the standard fact Bayes-Ball correctness rests on was not available to import. `Examples.Causal.DSep.intChain_not_dSepPath` answers print's own reading on a carrier that is not finite. **Both of this row's axes are now closed and the row is `Same`.** |
| Def. 7 nonrequisite observation | *"Let `U^D := 𝐔 ∩ Desc^D` be the utility nodes downstream of `D`. An observation `X ∈ Pa^D` in a single-decision CID `𝒢` is nonrequisite if `X ⊥ U^D \| Pa^D ∪ {D} \ {X}`. In this case, the edge `X → D` is also called nonrequisite. Otherwise `X` and `X → D` are requisite"* | `CID.IsNonrequisiteSet`, `CID.isNonrequisiteSet_iff_dSepPath`, `CID.utilityDescendantsSet`, `CID.requisiteContextSet`, `CID.isNonrequisiteSet_iff`, `CID.coe_utilityDescendants`, `CID.coe_requisiteContext`, `CID.not_mem_requisiteContextSet`, `CID.IsNonrequisite`, `CID.IsRequisite`, `CID.utilityDescendants`, `CID.requisiteContext`, `CID.parentsFinset`, `CID.isNonrequisite_or_isRequisite`, `CID.requisite_sets_pairwise_disjoint`, `CID.isNonrequisite_of_utilityDescendants_eq_empty` | Yes | **Wider** | **Closed 2026-09-09**, the same day Definition 6 was, and it is d-separation at one conditioning set with no new separation argument. **Wider on two axes, both of them print's phrasing restricting the word rather than the condition.** (i) Print says *"an observation `X ∈ Pa^D` ... is nonrequisite if"*, which says what the term is being defined for; `CID.IsNonrequisite` takes an arbitrary vertex and asserts nothing about membership, and the lemmas that need `X` to be an observation take it as a hypothesis. The displayed condition is well-formed at any `X` because print writes the conditioning set with the removal already performed. (ii) Print says *"in a single-decision CID"*; nothing in the condition mentions a second decision and `Desc^D`, `𝐔` and `Pa^D` are defined at any diagram, so the hypothesis is absent. **One lemma does need `D` to be a decision, and the reason is a fact about print's own setup**: `𝐔` is childless but nothing stops a utility node from having *parents*, so at an arbitrary `D` the diagram may make `D` itself a utility node, which then lies in `U^D` reflexively and in its own conditioning set. `CID.requisite_sets_pairwise_disjoint` therefore assumes `IsDecision D` — strictly weaker than print's single-decision hypothesis — and establishes that at a genuine decision the three sets are pairwise disjoint, so Definition 7 does **not** exercise the overlapping-set generality Definition 6 is stated at. **Regraded Wider to Mixed on 2026-09-10.** The two widenings above are real and unchanged; what the row did not carry is that `AISafetyAtlas.Causal.Requisite` opens its variable block with the same `Fintype V` instance, that `CID.parentsFinset` is a `Finset.univ` filter and so needs it, and that the condition is `CID.DSep`, which narrows for the reason on the Definition 6 row above. Wider on two axes print restricts by phrasing and narrower on the vertex set is exactly what `Mixed` is for. **That vertex-set axis closed on 2026-09-20, and the row does not.** `CID.IsNonrequisiteSet` is Definition 7 on `Set V` at an unbounded carrier — `CID.utilityDescendantsSet` for `U^D`, `CID.requisiteContextSet` for `Pa^D ∪ {D} \ {X}`, and `CID.DSepSet` for the condition — and `CID.isNonrequisiteSet_iff` proves the `Finset` form is what it comes to on a finite carrier, so `CID.parentsFinset` and the rest are the computation rather than the definition. Every result on the row transfers along that lemma, and `Examples.Causal.Requisite.predictCID_not_isNonrequisiteSet` and `Examples.Causal.Requisite.unscoredCID_isNonrequisiteSet` are the two existing witnesses restated under print's own definition. What the row inherited from Definition 6 after that was the **walk-versus-path** axis and nothing else, and **that closed on 2026-09-20 too**, by `CID.dSepSet_iff_dSepPath` on the row above — `CID.isNonrequisiteSet_iff_dSepPath` is Definition 7 under print's own word, and `Examples.Causal.Requisite.predictCID_not_dSepPath` answers it at the diagram where the observation is requisite. **With no narrowing axis left, the row is `Wider` rather than `Mixed`**, on the two axes print restricts by phrasing and that this note has named since 2026-09-09. It carries no narrowing and so is owed no state. |
| Def. 8 value of information | `X ∈ 𝐕 \ Desc^D` has VoI in `𝓜` when it is material in `𝓜_{X→D}`, the model with the edge `X → D` added; a CID *admits* VoI for `X` when some compatible SCIM has it | — | No | — | New row 2026-09-09. `SCIM.IsMaterial` is the predicate this is stated over and exists; what is missing is edge **addition** (the atlas has `removeInfoLink`, not its converse) and the `admits` quantifier over compatible SCIMs |
| Thm. 9 value-of-information criterion | *"A single decision CID `𝒢` admits VoI for `X ∈ 𝐕 \ Desc^D` if and only if `X` is a requisite observation in `𝒢_{X→D}`, the graph obtained by adding `X → D` to `𝒢`"* | — | No | — | **Note corrected 2026-09-09.** It read *"requires the diagram as an object with decision and utility vertices"*; that object is `Causal.SCIM`, which has existed since 2026-08-22, so the note was stale by a fortnight. What blocks it is Definition 7, hence Definition 6: **requisiteness is d-separation**. Also missing: edge addition, and the `admits` quantifier. Soundness is their Lemma 26, completeness their Lemma 27, which defers to Theorem 12's construction |
| Def. 10 response incentive | a policy *responds* to `X` when some `do(X = x)` and some `𝓔 = ε` give `D_x(ε) ≠ D(ε)`; `X` has a response incentive when all optimal policies respond to it | — | No | — | New row 2026-09-09. Every piece is present — `SCM.submodel` is `do(X = x)`, `SCM.eval` is `·(ε)`, `SCIM.IsOptimalPolicy` is the quantifier — so this is a definition the atlas could state today, and the theorem it feeds (12) is what needs d-separation |
| Def. 11 minimal reduction | `𝒢^min` is `𝒢` with every information link from a nonrequisite observation removed | — | No | — | New row 2026-09-09. `SCIM.removeInfoLink` is the single-edge operation; what is missing is Definition 7, which decides *which* edges |
| Thm. 12 response incentive criterion | *"A single-decision CID `𝒢` admits a response incentive on `X ∈ 𝐗` if and only if the minimal reduction `𝒢^min` has a directed path `X ⇢ D`"* | — | No | — | **New row 2026-09-09, and its absence was the table's worst omission in this section**: this is one of the paper's four sound-and-complete graphical criteria, and the table listed Theorem 14 in its place. Needs d-separation through Definition 11, plus their Lemma 25. Completeness is their Lemma 28, the heaviest construction in the paper |
| Def. 13 counterfactual fairness | `π` is counterfactually fair w.r.t. `A` when `Pr_π(D_{a′} = d \| pa^D, a) = Pr_π(D = d \| pa^D, a)` for every `d`, every context, and every pair `a, a′` with `Pr(pa^D, a) > 0` | — | No | — | New row 2026-09-09. Not an incentive concept; it is the left-hand side of Theorem 14. Needs conditional probability given a decision context, which the atlas does not yet have |
| Thm. 14 counterfactual fairness and response incentives | *"In a single-decision SCIM `𝓜` with a sensitive attribute `A ∈ 𝐗`, all optimal policies `π*` are counterfactually unfair with respect to `A` if and only if `A` has a response incentive"* | — | No | — | **Note corrected 2026-09-09, and it was wrong in both halves.** It called this *"a graphical characterisation"* and listed **d-separation** among what is missing. Neither is right: this is stated at a **fixed** SCIM, not at *"a CID admits …"*, it carries no graph condition at all, and its proof (their §C.5) is manipulation of the support of the decision's policy-induced law in a fixed context, plus finiteness of `dom(D)`. It is the one result among the five here that d-separation would not help. What it needs is Definitions 10 and 13. The ancestor condition the surrounding prose mentions is cited to Kusner et al., not proved here |
| Def. 15 value of control | `X` has positive value of control when the maximum of `𝔼_π[𝒰]` over policies is **strictly less** than the maximum of `𝔼_π[𝒰_{g^X}]` taken over policies *and* soft interventions `g^X` at `X` | — | No | — | New row 2026-09-09. `SCM.softIntervention` and `SCIM.optimalValue` are both present; the maximum over pairs of a policy and an intervention is not. Read from a 400 dpi render: the relation is strict `<`, and the right-hand maximum ranges over both arguments |
| Thm. 16 value-of-control criterion | *"A single-decision CID `𝒢` admits positive value of control for a node `X ∈ 𝐕 \ {D}` if and only if there is a directed path `X ⇢ 𝐔` in the minimal reduction `𝒢^min`"* | — | No | — | **Note corrected 2026-09-09**, which said *"same missing object as Theorem 9"* — the object exists. Blocked on Definition 11, hence 6, and on their Lemma 23 (Correa & Bareinboim's sigma-calculus Rule 3) and Lemma 25. Note `𝐕 \ {D}`, which Theorem 18 deliberately does not carry |
| Def. 17 instrumental control incentive | there is an ICI on `X` in decision context `pa^D` when, for all optimal `π*`, `𝔼_{π*}[𝒰_{X_d} \| pa^D] ≠ 𝔼_{π*}[𝒰 \| pa^D]`; a CID *admits* one when some compatible SCIM has one for some context | `SCIM.HasICIAt`, `SCIM.HasICI`, `CID.AdmitsICI`, `SCIM.totalUtilityIn`, `SCIM.totalUtilityIn_congr`, `SCIM.expectedUtility_eq_sum`, `SCIM.point`, `SCIM.responseTo`, `SCIM.nestedUtility`, `SCIM.contextFiber`, `SCIM.condExp`, `SCIM.condExp_congr` | Yes | **Mixed** | **New row and formalized on 2026-09-09**, so this row has never carried a `No`. **Two readings print leaves open, both settled against print's own proof rather than by preference.** (i) The displayed inequality contains a free `d` and print quantifies it nowhere on the page; the `∀d` reading makes Theorem 18 **false**, because print's own completeness witness gives `𝒰_{X_d} = d` and the inequality fails at `d = 1`. `HasICIAt` reads `∃ d`, inside the policy quantifier, and the docstring carries that argument. (ii) Print conditions on `pa^D` without the positivity side condition its Definition 13 states explicitly for the analogous conditioning; `condExp` is a quotient, division by zero is zero, so both sides collapse and `HasICIAt` is **false** on a null context. That is the conservative direction and no theorem here depends on it: soundness is proved pointwise in `ε` and never divides, and print's completeness context has probability one. **Wider on the decision axis, and on two counts rather than one.** Print says *"in a single-decision SCIM"*, while `HasICIAt` takes the decision vertex as an argument and is defined at any SCIM, so it says something on the multi-decision diagrams where print says nothing — the same widening the policy row above carries for the same reason. And the vertex it takes need not be a **decision** at all: print's `pa^D` presumes one, the atlas requires nothing of it, and `not_hasICI_of_not_pathThrough` is therefore proved at an arbitrary pair of vertices. At print's own restriction it is print's condition exactly. **Narrower on the expectation layer**, which this section's preamble adjudicates and which Definition 5 carries too: `contextFiber` and `condExp` are `Finset` sums over `ExoAssignment V edom`, a `Fintype` only when `V` is, while print's `P(ε)` denotes at unbounded `V` as a product measure. Wider on one axis and narrower on another is what `Mixed` is for. The atlas additionally proves a **strictly stronger** statement of the same shape at the witness: `SCIM.iciWitness_forall_policy` gives the inequality against *every* policy rather than only the optimal ones, and `HasICI` follows from it — so Definition 17's own quantifier is transcribed while the stronger fact is available to any consumer that wants it. `totalUtilityIn` is `expectedUtility`'s inner sum given a name, because Definition 17 compares two **different** models at the same `ε` and `expectedUtility` writes that sum inline; `expectedUtility_eq_sum` is the `rfl` proving nothing moved. `responseTo` and `nestedUtility` are print's nested potential response `𝒰_{X_d}(ε) := 𝒰_x(ε)` at `x = X_d(ε)`, two composed `submodel`s, with the policy fixed first as print requires **The domain instances on this row's declarations are print's Definition 4, not this section's.** `AISafetyAtlas.Causal.Incentive` carries finiteness and decidability on the domains from 2026-09-20, when Definition 1's domains became a family of types; print writes *"finite-domain variables"* at Definition 4 and Definition 17 lives downstream of it, so those instances transcribe print rather than adding to it. **The narrowing axis is conditioning, and since 2026-09-20 it is not the expectation layer's.** That layer closed at Definition 5; `SCIM.HasICIAt` keeps a `[Fintype V]` anyway, because `SCIM.condExp` is a ratio of two sums over `SCIM.contextFiber`, a filtered `Finset.univ`. **Narrowing state: open, costed.** Generalising it is not a transcription job, and the reason is a fact about print: `E_{π*}[· \| pa^D]` conditions on the event `Pa^D = pa^D`, and once `Pa^D` may be infinite — which Definition 3 permits and this section's finite-indegree closure of 2026-08-22 made real — that event can be null under `SCM.exoLaw`, where print's conditional expectation names nothing. Print writes `Pr(pa^D, a) > 0` at Definition 13, on the same `pa^D`, four definitions earlier, and writes no condition here — so the silence is against a precedent print set itself, which is why it is a question rather than an oversight. **Half of this cost was ruled on 2026-09-21 and the cell is still open.** The cost was a conditional expectation given a σ-algebra **plus** a reading of Definition 17 that print does not supply, and the second half was the part this cost could not price from print. The maintainer ruled the reading: **a null decision context carries no incentive** — the convention the tree already had, now a decision of record rather than a default, on two grounds. It is the conservative direction for an incentive predicate, a false *"no incentive"* being a missed warning where a false *"incentive"* is a warning about nothing; and it is the only candidate reading that does not decide for print something print declined to write. So the remaining cost is the measure-theoretic conditional expectation and nothing interpretive, and for the first time it is fully priceable. **This does not close the cell**, and the grade does not move: the narrowing is `SCIM.condExp`'s `[Fintype V]`, the ruling removes no `Fintype` from any signature, and no statement here holds at unbounded `V` that did not before. Scoped, not started. |
| Thm. 18 instrumental control incentive criterion | *"A single-decision CID `𝒢` admits an instrumental control incentive on `X ∈ 𝐕` if and only if `𝒢` has a directed path from the decision `D` to a utility node `U ∈ 𝐔` that passes through `X`, i.e. a directed path `D ⇢ X ⇢ 𝐔`"* | `CID.admitsICI_iff`, `CID.AdmitsICI`, `SCIM.PathThrough`, `SCIM.not_hasICI_of_not_pathThrough`, `SCIM.nestedUtility_eq_of_not_pathThrough`, `SCM.eval_submodel_singleton_of_not_reaches`, `SCM.eval_submodel_singleton_of_eq`, `SCIM.iciWitness`, `SCIM.iciWitness_hasICI`, `SCIM.seg_propagate`, `SCIM.seg1_eval`, `SCIM.seg2_eval` | Yes | **Mixed** | **Closed 2026-09-09, both directions.** The note this replaces read *"a directed-path condition through the decision"* and deferred to Theorem 9's reason, and both halves of that were wrong: the path runs **from** the decision **through `X`**, and it is a path in `𝒢` rather than in `𝒢^min`, so **this row needed no d-separation** — the only one of the four that did not. **Wider on three axes, all of them print's single-decision restriction coming apart.** Print states Theorem 18 for a single-decision CID and proves both halves under that; neither half needs it in that form. (i) **Soundness needs no hypothesis at all**: `not_admitsICI_of_not_pathThrough` holds at every diagram, any number of decisions, and does not ask that `D` be a decision vertex. (ii) **Completeness needs `CID.DecisionFree`**, not single-decision: no decision *other than `D`* on either segment or among `Pa^D`. Other decisions elsewhere are admitted, and again `D` itself need not be a decision — the witness gives it a structural function when it is not. `admitsICI_iff_of_decisionFree` is the equivalence at that hypothesis, and `Examples.Causal.Incentive.twoDecisionCID_admitsICI_on_X` decides a **two-decision** diagram, which is the witness that the hypothesis is weaker than print's rather than a restatement of it. (iii) **The evaluability class is not a hypothesis of either.** It was, and it did not have to be: `CID.isWellFounded_of_fintype` derives it from `CID.acyclic` at any `[Fintype V]`, which every statement in this column already carries. `admitsICI_iff` is print's own statement, recovered as the corollary at `decisionFree_of_singleDecision`. **`DecisionFree` is not slack left in the proof, and its first clause is witnessed rather than argued.** Both clauses exclude a stray decision that breaks the construction by making a *deviating policy optimal* — a decision on a segment can play a constant and flatten the utility, a decision in `Pa^D` can move the context Definition 17 fixes — so this is a fact about Definition 17 and not about this development. `Examples.Causal.Incentive.segSCIM_not_hasICI` proves the first: a diagram `D → D' → X → U` with `D'` a second decision on the near segment carries the path in full, and a compatible SCIM over it has **no** incentive on `X`, under a policy `segConstPolicy_optimal` proves optimal. What that does **not** establish is that the criterion fails there — `¬ AdmitsICI` quantifies over every compatible SCIM and this is one — and that question is open and recorded as open. The second clause has no such witness and is argued only. **The redundancy first recorded here as an open question is closed.** `CID.isWellFounded_of_fintype` proves it — `Finite.wellFounded_of_trans_of_irrefl` on the transitive closure, whose irreflexivity is exactly `CID.acyclic` — and both statements in this column now go without the hypothesis. It is a **theorem and deliberately not an instance**: as an instance it would let `[Fintype V]` discharge every evaluability goal in the tree silently, which would hide the axis at the declarations graded on it. The same redundancy does sit on `expectedUtility`, `optimalValue` and `IsMaterial`; removing it there is a change to Definition 1's layer and is not made here. **Narrower on the expectation layer**, inherited from Definition 17's row and adjudicated in this section's preamble. **The reflexive reading is print's and is load-bearing.** Definition 3 makes a directed path *"of length at least zero"* and Theorem 18 quantifies `X ∈ 𝐕`, deliberately against Theorem 16's `X ∈ 𝐕 \ {D}` one page earlier, so `X = D` and `X ∈ 𝐔` are inside the criterion; `CID.IsDescendant` is that relation and `Model.properDescendants` would state a different and false theorem. Soundness consumes print's Lemma 20 at an empty conditioning set (`eval_submodel_singleton_of_not_reaches`) plus a consistency step print leaves implicit (`eval_submodel_singleton_of_eq`): when the forced value is the factual one, forcing changes nothing. **Completeness departs from print's proof and is graded on the statement, not the route.** Print fixes a path and makes each vertex copy its predecessor; `iciWitness` copies along *two reachability segments* split at `X`, which needs no path extraction, no `Chain` and no `Nodup`. The split is not cosmetic: copying along a single segment would let a bypass `D → Y → U` carry the decision's value past `X`, forcing `X` would change nothing, and the construction would fail. `iciWitness` also proves **more than print's**, and needs less: print derives the incentive from its model's unique optimal policy, while `SCIM.iciWitness_forall_policy` exhibits, at **every** policy, a counterfactual decision disagreeing with what that policy plays, and `iciWitness_hasICI` is its corollary at the optimal ones — so which policies are optimal is never settled, and the `∃ d` reading of Definition 17 is exactly what that stronger form needs **Narrowing state: open, costed.** Inherited from Definition 17, and costed on that row above — which as of 2026-09-20 is the conditioning axis and no longer the expectation layer's, that having closed at Definition 5. The 2026-09-21 ruling on the null-context reading is recorded there and applies here unchanged: it makes the remaining cost purely mechanical and closes nothing, because the narrowing on both rows is `SCIM.condExp`'s `[Fintype V]` and the ruling does not remove it. |
| — | zero regret characterised, and the optimum attained without a diagram | `Model.regret_decomp`, `Model.regret_eq_zero_iff`, `Model.bestDecision` | — | **Beyond** | the printed source defines regret and reasons about optima; the fibrewise-argmax characterisation, with ties left unconstrained, is proved here and not stated there |

**11 Yes, 0 Partial, 9 No, 1 Beyond**, recounted 2026-09-09 after Definitions 6 and 7 closed; the figure is a recount of the rows above, not the previous tally adjusted. The paragraph below
was written at `4 No` and the recount that follows it says what changed and why
no coverage moved.

The `7 Yes` was up from `6 Yes` on 2026-08-22 — not
because anything was proved that was previously missing from this table, but
because a printed sentence was missing **from the table**. Print's *"for a set
of variables `X` not in `Desc_D`, `Pr^π(x)` is independent of `π`"* sits in
running prose between Definitions 4 and 5, and every earlier pass over this
source enumerated the numbered environments. It now has a row, and the atlas
proves it. The setup is formalized and the results
are not.

**What the recount changed.** Nine rows were added
and four notes corrected, and none of it is new mathematics — it is print,
transcribed at last. The count of `No` rows more than tripled because the table listed
four of this source's numbered results, omitted a fifth, and omitted the eight
definitions all five are stated over, which is exactly the inventory gap the `Desc_D` row above
records for the paragraph between Definitions 4 and 5. Two passes caught the
prose and neither caught the vocabulary.

~~What is absent is **d-separation** — Definition 6, a path algebra the atlas
has no counterpart for — and the incentive concepts themselves.~~ **That
sentence is retracted and is left visible.** It is right about Theorems 9, 12
and 16 and wrong about the other two, and the correction is what made the next
increment tractable rather than blocked:

* **Theorem 18 needed no d-separation, and is now proved** — both directions,
  on 2026-09-09, the same day the correction was made. Its criterion is a
  directed path in `𝒢` itself — reflexive, over `𝐕` rather than `𝐕 \ {D}` —
  and `CID.IsDescendant` was already that relation. Soundness reads one imported
  lemma; completeness is `SCIM.iciWitness`.
* **Theorem 14 needs no graph object at all.** It is an equivalence at a fixed
  SCIM between counterfactual unfairness and a response incentive; d-separation
  would not advance it by a line.
* **Theorem 12 was missing from the table**, and it — not Theorem 14 — is the
  response-incentive criterion and the third genuine consumer of d-separation.

So the blocked set is smaller and better identified than *"the incentive
theorems"*: **Definitions 6, 7 and 11 gate Theorems 9, 12 and 16**, and nothing
gated Theorem 18 except writing it. The remaining *completeness* halves are
still constructions of witnessing SCIMs rather than derivations, which is a
second layer on this one and not a continuation of it — and Theorem 18's, now
written, is the evidence that the layer is reachable rather than the reason to
defer: `iciWitness` is one structure, one induction and three evaluations.
[`d-separation-build-or-depend.md`](d-separation-build-or-depend.md) §7 carries
the per-theorem table these bullets summarise, together with the re-costed
depend-or-vendor comparison the corrected reading forced.

Assumption 1 remains a scope fence in this formalization rather than a
hypothesis — `Causal.Decision` *is* the unmediated projection, and `Causal.SCIM`
is a separate object no statement in that module is phrased over — which is why
there is no declaration stating it. **Nothing here re-grades section 6.**
Richens & Everitt's §2.2 value and regret are the unmediated projection, and
section 6 grades them `Same` since 2026-09-20 through `Causal.DecisionNetwork`,
not through this section's objects: wiring `Model.value` to a SCIM's decision
vertex is still a construction nobody has written.

**Two ingredient sources are deliberately ungraded.** Uhler, Raskutti, Bühlmann
& Yu 2013 and Meek 1995 motivate replacing a measure-zero exception with an
explicit margin, and are cited for that role in
`mais-a2-causal-collision.md`. No atlas declaration transcribes a statement from
either: strong faithfulness bounds a partial correlation, and the six margin
conditions bound CPT entries and utility gaps. Grading them would produce a
section of `No` rows resting on a single sentence, so they are recorded here
instead of tabulated.

---

## 9. Everitt, Krakovna, Orseau, Hutter & Legg 2017, arXiv:1705.08417v2 → `AISafetyAtlas.Wireheading.CRMDP`

Graded for the first time on 2026-09-09. The wireheading cluster had been
outside this ledger entirely: seven modules, four registry rows, and no row in
this table. Sections 9 to 12 close that.

**Which text.** The pinned file is the **long version**, arXiv:1705.08417v2,
19 Aug 2017, 24 pp., sha256
`68ed8a0dcadc93d5d494538d666cb09c428b7b81a1e8ff681a8d5f6fce153dad`, manifested
 2026-09-09 in the literature directory. The atlas's
modules cite "IJCAI 2017; long version arXiv:1705.08417"; the IJCAI proceedings
paper has **not** been read, and no claim is made here that the two number
their statements alike.

**Three axes run through every row and are not repeated in each note.**

* **Randomness, in the dynamics and in the agent.** Print's Definition 7 gives a
  transition function `T(s' ∣ s, a)`, a stochastic kernel; print's equation (1)
  draws the action from a factor *P(π(ĥ) = a)*, so its policy may randomise too;
  and Definition 10's return is an expectation `E` over the process those two
  induce. The atlas `Model.transition` is `State → Action → State` and
  `returnOver` is a bare `Finset` sum with no measure anywhere, so everything
  `AISafetyAtlas.Wireheading.CRMDP` alone proves about the complement
  construction is the degenerate case of print's. **Both halves of that gap are
  now closed elsewhere in the cluster**, and a row is graded against the widest
  rendering it cites: `AISafetyAtlas.Wireheading.StochasticCRMDP` makes the
  transition a `PMF` and the return an expectation, and
  `AISafetyAtlas.Wireheading.StochasticPolicy` makes the policy a `PMF`-valued
  function of the observed history, which is print's *P(π(ĥ) = a)* exactly. A
  row citing `AISafetyAtlas.Wireheading.CRMDP` declarations alone is still graded
  against the deterministic shadow.
* **Two carriers, and only one of them is print's.** Theorem 11 fixes
  `R = {r₁, …, rₙ}`, a **uniform** discretisation of `[0,1]` with `r₁ = 0` and
  `rₙ = 1`. Uniformity is load-bearing and not decoration: it is what makes
  `x ↦ 1 - x` map the grid to itself, so that the complement of a member of the
  hypothesis class is a member. `CRMDP.Reward` is `Set.Icc 0 1`, which is closed
  under the same involution — so the argument survives there — but `Env State`
  is then the full product of two *continuum* function spaces, and print's
  finite class is a proper subclass of it. `AISafetyAtlas.Wireheading.RewardGrid`
  supplies print's carrier: `GridEnv` is the full product of functions into the
  grid, `gridVal_gridRev` is the closure fact, and `gridVal_zero`,
  `gridVal_last` and `gridVal_strictMono` are the rest of the printed sentence.
  Rows citing `CRMDP` declarations alone are graded against the interval
  carrier; rows citing a declaration of `AISafetyAtlas.Wireheading.RewardGrid` are graded
  against print's.
* **The three extrema are hypotheses in one module and theorems in the other.**
  The `CRMDP.Model` fields *bestPolicy*, *worstEnvironment* and *worstPolicy*
  are supplied, with their optimality as further fields. Print derives all three
  from finiteness of `S`, `A` and `R`: with finitely many states, actions and
  rewards and a finite horizon there are finitely many achievable returns, so
  every `max` and `min` in its equations (4) and (5) is attained. **That
  derivation is now carried out**, in `AISafetyAtlas.Wireheading.RewardGrid`: `historyUpTo_length`,
  `stateAt_eq_seqState`, `stateAt_seqPolicy` and `seqState_congr` reduce a
  horizon-`t` return to a function of `Fin t → Action`, so
  `exists_max_gridReturn` and `exists_min_gridReturn` attain the extrema over
  the **whole policy function space**, and finiteness of `GridEnv` attains them
  over the class. `toComplementedClass` therefore discharges every field rather
  than supplying any.

**What the atlas does have that print's proof needs.** The complement
construction is verified rather than assumed: `Env.observed_complement` proves
the indistinguishability step and `return_add_complement` proves equation (3),
both from the definitions rather than as class hypotheses. That is why the
Coverage column is not uniformly `No` on the proof steps.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Ex. 1 | reward misspecification: a boat-racing agent scores by looping | — | No | — | an informal scenario, argued only in prose. Nothing in the atlas represents a particular task |
| Ex. 2 | sensory error: a robot short-circuits its reward in the shower | — | No | — | as above. It is the scenario Definition 7's corruption function is designed around, and the corruption function *is* formalized — but the example itself asserts nothing checkable |
| Ex. 3 | wireheading: an agent hijacks its reward channel | — | No | — | as above |
| Ex. 4 | CIRL misinterpretation | — | No | — | as above; CIRL is not modelled anywhere in the atlas |
| Def. 5 | the reward corruption problem: learn to optimise the true reward while observing only the corrupt one | — | No | — | a statement of the problem, not of a proposition. The atlas has no learning layer at all — no belief over environments, no time-indexed agent — so there is nothing to grade it against |
| Def. 6 | dot for the true signal, hat for the observed one, over one reward set | `Env`, `Env.observed` | Yes | Same | notation, and the object rule says notation need not be mirrored; it is graded because the *distinction* is what the whole paper turns on, and the two fields carry it. One reward type serves both, as print's `R` does |
| Def. 7 | a CRMDP is a tuple of finite state, action and reward sets, a transition function, a true reward function and a corruption function | `Model`, `Env`, `Env.observed`, `RewardGrid.GridEnv`, `RewardGrid.gridVal`, `StochModel`, `stochRun` | Partial | **Wider** | the tuple is present and the corruption function is exactly print's `C(s, ṙ)` curried. `GridEnv` carries print's finite reward set; the `Fintype` instance on it is print's finiteness of `S` and `R`. Wider in that `State` and `Action` are arbitrary types where print requires finite ones, so a statement not needing finiteness is proved without it. Regraded from `Mixed` on 2026-09-18. The one narrowing this row carried was the transition: a function where print's is a kernel. The atlas has print's kernel and has had it since 2026-09-10 -- `StochModel` carries an `mdp` field whose transition is distribution-valued, and `stochRun` is the trajectory distribution it induces, which at print's finite state set is print's `T` exactly. The row named only the deterministic rendering, so the narrowing was in the cell and not in the tree; the Thm. 11 row below already said so in its clause *(c)*. Nothing moved but the names |
| Def. 8 | the observed reward function is the corruption of the true one | `Env.observed` | Yes | Same | `Env.observed` unfolds to the corruption channel applied to the true reward at the same state, which is print's `R̂(s) = C_s(Ṙ(s))` on the nose |
| eq. (1) | the interaction of a possibly stochastic policy with a CRMDP induces a measure over histories | `mixedRun`, `mixedHistoryUpTo`, `mixedStateAt`, `mixedHistoryUpTo_ofDet`, `stochRun`, `stochHistoryUpTo`, `run`, `historyUpTo` | Yes | **Wider** | closed 2026-09-10 at print's own quantifiers. `mixedRun` draws the action out of the policy's distribution at the history so far and the successor state out of the transition, which is print's product term *P(π(ĥᵢ₋₁) = aᵢ) · T(sᵢ ∣ sᵢ₋₁, aᵢ)* — the agent's randomness and the environment's, in print's own order. Print's remaining factor *P(Ṙ(sᵢ) = ṙᵢ, R̂(sᵢ) = r̂ᵢ)* is a point mass **at print's own Definition 7**, where the true reward is a function `Ṙ : S → Ṙ` and Definition 8 makes the observed reward `Cₛ(Ṙ(s))`; the atlas records `(s, μ.observed s)` at each step for exactly that reason. `mixedHistoryUpTo_ofDet` recovers the deterministic-policy case and `stochHistoryUpTo_ofDet` the deterministic-transition one, so nothing earlier is lost. **Two things this row does not claim.** The product *display* is not stated as a proved equation: the distribution is built by the recursion that product unfolds, which is how print introduces the measure in the first place, but no theorem here reads the mass of a given history off as that product. And the object is over **observed** histories *ĥ*, not print's *h*: the true-reward coordinate of *h* is a function of a state the observed history already carries, so no information is dropped, but the two are not literally the same tuple. `Wider` because `State` and `Action` are arbitrary types where print requires finite ones — and at a finite state set a `PMF` is print's kernel exactly, so print's instances are all covered |
| Def. 9 | for given sets of transition, reward and corruption functions, the CRMDP class is the family of tuples drawn from their product | `Env`, `Model`, `RewardGrid.GridEnv`, `RewardGrid.GridEnv.complement`, `RewardGrid.FullEnv`, `RewardGrid.FullEnv.complement`, `RewardGrid.FullEnv.complement_involutive`, `RewardGrid.fullReturn`, `RewardGrid.fullReturn_add_complement`, `RewardGrid.toFullComplementedClass`, `RewardGrid.everitt_theorem_eleven_fullClass` | Yes | Same | **Closed 2026-09-19; the row was `Partial`/`Narrower` until then.** `GridEnv m State` is the full product of the two function spaces at print's own reward set, which is print's class when those two sets are "all functions" — so completeness needs no hypothesis: `GridEnv.complement` lands in the class by construction. **What was narrower was the `T`-component.** `toComplementedClass` shares one transition across the class, so print's product over transition functions was a singleton, and the fibre argument does **not** repair that: `worstCaseRegret` is a maximum over the class, a maximum over a larger class is larger, and Theorem 11 on each fixed-transition fibre therefore does not give Theorem 11 on the product. `FullEnv` closes it. A member carries a transition **index** drawn from an arbitrary type together with that type's map into transition functions, which is at least as general as print's *given set* `T` — any set of transitions is such a type by its own inclusion — and it is deliberately **not** specialised to all functions, since that would be a different class again and a larger maximum. `FullEnv.complement` fixes the transition and complements the grid, which is print's `μ⁻` exactly; `fullReturn_add_complement` is equation (3) on the product, and each fibre's own proof is its whole content. All three extrema are rederived over the product rather than per fibre, so `toFullComplementedClass` assumes nothing, and `everitt_theorem_eleven_fullClass` is Theorem 11 over print's Definition 9 class with the transition component arbitrary. **The residual, stated so a reader can disagree with the grade rather than discover it.** The reward and corruption components are still the full function spaces rather than arbitrary given sets. That is not a narrowing of anything the source uses: Theorem 11 *assumes* those two classes contain all functions, and completeness under print's complement — which an arbitrary given set does not provide — is what makes the class a `ComplementedClass` at all. A class over arbitrary reward and corruption sets is a product type the atlas can write and has no theorem about, and print has none about it either. Witnessed in `AISafetyAtlas.Examples.Wireheading.RewardGrid` at a two-element transition set, where the two transitions are shown distinct so the `T`-component is genuinely not a singleton, the maximal worst-case regret over the product is put at one or more, and every policy is shown to regret at least one half. Those witnesses are module-private, as the rest of that file is, so they are named here by their module rather than cited individually |
| Def. 10 | expected cumulative true reward, regret against the best policy in hindsight, and worst-case regret over the class | `mixedReturnOver`, `mixedReturnOver_ofDet`, `stochReturnOver`, `stochReturnOver_ofDet`, `returnOver`, `returnWithStart`, `returnWithStart_eq_returnOver_add`, `returnWithStart_sub`, `returnWithStart_add_complement`, `returnWithStart_add_complement_ne`, `Corruption.ComplementedClass.regret`, `worstCaseRegret`, `Examples.Wireheading.witness_returnWithStart_add_complement`, `Examples.Wireheading.witness_returnWithStart_ne_horizon`, `Examples.Wireheading.witness_returnWithStart_eq` | Yes | Same | three separate departures, **all three now closed**; the row was `Partial`/`Mixed` until 2026-09-19. **(i)** **Closed 2026-09-10.** `mixedReturnOver` is the expected cumulative true reward against a trajectory distribution that averages over the dynamics *and* over a possibly stochastic policy, which is print's expectation at print's own quantifiers; `mixedReturnOver_ofDet` and `stochReturnOver_ofDet` identify `stochReturnOver` and `returnOver` as its successive degenerate cases. **(ii)** **Closed 2026-09-19, and it is print that is inconsistent, not the transcription.** Statements re-read from rendered pages 4 and 5 of the pinned v2. **The source defines the return twice and the two do not agree.** Definition 10 prints `Ġ_t(μ, π, s₀) = 𝔼[∑_{k=0}^{t} Ṙ(sₖ)]`, which counts the start state and has `t + 1` terms. The proof of Theorem 11 writes an **undotted `G_t`, defines it nowhere**, and computes with `∑_{k=1}^{t}` in the display under equation (3) — and must, since `t + 1` unit-complementary terms sum to `t + 1` rather than to `t`. Previously the atlas rendered only the proof's sum and recorded the discrepancy in prose. It now renders **both** and proves which one equation (3) admits. `returnWithStart` is Definition 10 exactly as printed; `returnWithStart_eq_returnOver_add` says it is `returnOver` plus the start state's true reward; `returnWithStart_add_complement` computes the complementary printed returns as `t + 1`; and `returnWithStart_add_complement_ne` states the consequence, that **print's equation (3) is false for print's own Definition 10**. `returnWithStart_sub` then shows the discrepancy never reaches Definition 10's `Reg`: regret is a *difference* of two returns in the same environment from the same start state, so the start-state term cancels and the atlas's regret is Definition 10's regret exactly. The disagreement bites in one place only — equation (3), where the returns are added rather than subtracted — and there the atlas follows the proof, as it must. Grounded at data by `witness_returnWithStart_add_complement`, which reads `2` at `witness`'s horizon of `1`, and `witness_returnWithStart_ne_horizon`. **(iii)** in `CRMDP`, `StochModel` and `MixedModel` the `max` over policies and over the class are attained by structure fields; in `AISafetyAtlas.Wireheading.RewardGrid` they are **derived** — `exists_max_gridReturn` and `exists_min_gridReturn` over the whole policy function space, and `Fintype (GridEnv m State)` over the class. Proving what a source asserts without proof is coverage rather than generality, so this closes a departure and moves no scope cell. **Why `Yes`/`Same`.** Every printed component of Definition 10 is rendered — both readings of the return, the regret against the best policy in hindsight, and the worst-case regret over the class — and the one place the two readings differ is proved rather than asserted. Nothing here is narrower than print, and the atlas holds a statement about print's `Ġ` that print does not: that it cannot satisfy the paper's own equation (3) |
| Thm. 11 | if the reward and corruption classes contain all functions over a uniform discretisation, every policy's worst-case regret is at least half the maximum worst-case regret | `RewardGrid.everitt_theorem_eleven_fullMixedClass`, `RewardGrid.toFullMixedComplementedClass`, `RewardGrid.everitt_theorem_eleven_mixedGridClass`, `RewardGrid.everitt_theorem_eleven_stochGridClass`, `RewardGrid.everitt_theorem_eleven_fullClass`, `RewardGrid.everitt_theorem_eleven_gridClass`, `RewardGrid.fullMixedReturn_ofDet`, `RewardGrid.gridMixedReturn_affine`, `Decision.MDP.run_update_decomp`, `Decision.le_of_affine_of_det_le`, `Decision.MDP.run_mapObs`, `Corruption.ComplementedClass.everitt_theorem_eleven`, `CRMDP.Model.everitt_theorem_eleven`, `CRMDP.StochModel.everitt_theorem_eleven`, `CRMDP.MixedModel.everitt_theorem_eleven`, `CRMDP.Model.toStoch_returnValue`, `CRMDP.StochModel.toMixed_returnValue` | Yes | **Wider** | **Closed 2026-09-19. The row was `Partial`/`Mixed` from the first grading until then, and its own axis list was wrong.** Print's statement is **five** things at once, not the four this row counted. *(a) the printed class* -- the full product of grid-valued true-reward and corruption functions, completeness structural rather than assumed; *(b) the three extrema derived rather than assumed*; *(c) a kernel-valued transition*, which at print's finite state set (Definition 7) is print's `T` exactly; *(d) print's quantifier over a possibly stochastic policy*; and *(e) print's **class**, which is Definition 9's and whose transition component is a **given set**, not one transition. **Axis (e) is the one this row never named**, and naming it is part of the closure: the four-axis list was an inventory of what the atlas had split across renderings, not a reading of print. Theorem 11 is stated over `M` of Definition 9, and Definition 9 quantifies over `T` as well as over the reward and corruption sets. Grading this row closed against *(a)*--*(d)* alone would have laundered *(e)*, which is exactly the move the Definition 9 row above refused when it recorded that a maximum over a larger class is larger. For the same reason *(e)* is not a corollary of the rest: `worstCaseRegret` is a maximum over the class, so a statement at one transition says nothing about a statement over a set of them.** **`everitt_theorem_eleven_fullMixedClass` carries all five.** Its class is Definition 9's -- a given set of transitions, each read as a `Decision.MDP`, crossed with the full product of grid-valued reward and corruption functions -- its transitions are distributions, its policies are **all** the possibly stochastic ones, and none of the three extrema is a field. **How (d) was reached, since the headers priced it wrongly twice.** It is neither a mixture decomposition nor backward induction, both of which would have rebuilt the run this cluster shares. `Decision.MDP.run_update_decomp` says the run is affine in what the policy does at a **single** history -- drawing that action first and running with a point mass there is the same distribution -- and `Decision.le_of_affine_of_det_le` iterates that over the finitely many histories a run of `t` steps can reach, so the deterministic extrema already derived bound the mixed policies with nothing new assumed. No argmax appears anywhere: a weighted average of terms below a bound is below the bound. **All of it happens at a finite observation alphabet, and that is why the earlier cost estimate was wrong.** `CRMDP.Obs` carries a real-valued reward, so the short histories over it are not a finite set and the reduction has nothing to induct over. `Decision.MDP.run_mapObs` says a run at a relabelled alphabet is the pushforward of the run underneath it, and a grid environment's real channel is finite, so the argument runs there and transports back. The observation-type *refactor* this row was priced at on 2026-09-19 does not exist; one lemma did it. **The renderings are chained rather than merely analogous**, which is what keeps the four narrower statements meaningful: `CRMDP.Model.toStoch_returnValue` and `CRMDP.StochModel.toMixed_returnValue` identify the deterministic, drawn-dynamics and mixed-policy returns, and `RewardGrid.fullMixedReturn_ofDet` identifies `everitt_theorem_eleven_fullClass` as the determined instance of the full statement rather than a parallel one. **Wider, not `Same`.** `Corruption.ComplementedClass` is abstract in its return function, so every widening above is carried by `stochReturn_add_complement` and `mixedReturn_add_complement` and nothing of the regret argument is reproved; the abstract form applies to any complement-closed class with attained extrema, whatever its rewards, and `AISafetyAtlas.Examples.WorkbenchConsumers` instantiates it at `Bool` environments and `Bool` policies, which is not a CRMDP at all. **Non-vacuity, and tightness.** `AISafetyAtlas.Examples.Wireheading.CRMDPModel` inhabits `CRMDP.Model` with a worst-case regret of exactly one -- the most a one-step horizon admits. `AISafetyAtlas.Examples.Wireheading.StochasticPolicy` does the same at the full policy class, where `coinPolicy` is a fair coin at every history, `coinPolicy_apply` shows it is not a point mass, and `coinPolicy_worstCaseRegret` computes its worst-case regret as exactly `1/2`, so **print's factor of two is attained** and the constant cannot be improved. `AISafetyAtlas.Examples.Wireheading.RewardGrid` works the joined statement at a two-element transition set with a fair coin, so every one of the five axes is non-degenerate at once in a single instance; those witnesses are module-private, as the rest of that file is, and are named here by their module. **One thing this closure makes stale and does not decide.** The registry relationship is `RELATED`, and the reason recorded for it was the missing join. The join now exists, so that reason is gone; whether the relationship should change is a registry decision and is left to a maintainer rather than taken here |
| Thm. 11 proof, step 1 | complementing the true reward and pre-composing the corruption with the same complement leaves the observed reward function unchanged | `Env.observed_complement`, `Env.rewardComplement_involutive`, `Env.complement`, `Env.complement_involutive` | Yes | Same | the load-bearing step, proved rather than assumed. `rewardComplement` is `x ↦ 1 - x` on `Set.Icc 0 1`, and print's uniform grid is closed under exactly this map — which is why the atlas's wider carrier does not break the argument |
| Thm. 11 proof, step 2 | therefore the two environments induce the same measure over histories | `run_complement`, `stateAt_complement`, `history_complement`, `stochRun_complement`, `stochStateAt_complement`, `mixedRun_complement`, `Examples.Wireheading.StochasticPolicy.coinPolicy_mixedRun_complement` | Partial | Same | **Regraded from `Narrower` on 2026-09-18.** The note this row carried said the atlas had only the deterministic shadow -- the two environments generate the same *history* -- and that "an equality of histories is not an equality of measures, and the general statement is not obtained". The general statement was obtained and the note went stale. `stochRun_complement` is print's step 2 verbatim: an environment and its complement induce the **same distribution** over state-and-history pairs, for every deterministic policy and every number of steps, with `stochStateAt_complement` the state marginal of it. `mixedRun_complement` is the same equality when the action is drawn rather than determined, so print's "every policy" is met at the widest quantifier the section carries, and `coinPolicy_mixedRun_complement` works it at a fair coin. The deterministic lemmas are kept in the Atlas cell because they are what `Model` uses |
| eq. (3) | the true returns of an environment and its complement sum to the horizon | `mixedReturn_add_complement`, `mixedRun_complement`, `mixedStateAt_complement`, `stochReturn_add_complement`, `return_add_complement`, `expectReward_add_complement` | Yes | **Wider** | closed 2026-09-10, the policy axis included. `mixedReturn_add_complement` is the printed identity between expectations that average over the dynamics **and** over the agent; `stochReturn_add_complement` and `return_add_complement` are its successive degenerate cases, identified as such by `mixedReturnOver_ofDet` and `stochReturnOver_ofDet`. The previous revision of this row said that closing the policy axis "means an action-distribution-valued policy and a second `bind` in the run, which is a further widening on a different axis and is not taken here". It has been taken, and it cost one lemma rather than a second proof. Two facts carry the identity and neither changed shape: `mixedRun_complement`, which says the whole trajectory *distribution* cannot see the complement because the recursion mentions the environment only through `Env.observed`, and `expectReward_add_complement`. The agent's randomness is bound in on the outside of the step and the environment enters the step only through the channel `Env.observed_complement` fixes, which is *why* the argument is indifferent to it. `Wider` on the carrier: `Reward` is `Set.Icc 0 1` where print's `R` is a finite uniform grid inside it, and `State` and `Action` are arbitrary types. The horizon convention is print's own **proof's**, not its Definition 10's — see the `Def. 10` row, departure (ii) |
| eq. (4) | the maximum regret of any policy in one environment is the spread between the best and worst achievable returns there | — | No | — | the atlas's proof of Theorem 11 takes a different route: it pairs the environment witnessing the worst policy's regret with that environment's complement and closes with one linear-arithmetic step, so the printed **identity** is never stated. Both of its sides now exist — `RewardGrid.bestPolicy` and `RewardGrid.minPolicy` are the two returns, and `RewardGrid.spreadEnv_max` maximises their difference over the class — and the identity between them is still not proved, which is what keeps this row `No` |
| eq. (5) | the best return in the complement environment is the horizon minus the worst return in the original | — | No | — | as above |
| Asm. 12 | reward corruption is limited to an unsafe set of states, and the observed reward agrees with the true one on the safe set | — | No | — | the atlas has no safe/unsafe partition and no assumption restricting the corruption function. Every environment in `Env State` may corrupt everywhere |
| Def. 13 | a CRMDP is communicating when the expected time to reach any state under some policy is bounded | — | No | — | this row named the stochastic layer as its blocker until 2026-09-10; that layer is here, `mixedStateAt` is the distribution over states after `n` steps, and the definition is still not stated. `No` because nothing states it, not because the means are missing. What it would need beyond the substrate is a hitting time and its expectation, neither of which the cluster has |
| Asm. 14 | an easy environment class: no traps, and enough safe states | — | No | — | the stochastic half of the blocker this row named closed on 2026-09-10; what is left is Definition 13's hitting time and Assumption 12's safe/unsafe partition of the state set, and the atlas has neither |
| Def. 15 | the Bayesian and the conservative agent, defined against a belief over a countable class | — | No | — | the atlas has no belief distribution over environments and no time-indexed agent |
| Thm. 16 | under the simplifying assumptions, a Bayesian agent still suffers high regret on some CRMDP | — | No | — | the second negative result of §3, and entirely absent. It needs Definition 15's agents, which need the belief layer |
| Def. 17 | a CRMDP with decoupled feedback: a family of observed reward functions indexed by the state the agent is in | — | No | — | §4's whole apparatus is absent |
| Asm. 12′ | decoupled feedback with limited reward corruption | — | No | — | as above |
| Ex. 18 | a two-state decoupled RL instance | — | No | — | as above |
| Thm. 19 | in a countable communicating class with decoupled feedback and limited corruption, the true reward function is learnable | — | No | — | the paper's main positive result, and the reason the negative one matters. Absent |
| Thm. 20 | the Bayesian agent's regret is sublinear under the same conditions | — | No | — | as above |
| Ex. 21 | CIRL sensory corruption as a decoupled RL instance | — | No | — | as above |
| Def. 22 | the quantilising agent random-walks until every state is visited, then commits to a high-value one | — | No | — | §5 is absent; it needs randomisation, which needs the stochastic layer |
| Thm. 23 | the quantilising agent's regret bound | — | No | — | as above |
| Ex. 24 | soft-max and epsilon-greedy on a CRMDP with many actions | — | No | — | as above |
| Def. 25 | unichain CRMDP | — | No | — | as above |
| Def. 26 | the asymptotic value contribution of a state to a policy | — | No | — | as above |
| Def. 27 | the general quantilising agent | — | No | — | as above |
| Thm. 28 | the general quantilisation regret bound | — | No | — | as above |
| — | complementing is an involution on environments and on rewards, and the whole class is therefore closed under it with no side condition | `Env.complement_involutive`, `Env.rewardComplement_involutive` | — | **Beyond** | print asserts that the complemented functions are in the class and does not state involutivity. `ComplementedClass` carries the involutivity as a field precisely so that a class supplied by a consumer has to prove it |
| — | as a function of the unknown environment, the true finite-horizon return does not factor through the observed history a fixed policy receives | `ObservationLimits.not_knowable_trueReturn_of_complement_mem`, `ObservationLimits.not_knowable_trueReturn`, `ObservationLimits.complementWitness` | — | **Beyond** | print's two steps read as one statement about what an observation settles, with the environment as the unknown. Print does not state it. The class-relative form is the primary one, and the escape route — a class containing no return-disagreeing complement pair — is exhibited in `AISafetyAtlas.Examples.Wireheading.ObservationLimits` |

**8 Yes, 2 Partial, 25 No, 2 Beyond.** `Yes` moved from 3 on 2026-09-10, when
equations (1) and (3) closed at print's own quantifier over the policy.

**The largest gap was closed on 2026-09-09, and the sentence that used to stand
here estimated it.** The estimate is kept because it is now checkable against
what was built: at a fixed horizon `t` a return depends on a policy only through
the actions it takes at the `t` histories the rollout reaches, those histories
have pairwise distinct action-list lengths, so every length-`t` action sequence
is realised by some policy and conversely, and the image of the return over the
whole policy function space is its image over `Fin t → Action`. Those are `RewardGrid.historyUpTo_length`, `stateAt_eq_seqState`, `stateAt_seqPolicy`
and `seqState_congr`, and the extrema follow. Extrema over environments follow
from `Fintype (GridEnv m State)`.

**The stochastic layer arrived on 2026-09-10, in two steps and on both axes.**
The sentence that used to stand here said `transition` would become a kernel,
`returnOver` an expectation over the process of print's equation (1), and
`history_complement` — an equality of histories — an equality of measures. All
three happened. `AISafetyAtlas.Wireheading.StochasticCRMDP` makes the transition
a `PMF` and the return an expectation;
`AISafetyAtlas.Wireheading.StochasticPolicy` makes the policy a `PMF`-valued
function of the observed history, so the process of equation (1) is built at
print's own quantifiers; and `mixedRun_complement` is the equality of
*distributions* over trajectories that `history_complement` was standing in for.
`PMF` rather than `Mathlib.Probability.Kernel` is a further widening on the same
axis, is not taken, and is not costed.

**What that did not do is unblock the `No` rows, and the estimate that stood here
was wrong about which gap they share.** It said Section 9's `No` rows from
Assumption 12 onward all wait on the same substrate as the measure layer. The
measure layer landed and not one of them moved. What Assumption 12 onward
actually wait on is a safe/unsafe partition of the state set, a belief
distribution over a countable environment class, and a time-indexed agent — the
learning layer, which is separate from the measure layer and was never a
consequence of it. That remains **open and not costed**: nothing here has
measured what a belief layer would take on this tree, and an unmeasured estimate
is not evidence. The two rows that named the stochastic layer as their blocker
are corrected above.

---

## 10. Everitt, Filan, Daswani & Hutter 2016, arXiv:1605.03142v1 → `AISafetyAtlas.Wireheading.GoalPreservationSource`

Graded for the first time on 2026-09-09. The pinned file is the **technical
report**, arXiv:1605.03142v1, 10 May 2016, 19 pp., sha256
`1b7a3c091bd2c02b30d9bc9201bf09b5c6f9af839d30240458da917a3f750461`. Every
number in the `#` column is that report's.

**The published chapter was obtained later the same day** — inside the
publisher-typeset AGI 2016 proceedings volume, LNAI 9782, sha256
`4486e912ea2c0ed387bfaa4eaaf431db39ae2f362902fb880f5f2bc14d18d403`, where the
chapter occupies pp. 1–11 — and two claims the atlas had been carrying are now
verified rather than reported. First, the chapter really does print no proofs:
its p. 8 reads "Proofs for all theorems are provided in a technical report",
and no proof environment appears in it. Second, the cross-map is right, and the
full concordance for what this section grades is:

| This report | AGI 2016 chapter |
|---|---|
| Definition 12 (realistic value functions), eqs. (7)–(8) | Definition 9 |
| Lemma 13 (iterative value functions), eqs. (9)–(11) | *absent* |
| Theorems 14 / 15 | Theorems 10 / 11 |
| Theorem 16, conclusion eq. **(13)** | Theorem 12, conclusion eq. **(7)** |
| Appendix A: Lemma 19, Theorems 20 and 21 | *absent* |

The two statements of the theorem **were read side by side** — the chapter's
p. 9 rendered as an image, the report's from its text layer — and they agree
word for word, lead-in sentence included, up to the renumbering. The collision
is worth naming: "equation (7)" in
this section and in the Lean modules always means **this report's** `V = Q∘π`
identity, never the chapter's number for Theorem 16's conclusion.

**Where the declarations live.** Two modules do the work and a third is
secondary. `Wireheading.GoalPreservationRun` carries the printed conclusion;
`Wireheading.GoalPreservationSource` carries its one-step ingredient and the
strict-expectation lemma; `Wireheading.GoalPreservation` is a deterministic
named-policy specialization that reaches the same conclusion under a premise
print does not have, and grades nothing on its own — see the note on Theorem 16.

**Two axes run through the section.**

* **Percepts are finite, and so are print's** — *retracted as a narrowing on
  2026-09-10.* This bullet used to read "Print's `E` is an expectation over a
  percept space with no cardinality stated", and recorded finite percepts as an
  axis this section narrows on. That was a debt to nobody. Page 3 of
  arXiv:1605.03142v1 opens the setup with *"The agent picks actions `a` from a
  finite set `A` of actions, and the environment responds with a percept `e`
  from a finite set `E` of percepts"*, and the same page restricts the
  environment to **full-support** percept distributions. So `Fintype Percept`
  and the positivity field are print's own conditions rather than atlas
  additions, and no row below narrows on them. Every expectation here is a
  normalised `Finset` sum over a `Fintype`, which at print's finite `E` is
  print's expectation exactly; no measure theory is used, and none is owed on
  this axis. What the retraction does **not** buy is a better grade: the rows
  below stay where they are for the reasons in their own notes — the naming map
  as an object, the value family at `t = 1` only, and Theorem 20 assumed rather
  than proved.
* **Modification-independence is structural, not derived.** Print defines it
  (Definition 7), assumes it (Assumption 8), and uses its Appendix-A Theorems 20
  and 21 to conclude that an optimal policy's realistic `Q`-value is
  modification-independent. In the atlas the continuation value is a function of
  a policy *name* and a history that records no modifications, so
  modification-independence holds by the shape of the signature. Under
  Assumption 8 that signature is print's setting, which is why it is a rendering
  rather than an added hypothesis — but Definition 7, Assumption 8 and Theorems
  20 and 21 are consequently absent as statements, and each has its own `No` row.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Rem. 1 | utility as a discounted sum is a restriction, and a continuity condition would be more general | — | No | — | a remark about the setup's generality, not a proposition |
| Def. 2 | the standard, non-self-modifying `Q`- and `V`-value functions | — | No | — | the atlas has only the realistic value functions of Definition 12. Nothing here compares a self-modifying agent with a standard one |
| Def. 3 | a policy self-modification model is a tuple of world actions, percepts, policy names and a naming map | `GoalPreservationRun.Model`, `GoalPreservationSource.Model` | Partial | Same | the world actions, percepts and policy names are all present, and `act` is print's `ι(p)` applied at a history. **The missing-object axis closed 2026-09-13.** Definition 3 reads *"Let `Π = {(𝒜 × ℰ)* → 𝒜}` be the set of all policies, and let `ι : 𝒫 → Π` assign names to policies"*, so print's `Π` is the full function space and its `ι` is exactly `act` uncurried. Both models now name them — `Policy` and `Model.name`, with `name_eq_act` recording that naming them changed nothing — so the quadruple `(𝒜̌, ℰ, 𝒫, ι)` has all four components as objects, and `Examples.Wireheading.GoalPreservationRun` exhibits a model whose `ι` is **not** surjective, so the absence of a surjectivity assumption is not vacuous. That absence is what `Wireheading.GoalPreservation`'s *names_surjective* field was papering over. **Still `Partial`, and on a coverage axis rather than a scope one**: print's own argument that `𝒫 = Π` is impossible is a cardinality claim about `\|Π\| > \|𝒫\|`, and what is carried is one model where `ι` misses a policy, not that every model must |
| Ex. 4 | the Gödel machine as a self-modification model | — | No | — | not modelled |
| Def. 5 | the utility self-modification model | — | No | — | **the atlas formalizes policy self-modification only.** Utility modification is absent from every module in the cluster |
| Ex. 6 | a chess-playing RL agent that would rather rewrite its utility | — | No | — | an informal scenario |
| Def. 7 | modification-independence of a belief or a utility function | — | No | — | see the second standing axis: it is a property of the signature here and not a definition |
| Asm. 8 | the belief and every utility function are modification-independent | — | No | — | as above. This is the hypothesis under which the atlas's signature is print's setting, so it is assumed by construction and never stated |
| Def. 9 | an agent's performance is its expected discounted initial utility | — | No | — | no infinite-horizon performance measure is defined anywhere; the *contValue* field is a continuation value, not a performance |
| Def. 10 | hedonistic value functions, which evaluate the future by the *future* utility function | — | No | — | absent, and its absence is why Theorem 14 is absent |
| Def. 11 | ignorant value functions, which ignore the effect of self-modification on future action selection | — | No | — | absent, and its absence is why Theorem 15 is absent |
| Def. 12, eqs. (7) and (8) | realistic value functions: the value of a policy at a history is the `Q`-value of the action it takes, and the `Q`-value anticipates the *next* policy | `GoalPreservationRun.Model.qValue`, `GoalPreservationRun.Model.contValue_eq_qValue`, `GoalPreservationSource.Model.qValue`, `GoalPreservationSource.Model.qValueWith`, `GoalPreservationSource.Model.qValueWith_utility`, `GoalPreservationSource.Model.qValueWith_eq_qValue_of_utility_fixed`, `Examples…trivialModel_qValueWith_eq`, `Examples…trivialModel_qValueWith_ne` | Partial | **Wider** | equation (8) is `GoalPreservationRun.Model.qValue` and equation (7) is the *bellman* field of `GoalPreservationRun.Model`. **The utility-index axis was regraded, not closed, on 2026-09-19, and the earlier `Narrower` was a double count.** This row read that print defines the pair for every time index `t` while the atlas has it at `t = 1`. Print's `t` indexes the *utility function* `uₜ`, not the time step — `k` is the history index — and the family is non-constant only under **Definition 5**, the utility self-modification model. The model here is print's **Definition 3**, where print says of the two models that in the policy one, modifications *"do not affect the agent's utility function or belief"*; Theorem 16, which this cluster proves, is *"Realistic policy-modifying agents make safe modifications"* and lives in that same model. So `uₜ = u₁` for every `t` here and the single utility is print's whole family, not one member of it. `qValueWith` makes the index explicit rather than silently fixed and `qValueWith_eq_qValue_of_utility_fixed` is the collapse, with `Examples…trivialModel_qValueWith_ne` showing the index is not vacuous — two utilities do give different `Q` values — so the collapse is Definition 3 doing work and not a rendering in which `t` could never have mattered. **The missing family is Definition 5's absence and is already graded `No` on its own row**; grading it twice was the error. `Wider` on two axes: the continuation value is a *field* constrained by `bellman`, so the class is every `V` satisfying print's (7)–(8) rather than the unique discounted solution print's recursion denotes, and `History` is an abstract type where print's is `(𝒜 × ℰ)*`. **Still `Partial`**, and for the reason the `Wider` axis creates: no `V` is *constructed* here, so existence of a solution to (7)–(8) is not proved in general, and `Examples…trivialModel`, together with the alternating model the run module's own example file builds, is what keeps the class inhabited. The finite-percept clause this note once carried was retracted with the section's first bullet, print's percept set being finite already |
| Lem. 13 | the realistic value functions are the recursive form of expected initial utility | — | No | — | the atlas takes the recursive form as given — the *bellman* field asserts it — and never connects it to a sum of discounted utilities. So the *interpretation* of *contValue* as an expected initial utility is assumed |
| Thm. 14 | a hedonistic agent self-modifies, and its performance can be arbitrarily bad | — | No | — | needs Definition 10, and the utility-modification model of Definition 5. Absent |
| Thm. 15 | an ignorant agent is indifferent between self-modifying and not | — | No | — | needs Definition 11. Absent |
| Thm. 16, eq. (13) | for every `t`, for all percept sequences, and for the on-policy action sequence, the initial `Q`-value of the action the current policy takes equals that of the action the initial policy would take | `GoalPreservationRun.Model.equation_thirteen`, `GoalPreservationRun.Model.run_optimal`, `GoalPreservationRun.Model.run` | Yes | **Same** | the printed conclusion, at the printed quantifiers: every step, every percept sequence, actions on-policy. **Regraded Narrower to Same on 2026-09-10.** This row read *"Narrower only by finite percepts"*, and print's own page 3 fixes a finite percept set, so the one axis it named was never an axis; with it retracted nothing is left to narrow on. The conditionality on Theorem 20 is not a scope axis of this row and is tracked on Theorem 20's own row below. **The two hypotheses are print's, not the atlas's**: the *bellman* field is equation (7), and the *initial_optimal* field is print's "the initial policy optimises the realistic value function", unfolded through equation (7) and through the full policy space being a function space into world-action-and-name pairs, so that the supremum over policies is the supremum over actions — which is the supremum print's own equation (14) takes. This replaces `Wireheading.GoalPreservation`'s *names_surjective* field, which demanded that the **named** policies already realise every action pair; that is a premise print explicitly denies, and it conflated the policy space with the set of names. `GoalPreservation.goal_preservation` still exists and still proves this conclusion under that stronger premise; it grades nothing here because a theorem with an added hypothesis proves something print did not say |
| eq. (14) | if the policy at time `t` acts optimally for the initial `Q`, so does the policy at time `t + 1` | `GoalPreservationRun.Model.optimalAt_next`, `GoalPreservationSource.Model.selected_matches_initial`, `GoalPreservationSource.Model.qValue_lt_of_lt`, `GoalPreservationSource.Model.safe_modification` | Yes | **Same** | print's induction step, and print's argument: a strictly worse continuation at one percept makes the expectation strictly worse because the percept distribution has full support, contradicting the current policy's optimality. `qValue_lt_of_lt` is that step. **Regraded Narrower to Same on 2026-09-10**, for the reason on the eq. (13) row: the finite-percept axis was print's own and has been retracted. The full-support hypothesis this argument consumes is likewise print's, stated on the same page |
| Ex. 17 | the chess agent again, now with realistic value functions | — | No | — | an informal scenario |
| Def. 18 | the world policy associated with a policy | — | No | — | Appendix A apparatus; absent |
| Lem. 19 | values in the self-modification model agree with values in the standard model | — | No | — | Appendix A apparatus; absent, and it needs Definition 2 |
| Thm. 20 | an optimal policy exists in the utility-modification case | — | No | — | **this is what the *initial_optimal* field assumes.** Print's proof of Theorem 16 opens by invoking it, so the atlas's conditional form is exactly as strong as print's unconditional one minus this existence result. Recorded here as the open item, and costed at the end of the section |
| Thm. 21 | an optimal policy has a name | — | No | — | the other half of what *initial_optimal* assumes: without it, the optimal policy might be unnamed and unreachable by self-modification |
| — | the initial policy's continuation value dominates every named policy's, and the policy in force at any step is worth exactly what the initial policy is worth there | `GoalPreservationRun.Model.contValue_le_initial`, `GoalPreservationRun.Model.run_contValue_eq_initial` | — | **Beyond** | print uses the domination fact inside its proof and never displays it; the atlas had it as a **structure field**, *initial_dominates* on `GoalPreservationSource.Model`, until this pass, which made an assumption of something derivable from equation (7) and the initial policy's optimality. `contValue_le_initial` derives it. The continuation-value form of equation (13) is not displayed in print either |

**2 Yes, 2 Partial, 18 No, 1 Beyond.**

**What it would cost to close the largest gap.** Theorems 20 and 21 are an
optimal-policy-existence argument over an action set that grows with the policy
space, which print handles in an appendix by passing through the associated
world policy of Definition 18 and the value-equivalence of Lemma 19. Formalizing
that route needs Definition 2's standard value functions and a fixed-point or
compactness argument the atlas has no infrastructure for, and it is not a small
addition. Nothing in the atlas should be read as claiming that a model
satisfying *initial_optimal* exists whenever print's setting does;
`AISafetyAtlas.Examples.Wireheading.GoalPreservationRun` exhibits **one** such
model, chosen so that the agent genuinely alternates policy names and the
derived domination is strict somewhere.

---

## 11. Ring & Orseau 2011, AGI-11, `hal-01000226v1` → `AISafetyAtlas.Wireheading.Objective`

Graded for the first time on 2026-09-09, and this is the first pass in which the
source has been read at all: the two modules citing it were written against a
description of it.

**Which text, and what it is not.** The Springer chapter (LNAI 6830, pp. 11–20,
doi `10.1007/978-3-642-22887-2_2`) is closed — OpenAlex reports its open-access status as
closed with no repository copy, and Unpaywall reports no open location. What is
pinned is the **author deposit on HAL**, `hal-01000226v1`, sha256
`a207ab73c87896e0663e4998906aa4c4bcef6d93a43d8e29ebc3cdb81e32ea6d`; HAL is the
institutional repository of the second author's affiliation on the paper, so
this is a lawful route. **It is the author version and has not been compared
with the publisher's typeset chapter.** Pagination differs. Any statement here
about the published text would be unverified, so none is made. This is the one
section in the table still graded against a text the publisher has closed.

**A second author draft exists and this section is not graded against it.** A
different author version, sha256
`ee44df16375d04f4e714c99d24fc1344bef6f324338b7b6c5567182fd6ac0b9f`, 11 pp.,
created 2011-03-07, was supplied later the same day. It is a distinct draft, not
a re-encoding: a token-level comparison of the two extracted texts gives a
similarity of 0.83 over ~4,850 tokens with 256 differing blocks, both texts
anchored at the author line so that the HAL cover sheet is excluded and nothing
else is. Draft b is also a page longer — 11 pp. of paper against 10, per each
file's own page count and running heads. Both number the same four displayed
equations; equations (2) and (3) are character-identical; equation (1) differs in
its time-index convention, the HAL copy subscripting the action by *t_h*, stated
to be *|h| + 1*, and the other subscripting it by *|h|* with no *t_h* defined.
**Every row below is
graded against the HAL copy and against no other file.** Neither draft has been
compared with the Springer chapter.

**One correction to the atlas's own prose, and its partial reinstatement.**
`Wireheading/AgentEquations.lean` recorded that the published paper writes `a`
at index `t` with `t = |h| + 1` while "the AGI-2011 conference draft writes" the
index `|h|`. The HAL deposit *is* the AGI-11 paper and it uses `|h| + 1`, so the
claim was withdrawn on the first reading. The second author draft pinned later
the same day settles what the sentence was half-remembering: that draft does
subscript the action by *|h|*. Both conventions are therefore real, one per
draft. What is
still unverified, and is not asserted anywhere, is which one the **Springer
chapter** prints. The module's own statement is unaffected either way — `t` is a
parameter there, so both indexings instantiate it.

**The paper prints no theorem, lemma or definition environment.** Its seven
numbered items are **Statements**, each followed by a paragraph headed
*Arguments*. That is why no row below can be `Yes` on a numbered item: there is
no proof to reproduce and the statements are about four specific agents the
atlas does not construct.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §2, eq. (1) | the agent takes the action maximising the value of the extended history | `AgentEquations.bestAction`, `AgentEquations.bestAction_max` | Yes | Same | `bestAction` chooses an action attaining the maximum and `bestAction_max` proves it maximal, which is what the equation asserts. **The action axis closed 2026-09-13**: `Action` was a nonempty `Fintype` where print writes `max` over an unqualified set `A`, and the maximum inside *value* is now `⨆` over an arbitrary action type while `bestAction` takes `Attains` — print's own presupposition in writing an argmax, and strictly weaker than a `Fintype`. `attains_of_fintype` and `value_succ_eq_sup'` recover the finite readings, so the previous signatures are instances of these. No hypothesis was added to buy it: `value`, `actionValue`, `value_eq_of_agree_on_window`, `value_eq_zero_of_horizon_vanishes` and `truncation_exact` need attainment nowhere, and four of them turned out not to need the action type inhabited either. **The grade rests on a fact this tree does not prove.** `⨆` is Mathlib's conditional supremum, zero by convention at a family that is empty or unbounded above; at print's own hypotheses — `u : ℋ → [0,1]`, `w` summable — the family is bounded and the supremum is print's maximum, and that implication is not formalized here. Print breaks ties lexicographically (its footnote 4); the atlas breaks them by choice, so `bestAction` is not print's function, only a maximiser. Nothing downstream depends on which |
| §2, eq. (2) | the value of an action is the prior-weighted sum over observations of the values of the resulting histories | `AgentEquations.actionValue`, `AgentEquations.Belief` | Yes | **Wider** | the sum is print's. **The observation axis was closed on 2026-09-13 and this row was `Mixed` for it until then**: `Obs` was a `Fintype` where print's setup page bounds `𝒪` nowhere, and the sum is now unconditional over an arbitrary type, with `actionValue_eq_sum` recovering the finite case. No summability hypothesis was added to buy it — the module's three theorems need only congruence and the vanishing case. Wider in that the *cond* field of `AgentEquations.Belief` is an arbitrary real-valued weight: print's `ρ(o ∣ ha)` is a probability, and the atlas assumes neither nonnegativity nor normalisation, so every statement proved here holds for print's `ρ` and for more besides **The grade rests on a fact this tree does not prove.** `∑'` is the unconditional sum, which is zero by convention at a family that is not summable; at print's own hypotheses — `ρ` a probability, `u : ℋ → [0,1]`, `w` summable — the family is summable and the value is print's, and that implication is not formalized here. `actionValue_eq_sum` covers the finite case only. Recorded the way §8's Definition 6 row records its walk-versus-path fact, and for the same reason. |
| §2, eq. (3) | the value of a history is the horizon-weighted utility plus the value of the best action | `AgentEquations.value`, `AgentEquations.value_succ`, `AgentEquations.truncation_exact`, `AgentEquations.value_eq_zero_of_horizon_vanishes`, `AgentEquations.infiniteValue`, `AgentEquations.tendsto_value_infiniteValue`, `AgentEquations.infiniteValue_eq`, `AgentEquations.value_error_le_tail` | Partial | **Wider** | `value_succ` is equation (3) with equation (2) substituted, at a remaining depth. **Equations (2) and (3) are mutually recursive with no base case**, so print's `v` is not a function until an infinite-horizon limit is supplied, and **this paper supplies none**. **The missing-limit axis closed 2026-09-13.** `AgentEquations.infiniteValue` is the limit of the finite-depth values, `AgentEquations.tendsto_value_infiniteValue` proves it is one, `AgentEquations.value_error_le_tail` certifies the truncation error uniformly at every history of a given length, and `AgentEquations.infiniteValue_eq` is this equation **at that limit**. The operators the finite form uses now denote rather than defaulting: `AgentEquations.actionValue_summable` and `AgentEquations.actionValue_bddAbove` discharge, at print's own conditions, the two implications this file recorded on 2026-09-13 as resting on nothing. **Bounded is not attained**: `AgentEquations.Attains` is still a hypothesis and is not derived from the bound, so where print's maximum is not attained the two still differ. The limit is constructed under a summable horizon, which **this paper does not print and its companion does** — section 13's equation (1) row quotes it — so the condition is named and attributed rather than attributed here. Wider in the utility codomain: print's `u` maps into `[0,1]` and the utility component of `AgentEquations.Agent` is real-valued with no range invariant |
| §2, `A` sub `rl` | the reinforcement-learning agent: utility is the last reward, horizon weight one inside a window | `DelusionBox.rlAgent`, `DelusionBox.windowHorizon`, `DelusionBox.lastReward` | Yes | **Wider** | print's *u(h)* is the reward at step *\|h\|* and its *w(t,k)* is one exactly when *k - t ≤ m*. `windowHorizon` writes that condition as `k ≤ t + m`, which is the same over the integers and avoids truncated subtraction. Wider on two axes: the reward is read off an observation by an arbitrary function, where print fixes the observation as a pair of other information and a reward and takes the second component; and `Agent.utility` is real-valued where print's `u` maps into `[0,1]`. `lastReward` is total, zero on the empty history, where print's reward at step *\|h\|* is undefined there |
| §2, `A` sub `g` | the goal-seeking agent: utility one when the goal is reached, horizon weight favouring short histories | `DelusionBox.goalAgent`, `DelusionBox.shortHorizon` | Yes | **Wider** | print's utility is one exactly when its goal predicate holds of the observations so far, and its *w(t,k)* is *2^{t-k}*. `shortHorizon` takes the exponent as an **integer** difference, so it is print's weight at every `(t,k)` and not only at future steps. Wider in that print's side condition — the goal is reachable at most once, so the utilities along a trajectory sum to at most one — is a condition on `g` that is not imposed. **It is no longer unused, as of 2026-09-20**: `ReachedAtMostOnce` is that condition and `goalAgent_value_le_shortHorizon` is what print stated it for, since without it the goal-seeking value exceeds the horizon weight of its own step by a factor of two and Statement 2's bound fails |
| §2, `A` sub `p` | the prediction-seeking agent: utility one on a correct prediction | `DelusionBox.predictionAgent` | Yes | **Wider** | print's utility is one exactly when the agent predicted the observation it just received. Wider in that the prediction is an arbitrary function of the history before that observation arrived; print takes it to be Solomonoff induction's maximiser over the prior, so print's is one instance |
| §2, `A` sub `k` | the knowledge-seeking agent: utility is the negated prior mass of the history | `DelusionBox.knowledgeAgent`, `DelusionBox.coherentKnowledgeAgent`, `DelusionBox.spikeHorizon`, `AgentEquations.historyMass` | Yes | **Wider** | print's utility is the negated prior mass of the history and its *w(t,k)* is one exactly when *k - t = m*. `knowledgeAgent` takes the mass as a parameter, so print's own prior mass is one instance; `coherentKnowledgeAgent` restores the tie at the observation-conditional. Statement 4 is the paper's positive claim about this agent and is graded on its own row |
| §2, optimal variants | for each agent there is an optimal non-learning variant with full knowledge of the environment, and if the learning agent takes the same actions its behaviour is also optimal | `DelusionBox.diracBelief`, `DelusionBox.actionValue_diracBelief`, `ProgramPrior.Model.point`, `ProgramPrior.Model.point_belief_eq`, `ProgramPrior.Model.value_point_eq` | Partial | Same | print obtains the variant by replacing its prior with one that puts weight one on the true environment and zero on every other, in equation (2) only, and `DelusionBox.actionValue_diracBelief` is equation (2) at such a belief: the sum over observations collapses to the one the known environment produces. **The program-layer axis closed 2026-09-13.** `ProgramPrior.Model` is print's page-2 setup: `ProgramPrior.Model.Consistent` is its `𝒬_h` — *"a program q is consistent with h ... means that the program outputs the observations in the history if it is given the actions as input"* — and `ProgramPrior.Model.mass` is its `ρ(h) := Σ_{q∈𝒬_h} ρ(q)`, summable because print says that sum *"must be finite"*. `ProgramPrior.Model.mass_eq_historyMass` joins it to the observation layer rather than leaving the two parallel, and `ProgramPrior.Model.belief_isSubprobability` is what the value bounds consume. `ProgramPrior.Model`'s weight field is nonnegative where print's `ρ : 𝒬 → (0,1]` is strictly positive, and that is not a liberty taken against this row: print's own `μ` for the optimal variant is the weight that is one at its own true program and zero elsewhere, so a prior class closed under that is what the row needs. `ProgramPrior.Model.point` is print's replacement **at the program level**, and `ProgramPrior.Model.point_belief_eq` shows it induces exactly this section's observation-level belief on every history the true program explains, with `ProgramPrior.Model.value_point_eq` carrying that to the values — so the point mass is no longer an observation-level stand-in for an object the tree lacked. **Still `Partial`**, and on the other count only: print's second sentence, that a learning agent taking the same actions is also optimal with respect to its own utility and horizon, is not proved anywhere |
| §3, the delusion box | the global environment splits into an inner environment and a box the agent programs, which rewrites its observations | `DelusionBox.GlobalEnv`, `DelusionBox.Act`, `DelusionBox.GlobalEnv.trace`, `DelusionBox.GlobalEnv.globalObs`, `DelusionBox.GlobalEnv.innerHistory_congr_innerAction`, `DelusionBox.GlobalEnv.globalObs_identity`, `DelusionBox.GlobalEnv.globalObs_const_of_isConstant`, `DelusionBox.GlobalEnv.globalObs_indep_inner` | Yes | **Wider** | field for field: the first field is print's inner environment, the second is print's box, the third and fourth are print's initial condition that the box starts by running the identity, and an action is print's pair of a program and an inner action. Print's two assumptions become theorems rather than restatements — the inner environment cannot read the program (`innerHistory_congr_innerAction`, which holds because `inner` takes an inner action), and a constant program makes the inner environment invisible (`globalObs_indep_inner`). Wider in that a program is an abstract type with a semantics map, where print says the box executes *code*: any coding of a map on observations instantiates it, and no computability assumption is imposed |
| Stmt. 1 | the reinforcement-learning agent will use the delusion box | `DelusionBox.statement_one`, `DelusionBox.statement_one_of_posterior`, `DelusionBox.mixture_lt_of_threshold`, `DelusionBox.bestAction_ne_of_lt`, `Mixture.posterior`, `Mixture.mixtureBelief`, `Mixture.mixtureBelief_cond_mul_posterior`, `Mixture.policyValue`, `Mixture.policyValue_mixture`, `Mixture.policyActionValue_mixture`, `Mixture.actionValue_mixture_le`, `Mixture.value_mixture_le`, `Examples.DelusionBox.rl_uses_the_box`, `Examples…not_mixesAt_one`, `Examples…rl_uses_the_box_of_posterior`, `rlAgent_actionValue_next_const`, `rlAgent_actionValue_nonneg`, `rlAgent_actionValue_le`, `rlAgent_actionValue_zero`, `GlobalEnv.next_const`, `threshold_unattainable_of_one_le`, `not_mixture_lt_of_threshold_without_rbar`, `Examples…rl_boxed_yes_one` | Yes | **Wider** | print's threshold is print's: `statement_one` concludes at `P(DB) > 1/(2 - r̄)`, and `bestAction_ne_of_lt` carries that to equation (1). What print does not state, and what is therefore carried as named explicit hypotheses, is the whole of the gap. (i) `MixesAt`: print treats `v(h yes)` and `v(h no)` as `P(DB)`-weighted averages of the value under each hypothesis, and equations (2) and (3) do not give that, because equation (3) maximises over actions *inside* the recursion. (ii) The four bounds on the two actions' branch values — `1` attained in the box branch, `≥ 0` outside it, `≤ r̄` for the other action in the box branch, `≤ 1` outside — which print writes as arithmetic without deriving from the agent. (iii) `r̄ < 1`, without which the printed threshold exceeds every probability. (iv) That a box-using action exists at all. Nothing is folded into `rlAgent`, which is a parameter of the theorem. `Partial` and not `Yes` because a reader cannot derive print's unconditional claim from this: what is proved is print's argument with its premises named. **Hypothesis (i) is no longer merely unproved: it is false, as of 2026-09-19.** `Examples…not_mixesAt_one` exhibits two one-bit environments whose fixed-weight half mixture is the uniform belief — exactly `mixesAt_zero`'s hypothesis — and at remaining depth **one** the informed action values are `2` and `1` while the mixture's own is `1`, so print's average of `3/2` is not the mixture's value. A maximum does not commute with a convex combination, and equation (3)'s maximum sits inside the recursion. **What print needed is now built**, in `AISafetyAtlas.Wireheading.Mixture`: a fixed weight is not a mixture of two environments at all but a third that never learns, so the weight is the *posterior* `Mixture.posterior`, the mixture is `Mixture.mixtureBelief`, and `Mixture.mixtureBelief_cond_mul_posterior` is the Bayes identity that makes the cross term a fixed weight leaves behind vanish. At that weight a **committed policy's** value is exactly the average — `Mixture.policyValue_mixture`, an equality, because no maximum intervenes — while the **optimal** value is only at most it, `Mixture.value_mixture_le`. **That distinction is the finding.** Print uses an equality on *both* branches of its comparison, and the two branches need opposite directions: the `no` branch needs the upper bound, which is what the optimal value gives, and the `yes` branch needs a *lower* bound, which the inequality does not give and a committed policy's value does. So print's `yes` branch has a real gap and not a cosmetic one. **Two of the four axes closed on 2026-09-19.** `statement_one_of_posterior` is print's conclusion with **no** decomposition hypothesis at all: the belief is `Mixture.mixtureBelief`, the weight is the posterior at the history where the comparison is made — which is what print's `P(DB)` denotes, a credence, though print never indexes it by history — the `no` branch is bounded above by `Mixture.actionValue_mixture_le` and the `yes` branch **below** by `Mixture.policyActionValue_mixture` at a committed policy. That closes (i). It also closes (iv): the action compared against is the one the policy takes, so a box-using action is exhibited rather than assumed. `Examples…rl_uses_the_box_of_posterior` inhabits the whole antecedent at prior `3/4` and `r̄ = 0`, so the repaired statement is not a vacuous implication; at the empty history both masses are one, which is why the posterior there is the prior and print's threshold is a condition on `p` itself. **The last two axes closed on 2026-09-20, and print's argument is why they could.** (ii): the four branch bounds are now theorems about print's own agent. `rlAgent_actionValue_next_const` is *"the agent can program the DB to produce a constant reward of 1"* — at a global environment whose box runs a program constant at a reward-one observation, the value is that reward **exactly**, by `GlobalEnv.next_const`, where print writes an inequality. `rlAgent_actionValue_nonneg` and `rlAgent_actionValue_le` are print's `≥ 0` and `≤ 1` from a bounded reward and `Belief.IsSubprobability` — print's own `u : ℋ → [0,1]` and its `ρ` a probability. The fourth, `v(h no) ≤ r̄`, is **print's definition** and not a bound to prove: print says *"r̄ is the expected reward when not using the DB"*, and `rlAgent_actionValue_zero` is that expectation. (iii): `threshold_unattainable_of_one_le` shows that for `1 ≤ r̄ < 2` print's threshold exceeds every probability, so print's Statement is **vacuous** there rather than false, and `not_mixture_lt_of_threshold_without_rbar` shows that above `2` the comparison is **false** — so `r̄ < 1` is forced by print's own threshold and is not an added hypothesis. **All four derivations are at remaining depth zero, and that is print's own reading rather than a narrowing.** Print's bounds are rewards — *"the maximum possible reward"*, *"the expected reward when not using the DB"* — not sums of rewards, and at remaining depth `n` the same construction is worth `n + 1` rather than `1`, so print's constants are print's only one step ahead. `Wider` because `statement_one_of_posterior` quantifies over an arbitrary agent with bounded utility and an arbitrary pair of sub-probability beliefs, where print has its own agent and its universal prior. |
| Stmt. 2 | the goal-seeking agent will also use the delusion box | `DelusionBox.statement_two`, `DelusionBox.statement_two_of_posterior`, `DelusionBox.mixture_lt_of_gap`, `Mixture.posterior_nil`, `Examples.DelusionBox.goal_uses_the_box`, `Examples…goal_uses_the_box_of_posterior`, `shortHorizon_ahead`, `goalAgent_value_zero_snoc`, `goalAgent_actionValue_next_const`, `goalAgent_actionValue_zero_of_not_goal`, `Examples…goal_boxed_yes_eq`, `Examples…goal_boxless_no_zero`, `ReachedAtMostOnce`, `GoalOutOfReach`, `ReachesIn`, `goalAgent_value_le_shortHorizon`, `goalAgent_actionValue_le_of_outOfReach`, `shortHorizon_le_goalAgent_policyActionValue`, `Examples…goal_boxed_yes_ge`, `Examples…goal_slow_no_le`, `Examples…goal_gap` | Yes | **Wider** | print's threshold again: `(1/2)^l < p · (1/2)^k` is `P(DB) > 2^{\|o⁺\|-lᵃ}` with `k` for `\|o⁺\|` and `l` for `lᵃ`, and the witness takes `k = 1 < l = 2`, print's "easily satisfiable once `\|o⁺\| < lᵃ`". Narrower in the same four ways as Statement 1, and in one more: print *computes* `2^{-\|o⁺\|}` and `2^{-lᵃ}` from its universal prior and its goal predicate, and here they are hypotheses about the two actions' values. Note that print's bound on `v(h no)` has a different shape from Statement 1's — `2^{-lᵃ}` in **both** branches rather than `r̄` in one and the maximum in the other — which is why `mixture_lt_of_gap` is a second lemma rather than an instance of the first. Hypothesis (i) is refuted and its replacement built, as Statement 1's row records. **Repaired on 2026-09-19**: `statement_two_of_posterior` is this Statement with no decomposition hypothesis, by Statement 1's route at print's second comparison shape, and (iv) closes here too because the action compared against is the policy's. **Its antecedent needed a third environment and that is a fact about print's shape, not about the model.** Print bounds the refusing action by `2^{-lᵃ}` in *both* branches, where Statement 1 bounds it by `r̄` in one and the maximum in the other; against the negating environment refusing is worth the maximum here, so `Examples…goal_uses_the_box_of_posterior` inhabits it at an environment where refusing pays nothing either way, with `∣o⁺∣ = 1`, `lᵃ = 2` and prior `3/4` — print's *"easily satisfiable once `∣o⁺∣ < lᵃ`"*. **Closed 2026-09-20, and the cost note was wrong about the object.** It said print *computes* `2^{-\|o⁺\|}` and `2^{-lᵃ}` *"from its universal prior and its goal predicate"*. **The universal prior enters print's Statement 2 paragraph nowhere.** Both constants are values of print's goal-seeking horizon `w(t, k) = 2^{t-k}`: `shortHorizon_ahead` is `2^{-j}` at `j` steps ahead, and what the goal predicate supplies is *which* step. `goalAgent_actionValue_next_const` is print's `v(h yes) > P(DB) · 2^{-\|o⁺\|}` as an **equality** at `\|o⁺\| = 1` — programming the box to produce the goal observation is worth exactly that step's horizon weight — and Statement 1's two axes closed here too and by the same declarations. **And a third axis appeared on closing them, and closed the same day.** Statement 1's bounds are *rewards* — one-step quantities — so deriving them at remaining depth zero is print's own reading. Statement 2's are not: both of its constants are horizon weights of steps **later**, so both bounds have to hold at every depth. They now do. `ReachedAtMostOnce` is print's own side condition on the goal predicate, *"the goal can be reached at most once"*, recorded on the `A` sub `g` row since 2026-09-09 as a condition *nothing used*; `goalAgent_value_le_shortHorizon` is what it was stated for, and without it the bound fails by a factor of two because the weights sum to twice the first. `GoalOutOfReach` is print's `lᵃ` **relative to the belief** — print's `lᵃ` exceeds `\|o⁺\|` because the environment is slower, not because the goal is longer — and `goalAgent_actionValue_le_of_outOfReach` is print's `v(h no) < 2^{-lᵃ}` at every depth. `ReachesIn` and `shortHorizon_le_goalAgent_policyActionValue` are print's `v(h yes) > P(DB) · 2^{-\|o⁺\|}` at every `\|o⁺\|`, through a **committed policy** — the same object Statement 1's repair needed, because the maximum of equation (3) gives no lower bound. `Examples…goal_gap` is print's *"easily satisfiable once `\|o⁺\| < lᵃ`"* on a real pair, and on print's own case rather than a degenerate one: the box reaches the goal one step on and the slow environment reaches it **two** steps on — `lᵃ = 2 > 1 = \|o⁺\|`, with `Examples…slow_reachesIn_two` showing the goal is genuinely reached without the box — so the two bounds are `2^{-1}` against `2^{-2}`. The depth-zero lemma `goalAgent_actionValue_zero_of_not_goal` remains beside these as the case where the goal is never reachable at all; `goalAgent_actionValue_le_of_outOfReach` is the one print's argument needs. `Examples…goalNever_afterTrue` is print's *"at most once"* from the other side: once reached, the goal is out of reach forever. |
| Stmt. 3 | the prediction agent will use the delusion box | `DelusionBox.statement_three`, `DelusionBox.statement_three_of_posterior`, `ProgramPrior.Model.setMass`, `ProgramPrior.Model.weight_le_setMass`, `ProgramPrior.Model.weight_lt_setMass`, `ProgramPrior.Model.mass_eq_setMass`, `Examples.DelusionBox.pred_uses_the_box`, `Examples…pred_uses_the_box_of_posterior`, `Examples…weight_lt_setMass_univ` | Yes | **Wider** | print's threshold `P(DB) > 1/2` — print's own form of it — which is Statement 1's threshold at `r̄ = 0`, and not by accident: print's prediction bound gives the other action *no* value in the branch where a box is present, because there the true inner environment is the one being deluded away. `GlobalEnv.globalObs_indep_inner` is that obliteration, proved. Narrower in the same four ways, and in one more: print's step from its prior assigning the true environment less mass than the whole set of environments containing a box, so that convergence to that set takes fewer errors, to the agent believing a box is present with probability above one half, is a claim about a universal prior and a convergence rate, and it is not formalized — `p` is simply given. Hypothesis (i) is refuted and its replacement built, as Statement 1's row records. **Repaired on 2026-09-19**: `statement_three_of_posterior` is this Statement with no decomposition hypothesis, and it is `statement_one_of_posterior` at `r̄ = 0` exactly as `statement_three` is `statement_one` at `r̄ = 0`, so the repair inherits print's own reduction rather than repeating it. `Examples…pred_uses_the_box_of_posterior` inhabits it on the same pair as Statement 1. (iv) closes here too. **Closed 2026-09-20, and the convergence-rate axis is retracted rather than paid.** Print's *Arguments* run on two steps. The first is print's inequality between the true environment's weight and the mass of the class containing it, which is this paper's and is now proved: `ProgramPrior.Model.setMass` is print's `ρ(𝒬)` at a set of programs, `ProgramPrior.Model.weight_le_setMass` is the inequality, and `ProgramPrior.Model.weight_lt_setMass` is print's strict form, which needs a second member of positive weight — which a class of environments containing a delusion box has and a singleton would not. The second step, *"it takes fewer errors to converge to the class than to the true environment"*, rests on the sentence print writes immediately before the Statement: *"for an environment `q ∈ 𝒬`, a predictor makes approximately `−log(ρ(q))` errors [2]"*. **That is a cited theorem of another paper, not a claim of this one**, so it is not this section's to formalize and the row is not owed it; it would be graded where [2] is graded, which is nowhere yet. Statement 1's two axes closed here too, and this Statement is `statement_one_of_posterior` at `r̄ = 0` exactly as print's reduction is. `Wider` for the reason Statement 1's row is. |
| Stmt. 4 | the optimal knowledge-seeking agent will not consistently use the delusion box | `ProgramPrior.Model.knowledgeAgent`, `ProgramPrior.Model.mass`, `ProgramPrior.Model.relative_weight_le`, `DelusionBox.coherentKnowledgeAgent`, `AgentEquations.historyMass`; refuted at the untied agent by `Examples.DelusionBox.knowledge_uses_the_box`; coherence is not enough by `Examples.DelusionBox.coherent_uses_the_box`, `Examples.DelusionBox.deludedMass_ne_historyMass` | Partial | Same | **The layer this row was costed for landed on 2026-09-13.** What it asked for was a type of programs, a prior on it, and `ρ(h) := Σ_{q∈𝒬_h} ρ(q)`; `ProgramPrior.Model` is all three at print's page-2 setup, and `ProgramPrior.Model.knowledgeAgent` is print's `u(h) = -ρ(h)` for the agent's **own** program mass rather than for a parameter, so the statement is now stated at print's agent and not at a neighbour of it. `ProgramPrior.Model.relative_weight_le` is print's page-4 monotonicity — a surviving positive-weight program's relative share can only rise as observations discard others — which is the step its argument runs on. **The conclusion is still not proved, and that is why this row stays `Partial`.** The earlier separations are unaffected and are not evidence against print: `knowledge_uses_the_box` refutes the statement at the untied `DelusionBox.knowledgeAgent`, `deludedMass_ne_historyMass` shows that refutation does not instantiate at the coherent agent, and `coherent_uses_the_box` is at the mixture belief, which is not a prior over programs. **Nothing here exhibits print's own agent programming the box, and nothing here proves it does not** |
| §4, eq. (4) | the fully-modifiable agents, whose actions may rewrite their own utility and horizon functions | — | No | — | §4's self-modification setting is absent from this module. What the atlas has of self-modification is `AISafetyAtlas.Wireheading.GoalPreservationRun`, against a different source |
| Stmt. 5 | the fully-modifiable survival agent will stop exploring | — | No | — | §4's self-modification setting is absent |
| Stmt. 6 | under the stated conditions the optimal non-learning agent is a survival agent | — | No | — | as above |
| Stmt. 7 | the fully-modifiable knowledge-seeking agent cannot be reduced to a survival agent | — | No | — | as above |
| — | once the horizon weighting vanishes past the window, deepening the recursion changes nothing, and every value computed from a long enough history is zero | `AgentEquations.truncation_exact`, `AgentEquations.value_eq_zero_of_horizon_vanishes` | — | **Beyond** | print never raises the question of what its unfounded recursion means, so it states no truncation-error condition. These make the finite-horizon form honest rather than approximate, and they are cited in the equation (3) row for that reason as well |
| — | the finite-horizon value depends only on the utility and horizon weights inside the reachable window, so two agents may differ arbitrarily outside it and agree on it | `AgentEquations.value_eq_of_agree_on_window`, `Objective.value_eq_of_agree_on_window` | — | **Beyond** | the factorisation claim with content — its proof unfolds the recursion. Print observes that its four agents differ only in `(u, w)`; it does not state a locality property of the value in those components |
| — | the two-hypothesis decomposition all three Arguments paragraphs use is available exactly one step ahead, where equation (3)'s maximum has not yet entered the recursion, and equation (2)'s sum is linear in the belief | `DelusionBox.mixesAt_zero`, `Examples.DelusionBox.mixed_mixesAt` | — | **Beyond** | print never raises the question of whether its own decomposition follows from its own equations, so it states no condition under which it does. This one bounds the narrowing in the three Statement rows rather than leaving it unbounded: at remaining depth zero, where equation (3)'s maximum has not entered, `MixesAt` is a **theorem**, and the witness discharges it there. It is also what stops those three rows being implications nothing inhabits. **It is not a reconstruction of print.** Print's own values are the full recursion, so print applies the decomposition at every depth; only the depth-zero case is proved, nothing here shows the general case fails, and no claim either way is made |
| — | print's Statement 4 is **false** at an agent whose history mass is not the belief's own, so the tie between `u` and `ρ` is load-bearing rather than decorative | `Examples.DelusionBox.deludedMass`, `Examples.DelusionBox.knowledge_uses_the_box`, `Examples.DelusionBox.knowledge_bestAction_ne_no` | — | **Beyond** | print never asks what its knowledge-seeking agent does when the mass it minimises is *not* its own prior, because print never separates them. Separating them is what the atlas's `Agent`/`Belief` split does, and the separated agent takes the box. This is the witness the Statement 4 row above rests on: it converts a `No` that used to be graded on unmeasured cost into one graded on a model |
| — | the value is homogeneous in the utility component, and strictly positive rescaling preserves the set of optimal decisions | `Objective.value_scaleUtility`, `Objective.optimal_decisions_eq_of_pos_scaleUtility` | — | **Beyond** | not stated in print in any form. **`Objective.value_congr` and `Objective.optimal_decisions_congr` grade nothing anywhere in this table**: they are record congruence, their proofs never unfold the value, and they are named here so that no reader counts them as coverage |

**10 Yes, 3 Partial, 4 No, 5 Beyond**, regraded on 2026-09-20 from 7 / 6 / 4 / 5
when Statements 1, 2 and 3 all reached `Yes` and `Wider`, and the section's three
owed cells closed with them.

**What changed on 2026-09-10, and what did not.** The nine rows above that were
`No` on 2026-09-09 covered §3, the four agents, the optimal non-learning
variants, and Statements 1 to 3. Eight of them have moved. The earlier note here
said that formalizing them "needs the delusion box, four concrete agents, and a
universal prior"; the first two were right and the third was not. A universal
prior is needed for Statement 4 and for print's route *to* the threshold — its
convergence argument — but not for the comparison each of Statements 1 to 3
makes once the belief in a delusion box is given a number, which is what print's
own footnote 5 says it assumes.

**The three Statement rows were `Partial` until 2026-09-20 and are now `Yes`,
and nothing was folded into the agent to get there.** The grade existed to stop
exactly that: strengthening `rlAgent` until Statement 1 falls out would produce a
theorem true of a model nobody claimed. What changed is that the premises print's
*Arguments* paragraphs use without stating are now **derived from print's own
construction**, as separate theorems, with the agent still a parameter of the
Statement theorems.

The two-hypothesis decomposition went first, on 2026-09-19, and it went by being
**refuted** — print's fixed-weight average is not a mixture's value above
remaining depth zero — and replaced by a posterior and a committed policy. The
four branch bounds and `r̄ < 1` went on 2026-09-20. Three of the four bounds are
theorems about print's agent and the fourth is print's own definition of `r̄`;
`r̄ < 1` turns out to be forced by print's threshold rather than assumed, since
the threshold is unattainable just above one and the comparison is false above
two.

**A reader can now derive print's claim from the atlas** — for Statements 1 and
3 at print's own one-step reading, because print's bounds there are *rewards*
rather than sums of them, and the derivations are at remaining depth zero for
that reason. The Statement theorems themselves are at arbitrary depth and
quantify over an arbitrary agent with bounded utility, which is why those two
rows grade `Wider`.

**Statement 2 did not follow from the one-step reading, and the closing is what
showed it.** Both of its constants are horizon weights of steps *later*, so both
of its bounds have to hold at every depth, and the depth-zero derivations are the
degenerate case rather than print's. Both were then proved at every depth, and
doing so consumed the one thing in this paper that had been sitting unused since
the section was first graded: print's *"the goal can be reached at most once"*.
Without it the goal-seeking value exceeds the horizon weight of its own step by a
factor of two — the weights `2^{t-k}` sum to twice the first — and no single
`2^{-lᵃ}` bounds it. A side condition print states and never uses turns out to be
exactly what its own argument needs.

**What is still open, and what changed about how it is stated.** §4's
self-modification setting and Statements 5 to 7 are open and are not costed. §4
is a different setting from §3, and the atlas's self-modification work is
`AISafetyAtlas.Wireheading.GoalPreservationRun`, against a different source.

**Statement 4 moved from `No` to `Partial` on 2026-09-11**, and the conclusion
did not close. The cheap half of the costing is now a declaration:
`historyMass` and `coherentKnowledgeAgent` restore print's `u(h) = -ρ(h)` at
the observation layer, so the statement is instantiable at print's agent. The
expensive half is untouched: there is still no type of programs. `coherent_uses_the_box`
records that coherence at the mixture belief is not Statement 4 — the coherent
agent still programs the box there — so nobody should read the regrade as a
proof of print's positive claim.

**The companion paper now has a section.** This paper's reference [4] is
Orseau and Ring, *Self-Modification and Mortality in Artificial Agents*, AGI
2011, pinned in the project's literature directory as
`orseau-ring-authorversion-2011-self-modification-and-mortality-in-artificial-agents.pdf`.
Until 2026-09-10 it was entirely ungraded and this paragraph said so. It is
graded in **section 13**, and the two papers turn out to share their whole §2 —
the same three displayed equations, in a different printed order, and the same
four agents — so several of the declarations cited in this section are cited
there as well. Section 13's totals **do not re-count** this section's `Beyond`
rows, for that reason.

---

## 12. Everitt & Hutter 2016, arXiv:1605.03143v1 → `AISafetyAtlas.Wireheading.ValueLearning`

Graded for the first time on 2026-09-09, on a module built for it in the same
change. Before that the source had no atlas declaration of any kind.

**Which text.** arXiv:1605.03143v1, 10 May 2016, 21 pp., sha256
`a0a9a8c96a52131f297ee123fcabd8a11a24641a640d35592cd688f662fd37a9`. Every number
below is the arXiv version's. **The published chapter was obtained later the
same day**, at pp. 12–22 of the AGI 2016 proceedings volume LNAI 9782, sha256
`4486e912ea2c0ed387bfaa4eaaf431db39ae2f362902fb880f5f2bc14d18d403`, and here the
two versions do **not** renumber: Definitions 2/3/5/7/8/9/10/11/12, Assumptions
4/6/15, Lemma 13 and Theorem 14 carry the same numbers in both, and equation (1)
— the utility posterior `Beliefs.posterior` renders — is equation (1) in both,
with identical text. The chapter carries no appendix, so the Lemma 27 row below
is graded against a statement the chapter itself delegates outward, citing it as
"(Everitt and Hutter 2016, Lemma 27)". This is
the companion of §10's source — consecutive arXiv identifiers, same day, same
venue — and the two cite each other.

**Two axes run through the section and are not repeated in each note.**

* **The utility class is finite — which is one of print's two cases, not a bound
  print never wrote.** *Corrected 2026-09-10.* This bullet used to say print
  "never bounds" the class `𝒰`. It does: p. 4, in the paragraph immediately
  before Definition 2, reads *"We also assume that `R`, `S`, and `U` are finite
  **or countable**. Finally, to ensure well-defined expectations, we assume that
  `R` is bounded if it is countable."* So print states two cases for all three
  types, and the atlas formalizes the first of them. Every sum here is a `Finset`
  sum over a `Fintype`, which is print's finite case exactly and reaches none of
  its countable one; Definition 3, Definition 9, Definition 12, Lemma 13 and
  Theorem 14 are `Narrower` for that reason and not for the one previously given.
  The countable case would need a summability layer this cluster does not have,
  and print's boundedness proviso is where that layer would attach.
* **Utility functions are indexed rather than extensional.** `Utility` is an
  index type with an evaluation map, so two indices may name the same function.
  Every statement here quantifies over an index and reads it only through its
  evaluation and its prior mass, so nothing is affected; a **cardinality** claim
  about the class would not transfer, and none is made.

**One thing the atlas does that print does not, and it is not a widening.**
Equation (1) divides by the reward marginal. Division by zero in Lean is zero,
so a state-and-reward pair with vanishing marginal but non-vanishing numerator
would falsify Lemma 13 in Lean while being unreachable in print's reading.
`Beliefs` carries nonnegativity of the prior and of the state belief as structure fields — print
calls both objects distributions, and this is the only part of that used — and
`Beliefs.prior_mul_condReward_eq_zero_of_marginal_eq_zero` squeezes every
numerator in the vanishing case. The result is that Lemma 13 and Theorem 14
carry **no side condition on their statements**. Handling a junk value is
coverage, not generality, so it moves no scope cell.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Ex. 1 | a chess agent that wireheads by subverting its own referee | — | No | — | an informal scenario |
| Def. 2 | self-delusion types: non-delusional, self-deluding, and the identity delusion | — | No | — | the atlas models the *belief disagreement* a delusion produces, not the delusion. This is the object §6 and the appendices are built on, and none of that is formalized |
| Def. 3, eq. (1) | the utility prior, the reward-given-utility indicator, the reward marginal, and the utility posterior | `Beliefs.condReward`, `Beliefs.marginalReward`, `Beliefs.posterior`, `Beliefs.sum_condReward` | Yes | Same | the indicator, the marginal and equation (1) transcribed. Print's own replacement of the inner reward by the observed reward is taken as done, since it says so immediately after the display and every later statement uses the replaced form. **The finiteness axis closed 2026-09-13.** Print's setup page says *"we also assume that `ℛ`, `𝒮`, and `𝒰` are finite or countable"*, and the atlas took the finite case with `[Fintype State] [Fintype Reward] [Fintype Utility]`. Every sum in the module is now unconditional over arbitrary types. Nothing was added to `Beliefs`: summability of `C`, and of the joint family Theorem 14 exchanges, are hypotheses of the results that need them and of no others, and at a `Fintype` each is `Summable.of_finite`, so the previous signatures are instances. **The grade rests on a fact this tree does not prove**: `∑'` is zero by convention at a non-summable family, and print's own route from countability plus its bounded `ℛ` to summability is not formalized here. |
| Asm. 4 | the belief distributions are consistent on non-delusional states | — | No | — | needs Definition 2's delusion types. The atlas never assumes it; `IsCP` is the property print says is checkable *without* it |
| Def. 5, eq. (3) | an action is consistency preserving when, at every state it can reach, the reward belief equals the reward marginal | `Beliefs.IsCP` | Yes | Same | print displays the implication with the state free and prefixes "for all `r ∈ R`"; the proof of Lemma 13 reads it back as holding for all states the action can reach, so both variables are universally quantified and `IsCP` quantifies both |
| Asm. 6 | the agent has at least one consistency-preserving action | — | No | — | print's assumption. The atlas never carries it, because no theorem here quantifies over the set of consistency-preserving actions — Definition 11 is a predicate on an action rather than a selection from a set. `AISafetyAtlas.Examples.Wireheading.ValueLearning` shows it satisfiable in a two-state model, which is a witness and not the assumption |
| Def. 7 | the RL agent maximises the reward-weighted value | `Beliefs.rlValue`, `Beliefs.IsRLAction` | Yes | Same | the value function and its argmax |
| Def. 8 | the utility-`u` agent maximises expected utility | `Beliefs.utilityValue`, `Beliefs.IsUtilityAction` | Yes | Same | as above |
| Def. 9 | the VRL value of an action is the expected utility under the posterior | `Beliefs.vrlValue` | Yes | Same | Definition 9, the VRL value function, transcribed. **The finiteness axis closed 2026-09-13.** Print's setup page says *"we also assume that `ℛ`, `𝒮`, and `𝒰` are finite or countable"*, and the atlas took the finite case with `[Fintype State] [Fintype Reward] [Fintype Utility]`. Every sum in the module is now unconditional over arbitrary types. Nothing was added to `Beliefs`: summability of `C`, and of the joint family Theorem 14 exchanges, are hypotheses of the results that need them and of no others, and at a `Fintype` each is `Summable.of_finite`, so the previous signatures are instances. **The grade rests on a fact this tree does not prove**: `∑'` is zero by convention at a non-summable family, and print's own route from countability plus its bounded `ℛ` to summability is not formalized here. |
| Def. 10 | the unconstrained VRL agent takes the action of highest VRL value | `Beliefs.IsUVRLAction` | Yes | Same | a predicate on an action rather than a chosen action, which is the same content without an attainment assumption print does not make either |
| Def. 11 | the consistency-preserving VRL agent maximises the VRL value over consistency-preserving actions | `Beliefs.IsCPVRLAction` | Yes | Same | the predicate carries both halves: the action is itself consistency preserving, and no consistency-preserving action beats it |
| Def. 12, eq. (4) | an action is expected-ethics preserving when the expected posterior equals the prior at every state it can reach | `Beliefs.IsEEP` | Yes | Same | Definition 12 transcribed. **The finiteness axis closed 2026-09-13.** Print's setup page says *"we also assume that `ℛ`, `𝒮`, and `𝒰` are finite or countable"*, and the atlas took the finite case with `[Fintype State] [Fintype Reward] [Fintype Utility]`. Every sum in the module is now unconditional over arbitrary types. Nothing was added to `Beliefs`: summability of `C`, and of the joint family Theorem 14 exchanges, are hypotheses of the results that need them and of no others, and at a `Fintype` each is `Summable.of_finite`, so the previous signatures are instances. **The grade rests on a fact this tree does not prove**: `∑'` is zero by convention at a non-summable family, and print's own route from countability plus its bounded `ℛ` to summability is not formalized here. |
| Lem. 13 | any consistency-preserving action is expected-ethics preserving | `Beliefs.isEEP_of_isCP`, `Beliefs.prior_mul_condReward_eq_zero_of_marginal_eq_zero` | Yes | Same | print's proof, unchanged: substitute the consistency identity, cancel the marginal, and marginalise the reward out. The division hazard is handled as described above and costs the statement nothing; the squeeze lemma now carries summability of `C`, which is print's own assumption that `𝒰` is countable with a prior on it. **The finiteness axis closed 2026-09-13.** Print's setup page says *"we also assume that `ℛ`, `𝒮`, and `𝒰` are finite or countable"*, and the atlas took the finite case with `[Fintype State] [Fintype Reward] [Fintype Utility]`. Every sum in the module is now unconditional over arbitrary types. Nothing was added to `Beliefs`: summability of `C`, and of the joint family Theorem 14 exchanges, are hypotheses of the results that need them and of no others, and at a `Fintype` each is `Summable.of_finite`, so the previous signatures are instances. **The grade rests on a fact this tree does not prove**: `∑'` is zero by convention at a non-summable family, and print's own route from countability plus its bounded `ℛ` to summability is not formalized here. |
| Thm. 14, eq. (5) | for the consistency-preserving VRL agent the value function reduces to the prior-weighted expected utility | `Beliefs.vrlValue_of_isCP`, `Beliefs.vrlValue_of_isEEP` | Yes | Same | the reward evidence has disappeared from the right-hand side, which is the whole point: no choice among such actions can be motivated by what the reward channel would report. Stated for expected-ethics-preserving actions and specialised to consistency-preserving ones, which is print's own order of argument. **The finiteness axis closed 2026-09-13.** Print's setup page says *"we also assume that `ℛ`, `𝒮`, and `𝒰` are finite or countable"*, and the atlas took the finite case with `[Fintype State] [Fintype Reward] [Fintype Utility]`. Every sum in the module is now unconditional over arbitrary types. Nothing was added to `Beliefs`: summability of `C`, and of the joint family Theorem 14 exchanges, are hypotheses of the results that need them and of no others, and at a `Fintype` each is `Summable.of_finite`, so the previous signatures are instances. **The grade rests on a fact this tree does not prove**: `∑'` is zero by convention at a non-summable family, and print's own route from countability plus its bounded `ℛ` to summability is not formalized here. |
| Asm. 15 | the agent self-deludes only deliberately | — | No | — | needs Definition 2 |
| Ex. 16 | consistency-preserving VRL chess, informally | — | No | — | an informal scenario |
| Def. 17 | the inner state, the part of the state a delusion does not touch | — | No | — | appendix apparatus, absent |
| Ex. 18 | the unconstrained VRL agent wireheads indirectly | — | No | — | an informal scenario. Its *content* — that the unconstrained agent has an incentive the constrained one lacks — is exhibited concretely in `AISafetyAtlas.Examples.Wireheading.ValueLearning`, where a non-consistency-preserving action has strictly higher VRL value than every consistency-preserving one. That is a worked model, not a formalization of this example |
| Ex. 19 | the consistency-preserving VRL agent avoids the delusion of Example 18 | — | No | — | as above |
| Lem. 20 | the assumptions hold when the belief correctly specifies the delusion | — | No | — | appendix apparatus, and it needs Definition 2 |
| Def. 21 | an inner-state-based utility function | — | No | — | appendix apparatus, absent |
| Thm. 22 | an inner-state-based utility function gives no direct wireheading | — | No | — | absent |
| Ex. 23 | a reward-maximising utility agent | — | No | — | absent |
| Cor. 24 | if the class contains only inner-state-based utility functions there is no wireheading | — | No | — | absent |
| Thm. 25 | approximately inner-state-based utility functions give approximately no direct wireheading | — | No | — | absent, and the atlas has no approximation layer anywhere in this cluster |
| Def. 26 | convolutional utility functions | — | No | — | absent |
| Lem. 27 | the unconstrained VRL agent is the RL agent | `Beliefs.posterior_expectation`, `Beliefs.vrlValue_eq_rlValue`, `Beliefs.vrlValue_eq_rlValue_of_isCP`, `Examples.Wireheading.ValueLearning.blindModel_not_supported`, `Examples.Wireheading.ValueLearning.blindModel_vrlValue_ne_rlValue` | Yes | Same | **Regraded from `Partial`/`Narrower` on 2026-09-18, and the old reason is refuted rather than restated.** The row read `Narrower` because the value identity is proved under a **support condition** — at any state the action can reach, wherever the reward belief is nonzero the reward marginal is nonzero — and print states the identity unconditionally. The condition is not an atlas addition: print's equation (1) *defines* the posterior as `C(u) C(r ∣ s,u) / C(r ∣ s)`, so at a reward the utility class can never produce the divisor is zero and print's own `V(a)` is undefined. The support condition names exactly print's domain of definition, and it is guarded by reachability exactly as print's Definitions 5 and 12 are. **The witness settles that it is not removable.** `blindModel` is one state, one action, one utility and two rewards, with the utility valuing the state at reward `0` while the sensor reports reward `1` with certainty; `blindModel_not_supported` shows the condition fails at a reachable state, and `blindModel_vrlValue_ne_rlValue` shows the conclusion fails with it, `0 ≠ 1`. So the unconditional reading is a *false* statement, not a wider one, and the atlas is not narrower than print but coextensive with it. the sensor-belief and reward-marginal fields of `Beliefs` are independent, so the hypothesis was never derivable and the note that called the row `Partial` was pricing a gap that does not exist. `vrlValue_eq_rlValue_of_isCP` still discharges the condition outright for a consistency-preserving action |
| — | for a consistency-preserving action the VRL value is the prior mixture of the utility agents' values | `Beliefs.vrlValue_eq_prior_mixture` | — | **Beyond** | Theorem 14's right-hand side with the sums exchanged. Print does not display it, and it is what makes "the constrained agent is a utility agent under the prior" precise rather than suggestive |
| — | the reward marginal is nonnegative and dominates each of its summands, and the reward-given-utility indicator is a probability mass function | `Beliefs.marginalReward_nonneg`, `Beliefs.prior_mul_condReward_le_marginal`, `Beliefs.sum_condReward` | — | **Beyond** | the apparatus that makes the division in equation (1) safe, and the small lemmas that pin the transcribed definitions down so a reader can see what they do without unfolding a proof |

**11 Yes, 0 Partial, 16 No, 2 Beyond.**

**What is open.** Everything after §5: the delusion types of Definition 2 and
the whole appendix development built on them, and any sequential agent. Print's
own Table 1 caption records the design question this leaves — how to specify a
utility prior consistent with a real reward channel — as open, and nothing here
bears on it.

---

---

## 13. Orseau & Ring 2011, AGI-11, author version → `AISafetyAtlas.Wireheading.Objective`

Graded for the first time on 2026-09-10. It was pinned on 2026-09-09 and section
11 recorded, correctly, that nothing in this table covered it.

**The heading names the same target module as section 11**, and that is not a
slip. Every declaration cited below lives in
`AISafetyAtlas.Wireheading.AgentEquations` or
`AISafetyAtlas.Wireheading.DelusionBox`, and the registry row that hosts both is
`LAND-WIRE-OBJ-001`, whose module is `AISafetyAtlas.Wireheading.Objective`. Two
sections sharing a target is what it looks like when two papers share a section,
which is exactly what happened here.

**Which text.** `orseau-ring-authorversion-2011-self-modification-and-mortality-in-artificial-agents.pdf`,
sha256 `e211682aa5cc9e1bcd7f0a277030a4a909ff52695ff4e1d0fa3905d9b223b52d`, manifested
 2026-09-09. Ten pages by its own page numbering and its
own `pdfinfo`; Producer pdfTeX-1.40.10, CreationDate 2011-03-03. Title and
authors are read off page 1: *Self-Modification and Mortality in Artificial
Agents*, Laurent Orseau (UMR AgroParisTech 518 / INRA) and Mark Ring (IDSIA).
**This is an author version and it has not been compared with the Springer
chapter** (LNAI 6830). No statement here is about the published text. Page
images were read; `pdftotext` was used only for navigation, because this
project has been bitten by AMS fonts with no *ToUnicode* map.

**It is one half of a double paper, and the atlas already had the other half.**
Its footnote 3 reads: "This paper is part one of a 'double paper' submission. It
should stand on its own, but both papers may be found at
http://www.idsia.ch/~ring/AGI-2011." The other half is Ring and Orseau,
*Delusion, Survival, and Intelligent Agents*, graded in section 11. **Their §2 is
the same section.** Same three displayed equations, same `ρ`, `u`, `w`, same four
agents, same lexicographic tie-breaking footnote. So the declarations section 11
cites for §2 cover §2 here as well, and this section cites them again. Its
`Beyond` rows are **not** re-counted in the totals table, for that reason.

**Three differences from the companion, all checked against both files, none of
them adjudicated here.**

1. **The equation numbers are permuted.** In this paper (1) is the value of a
   history, (2) is the value of an action, and (3) is the `argmax`. In the
   companion (1) is the `argmax`, (2) is the value of an action, and (3) is the
   value of a history. The equations themselves are the same three.
2. **The action index convention is this file's.** It prints
   *a_{|h|} := argmax_a v_{|h|}(ha)*, the `|h|` convention. Section 11 records
   that the HAL copy of the companion uses `|h| + 1` with *t_h* defined, and a
   second author draft of the companion uses `|h|`. This file agrees with the
   second draft. The atlas's `t` is a parameter, so both instantiate it.
3. **Two of the four agents carry different horizon functions from the
   companion's**, and this matters for the grades below. Print here sets the
   goal-seeking agent's horizon to the constant `w(t,k) = 1`, saying it "is not
   necessary, does not need to be summable"; the companion prints `2^{t-k}`, and
   `DelusionBox.shortHorizon` is the companion's. Print here sets the
   knowledge-seeking agent's horizon to `w(t,k) = 1 if k + t = m`; the companion
   prints `k - t = m`, and `DelusionBox.spikeHorizon` is the companion's. **No
   view is taken here on which is intended.** `k + t = m` at a fixed `m` selects
   no future step at all once `t > m/2`, and the surrounding prose says "a single
   distant step", which reads like the companion's condition; but this section
   grades what this file prints, and what it prints is not what the atlas
   implements.

**The paper prints no theorem, lemma or definition environment**, exactly as the
companion does not. Its six numbered items are **Statements**, each followed by a
paragraph headed *Arguments*, and it says why on page 2: "generally framing our
observations as 'statements' and (strong) 'arguments', as proofs would require
much more formalism and space."

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §2, eq. (1) | the value of a history is the horizon-weighted utility plus the maximum over actions of the value of the extended history | `AgentEquations.value`, `AgentEquations.value_succ`, `AgentEquations.truncation_exact`, `AgentEquations.value_eq_zero_of_horizon_vanishes`, `AgentEquations.infiniteValue`, `AgentEquations.tendsto_value_infiniteValue`, `AgentEquations.infiniteValue_eq`, `AgentEquations.value_error_le_tail` | Partial | **Wider** | the companion's equation (3), verbatim. `value_succ` is it with equation (2) substituted, at a remaining depth. The two equations are mutually recursive with no base case. **The missing-limit axis closed 2026-09-13.** `AgentEquations.infiniteValue` is the limit of the finite-depth values, `AgentEquations.tendsto_value_infiniteValue` proves it is one, `AgentEquations.value_error_le_tail` certifies the truncation error uniformly at every history of a given length, and `AgentEquations.infiniteValue_eq` is this equation **at that limit**. The operators the finite form uses now denote rather than defaulting: `AgentEquations.actionValue_summable` and `AgentEquations.actionValue_bddAbove` discharge, at print's own conditions, the two implications this file recorded on 2026-09-13 as resting on nothing. **Bounded is not attained**: `AgentEquations.Attains` is still a hypothesis and is not derived from the bound, so where print's maximum is not attained the two still differ. **Every hypothesis it is built on is this paper's own, on its page 2**: *"ρ : 𝒬 → (0,1] assigns a positive weight"* with *"ρ(h) := Σ_{q∈𝒬_h} ρ(q), which must be finite"*, *"u : ℋ → [0,1]"*, and *"In general, it must be summable: Σ_{k=t}^∞ w(t,k) < ∞"* — the summability clause this row recorded as not imposed. Wider in the utility codomain: the utility field of `AgentEquations.Agent` is real-valued with no range invariant |
| §2, eq. (2) | the value of an action is the prior-weighted sum over observations of the values of the resulting histories | `AgentEquations.actionValue`, `AgentEquations.Belief` | Yes | **Wider** | the companion's equation (2), verbatim. The sum is print's. **The observation axis closed 2026-09-13**, for the reason and by the route the companion section's row for this equation gives; wider in that `Belief.cond` is an arbitrary real weight where print's `ρ(o ∣ ha)` is a probability **The grade rests on a fact this tree does not prove.** `∑'` is the unconditional sum, which is zero by convention at a family that is not summable; at print's own hypotheses — `ρ` a probability, `u : ℋ → [0,1]`, `w` summable — the family is summable and the value is print's, and that implication is not formalized here. `actionValue_eq_sum` covers the finite case only. Recorded the way §8's Definition 6 row records its walk-versus-path fact, and for the same reason. |
| §2, eq. (3) | the agent takes the action maximising the value of the extended history | `AgentEquations.bestAction`, `AgentEquations.bestAction_max` | Yes | Same | the companion's equation (1), verbatim. `bestAction` chooses an action attaining the maximum and `bestAction_max` proves it maximal. **The action axis closed 2026-09-13** by the companion section's route: `Action` was a nonempty `Fintype` where print writes `max` over an unqualified `A`, and equation (1) is now stated at the hypothesis `Attains`, which is what print presupposes by writing an argmax, with `attains_of_fintype` recovering the finite case. The companion section's row for equation (1) carries what the new grade rests on and this row inherits it. Print breaks ties lexicographically (footnote 5) and the atlas breaks them by choice |
| §2, `ρ` and `Q` | the universe is a program `q ∈ Q`; `ρ : Q → (0,1]` weights programs, `Q_h` is the set consistent with `h`, and `ρ(h) := Σ_{q ∈ Q_h} ρ(q)`, which must be finite | — | No | — | **the atlas has no program layer and no prior over one.** `AgentEquations.Belief` is a conditional weight on the next observation and nothing else, so `Q`, `Q_h` and `ρ(h)` have no counterpart. This is the remaining half of the companion's Statement 4, now graded Partial there: the observation-level tie `u(h) = -ρ(h)` is built, and the program prior is not |
| §2.1, `A_rl` | the reinforcement-learning agent: utility is the last reward, horizon weight one inside a window | `DelusionBox.rlAgent`, `DelusionBox.windowHorizon`, `DelusionBox.lastReward` | Yes | **Wider** | identical to the companion's `A_rl` and graded identically there: print's `w(t,k) = 1` exactly when `k - t ≤ m`, written here as `k ≤ t + m` to avoid truncated subtraction. Wider on two axes — the reward is read off an observation by an arbitrary function where print fixes *o_t = ⟨õ_t, r_t⟩* and takes the second component, and the utility is real-valued where print's is in `[0,1]` |
| §2.1, `A_g` | the goal-seeking agent: utility one exactly when the goal is achieved at the current step, **horizon constant one** | `DelusionBox.companionGoalAgent`, `DelusionBox.unitHorizon`, `DelusionBox.goalAgent_horizon_ne` | Yes | Same | the utility half is print's, and is the companion's too. **The horizon half closed 2026-09-13.** Print says here, on its page 4: *"The goal can be reached at most once, so Σ_{t=0}^∞ u(h_t) ≤ 1. For this utility function, the horizon function is not necessary, does not need to be summable, and can be set to 1: w(t, k) = 1."* `DelusionBox.goalAgent` fixes `DelusionBox.shortHorizon`, which is the *companion's* `2^{t-k}`, so it was the other paper's agent and not this one's. `DelusionBox.companionGoalAgent` is this paper's, at `DelusionBox.unitHorizon`; `companionGoalAgent_utility_eq` records that the two share a utility and `goalAgent_horizon_ne` that the horizons differ at `t = 0, k = 1`, so neither record covers the other paper's agent and the object rule is satisfied by a record rather than by a proxy. Print's side condition that the goal is reached at most once is a condition on `g` and is still not imposed, which widens the record rather than narrowing it, and nothing below assumes the trajectory sum is bounded |
| §2.1, `A_p` | the prediction-seeking agent: utility one on a correct prediction | `DelusionBox.predictionAgent` | Yes | **Wider** | identical to the companion's, and graded identically: wider in that the prediction is an arbitrary function of the history before the observation arrived, where print takes it to be Solomonoff induction's *ô_t = f(h)* |
| §2.1, `A_k` | the knowledge-seeking agent: utility is the negated prior mass of the history, **horizon one exactly when `k + t = m`** | `ProgramPrior.Model.knowledgeAgent`, `ProgramPrior.Model.companionKnowledgeAgent`, `DelusionBox.companionSpikeHorizon`, `DelusionBox.knowledgeAgent`, `DelusionBox.spikeHorizon` | Yes | **Wider** | **Both halves closed 2026-09-13.** The utility half: the mass was a parameter where print's is `ρ(h)` for the agent's own `ρ`, and `ProgramPrior.Model.knowledgeAgent` is now print's `u(h) = -ρ(h)` at the program mass this paper defines on its page 2. The horizon half: `DelusionBox.spikeHorizon` writes `k = t + m`, the *companion's* `k - t = m`, and **this paper prints `k + t = m`**; `DelusionBox.companionSpikeHorizon` is this paper's literal reading and `ProgramPrior.Model.companionKnowledgeAgent` is the agent at it. Difference 3 above still takes no view on which indexing is meant — **both are carried, and carrying both is not a view**, with `DelusionBox.knowledgeAgent_horizon_ne` recording that they differ at a future step. `Wider` because the prior is an arbitrary summable nonnegative weight where print's is a universal prior strictly positive on `𝒬`, so every statement here holds of print's `ρ` and of more besides |
| §2.1, `A^μ` and asymptotic optimality | the optimal non-learning agent knows the true program `μ` and is defined by (1)–(3) with `ρ` replaced by `μ` **in the value equations only, not in the utility functions**; a learning agent is asymptotically optimal if its number of mistakes against `A^μ` tends to zero | `DelusionBox.diracBelief`, `DelusionBox.actionValue_diracBelief`, `ProgramPrior.Model.point`, `ProgramPrior.Model.point_belief_eq`, `ProgramPrior.Model.value_point_eq` | Partial | Same | `actionValue_diracBelief` is equation (2) at a belief concentrated on what one environment produces: the sum over observations collapses. **The program-layer axis closed 2026-09-13.** `ProgramPrior.Model` is print's page-2 setup: `ProgramPrior.Model.Consistent` is its `𝒬_h` — *"a program q is consistent with h ... means that the program outputs the observations in the history if it is given the actions as input"* — and `ProgramPrior.Model.mass` is its `ρ(h) := Σ_{q∈𝒬_h} ρ(q)`, summable because print says that sum *"must be finite"*. `ProgramPrior.Model.mass_eq_historyMass` joins it to the observation layer rather than leaving the two parallel, and `ProgramPrior.Model.belief_isSubprobability` is what the value bounds consume. `ProgramPrior.Model`'s weight field is nonnegative where print's `ρ : 𝒬 → (0,1]` is strictly positive, and that is not a liberty taken against this row: print's own `μ` for the optimal variant is the weight that is one at its own true program and zero elsewhere, so a prior class closed under that is what the row needs. Print's `μ` is concentrated on a *program*, and `ProgramPrior.Model.point` is that concentration, with `ProgramPrior.Model.point_belief_eq` and `ProgramPrior.Model.value_point_eq` showing it induces this section's observation-level belief and the same values on every history the true program explains. Print's own proviso that `ρ` is replaced by `μ` **in the value equations only, not in the utility functions** is respected: only the belief changes. **Still `Partial`**, and on the other count only: **asymptotic optimality is absent entirely** — there is no mistake count anywhere in the cluster, and print's own §4 opens by saying the notion "becomes ill defined" for self-modifying agents |
| §3, `A_sm` | the self-modifiable agent is a code *c_t ∈ C* and a code executor *E*, with *y_t = ⟨a_t, c_t⟩ := E(c_{t-1})*; `C` holds all programs shorter than a fixed bound | `SelfMod.Exec`, `SelfMod.CompAct`, `Examples…Prog`, `Examples…prog_length_lt`, `Examples…exists_argmax_printValue_prog` | Yes | **Wider** | `Exec` is print's executor and `CompAct` is print's `⟨a, c⟩`. Closed 2026-09-11. **The code-set axis closed 2026-09-19.** `Examples…Prog` is print's `C` itself — the programs over a two-symbol language shorter than a bound — and `Examples…prog_length_lt` is print's defining property of it, so the set is recovered as an object and not only as an arbitrary type. It is recovered where print uses it: `Examples…exists_argmax_printValue_prog` is equation (4)'s attainment over print's own `A × C`, so the finiteness the argmax rests on is print's length bound rather than an added hypothesis. `Wider` because the library keeps `Code` an arbitrary type, of which print's bounded set is one instance. **Print's footnote 7 variant is not carried**: it offers a `C` that grows with `t`, and nothing here is indexed by time. GoalPreservation remains a different model against a different source, and no bridge is claimed |
| §3, eq. (4) | the initial program *c_0*: the maximised argument is the compound action `y = ⟨a,c⟩`, and the value function uses *c* to generate the compound action at the next step | `SelfMod.printValue`, `SelfMod.printValue_zero`, `SelfMod.printValue_succ_eq`, `SelfMod.smValue_eq_printValue`, `SelfMod.exists_argmax_printValue`, `SelfMod.IsInitialProgram`, `SelfMod.smValue_le_of_isInitialProgram`, `SelfMod.abs_printValue_succ_sub_le`, `SelfMod.printInfiniteValue`, `SelfMod.tendsto_printValue_printInfiniteValue`, `SelfMod.printValue_error_le_tail`, `SelfMod.IsInitialProgramLimit`, `SelfMod.exists_argmax_printInfiniteValue`, `SelfMod.smValue`, `SelfMod.smInfiniteValue`, `Examples…stay_isInitialProgramLimit`, `Examples…not_exists_isInitialProgram_alwaysSimpleton`, `Examples…printInfiniteValue_eq_smInfiniteValue_stays` | Yes | **Wider** | **Closed 2026-09-19, at three axes, one of which this row had not named.** (i) *The argument.* Print's `v` takes the **compound action** `y`, and in print the halves of `y = ⟨a, c⟩` are independent: `a` drives `ρ(o ∣ ha)` here, `c` only generates the compound action next. `smValue` takes a **code**, so it ranges over the image of `E(·, h)` and not over print's `A × C` — which is exactly the set equation (4) maximises over. That second narrowing was not recorded before 2026-09-19 and is closed by the same work: `printValue` is print's signature and `smValue_eq_printValue` identifies `smValue` as its restriction to the diagonal `y = E(c, h)`. (ii) *The argmax.* `exists_argmax_printValue` attains the maximum over print's finite `A × C`, `IsInitialProgram` is print's `c₀` condition at print's own `t := ∣h∣`, and `smValue_le_of_isInitialProgram` is what it buys. (iii) *Depth.* The print form now has the limit the through-code form got on 2026-09-14, by the same Cauchy route and at parity: `abs_printValue_succ_sub_le`, `printInfiniteValue`, `tendsto_printValue_printInfiniteValue`, `printValue_error_le_tail`, and `IsInitialProgramLimit` with `exists_argmax_printInfiniteValue`, so `c₀` is stated at the untruncated `v` print actually maximises rather than at a truncation. **Attainment is not existence, and the row says so because print does not.** `printValue` mentions `E` in its continuation, so the function being maximised moves when the executor does: existence of a code realising the argmax is a fixed point on the pair `(E, c₀)`, which print's `»...«` quotation and its footnote 8 assume away. Both sides are witnessed. `Examples…stay_isInitialProgramLimit` exhibits one, and `Examples…not_exists_isInitialProgram_alwaysSimpleton` exhibits a model with `A` and `C` both finite — so the argmax is attained — in which **no** code is an initial program, because the executor's image misses the maximiser. `Examples…printInfiniteValue_eq_smInfiniteValue_stays` cross-checks the two renderings at the limit against the value this row already carried. `Wider` on two axes: the utility codomain is real where print's is `[0,1]`, as elsewhere in this section; and `ρ` conditions on the whole compound action, which is print's Fig. 1(b) and contains its Fig. 1(a), where the environment cannot read `c`. **Statement 1 is still No** and this does not touch it. |
| §3, `A_s` | the survival agent: *u_t = 1 ⟺ c_t = c_0* and *0* otherwise, horizon as `A_rl` | `SelfMod.survivalUtility`, `SelfMod.survivalAgent` | Yes | **Same** | print's utility, read off the code half of the last compound action, and print's `A_rl` window horizon. Empty history scores one: nothing has modified the initial code |
| Stmt. 1 | `A^ρ_sm` is optimal, w.r.t. `ρ`, `w` and `u` | — | No | — | **and the substrate is not the reason.** The *Arguments* turn on the Kolmogorov complexity `K(c*)` of a better program, and the atlas has plain Kolmogorov complexity: `Kolmogorov.plainKNat`, `Kolmogorov.Map` and `Kolmogorov.isOptimalConditional`, vendored, reached through `AISafetyAtlas.Logic`. The code type and executor are now in `AISafetyAtlas.Wireheading.SelfMod`; what is missing is the tie between the program set and the belief, and the Kolmogorov-complexity comparison itself. The argument also needs `C` to grow with the history length, which print's footnote 7 offers as a variant of its own definition rather than as the definition |
| §4, eq. (5) | the environment has read-only access to the code: the action is the compound *a_t = ⟨a'_t, c_t⟩ ∈ A' × C*, and *c_0* is restated over it | — | No | — | **the shape is present and the semantics are not**, which is worth saying because the near-miss is close enough to mislead. `DelusionBox.Act` is a product of a program type with an ordinary action type, carried inside the action so the environment reads it — print's `A' × C` exactly. But the program of `AISafetyAtlas.Wireheading.DelusionBox` is a rewrite of the agent's *observations*, and print's *c* is the agent's own next *definition*. `GlobalEnv.innerHistory_congr_innerAction` is a theorem about the former and says nothing about the latter |
| §4, the Simpleton Gambit | the environment offers unbounded utility in exchange for the agent replacing its code with a simpleton *⟨0, c_{t-1}⟩* that can take only one action | — | No | — | a construction, not a claim, and it is the construction every one of Statements 2 to 6 is about. Absent for the same reason §3 is |
| Stmt. 2 | the `A^ρ_rl` agent cannot be optimal in all environments | — | No | — | absent; §4's setting is absent |
| Stmt. 3 | the `A^μ_{sm,rl}` and `A_{sm,rl}` agents accept the Simpleton Gambit | — | No | — | absent, and the atlas's nearest arithmetic does **not** apply. Print's bounds are *v_t(h yes) ≥ m ρ(q_A)* and *v_t(h no) ≤ m(ρ(Q_h) − ρ(q_A))*, so its threshold *ρ(q_A) > ρ(Q_h)/2* closes the comparison in one step from two absolute bounds, not from a two-branch mixture. `DelusionBox.mixture_lt_of_threshold` and `mixture_lt_of_gap` are the companion's *mixture* shape and neither is print's step here. The content of this Statement is the self-modifying agent, which does not exist in the atlas |
| Stmt. 4 | the `A_{sm,g}` agents accept the Simpleton Gambit, for some goals | — | No | — | absent. Print's argument reaches the same *ρ(q_A) > ρ(Q_h)/2* threshold "as for `A_{sm,rl}`", after an exhaustion step — "if it exhausts all such possibilities … the only remaining ones are to modify itself" — which is a claim about the prior and is not formalized anywhere |
| Stmt. 5 | the self-modifying knowledge-seeking agent `A_{sm,k}` would accept the self modification | — | No | — | absent. **Note the pairing and do not read it as a contradiction.** The companion's Statement 4 says the knowledge-seeking agent will *not* consistently use a delusion box; this one says it *would* accept a self-modification. The settings differ — a box that rewrites observations against a code change that the environment rewards — so the two are compatible, and neither is formalized. What the atlas does have is `Examples.DelusionBox.knowledge_uses_the_box`, which refutes the companion's Statement 4 at the atlas's own knowledge-seeking agent; that is a statement about the atlas's agent and not about either paper's |
| Stmt. 6 | the survival agent will not modify itself in any environment | — | No | — | absent. Its *Arguments* are that the Gambit "cannot be posed" to this agent, because maximal utility forever requires becoming a simpleton and the survival agent's utility cannot be positive if it is one — a claim about the joint satisfiability of two conditions on *c_t*, and the atlas has no *c_t* |

**9 Yes, 2 Partial, 9 No, 0 Beyond.**

**Two printed passages get no row, and here is why, so that nobody records them
as gaps.** §4's *prediction-seeking agent* paragraph states **no numbered
claim**: print says of `A_{sm,p}` that "it is not clear whether the learning
agent `A_{sm,p}` would accept also, because it can converge to optimal behavior
even without modification", and asserts only in passing prose that the
non-learning `A^μ_{sm,p}` accepts. There is nothing to cover. §5's finding that
"there are no reasonable existing measures of optimality" for self-modifying
agents, and that the authors "were unable to find any consistent alternative", is
a statement about the literature and about their own search, not a mathematical
claim.

**What the `Yes` and `Partial` rows are, and what they are not.** Eight of them
are §2, and §2 is the section this paper shares with the companion: those were
closed by declarations written for section 11. Three more — `A_sm`, equation
(4), `A_s` — closed on 2026-09-11 against *this* source, in
`AISafetyAtlas.Wireheading.SelfMod`. Every one of the six Statements is still
`No`, and so is the Simpleton Gambit.

**The `Partial` on `A_g` and `A_k` is the finding this pass added.** Section 11
grades both agents `Yes`. They cannot be `Yes` here, because this paper prints a
different horizon function for each, and `DelusionBox.shortHorizon` and
`DelusionBox.spikeHorizon` implement the companion's. That is a divergence
between two papers by the same two authors, submitted together, describing what
they call the same four agents — and it was invisible until both were read.
Nothing in the atlas is wrong: the atlas transcribes the companion, which is the
source its modules cite. What would be wrong is a future note saying the atlas
carries "Ring and Orseau's four agents" without saying which paper's.

**The code-and-executor gap closed on 2026-09-11**, at finite depth.
`SelfMod.Exec` is print's `E`, `smValue` is equation (4) truncated, and
`survivalAgent` is `A_s`. What remains of the nine `No` rows is the Simpleton
Gambit, Statements 1 to 6, the program prior, and equation (5)'s environment
that reads the code. Statement 1's Kolmogorov-complexity argument is still
open even though the substrate it was waiting on is here: the atlas has
`Kolmogorov.plainKNat`, and tying it to `Exec` is a different piece of work.

## 14. Goranko, Jamroga & Turrini 2013, JAAMAS 26: 288-314 → `AISafetyAtlas.Sovereignty.TrulyPlayable`

**Graded for the first time on 2026-09-10.** Until then this source had no
section and `AISafetyAtlas.Sovereignty.TrulyPlayable` had no registry row, so
every scope claim it makes lived in a module docstring that no script read —
and one of them was false for two days: the module said print gives no route
from finiteness to true playability, when that route is print's **Proposition
6**.

**Which text.** The author manuscript of the JAAMAS version, sha256
`9fc20337290d725d50f60772642fb942f36321f382c979b9a57c6f5e492a965f`, pinned in
the private manifest of 2026-09-09; the published text is subscription-only.
The AAMAS 2011 conference version is pinned beside it and is not the text graded
here. Statements below were read from the manuscript; where a symbol matters the
page was rendered, because text extraction drops mathematics from this file — in
the counterexample of §3.1 it silently loses the complement bar, turning *"`E(∅)`
= the cofinite subsets"* into *"the finite subsets"*, and the surrounding prose is
what disambiguates it.

**What this source is for.** `AISafetyAtlas.Sovereignty.PlayableConverse` proves that Pauly's five
conditions do **not** characterize the effectivity functions of strategic games.
This paper is where that was published and where the repair lives, so the two
modules grade against two different sources and section 14 is the repair.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Def. 4 | *"the nonmonotonic core `E_nc(C)` for `C ⊆ N` is the set of minimal sets in `E(C)`"*, `E_nc(C) = {X ∈ E(C) \| ¬∃Y (Y ∈ E(C) and Y ⊊ X)}` | `nonmonotonicCore` | Yes | **Same** | term for term, at an arbitrary coalition. Print attributes the notion to reference [16], which is Pauly's *Coalition Logic* — the same key its Definition 3 and its representation theorem carry — and the module says so |
| Def. 5 | *"the nonmonotonic core `E_nc(C)` is complete iff for every `X ∈ E(C)` there exists `Y ∈ E_nc(C)` such that `Y ⊆ X`"* | `CompleteCore` | Yes | **Same** | print states it at an arbitrary `C` and so does this |
| Def. 8 | *"an effectivity function `E` is truly playable iff it is playable and `E(∅)` has a complete nonmonotonic core"* | `TrulyPlayable` | Yes | **Same** | the binder that carries the paper: completeness is asked at `∅` only, not at every coalition, and print's own Example 5 is why |
| Def. 9 | *"`E` is a crown iff `X ∈ E(N)` implies `{x} ∈ E(N)` for some `x ∈ X`"* | `IsCrown` | Yes | **Same** | the definition is transcribed; the equivalence that makes it useful is Proposition 5 (4) and is a separate row below |
| Prop. 1 (1) | `E(∅)` is a filter, with footnote 2 listing the four conditions | `Playable.emptyFilter`, `Playable.emptyFilter_neBot`, `Playable.mem_emptyFilter`, `Playable.mem_empty_univ`, `Playable.inter_mem_empty`, `Playable.upward_mem_empty`, `Playable.empty_not_mem_empty` | Yes | **Same** | closed as an *object* on 2026-09-10 rather than as four separate closure lemmas. Print's footnote 2 gives exactly Mathlib's `Filter` together with properness, and building it is what lets Proposition 6 below be proved print's way instead of re-argued |
| Prop. 1 (2) | `E_nc(∅)` is empty or a singleton | `Playable.subsingleton_nonmonotonicCore_empty`, `Playable.subset_of_mem_nonmonotonicCore_empty` | Yes | **Same** | the load-bearing step is that a *minimal* element of `E(∅)` is a *least* one, which is where superadditivity at the empty coalition is spent |
| Prop. 2 | an α-effectivity function's nonmonotonic core at `∅` is the singleton of the reachable set, and such a function is truly playable | `nonmonotonicCore_effectivity_empty`, `trulyPlayable_effectivity` | Yes | **Same** | this is the proposition print's own counterexample argument runs through, and the atlas uses it the same way |
| Prop. 5 (1) ⇔ (2) | truly playable iff `E(∅)` has a non-empty nonmonotonic core | `Playable.trulyPlayable_iff_nonmonotonicCore_empty_nonempty` | Yes | **Same** | |
| Prop. 5 (1) ⇔ (3) | truly playable iff `E_nc(∅)` is a singleton and `E(∅)` is the principal filter it generates | `Playable.trulyPlayable_iff_principal`, `Playable.trulyPlayable_iff_emptyFilter_principal` | Yes | **Same** | stated twice on purpose: once by exhibiting a least element, and once as `Filter.principal` on the filter of Proposition 1 (1), which is the form print's Proposition 6 consumes |
| Prop. 5 (1) ⇔ (4) | truly playable iff `E` is a crown | — | No | — | `IsCrown` is defined and the equivalence is not proved. Print's two directions are short but neither is transcribed; the module header says so |
| Prop. 6 | *"on finite domains playability and true playability coincide"* — every playable effectivity function on a finite domain is truly playable | `Playable.trulyPlayable_of_finite`, `Playable.trulyPlayable_of_finite_empty`, `Playable.trulyPlayable_of_exists_minimal` | Yes | **Wider** | print's one-line proof is *"by Proposition 5.3 and the fact that every filter on a finite set is principal"*, and that is now the proof here. Wider because the argument consumes strictly less than a finite domain: `Playable.trulyPlayable_of_exists_minimal` asks only that the family `E(∅)` have a minimal element, `Playable.trulyPlayable_of_finite_empty` asks only that the family be finite, and print's hypothesis is two corollaries down. **This row is why the section exists**: the module attributed the finite route to an unlicensed Lean 3 development for two days, and a source with no section here is a source whose attribution nothing checks |
| §3.1 counterexample | a playable effectivity function on `ℕ` with one player, `E(∅)` the cofinite sets and `E({a})` the infinite sets, whose core at `∅` is empty *"because there are no minimal cofinite sets"*, hence `E ≠ E_G` for every strategic game | `cofiniteEff`, `cofiniteEff_playable`, `nonmonotonicCore_cofiniteEff_empty`, `not_trulyPlayable_cofiniteEff`, `Examples.Sovereignty.exists_playable_not_trulyPlayable` | Yes | **Same** | print's example exactly, written as one formula over `Set Unit` rather than by cases so that no decidability of coalition membership is needed. The route to the conclusion is print's — through Proposition 2 rather than through the least element — and `exists_playable_not_trulyPlayable` is the separation the whole paper turns on |
| §4.2 | the **corrected** representation theorem: `E` is the effectivity function of a strategic game iff `E` is truly playable, by revising Pauly's construction | — | No | — | the headline result of the repair. `paulyGame` in `AISafetyAtlas.Sovereignty.PlayableConverse` is Pauly's construction *unrevised*, so the atlas is one step short of this and nothing here should be read as progress toward it |
| §4.4 | the reconstruction of a playable effectivity function into a truly playable one, preserving the power of most but not all coalitions | — | No | — | not attempted |
| Ex. 5 | in a truly playable function the nonmonotonic core at coalitions other than `∅` and `N` need not be complete, nor non-empty | — | No | — | not built. It is the witness that Definition 8's restriction to `∅` is print's own and not a simplification, and the Def. 8 row above rests on print's assertion of it rather than on a formalized instance |
| — | a minimal element of `E(∅)` suffices, with no finiteness on the outcome type and none on the family | `Playable.trulyPlayable_of_exists_minimal` | — | **Beyond** | print states the finite-domain case only. This is the hypothesis its proof actually consumes, and `cofiniteEff` witnesses that it cannot be dropped: there the family is infinite, no minimal element exists, and the conclusion genuinely fails |

**11 Yes, 0 Partial, 4 No, 1 Beyond.** The four `No` rows are one absence and two
separate ones: Proposition 5 (4) and Example 5 are short and unbuilt, while §4.2
and §4.4 are the paper's constructive half and need a revised `paulyGame`. What
this section establishes is that the *diagnostic* half of the repair — the
definitions, the filter, the equivalences, the counterexample and the finite-domain
corollary — is complete and correctly attributed, and that the atlas is wider than
print at exactly one place and says which.

---

## 15. Pauly 2002, J. Logic and Computation 12(1): 149-166 → `AISafetyAtlas.Sovereignty.Playability`

**Graded for the first time on 2026-09-10**, the same day as section 14, and the
two belong together: this is the source `AISafetyAtlas.Sovereignty.PlayableConverse`
**refutes**, and section 14 is the repair.

**Where these declarations live.** The five conditions, the easy direction and
Theorem 3.3 are in `AISafetyAtlas.Sovereignty.Playability`; the `Playable`
predicate itself, Lemma 3.1's two consequences and the counterexample are in
`AISafetyAtlas.Sovereignty.PlayableConverse`. `LAND-SOV-PLAYABILITY-001` hosts
both modules.

**Which text.** `pauly-coalition.pdf`, sha256
`aa761c97e227ec186beb2e06...` as pinned in the private manifest of 2026-09-09.
Statements below were read from **rendered pages 152 and 155**; text extraction
strips every formula from this file, leaving prose with holes where the
mathematics was.

**One thing print says about itself that matters for every scope cell below.**
Pauly is explicit that he does *not* assume the outcome function surjective and
does *not* assume `X ∈ E(N)` for all `X ≠ ∅`, unlike the two earlier
characterizations he cites: *"certain states may be unreachable no matter how the
players play"*. So the atlas inherits that generality from print rather than
adding it.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| p. 152 defs | outcome-monotonic, coalition-monotonic, `C`-regular, `C`-maximal, regular, maximal, superadditive | `Playable`, `Playable.regular`, `Playable.mono_coalition` | Yes | **Same** | the properties are transcribed as the fields of `Playable` and as its two derived lemmas. Print defines `C`-maximality for every `C` and asks it only at `N` in the playability list, and the structure follows that |
| p. 152 playability | *"`E` is playable iff (1) `∀C ⊆ N : ∅ ∉ E(C)`, (2) `∀C ⊆ N : S ∈ E(C)`, (3) `E` is `N`-maximal, (4) `E` is outcome-monotonic, and (5) `E` is superadditive"* | `Playable` | Yes | **Same** | five fields, print's five conditions, in print's order. Print adds *"it can be shown that these conditions are independent"* and that independence is **not** proved here |
| Lemma 3.1 | every playable effectivity function is regular and coalition-monotonic | `Playable.regular`, `Playable.mono_coalition` | Yes | **Same** | both directions of print's short proof, including the step through `S ∈ E(C' \ C)` that superadditivity then combines |
| Thm. 3.2, game ⟹ playable | the effectivity function of any strategic game satisfies the five properties | `effectivity_playable`, `playable_effectivity`, `not_forces_empty`, `forces_univ_of_not_forces_empty_compl`, `not_forces_compl_of_forces` | Yes | **Same** | print's *"one can easily check"*, discharged condition by condition. `N`-maximality is the one that is not immediate and `forces_univ_of_not_forces_empty_compl` is it |
| Thm. 3.2, playable ⟹ some game | *"an effectivity function `E` is playable iff it is the effectivity function of some strategic game"* — the converse half | `cofiniteEff`, `cofiniteEff_playable`, `not_exists_gameForm_cofiniteEff` | No | — | **this half of the printed theorem is false, and the atlas proves it false rather than leaving it open.** Goranko, Jamroga and Turrini published the refutation; the witness is their cofinite effectivity function on `ℕ`, and it is graded in section 14 above. There is nothing here to cover, and a reader should not read the `No` as work outstanding. Print's proof is not merely incomplete: its construction cannot be repaired without changing the theorem, which is what section 4.2 of the repair paper does |
| p. 153 construction | the strategy triple and the refinement that Pauly's proof of the converse builds | `BlockChoice`, `blockOf_disjoint`, `iUnion_blockOf`, `forces_iInter_blockChoice`, `iInter_blockChoice_nonempty`, `exists_stable_of_refining`, `exists_refineFixed`, `paulyGame` | Partial | **Same** | the construction is built and its parts are proved — the partition, the forced intersection, its non-emptiness, and the fixed point the refinement reaches. What is not proved is that it *represents* `E`, and by the row above it cannot be. It is kept because section 4.2 of the repair paper revises exactly this construction, so it is the material the corrected theorem needs |
| §3.2 individualistic | *"call an effectivity function `E` individualistic iff it is playable and"* the grand coalition's power is the union of the individuals' | `Individualistic`, `iUnion_effectivity_singleton_subset` | Yes | **Same** | print writes the condition as an equality and the `⊇` half is free, which the module records rather than silently proving the easier inclusion |
| Thm. 3.3 | *"an effectivity function is individualistic iff it is the effectivity function of a dictatorship"* | `individualistic_iff_exists_dictator`, `IndividualisticEff`, `individualisticEff_effectivity_iff`, `cofiniteEff_individualisticEff`, `not_forall_individualisticEff_exists_gameForm`, `not_forall_individualisticEff_exists_dictator`, `Examples…exists_individualisticEff_not_dictatorship` | Yes | **Narrower**, and closed | the Lean biconditional is **on an existing game form**; print quantifies over an arbitrary effectivity function. **Closed 2026-09-20, and the branch the cost note named as the bad one is the branch that happened: print's Theorem 3.3 is false as printed.** The note asked for a measurement — lift `Individualistic` off `GameForm` and test `cofiniteEff` for it — and the measurement came back *individualistic*. `IndividualisticEff` is print's definition with print's own playability conjunct, which `Individualistic` drops because it is free for a game form, and `individualisticEff_effectivity_iff` is the converting lemma. `cofiniteEff_individualisticEff` then holds for the cheapest possible reason: there is **one** player, so the union over individuals is the grand coalition's own power and the equation is free, and playability is `cofiniteEff_playable`. `not_forall_individualisticEff_exists_dictator` is print's sentence refuted. **The refutation does not read the word *dictatorship***: `not_forall_individualisticEff_exists_gameForm` says the witness is outside the range of `effectivity` altogether, so no reading of print's right-hand side saves the statement, and the dictatorship form is the corollary. **Why this is `Yes` and `closed` rather than a permanent narrowing.** The atlas holds print's statement restricted to effectivity functions that are some game form's, which is exactly the restriction print's own proof performs in its first sentence — *"assume `E` is individualistic, and so there is a strategic game such that `E = E_G`"* — and it now also holds the reason the unrestricted form cannot be had. That is the same shape as §27's Theorem 1 and §29's Theorem 1: the wider statement is refuted, so the narrowing is closed by counterexample rather than owed. **What this costs print is more than Theorem 3.3.** Theorem 3.3 was the one place where the defect in Theorem 3.2's converse had been argued about print's *proof*; it is now a fact about print's *statement*, at the same witness, with no second construction |
| Lemma 3.4 | *"an effectivity function `E` is playable iff it is semi-playable, regular and `N`-maximal"*, where semi-playable is the four conditions restricted to coalitions `C ≠ N` | — | No | — | **not built, and the reason recorded for not building it was wrong.** `cognitive-sovereignty-obligation.md` said the notion's provenance was unclear because the Lean 3 development that carries it cites three papers without saying which owns it. It is **Pauly's own, §3.3, page 155** — in the source this very section grades. Nothing checked that because Pauly had no section here until today. The lemma is now unblocked and is the cheapest open item in this cluster |
| §4 | coalition frames, coalition models, and the logic over them | — | No | — | the modal layer. Nothing in the atlas is a syntax or a satisfaction relation, and this is the boundary the sovereignty cluster deliberately stops at |

**6 Yes, 1 Partial, 3 No, 0 Beyond.** The section's shape is unusual and worth
stating plainly: **two of print's theorems are refuted rather than unfinished,
at the same witness**, and the one remaining `Partial` row is partial *because*
of them. Theorem 3.2's converse is the `No` row, refuted by Goranko, Jamroga and
Turrini and graded against them in section 14. Theorem 3.3 is the `Yes` row,
refuted here on 2026-09-20 — **their papers do not mention it**: neither the
AAMAS 2011 nor the JAAMAS 2013 manuscript contains the word *individualistic* or
the word *dictator*, so the consequence for Theorem 3.3 is drawn here rather
than taken from them, while the witness that draws it is entirely theirs. What
the atlas has of Pauly is the whole of the easy direction, the definitions, the
machinery of a construction whose target statement is false, and now the reason
the second theorem falls with the first; what it does not have is a lemma it
declined to build on a provenance question this section answers.

---

## 16. Turner & Tadepalli 2022, arXiv:2206.13477v2 → `AISafetyAtlas.Sovereignty.Retargetable`

**Graded for the first time on 2026-09-10.** This section covers **three
modules**, because the source is one chain: section 3 is the combinatorial core,
appendix B.2 is the machinery that reaches theorem A.13, and definition D.6 is a
carrier a different cluster borrows.

**Where these declarations live.** Section 3, definition A.6 and the
involution-free rendering of A.7 are in `AISafetyAtlas.Sovereignty.Retargetable`;
**A.7 as printed lives in `AISafetyAtlas.Sovereignty.EUDetermined`**, beside the
appendix B.2 chain, definition A.12 and theorem A.13;
definition D.6 is in `AISafetyAtlas.Decision.MDP`.
`LAND-SOV-RETARGETABLE-001` hosts the first two and `LAND-DEC-MDP-001` hosts the
third, because the carrier belongs to the decision cluster rather than to this
paper's own subject.

**Which text.** `turner-tadepalli-arxiv-v2-2022-parametrically-retargetable-decision-makers-tend-to-seek-power.pdf`,
sha256 `5e4e811bd5a8cbf62203f29e9b7e430d0597d123397ab9f2be12ade6878a694e`, as
pinned in the private manifest of 2026-09-09. **The NeurIPS 2022 version is not
open access**, so every statement number here is the arXiv v2 numbering.
Statements below were read from **rendered pages 4, 5, 12, 14–21 and 35**; the
file's xref table is damaged and needs reconstruction, and its formulas are
AMS-glyph.

**A manifest line this section corrects.** the private manifest of 2026-09-09
recorded this source as *"Not yet read"* and guessed that its two ingredients
would be a Mathlib measure-preserving congruence lemma and an
image-monotonicity lemma. Neither describes what was built:
the modules quote print's equation numbers throughout, so it plainly had been
read, and **no measure appears anywhere in the chain** — appendix B.2 is finite
combinatorics, an order and a group action. The manifest is corrected in the
same commit.

**What "appendix B.2" means, since the citation looks ambiguous.** Appendix B
has subsections `B.1 General results on retargetable functions`, `B.2 Helper
results on retargetable functions`, `B.2.1 EU-determined functions` and `B.3
Particular results on retargetable functions`. The modules cite the
**subsection**, which holds lemmas B.7 to B.11 — not lemma B.2, which is a
different statement in subsection B.1. The citation is correct as written.

### Section 3, the combinatorial core → `Sovereignty.Retargetable`

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Def. 3.1 | *"the orbit inside `Θ` is `Orbit\|_Θ(θ) := (S_d · θ) ∩ Θ`"* | `orbitIn` | Yes | **Wider** | print's `S_d`, an arbitrary group here. Every statement in this module is wider on exactly this axis and the notes below do not repeat it |
| Def. 3.2 | `f(B ∣ θ) ≥ⁿ_{most: Θ} f(A ∣ θ)` when for *all* `θ ∈ Θ` the printed cardinality inequality (2) holds | `MostOrbit`, `orbitFavouring`, `orbitAgainst` | Yes | **Wider** | print asks `n ≥ 1`; the Lean takes any `n : ℕ`, and `n = 0` is vacuously true. Print writes one `f : {A,B} × Θ → ℝ`; **the appendix's own Remark on page 15 switches to two functions `f₁, f₂ : Θ → ℝ`** for compatibility with Turner et al. 2021, which is exactly the atlas's two-function rendering. That rendering is print's, not the atlas's |
| Def. 3.3 | *"if `∃φ ∈ S_d : ∀θᴬ ∈ Θ : f(B ∣ θᴬ) < f(A ∣ θᴬ) ⟹ f(A ∣ φ · θᴬ) < f(B ∣ φ · θᴬ)`"* | `SimplyRetargetable` | Yes | **Wider** | the quantifier order is print's: **one** `φ` for every `θᴬ`, not one per parameter. Wider on `Θ` as well as on the group: print says *"let `Θ` be a set acted on by `S_d`"*, which footnote 3 reads as closure under permutation, and the Lean takes an arbitrary `Θ : Set Ω`. Proposition 3.4's row below is where that closure comes back, as an explicit hypothesis |
| Def. 3.5 | `(Θ, A →ⁿ B)`-retargetable: for each `θ`, permutations `φ₁ … φₙ` with items 1 *retargetable via `n` permutations*, 2 *parameter permutation is allowed by `Θ`*, 3 *permuted parameters are distinct* | `MultiplyRetargetable` | Yes | **Wider** | three clauses, print's, in print's order, all scoped over `θᴬ ∈ Orbit\|_{Θ,A>B}(θ)` as print scopes them |
| Prop. 3.4 | *"if `f` is `(Θ, A →^simple B)`-retargetable, then `f(B ∣ θ) ≥¹_{most: Θ} f(A ∣ θ)`"* | `SimplyRetargetable.mostOrbit` | Yes | **Same** | print's **footnote 3** says definition 3.3 *"implicitly assumes `Θ` is closed under permutation"*, and print's proof of 3.4 uses it to discharge definition 3.5's item 2. The Lean carries it as the explicit hypothesis `hclosed`. Same total assumptions as print; the atlas puts on the theorem what print puts on the definition |
| Thm. 3.6 | *"if `f` is `(Θ, A →ⁿ B)`-retargetable, then `f(B ∣ θ) ≥ⁿ_{most: Θ} f(A ∣ θ)`"* | `MultiplyRetargetable.mostOrbit`, `orbitIn_finite` | Yes | **Wider** | print's counting argument: `n` pairwise-disjoint injective images of the `A`-favouring part inside the `B`-favouring part. `[Finite G]` is stated because print gets orbit finiteness free from `S_d` |
| Def. A.6 | similarity of vector sets; *involution*; *`X` contains a copy of `X'`* | `SimilarUnder` | Partial | **Wider** | only the similarity half. The involution and the contains-a-copy notions are rendered at A.7 below rather than here |
| Def. A.7 | *"`B` contains `n` copies of `A` when there exist **involutions** `φ₁ … φₙ` such that `∀i : φᵢ · A =: Bᵢ ⊆ B` and `∀j ≠ i : φᵢ · Bⱼ = Bⱼ`"* | `InvolutiveCopies` (in `EUDetermined`), `ContainsCopies`, `InvolutiveCopies.containsCopies`, `containsCopies_one_of_subset`, `ContainsCopies.mono` | Yes | **Wider** | **two renderings, deliberately.** `InvolutiveCopies` is A.7 as printed; `ContainsCopies` drops the involution clause, which is wider and sound for its own consumers. `InvolutiveCopies.containsCopies` records that print's is the stronger. Print's **footnote 8** admits its own definition is degenerate — the identity makes `A` contain `n` copies of `A` for every `n` — and declines to fix it, because disjointness *"would narrow our results to not apply e.g. when the `Bᵢ` share a constant vector"*. That looseness is reproduced rather than silently repaired |

### Appendix B.2 and theorem A.13 → `Sovereignty.EUDetermined`

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Lemma B.7 | *quantitative general orbit lemma*: involutions `φᵢ`, alternatives `B⋆ᵢ`, four items, concluding `f(B ∣ θ) ≥ⁿ_{most: Θ} f(A ∣ θ)` | `mostOrbit_of_orbitConditions`, `smul_mem_orbitIn` | Yes | **Wider** | **item 1 is stated here without print's guard, and print's own proof requires the unguarded form.** Print writes item 1 as *"there exist `B⋆ᵢ` such that **if** `f(B ∣ θ*) < f(A ∣ θ*)`, then `∀i : f(A ∣ θ*) ≤ f(B⋆ᵢ ∣ φᵢ · θ*)"*. Its equation (24) rewrites `f(A ∣ φᵢ · θ*) = f(A ∣ φᵢ⁻¹ · θ*)`, and equation (25) then applies item 1 **at the parameter `φᵢ⁻¹ · θ*`** — where, `φᵢ` being an involution, the guard reads `f(B ∣ φᵢ · θ*) < f(A ∣ φᵢ · θ*)`, the **negation of the inequality equation (29) concludes**. The guard therefore cannot be available at its own use. This was checked at the page, both directions. Items 2 and 4 keep their guards, and their uses respect them — equation (32) applies item 4 at a parameter print has just placed in `Orbit\|_{Θ,B>A}(θ)`. Print's **table 3** exhibits a function meeting every item but item 4, so item 4 is not droppable and is not dropped |
| Def. B.4 | *"`f` is increasing under joint permutation by `P` when `∀φ ∈ P : f(X₁ … X_m) ≤ f(φ · X₁ … φ · X_m)`; if equality always holds, invariant"* | `IncreasingUnderJointPerm` | Yes | **Same** | at the two-argument shape lemma B.9 consumes; the invariant half is carried by B.10's second theorem below |
| Def. B.8 | *"`B` contains `n` superset-copies `B⋆ᵢ` of `A` when there exist involutions with `φᵢ · A ⊆ B⋆ᵢ ⊆ B`, and whenever `i ≠ j`, `φᵢ · B⋆ⱼ = B⋆ⱼ`"* | `SupersetCopies`, `InvolutiveCopies.supersetCopies` | Yes | **Same** | four clauses, print's. The bridge theorem proves A.7 gives B.8 by taking `B⋆ᵢ := φᵢ · A`, so the chain's hypothesis is genuinely looser than print's A.7 rather than differently shaped |
| Lemma B.9 | *looser sufficient conditions for orbit-level incentives* — `Θ` closed, `B` contains `n` superset-copies, `f` increasing under joint permutation, `f` monotone in its first argument | `mostOrbit_of_supersetCopies` | Yes | **Wider** | print states B.8 and B.9 over a family `E` of subsets of `ℝᵈ` ordered by inclusion and permuted pointwise. The proof uses exactly an order and an action, so the Lean is stated over an arbitrary ordered `G`-set; `Set X` is print's instance and `Finset V` is the one A.13 needs. Item 1 is discharged exactly as print discharges it — *"holds since `f(A ∣ θ*) ≤ f(φᵢ · A ∣ φᵢ · θ*) ≤ f(B⋆ᵢ ∣ φᵢ · θ*)"*, **with no antecedent**, which is the independent confirmation that B.7's item 1 is meant unguarded |
| Lemma B.10 | *hiding an argument which is invariant under certain permutations*, and its *furthermore* clause for invariance | `increasingUnderJointPerm_of_hide`, `increasingUnderJointPerm_of_hide_invariant` | Yes | **Same** | both halves, print's equations (40)–(43), including the step that consumes `φᵢ · C = C` |
| Def. A.12 | EU-determined: `f(X₁ … X_m ∣ u) = g^{∣X₁∣,…,∣X_m∣}([x₁ᵀu]_{x₁∈X₁}, …)` — a family indexed by cardinalities, applied to *multisets* of inner products | `EUDetermined`, `euProfile` | Yes | **Narrower** | rendered at `m = 2`, the case A.13 uses. The cardinality index is dropped and that is **not** a narrowing: `Multiset.card` recovers `∣Xᵢ∣` from the profile, so one `g` carries the family's data. The **narrowing is the carrier** — print's type is the power set `𝒫(ℝᵈ)` and the Lean is `Finset V`. Costed, and the cost buys nothing: an infinite profile needs a multiplicity function `ℝ → Cardinal`, which Mathlib has no API for, and no step in the chain reads a cardinality. Print's own equation (4) presupposes finiteness by writing a multiset and its size, and print's definition A.2 states it outright while A.12 and A.13 do not restate it **Narrowing state: open, costed.** The cost is the one stated above, which argues against paying it. |
| Lemma B.11 | *"EU-determined functions are invariant under joint permutation"* | `EUDetermined.jointPermInvariant`, `euProfile_smul` | Yes | **Wider** | print's proof uses exactly one property of the permutation matrix, checked at equation (47): orthogonality, giving `xᵀu = (P_φ x)ᵀ(P_φ u)`. That property is the hypothesis `hpair`, so the lemma holds for **any invariant pairing**; print's dot product with coordinate permutation is one instance |
| Thm. A.13 | *"let `A, B, C ⊆ ℝᵈ` be such that `B` contains `n` copies of `A` via `φᵢ` with `φᵢ · C = C`; let `h` be EU-determined and `p(X ∣ u) := h(X, C ∣ u)` return a probability of selecting an element of `X` from `C`. Then `p(B ∣ u) ≥ⁿ_{most: ℝᵈ} p(A ∣ u)"* | `eu_determined_mostOrbit` | Yes | **Mixed** | **wider** on two axes — the hypothesis is B.8's superset-copies rather than A.7's copies, which is strictly looser and bridged by `InvolutiveCopies.supersetCopies`; and the pairing is arbitrary, per B.11. **Narrower** on the carrier, per A.12. Print's `Θ` is all of `ℝᵈ` and the Lean's is `Set.univ`. `hmono` is print's sentence about returning a probability, stated as the monotonicity its proof immediately reduces it to. Print does **not** require `A, B ⊆ C` here, though proposition A.11 does, and the Lean follows A.13 **Narrowing state: open, costed.** Narrower on the carrier only, inherited from A.12 and costed there. |

### Definition D.6 → `AISafetyAtlas.Decision.MDP`

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Def. D.6 | *"`⟨S, A, T⟩` is a **rewardless MDP** with finite state and action spaces `S` and `A`, and stochastic transition function `T : S × A → Δ(S)`. We treat the discount rate `γ` as a variable with domain `[0,1]`"*, attributed to Turner et al. 2021 | `MDP` | Yes | **Wider** | the triple, curried, with `PMF` for `Δ(S)`. Two widenings, both deliberate and both stated in the module: **finiteness of `S` and `A` is dropped** and nothing downstream needs it, and **the discount is absent** because the consumer sums undiscounted over a finite horizon. The word *rewardless* is print's, and the reason the atlas needs a carrier without a reward field is that `AISafetyAtlas.Wireheading.CRMDP` makes the reward a field of an environment ranging over a class |
| — | the run, the policy type, the observation map, and their congruence and determinism lemmas | `Decision.Policy`, `DetPolicy`, `Decision.History`, `MDP.run`, `MDP.stateAt`, `MDP.historyUpTo`, `genRun`, `run_congr_obs`, `run_ofDet`, `genRun_pmf` | — | **Beyond** | print states no run. The observation map is parameterised so a consumer chooses what a policy may read, which is what makes an environment and its complement indistinguishable to `CRMDP`; none of that is a printed claim |

### Not covered

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Defs A.1–A.5 | *outcome lotteries* (A.1); and four decision rules over them — *IsOptimal* (A.2), *AntiOpt* (A.3), *Boltzmann* at temperature `T`, after Baker et al. 2007 (A.4), and *Satisfice* at threshold `t` (A.5) | — | No | — | **these four rules are what proposition A.11 quantifies over**, so this row and the A.11 row below are one gap counted at its two ends. A.2 and A.3 are where print says the option sets are `X, C ⊊ ℝᵈ` **finite**, which is the sentence the A.12 row above leans on; A.12 and A.13 then do not restate it. Print's **footnote 7** says A.1's unit-vector restriction is presentational — *"our results on outcome lotteries hold for generic `x' ∈ ℝᵈ`"* — so nothing here is narrower than print for want of it |
| Defs A.8–A.10 | `𝒟_any`, the pushforward of a permutation, and the orbit of a probability distribution | — | No | — | the distribution layer. Every atlas statement here is at the parameter level, which is where print's A.13 also lives — its conclusion is `≥ⁿ_{most: ℝᵈ}`, not `≥ⁿ_{most: 𝔇_any}` |
| Lemma B.5 | *"expectations of joint-permutation-increasing functions are also joint-permutation-increasing"* | — | No | — | **this is the bridge from the parameter layer to the distribution layer**, and it is the one missing step between what the atlas has and print's `𝒟_any` results. It needs a bounded measurable `f` and the unit determinant of a permutation matrix. Naming it is the point of this row: the gap above is one lemma wide, not a layer wide |
| Lemmas B.1, B.2, B.3, B.6 | limited transitivity of `≥most`; order inversion; the `n/(n+1)` orbital fraction; closure of orbit incentives under increasing functions | — | No | — | subsection B.1's general results. The A.13 chain consumes none of them — its proof is B.11, then B.10, then monotonicity, then B.9 — and they are used for proposition A.11's other rationalities and for appendix D |
| Prop. A.11 | *orbit incentives for different rationalities*: the same `≥ⁿ_{most}` conclusion for rational choice, uniform choice among optima, **anti-rational** choice, Boltzmann rationality, best-of-`k`, satisficing and quantilizing | — | No | — | **the paper's headline breadth result**, and the atlas has no target for it. Each item is an instance of A.13 once the rationality is rewritten as an EU-determined function, so the chain the atlas has is the machinery A.11 runs on; what is missing is the seven instantiations and the measurability work print says most of its proof length goes to. Note A.11 asks `A, B ⊆ C ⊊ ℝᵈ` finite, which A.13 does not |
| Def. B.12, Appendix C | quantilization in closed form, and the appendix of particular results | — | No | — | — |
| Defs D.7–D.10, Thm. D.11 | 1-cycle states, state visit distributions, recurrent state distributions, average-optimal policies, and *"average-optimal policies tend to end up in larger sets of RSDs"* | — | No | — | **this is the power layer, and the boundary is deliberate.** `Sovereignty.Retargetable`'s header says section 3 is not about power and that the power claim needs these; this row is the itemisation. D.11 rests on Turner et al. 2021's theorem 6.13, a source this atlas has pinned but has not graded |
| §4, §5 | the Montezuma's Revenge instantiation and the discussion of RL training as retargeting | — | No | — | the empirical and interpretive layer |

**16 Yes, 1 Partial, 8 No, 1 Beyond.** Two things distinguish this section.
**One `Wider` verdict is a correction of print rather than a generalisation of
it** — lemma B.7's item 1 carries a guard that print's own equation (25) cannot
have, and the atlas states the form print's proof needs and print's only
consumer supplies. And the `No` column is unusually informative: the distance
from what the atlas holds to print's headline proposition A.11 is **one lemma,
B.5**, plus seven instantiations, rather than a missing layer.

---

## 17. Manheim & Garrabrant 2018, arXiv:1803.04585v4 → `AISafetyAtlas.Goodhart.Regressional`

**Graded for the first time on 2026-09-11.** Read in full, all ten pages, from
rendered images of pages 1 to 9.

**Which text.** `manheim-garrabrant-arxiv-v4-2018-categorizing-variants-of-goodhart-s-law.pdf`,
sha256 `7691af8a05ed88262d0eaebebf082f5d028979445a0cd586acc29c861a7a012a`, as
pinned in the private manifest of 2026-09-10.

**This source has a different shape from every other section in this file, and
the grading has to say so.** It **numbers no theorem, no proposition, no lemma
and no corollary** — verified by scanning the whole document, not by reading its
front matter. What it numbers is **nine equations**, and each is a *generative
model* rather than a claim: print calls them "Simple Model" and attaches asserted
consequences in running prose. So the rows below grade **bolded variant
definitions and asserted prose consequences**, and a `Yes` against a prose row
means the atlas proves a sentence print asserts without proof. That is the
`Wider` category this file already recognises for a source's unproved
assertions, and it is why the two Lean modules are **routed as atlas-original
work citing this paper for its model**, per
`docs/provenance/by037-by038-goodhart-campbell-plan.md`. Nothing below books an
unnumbered gloss as coverage of a printed theorem, because there is no printed
theorem to book it against.

**Where these declarations live.** Section 1 is
`AISafetyAtlas.Goodhart.Regressional`; section 2, both sub-variants, is
`AISafetyAtlas.Goodhart.Extremal`. `LAND-GOODHART-SELECTION-001` hosts both.

**A threshold print states two ways.** The setup paragraph on page 2 writes the
permissible region non-strictly — *"`s ∈ A` if `M(s) ≥ c`"* — and section 1's own
sentence writes *"the values of G when `M > c`"*. The two modules follow their
local sentence: `Extremal.selectedAt` is `{s | c ≤ M s}` and
`Regressional.selected` is `{p | c < proxy p}`. Neither is a deviation; print is
inconsistent with itself and each module takes the reading of the passage it
formalizes. Regressional's header records this, and the proof uses only that the
selected slice lies above the threshold.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| p. 2 setup | a system `S` with states `s`, a regulator selecting a permissible region `A ⊆ S`, a goal `G(s) → ℝ`, a proxy `M(s) → ℝ` because *"regulators have incomplete knowledge"*, and a threshold `c` | `goal`, `gap`, `proxy`, `selected`, `selectedAt` | Yes | **Same** | the carrier is print's, with `proxy = goal + gap` as coordinate functions on a product of two lines, so the two-variable structure and the independence are built into the space rather than asserted about it. See the threshold note above |
| §1 definition | *"When selecting for a proxy measure, you select not only for the true goal, but also for the difference between the proxy and the goal. This is also known as 'Tails come apart.'"* | `goal`, `gap`, `proxy`, `selected` | Yes | **Same** | the definition **is** the carrier: print's *"difference between the proxy and the goal"* is `gap`, and selecting on `proxy` is selecting on a sum in which `gap` is a summand |
| eq. (1) | `M = G + normal(μ, σ²)` | `proxy`, `gap_selection_gaussianReal_gt` | Yes | **Wider** | print writes normal noise; the theorems need only **independence and integrability**, and the Gaussian case is recovered through `ProbabilityTheory.gaussianReal`. Note print's own tension: the prose says *"despite the lack of bias"* beside a formula whose noise carries a mean `μ`. The atlas grades against the **formula** and leaves the mean free, which is wider than the prose's intent and faithful to what is displayed. The Gaussian corollary asks a nonzero variance, which print leaves implicit — at variance zero there is no noise and no inequality is strict |
| §1 consequence (a) | *"when M is large, you can expect G to be predictably smaller than M"*, and *"an inexact metric necessarily leads to a divergence between the goal and the metric in the tail"* | `gap_selection_ge`, `gap_selection_gt`, `gap_selection_gaussianReal_gt`, `tail_integral_ge`, `tail_integral_gt` | Yes | **Wider** | **asserted in running prose with no proof, and proved here.** Stated in product form — the selected gap mass is at least the unconditional mean gap times the selected mass — so nothing divides by a selected mass that may be zero, and the statement survives a selection event of measure zero. `gap_selection_gt` adds the hypothesis strictness genuinely needs: a set of goal values of positive mass at which the threshold cuts the noise law. The module records a counterexample showing non-degenerate noise alone does **not** give strictness |
| §1 consequence (b) | *"for large values of `c` the values of G when `M > c` is expected to be higher than otherwise"* | — | No | — | **a second and distinct claim, and it is not proved.** (a) says the *gap* grows under selection; this says the *goal* still rises — selection on the proxy does help, just less than it appears. Neither implies the other. It is not hard: it is the same association inequality applied to the goal coordinate rather than to the gap, and the one-dimensional core the module already carries, `tail_integral_ge`, is the tool. Nothing was written, and that is the whole reason this row is `No` |
| §2 definition | *"Worlds in which the proxy takes an extreme value may be very different from the ordinary worlds in which the relationship between the proxy and the goal was observed."* A form of this occurs as *"out of sample prediction"* | `selected_disjoint_observed` | Partial | **Wider** | **the sentence has two halves and only one is proved.** That selection *reaches* worlds outside the observed region is `selected_disjoint_observed`, and sharply: if the proxy is bounded above on that region, every threshold above the bound selects **only** states outside it. That the relationship there *"may be very different"* is **not** proved, and the module's own scope note says why — *"print says selection **causes** the collapse. Nothing here is causal"*. What the atlas has instead is that the observations do not **constrain** the relationship off the observed region, which is a different claim and is the `Beyond` row below. Graded `Yes`/`Wider` when this section was first written on 2026-09-11 and corrected the same day: calling it `Wider` asserted the atlas proved more of this sentence than it does. **Scope, on the covered half.** Print writes *"may be"* — a possibility about extreme-proxy worlds. `selected_disjoint_observed` proves a universal: *every* state above the bound is outside the observed region, with none excepted. That is a strict logical change in the conclusion, not a re-encoding, so the half that is covered is covered `Wider`. The boundedness hypothesis it carries is not a narrowing axis: it is what renders print's undefined word *"extreme"*, exactly as the §2 Model Insufficiency row below reads the same declaration. The widening is worked at data by `Examples.Goodhart.Extremal.selectedAt_disjoint_observed`, which is a universal disjointness at print's own linear fit — the conclusion print's *"may be"* does not license. Graded 2026-09-18; this row carried `—` until then, the only `Partial` row in the file with no scope cell |
| §2 Model Insufficiency | *"The metric of interest is based on a learned relationship between the goal and the metric which is approximately accurate in the initial region. Selection pressure moves the metric away from the region in which the relationship is most accurate so that the relationship collapses."* | `selected_disjoint_observed`, `FitsOn` | Yes | **Same** | `FitsOn` is print's *"approximately accurate in the initial region"*, with the tolerance explicit. This is the only place the word *extremal* does any work |
| eq. (2) | `M = G(sᵢ) + G′(sᵢ)` | `FitsOn` | Partial | **Same** | **the equation asserts nothing.** As printed it names the residual `G′` and stops; there is no claim to prove and no hypothesis to carry. What the atlas has instead is `FitsOn`, the relation eq. (2) is *about* — agreement with the learned relationship on the observed region, to within a tolerance. `Partial` rather than `Yes` because a reader looking for eq. (2) will find a rendering of its subject rather than of the equality |
| §2 Change in Regime | *"The proxy M may be related to G differently in different regions. Even if the correct relationship is learned for the observed region, in the region where the proxy takes an extreme value the relationship to the goal may be fundamentally different. Selection on the basis of the proxy moves into such a region."* | `regime_selected_disjoint_observed` | Yes | **Same** | the last sentence is the theorem: above the regime boundary, selection lands entirely in the upper regime |
| eq. (3) | `G = M + x` where `M <= a`; `G = M + y` where `M > a` | `regimeGoal`, `regimeGoal_eq_of_le`, `regimeGoal_eq_of_lt` | Yes | **Same** | print's two branches, read off at print's own comparisons — non-strict below, strict above |
| — | the size of the extrapolation error, and its underdetermination | `regime_prediction_error`, `regime_underdetermines`, `fits_underdetermined_off_observed` | — | **Beyond** | **print states no quantity.** Its sentence is that the relationship *"may be fundamentally different"*. The atlas proves three things print does not state: extrapolating the lower regime into the selected region is wrong by **exactly** the difference of the two offsets at every selected state; for any goal fitting the learned relationship on the observed region and any displacement, a second goal fits equally well, agrees on the whole observed region and differs by exactly that displacement at every selected state; and print's own regime model realises that underdetermination, its witness being two regime models differing only in the upper offset rather than a spike planted at one state |
| §3 Causal Goodhart | *"When the causal path between the proxy and the goal is indirect, intervening can change the relationship between the measure and proxy"*, with three intervention effects — **Shared Cause Intervention**, **Intermediary Intervention** and **Metric Manipulation**, each a shaded node in print's three-DAG figure and each with a prose *Simple Model* rather than an equation | — | No | — | the whole section needs an **interventional** layer: print's distinction is between selecting on a proxy and *acting* on a node, and nothing in the Goodhart cluster represents an intervention. The substrate now exists elsewhere in the atlas — `AISafetyAtlas.Causal.StructuralModel` and `AISafetyAtlas.Causal.Incentive` — and `by037-by038-goodhart-campbell-plan.md` records that BY-038 was parked pending exactly that merge |
| §3 non-causal cases | *"Non-Causal Goodhart Effects in Causal Systems"* — **Ignored Shared Cause** with eq. (4) `Metric ~ normal(X, σ_m²)`, `Goal ~ normal(X, σ_g²)`; **Ignored Intermediary**; **Ignored Additional Cause** with eq. (5) `Metric ~ normal(X + Goal, σ_m²)` or eq. (6) `Goal ~ normal(X + Metric, σ_g²)` | — | No | — | print's own reading is that these *"lead to worsened regressional Goodhart effects or extremal Goodhart effects, but not causal Goodhart effects"* — so they are the covered variants under a mis-specified graph, not new consequences. Reaching them needs the graph, not new selection theory |
| §4 Adversarial Misalignment | *"The agent applies selection pressure knowing the regulator will apply different selection pressure on the basis of the metric"* | — | No | — | multi-agent; the Goodhart cluster has one actor. Print's footnote 5 ties this row to Campbell's law |
| §4 Campbell's Law | *"Agents select a metric knowing the choice of regulator metric"*, eq. (7) `M_R = G_R + X`, `M_A = G_A · X` | — | No | — | **the sharpest uncovered claim in the paper**, and a genuinely quantitative one: print asserts that under normal `X` the correlation between the agent's goal and the agent's metric is **zero over the full state set but positive on the subspace the regulator selects**. That is a statement about a conditional correlation and is provable; it needs a second actor and a product-of-two-metrics carrier the cluster does not have. It is the closest thing in this paper to a numbered result |
| §4 Cobra effects | **Normal Cobra Effect**, eq. (8) `G_{A_R} = G_{A_0} + M_R`, where the agent moves an ignored additional cause; and **Non-Causal Cobra Effect**, eq. (9), where the agent instead applies selection pressure | — | No | — | **equations (8) and (9) are printed identically**, `G_{A_R} = G_{A_0} + M_R` in both places, so the displayed models do not separate the two variants at all — the distinction lives entirely in the surrounding prose, one route causal and one selective. Recorded because a reader checking the atlas against print will otherwise assume a transcription error here |
| footnote 3 | *"There are other forms of selection pressure which can apply"*, naming probabilistic state choice and **evolutionary selection**, where *"the most likely states are generated based on a set of states selected in a previous generation"* | — | No | — | the atlas's selection is a single threshold event. Iterated or distributional selection is a different object and print explicitly sets it aside as unnecessary for the basic dynamics |

**7 Yes, 2 Partial, 7 No, 1 Beyond.** Three things are worth carrying out of
this section. **The source proves nothing**, so every `Yes` here is a prose
assertion made checkable, and the modules are booked as atlas-original for that
reason. **The `No` column is where this paper's content actually is**: causal
and adversarial Goodhart are two thirds of the taxonomy and neither is reachable
without substrate the Goodhart cluster does not have — an intervention for §3, a
second actor for §4. And one `No` is neither: section 1's second consequence,
that the goal still rises under selection, is a short step from a core the module
already carries and was simply never written.

---

## 18. Zhuang & Hadfield-Menell 2020, NeurIPS → `AISafetyAtlas.Goodhart.Overoptimization`

**Graded for the first time on 2026-09-11.** Statements read from rendered pages
3 to 8 of the published version, and Theorem 1's proof from rendered page 5 of
the preprint.

**Which text, and this source has two.** The **published** NeurIPS 2020 version
is canonical and is pinned at sha256
`bb5c7b5d179c6d63a777ef946c0449adeffc036036883280248ce0e50ae32710`; it states
every result and says outright *"proofs for all theorems and propositions can be
found in the supplementary material"*, which is not in the pinned file. The
**arXiv preprint**, sha256
`37723b9165855628c3b0dd11908884dde8edd145ae277017be861d40dc8724aa`, carries the
proofs inline, and Theorem 1's four-line proof is read from it. Both are pinned
in the private manifest of 2026-09-10. Statement numbering agrees
between the two for everything graded here.

**Unlike sections 15 and 17, this source numbers its results** — three theorems
and five propositions — so the rows below are printed statements in the ordinary
sense, and the module is coverage rather than atlas-original work.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §2.1.1 attribute space | *"attribute space `S ⊂ ℝᴸ` … We assume that `S` is closed, and `S` can be written as `{s ∈ ℝᴸ : C(s) ≤ 0}` where constraint function `C : ℝᴸ → ℝ` is a continuous function strictly increasing in each attribute. Furthermore, each attribute is bounded below at `bᵢ`."* | `feasibleStates`, `StrictMonoCoord`, `isClosed_feasibleStates` | Yes | **Same** | **print's three sentences are jointly unsatisfiable as written**, and the module says so. If the feasible set were exactly `{s : C(s) ≤ 0}` with `C` strictly increasing in each coordinate, then lowering any coordinate preserves `C(s) ≤ 0`, so the set is unbounded below in every coordinate and no attribute is bounded below at `bᵢ` unless it is empty. `feasibleStates` carries the box as a **second** constraint, which is the reading that makes the setup consistent, and nothing in the paper turns on the difference. Print's closedness is then **redundant rather than dropped**: `isClosed_feasibleStates` derives it from the continuity print already assumes |
| §2.1.1 utility | *"utility function `U : ℝᴸ → ℝ` … continuous and strictly increasing in each attribute"* | `gap_le_of_unmentioned_eq_lowerBound` | Yes | **Wider** | the true utility enters only through the consequence row below, and that theorem asks **monotone** rather than continuous-and-strictly-increasing. Print's is one instance |
| §2.1.2 proxy attributes and proxy utility | *"the human chooses a set of proxy attributes `J ⊂ {1,…,L}` … let `Jmax < L` be the maximum possible number of proxy attributes"*, with the count of the proxy set at most `Jmax`; the unmentioned attributes as the complement; and *"proxy utility function … which takes in only the value of proxy attributes as input"* | `restrictAttrs`, `continuous_restrictAttrs` | Yes | **Same** | the proxy set is a set of attribute indices and the proxy utility eats only the restriction, which is print's *"only the value of proxy attributes"*. The unmentioned set is not a definition here: the conclusion quantifies over the complement directly |
| §2.1.2 incremental optimization | *"a rate function, a continuous mapping from `ℝ⁺` to `ℝᴸ` … the state at each `t` is `s⁽ᵗ⁾ = s⁽⁰⁾ + ∫₀ᵗ f(u)du` … we require that the entire sequence be feasible"* | binders of `zhuang_hadfield_menell_theorem_one` | Yes | **Same** | carried in full, and **carried in order to record that print's setup is stronger than print's proof needs**. The rate function, its continuity, the initial state and the integral representation are marked unused in the Lean; the argument consumes only feasibility along the sequence, convergence, and Complete Optimization. That the printed hypotheses are not all consumed is a finding about the paper, and keeping them in the binders is how it is recorded rather than asserted |
| §2.1.2 Complete Optimization | *"we assume that `limsup Ũ(s⁽ᵗ⁾) = sup Ũ(s)`"*, over the feasible set | `zhuang_hadfield_menell_theorem_one` | Yes | **Same** | print's limit superior, at print's own filter. **The supremum is taken as a hypothesis, not as a term**, because print's equation is between two *real numbers* and therefore silently assumes the proxy is bounded above on the feasible set. Writing it with Lean's indexed supremum instead would make the theorem **false**: at an unbounded proxy that notation returns a junk value which a convergent sequence can meet at a limit point whose omitted attributes are nowhere near their floors |
| **Theorem 1** | *"For any continuous strictly increasing proxy utility function based on `J < L` attributes, if `s⁽ᵗ⁾` converges to some point `s*`, then `s*ₖ = bₖ` for `k ∈ K`."* | `zhuang_hadfield_menell_theorem_one`, `proxyMax_unmentioned_eq_lowerBound` | Yes | **Narrower**, and closed | **as printed the theorem is false, and the atlas states the repaired form.** Print writes `J < L`, which bounds the count above and not below, and its setup lets the proxy set be any subset with `J ≤ Jmax` — nothing excludes the empty one. At `J = 0` the proxy is a constant, *strictly increasing* holds vacuously of it, every feasible state attains the supremum, a constant sequence converges, and the conclusion fails at any state above its floors. So nonemptiness of the proxy set is a hypothesis and the axis is **closed by counterexample rather than owed**. Two pieces of evidence that this is print's oversight and not print's generality: print's own proof picks *"some feature `j`"* in the proxy set to raise, which requires it inhabited; and **print states the missing hypothesis itself two pages later** — Proposition 2 reads *"for any **non-empty** set of proxy attributes"*. The other half of `J < L`, that the proxy omits something, is **not** carried, and dropping it is a vacuous-true widening: at a proxy over every attribute the conclusion quantifies over an empty set. `proxyMax_unmentioned_eq_lowerBound` is the argument at an arbitrary attribute type with no finiteness, taking the maximizing property in place of the sequence, so print's finite index and its optimization sequence are one instance of it |
| — | print's proof, and the step it omits | `proxyMax_unmentioned_eq_lowerBound` | — | **Beyond** | print lowers an omitted coordinate by `ε`, raises a proxy coordinate by `δ`, and justifies feasibility of the perturbed state with *"since `C` is strictly increasing"*. That discharges the constraint half of feasibility and **says nothing about the box half**, which is the only place the floor is used at all: the perturbation is admissible exactly while that coordinate sits strictly above its floor, and it is the failure of that condition, not of the constraint, that the conclusion asserts. The proof here supplies the missing step by taking `ε` to be the whole distance to the floor |
| — | what the limit point costs the principal | `le_of_unmentioned_eq_lowerBound`, `gap_le_of_unmentioned_eq_lowerBound`, `monotone_of_strictMonoCoord` | — | **Beyond** | print states no gap claim. The limit point is the pointwise **least** feasible state carrying its own proxy attributes, so for any monotone true utility the proxy-goal gap there is at least its value at every feasible state with the same proxy attributes. Optimizing the proxy does not merely fail to raise the goal: it lands on the gap-maximal point of its own level set. Stated in the vocabulary the rest of the Goodhart cluster uses, so this row's conclusion can be compared with `AISafetyAtlas.Goodhart.Regressional` without either module importing the other |
| §2.2 example | the content-recommendation instance at four attributes, with the utility their sum and the constraint their sum of squares less one hundred | — | No | — | print's worked example and its two figures. No file under `Examples/` instantiates the theorem at it, which would be the cheapest addition this section suggests |
| §3 `u`-costly and **Theorem 2** | the definition of a `u`-costly problem; and Theorem 2, that the intersection of the feasible set with an upper contour set of the true utility is compact for all levels **if and only if** for every level, every continuous strictly increasing proxy on `J < L` attributes and every omitted attribute, there is a bound below which lowering that attribute's floor makes optimization `u`-costly | — | No | — | **this is the paper's main result and Theorem 1 is the warm-up for it.** Theorem 1 says where a *convergent* sequence lands; Theorem 2 characterises when optimization is guaranteed to be costly, and print immediately notes Theorem 1 *"is not surprising, and may not even be suboptimal"*. It is a biconditional over a compactness condition and needs the upper contour sets, which nothing here has |
| §3 **Proposition 1** | a sufficient condition for that compactness, in terms of *sensitivity* — the ratio of the two partial derivatives — being non-increasing and tending to zero, both functions additively separable, and the constraint's partials bounded below | — | No | — | the differential layer. **Sensitivity is the paper's own bridge between decreasing marginal utility and increasing opportunity cost**, and nothing in the atlas differentiates a utility |
| §4.1 **Proposition 2** | the impact-minimising robot: freezing the unmentioned attributes at their initial values makes proxy utility agree with true utility, *"for any non-empty set of proxy attributes"* | — | No | — | the first mitigation, and **the row that supplies the hypothesis Theorem 1 omits**; see the Theorem 1 row. Section 4 also adds standing assumptions the earlier sections do not carry — both functions twice continuously differentiable, the utility concave and the constraint convex |
| §4.2 interactive game and **Proposition 3** | the human-robot game at a fixed interaction spacing, in which the human at each timestep sends a new proxy utility or an `OFF` signal; and *"the maxmin solution yields `0` utility, obtained by immediately sending the `OFF` signal"* | — | No | — | multi-step and two-actor: the object is a game with an interrupt, not a single optimization sequence. This is the paper's own negative result about interactivity alone |
| §4.2.2 efficient robot, **Theorem 3** and **Proposition 4** | *efficiently reachable* states; Theorem 3, that taking the proxy set to be the strictly most sensitive attributes gives a neighbourhood of the initial state on which a proxy gain is a true gain; and Proposition 4, that bounding the rate makes interactive optimization improve | — | No | — | the paper's positive result, and the one a reader would most want: it says **which** attributes to put in the proxy. It needs sensitivity, hence the differential layer, plus the efficient-reachability order |
| §4.3 **Proposition 5** | taking the proxy set to be the most **and least** sensitive attributes at each timestep, the solution converges to a human-optimal state | — | No | — | the paper's optimality result, combining both mitigations |

**6 Yes, 0 Partial, 7 No, 2 Beyond.** What this section records is a single
printed theorem carried at print's own binders together with **the hypothesis
print left out and states itself elsewhere**, and two consequences print does
not draw. The `No` column is the rest of the paper, and its shape is worth
naming: **Theorem 1 is the paper's warm-up, not its result.** Theorem 2 is the
characterisation, Theorem 3 is the constructive advice, and both sit behind a
differential notion — sensitivity — that no module in this atlas has. That is
one substrate, and it unlocks four of the seven `No` rows.

---

## 19. Breuer 1995, *Philosophy of Science* 62(2): 197-214 → `AISafetyAtlas.Knowledge.Embedded`

**Graded for the first time on 2026-09-11.** Statements read from rendered pages
8, 10, 12, 13 and 14 of the pinned scan, which are journal pages 203, 205, 207,
208 and 209.

**Which text, and two provenance corrections this section makes.** The file is
PhilSci1993-ImpossibilityOfAccurateSelfMeasurements.pdf, sha256
`5e558352d034e2a1e18f8316…`, a JSTOR scan whose own first page reads *"Philosophy
of Science, Vol. 62, No. 2 (Jun., 1995), pp. 197-214"*, stable URL
`jstor.org/stable/188430`.

* **The filename says 1993 and the document says 1995.** `registry.yaml`'s
  citation is the correct one; the filename is not, and it is why a search of the
  literature directory for "breuer" returns nothing. Renaming a pinned file
  changes its path but not its hash, and is not done here — the mismatch is
  recorded instead.
* **The file was in no `SOURCES` manifest.** Every other source in this audit is
  pinned with a hash in a dated manifest; this one was read on 2026-08-11 and
  never pinned. A manifest entry is added in the same commit.

**A citation this section retracts.** The module ledger recorded
`AISafetyAtlas.Knowledge.Check` as *"Breuer, Definition 3, on a finite device"*.
**Breuer has no Definition 3.** The paper numbers exactly two things, Proposition
1 and Proposition 2; its inference map, exact measurability, proper inclusion and
meshing are all defined in running prose inside numbered *sections*, and its
Lemma and its Corollary are unnumbered. Scanning the whole document for
"Definition" returns one hit, and it is the word used informally in a footnote
reference. The ledger line is corrected below.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §3.2 inference map | a map `θ` from the power set of the apparatus states into the power set of the system states, assigning *"to every set S_A of apparatus states (**except the empty set**) the set θ(S_A) of object states compatible with the information that the apparatus after the experiment is in one of the states in S_A"*, with θ(S_A) = ⋃_{s_A ∈ S_A} θ({s_A}) | `InferenceMap`, `ReadingSet`, `ReadingSet.singleton`, `ReadingSet.univ` | Yes | **Same** | both of print's conditions are structural rather than assumed: the empty reading set is excluded by making `ReadingSet` a nonempty subtype, and the union law is a field of the structure. Print's footnote 1 warns that 𝒮_A is all apparatus states while S_A is some set of them, and the two are separate types here |
| §3.2 exactly measurable | *"a state s_o is exactly measurable if after the measurement there exists a set S_A of apparatus states referring uniquely to the state s_o, i.e., θ(S_A) = {s_o}"* | `ExactlyMeasurable`, `MeasuresAllStates` | Yes | **Same** | print's equality, and the all-states form that Proposition 1 negates |
| §3.2 distinguish | *"there is one set S¹_A of final apparatus states referring to `s₁` but not to `s₂`, and another set S²_A referring to `s₂` but not to `s₁`"* | `Distinguishes` | Yes | **Same** | both halves, in print's asymmetric form |
| §3.3 proper inclusion | *"(∃`s`, `s'` ∈ 𝒮_O) : s\|_A = s'\|_A, `s ≠ s'`"* | `ProperInclusion`, `properInclusion_iff_not_injective` | Yes | **Same** | exactly non-injectivity of the restriction, and the bridge theorem says so. Print is explicit that this is a property of the restriction *map* and not of the two state sets — it gives two restrictions on the same pair of sets, one satisfying it and one not — so the atlas taking the restriction as a parameter rather than deriving it from a subsystem relation is print's own framing |
| §3.3 surjectivity | *"So \|_A describes a surjective map from the states of `O` to the states of `A`"* | `Meshing.restrict_surjective` | Yes | **Wider** | **print assumes this and the atlas derives it.** Breuer states surjectivity in the §3.3 setup and imposes meshing separately in §3.5; here the exact singleton-image equality of meshing already entails it. So the hypotheses carried below are strictly weaker than print's, and `ProperInclusion` is left carrying only the genuinely obstructive non-injectivity |
| §3.5 meshing | *"For every apparatus state s_A, the restriction of the system states θ({s_A}) to which it refers should again be the same apparatus state s_A. So meshing can be written: ∀s_A ∈ 𝒮_A : {s\|_A : s ∈ θ({s_A})} = {s_A}"* | `Meshing` | Yes | **Same** | the equality is exact and not an inclusion, which is what forces the image nonempty, and the definition is that equality |
| Lemma | *"The meshing condition implies that (∀s_A) : θ({s_A}) = {s ∈ 𝒮_O : s ∈ θ(𝒮_A), s\|_A = s_A}"* | `infer_singleton_eq_of_meshing` | Yes | **Same** | print's unnumbered Lemma, both inclusions |
| **Proposition 1** | *"The assumption of proper inclusion and the meshing condition imply that not all states of a system can be measured exactly by an internal observer. ∃s_o ∈ 𝒮_O, ∀S_A ∈ 𝒫(𝒮_A) : θ(S_A) ≠ {s_o}"* | `no_meshing_inference_measures_all_states`, `exists_state_not_exactly_measurable`, `not_knowable_state_of_properInclusion`, `no_meshing_inference_measures_all_states_direct` | Yes | **Same** | print's two hypotheses and print's existential conclusion. Two routes are carried, one through the Lemma as print argues it and one direct |
| Corollary | *"Under the assumption of proper inclusion, if all states are exactly measurable from inside the system then the inference map `θ` is contradictory (i.e., the meshing condition is violated)"* | `meshing_fails_of_measuresAllStates`, `exists_state_meshing_failure_of_measuresAllStates` | Yes | **Same** | print's unnumbered Corollary, the contrapositive reading of Proposition 1, and the second declaration produces the witnessing apparatus state rather than only the negation |
| **Proposition 2** | *"Let `s₁`, `s₂` be two states of `O` fulfilling s₁\|_A = s₂\|_A. Then there is no inference map `θ`, and thus no measurement using as apparatus `A`, which can distinguish `s₁` and `s₂`"* | `no_meshing_inference_distinguishes` | Yes | **Same** | print quantifies over *all* inference maps, and so does this |
| footnote 4, the two independence examples | a bijection **not** fulfilling meshing, and a bijection fulfilling meshing while **violating** proper inclusion — *"𝒮_A ⊂ 𝒮_O does not imply that `A` is a subsystem of `O`"* | `fibreInference`, `meshing_fibreInference_of_surjective`, `measuresAll_fibreInference_of_injective`, `meshing_and_measuresAll_fibreInference_of_bijective` | Yes | **Wider** | print offers these as prose footnote examples to show the two hypotheses are independent; the atlas builds an inference map from the fibres of the restriction and proves meshing from surjectivity, exact measurability from injectivity, and both from bijectivity. That is a **satisfiability witness** for the hypothesis set rather than an illustration, which is what stops Proposition 1 from being vacuously true |
| p. 207 finite remark | *"finitely many possible states, this already excludes the possibility of exact measurement of all states from inside the observed system"* | `properInclusion_of_card_lt`, `no_meshing_measures_all_of_card_lt`, `properInclusion_product_of_card_rest_ge_two` | Yes | **Wider** | asserted in passing prose and proved here, by pigeonhole from a strict cardinality gap. This is the whole content of `AISafetyAtlas.Knowledge.Embedded.Finite`, and it is why that module is a specialisation of Proposition 1 rather than a separate result |
| — | deciding these obstructions on a given finite model | `findCollision`, `knowable_of_findCollision_eq_none`, `not_knowable_of_findCollision_eq_some`, `findCollision_eq_none_iff`, `decidableRealized`, `decidableWeaklyInfers`, `decidableBlockwiseCollision` | — | **Beyond** | print states no decision procedure. `AISafetyAtlas.Knowledge.Check` supplies a search that returns an indistinguishability witness together with the theorem that its `none` is exactly knowability, which is what makes the output evidence rather than a report. Nothing here decides anything about an infinite state space and nothing produces a proof term at runtime; the module says so itself |
| p. 207 continuity | print considers requiring the inference to be continuous, argues that in classical mechanics this would force equal phase-space dimension and so fail under proper inclusion, and then *"I will drop the assumption of continuity altogether"* | — | No | — | nothing to cover: print raises the hypothesis in order to decline it. Recorded because a reader may expect a topological version and there is none to build |
| §4 EPR-correlations | the quantum-specific strengthening, *"stronger results hold when we take into account particular features of the quantum mechanical situation"* | — | No | — | the whole second half of the paper. It needs Hilbert-space structure, and the cluster deliberately stops at the set-theoretic core that print says holds *"for classical and for quantum mechanics, and irrespective of the character of the time evolution"* |
| §§1–2, §3.1 | the Gödel analogy, semantic closure, and print's own account of where the analogy fails — *"my argument does not have much more in common with Gödel's proof than the use of self-reference"* | — | No | — | interpretive. `AISafetyAtlas.Knowledge.SelfReference` is a different development and is not this |

**12 Yes, 0 Partial, 3 No, 1 Beyond.** This is the most completely covered source
in the file after Cover & Thomas §2.8: every numbered statement, both unnumbered
ones, and both hypotheses are carried at print's own binders, one hypothesis is
**derived where print assumes it**, and print's two footnote examples are built
as a satisfiability witness rather than quoted. What is not here is the quantum
half of the paper and a continuity assumption print itself discards.

---

## 20. Armstrong & Mindermann 2018, NeurIPS 31: 5598-5609 → `AISafetyAtlas.Preference`

**Graded for the first time on 2026-09-11.** Statements read from rendered pages
3, 4, 5, 6, 7 and 9 of the publisher's main PDF and pages 1 to 4 of the
publisher's supplemental appendix.

**Why this section is late, and what that says about the ledger's own check.**
The `AISafetyAtlas.Preference` cluster — survey row **BY-011**, six modules —
formalizes from this paper, and
`docs/provenance/a1-a3-b1-b3-b7-statement-maps.md` has carried a **25-row
statement map** against it under the heading "B7 preference deduction" since long
before this file existed. The paper was nevertheless **in no manifest, in no
section of this audit, and in no copy anywhere in the literature directory**.
The three clusters recorded above as "outside this ledger" were found by the
heuristic *a cluster with no registry rows has no scope claims to check*. This
cluster holds registry rows, a statement map and a published "6/8" ledger count,
and it was outside the ledger anyway. **Registry rows are not a pinned source,
and a statement map is not a grade.** The map is used below as a candidate list
only; every row is graded against the rendered pages.

**Which text.** Three files are now pinned in
the private manifest of 2026-09-11. The publisher's main PDF, sha256
`7e580c07450226dc…`, 12 pages, carries Theorem 1, Theorem 2, Propositions 3, 4,
7 and 8, Definition 5, Lemma 6 and Conjecture 9. **It does not carry Proposition
10 or Definition 11.** Those are in the publisher's supplemental appendix, sha256
`7da3a4b24f8d5f2b…`, 5 pages, whose own page numbers run 13 to 17 — it is
paginated as a continuation of the main text, and arXiv:1712.05812v6 (sha256
`0cc5ff7a51458…`, 17 pages) is exactly the two together. **The numbering agrees
across all three**, so no concordance table is needed. The atlas's
`AISafetyAtlas.Preference.Override` therefore formalizes from the supplemental,
which is the part that had never been fetched at all.

**Three axes run through the rows and are not repeated in each note.**

* **The reward range is dropped, and nothing printed depends on it.** Print's
  §3 sets the reward space to the functions from state-action pairs into the
  interval from minus one to one; the atlas's `RewardFn` is real-valued with no
  range invariant. Every rendered statement is either unaffected or *strengthened*
  by the widening: Theorem 1's first half and every "amongst the lowest among
  compatible pairs" claim quantify over the reward space on the side where a
  larger space is a stronger hypothesis-free claim, and Lemma 6's three
  witnesses — the constant zero, the indicator of the policy's action, and its
  negative — all land inside print's interval anyway. The widening is recorded
  once here and marked in the Scope column where it bites.
* **No dynamics.** Print's environment is an MDP without reward function, a
  tuple of a state space, a finite action space, a transition kernel and a fixed
  start state. Nothing in `AISafetyAtlas.Preference` carries a transition or a
  start state: values and regrets enter as *fields* of `RegretModel` and
  `OverrideModel` rather than as sums over trajectories. So every value-level row
  below is graded against an abstract evaluation point, which is what print's own
  appendix parenthetical licenses — "when the state is not specified ... the
  expectation is taken from the very beginning of the MDP".
* **The complexity measure is abstract where print's is Kolmogorov complexity.**
  `Source.ReasonableForF` carries any natural-number-valued assignment on pairs
  satisfying print's own bound, not the shortest-program length. This matters
  twice below, once as a widening and once at Proposition 10.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §3 setup | the environment is an MDP without reward function: a discrete state space, a finite action space, a probabilistic transition function to the next state, and a fixed starting state | — | No | — | none of it is here. The cluster is about which pairs explain an *observed* policy, and no rendered statement in sections 4, 5 or 6 of print needs a transition. The value-bearing statements of §4.1.2 and appendix B do need one, and the atlas supplies values as structure fields instead; see the second axis above. `AISafetyAtlas.Decision.MDP` exists elsewhere in the atlas and is **not** wired to this cluster |
| §3 reward space | the candidate rewards are the functions from state-action pairs into the closed interval from minus one to one | `RewardFn` | Yes | **Wider** | the function space is rendered exactly; the range invariant is dropped. First axis above says why no statement is weakened by that, and the facade's "Explicit non-claims" already declared it |
| §3 policy space | the deterministic, Markovian policies, i.e. the functions from states to actions, with the human following one of them | `Policy` | Yes | **Same** | print's Π exactly, deterministic and Markovian as printed. Print's footnote 6 says the restriction is "only chosen for notational convenience" and that the setting emulates discrete POMDPs and non-Markovian policies by encoding history in the state; the atlas takes print's stated object, not its informal generalisation |
| §3.1 planner and pair | a planner is a function from rewards to policies, encoding all the rationality, irrationality and biases of the human; the human is a planner-reward pair | `Planner`, `Pair` | Yes | **Wider** | `Planner` is over two arbitrary types rather than print's two fixed spaces, which is the form Theorem 1 is proved at; `Pair` instantiates it at print's. Print's own sentence that a planner "need not be rational" is what the atlas's total absence of constraints renders |
| §3.2 compatible | a pair is compatible with the human policy when the planner applied to the reward reproduces that policy | `Explains`, `ReasonableForF.Compatible`, `compatible_iff` | Yes | **Wider** | one equation, rendered three times over: abstractly, and once in each of the two language structures. `compatible_iff` proves the two named relations are the same, which is why a reader finding one is not misled about the other |
| **Theorem 1**, first half | *"For all π ∈ Π and R ∈ R, there exists a p ∈ P such that p(R) = π"* | `exists_planner`, `consistent_rewards_eq_univ` | Yes | **Wider** | print's quantifier order and print's own witness, the indifferent planner that ignores its argument — print's footnote 7 names that witness. The set-level form states the consequence print draws in the same breath, that compatibility "puts no restriction on R" |
| **Theorem 1**, second half | *"For all p ∈ P and π ∈ Π in the image of p, there exists an R such that p(R) = π"* | `exists_reward` | Yes | **Wider** | print calls this "even more trivial" and the Lean proof is the membership hypothesis itself, which is the same observation |
| §4.1.2 regret | the regret of a policy for a reward at a state is the optimal value minus the policy's value there | `OverrideModel.regret`, `regret_nonneg` | Yes | **Same** | in `AISafetyAtlas.Preference.Override` the name `regret` is literally that difference; in `AISafetyAtlas.Preference.Regret` the same name is an abstract field, because the module that needs it carries no values. `regret_nonneg` is the sanity fact that makes a regret bound readable as a shortfall rather than a signed quantity |
| §4.1.2 worst case | the maximum of the regret over the reward space, and the maximum over policies and rewards jointly | `worstCaseRegret`, `worstPolicy_worst`, `RegretModel` | Yes | **Same** | print's inner and outer maxima, carried as an attained upper bound and a worst policy, the attainment and upper-bound conditions being fields of `RegretModel`. Attainment is a hypothesis here and a consequence of finiteness in print's source, exactly as section 9 records for the same objects |
| §4.1.2 the half-maximal bound | *"Then Everitt et al. [2017] demonstrates that for any π"*, the maximum over rewards of the regret of that policy is at least half the maximum over policies and rewards | `HalfMaximalRegretBound`, `ComplementedClass.everitt_theorem_eleven` | Yes | **Same** | **print imports this inequality rather than proving it**, attributing it to Everitt et al. 2017. The atlas splits it the same way: `HalfMaximalRegretBound` is a hypothesis in this cluster and is discharged in the wireheading cluster, whose grading is section 9 above. The split is print's own structure, not an atlas evasion, and the module docstring says so. The IJCAI-versus-long-version caveat section 9 records is inherited here unchanged and no new claim is made about it |
| §4.1.2 conclusion | *"So for any compatible (p, R) = π̇, we cannot rule out that maximizing R leads to at least half of the worst-case regret"* | `cannot_rule_out_half_maximal_regret`, `bad_compatible_rewards_nonempty` | Yes | **Wider** | print's closing sentence, and print's own argument for it: the reward attaining a candidate behaviour's worst case is paired with a planner explaining the *observed* behaviour, and the planner comes from Theorem 1. The set-level form is the same statement at another carrier, and the CRMDP cluster carries a specialisation of the same name. This is the whole content of `AISafetyAtlas.Preference.Regret`, which the module ledger had listed as owed against Everitt's Theorem 11; the theorem this module states is **this sentence of Armstrong and Mindermann**, and Everitt's bound is its hypothesis |
| **Theorem 2** (informal) | a reasonable pair capturing our judgements about a human's biases admits degenerate compatible pairs of *lower* complexity, and a pair with the opposite reward of *similar* complexity | `theorem_two_conditional`, `ReasonableForF.proposition_eight` | Partial | **Same** | two conclusions with different status, and the atlas keeps them apart. The opposite-reward half is Proposition 8 and is proved outright. The lower-complexity half is conditional on Conjecture 9 and is stated that way, as an implication whose hypothesis is never assumed. Print itself says of this theorem that *"there exists languages in which the theorem is clearly false"*, so an unconditional rendering would be wrong; `Partial` here is the honest grade rather than a shortfall |
| **Proposition 3** | *"If π̇ is a human policy, and L is a 'reasonable' computer language, then there exists degenerate planner-reward pairs amongst the pairs of lowest complexity compatible with π̇"* | — | No | — | print introduces this and Proposition 4 as *"the following two semi-formal results"* and supplies Propositions 7 and 8 as their rigorous counterparts. The counterparts are graded `Yes` below. What is not rendered is the informal predicate "reasonable language", which has no formal content to render — print calls what constitutes one *"a long-standing open problem"* |
| **Proposition 4** | *"there exist a pair (ṗ′, −Ṙ) of comparable complexity to (ṗ, Ṙ), but opposite reward function"* | — | No | — | same reason; its rigorous counterpart is Proposition 8 |
| §5.1.1 greedy planner | the greedy planner takes the action maximising the immediate reward, and the anti-greedy planner the minimising one | `greedyPlanner`, `greedyAction`, `greedyAction_max`, `negPlanner` | Yes | **Same** | the choice among tied maximisers is unspecified in print's argmax and arbitrary here, which is the same latitude. `greedyAction_max` is the defining property a consumer needs, since the definition goes through a choice. **The finiteness and nonemptiness of the action type are print's own** — §3 fixes a finite action space and print's policies inhabit it — so this is not an added hypothesis, and the existing statement map's label "specialization: finite nonempty action type" is stricter about the atlas than the source warrants |
| **Definition 5** | *"If p : R → Π is a planner, the planner −p is defined by −p(R) = p(−R)"* | `negPlanner` | Yes | **Same** | the defining equation, character for character |
| §5.1.1 indifferent planner and policy indicator | the indifferent planner maps any reward to a fixed policy; the reward paying one for the policy's action and zero elsewhere | `indifferentPlanner`, `rewardOf` | Yes | **Same** | both of print's constructions. The indicator's values lie in print's interval, so the dropped range does not reach this row |
| **Lemma 6** | *"The pairs (pπ, 0), (pg, Rπ), and (−pg, −Rπ) are all compatible with π"* | `lemma_six`, `degenerate_indifferent`, `degenerate_greedy`, `degenerate_antirational`, `greedy_rewardOf` | Yes | **Same** | print's three-way conjunction, collected as print collects it, with each conjunct also available separately. `greedy_rewardOf` is print's own middle step — the greedy planner recovers the policy from its indicator — proved here by the strict inequality between one and zero rather than by print's "greater than zero iff" phrasing, which is the same fact |
| §5.1.2 basic operations | the six operations that build the degenerate pairs from any compatible pair | `op1`, `op2`, `op3`, `op4`, `op5`, `op6` | Yes | **Same** | all six, in print's order and with print's definitions |
| §5.1.2 composite operations | the family of four composites, and their values on any compatible pair | `Fmap`, `op3_op1_op5`, `op3_op2_op6`, `op3_op4_op2_op6` | Yes | **Same** | print's four composites and print's own computation that they send any compatible pair to the three degenerate ones, which is the step its Proposition 7 proof opens with. `Fmap` collects the four so that print's maximum over the family becomes one uniform bound rather than four. The three lemmas sending a compatible pair to each degenerate pair are in the same module, named for the composite each computes; they are not backticked here because this file's checker tokenises names as ASCII and splits a subscript |
| §5.1.2 F-complexity, c-reasonable | the F-complexity of a language is the largest amount any composite increases the complexity of a pair, and the language is c-reasonable for the family when that is at most c | `ReasonableForF` | Yes | **Wider** | the bound is print's, stated per composite rather than as a maximum, which is the same condition. The widening is the third axis: the complexity assignment is any natural-number-valued function satisfying the bound, not specifically shortest-program length. Print's footnote 10 observes the quantity is non-negative because the negation composite is an involution, and that composite is in the family here for that reason; the involution lemma sits beside it in the same module |
| §5.1.3 comparable complexity | two pairs are of comparable complexity when the absolute difference of their complexities is at most c | `ReasonableForF.proposition_eight`, `ReasonableLanguage.proposition_eight` | Yes | **Same** | the absolute value is rendered as the two separate inequalities, which is what it abbreviates |
| §5.1.3 amongst the lowest | a pair is amongst the lowest complexity in a set when its complexity is within c of the minimum over that set | `AmongLowestCompatible`, `compatible_indifferent` | Yes | **Wider** | stated without an attained minimum: the pair is compatible, and no compatible pair beats it by more than c. Over the naturals with a nonempty set the two readings coincide, and `compatible_indifferent` supplies the inhabitant that makes the universal quantifier non-vacuous — so the widening is a removal of machinery rather than a change of content. Print's own Proposition 7 proof does pick "the simplest pair compatible with π̇", which the atlas proof never needs |
| **Proposition 7** | *"the degenerate planner-reward pairs (pπ̇, 0), (pg, Rπ̇), and (−pg, −Rπ̇) are amongst the pairs of lowest complexity among the pairs compatible with π̇"* | `ReasonableForF.proposition_seven`, `ReasonableLanguage.proposition_seven`, `indifferent_amongLowest`, `greedy_amongLowest`, `antirational_amongLowest` | Yes | **Same** | all three pairs, **at print's own distance c**. The second rendering, at twice c, is a reparameterisation kept because the concrete plain-complexity layer instantiates its evaluation bound; the module docstrings say which is which and that the source distance is c |
| §5.2 negation preserves compatibility | *"If (ṗ, Ṙ) is compatible with π̇, then so is (−ṗ, −Ṙ)"* | `op3_op4`, `op4_op4` | Yes | **Same** | print's opening observation of §5.2, and the involution it rests on |
| **Proposition 8** | *"if (ṗ, Ṙ) is compatible with π̇, then (−ṗ, −Ṙ) is of comparable complexity to (ṗ, Ṙ)"* | `ReasonableForF.proposition_eight`, `ReasonableLanguage.proposition_eight` | Yes | **Same** | both directions of the comparison and the compatibility half, at c. Print's conclusion — *"So complexity fails to distinguish between a reasonable human reward function and its negative"* — applies to **every** compatible pair including the intended one, not only the constructed degenerate ones, and the Lean statement is quantified that way |
| §5.1 lower bound | the complexity of the policy is close to a lower bound on any pair compatible with it, because evaluation is a simple map | `policy_le_of_compatible`, `evalPair`, `EvaluatesTo`, `behaviour_le_of_evaluatesTo`, `evaluatesTo_degeneratePair` | Yes | **Same** | **Closed 2026-09-20.** The abstract half was always print's, over an arbitrary language structure where evaluation is a structure field. The concrete half now is too: `evalPair` **is** print's map — the pair names a program and a reward, and evaluating runs the one on the other — and `behaviour_le_of_evaluatesTo` bounds the behaviour's plain complexity by that of **every** string that evaluates to it, with one constant fixed before both. Print's reason is print's: evaluation is partial computable. Two things had to be built. Evaluation is **partial**, since a planner need not halt on a reward, so `plainK_le_of_partrec` is the invariance lemma for a partial computable map where the vendored development has only the total one. And the program slot is read off the pair as a **run length**, which makes every program index reachable — `evaluatesTo_degeneratePair` inhabits the antecedent with print's own degenerate pair, and would not exist under an encoding that missed indices. `readerPair_complexity_eq_behaviour` carries print's *argument* — some compatible pair sits within additive constants of the bound in both directions — at a **fourth** compatible pair rather than at any of print's three, so it is the shape of print's second §5.1 claim and not that claim. The earlier pair of bounds is kept and is **not** superseded: `explanation_at_least_behaviour`, `degenerate_explanation_cheap` and `explanation_complexity_eq_behaviour` are a two-sided fact about `encodeExplanation`, a different pairing that names no program, and the module says which is which |
| §6 the complexity of human judgement | the three-stage argument that any reasonable pair is of high complexity, involves many contingent choices, and has resisted past attempts | — | No | — | print says of this section that *"the arguments in this section are mostly qualitative"* and that a formalisation *"would likely already solve the problem"*. Nothing to render; it is the paper's argument for believing Conjecture 9, not a statement |
| **Conjecture 9** | *"the complexity of (ṗ, Ṙ) is not close to minimal amongst the pairs compatible with π̇"* | `NotAmongLowestCompatible`, `notAmongLowest_iff` | Yes | **Same** | rendered as a predicate at print's own quantifier and **never assumed anywhere**. `notAmongLowest_iff` proves it is exactly the negation of the "amongst the lowest" property for a compatible pair, which is what makes it the right predicate rather than merely a plausible one. It is the hypothesis of `theorem_two_conditional` and of nothing else |
| appendix A, time-bounded complexity | two time-bounded complexity measures, one adding the logarithm of the running time and one adding the running time | — | No | — | neither is defined in the atlas, and the atlas holds no resource-bounded complexity at all |
| **Proposition 10** | *"The results of Proposition 7 still apply to (pπ̇, 0) if KtL or KTL are used instead of KL"*, and to the other two degenerate pairs if a planner may take in algorithms generating reward functions | `ReasonableForF.proposition_seven` | Partial | **Wider** | this needs stating carefully. Because `Source.ReasonableForF` abstracts over the complexity assignment, print's *conclusion* transfers to either time-bounded measure the moment someone supplies an instance — the atlas's Proposition 7 is already quantified over exactly that, which is **wider than print on the axis print's Proposition 10 is about**: print names two measures and the atlas quantifies over every assignment satisfying the structure. What print's Proposition 10 actually does is establish that the two measures *are* such instances, by the wrapping construction on the generating algorithms, and **none of that is here** — the atlas holds no resource-bounded complexity at all, as the appendix A row records. Print itself says *"The proof will only be briefly sketched"*. The second sentence's hypothesis also changes the planner's domain to algorithms, which `Pair` does not model. **Regraded `Narrower` → `Wider`, 2026-09-22, and the old grade was double-counting.** What is missing here is that two named measures instantiate the abstraction; that is a fact the atlas does not *reach*, which is what the `Partial` coverage cell already says. It is not a respect in which the atlas statement is less general than print's — the atlas statement is strictly more general — so carrying it a second time in the Scope column counted one absence twice and put a cell in the owed queue that no widening could ever close. The scope axis was also being graded against an empty Atlas cell, which this file's own `—` rule forbids for exactly this reason: a grade compares two statements. Coverage is untouched and stays `Partial`; the missing construction is unchanged and is recorded in the appendix A row and here. |
| appendix B setup | the environment is doubled by a boolean that never changes, the human follows the observed policy on one copy and an overridden policy on the other, the agent chooses between leaving the human alone and forcing the overridden policy, and two planners and two rewards are considered | — | No | — | the entire construction. `OverrideModel` keeps only what the statements need — an action type, the policy resulting from each action, a value and an optimum — so the doubled state space, the mixed policy, the fully-rational and indifferent planners and the twisted reward are all absent. This is the cost of the abstraction that makes the appendix's statements type-check without dynamics |
| appendix B, three compatible pairs | the three planner-reward pairs compatible with the mixed policy, and the reading each encodes | — | No | — | needs the setup above |
| **equation (1)** | the regret of an agent action is the maximum over the agent's actions of the value difference | `optValue_isGreatest`, `OverrideModel.regret` | Yes | **Wider** | print writes the maximum over the *agent's* action set rather than an unexplained optimum, and `optValue_isGreatest` proves that the model's optimum **is** that maximum — attained, with the rationalising action as witness. Wider because the agent's action type is arbitrary here where print's has exactly the two shapes its construction allows |
| appendix B.1, zero regret at inaction | *"We already know that π̇ is optimal with respect to Ṙ (by definition), so the regret for `a = 0` is 0"*, and the resulting closed form for the overriding action's regret | `IsRationalPlanner`, `regret_noop_eq_zero_of_rationalPlanner`, `regret_eq_noopValue_sub_of_rationalPlanner`, `not_overrides_noop_of_rationalPlanner`, `regret_noop_eq_zero_or_overrides`, `regret_rationalise`, `Examples…trivial_regret_noop_eq_zero`, `Examples…trivial_regret_eq_noopValue_sub` | Yes | **Wider** | **Closed 2026-09-20 by addition, which is what the cost note said it would be.** Print writes two things about inaction two paragraphs apart and they do not conflict, because they assume different planners. The atlas had only the second — a less-than-rational human, for whom inaction is strictly worse, which is the row below. The first is now here: `IsRationalPlanner` is print's *"π̇ is optimal with respect to Ṙ (by definition)"* — a property of the planner in the compatible pair, not of the human — and `regret_noop_eq_zero_of_rationalPlanner` is print's conclusion from it. `regret_eq_noopValue_sub_of_rationalPlanner` is the closed form print draws next: with the optimum equal to the untouched human's value, the regret of any action is exactly its shortfall below inaction. `not_overrides_noop_of_rationalPlanner` is what makes the paragraph a claim about incentive rather than a restatement of Definition 11. **Wider on two counts.** The rationality hypothesis is carried on an arbitrary planner and consumed through `Explains`, where print has one constructed planner in its doubled environment, so the theorems apply to any compatible pair that happens to be rational. And `regret_noop_eq_zero_or_overrides` is not in print at all: it proves the two paragraphs **exhaustive** rather than merely consistent — inaction either has no regret or is itself an override at every threshold up to its regret, with no third case. Both branches are inhabited: the trivial model takes the left, `Examples.SixTargets.suboptimalOverrideModel` the right |
| **Definition 11** | *"Given a compatible (p, R), the agent's action a overrides the human reward function when it puts the human in a situation where the human policy leads to high regret for R"* | `OverridesFor`, `Overrides`, `overrides_of_overridesFor`, `exists_overridesFor` | Yes | **Wider** | print's relativisation to a compatible pair is kept, and print's informal "high regret" becomes an explicit threshold parameter, so the family covers every reading of the adjective rather than fixing one. Print licenses this directly: *"there is no natural zero or default"*. `exists_overridesFor` shows the relativisation never rules an action out, by Theorem 1, so the stronger notion is not accidentally empty — the definition ships with its own satisfiability witness |
| appendix B.1, no natural zero | *"if the agent does not aid the human to become perfectly rational, then that also counts as an override of R"* | `noop_overrides_of_suboptimal` | Yes | **Same** | a printed sentence and a theorem: a suboptimal human is already at positive regret, so inaction overrides at every threshold up to it |
| appendix B.1, what overriding is not | *"overriding is not encoded as a change in p or R; instead, (p, R) outputs the observed human policy, even after overriding"* | `OverridesFor` | Yes | **Same** | the definition is built exactly this way — the pair explains the policy *resulting from* the action, and the action appears nowhere else in it |
| **equation (2)** | the value of the overriding action when the agent gives the twisted reward probability ε and the true reward the rest | `mixtureValue` | Yes | **Same** | print's two terms. The action is fixed to the one that rationalises for the hypothesised reward, which is what justifies the optimal-value term rather than an arbitrary value; the module records that an earlier atlas definition took an arbitrary action and was wrong to |
| appendix B.2, the agent's best choice | the agent chooses the twisted reward maximising equation (2) | — | No | — | no choice rule is formalized. The module states this limit itself: it proves a scalar inequality and says that reading it as a preference *"needs a decision rule that is not formalized here"* |
| appendix B.2, "at the very least" | choosing the true reward makes equation (2) equal to the true optimum | `mixtureValue_rationalise` | Yes | **Same** | print's lower bound, at every mixture weight |
| appendix B.2, "very plausible" | *"It is very plausible that the value can go higher"* | — | No | — | print's own non-theorem, hedged in print's own words. It would need the choice rule above and a construction of a twisted reward easy to maximise and cheap for the true one |
| appendix B.2, the gain from overriding | *"If the human is not fully rational, then the value of action 0 is V_Ṙ^π̇, which is strictly less than V*_Ṙ"* | `noopValue`, `noopValue_lt_mixtureValue_rationalise`, `rationalise_strictly_better` | Yes | **Same** | print's closing inequality of appendix B, at print's own hypothesis that the human is not already optimal. `noopValue` is kept separate from equation (2) precisely because inaction does not acquire the optimal-value term unless it happens to rationalise |
| appendix C | the poker example and the symbol-grounding discussion | — | No | — | an illustration of why normative assumptions are needed, with no statement in it |
| — | reward unidentifiability in the knowability vocabulary | `not_knowable_reward`, `knowable_reward_of_isEmpty_state` | — | **Beyond** | print states nothing about knowability. `AISafetyAtlas.Preference.Knowability` re-expresses the obstruction in the kernel vocabulary that `AISafetyAtlas.Knowledge` shares with the wireheading and oversight clusters, so a consumer holding a knowability question can reach it. Its own registry row `LAND-PREF-KNOW-001` says it is a shared-API formulation and claims no new coverage, and that is the right reading |
| — | the abstract anti-rational twin and its instantiation at policies | `neg_twin`, `policy_neg_twin`, `policy_reward_unidentifiable` | — | **Beyond** | print's Definition 5 and §5.2 are about a planner-reward pair inside its fixed spaces. These state the same negation fact over arbitrary types with an involutive negation, with no maximisation anywhere — and `neg_twin`'s docstring is explicit that reading the negated planner as a minimiser would need optimality assumptions the module does not make. That caution is the atlas's, not print's |

**32 Yes, 2 Partial, 10 No, 2 Beyond**, up from 31 / 3 / 10 / 2 on 2026-09-20
when the §5.1 lower-bound row closed. All eleven numbered statements in the
paper are accounted for, and none is missing from the table: **seven** are graded
`Yes` (Theorem 1, Definition 5, Lemma 6, Propositions 7 and 8, Conjecture 9 and
Definition 11), **two** `Partial` (Theorem 2 and Proposition 10), and **two**
`No` — Propositions 3 and 4, which print itself labels semi-formal and replaces
with Propositions 7 and 8. So every numbered item print states rigorously is
here. The `No` column is not about the numbered statements at all: it is
dominated by appendix B's doubled-environment construction, which the atlas
abstracts away wholesale, by the qualitative §6, and by print's own hedged
non-theorems.

**What this section changes outside itself.** The module ledger listed
`AISafetyAtlas.Preference.Regret` as owed against *"Everitt et al., IJCAI 2017,
Theorem 11 certificate"*. That is the module's **hypothesis**, not its theorem.
What it states is the closing sentence of this paper's §4.1.2, and §4.1.2 is a
*section heading*, not a numbered statement — so the module renders an argument
rather than a printed theorem, which is the same routing this file gave the
Goodhart modules in section 17. The ledger line is corrected below, and the
module needs no registry row of its own because this section's target module is
`AISafetyAtlas.Preference`, hosted by `BY-011`.

---

## 21. Peleg 1998, *Social Choice and Welfare* 15: 67-80 → `AISafetyAtlas.Sovereignty.Mandate`

**Graded for the first time on 2026-09-11.** Statements read from rendered pages
1, 2, 3, 6 and 7 of the pinned file, which are journal pages 67, 68, 69, 72 and
73.

**Which text, and a filename mismatch.** The file is `peleg1997.pdf`, sha256
`99039339aae01cb8e903ebab…`, manifested  2026-09-09,
maintainer-supplied. **Its own first page reads "Soc Choice Welfare (1998) 15: 67–80"
and "© Springer-Verlag 1998"**, with "Received: 25 November 1994 / Accepted: 28
June 1996". The filename and OpenAlex both say 1997; the document says 1998, and
the heading above follows the document. This is the second filename-versus-
document mismatch in this file, after Breuer in section 19, and it is recorded
rather than renamed for the same reason: the hash identifies the file.

**Why this section grades a cluster through one module.** The declarations that
carry Peleg's §3 — `GameForm`, `Forces`, `effectivity` and the monotonicity and
superadditivity results — live in `AISafetyAtlas.Sovereignty.Separations`, whose
own header says it is "not a foundation and not coverage". That header is now
half wrong and is amended in the same commit: the module does reproduce printed
statements, it just does not reproduce the printed statements it was written to
test. `AISafetyAtlas.Sovereignty.Mandate` is this section's target because it is
the module that cites Peleg by number, and `Separations` rides on it — the
`AISafetyAtlas.Causal.DSep` precedent. `AISafetyAtlas.Sovereignty.Representation`
rides on it too, for the same reason: it is Theorem 3.5's sufficiency direction
and nothing else, and it is graded on the Theorem 3.5 row below rather than on a
section of its own.

**What is Peleg's and what is not.** Print's object is a *society* and its
*constitution*; the atlas builds neither. What the atlas takes is §3's game-form
layer, and everything above `Represents` in `Mandate` — the mandate family, the
retention comparison, and the three readings of a delegated game — is atlas-side
interpretation, declared as such in the module and in
`docs/provenance/cognitive-sovereignty-obligation.md` §8 item 1. It is graded
`Beyond` below, not `Yes`.

**One defect of print, confirmed at the page.** Definition 3.3 on journal page 73
prints the α-effectivity family as

> E_α(S; Γ) = {B ⊂ S | S is α-effective for B}

and **`B ⊂ S` is a typo for `B ⊂ A`**. The same definition's own opening line
reads "let S ⊂ N, S ≠ ∅, and let B ⊂ A", so B is a set of social states and S is
a coalition; the two are not even the same type. The module's docstring already
recorded this; it is confirmed here at the rendered page rather than inferred.

**A second defect of print, and this one is mathematical.** Theorem 3.5 puts
condition (i) — *"γ is monotonic w.r.t. the alternatives"* — on the right of an
`iff`, which makes it **necessary** for a constitution to be representable. It is
not. (3.3) is a condition on `γ` at every set of rights `θ ⊆ ρ`, while a
representation constrains only the diagonal `γ(S, α(S))`; print's own page 70
says the off-diagonal values *"do not enter the analysis of a society at a given
date"*. `Examples…represented_not_monotoneAlternatives` is a represented
constitution that fails (3.3) off the diagonal, so the necessity of (i) as
printed is **refuted**, not unproved. The sufficiency direction, and the
necessity of (ii), are both true and both carried — see the Theorem 3.5 row.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §2 society | a society is a list of members, social states, a finite set of rights, an assignment of rights to groups, and an access correspondence determining the attainable sets of social states | `Constitution` | Yes | **Wider** | print's five components: the members and the social states are the type parameters `N` and `X`, the rights are the type `R`, and `assign` and `access` are print's `α` and `γ`. **Wider** because print's `ρ` is a finite set and nothing here needs finiteness, so every statement below holds at an arbitrary type of rights. `GameForm` remains print's Definition 3.2 with no constitution attached; the two meet at Definition 3.4 |
| §2 standing assumptions | the empty coalition is assigned no rights, and both the empty coalition and the empty set of rights give the whole state space as the only attainable set | `Constitution.Standing`, `Constitution.induced_empty` | Yes | **Same** | print's three clauses, journal page 69, as a predicate rather than as structure fields — Definition 3.4 needs none of them and only the surjectivity transfer and the empty-coalition computation do, so imposing them on the object would have made the representation condition look weaker than it is. `induced_empty` is print's EF condition (i) as a consequence of them |
| **Definition 2.4** | the triple of rights, assignment and access correspondence is a *constitution* | `Constitution` | Yes | **Wider** | the object Theorem 3.5 quantifies over, and the right-hand side of Definition 3.4. **Wider** for the same reason as the society row: print's set of rights is finite and the type `R` here is arbitrary |
| Remark 2.5 | symmetric members and the equal-treatment condition on a constitution | — | No | — | needs the constitution |
| §2 examples | the two-shirt society and the further worked constitutions | `Examples…shirtConstitution`, `Examples…shirtConstitution_standing`, `Examples…smokeConstitution`, `Examples…smokeConstitution_standing`, `Examples…smokeConstitution_induced`, `Examples…smoky_notMem_smokeAccess`, `Examples…not_superadditive_officeConstitution`, `Examples…not_represents_officeConstitution`, `Examples…gibbardConstitution`, `Examples…gibbardConstitution_standing`, `Examples…unvetoed`, `Examples…gibbardAssign` | Yes | **Wider** | print's Example 2.3 is rendered in full — two members, two shirts, one right, `α(∅) = ∅` and `α(S) = ρ₁` otherwise — and its standing assumptions are proved rather than assumed. Print's Examples 2.7 and 2.10 are not. **One looseness of print, found by rendering it.** Example 2.3 lists `γ(1, ρ₁)` and `γ(2, ρ₁)` as two sets each — the *minimal* attainable sets — while writing `γ(N, ρ₁) = 2^A \ {∅}` in full in the same sentence, so within one example one coalition's family is given entire and two are given by their generators. Remark 2.2 on the same page supplies the reading and Example 2.10 writes the closure out with its `B⁺` notation. Taken as whole families the listing fails print's own (3.3), which `Examples…not_monotoneAlternatives_listedShirt` states, and `Examples…not_represents_of_induced_eq_listed` then shows that no game form represents *any* constitution whose induced family at member 1 is the listing — contradicting Example 3.6, which is the argument that the listing names generators. This is notational looseness, not a misstatement, and it is recorded because it changes how the example must be read **Both were built on 2026-09-20 and the row closes.** `smokeConstitution` is Example 2.7 and `gibbardConstitution` is Example 2.10, each with print's standing assumptions proved rather than assumed, so coverage moves `Partial` to `Yes` as well. **The row is `Wider` rather than `Same`**, on one axis and in the direction the §2 society row already carries: print's `N` in Example 2.7 is `{1, …, n}` and `smokeConstitution` takes an arbitrary type, which costs nothing because the condition deciding print's `γ` is *"the coalition contains a non-smoker"* — a property of the coalition, not a count. **Example 2.7 turned out to settle something print raises abstractly and leaves open.** Definition 3.1's discussion says *"an EF that is derived from a constitution by (3.1) might not be superadditive"* and supplies no example; `not_superadditive_officeConstitution` is one, at print's own society — the smoker alone may have the office smoky, the non-smoker alone may have it clear, and superadditivity would make the two of them effective for the empty set, which the obligation forbids — and `not_represents_officeConstitution` is `Represents.superadditive` applied to it. **And the looseness recorded above recurs twice.** Examples 2.7 and 2.10 both write print's standing assumption as `γ(S, ∅) = A` where page 69 writes `= {A}`, the same singleton-for-set shorthand, three examples running. It is harmless — `Standing` asks for the family and both constitutions satisfy it in that form — and it is recorded because the Example 2.3 case shows the shorthand is not always harmless. |
| §3 EF condition (iv) | every coalition is effective for the whole set of social states | `Sovereignty.forces_univ` | Yes | **Wider** | print lists this as a defining condition on an effectivity function; here it is a **theorem** about every game form whose strategy spaces are inhabited, which is print's own Definition 3.2 requirement. So the condition is derived rather than imposed |
| §3 EF condition (iii) | the empty set is in no coalition's effectivity family | `not_forces_empty` | Yes | **Same** | print's condition at every coalition, not only the empty one. Closed 2026-09-11: the statement is `not_forces_empty`, not an assembly from the intersection lemmas |
| §3 EF condition (i) | the empty coalition's effectivity family is the single set of all social states | `effectivity_empty_eq_singleton_univ`, `range_outcome_mem_effectivity_empty`, `Examples…vetoGame_effectivity_empty` | Yes | **Wider** | print **stipulates** this by fiat and separately assumes the outcome function is onto. The atlas still computes the family rather than stipulating it; `effectivity_empty_eq_singleton_univ` recovers print's singleton under print's own surjectivity hypothesis, so the stipulated value is a theorem rather than a gap. Wider in holding the general computed family without surjectivity, of which print's singleton is the onto case. Closed 2026-09-11 |
| §3 EF condition (ii) | the grand coalition is effective for exactly the non-empty sets | `effectivity_univ_eq_nonempty`, `Examples…effectivity_shirtGame_univ` | Yes | **Wider** | closed 2026-09-20, the last of print's four effectivity conditions to get a rendering. Print **stipulates** this; here it is a theorem about every game form whose outcome function is onto — the grand coalition fixes a whole profile, so it forces exactly the sets containing a reachable outcome, and surjectivity makes that every non-empty set. It needed print's surjectivity hypothesis, which nothing here assumes; what unblocked it is that `Represents.surjective_outcome` now **derives** surjectivity where print uses it, so the witness runs on a game form that was never assumed onto |
| **(3.1)** | the constitution induces an effectivity function by applying the access correspondence to a coalition and its assigned rights | `Constitution.induced` | Yes | **Same** | print's `E(S; α, γ) = γ(S, α(S))`, at print's arguments |
| **(3.2)** | the assignment of rights is monotonic: larger groups have at least the rights of smaller ones | `Constitution.MonotoneAssign` | Yes | **Same** | print's condition on the assignment, as a predicate on a constitution. Print's remark that it *"follows from the usual interpretation of rights"* is interpretive and is not rendered |
| **(3.3)** | the access correspondence is *monotonic with respect to the alternatives*: a superset of an attainable set is attainable | `Constitution.MonotoneAlternatives`, `Sovereignty.Forces.mono` | Yes | **Wider** | `MonotoneAlternatives` is print's condition on the access correspondence, verbatim. Print states it as a condition that may or may not hold, and Theorem 3.5 makes it one of two necessary and sufficient conditions for representability. For an α-effectivity function it is **automatic**, and `Forces.mono` proves it for every game form. Proving what print assumes is coverage rather than generality |
| **(3.4)** | the access correspondence is monotonic with respect to rights | `Constitution.MonotoneRights` | Yes | **Same** | print says outright that this "generally does not hold", because rights in its model include obligations, which is exactly why it is a predicate here and not a field. `Constitution.induced_mono` is the one statement that needs it: coalition-monotonicity of the *induced* effectivity function follows from (3.2), (3.4) and (3.5) together and from no one of them alone |
| **(3.5)** | the access correspondence is monotonic with respect to coalitions | `Constitution.MonotoneCoalitions`, `Forces.mono_coalition` | Yes | **Wider** | `MonotoneCoalitions` is print's condition on the access correspondence, verbatim. print says this "may not be true" — a larger coalition can carry conflicting rights — and then "we shall usually assume (3.5)". For α-effectivity it is a theorem, proved here for every game form with inhabited strategy spaces. Print's own taxi-driver example is about the rights layer, which is why the two can differ |
| **Definition 3.1** | an effectivity function is *superadditive* when disjoint coalitions effective for two sets make their union effective for the intersection | `Superadditive`, `forces_superadditive` | Yes | **Wider** | `Superadditive` is print's condition on a bare effectivity function, which is the form Theorem 3.5 needs. print's condition exactly, and again a theorem here rather than a hypothesis. Print is explicit that this is a real condition in general — "an EF that is derived from a constitution by (3.1) might not be superadditive" — so the atlas's version is not wider by fiat: it is wider because α-effectivity functions of game forms are a subclass on which the condition always holds. The `Separations` docstring already names the frame assumption doing the work, citing Chen, Ju and Ågotnes, and does not claim more |
| p. 72 | *"A superadditive EF is monotonic w.r.t. coalitions … (the proof is straightforward)"* | `Playable.mono_coalition` | Yes | **Same** | print's implication, from playability's superadditivity and whole-space conditions, via `C'' := C' \ C` — which is print's own "straightforward" proof, transcribed at Pauly's Lemma 3.1 where the same implication lives. Closed 2026-09-11: the atlas now states the implication, not only the two ingredients |
| **Definition 3.2** | a game form is a list of members, a non-empty strategy set per member, an outcome function into the social states, and the social states | `GameForm` | Yes | **Wider** | print's tuple. **Non-emptiness of each strategy set is print's own requirement**, carried here as an instance hypothesis on the theorems that need it rather than as a field, so no theorem below assumes more than print. Wider because the member type is arbitrary where print's is a finite initial segment, and the strategy spaces are dependent types rather than sets |
| Definition 3.2 | a game form is *legal* when no strategy contradicts the assignment of rights, and only legal game forms are considered | — | No | — | legality is a relation to the constitution. Every game form here is unconstrained, so the atlas's statements are about a strictly larger class than print's — which is a widening that cannot be recorded as one, because the printed statements it would widen are about the constitution |
| **Definition 3.3** | a coalition is *α-effective* for a set when it has a joint strategy choice such that every completion by the complement lands the outcome in that set | `Sovereignty.Forces` | Yes | **Wider** | print's quantifier order and print's guarantee against *every* completion. Stated by agreement on the coalition rather than by splitting a profile, which needs no decidable membership and has the same content. Wider on two axes print fixes: the coalition may be empty, and the outcome function need not be onto |
| **Definition 3.3** | the α-effectivity function of a game form collects every set the coalition is α-effective for | `effectivity` | Yes | **Wider** | print's family. **Print prints this as sets `B ⊂ S` where `S` is the coalition; it is a typo for `B ⊂ A`**, the social states, as the definition's own first line shows. The atlas renders the intended statement, and the two differ in type rather than in degree |
| Definition 3.3 | the outcome function is assumed onto the social states | `Represents.surjective_outcome`, `Examples…surjective_shirtGame_outcome` | Yes | **Wider** | not assumed as a standing field, deliberately, and as of 2026-09-20 not assumed at all: a game form representing a constitution that obeys print's standing assumptions **has** an onto outcome function, because the empty coalition's family is computed here where print stipulates it and the two agree only under surjectivity. **Wider** because a derived fact is stronger than an assumed one and because every statement in the cluster that is not about representation holds without it. Conditions (i) and (ii) both now run on it |
| **Definition 3.4** | a legal game form is a *representation* of a constitution when its α-effectivity function equals the effectivity function the constitution induces | `Represents`, `represents_ofGameForm`, `Represents.surjective_outcome`, `Examples…represents_shirtGame`, `Examples…not_represents_sequentialGame` | Yes | **Wider** | closed 2026-09-20. `Represents G κ` is print's equality at every coalition, against the constitution rather than against a second game form; the pre-constitution stand-in survives as `EffectivityEq`, and `effectivityEq_iff_represents_ofGameForm` says exactly how it was weaker — it is representation against `Constitution.ofGameForm`, which `represents_ofGameForm` shows every game form passes. **Three widenings, none a strengthening**: print restricts to *legal* game forms and leaves legality informal, the equality uses none of it, so every game form is quantified over; print's `ρ` is finite and this is not; and print assumes the outcome function onto from Definition 3.3 onward, where `Represents.surjective_outcome` **derives** it from representation of a constitution obeying the standing assumptions. Both sides are witnessed at print's own pair: Example 3.6's simultaneous game form represents the two-shirt constitution, Example 3.7's sequential one does not |
| **Theorem 3.5** | an effectivity function induced by a constitution is the α-effectivity function of some game form **iff** the access correspondence is monotonic with respect to the alternatives and the effectivity function is superadditive | `Represents.superadditive`, `Represents.upwardClosed`, `IsEffectivityFunction`, `IsEffectivityFunction.playable`, `Playable.surjective_paulyGame_outcome`, `IsEffectivityFunction.effectivity_paulyGame`, `exists_gameForm_of_isEffectivityFunction`, `Constitution.upwardClosed_induced`, `Constitution.exists_represents`, `Constitution.exists_represents_iff_superadditive`, `Examples…represented_not_monotoneAlternatives`, `Examples…dictator_exists_represents`, `Examples…dictator_not_standing` | Yes | **Wider** | the paper's main existence result. **Necessity of (ii) is here**: `Represents.superadditive` transfers `forces_superadditive` to the induced effectivity function. **Necessity of (i) as printed is not, and that is a fact about print's quantifier rather than a gap.** Condition (3.3) quantifies `γ` over every `θ ∈ 2^ρ`, while a representation constrains only the diagonal `γ(S, α(S))`; print's own page 70 says the off-diagonal values *"do not enter the analysis of a society at a given date"*. `Represents.upwardClosed` is (3.3) on the diagonal, and `represented_not_monotoneAlternatives` is a represented constitution that fails (3.3) off it, so the shortfall is exhibited rather than asserted **Sufficiency closed on 2026-09-20, and it cost one hypothesis rather than a construction.** `Constitution.exists_represents` builds the game form, at **arbitrary `A`** — print's appendix proof is general and cites Moulin 1983 only for the finite case, and nothing here needs `A` finite. The construction was already in the tree and the previous pass of this note did not see it: `paulyGame`, in `Sovereignty.PlayableConverse`, is Pauly's game built from a playable effectivity function, and `Playable.effectivity_paulyGame_eq` delivers the printed equality at every coalition **except the two ends of the lattice**. Pauly's own converse is false there — `not_exists_gameForm_cofiniteEff` exhibits a playable effectivity function that is no game form's, and the obstruction is that its empty-coalition family is the cofinite filter, which has no least element. **Peleg's page-72 definition of an effectivity function pins exactly those two ends**, `E(∅) = {A}` and `E(N) = 2^A ∖ {∅}`, the second of which print calls *citizen's sovereignty*; `IsEffectivityFunction` is that list, `IsEffectivityFunction.playable` derives Pauly's five conditions from print's four plus Theorem 3.5's two, and `Playable.surjective_paulyGame_outcome` supplies the surjectivity the two end computations need — print assumes it from Definition 3.3 onward, and for the game form this theorem builds it is derived. So Peleg's theorem and Pauly's refutation are the same fact read twice, and the sentence that told them apart is print's own stipulation. **What is not here is print's `iff` as printed, and that is print's defect**, recorded in this section's preamble: the necessity of (i) is refuted by `Examples…represented_not_monotoneAlternatives`. `Constitution.exists_represents_iff_superadditive` is the strongest honest form — with (i) standing, representability *is* superadditivity, both directions. Non-vacuity: `Examples…dictator_exists_represents` discharges every hypothesis at once on a two-member, two-state society with one right, written down rather than read off a game form. **`Wider`, on two axes, and the second is witnessed.** First, the rights: print's `ρ` is finite and `R` here is an arbitrary type, which is the axis the §2 society and Definition 2.4 rows already carry. Second, print's page-69 **standing assumptions are not hypotheses of this theorem**: `IsEffectivityFunction` asks that the *induced* family at the empty coalition be `{A}` and asks nothing of `α(∅)` or of `γ(S, ∅)`, so the sufficiency applies to constitutions print's §2 does not admit. `Examples…dictator_not_standing` is one — its access correspondence reads the rights and not the coalition, so `γ(∅, ρ) = 2^A ∖ {∅}` while `E(∅)` is still `{A}` because the empty coalition holds no rights — and it is represented. **Arbitrary `A` is not one of the axes**: print states Theorem 3.5 at a general set of social states and sends the reader to Moulin only for the finite case, so holding it at infinite `A` is coverage, not generality. The rights axis is stated and not witnessed — every example in this section has finitely many rights — and that is disclosed rather than claimed. |
| Examples 3.6, 3.7, 3.8 | worked representations of the earlier societies | `Examples…represents_shirtGame`, `Examples…not_represents_sequentialGame`, `Examples…effectivity_shirtGameOf`, `Examples…mem_gibbardConstitution_induced`, `Examples…gibbardInduced_empty`, `Examples…gibbardInduced_angelina`, `Examples…gibbardInduced_edwin`, `Examples…gibbardInduced_judge`, `Examples…gibbardInduced_angelina_edwin`, `Examples…gibbardInduced_angelina_judge`, `Examples…gibbardInduced_edwin_judge`, `Examples…gibbardInduced_univ`, `Examples…gibbardInduced_superadditive`, `Examples…gibbardConstitution_upwardClosed` | Yes | **Same** | Example 3.6 is `represents_shirtGame`: both members choose simultaneously, the outcome is the pair of choices, and that game form represents the two-shirt constitution. Example 3.7 is `not_represents_sequentialGame`: with member 2 choosing after observing member 1, member 2 alone forces the two matching outfits, which the constitution does not allow them — print's own reason, at print's own strategy. Example 3.8 computes the effectivity function of Example 2.10's society and is not rendered **Example 3.8 was computed on 2026-09-20 and the row closes**, coverage with it. The eight computed values are print's table, reached through `mem_gibbardConstitution_induced`, which replaces print's eighteen listed values of `γ` with the two closed forms they follow from: the right to remain single is a **veto**, so a coalition holding it is effective for the upward closure of the states nobody in it vetoes, and the right to marry forces a wedding only for a coalition holding both parties to it. **Print ends Example 3.8 with two verifications it leaves to the reader** — *"as the reader may easily verify, `E(·)` is superadditive and monotonic w.r.t. the alternatives"* — and both are theorems here: `gibbardConstitution_upwardClosed` and `gibbardInduced_superadditive`. The second is not quite routine: three of the nine coalition pairs are vacuous because a wedding needs Angelina and two disjoint coalitions cannot both contain her, and the pair that does the work is a veto against a wedding — if one coalition forces a wedding the other contains neither party to it, so that wedding is unvetoed there and lies in its set too. **What is deliberately not rendered is print's next sentence**, *"hence, by Theorem 3.5, `E` is representable"*, which uses the sufficiency half of Theorem 3.5. That half is absent and is costed on the Theorem 3.5 row above; this row grades the computation and the two verifications, all three of which are here. |
| §4 | games and rights, and the relation to Gibbard's paradox | — | No | — | a whole section, and it adds preferences to the model |
| §5 | implementation and Sen's liberal paradox, with Theorem 5.1 | — | No | — | a whole section. It is the paper's connection to Maskin implementation and needs social choice correspondences |
| §§1, 6, 7 | the Arrow discussion, the comparison with related theories of rights, and the conclusion | — | No | — | interpretive |
| — | mandate retention across a delegation | `RetainsFamily`, `retainsFamily_of_represents`, `retainsFamily_of_effectivityEq`, `effectivityEq_of_retainsFamily_univ`, `RetainsFamily.mono_mandate`, `RetainsFamily.mono_coalition`, `retainsWith_of_retainsFamily`, `retainsAgainst_of_retainsFamily` | — | **Beyond** | print states nothing of the kind. This is the atlas's own weakening of Definition 3.4 on three axes at once — one coalition rather than all, inclusion rather than equality, and a mandate family rather than every set — and the two theorems that bracket it show it meets Definition 3.4 exactly at the extremes, so it is a genuine weakening rather than a different notion. The mandate family itself comes from unpublished material and is graded as interpretation, not against a source |
| — | the separations the forcing development was written for | `forces_of_forces_singletons`, `dominated_forces_univ`, `minCard_cannot_separate`, `retainsAgainst_imp_retainsWith`, `hasPowerOver_iff_effectivityGiven_ne`, `mforces_of_factors` | — | **Beyond** | print asks none of these questions. They test an obligation stated in the atlas's own note: whether superadditivity carries information about domination, whether widening a target is a missing capability, whether three readings of "who acts for the principal" are three obligations, and whether a retracted measure separates the cases it claimed to. Peleg supplies the vocabulary and none of the questions |

**22 Yes, 0 Partial, 5 No, 2 Beyond.** Regraded 2026-09-20, when the rights
layer was built, then again when print's other two societies were, and once more
when Theorem 3.5's sufficiency landed. It used to read 10 Yes, 1 Partial, 16 No: this is a paper about
*rights*, and the atlas took only its §3 game-form layer, so the constitution
and everything resting on it graded `No`. `AISafetyAtlas.Sovereignty.Rights`
closes that: the constitution is `Constitution`, (3.1) is
`Constitution.induced`, print's four monotonicity conditions are predicates on
it, and Definition 3.4 is `Represents` at print's right-hand side.

**The owed count went up, and it should have.** Closing Definition 3.4 removed
one `Narrower` cell and converted three `No` rows into `Partial` ones that are
each narrower than print — the §2 examples, Theorem 3.5, and Examples 3.6-3.8.
A `No` row owes nothing because it claims nothing; a `Partial` row owes the rest
of its statement. Section 21 now says more about this paper and is therefore in
debt for more of it, which is the direction the debt is supposed to move.

What the `Yes` rows have in common is worth stating once. **The effectivity
conditions print imposes, the atlas derives** — the whole-space condition,
liveness, the empty-coalition singleton and the grand-coalition family under
surjectivity, monotonicity in the alternatives, monotonicity in coalitions,
superadditivity, and the implication from superadditivity to
coalition-monotonicity. **All four of print's defining conditions on an
effectivity function now have a rendering**, the last of them since
surjectivity stopped being something the cluster had to assume. Print states all four as properties an effectivity function may
or may not have, and Theorem 3.5 turns two of them into the criterion for
representability. For the α-effectivity function of a game form all four are
theorems, which is why `AISafetyAtlas.Sovereignty.Separations` could reach its
conclusion that superadditivity "carries no information about domination": within
this class the condition cannot fail.

With the constitution in the development the same conditions now also appear in
print's own form, as predicates a constitution may fail — `MonotoneAssign`,
`MonotoneAlternatives`, `MonotoneRights`, `MonotoneCoalitions` and
`Superadditive` — and the two readings sit side by side in the rows above. That
is what makes Theorem 3.5 statable at all, and what makes the remaining gap
precise: its sufficiency direction, the construction of a game form from a
prescribed superadditive effectivity function.

---

## 22. List & Valentini 2016, *Ethics* 126(4): 1043-1074, and Carter & Shnayderman 2018, *Political Studies Review* → `AISafetyAtlas.Sovereignty.Independence`

**Graded for the first time on 2026-09-11.** Two sources, one target module, as in
section 4. List and Valentini read from rendered pages 4 and 5 of the pinned
file, which are journal pages 1046 and 1047; Carter and Shnayderman from
rendered pages 4 and 5, which are the article's own pages 4 and 5.

**Which texts.** List and Valentini is the **published** *Ethics* version, sha256
`93fb7dad01fa93d20ce33550…`, 32 pp., manifested
 2026-09-09. Carter and Shnayderman, sha256
`bb5bf47c635036527739b5d6…`, 11 pp., is **not** a final version: its own page 1
gives the pagination as "1–11" and its running head reads "Political Studies
Review 00(0)", so it carries no volume, issue or journal page numbers. It is the
publisher's OnlineFirst text, with DOI `10.1177/1478929918771452` and
"© The Author(s) 2018". The atlas's standing rule is that the published version
is canonical; here the published version *is* this one as far as it goes, and a
later paginated reprint has not been sought. **Every citation of this paper
should therefore give the DOI rather than a page number**, and the rows below
cite the article's own pages.

**Why a philosophy paper is graded at all.** Neither paper numbers a theorem;
both state their central claims in **displayed, italicised theses**, and List and
Valentini's taxonomy is a two-by-two matrix given in four numbered cases. Those
are printed claims with definite content, and the module renders them as
definitions and conditionals. The precedent is section 17: a source that numbers
nothing still gets rows, and the routing says the module states no printed
*theorem*.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| L&V §II definition scheme | *"**Freedom:** An agent's freedom to do X is the absence of relevant constraints on the agent's doing X"* | `Free`, `Counts`, `Setting` | Yes | **Wider** | print's scheme, with the agent, the action and the worlds all arbitrary types. `Free` is the absence of a counting constraint across the worlds the conception looks at, which is print's scheme once both parameters are fixed |
| L&V §II "relevant" | print is deliberately agnostic about which constraints are relevant — intentional only or also structural, physical only or also psychological — and *"encourage[s] the reader to substitute a preferred answer into the qualification 'relevant'"* | `Setting` | Yes | **Same** | the field is an uninterpreted relation, which is exactly print's agnosticism. Nothing in the module narrows it, and no theorem below reads anything into it |
| L&V footnote 8 | *"we do not build criteria of moral permissibility or impermissibility into the specification of 'relevant' constraints; i.e., the notion of 'relevance' should not be 'moralized'"* | `Setting` | Yes | **Same** | this is why the two are separate fields rather than one filtered relation, and the module says so. Print states the requirement in a footnote and the type discipline enforces it |
| L&V §II, the moralization question | *"Is the constraint-absence condition qualified by some moralized exemption clause, according to which morally permissible constraints … do not count as freedom restricting?"* | `Counts` | Yes | **Same** | the answer is the `moralized` parameter, and `Counts` is print's "counts as freedom restricting" at that answer |
| L&V §II, the robustness question | *"Is the constraint-absence condition fortified with a modal robustness requirement, according to which freedom requires the absence of the constraints in a sufficiently large class of possible worlds (relevant hypothetical scenarios) over and above the actual world?"* | `worlds`, `Setting` | Yes | **Same** | the answer is the `robust` parameter. **Print's "over and above the actual world" is carried as a field condition**, not left implicit: the actual world is a member of the relevant class, which is what makes the robust reading genuinely stronger rather than merely different |
| L&V §II | *"The relevant notion of possibility, and which possible worlds matter, can be spelled out in a variety of ways"* | `Setting` | Yes | **Same** | print says the class is a parameter, so it is one. No theorem below fixes it, including the two conditionals — which is why they are conditionals |
| L&V §III, four cases | the four numbered cases: actual absence without exemption; actual absence except when morally permitted; robust absence without exemption; robust absence except when morally permitted | `LiberalFree`, `MoralizedLiberalFree`, `IndependenceFree`, `RepublicanFree` | Yes | **Same** | all four, in print's order, at print's two parameters. The attributions are print's too and are carried in the docstrings — case 1 is Berlin, case 2 is Nozick and Dworkin, case 4 is Pettit's republican freedom, and case 3 is *"what we call 'freedom as independence'"* |
| L&V §III | *"Since 'moralization' and 'robustness' are independent from one another, we arrive at a two-by-two matrix of possibilities"* | `free_of_free_not_moralized`, `free_of_free_robust`, `Examples…four_corners_distinct`, `Examples…matrix` | Yes | **Same** | the two implications order the matrix; `four_corners_distinct` exhibits a `Setting` whose four conceptions are four different sets of free actions, so the dimensions are independent rather than two names for one cell. Closed 2026-09-11. The nonbinary refinement print also names is a different row below |
| L&V §III, families | *"Each case in table 1 corresponds to an entire family of conceptions of freedom"*, subdivided by whether constraints go beyond intentional or beyond physical ones | — | No | — | print's own refinement of the taxonomy. The atlas fixes one relation and does not stratify it |
| L&V §III, nonbinary | *"the moralization and robustness dimensions can themselves be refined and thereby made nonbinary"* — moralization can take various forms, and different levels of robustness can be required | — | No | — | **this is the axis on which the module is narrower than print and it is print that says so.** `Free` takes two `Bool`s, which renders the two-by-two exactly and forecloses the graded versions print explicitly leaves open. Recorded rather than closed: a graded rendering would be a different development, not a widening of this one |
| L&V §III, modality | *"all four families of conceptions of freedom qualify as modal"*, since a constraint depends on facts about other possible worlds | — | No | — | print's claim is about the notion of *constraint* itself, which the atlas takes as a primitive relation indexed by a world. On the atlas's rendering cases 1 and 2 look at the actual world alone, so the printed claim is not visible in the model. A faithful version would have to unfold what a constraint is, which neither module does |
| L&V §IV | the functional-role desideratum, that an obstacle counts as a source of unfreedom iff it stands in need of justification | — | No | — | the paper's positive argument for case 3, and the thing Carter and Shnayderman turn against it |
| L&V, remainder | the case for freedom as independence, the arguments against the other three conceptions, and the political implications | — | No | — | the bulk of the paper. The module takes the taxonomy and not the argument |
| **C&S thesis 1** | *"**The impossibility of republican freedom.** Republican freedom entails that no one is ever free to do anything whatsoever, not even in a republican state, given that there is always a relevant possibility that a person or a group of persons will succeed in acquiring the means that would enable them to take over the state and thereby possess more or less absolute arbitrary power…"* | `not_republicanFree_of_impermissible_threat` | Yes | **Same** | print's thesis as a **conditional**, which is the honest rendering: print's antecedent is a claim about politics — that a takeover is always a relevant possibility — and that is a hypothesis here, not a theorem. The conclusion is print's, at print's quantifier: nobody, no action |
| **C&S thesis 2** | *"**The impossibility of freedom as independence.** Freedom as independence entails that no one is ever free to do anything whatsoever. But this entailment depends not only on the particular case of a threat to any regime … it depends also on the countless threats which everyone constantly faces in everyday situations"* | `not_independenceFree_of_universal_threat` | Yes | **Same** | the second thesis, again as a conditional, and again at print's quantifier |
| C&S §"Probability Versus Sheer Possibility" | the asymmetry between the two theses: on Pettit's conception a power to interfere must be *arbitrary*, hence possessed with impunity, so everyday threats inside a republican state are punished and do not count — whereas freedom as independence drops arbitrariness and so the everyday threats do count | `not_republicanFree_of_impermissible_threat`, `not_independenceFree_of_universal_threat` | Yes | **Same** | **this asymmetry is the paper's actual argument and it is visible in the two hypotheses rather than stated as prose.** The republican thesis needs a relevant world carrying an *impermissible* constraint; the independence thesis needs only a constraint. That difference is exactly print's dropped arbitrariness requirement, and it is why the second thesis is the stronger claim. Nothing in the module editorialises about it |
| C&S | the Kramer argument that acquiring arbitrary power is a matter of probability rather than binary possibility, and *"the very low probability of anyone actually killing us is irrelevant"* on this conception | — | No | — | print's positive diagnosis, and the atlas neither renders nor rebuts it here. `AISafetyAtlas.Sovereignty.Boundary` answers it in prose for its own predicate — that an all-profiles invariant is the right shape against an adversary that is searching rather than sampling — and that reply is a docstring, not a theorem |
| C&S, remainder | the reply to List and Valentini's nearby-worlds qualification, the functional-role discussion, and the conclusion | — | No | — | interpretive |
| atlas, lattice | the implication lattice print leaves implicit | `free_of_free_not_moralized`, `free_of_free_robust`, `republicanFree_of_independenceFree`, `liberalFree_of_independenceFree` | — | **Beyond** | print says which cases are more demanding and proves nothing about it. These four make it precise: moralizing can only add freedom, robustness can only remove it, and freedom as independence therefore implies both liberal and republican freedom. That last pair is what makes case 3 *"the corner that cannot escape"* — it is the strongest of the four, so an impossibility for it is the weakest premise from which the others follow |
| atlas, boundary | Carter and Shnayderman's argument turned on the atlas's own predicate | `not_sovereign_of_outsider_moves_view` | — | **Beyond** | print says nothing about game forms. `AISafetyAtlas.Sovereignty.Boundary` states their objection *inside the model*: if any outsider can move the protected view by a unilateral deviation, the coalition is not sovereign. That module sits in the "no printed source to grade" list below, and that classification is still right — the statement is about the atlas's `Sovereign`, not about print's freedom predicate — but the module does render print's argument, and this row is where that is recorded |

**11 Yes, 0 Partial, 7 No, 2 Beyond.** Both papers' central claims are here:
List and Valentini's two questions, their four cases with print's own
attributions, the independence of the two dimensions, and both of Carter and
Shnayderman's displayed theses, each as a conditional on the political premise
print supplies.

**The independence row closed on 2026-09-11.** Print's taxonomy is asserted to
be a genuine two-by-two — *"moralization and robustness are independent from
one another"* — and `Examples.Sovereignty.four_corners_distinct` is a `Setting`
in which the four conceptions are four different sets of free actions. The two
implications that order the matrix remain; they no longer have to carry the
independence claim by themselves.

**What the two `No` rows about refinement mean together.** Print says the cases
are families and that both dimensions can be made nonbinary; the module's two
`Bool`s are print's presentation and not print's full claim. This is a narrowing
the source itself identifies, which is the most checkable kind, and it is
recorded rather than quietly widened.

---

## 23. Chen, Ju & Ågotnes 2026, arXiv:2607.10567v1 → `AISafetyAtlas.Sovereignty.Separations`

**Graded for the first time on 2026-09-11.** Statements read from rendered pages
8 and 10 of the pinned file. The module reads this source for two definitions
and is graded against those; the rest of a 50-page paper is inventoried below.

**Two files, and they are two different papers.** The literature directory holds
`chen-ju-agotnes-arxiv-v1-…-general-cgf.pdf` and
`chen-ju-agotnes-arxiv-v2-…-two-agent.pdf`, and the `v1`/`v2` in those names is
**not** a version number. The first is **arXiv:2607.10567v1**, *Representation
theorems for actual and alpha powers over general concurrent game frames without
assuming independence of agents*, sha256 `c7aece726de1b7a7a106c646…`, 50 pp. The
second is **arXiv:2603.04160v2**, *… over **two-agent** general concurrent game
frames*, sha256 `4cb9ce1ce71e5d60726376…`, a separate submission with a different
identifier and a different title. Each file's own margin stamp says so. The atlas
cites arXiv:2607.10567 and **this section grades that file only.**

**A citation defect this section found, and it is ours.** The docstring of
`ActualPower` cites arXiv:2607.10567 and then quotes, as "the literature's stated
objection" to α-monotonicity, the sentence

> "can obscure relevant information about the power structure in the game: we
> don't know whether two sets a coalition has the power to enforce correspond to
> the same or different joint actions."

**That sentence is not in arXiv:2607.10567.** It is in the *two-agent* paper,
arXiv:2603.04160v2 — the file the manifest records as "not yet read" — and there
it is not the authors' own claim either: it is prefaced *"as pointed out by
[BBE19]"*, so the objection belongs to a third source that the atlas has not
pinned. The docstring's wording ("the literature's") is not false, but a reader
follows the citation two sentences above it and lands on the wrong paper. The
docstring is amended in the same commit to say which file the sentence is in and
whose objection it is.

**What the atlas's `GameForm` is, in this paper's vocabulary — and a correction
this section owed itself.** Print's frames carry a state set and send a
coalition's joint action to a *set* of possible successor states. `GameForm` has
no states and sends a complete profile to one outcome. In print's taxonomy it is
the **SID** case — serial, independent and deterministic — which print's own page
confirms: *"The standard class of concurrent game frames corresponds to the SID
case. For this class, the corresponding representation theorem for what we call
alpha powers is Pauly's representation theorem."*

Until 2026-09-20 this paragraph and the module header both added *"at a single
state"*, and that is **wrong**. With a one-point state set every alpha power is
trivial, because a coalition's only possible successor is the point it is
already at. `gameFrame`, in `AISafetyAtlas.Sovereignty.ConcurrentGameFrame`, is
the embedding that makes the claim true, and its state set is the **outcome
type** with state-independent dynamics: from every state the same one round is
played. That is what makes `alphaPower_gameFrame` an equivalence with `Forces`
rather than a triviality, and the error was invisible while nothing in the atlas
could state print's carrier.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| **Definition 1** | an *action frame* is a nonempty state set, a nonempty action set, and for each coalition an availability function and an outcome function into sets of states | `ActionFrame`, `restrictJA`, `jointUnion` | Yes | **Wider** | **Built 2026-09-20**, as the carrier the four rows below were owed against. `av` and `out` are print's two families, indexed by coalition and state, and a joint action of a coalition is print's `JA_C`, a function from the coalition to the action set. `restrictJA` is print's restriction bar and `jointUnion` is print's union of joint actions on disjoint coalitions. Wider on three axes, each a dropped hypothesis: print's agent set is finite and nothing here needs it, and print's two nonemptiness conditions are carried on the theorems that use them rather than in the carrier |
| **Definition 5**, alpha | the *alpha effectivity function* of an action frame collects the sets that some available joint action of the coalition drives the outcome into | `AlphaPower`, `alphaEff`, `SafeFor`, `alphaPower_gameFrame`, `alphaEff_gameFrame` | Yes | **Wider** | **Closed 2026-09-20.** print's condition exactly, at print's own carrier: a state, an available joint action of the coalition, and every possible successor inside the target. The narrowing this row carried was never the condition but the carrier — one state, one successor — and `AISafetyAtlas.Sovereignty.ConcurrentGameFrame` supplies print's. Wider for the reason the Definition 1 row is. `Forces` and `effectivity` survive as the `SID`-corner instance: `alphaPower_gameFrame` and `alphaEff_gameFrame` identify them as the alpha effectivity function of the frame a game form induces |
| **Definition 5**, actual | the *actual effectivity function* collects the outcome sets themselves, one for each available joint action of the coalition | `ActualPowerAt`, `actualEff`, `TightFor`, `actualPowerAt_iff_out_eq`, `mem_actualEff_iff`, `ActualPowerAt.alphaPower`, `actualPowerAt_gameFrame` | Yes | **Wider** | **Closed 2026-09-20**, on the carrier the row above names. print's *safe* and *tight* are `SafeFor` and `TightFor`, `ActualPowerAt` is their conjunction at an available joint action, and `actualPowerAt_iff_out_eq` is print's own *"equivalently"* — the actual powers are exactly the outcome sets of available joint actions. `ActualPowerAt.alphaPower` is print's immediate observation that the actual notion implies the alpha one, and `actualPowerAt_gameFrame` keeps `ActualPower` as the `SID`-corner instance |
| p. 8 | *"From the definition, it is immediate that each alpha effectivity function is closed under supersets"* | `AlphaPower.mono` | Yes | **Wider** | print's immediate consequence, at print's carrier. The `SID`-corner version is `Forces.mono` |
| coalition monotonicity | *"enlarging a coalition cannot destroy an alpha power"* — the alpha family of a subset coalition is contained in that of a superset coalition | `IsGCGF.alphaPower_mono_coalition`, `IsGCGF.exists_av_univ_restrict`, `endFrame_alphaPower_univ` | Yes | **Wider** | a named property of alpha powers, used in the proof of print's Fact 2. **Wider in a way that is not only the carrier, 2026-09-20**: at print's frames it needs **no seriality at all**. The outcome-driven availability condition extends the smaller coalition's action to an available grand-coalition action and outcome monotonicity does the rest, where the `SID`-corner version `Forces.mono_coalition` carries inhabitance of every strategy type. `endFrame_alphaPower_univ` instantiates it at a frame that is **not** serial |
| **Definition 9**, seriality | a frame is *serial* when every coalition has some available joint action at every state | `Serial`, `gameFrame_serial`, `endFrame_not_serial` | Yes | **Wider** | **Closed 2026-09-20.** `Serial` quantifies over states, so it can hold at one and fail at another, and `endFrame_not_serial` is print's own motivating case — a game that ends, whose later state has nothing available for anybody. The `SID`-corner rendering, inhabitance of each strategy type, is a property of the *types*: `gameFrame_serial` shows it implies print's condition, and nothing there can express the failure |
| **Definition 9**, independence | a frame is *independent* when, for disjoint coalitions, an action available to each is jointly available to their union | `Independent`, `gameFrame_independent`, `clashFrame_not_independent`, `exists_gcgf_not_superadditive` | Yes | **Wider** | print's condition at print's carrier, where it is a condition a frame may fail — `clashFrame_not_independent` is one that does. A game form **builds it in**: strategies are dependent functions, so any two choices on disjoint index sets combine, which `gameFrame_independent` proves with no hypothesis whatever. That is exactly why superadditivity is a theorem in the atlas rather than a hypothesis, and `exists_gcgf_not_superadditive` shows the converse side of the same coin: off the independent classes superadditivity is **false** |
| **Definition 9**, determinism | a frame is *deterministic* when the grand coalition's action determines a single outcome | `Deterministic`, `gameFrame_deterministic`, `coinFrame_not_deterministic` | Yes | **Wider** | print's condition at print's carrier, where the outcome function returns a *set*, so determinism is a condition rather than a shape. `gameFrame_deterministic` is it for a game form, whose `outcome` is a function; `coinFrame_not_deterministic` is a frame with two possible successors |
| **Definition 9**, the eight classes | the eight labels obtained by imposing each subset of seriality, independence and determinism, and the notion of an X-frame | `FrameClass`, `card_frameClass`, `IsFrame`, `isFrame_epsilon_iff`, `isFrame_sid_iff`, `gameFrame_isFrame_sid` | Yes | **Wider** | **Closed 2026-09-20.** A label is three bits, `card_frameClass` is print's *"eight strings"*, and `IsFrame` imposes exactly the conditions the label names. `gameFrame_isFrame_sid` places the atlas's older carrier: every row this section graded against a game form is a row about the `SID` corner |
| p. 10, *On the eight frame classes* | *"The labels in ES record which frame conditions are imposed; they do not record which conditions are required to fail. Thus the eight classes are not intended to be disjoint … we mean the four labels not containing I, not the class of frames in which independence fails"* | `isFrame_mono`, `isFrame_of_sid`, `vetoGame_isFrame` | Yes | **Wider** | **print's caution, and the atlas's own docstring needed it.** The `forces_superadditive` docstring said superadditivity "is not available in the classes where [independence] is [dropped]", which reads as *fails there*. Print says the opposite, and `isFrame_mono` is that: weakening a label cannot lose a frame. `isFrame_of_sid` and `vetoGame_isFrame` put one frame in all eight classes at once, so the classes are visibly not disjoint |
| **Fact 1**, item 1 | *outcome monotonicity*: extending a joint action to a larger coalition can only shrink the set of possible outcomes | `IsGCGF.out_anti_coalition` | Yes | **Wider** | **Closed 2026-09-20.** print's statement, about the outcome *sets* of joint actions rather than the effectivity-level consequence, and now at print's own carrier: states, and nondeterministic outcome sets. The `SID`-corner version stays in `AISafetyAtlas.Sovereignty.Separations` as `outcomesOf_anti_coalition`, with `vetoGame_outcomesOf_strict` showing the inclusion can be proper there; an earlier note on this row said it degenerated to equality of singletons, which was false of `SID` frames and is why that witness exists |
| **Definition 8** | a general concurrent game frame is an action frame satisfying the grand-coalition-induced outcome condition and the outcome-driven availability condition | `IsGCGF`, `IsGCGF.mem_out_iff`, `IsGCGF.mem_av_iff`, `gameFrame_isGCGF` | Yes | **Wider** | **Closed 2026-09-20.** Both conditions verbatim, the first as print's union over the extensions of a joint action. `IsGCGF.mem_out_iff` and `IsGCGF.mem_av_iff` are their pointwise forms, and every later proof runs through those rather than through the union. `gameFrame_isGCGF` says a game form's induced frame satisfies both |
| **Fact 1** item 2 | the *alternative GCI-condition*: the same union taken over the grand coalition's available actions only | `IsGCGF.out_eq_iUnion_av` | Yes | **Wider** | print's reformulation, on print's own reason — unavailable grand-coalition actions have empty outcome sets, so they contribute nothing to the union |
| §1, the objection to alpha | alpha powers are inherently monotonic, and that *"can obscure relevant information about the power structure in the game"* — two sets a coalition can enforce may or may not correspond to the same joint action | `pinned_actualPower_singleton`, `pinned_not_actualPower_pair`, `pinned_forces_pair`, `ActualPower.forces` | Yes | **Wider** | print states the objection in prose and motivates the actual notion by it; the atlas **exhibits** it. A principal pinned to one outcome alpha-forces the pair containing a second outcome, by monotonicity alone, and has no actual power over that pair. So the two notions come apart exactly where monotonicity is doing the work. See the provenance note above: the quoted sentence is from the companion two-agent paper and is there credited to a third source |
| Definitions 2-4, 6, 7, 10-32 | alpha and actual neighborhood frames, nonmonotonic cores, representability, groundedness, liveness, and the constructions the representation theorems run through | — | No | — | twenty-two further numbered definitions. Definitions 1 and 8 moved out of this row on 2026-09-20 and have rows of their own; what stays is the neighborhood-frame layer and the representation program, and the atlas builds none of it |
| Theorems 1-8, Lemmas 1-14, Propositions 1-2, Corollary 1, Fact 2, Examples 1-4 | the representation theorems themselves — which classes of frames are represented by which classes of neighborhood frames, with and without independence | — | No | — | **this is the paper**, and none of it is here. The atlas uses the source for two definitions and one motivating objection, and claims nothing about representation. Grouped rather than listed because the alternative is thirty rows that all say the same thing |
| — | forcing against a constrained environment | `ForcesGivenEnv`, `forcesGivenEnv_true_iff`, `ForcesGivenEnv.mono_env`, `triad_power_when_aligned`, `triad_no_power_when_neutral`, `power_depends_on_environment` | — | **Beyond** | print quantifies over every completion, and so does every notion in it. This layer makes a coalition's reach depend on which profiles the remaining parties actually take, so that a bystander is not an adversary. The module's own docstring names partition function form games as the prior art and says the combination is **unchecked** against sources and claims no novelty — which is the right standing for it, and this row does not upgrade that |
| — | building the frame from the grand coalition's outcome function, and the empty set | `ActionFrame.ofGrand`, `ofGrand_out_univ`, `ofGrand_isGCGF`, `IsGCGF.not_alphaPower_empty`, `exists_gcgf_not_superadditive` | — | **Beyond** | print says the two conditions of Definition 8 *determine* the coalition-level outcome and availability functions from the grand coalition's outcome function and never builds the map; `ActionFrame.ofGrand` is it, and every frame witnessed in this section is built with it. `IsGCGF.not_alphaPower_empty` — no coalition is ever effective for the empty set — is one line from those two conditions, print does not state it, and it is what makes `exists_gcgf_not_superadditive` work: two disjoint coalitions with disjoint alpha powers at a frame that is not independent |

**14 Yes, 0 Partial, 2 No, 2 Beyond**, regraded on 2026-09-20 from 9 Yes, 0
Partial, 5 No, 1 Beyond. The atlas now reads this paper for **its carrier** —
Definitions 1, 5, 8 and 9 and both items of Fact 1 — rather than for two
definitions and an objection. The two grouped `No` rows carry twenty-two
definitions and every numbered result, because the representation theorems are
what the paper is for and the atlas does not touch them. Grading those
individually would produce thirty rows saying the same sentence.

**What the four owed cells cost, against what they were priced at.** The row
above priced them at one move: a state set, state-indexed effectivity, and an
outcome map that is a relation. That was right about the shape and wrong about
the object. Print's frames without independence cannot have per-agent action
sets at all — availability is a family indexed by *coalition* — so the move is
not an edit to `GameForm` but a second carrier, `ActionFrame`, with `gameFrame`
placing the old one at the `SID` corner. What the estimate missed in the other
direction is that print's Definition 8 makes everything a consequence of the
grand coalition's outcome function, so the carrier arrives with its own
constructor and the four rows closed together with five more.

**What this section repairs.** Two provenance defects, both ours and neither
mathematical. The quoted objection in `ActualPower`'s docstring is not in the
cited paper but in its companion, where it is credited to a third source; and
the `forces_superadditive` docstring inverted print's own caution about the eight
frame classes, saying a condition is unavailable where print says only that it is
not imposed. Both docstrings are corrected in the same commit. The mathematics in
both is unaffected: `ActualPower` is Definition 5's actual effectivity function
and `forces_superadditive` is Definition 9's independence condition, and both
rows grade `Yes`.

---

## 24. Melo, Máximo, Soma & Castro 2024, arXiv:2408.08995v1 → `AISafetyAtlas.Verification.AgentBehavior`

**Graded for the first time on 2026-09-11**, and this closes the module-ledger's
live debt. Statements read from rendered pages 1, 3 and 4 of the pinned file, 7
pp., sha256 `66eb3448f8f36602d71f65c1…`, manifested
 2026-09-11.

**What was actually wrong, and it was not the ledger line.** The module-ledger
listed this module as owed against *"Melo, Maximo, Soma and Castro,
arXiv:2408.08995"*, while the module's own header named **Rice 1953** as its
source and filed this paper under *"Related literature"*. Reading the paper shows
**both roles are real and the header had them the wrong way round**: this paper
states the claim the module's theorem renders, and Rice's theorem is the *proof
route* — reached through Mathlib, not through this paper. So unlike section 20,
where the ledger line named the wrong source outright, here the ledger line was
**right** and the header was misleading about which work plays which role. The
header is corrected in the same commit to read *statement: Melo; proof route:
Rice, via Mathlib*.

**And the check could not have caught either.** The module was reported unrowed
while `BY-012` names its theorem — in that row's Lean-artifact declaration list,
which the module-ledger check does not read, as recorded above. But `BY-012` is
the row for the *proof route*: it is an upstream-reuse row for Rice whose
formalization modules are Mathlib's and Isabelle's, and it never claimed to be
the statement row. The statement row did not exist until today.
`LAND-VERIF-AGENTBEHAVIOR-001` is it.

**It numbers nothing.** No theorem, definition, lemma, proposition or corollary
appears in the seven pages. The precedent for grading it anyway is section 17 and
section 20: an unnumbered printed claim a module renders gets rows.

**Rice is cited by this file and pinned by nobody.** `ams.org` returns HTTP 403
to automated requests for both the volume contents and the article PDF, and no
attempt was made to work around that. **No grade depends on it**: the atlas does
not formalize Rice's statements — Mathlib's `ComputablePred.rice` does, and the
atlas consumes it — so this is a citation without a pinned copy, recorded in the
manifest under "Named, not pinned", and not an ungraded source.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| abstract, and §Formal Proof | *"The inner alignment problem, which asserts whether an arbitrary artificial intelligence (AI) model satisfices a non-trivial alignment function of its outputs given its inputs, is undecidable"*, concluding *"there is no Turing machine that decides P"* | `no_behavioral_safety_verifier` | Yes | **Same** | print's claim at print's own quantifiers: an arbitrary model, a fixed non-trivial judge of outputs given inputs, and no decider. The Lean proof reduces through the atlas's `rice` packaging of Mathlib's Rice, which is print's own first route — see the `No` row below for the route it does not take |
| §Formal Proof, extensionality | *"The property as defined by the acceptance of the output given the input by a judge function is a property of the language of the TM, as for any two TMs that accept the same language, either both satisfice the judge function or neither"* | `SafetySpec`, `Satisfies` | Yes | **Same** | print's extensionality condition, made structural rather than assumed: a specification is a property of the partial input/output map, so two agents with the same meaning satisfy exactly the same specifications by construction. Print has to argue it; here it cannot fail |
| §Formal Proof, non-triviality | *"The non-triviality of the judge function guarantees the non-triviality of the property, as a TM can be built to always output the dummy positive values, and a TM can be built to output at least one dummy negative value"* | `SpecNontrivial` | Yes | **Same** | print supplies **both witnesses**, a satisfying program and a non-satisfying one, rather than only the adjective — so this is not the pattern of section 18, where a needed hypothesis appears nowhere. `SpecNontrivial` is those two halves, and it is a hypothesis of the theorem rather than a standing assumption |
| §Formal Proof, the decider | *"Assume that there is a Turing machine M_P that decides P"* | `BehavioralSafetyVerifier` | Yes | **Same** | print's "decides" unpacked into the three things it means and no more: a **total** `Bool`-valued procedure, **computable**, and correct in **both directions**. The atlas is more explicit than print here and claims nothing print does not |
| §Formal Proof, the agent | an AI model is equivalent to its Turing machine, and the reduction's constructed machine *"computes a **partial function** with property P"* | `Agent` | Yes | **Same** | **print's objects are partial functions and so are the atlas's**, meaning `ℕ →. ℕ`. Worth stating because the paper is titled *Machines that Halt* and a reader would expect totality; the halting material is print's *proposal*, in the sections graded `No` below, and not a hypothesis of its undecidability claim |
| §Formal Proof, the halting reduction | the explicit construction of a machine that simulates `M` on `i` and computes a function with property `P` exactly when `M` halts, turning a decider for `P` into a decider for the Halting Problem | — | No | — | print offers **two** routes — *"could simply be reduced to a restatement of Rice's Theorem"*, and then this one — and the atlas takes the first. Nothing here reduces to halting, and `AISafetyAtlas.Computability` builds no halting-problem bridge. Recorded because a reader of print's proof will look for it |
| Figure 1 | the construction of an adversarial model that would fool any program claiming to decide the alignment problem, and the informal regress about ever-bigger verifying computers | — | No | — | print's motivating picture, which it calls *"this informal intuition"* before giving the formal proof. No content beyond the theorem |
| §Discussions | *"it is possible to do so for an enumerable set of AI systems that are architecturally designed … an initial set of finite models and operations that obey and preserve the property; those are called the axioms"* | — | No | — | the paper's positive claim and the second half of its abstract. It is an **architecture argument rather than a theorem**: print exhibits no enumeration and proves no closure property, so there is no printed statement to render. This is the largest thing in the paper the atlas does not touch |
| §A Special Decidable Case | feed-forward and unrolled recurrent networks always halt, so with inputs of a fixed length `L` one can check all `2^L` of them and alignment becomes decidable *"though untractable"* | — | No | — | a decidability claim in the opposite direction, on a restricted class. The atlas holds no finite-model layer for it, and it would not follow from anything here: `no_behavioral_safety_verifier` quantifies over all program codes |
| Figure 2, and the halting constraint | the masking architecture that runs the judge at inference and substitutes a dummy output when it disapproves, and the proposal that a judge function must itself impose a halting constraint | — | No | — | print's proposal, and the paper's actual recommendation. Neither is a claim the atlas could state without an architecture model |
| — | the semantic-to-code bridge | `rice`, `rice_code_iff` | — | **Beyond** | print states nothing of the kind, because it works informally with "the language of the TM". The atlas has to cross from a property of partial functions to a property of program codes before Mathlib's Rice applies, and these two declarations are that crossing. It is the step print's phrase *"given the equivalence of an AI model to its Turing Machine"* waves at |

**5 Yes, 0 Partial, 5 No, 1 Beyond.** Everything this paper establishes is here,
and the five `No` rows are its second half — an architecture proposal, a
restricted decidable case, and a picture — none of which is a printed statement.
The one route print gives that the atlas does not take is its halting reduction,
and print itself offers the Rice route first.

**Read the `Same` column carefully here.** All five graded rows are `Same`, and
none of them is a widening, because the atlas's extra precision goes into
*unpacking* print's words rather than weakening its hypotheses: "decides" becomes
three explicit fields, "property of the language" becomes a type, and the two
non-triviality witnesses print describes become the hypothesis's two halves. The
only place the atlas does more than print is the `Beyond` row, which crosses a
gap print's informality lets it step over.

---

## 25. Klamka 1972, IEEE TAC 17(5):725–726 → `AISafetyAtlas.LinearSystems`

**Graded for the first time on 2026-09-11**, the same day the module it grades
landed. Both printed pages read as rendered images, sha256
`fdaa652dc63e69a5bcae88cd679d2b78…`, manifested
 2026-09-11. The file was supplied by the maintainer
after the triage note recorded that IEEE Xplore would not serve it.

**Why this section exists, and what it corrects.** This two-page note is the
cited source of the survey rows `BY-001` (Unobservability) and `BY-002`
(Uncontrollability of dynamical systems). Earlier the same day, before the paper
was in hand, `docs/provenance/by001-by002-linear-systems-triage.md` reasoned from
a catalogue description that print gives a **minimal-polynomial sufficient**
condition rather than a rank characterization, and stopped at `CANDIDATE_LEAD`
for that reason. **The pages confirm it.** Print's abstract: *"A simple test
based on the properties of the minimal polynomial yields the sufficient
conditions for uncontrollability and unobservability."* Every numbered result is
a one-directional counting bound, and none of them is the Kalman rank criterion
or the Hautus test that `AISafetyAtlas.LinearSystems` carries.

**The object is shared; the theorems are not.** Print's system is
`ẋ = Ax + Bu`, `y = Cx` with `A` of shape `n × n`, `B` of `n × p` and `C` of
`q × n` — the atlas's matrices exactly. Print's property is complete state
controllability (observability), which for a linear time-invariant system is
what the Kalman criteria characterize. So this is **not** the keyword-false-friend
situation the earlier AFP triage found: the atlas holds the standard algebraic
characterization of the very property print reasons about.

**Updated 2026-09-13.** When this section was written the atlas held *none* of
print's six numbered statements: it held strictly stronger theorems with a
different antecedent, and the inequality that would let print's antecedent reach
them — print's equation (5) — was not in the tree. It is now, in
`AISafetyAtlas.LinearSystems.BlockBound`, together with print's Theorem 1,
Theorem 2 and Corollaries 1 and 2 stated at print's own quantities. Corollaries 3
and 4 are still `Partial`, for a reason given in their rows. **Updated again
2026-09-20, and the sentence that stood here is retracted.** It read: *"What has
not changed is the thing that matters to `BY-001` and `BY-002`: nothing here
defines a trajectory, a solution or an output signal, so the state cannot be
reconstructed from the outputs is still not proved anywhere in this
repository."* `AISafetyAtlas.LinearSystems.Dynamics` defines `IsTrajectoryOn`
and `outputSignal`, `AISafetyAtlas.LinearSystems.Flow` builds the matrix
exponential and variation of constants, and
`determinesStateOn_iff_isObservable` and `isCompletelyReachable_iff_isControllable`
prove each criterion **equivalent** to the property it is named for. The Intro
row below carries the detail.

**What print proves.** Write `λᵢ` for the distinct eigenvalues, `nᵢ` for the
multiplicity of `λᵢ` in the characteristic polynomial, `νᵢ` for its index — its
multiplicity in the minimal polynomial — `αᵢ` for the number of Jordan blocks
carrying `λᵢ`, `r` for the rank of `B` and `m` for the rank of `C`. Print bounds
the block count below by `⌈nᵢ/νᵢ⌉`, notes that the Jordan-form input matrix has
rank `r`, and concludes that when the bound exceeds `r` the rows that a known
criterion requires to be independent cannot be. Its stated advantage is that
`λᵢ` itself is never needed, only `nᵢ` and `νᵢ`, and that the transformation
matrix `T` need not be computed.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §Intro, the system | the linear time-invariant system `S` given by `ẋ(t) = Ax(t) + Bu(t)`, `y(t) = Cx(t)`, with state `n × 1`, input `p × 1`, output `q × 1`, and its complete state controllability and observability | `IsControllable`, `IsObservable`, `IsTrajectoryOn`, `IsTrajectory`, `outputSignal`, `DeterminesStateOn`, `IsReachable`, `isObservable_imp_determinesStateOn`, `not_determinesStateOn_of_not_isObservable`, `determinesStateOn_iff_isObservable`, `not_isReachable_of_not_isControllable`, `eigenTrajectory`, `flow`, `drivenState`, `drivenState_isTrajectory`, `adjointFlow`, `reachedSet`, `IsCompletelyReachable`, `isCompletelyReachable_iff_isControllable`, `isReachable_iff_isControllable`, `adjointSignal_eq_zero_of_dotProduct_drivenState_eq_zero`, `eq_zero_of_adjointFlow_eq_zero` | Yes | **Wider** | **the matrices were print's and the dynamics were not, and that is no longer the reading.** Shapes, roles and field match; `IsControllable` and `IsObservable` are the standard algebraic characterizations of print's two properties. The sentence this note opened with until 2026-09-20 — *"nothing in the atlas defines `ẋ`, a solution, or an output signal, so print's notions are not defined here, only an equivalent condition is, and the equivalence is not proved either"* — is now false in all three of its clauses, and the paragraphs below say what replaced each. This is the one row where the atlas's own earlier notes were the thing most in need of correction, and the paragraphs below keep each retraction rather than deleting it. **The two equations came first.** `IsTrajectoryOn` is `ẋ(t) = Ax(t) + Bu(t)` asked on a set of times, `outputSignal` is `y(t) = Cx(t)`, and `DeterminesStateOn` is complete state observability *as the property* — the output determining the states the system passed through — rather than as a criterion for it. **Closed on 2026-09-20, and both of print's properties are now equivalences rather than criteria.** `determinesStateOn_iff_isObservable`: the rank criterion holds **exactly when** the output determines the state, on any non-empty open window. `isCompletelyReachable_iff_isControllable`: the rank criterion holds **exactly when** the system is completely state controllable at print's own quantifier — a run between **any** two states, not only out of the origin. Page 726 states both equivalences and attributes them to Chen and Desoer; `NC-013` in `formalization-search.json` records that no proof assistant had the continuous-time reachability one when the search was run that morning. **The construction is the classical one with the Gramian removed.** `flow A t` is *e^{At}*; `drivenState A B u` is *x(t) = Φ(t) ∫₀ᵗ Φ(-s) B u(s) ds* and `drivenState_isTrajectory` is variation of constants, with the two flow factors written apart so that only the upper limit of the integral depends on the time — which turns the derivative into a product rule and a fundamental theorem of calculus rather than a differentiation under the integral sign. Then three pieces replace the Gramian: `reachedSet` makes the states reached at a fixed positive time a subspace; `adjointSignal_eq_zero_of_dotProduct_drivenState_eq_zero` shows that a covector annihilating that subspace makes the adjoint signal silent, **because the input that exposes the silence is the signal's own conjugate**, so the integrand is a non-negative real; and `eq_zero_of_adjointFlow_eq_zero` kills the covector, through `isControllable_iff_isObservable_transpose`, which the cluster already had. **Four costings of this cell were wrong, all in the same direction, and they are retracted here.** Each priced machinery the tree already held or Mathlib already had. Cayley-Hamilton was **already spent** — `A_mulVec_mem_unobservableSubspace_of_mem` in `Hautus` — so lifting the `Fin n`-indexed criterion to every natural power took six lines. The matrix exponential was **not needed** for the observability converse, because `exists_eigenvector_of_unobservableSubspace_neBot` was in the cluster and an eigenvector turns the matrix exponential into a scalar one. The matrix **norm instance** was guessed to be the friction and is one scoped `open`. And the **Gramian** was named as the only route to sufficiency; it is not, and the route that replaces it needed one lemma Mathlib does not state in one piece — that a non-negative continuous function with vanishing interval integral is zero, here `eqOn_zero_of_intervalIntegral_eq_zero`. **`Wider`, on one axis and in the disclosed direction.** `DeterminesStateOn` and `IsTrajectoryOn` carry the time window as a parameter and the observability equivalence is proved at **any** non-empty open window. **The reachability statements do not carry that parameter, and the asymmetry is a decision rather than an oversight.** Print writes `ẋ(t) = Ax(t) + Bu(t)` with no domain restriction, so the whole line *is* print's reading, and there is no narrower class of interval runs in print for the atlas to fall short of; the observability side then goes past print by holding on every window as well. Nothing is narrower at either end: the necessity directions quantify over trajectories under an **arbitrary** input, while the sufficiency direction produces a **continuous** one, so the atlas proves more than print asks on both. Witnessed at two systems that fail the criteria — a blind readout and a deaf input — and at one that meets them, the integrator, where `Examples…integrator_drivenState_eq_ramp` proves the general construction reproduces the hand-written solution. **Two findings against the earlier note.** The first: `IsControllable` **was already a reachability notion** — its own docstring says *"every state can be reached from the origin in `n` steps via some sequence of inputs"* — but in **discrete** time, for the difference equation *x(k+1) = A x(k) + B u(k)*, while print's system is continuous. The rank criterion is the same for both, and that shared criterion is what this cluster proves, so the axis was never that the atlas lacks a reachability notion; it is that it had the discrete one. The second is from the rendered page. The note said print's notions are not defined in the atlas while implying print defines them. Print does not: page 726 reads *"It is well known [1] that the system `S` is completely state controllable (observable) if and only if for each `i` the set of `αᵢ` row vectors (column vectors) … are linearly independent over the field of complex numbers"*, citing Chen and Desoer. So print states the criterion it reasons with — the Jordan-block one — and imports the notion behind it, which is the same move the atlas makes with the Kalman criterion. The axis was therefore never *"print has dynamics and the atlas does not"*; it was that neither print nor the atlas connected its criterion to the property. The atlas now connects both, both ways. |
| §Intro, the notation | `λᵢ` distinct eigenvalues, `φ` the characteristic and `ψ` the minimal polynomial, `nᵢ` the multiplicity in `φ`, `r` the rank of `B`, `m` the rank of `C` | `charpoly_mulVecLin`, `minpoly_mulVecLin` | Partial | **Same** | **Regraded 2026-09-20 from `No`, and the earlier grade was a miscount rather than a change.** The note this replaces read *"no atlas declaration names the eigenvalue multiplicities of a state matrix"*, and that had been false since 2026-09-13, when `not_isControllable_of_ceil_div_gt_rank` began quantifying over the multiplicity of `μ` in the characteristic polynomial of `A` — print's `nᵢ` written out. What 2026-09-20 added is print's `νᵢ`, the multiplicity of `μ` in the minimal polynomial of `A`. Both polynomials are Mathlib's; what the atlas supplies is the identification of each with the matrix's own, which is what lets print's two multiplicities be read off `A` and not off the map it induces. `Same`, because both bridges are stated at print's own field and shape. Still `Partial` and not `Yes`: nothing here enumerates print's *distinct* eigenvalues `λᵢ`, and `r` and `m` are `Matrix.rank` with no atlas declaration naming them |
| §Intro, the index | the index `νᵢ` is the least `w` with `ker (A - λᵢ I)^w` stationary, and equals the multiplicity of `λᵢ` in the minimal polynomial | `maxGenEigenspaceIndex_eq_rootMultiplicity_minpoly`, `maxGenEigenspace_eq_genEigenspace_rootMultiplicity_minpoly`, `rootMultiplicity_minpoly_le_of_stabilizes`, `minpoly_mulVecLin`, `maxGenEigenspace_mulVecLin_eq_rootMultiplicity_minpoly`, `finrank_maxGenEigenspace_le_index_mul` | Yes | **Wider** | **Closed 2026-09-20, and the measurement the previous note asked for was made first and came back negative.** The pinned Mathlib relates a *root* of the minimal polynomial to an eigenvalue (`Module.End.hasEigenvalue_iff_isRoot`) and carries nothing relating the stabilization index to the root multiplicity; `Module.End.maxGenEigenspaceIndex` is `sInf` of the set of exponents at which the chain is stationary and is never compared with `minpoly` anywhere in the tree. **Both halves of print's sentence are now proved, and they are print's own definition split in two.** `maxGenEigenspace_eq_genEigenspace_rootMultiplicity_minpoly` says the chain has already stopped at the minimal-polynomial multiplicity, and `rootMultiplicity_minpoly_le_of_stabilizes` says no smaller exponent stops it — least, and stationary there. **No Jordan form, no algebraic closure, no split minimal polynomial**, which is why this cost nothing like the section's other open item: factor `ψ = (X - λ)^ν · q` with `q` not divisible by `X - λ`, and Bézout between `q` and a power of `X - λ` gives the first half while `minpoly.dvd` and cancellation give the second. **Wider**: print states the index for a complex `n × n` matrix, and these hold for an endomorphism of any finite-dimensional vector space over any field, with `minpoly_mulVecLin` carrying the statement back to print's matrix. `Examples.LinearSystems.Criteria.frozenC_maxGenEigenspaceIndex` and `…frozenC_minpoly_rootMultiplicity` exhibit both numbers at the witness. **What this closes is not only this row**: every statement below was stated at an arbitrary stabilizing exponent supplied by the caller, and print's `νᵢ` is now known to be one, so the four numbered results are available with the exponent *computed from `A`* rather than chosen |
| §Intro, the Jordan form | `J = T⁻¹AT`, `G = T⁻¹B`, `H = CT`, with `k` diagonal blocks `Jᵢ` of size `nᵢ`, each composed of `αᵢ` Jordan blocks `Jᵢⱼ` of size `βᵢⱼ` | — | No | — | the atlas has no Jordan canonical form and Mathlib carries none at the pinned revision. Everything below rests on this |
| §Jordan criterion | complete state controllability (observability) holds iff for each `i` the `αᵢ` row vectors of `G` at the last rows of the blocks (column vectors of `H` at the first columns) are linearly independent over the complex numbers | — | No | — | print quotes this from Chen and Desoer and uses it as its engine. The atlas proves two *different* criteria for the same property — see the `Beyond` rows — and proves no equivalence with this one |
| eq (1) | `βᵢⱼ ≤ νᵢ ≠ 0` for every block | — | No | — | block size bounded by the index |
| eq (2) | `αᵢ ≥ int[nᵢ/νᵢ]` | `rootMultiplicity_le_mul_finrank_eigenspace` | Yes | **Wider** | the counting step, and **print derives it from the Jordan form while this does not have one**. `finrank_ker_pow_le` — the kernel of a `k`-th power is at most `k` times the kernel — is the same count with no blocks in it, and `finrank_ker_comp_le` is the two-map case it comes from. Neither is in Mathlib at the pinned revision. **Wider** because print states it at the index and this holds at *any* exponent at which the generalized eigenspace chain has stabilized |
| eqs (3) and (4) | `αᵢ ≥ nᵢ/νᵢ` when the quotient is an integer, and `αᵢ ≥ int[nᵢ/νᵢ] + 1` when it is a fraction | — | No | — | the two cases print splits |
| eq (5) | `αᵢ ≥ int[(nᵢ + νᵢ - 1)/νᵢ]` | `ceil_div_le_finrank_eigenspace` | Yes | **Wider** | the two cases rejoined — the ceiling of `nᵢ/νᵢ`, and the quantity every numbered result below is stated in. `Wider` for the same reason as eq (2) |
| eq (6) | `rank G = min (rank T⁻¹, rank B) = min (n, r) = r` | — | No | — | rank is preserved by the similarity. The nearest atlas fact is `mulVec_kernel_trivial_iff_rank_eq_card_cols`, which is about one matrix and not about a product with an invertible one |
| Theorem 1 | if for some `i` the quantity of eq (5) exceeds `r`, then `S` is uncontrollable | `not_isControllable_of_ceil_div_gt_rank`, `not_isControllable_of_ceil_div_minpoly_gt_rank` | Yes | **Wider** | **the conclusion is print's and the antecedent is not.** The atlas proves it from the dimension of the eigenspace `ker (μ • 1 - A)` at an arbitrary `μ`, print from `int[(nᵢ + νᵢ - 1)/νᵢ]`. That quantity bounds the eigenspace dimension below — each Jordan block at `λᵢ` has size at most `νᵢ` and the blocks partition `nᵢ` — so the atlas hypothesis is strictly weaker and the theorem is strictly stronger. **As of 2026-09-13 print's own statement is in the tree too**: `not_isControllable_of_ceil_div_gt_rank` takes print's antecedent, through the eq (5) row above, and the eigenspace version remains the stronger theorem it always was. Print's route is still different: the Hautus pencil, not the Jordan rows **And as of 2026-09-20 the exponent is print's own `νᵢ` and not a parameter**: the minimal-polynomial form takes the multiplicity in the minimal polynomial, computed from `A`, through the index row above |
| Corollary 1 | the same with `p`, the input dimension, in place of `r` | `not_isControllable_of_ceil_div_gt_width`, `not_isControllable_of_ceil_div_minpoly_gt_width` | Yes | **Wider** | print's own weakening, since `r ≤ p`; the atlas gets it the same way, from `Matrix.rank_le_card_width`. `Yes` and `Wider` for exactly the reason Theorem 1 is **And as of 2026-09-20 the exponent is print's own `νᵢ` and not a parameter**: the minimal-polynomial form takes the multiplicity in the minimal polynomial, computed from `A`, through the index row above |
| Theorem 2 | if for some `i` the quantity of eq (5) exceeds `m`, then `S` is unobservable | `not_isObservable_of_ceil_div_gt_rank`, `not_isObservable_of_ceil_div_minpoly_gt_rank` | Yes | **Wider** | **print's proof is one sentence — *"It follows by duality"* — and that is now literally the atlas proof**, through `isControllable_iff_isObservable_transpose`. The antecedent is the transposed eigenspace, and `finrank_ker_transpose_eq` shows it is the same dimension. `Yes` for the same reason as Theorem 1 **And as of 2026-09-20 the exponent is print's own `νᵢ` and not a parameter**: the minimal-polynomial form takes the multiplicity in the minimal polynomial, computed from `A`, through the index row above |
| Corollary 2 | the same with `q`, the output dimension, in place of `m` | `not_isObservable_of_ceil_div_gt_height`, `not_isObservable_of_ceil_div_minpoly_gt_height` | Yes | **Wider** | the observability twin of Corollary 1, from `Matrix.rank_le_card_height` **And as of 2026-09-20 the exponent is print's own `νᵢ` and not a parameter**: the minimal-polynomial form takes the multiplicity in the minimal polynomial, computed from `A`, through the index row above |
| Corollary 3 | if the quantity exceeds `max (r, m)`, then `S` is both uncontrollable and unobservable | `not_isControllable_and_not_isObservable_of_finrank_ker_gt_ranks`, `not_isControllable_and_not_isObservable_of_ceil_div_gt_ranks`, `not_isControllable_and_not_isObservable_of_ceil_div_minpoly_gt_ranks` | Yes | **Wider** | the conjunction, stated against one eigenspace rather than two because `finrank_ker_transpose_eq` identifies them. **`Yes` on 2026-09-20, and the cost this row carried was not a cost — it was a misreading of the atlas's own proof.** The note here said the conjunction form *"needs a stabilizing exponent for the matrix and for its transpose at once and nothing in the tree identifies those two"*, and called that costed rather than overlooked. It needs no such thing: `finrank_ker_transpose_eq` had already collapsed the two eigenspace dimensions into one, which is the very sentence the first half of this note has carried since 2026-09-11, so there is only ever **one** count to bound and print's antecedent on `A` alone reaches it. The restatement is four lines. **What that is a lesson about** is where a cost note comes from: this one was written from the *shape of print's statement*, which mentions both matrices, rather than from the atlas's proof, which had already eliminated one of them |
| Corollary 4 | if the quantity exceeds `max (p, q)`, then `S` is both uncontrollable and unobservable | `not_isControllable_and_not_isObservable_of_finrank_ker_gt_dims`, `not_isControllable_and_not_isObservable_of_ceil_div_gt_dims`, `not_isControllable_and_not_isObservable_of_ceil_div_minpoly_gt_dims` | Yes | **Wider** | the conjunction in dimensions alone, `Yes` on 2026-09-20 with Corollary 3 and for its reason. `Examples.LinearSystems.Criteria.frozenC_klamka_minpoly_corollary3` and `…frozenC_klamka_minpoly_corollary4` fire both at the frozen system, with `nᵢ = 2` and `νᵢ = 1` read off `A` |
| §Conclusion | the test needs only `nᵢ` and `νᵢ`, never the value `λᵢ`, and the transformation matrix `T` need not be known | — | No | — | print's stated selling point, and the reason it prefers this test to the Jordan criterion it is derived from |
| — Kalman | — | `isObservable_iff_observabilityMatrix_rank_eq`, `isControllable_iff_controllabilityMatrix_rank_eq` | — | **Beyond** | the rank characterizations of print's two properties. Print states neither, and reaches for the Jordan criterion instead |
| — Hautus | — | `isObservable_iff_hautus`, `isControllable_iff_hautus` | — | **Beyond** | the eigenvalue-pencil tests over the complex numbers. Not in print, and the natural route to print's Theorem 1 |
| — duality | — | `isControllable_iff_isObservable_transpose` | — | **Beyond** | print invokes duality in one sentence to get Theorem 2 from Theorem 1; the atlas proves it |
| — indistinguishability | — | `frozen_indistinguishable` | — | **Beyond** | two distinct states of a concrete system whose entire output sequence agrees. Print asserts unobservability and never exhibits a collision. **This was the closest thing in the tree to the survey's informal reading until 2026-09-20, and is no longer**: there is still no trajectory behind it, but `blind_not_determinesStateOn` is now that reading exactly, at a system whose outputs do not determine its state. This row stays because the collision is a different and sharper fact — the two states are *named*, and the agreement is on the whole family of maps rather than on one window |
| — block rank | — | `rank_fromCols_le`, `rank_fromRows_le` | — | **Beyond** | a block matrix has no more rank than its blocks apart. Atlas-original and domain-neutral, written for the pencil bound; print reasons about Jordan rows and never needs it |
| — rank-nullity at the pencil | — | `finrank_ker_add_rank_eq`, `finrank_ker_transpose_eq` | — | **Beyond** | kernel dimension plus rank is the side length, and the eigenspace has the same dimension for a matrix and its transpose. The second is what turns print's one-sentence duality argument into a proof |
| — the bound is inhabited | — | `frozenC_not_isControllable`, `frozenC_finrank_ker` | — | **Beyond** | a system satisfying the hypothesis of the Corollary 1 row: the identity on two states has a two-dimensional eigenspace and one input column. Print offers no example, and without one the six rows above would be statements about a class nobody has shown to be non-empty |

**10 Yes, 1 Partial, 6 No, 7 Beyond**, and the section has moved four times.
It opened at 0/1/16/4 on 2026-09-11, with every numbered result `No`; the six of
them moved to `Partial` the same day when the Hautus half was proved; four of
those went to `Yes` on 2026-09-13 when eq (5) was proved and print's antecedent
entered the tree; and on 2026-09-20 the index row, the notation row and the two conjunction
corollaries all moved.
What has still not moved is **print's route**. Print's engine is a Jordan-block
count read off the Jordan form, and the atlas has no Jordan form and reaches the
same conclusions through the Hautus pencil and a kernel count. The two arrive at
the same statements by different arguments, which is what the `Wider` grades
record.

**Three paragraphs below were falsified on 2026-09-13 and are replaced here
rather than repaired, and the delay is the finding.** They said, in three
different ways, that eq (5) was the whole distance between this section's
`Partial` and a `Yes`, that eq (5) needed a Jordan normal form, and that the
index was not in the tree. The first two stopped being true on 2026-09-13, when
`AISafetyAtlas.LinearSystems.BlockBound` proved eq (5) with no Jordan form in
it, and the third on 2026-09-20. The rows were regraded on both days and the
surrounding prose was not swept on the first, so this section spent a week
asserting a blocker it had itself removed.
**This is what settles `BY-001` and `BY-002`, in both directions, and the
paragraph that stood here was stale twice over.** It said both rows stay
`CANDIDATE_LEAD` and that not one printed claim is obtained. Neither holds: both
rows were retriaged to `TRIAGED_DISTINCT` on 2026-09-13, and ten of print's
statements are `Yes` in the table above. What remains true is the part worth
keeping — the earlier verdict on `BY-001` said nothing existing covered it, that
was about ten Isabelle keyword hits, and a Lean development of the same property
did exist that the recorded sweep could not see; and the **adapted** development
is still not coverage of print. What covers the two rows' own informal claims is
neither print nor the port but `AISafetyAtlas.LinearSystems.Dynamics` and
`…Flow`, built here on 2026-09-20. **Both rows were promoted from uncovered to
covered on 2026-09-21**, on the maintainer's decision, at `EXACT`; headline
coverage moved 14 claim rows to 16. **2026-10-05:** the definitional-closure audit
found that `IsTrajectoryOn` admits only classical solutions, which left out the
piecewise-continuous inputs print takes from Chen and Desoer, so the necessity
side of reachability and the sufficiency side of observability were narrower
than print. Both equivalences are now proved at the integral (Carathéodory)
solution class, `determinesStateSolOn_iff_isObservable` and
`isCompletelyReachableSol_iff_isControllable` in `AISafetyAtlas.LinearSystems.Flow`,
with a step input witnessed as a solution that is not a classical run. That
print's whole piecewise-continuous class gives solutions of this kind is
standard and is not proved here; the grade rests on that standard inclusion. The rows
stay `EXACT`, graded at those declarations. Their `statability` verdicts were retired
into their notes rather than deleted, because policy rejects a verdict on a row
that carries Lean and the `TRIAGED_DISTINCT` finding remains correct about the
thing it was about — the external candidate, which is still not coverage. The
class restriction is on the rows and not left implicit: what is proved is the
finite-dimensional linear time-invariant system over `ℂ`, which is print's own
object and not dynamical systems at large.

**The route was taken, and it is recorded here because the estimate was
wrong in the usual direction — twice.** When this section was first written it
noted that Theorem 1 *looked* reachable from `isControllable_iff_hautus` and
declined to price it. It took one general lemma — a block matrix has no more
rank than its blocks apart — plus rank-nullity, and all six numbered results
followed, including Corollary 3 and Corollary 4, which print states and does not
prove. The paragraph that replaced it then said eq (5) was what remained and
that it needed the Jordan decomposition. **Eq (5) was proved the next day
without one**, from `finrank_ker_pow_le` — the kernel of a `k`-th power is at
most `k` times the kernel — which is print's counting argument with the blocks
taken out of it. **And the index identity went the same way on 2026-09-20**:
print's `νᵢ` is the multiplicity in the minimal polynomial and Mathlib's is the
stabilization stage of the generalized eigenspace chain, and the two are
identified by a factorization and Bézout, over an arbitrary field, in about
sixty lines. Both estimates priced the object by the machinery print used to
reach it rather than by what the statement needs.

**What is left in this section is not a lemma.** All six numbered results are
`Yes`. The two rows that still carry `Partial` — print's system and its notation
— and the `No` rows below them need a solution to a differential equation, a
Jordan canonical form, or an enumeration of distinct eigenvalues; nothing
remaining here is a missing inequality.

**Corollaries 3 and 4 spent a week `Partial` on a cost that was never there**,
and their rows say so. The note that kept them there was written from the shape
of print's statement rather than from the atlas's proof, which had already
identified the two eigenspace dimensions it thought were the obstacle. That is
the third estimate in this section to have priced the wrong object, after the
two above, and the three failed in the same direction each time.

**Searched 2026-09-12 on the premise that it needs Jordan normal form, and
that premise was wrong.** The search is kept because its result is worth having
and because the prediction it rests on was scored the next day. Mathlib has
generalized eigenspaces and no Jordan canonical form at the pinned revision, and
neither does any Lean development on GitHub — a code search over the whole of
GitHub returns the Isabelle AFP theory of that name and nothing in Lean. The
machinery does exist, in one place that is not a repository: **Prove2Me's
Formalpedia**, where a string basis for a nilpotent map, a Jordan basis for a
complex linear map, and the formula recovering the block sizes from the kernel
dimensions of the powers of `A - μ I` are all proved. Eq (5) itself is not there,
and it was **submitted there as an open problem the same day**; the search, the
submission and their limits are recorded in
[`external-formalizations.md`](external-formalizations.md). Nothing in this file
depends on the outcome: if the statement comes back proved it arrives in a
different environment and would have to be ported. **The clause that stood here
said the six rows stay `Partial` until it is ported. Four of them did not** —
they were proved in-tree on 2026-09-13, from a kernel count rather than from
blocks, and the submission is now a record of a route not taken rather than a
dependency.

**What went the other way.** The two block-rank lemmas this section's proofs
rest on — `rank_fromCols_le` and `rank_fromRows_le`, atlas-original and
domain-neutral — were not in that library either, and were stated and proved
there the same day. Both come back `Proved` against Mathlib `0df444a` at Lean
`v4.33.1`, which is one revision off this repository's pin, so the proofs above
are now known to survive that step. Nothing derived from LeanForControl was
offered, since that work is Anand Gokhale's and the platform's credit is
permanent to the submitter.

---

## 26. Skalse, Howe, Krasheninnikov & Krueger 2022, NeurIPS → `AISafetyAtlas.Goodhart.Hackability`

**Graded for the first time on 2026-09-13.** Statements read from rendered pages
5 to 8 of the published version. This is the **last of the six sources** the
integration blind-spot paragraph at the top of this file names as outside
the ledger; with this section that debt is discharged.

**Which text.** The published NeurIPS 2022 version is canonical, sha256
`634ffa7ccb0225296482ef2961a38ba175bd8c1b97b998556a6bcfa7ad560210`, 12 pp. The
arXiv v2, sha256 `d9a8567f…`, carries the same Definitions 1–4, Lemma 1,
Theorems 1–3 and Corollaries 1–3 *"identical in wording and numbering"* plus an
appendix with the proofs and Propositions 1–4; both are pinned in
the private manifest of 2026-09-10. There is no version fork.

**Regraded 2026-09-20, and the heading moved with it.** Until that date the
verdict here was *"nothing in this atlas covers any printed claim in this
paper"*, and the heading named `AISafetyAtlas.Goodhart.Regressional` only
because the plan document routed the source to that cluster. Both are now
false: `AISafetyAtlas.Goodhart.Hackability` renders §4.2, and
`AISafetyAtlas.Decision.Occupancy` renders the §4.1 setup it needs.

**What the old verdict got right, and it is still the shape of this section.**
The reason nothing covered this paper was structural rather than accidental: the
Goodhart cluster asks what happens when you *optimize* a proxy, and this paper
asks whether two reward functions ever disagree about which of two policies is
better. That is still true of `Regressional`, `Extremal` and `Overoptimization`,
which is why the new work is a new module rather than an addition to one of
them. What changed is that the two objects the paper needs — an occupancy
embedding and value as a linear functional of the reward — were built, and with
them §4.2 is two definitions and five short proofs.

**What is still `No` is the geometry**, and it is the bulk of the paper: Lemma 1
and Theorems 1, 2 and 3. Those need a topology on policy space or a rank
computation in occupancy space, and each row below costs its own.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §4.1 setup | policies embedded by visit counts, `F : Π → ℝ^{\|S\|\|A\|}`; value as the inner product `J_i(π) ≐ ⟨R_i, F^π⟩`; a second embedding `G(π)[s,a] = π(a \| s)` | `Decision.visitCount`, `Decision.stateOcc`, `Decision.actionEmbed`, `Decision.J`, `Decision.J_linear`, `Decision.sum_stateOcc_eq` | Yes | **Wider** | closed 2026-09-20 by `AISafetyAtlas.Decision.Occupancy`. All three of print's objects: `visitCount` is `F^π`, `actionEmbed` is `G`, and `J` is the pairing, with the initial distribution a `PMF State` argument as print's `I`. `J_linear` is the consequence print's whole argument runs on -- value is a **linear functional of the reward** -- and `sum_stateOcc_eq` is why the picture is a picture: every policy's visit counts have total mass `(1 - γ)⁻¹`, so they all land on one scaled simplex. **Wider**: the definitions are stated at arbitrary state and action types and `J` needs only finiteness, where print assumes `S` and `A` finite, `\|A\| > 1` and every state reachable; none of those three is used. Print's `γ ∈ [0, 1]` is carried as `γ < 1` wherever a sum has to converge, which is print's own implicit assumption rather than an added one -- at `γ = 1` a policy that never leaves a state has infinite visit counts. The `AISafetyAtlas.Decision.DiscountedValue` fixed-point layer is untouched and is still not connected to this one; the row below and the module docstring say what that would take |
| §4.1, *"Note that"* | `J(π) = ∑_{s,a} ℛ(s,a) F^π(s,a)` -- that the pairing with the visit counts **is** the expected discounted return, the mean of the discounted sum of rewards along a trajectory | — | No | — | print defines `J` by the trajectory return and then observes it equals the pairing; the atlas defines it by the pairing and does not prove the identity, so print's `F^π` is rendered and print's `J` is not. Closing it needs a return along a trajectory distribution and a Tonelli exchange. **Two things the atlas already has make this smaller than it looks and neither closes it**: `Decision.MDP.run` is a trajectory distribution, at a single start state and a history-dependent policy rather than print's `I` and a stationary one; and `Decision.vPi` is the same number computed as a Bellman fixed point, for **deterministic** policies only. Costed: lift `vPi` to stochastic policies, then `⟨ℛ, F^π⟩ = 𝔼_I[vPi]`; the second half is a finite linear-algebra identity once the first exists |
| **Definition 1** | *"A pair of reward functions `R₁, R₂` are **hackable** relative to policy set `Π` and an environment … if there exist `π, π′ ∈ Π` such that `J₁(π) < J₁(π′) & J₂(π) > J₂(π′)`, else they are **unhackable**"* | `Goodhart.Hackable`, `Goodhart.Unhackable`, `Goodhart.HackableRewards`, `Goodhart.UnhackableRewards`, `Examples…hackable_rewards` | Yes | **Wider** | closed 2026-09-20. The paper's central relation, at print's quantifiers. **Wider** because it is stated on the *induced value* rather than on the reward, which is print's own content -- print says the relation is between two reward functions *mediated by the ordering each induces*, and neither definition mentions a reward except through its `J`. `HackableRewards` is print's statement at print's arguments, with `Decision.J` supplying the two orderings. The widening is not idle: a value function elicited from a person, coming from no reward at all, is a legitimate argument and every theorem below applies to it |
| §4.2 prose | *equivalent* on `Π` — `J₁` and `J₂` induce the same ordering; *trivial* on `Π` — `J(π) = J(π′)` for all `π, π′ ∈ Π`; and that unhackability is symmetric and **not transitive**, since the constant reward is unhackable with respect to everything | `Goodhart.Equivalent`, `Goodhart.Trivial`, `Goodhart.Unhackable.symm`, `Goodhart.unhackable_of_equivalent`, `Goodhart.unhackable_of_trivial_left`, `Goodhart.unhackable_of_trivial_right`, `Goodhart.unhackable_not_transitive`, `Goodhart.trivial_of_const`, `Examples…notTransitive` | Yes | **Same** | closed 2026-09-20. Print's three side conditions and both of its claims about them, each at print's own argument: symmetry *"can be seen by swapping `π` and `π′`"* and is; non-transitivity is the constant reward in the middle, and `trivial_of_const` proves that reward trivial in **every** environment rather than in a chosen one, because the discounted horizon is spent somewhere whatever the policy does. `unhackable_not_transitive` takes the two ends' disagreement as a hypothesis rather than fixing a model, and `Examples…notTransitive` inhabits it |
| **Definition 2** | `R₂` is a **simplification** of `R₁` relative to `Π` if for all `π, π′ ∈ Π`, `J₁(π) < J₁(π′) ⟹ J₂(π) ≤ J₂(π′)` and `J₁(π) = J₁(π′) ⟹ J₂(π) = J₂(π′)`, **and** there exist `π, π′` with `J₂(π) = J₂(π′)` but `J₁(π) ≠ J₁(π′)`; **trivial simplification** when `R₂` is trivial | `Goodhart.Simplifies`, `Goodhart.TrivialSimplification`, `Goodhart.SimplifiesRewards`, `Examples…trivialSimplification_const` | Yes | **Wider** | closed 2026-09-20, all three clauses including print's own non-degeneracy requirement, and wider for the same reason as Definition 1. `Examples…simplifies_const` is the trivial simplification print names |
| footnotes 4 and 5 | if `R₁ ⊴ R₂ ⊵ R₃` then `R₁, R₃` are unhackable; but `R₁ ⊵ R₂ ⊴ R₃` need not be, *"consider the case where `R₂` is trivial"* | `Goodhart.unhackable_of_simplifies_common`, `Goodhart.simplifies_of_trivial`, `Goodhart.not_simplifies_of_trivial_base`, `Examples…unhackable_coarse`, `Examples…not_simplifies_of_trivial_both` | Yes | **Wider** | print's two footnotes are its only proofs about the refinement relation, and footnote 4's is reproduced step for step: a strict preference of `J₃` forces one of `J₂`, which forces a weak one of `J₁`. **One place print is loose, recorded because it changes the statement**: footnote 5 says a trivial `R₂` is a simplification of *any* `R₁`, but Definition 2's non-degeneracy clause asks for a distinction to lose, so `R₁` must be non-trivial; `simplifies_of_trivial` carries that hypothesis and `not_simplifies_of_trivial_base` shows it cannot be dropped. Footnote 4's witness is at three abstract policies rather than in the worked environment, and `Examples…Hackability`'s docstring says why: on one state `J` is affine in the action probability, so no non-trivial simplification of a non-trivial reward exists there at all -- a small instance of what Theorem 3 measures |
| **Lemma 1** | *"In any `MDP\R`, if `Π̇` is an open set of policies, then `F(Π̇)` is open in `ℝ^{\|S\|(\|A\|−1)}`, and `F` is a homeomorphism between `G(Π̇)` and `F(Π̇)`"* | — | No | — | the geometric engine. It needs the occupancy embedding and a topology on policy space, neither of which exists here |
| **Theorem 1** | *"In any `MDP\R`, if `Π̂` contains an open set, then any pair of reward functions that are unhackable and non-trivial on `Π̂` are equivalent on `Π̂`"* | — | No | — | the paper's headline impossibility: **you cannot have an interestingly unhackable proxy on a policy set with volume.** Print stresses it *"makes no assumptions about the transition function"* |
| **Corollary 1** | the same at the set of all stationary policies `Π` | — | No | — | via `Π̃ ⊂ Π`, the policies taking every action with positive probability, which is open |
| **Definition 3** | *"A (stationary) policy `π` is `ε`-suboptimal if `J(π) ≥ J(π⋆) − ε`"* | — | No | — | |
| **Definition 4** | *"A (stationary) policy `π` is `δ`-deterministic if `∀s ∈ S ∃a ∈ A : ℙ(π(s) = a) ≥ δ`"* | — | No | — | |
| **Corollary 2** | Theorem 1 applied to `Π^ε` and to `Π^δ`, since *"both of these sets contain open subsets"* | — | No | — | the row that answers the obvious escape — restricting to good, or to nearly deterministic, policies does not buy unhackability |
| **Theorem 2** | *"For any `MDP\R`, any finite set of policies `Π̂` containing at least two `π, π′` such that `F(π) ≠ F(π′)`, and any reward function `R₁`, there is a non-trivial reward function `R₂` such that `R₁` and `R₂` are unhackable but not equivalent"* | — | No | — | the **positive** result, and the counterweight to Theorem 1: at finite policy sets interesting unhackability always exists. The proof rotates a reward function's contour lines through the occupancy space |
| **Theorem 3** | the decision procedure: partition `Π̂` into `E₁…E_m` by equal value, project each `E_i` to `Z_i` by subtracting one member's occupancy, then *"there is a non-trivial simplification of `R` iff `dim(Z₁ ∪ … ∪ Z_m) ≤ dim(F(Π̂)) − 2`"* | — | No | — | a **characterization**, and the sharpest uncovered claim in this paper: an effectively checkable linear-algebraic criterion for whether a reward function can be non-trivially simplified |
| **Corollary 3** | *"For any finite set of policies `Π̂`, any environment, and any reward function `R`, if `\|Π̂\| ≥ 2` and `J(π) ≠ J(π′)` for all `π, π′ ∈ Π̂` then there is a non-trivial simplification of `R`"* | — | No | — | Theorem 3's readable special case |
| §5.2 worked computation | the two-state two-action `MDP\R` with `γ = 0.5` in which 12 of the 4! orderings of the four deterministic policies are realizable, exactly two policies per realizable ordering can be equated non-trivially, and three never can | — | No | — | print's own finite check, and the one row here a finite `Examples/` module could carry without the geometry — but not without the occupancy layer, since *realizable by some reward function* is the whole content |
| §5.3 infinite policy sets | the two policy sets `Π_a` and `Π_b` over three policies, one admitting an unhackable pair and the other not | — | No | — | print's demonstration that Theorem 1 does not characterize the infinite non-open case |
| appendix (arXiv only) | Propositions 1–4 | — | No | — | not in the camera-ready; recorded so the count is against the published text |

**5 Yes, 0 Partial, 13 No, 0 Beyond.** Regraded 2026-09-20; it read 0 Yes, 1 Partial, 15 No when the section was first written on 2026-09-13.

### Why this needed a new module rather than an addition to an old one

`AISafetyAtlas.Goodhart.Regressional` and `.Extremal` are atlas-original work on
**Manheim & Garrabrant's model** — selection on a proxy drawn jointly with a
goal, graded in section 17 — and `.Overoptimization` is Zhuang &
Hadfield-Menell's attribute-space theorem, graded in section 18. All three ask
what happens when you *optimize* a proxy. Skalse et al. ask something else
entirely: **given two reward functions, do the orderings they induce on a policy
set ever disagree?** That is a question about a pair of functions and a policy
set, with no optimization, no distribution over outcomes, and no selection.

Until 2026-09-20 that was the reason the whole section graded `No`, and the row
that said what would be needed was the setup row: **an occupancy embedding and
value as a linear functional of the reward.** Both were built —
`AISafetyAtlas.Decision.Occupancy` — and with them Definitions 1 and 2 were two
lines each, as the note then predicted. The note's other prediction is not
discharged: Corollary 3 and Theorem 3 are *not* short, because both construct a
reward function in occupancy space, and the rows above cost them.

**What the new layer does not do.** It does not supersede
`AISafetyAtlas.Decision.DiscountedValue`, and no theorem connects them: `vPi` is
a Bellman fixed point for deterministic policies, `J` is a pairing with visit
counts for stochastic ones. Two value computations with no bridge is exactly
what `docs/agent/policy/lean-parsimony.md` asks to be justified rather than left
silent, and the justification is that the bridge needs `vPi` at stochastic
policies first. The `§4.1, "Note that"` row above is the same debt seen from
print's side.

### The existing external artifact, and why it does not close this

`audieleon/goodhart` carries *Skalse.skalse_theorem1*, *skalse_theorem3* and
*skalse_corollary3* in Lean, **with policies as occupancy vectors and value as an
inner product** — precisely the substrate named above. It was adjudicated on
2026-09-10 in `docs/provenance/external-formalizations.md`: statement by
statement, licence Apache-2.0, reproduced by cloning twice, verdict **cite, do
not vendor**, and version skew unresolved (its Lean v4.30.0-rc2 against this
tree's v4.33.0). That adjudication stands and is not disturbed by the 2026-09-20
build, and the reason is worth stating: **their `F` is given data and this one is
derived.** `audieleon/goodhart` takes the occupancy vector as an argument, which
is what lets it state Theorems 1 and 3 without a transition kernel at all;
`AISafetyAtlas.Decision.Occupancy` builds `F^π` from the transition kernel, the
initial distribution and the discount, which is what print does and is what makes
`sum_stateOcc_eq` — every policy on one scaled simplex — a theorem rather than a
hypothesis. The two are answering different halves, and *cite, do not vendor*
still holds.

---

## 27. Wooldridge & van der Hoek 2005, J. Applied Logic 3:396–420 → `AISafetyAtlas.Sovereignty.Deontic`

**Graded for the first time on 2026-09-13.** Held as
`wooldridge-van-der-hoek-published-jal-2005-on-obligations-and-normative-ability.pdf`,
sha256 `21970069…`, 25 pp., manifested  2026-09-13.
Statements read from **rendered page images at journal pages 402, 403, 405, 407,
408, 409 and 410**; §§6–8 and Examples 1–7 are located by text extraction and
graded from their section prose, which is why no numbered statement of theirs is
quoted below.

**Why this source is here.** Ågotnes, van der Hoek & Wooldridge 2007 — section 22
— carries no obligation at all, and its own bibliography points here. That made
this the named published alternative to `OughtImpliesCan`'s decision to carry
obligation as a *parameter*. It then turned out to carry something else: **the
published form of a claim this repository had built the same day from an
unpublished sketch.** See the Proposition 3 row.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §2 | an AATS: states, agents, actions, a precondition function `ρ`, a transition function `τ` over joint actions | `AATS` | Yes | **Wider** | closed 2026-09-20 by `AISafetyAtlas.Sovereignty.AATS`, and with it the four rows below that were costed to this one. Print's `(n + 7)`-tuple, with two differences of encoding and none of content: print says the action sets are **pairwise disjoint** and then writes `Ac_Ag = ⋃ᵢ Acᵢ`, so `Ac : Ag → Type` makes the disjointness structural and `ρ` a dependent function; and print's `τ` is **partial** with its domain fixed by coherence constraint (2), so `step` is `Option`-valued and `consistent` is that constraint. Both of print's coherence constraints are fields. **Wider**: print requires `Q`, `Ag`, each `Acᵢ` and `Φ` finite and nothing below uses it. `GameForm` is untouched and is still the one-step object; no theorem relates the two, which is the first item of what is not here |
| §2.2, p.402 | `comp(σ_C, q) = {λ \| λ[0] = q and ∀u ∈ ℕ: λ[u+1] ∈ out(σ_C, λ[u])}`, and *"for any state `q` and any grand coalition strategy `σ_Ag`, the set `comp(σ_Ag, q)` will be a singleton"* | `AATS.comp`, `AATS.out`, `AATS.out_univ_subsingleton`, `AATS.out_univ_nonempty`, `AATS.comp_univ_subsingleton` | Yes | **Same** | print's `comp` at print's indices. The grand-coalition remark is two theorems rather than one: `out_univ_subsingleton` is a fact about `step` being a function, and `out_univ_nonempty` needs print's coherence constraint (2), because the profile's legality is what puts the joint action in the domain of `τ`. Print states the singleton without separating them |
| §3 norms, p.402 | a normative system is `η : Ac_Ag → 2^Q`, where *"`q ∈ η(α)` means the normative system `η` forbids action `α` from being performed when the system is in state `q`"* | `Norm`, `Norm.ofActPredicate` | Yes | **Same** | print's `η : Ac_Ag → 2^Q`, forbidden-primitive and state-indexed. `Sovereignty.NormSystem`, in the `Deontic` module, is the *third shape* this section previously recorded as unreconciled — `permitted` and `forbidden` on acts alone, with no state — and `Norm.ofActPredicate` is now the embedding that says exactly how it is the state-free special case: a state-free norm forbids an act everywhere or nowhere. Neither is adopted in place of the other, and section 22 records why |
| §3 nature, p.402 | the standing requirement `∀α ∈ Ac_Ag: (Q \ ρ(α)) ⊆ η(α)` — *"they forbid anything that is forbidden by 'nature'"* | `Norm.RespectsNature`, `Norm.bot`, `Norm.respectsNature_bot`, `Norm.bot_le_of_respectsNature`, `Examples…not_respectsNature_eta1`, `Examples…not_bot_le_eta1` | Yes | **Wider** | **the row this section most deliberately did not have, and the reason it now does.** Print *couples* prohibition to possibility as a standing requirement on every normative system; imposing that as a field would make every norm in the tree inherit a physical reading, which is what the old note refused. `RespectsNature` is the same condition as a **predicate**, so print's results are available at it and nothing else in the tree is bound by it — that is the widening. `Norm.bot` is print's `η_⊥`, and `respectsNature_bot` with `bot_le_of_respectsNature` say it is the least norm satisfying the requirement, which is print's own reading of it. **A defect of print, found by rendering Example 2**: print's `η₁` does not satisfy this requirement. print states in words on page 400 that the westbound move is possible in every state but the crashed one, so nature forbids it at `q₈` while print's `η₁` forbids it only at `q₇`; the same holds of the eastbound move. `not_respectsNature_eta1` is that failure and `not_bot_le_eta1` is its consequence in print's own lattice, where page 404 says every normative system is above `η_⊥`. It is a slip and not a mistake of substance: `Examples…eta1'` adds `q₈` to both move actions and changes nothing the example is for, since print says of the crashed state *"which we need not consider!"* |
| §3.0 conformance, p.403 | `conf(σ_i, η) ⟺ ∀q: q ∉ η(σ_i(q))`; *conf* of a profile is *conf* of each member's component; `Σ^η_C ≜ {σ_C ∈ Σ_C \| conf(σ_C, η)}` | `AATS.Conf`, `AATS.ConfProfile` | Yes | **Same** | print's `conf` at an agent and at a profile, and print's `Σ^η_C` as a predicate on profiles rather than as a set — the same content at a different carrier |
| §3.1, p.403 | `η⊥`, the empty normative system, which *"imposes no constraints on the actions that"* agents may take | `Norm.bot`, `Norm.top` | Yes | **Same** | print's two distinguished systems, `η_⊥(α) = Q \ ρ(α)` and `η_⊤(α) = Q`. The `⊓` and `⊔` operations of the same subsection are **not** here, nor is Proposition 1's lattice over them |
| **Proposition 1**, p.405 | `(N, ≼)` is a complete lattice with least upper bound `η⊤`, greatest lower bound `η⊥`, meet `⊓` and join `⊔` | — | No | — | the lattice of normative systems. Nothing in the atlas orders norms at all |
| (1), p.405 | `η ⊓ η′ ≼ η`, `η ⊓ η′ ≼ η′`, `η ≼ η ⊔ η′`, `η′ ≼ η ⊔ η′` — union of two systems is *more* restrictive, intersection *less* | — | No | — | print's *"calculus through which to understand the composition of normative systems"* |
| p.405 | `η` is **non-trivial** iff *for every state there is a joint action none of whose components is forbidden there* | `Norm.IsNontrivial` | Yes | **Same** | print's condition verbatim. It gates one direction of print's Proposition 2 and none of Proposition 3(1), which is why the Proposition 3(1) row below grades `Wider` |
| **Proposition 2**, p.405 | for non-trivial `η, η′`: `η ≼ η′ ⟺ ∀C ⊆ Ag: Σ^{η′}_C ⊆ Σ^η_C`; and print's own remark that `⇐` fails for arbitrary systems, since a system forbidding everything at one state gives `Σ^{η′}_C = ∅` | `AATS.confProfile_of_le`, `AATS.le_of_confProfile_singleton` | Yes | **Wider** | both directions, and **wider on both**. Print states the equivalence for non-trivial `η` and `η′`; the forward direction `confProfile_of_le` needs neither hypothesis, which print half-concedes by calling it *"obvious"*. The converse is stated from a **weaker** hypothesis than print's: print assumes the inclusion at every coalition and this assumes it only at single agents, which are among print's coalitions. **What print's proof of the converse uses and does not cite**: the edited strategy `σ*ᵢ(q′) = α` is a strategy only if `α` is available at `q′`, and that is print's §3 standing requirement applied at `q′ ∉ η′(α)` — so `le_of_confProfile_singleton` takes `RespectsNature` as an explicit hypothesis where print leaves it standing. Print's own remark that the converse fails for arbitrary systems is the `IsNontrivial` hypothesis, carried |
| §4, p.407 | `S, q ⊨ ⟪η : C⟫φ` iff `∃σ_C ∈ Σ^η_C`, such that `∀λ ∈ comp(σ_C, q)`, we have `S, λ ⊨ φ` | `AATS.Sat` | Yes | **Wider** | print's `S, q ⊨ ⟪η : C⟫φ` at print's quantifier order — one conformant profile, every computation. **Wider on the path formula**: `φ` is an arbitrary set of computations where print has a formula, and print's path-satisfaction clauses for `○`, `◇`, `□` and `𝒰` each carve out one such set, so every printed statement about `⟪η : C⟫φ` is an instance. Nothing in the module inspects `φ`, which is what makes the generalisation free and what lets §4 be rendered without building a temporal logic. `Sovereignty.Forces` remains the one-step object and is **not** identified with `Sat` at `η_⊥`; that identification is not built and is costed on the first row |
| §5 permission, p.408 | `P_η φ ≜ ⟪η : Ag⟫φ`: *"`φ` is said to be permissible within the context of normative system `η` iff the grand coalition of agents can cooperate to achieve `φ` within the context of `η`"* | `AATS.Perm`, `AATS.perm_mono`, `AATS.perm_union_of_left`, `Examples…perm_noCrash` | Yes | **Wider** | closed 2026-09-22. Print's definition verbatim: `Sat` at the grand coalition. The note that used to sit here said the atlas had act-level permission and no formula level; the formula level is what this row now is. **Wider** on the same axis `Sat` is: `φ` is an arbitrary set of computations where print has a path formula, so every printed statement about `P_η` is an instance. `perm_union_of_left` is the half of print's page-410 duality that needs nothing; the converse turns on the grand coalition's computation being a singleton and is **not** proved -- `comp_univ_subsingleton` gives uniqueness and nothing here gives existence |
| §5 obligation, p.408 | `O_η φ ≜ ¬P_η ¬φ`: *"`φ` is said to be obligatory within the context of normative system `η` iff `φ` is inevitable if the grand coalition conforms to `η`"* | `AATS.Oblig`, `AATS.oblig_of_le`, `Examples…oblig_top_noCrash` | Yes | **Wider** | closed 2026-09-22, and **the row this source was fetched for**: print *defines* obligation where `OughtImpliesCan` carries it as a parameter, and the two could not be compared while only one existed here. Negation is set complement, because `φ` is a set of computations rather than a formula -- the same widening as `Perm`. `oblig_of_le` is the contrapositive of Proposition 3(2), which print does not state and a governance argument uses: **obligations grow as the system gets more restrictive**. Nothing here identifies `Oblig` with `OughtImpliesCan`'s parameter, and the difference is still live |
| (2), p.409 | for any objective formula `σ`: `⊨ (σ ↔ P_η σ) ∧ (σ ↔ O_η σ)` | — | No | — | deontic status is trivial on non-temporal formulae, which is print's argument that *"the object of obligation and permission are temporal"* |
| (3), p.409 | `⊭ O_η φ → O_η □φ` and `⊭ P_η ◇φ → O_η φ` | — | No | — | |
| p.409 duality | `⊨ P_η(φ ∨ ψ) ↔ (P_η φ ∨ P_η ψ)` and `⊨ O_η(φ ∧ ψ) ↔ (O_η φ ∧ O_η ψ)` — *"`P_η` can be conceived of as a diamond, and `O_η` as a box-like operator"* | — | No | — | |
| p.410 chain | for **non-trivial** `η`: `⊨ (Aφ → O_η φ)`, `⊨ (O_η φ → P_η φ)`, `⊨ (P_η φ → Eφ)`; and the second *"does not hold for arbitrary normative systems"* — at `η⊤`, `O_η φ` holds for every `φ` while `P_η ψ` holds for no `ψ` | `AATS.not_perm_top`, `AATS.oblig_top`, `Examples…perm_differs_at_top` | Partial | **Same** | **the sharpest row for the atlas's own decision**, and only its second half is here. The `η⊤` counterexample is closed both ways: nothing conforms to `η_⊤`, so nothing is permissible and everything is obligatory, and `perm_differs_at_top` pairs that against a norm on the same trains that does permit something -- without which the counterexample would be a claim about an empty world. **The three implications themselves are not proved**, and the reason is named: each needs the grand coalition's computation to EXIST as well as be unique, and `comp_univ_subsingleton` supplies only uniqueness. At print's definition **obligation implies permission** whenever anything is permitted at all, so `oughtImpliesCan_does_not_give_permission` is *not* an instance of this |
| p.410 ability | `⊭ ⟪C⟫φ → ⟪η : C⟫φ` — *"we would not expect physical ability to imply ability within a normative system"* | — | No | — | the witness would be a strategy profile that need not be `η`-conformant |
| p.410 ought | `⊭ O_η φ → ⟪η : C⟫φ` and `⊭ O_η φ → ⟪C⟫φ` — *"the fact that something is obligatory does not imply that any individual coalition can achieve it"* | — | No | — | ought does not imply **guaranteed** ability, at their definition. It is not a refutation of ought-implies-can: `⊨ O_η φ → P_η φ → Eφ` on the same page gives *some way exists*, which is the shape the *possible* field of `InstitutionalSetting` has |
| p.410 endpoints | `⊨ O_{η⊥} ○true` and `⊨ O_{η⊤} ○false` | — | No | — | the two endpoints of the lattice, as obligations |
| **Proposition 3(1)**, p.410 | for non-trivial `η ≼ η′`: `S ⊨ ⟪η′ : C⟫φ → ⟪η : C⟫φ` | `AATS.sat_of_le`, `AATS.sat_of_confProfile_mono`, `AATS.sat_bot_of_respectsNature`, `Examples…sat_noCrash_of_eta2` | Yes | **Wider** | **the published form of the governance sketch's GK3**, found after that was built and recorded in `docs/provenance/capability-maintenance-floor.md`; `Enlarges.forces` is the atlas-side one-step form and stays where it is. **Wider on two axes.** Print states the proposition for *non-trivial* normative systems and its proof of this part uses non-triviality nowhere — that hypothesis belongs to Proposition 2's converse, which this part does not need. And print concludes about a path formula where this concludes about an arbitrary set of computations. `sat_of_confProfile_mono` is the statement with the norms abstracted away, which is print's own proof structure: `φ` is never inspected, so anything supplying more conformant profiles supplies more ability |
| **Proposition 3(2)**, p.410 | `S ⊨ P_{η′}φ → P_η φ` | `AATS.perm_of_le`, `Examples…perm_noCrash_of_eta2` | Yes | **Wider** | closed 2026-09-22. Proposition 3(1) at the grand coalition, which is all print's proof of it is -- so it inherits both of that row's widenings: non-triviality is unused and `φ` is an arbitrary set of computations |
| **Proposition 3(3)**, p.410 | `S ⊨ O_η φ → O_{η′}φ` | `AATS.oblig_of_le`, `Examples…oblig_eta2_of_eta1'` | Yes | **Wider** | closed 2026-09-22, as the contrapositive of (2) that print names: **obligations grow as the system gets more restrictive**. Same two widenings as (2) |
| **Proposition 4**, p.410 | `⟪η ⊔ η′ : C⟫φ → ⟪η : C⟫φ`; `⟪η : C⟫φ → ⟪η ⊓ η′ : C⟫φ`; `P_{η⊔η′}φ → P_η φ`; `P_η φ → P_{η⊓η′}φ` | — | No | — | Proposition 3 combined with (1); the composition calculus applied |
| §6 global | a normative system with objective `Ψ` is **globally effective** / **weakly globally effective** / **globally ineffective** according to whether `Ψ` is obligatory, merely permissible, or neither, at `q₀` in the context of `η` | — | No | — | the social-contract layer, and the paper's title claim. Every clause is stated with `O_η` and `P_η` |
| §6 local | **locally effective for agent `i`** / **partially** / **weakly** / **locally ineffective**, by the same trichotomy applied to agent `i`'s own goal, and the lift to all agents | — | No | — | |
| Examples 1–7 | the two-train tunnel AATS and the normative systems `η₁…η₄`, the social contracts `Ω₁, Ω₂, Ω`, and the effectiveness computations over them | — | No | — | a single running example carried through the paper. Nothing in the atlas is indexed by it |
| — | dropping print's *"does not put any constraint on the agents outside coalition `C`"* breaks the transport: `foe_breaks_forces` keeps the embedding and the unchanged semantics, lets one agent **outside** the coalition gain an option, and loses the guarantee | `foe_breaks_forces` | — | **Beyond** | print cannot state this. Its complement is unconstrained by construction, so the condition is a property of its model rather than a clause of Proposition 3 — which is exactly why the abstracted form needs it as a hypothesis |

**14 Yes, 1 Partial, 12 No, 1 Beyond.** Recounted 2026-09-22 after the `P_η`/`O_η` layer landed; it read 10 Yes, 0 Partial, 17 No immediately before, and 0 Yes, 5 Partial, 22 No when the section was written on 2026-09-13, and every one of the five `Partial` rows of that first grading was costed to a single missing object. `AISafetyAtlas.Sovereignty.AATS` is that object, and building it closed all five, together with the four `No` rows that needed only it to be statable.

### What this grading changes

Two things, and they point in opposite directions.

**It removes a novelty this repository nearly kept.** GK3 was built from an
unpublished sketch, with a prior-art search run against Lean and Isabelle
corpora. The claim is published, in a paper this repository already held,
unread, and had cited two days earlier for something else. The correction is in
`capability-maintenance-floor.md` and in `LAND-SOV-CAPABILITY-001`'s
*scope_delta* record; the Lean is unchanged, because it is wider than print on the
carrier and the counterexample has no counterpart.

**And it makes the deontic decision cheaper than this repository said it was.**
`docs/provenance/deontic-layer.md` said adopting print's definition of obligation
"is adopting their normative ATL". That is false for the fragment above: `P_η`
and `O_η` need a restriction of strategies, coalition forcing, and a negation —
all of which the `Sovereignty` cluster has. What needs ATL is the *temporal*
object print then argues is the interesting one, by (2). The note is corrected.

## 28. Alfonseca, Cebrian, Fernández Anta, Coviello, Abeliuk & Rahwan 2021, JAIR 70:65–76 → `AISafetyAtlas.Verification.Containment`

**Graded for the first time on 2026-09-13**, the same day the module was built.
Held as
`alfonseca-cebrian-fernandez-anta-coviello-abeliuk-rahwan-jair-2021-superintelligence-cannot-be-contained.pdf`,
sha256 `ee8cfd46…`, 12 pp., manifested
 2026-09-13. The running head reads *Journal of
Artificial Intelligence Research 70 (2021) 65-76, Submitted 06/2020; published
01/2021*, so this is **the published text and not a preprint**. Statements read
from a **rendered image of journal page 71**; pages 68, 69, 70, 72 and 73 are
located by text extraction and graded from their section prose. **Page 69 was
added on 2026-09-13, after the section was first written**, and it changes how
the Corollary 3 row reads — see that row and the paragraph under this table.

**Two things shape every grade below.** Print's *HarmHumans* is an
*uninterpreted* operation of the language of `R` — print's own words are *"an
explicit program that harms humans and takes a finite time"* — so a
formalization of Theorem 1 is a theorem about an arbitrary effect predicate in
print as much as in Lean, and the safety reading is the bridge rather than the
theorem. And **the paper's own headline, Corollary 3, has no proof in it**: print
derives it in running prose from Assumption 2 and never defines the containment
problem as a decision problem. That is why the row hosting this section,
`BY-025`, whose informal claim is the containment one, is graded `RELATED` and
not `SAME`.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §3 proposals, p.68 | the containment literature surveyed: complete isolation such as a Faraday cage; Bostrom's argument that *"even allowing minimal communication channels cannot fully guarantee the safety"*; Yudkowsky's social-engineering result against question-answering AI; restriction to binary questions; Babcock et al. on the security/usability tradeoff | — | No | — | **this is the sense of *containment* the rest of the field uses** — keep the system in a box and stop it getting out, after Lampson's 1973 confinement problem. Print surveys it and then does not formalize it. The atlas has no channel, no isolation boundary and no notion of a system acting to escape one |
| §3 the carrier, p.69 | *"A **superintelligent machine** is a programmable machine with a program `R`, that receives input `D` from the external world (the state of the world), and is able to act on the external world as a function of the output of its program `R(D)`. The program in this machine must be able to simulate the behavior of a universal Turing machine"* | — | No | — | print's carrier. The Lean has a program, data and a relation between them, and **nothing that acts on an external world** — which is why the harm relation can be arbitrary without loss |
| §3 containable, p.69 | *"A superintelligent machine is **containable** if there is a control strategy that prevents its acting on the external world when there is a reason to predict that `R(D)` will harm humans, and allows it otherwise"* | — | No | — | **print's own definition of containment, and it is predict-then-gate**: a harm predictor plus a switch on actions. It is a property of a machine — *there is a control strategy* — and not a decision problem, and it is **not** the field's boxing sense in the row above. Formalizing it needs the acting-on-the-world half that the carrier row says is absent |
| §4 decomposition, p.70 | *"The containment problem is composed of two subproblems"* — the **harming problem** *Harm(R, D)* and the **control problem** *Control(R, D)* | — | No | — | the decomposition itself. The atlas carries the first subproblem and nothing that names the pair |
| **Algorithm 1**, p.70 | *Harm(R, D)*: *if `R(D)` is harmful to humans then return TRUE else return FALSE* — a **total** procedure on every program and input | `HarmDecider` | Yes | **Wider** | the structure is print's specification read as a decision procedure: total, computable in both arguments, sound and complete. **Wider** because the relation it decides is an arbitrary one between programs and data, where print fixes the informal reading *harmful to humans* |
| §4 isolation, p.70 | *"a solution to this problem must simulate the execution of `R(D)` … in an isolated situation"*, and *"the execution of `T(I)` cannot harm humans, as a Turing machine is isolated from the external world"* | — | No | — | the modelling assumption that makes the composite's harm attributable to *HarmHumans* alone. Nothing in the atlas distinguishes an isolated execution from any other |
| **Algorithm 2**, p.70 | *Control(R, D)*: *if `Harm(R, D)` then disable execution of `R(D)` else allow execution* | — | No | — | the control problem. The atlas has no object that gates an execution on a decision |
| **Algorithm 3**, p.71 | *HaltHarm(T, I)*: *execute `T(I)`; execute *HarmHumans()** | `HarmReduction` | Yes | **Wider** | print's composite, abstracted to the three things its proof consumes: a distinguished program, a computable packaging of a machine as data, and the biconditional in the next row. **Wider** because it does not require the composite to be built by concatenation — only that it exists and is constructible |
| §4 the observation, p.70 | *"*HarmHumans()* is executed if and only if `T(I)` halts"*, so *"*HaltHarm()* harms humans if and only if *HarmHumans()* is executed"* | `HarmReduction` | Yes | Same | the line the whole proof turns on, carried as this structure's *harms_iff_halts* field, which states it verbatim |
| **Theorem 1**, p.71 | *"The harming problem is undecidable."* | `harming_undecidable`, `harming_undecidable_pair`, `HarmReductionPair`, `HarmReductionPair.toHarmReduction`, `halting_problem_pair`, `Examples…halting_problem_pair_holds`, `Examples…exists_harmReductionPair` | Yes | **Wider** | print's proof, transcribed: hold the program at print's composite and let the data range over encoded machines. **The narrowing closed on 2026-09-20 and the row is `Wider` rather than `Same`, because both forms are now here and they are not the same theorem.** `HarmReductionPair` is print's own quantifier — the composite reproduces halting at every machine *and* every input — and `harming_undecidable_pair` is Theorem 1 from it. `harming_undecidable` keeps the fixed input, and that is the **stronger** theorem, not the weaker one: its hypothesis asks the composite to work at one input only. `HarmReductionPair.toHarmReduction` is the reduction between the two, which is the claim this row used to make in prose — *"the two are equivalent as undecidable source problems"* — and did not have in the tree. **What it cost was one lemma Mathlib does not state**: `halting_problem_pair`, the halting problem at both arguments, which follows from Mathlib's fixed-input form by restricting a pair decider to input `0`. The audit's cost note had priced this as *"either proved undecidable by the same reduction or reduced to the fixed-input one"* and the second branch is four lines. `Verification.Robot` still narrows in the way this row used to |
| **Assumption 2**, p.71 | *"`R` must be able to simulate a universal Turing machine and `D` includes the set of inputs that can be executed by a universal Turing machine. In addition, the language of `R` contains at least one explicit operation *HarmHumans()* that harms humans and takes a finite time"* | `Assumption2`, `Assumption2.harmReductionPair`, `harming_undecidable_of_assumption2`, `HaltsOn`, `HarmReduction`, `Examples…exists_assumption2`, `Examples…harming_undecidable_at_universal` | Yes | **Same** | the proof never simulates anything, so `HarmReduction` asks only that the composite be **constructible**, which is what that field records. **Print's Assumption 2 itself is a statement in the tree as of 2026-09-20**, which is what this row was owed. `Assumption2` carries print's three clauses in print's order: `simulates`, that run on the data packaging `(T, I)` the composite computes what `T` computes on `I`; `covers`, that every machine-input pair is packaged and distinct pairs stay distinct — print's *"`D` includes the set of inputs that can be executed by a universal Turing machine"*; and the packaging being computable. **The simulation clause is an equality of partial functions and that is deliberate**: a machine agreeing only on domains would not be *simulating*, and print's *"takes a finite time"* is exactly why the appended operation neither diverges nor prunes. So `Assumption2` is **stronger than the proof consumes**, which is what an assumption should be — `harming_undecidable_of_assumption2` derives Theorem 1 from it and nothing else, by print's own route, while `harming_undecidable` remains available at the weaker hypothesis. The witness is unchanged in kind and extended in reach: `Examples…exists_assumption2` extracts the composite from Mathlib's *exists_code* applied to an evaluation function that unpairs its input into a machine and an input for it, so Assumption 2's own *"must be able to simulate a universal Turing machine"* is what inhabits Assumption 2 |
| **Corollary 3**, p.71 | *"The containment problem is incomputable."* | — | No | — | **print gives no derivation.** Its argument is the preceding paragraph — *"the impossibility of deciding whether a superintelligent machine `R` will harm humans in the presence of a scenario `D` leads to the conclusion that the containment problem cannot be computed"* — and while page 69 does define *containable* — a machine for which a control strategy exists that gates its acting on the world by a harm prediction — that is a property of a machine and not a decision problem, so **the containment problem whose incomputability is asserted here is never defined at all**. There is nothing to transcribe. Stating the complement of the harm relation and calling it containment would invent the missing step, so nothing is claimed. This is the one row `BY-025`'s informal claim actually names |
| §5 Rice, p.72 | *"any non-trivial property (e.g., 'harm humans' or 'display superintelligence') of a Turing machine is undecidable"* — cited to Rice 1953 | `rice_code_iff` | Yes | Same | the atlas carries the cited theorem in both extensional forms, at `BY-012`, and has since before this section existed. Print states it, cites it, and proves nothing about it |
| §5 application, p.72 | that *deciding whether a machine exhibits intelligence* is therefore undecidable | — | No | — | needs *displays superintelligence* to be a non-trivial extensional property, which print asserts and does not argue. The atlas has the theorem and no such predicate |
| §5 four problems, p.72 | emptiness, all-strings, password-checker and equivalence, each undecidable by Rice | — | No | — | four instances print lists without stating. Reachable from `rice_code_iff`, and none is in the tree |
| §5 verification, p.72 | that formal verification's restriction to *"highly restricted classes of programs and inputs"* cannot serve containment, because superintelligent machines are Turing-complete with the world as input | — | No | — | an argument about the scope of a research field. Nothing to state |
| §6 busy beaver, p.72 | the busy beaver decision problem is undecidable, cited to Radó 1962 | — | No | — | a cited result. The atlas has no busy beaver and no maximum-output machine |
| §6 Radó's reading, p.73 | *"incomputable does not mean that the busy problem cannot be decided for a given `n`, but that the complexity of the algorithm that can decide has to increase unboundedly with `n`"* | — | No | — | a complexity claim about a family of deciders, and the atlas carries no resource-bounded layer. The same blocker `C11` names |
| §6 the analogy, p.73 | *"We believe it is reasonable to assume that inspecting a superintelligent machine … is harder from a computability point of view than inspecting a program and deciding whether it can write the largest number of nonblank symbols"* | — | No | — | print marks this as a belief, not a result. Graded `No` because there is no statement, not because the atlas lacks one |

**6 Yes, 0 Partial, 13 No, 0 Beyond**, over 19 rows.

**Two senses of *containment*, and print switches between them.** The word in
the field means what page 68 surveys: isolation, restricted channels, and a
system that may act to get out — Lampson's confinement problem, Yudkowsky's box
experiment, Yampolskiy's leakproofing. The word in print's own glossary at page
69 means something else: a control strategy that gates action on a harm
prediction. **The escape half is dropped between page 68 and page 69**, and
Theorem 1 is about what remains. So a reader who arrives here with the field's
definition will over-read the result: nothing in this paper, and nothing in
`AISafetyAtlas.Verification.Containment`, says anything about recognizing a
system that is trying to breach an isolation boundary.

**What the `Yes` column is worth here, stated plainly.** Four of the five are the
reduction and its parts, and the fifth is Rice, which the atlas held already and
which print cites rather than proves. The paper's two *named* results are
Theorem 1, carried, and Corollary 3, which is the one the survey row is about and
which print does not prove. So this section is a case where **covering
everything the source proves still does not cover what the source is cited
for** — and the honest place to record that is the row's scope-delta field, which
says so.


## Totals

| source | Yes | Partial | No | Beyond |
|---|---|---|---|---|
| Cover & Thomas §2.8 | 11 | 0 | 0 | 0 |
| Cover & Thomas §2.10 | 9 | 0 | 2 | 1 |
| Ashby ch. 11 | 11 | 0 | 4 | 0 |
| Igel–Toussaint / SVW | 14 | 0 | 1 | 1 |
| Touchette & Lloyd | 12 | 0 | 2 | 0 |
| Richens & Everitt 2024 | 10 | 0 | 13 | 4 |
| Pearl §1.3 | 5 | 0 | 0 | 1 |
| Everitt et al. 2021 | 11 | 0 | 9 | 1 |
| Everitt et al. 2017 (CRMDP) | 8 | 2 | 25 | 2 |
| Everitt, Filan, Daswani & Hutter 2016 | 2 | 2 | 18 | 1 |
| Ring & Orseau 2011 (Delusion) | 10 | 3 | 4 | 5 |
| Everitt & Hutter 2016 (VRL) | 11 | 0 | 16 | 2 |
| Orseau & Ring 2011 (Self-Modification) | 9 | 2 | 9 | 0 |
| Goranko, Jamroga & Turrini 2013 | 11 | 0 | 4 | 1 |
| Pauly 2002 | 6 | 1 | 3 | 0 |
| Turner & Tadepalli 2022 | 16 | 1 | 8 | 1 |
| Manheim & Garrabrant 2018 | 7 | 2 | 7 | 1 |
| Zhuang & Hadfield-Menell 2020 | 6 | 0 | 7 | 2 |
| Breuer 1995 | 12 | 0 | 3 | 1 |
| Armstrong & Mindermann 2018 | 32 | 2 | 10 | 2 |
| Peleg 1998 | 22 | 0 | 5 | 2 |
| List & Valentini 2016 / Carter & Shnayderman 2018 | 11 | 0 | 7 | 2 |
| Chen, Ju & Ågotnes 2026 | 14 | 0 | 2 | 2 |
| Melo, Máximo, Soma & Castro 2024 | 5 | 0 | 5 | 1 |
| Klamka 1972 | 10 | 1 | 6 | 7 |
| Skalse, Howe, Krasheninnikov & Krueger 2022 | 5 | 0 | 13 | 0 |
| Wooldridge & van der Hoek 2005 | 14 | 1 | 12 | 1 |
| Alfonseca, Cebrian, Fernández Anta, Coviello, Abeliuk & Rahwan 2021 | 6 | 0 | 13 | 0 |
| **total** | **300** | **17** | **208** | **41** |

**Orseau & Ring 2011 is new on 2026-09-10** and is the thirteenth source. Its
non-`No` rows were all §2, which it shares verbatim with Ring & Orseau 2011 — so
those rows were closed by declarations written for section 11 and not by work
against this source, and section 13 says so. **One is no longer shared**: its
`A_g` row moved to `Yes` on 2026-09-13 when `DelusionBox.companionGoalAgent`
gave this paper its own goal-seeking agent at the constant horizon its page 4
sets, where the shared record carries the other paper's `2^{t-k}`. Its four `Beyond` rows are
the same four as Ring & Orseau's and are **not** counted twice.

The Ring & Orseau row moved on 2026-09-10, from 2/1/14/3 to 7/5/5/5, and that
was coverage rather than inventory: §3's delusion box, §2's four agents and the
optimal non-learning variants, and Statements 1 to 3 were all `No` and eight of
the nine moved. Read the five `Partial` there with section 11's own note —
three of them are Statements whose printed conclusion is obtained only under
premises print does not state, and grading them `Yes` would be a claim the
atlas cannot support.

The Everitt `No` column moved from 4 to 13 on 2026-09-09 and **no coverage
changed**, then to 11 the same day when Definition 17 and Theorem 18 were formalized: eight printed definitions that the numbered theorems are stated over,
and one of the numbered theorems itself, had no rows, and the table's own rule is that every printed claim gets one. The
`Yes` column was untouched by that pass; it moved from 3 to 5 on 2026-09-10, when
equations (1) and (3) closed at print's own quantifier over the policy, and that
was coverage rather than inventory. Read this the way §8's closing paragraph asks — a
count of `No` rows measures how much of a source has been *inventoried*, and it
rises when a pass reads more carefully, which is the second time this has
happened to this source.

## Reading the totals

**Where the atlas is genuinely stronger:** the `Wider` verdicts rest on six
kinds of widening, and each row's note names which. Note which is *not* among
them — an arbitrary sample space in place of a fixed discrete one is a
presentation, for the reason given above. A hypothesis weakened to only what the
proof uses (Ashby's column condition); a hypothesis *derived*
rather than assumed (Ashby 11/8); a statement the source asserts without proof
(**three as of 2026-08-22**: two inside the proof of 2.8.1, and Everitt's
policy-invariance sentence, which is asserted in running prose between
Definitions 4 and 5 and proved in §8's new row for it); a wider class of objects or
parameters quantified over (signed weights in IT Thm 5, arbitrary sample length
in SVW NFL3, a different estimate *type* in `fano_of_embedding`); a sharper
conclusion at the same hypotheses (Ashby's integer `⌈r/c⌉`, Fano's surviving
`−1` in the no-observation remark); and a statement proved **off** an optimum as
well as at it, where the source only states it at the optimum (Touchette–Lloyd's
Theorems 2, 3 and 4, each proved at every controller and then transferred to the
minimized `L_C`). The causal sections add a seventh: **a scalar field left as a
parameter** where print fixes the reals. `Model` and the margin layer are stated
over any ordered field of characteristic zero, so print's real case is an
instance, witnesses are computed on rational literals, and the transport lemmas
carry them back. That is a strict widening rather than a presentation, and the
rational instance is what witnesses it — `margin_class_not_identifiable` lives
in a field the printed statement cannot name.

**Counting the weak cells, and one warning about how.** As of 2026-09-19 the
scope column holds **27 `Narrower` and 7 `Mixed`**, spread over twelve
sections: §6 (2/0), §8 (4/4), §11 (3/0),
§15 (1/0), §16 (1/1), §20 (1/2), §21 (1/0), §23 (4/0), §25 (2/0),
§26 (1/0), §27 (5/0), §28 (2/0). §9, §10, §12 and §13 leave the list entirely. **Three cells left
the tally on 2026-09-18**, and not one of them by proving something new. Two are
§9's — Definition 7 and the Theorem 11 proof's step 2 — graded against the
deterministic rendering while the distribution-valued layer that answers both had
been in the tree since 2026-09-10; the notes, not the tree, were the defect. The
third is §12's Lemma 27, closed by **refuting** the unconditional reading: the
witness below it shows that dropping the support condition makes the printed
identity false, so the atlas was never narrower than print there. **A fourth left
on 2026-09-19**, §9's Definition 10, and that one did need new Lean: the atlas
now renders the return *both* ways print writes it — Definition 10's `Ġ` summing
from `k = 0`, and the undefined `G` the proof of Theorem 11 sums from `k = 1` —
and proves that the printed one makes the paper's own equation (3) read `t + 1`.
**A fifth left the same day**, §9's Definition 9, and it needed the most: print's
class is a product over three given sets and the atlas fixed the transition
component to a singleton. A fibre argument cannot repair that, because
`worstCaseRegret` is a maximum over the class and a maximum over a larger class
is larger, so every extremum was rederived over the product with the transition
drawn from an arbitrary index type. §9 now carries no `Narrower` cell at all.
**§9's Theorem 11 followed the same day**, which emptied §9 of weak cells and
corrected the row's own axis list on the way: print's statement is five things
at once, not the four the row counted, because Theorem 11 is stated over the
class of Definition 9 and that class quantifies over the transition set as well.
The fifth axis went unnamed until it was closed, and it is not a corollary of
the other four, for the reason the Definition 9 row records -- a maximum over a
larger class is larger.
**One more left it on 2026-09-14**: §8's policy-invariance
row, whose expectation-layer narrowing was closed by giving the exogenous draws
a product measure that needs no finite vertex set, with the finite sums
recovered as instances and the new measurability side condition discharged for
free at print's own setting. **Seventeen cells left the tally on 2026-09-13**, in §10, §11, §12 and §13, and the last six of them are one piece of work: a program-prior layer and an infinite-horizon limit, built against the mortality paper's page 2 and joined to what the two Ring–Orseau sections already had. Those six are §11's equation (3), optimal variants and Statement 4, and §13's equation (1), `A_k` and `A^μ`. §10's is Definition 3, where print's policy space
`Π` and naming map `ι` were the objects the atlas lacked and now names. Five
are §12's, where the atlas took print's finite case
for `𝒮`, `ℛ` and `𝒰` and print's setup page says *finite or countable*; the
sums are now unconditional, and §12's Lemma 27 row, which stayed `Narrower` on
the support condition, left on 2026-09-18 as well — a different axis, and closed
by refuting the unconditional reading rather than by proving it. The other four are in §11 and §13. Equation (2) in each went `Mixed` to `Wider` when the
observation type was freed. Equation (1) in each — §13 numbers it (3) — went
`Narrower` to `Same` when the action type was freed the same way: the maximum
is a supremum over an arbitrary type and equation (1) is stated at the
attainment print presupposes by writing an argmax. The finiteness cluster that
work order **A** names is closed in this module and open in the other four. **§18 carries a seventeenth cell that this
tally deliberately excludes** and the paragraph below says why.

**Two warnings about counting it, both learned by getting it wrong.** A phrase
search over the file returns more than the tables hold, because `Narrower` and
`Mixed` also occur inside reason cells discussing a *different* row's grade. And
a column reader that splits rows on every `|` returns **fewer**, because this
file escapes `\|` inside cells: a description containing `F : Π → ℝ^{\|S\|\|A\|}`
shifts every later column of that row, and the row drops out of the tally
silently. A correct count splits on pipes not preceded by a backslash; the check
that it is correct is that the same pass reproduces the grade column's
the grade column's own totals, which the totals table carries and
`check_coverage_audit.py` verifies against the rows. **That sentence used to
quote the numbers 241/39/222/40 inline**, which stopped being the tally the next
time a row moved; the check reads the table rather than this paragraph, and the
paragraph now says so instead of carrying a second copy that can rot.

**This paragraph replaces one that said five and two, and its conclusion was
wrong as well as its arithmetic.** That paragraph claimed every `Narrower` or
`Mixed` row was a definition except one, so that **no printed claim is
narrower**. That line no longer holds and has not held for some time: §27's
Proposition 3(1) is a printed proposition, graded `Narrower` on the temporal
axis against `Enlarges.forces`, and §25's rows are printed theorems of Klamka's
graded against an algebraic fragment. The line is withdrawn rather than repaired
— at this size the honest statement is a per-cell one, and **the per-cell audit
of all of them is owed**. What is recorded per row is the reason cell; what was
not recorded anywhere, until 2026-09-18, was a mechanical check that each
narrowing is closed, proved unclosable, or costed.

**That check now exists, and it reports the audit as unstarted.**
`scripts/check_scope_owed.py` is advisory, runs in the gate beside
`check_scope_witnesses.py`, and asks the complementary question: that one asks
whether a widening is exhibited by a worked object, this asks whether a
narrowing has been adjudicated at all. It requires each owed cell's note to
carry one of the three states in the standing rule above, spelled exactly:

| marker | meaning |
|---|---|
| `**Narrowing state: regrade.**` | not a narrowing — a units restatement or a representation change, with the converting lemma named. Transitional: the rule says to regrade the cell rather than carry it, so a cell should not sit here |
| `**Narrowing state: unclosable.**` | provably not closable, with the witness that proves it named |
| `**Narrowing state: open, costed.**` | open, with what it would take stated in the note or in a document the note names |

Any other spelling after `**Narrowing state:` fails the check rather than being
counted as absent, so a typo cannot present itself as a worklist item. Its first
run, on 2026-09-18, reported **0 of 43 adjudicated**. That number is the honest
state of this paragraph's claim and is the reason the check was written: the
owed count of 43 was identical whether every cell had been decided or none had,
and none had.

**The sweep ran on 2026-09-19, and the audit is no longer unstarted: 34 of 34.**
Every owed cell now declares a state, and **all 34 are `open, costed`** — no
cell turned out to be a regrade, and none was proved unclosable. The
distribution is itself the finding, and so is a second number the per-cell count
had been hiding: **the 34 cells are 18 distinct pieces of work.** Eight costs are
shared by more than one row — §27's five rows are one missing AATS, §8's
expectation layer is four, §23's four are one move off print's SID corner, §11's
three are one absent prior-and-convergence layer, and §8's domains, §8's
d-separation, §6's agreement theorem and §16's carrier are two apiece — which
accounts for 24 cells; the remaining ten are singletons. Counting cells rather
than costs overstated the work by nearly half.

**Where that stands on 2026-09-20, and the shared costs are why the number moved
in jumps.** The count is **9**, and every one of them still declares a state.
Three of the eight shared costs have been paid since the sweep, and each took
its whole group with it: §27's five rows were one missing AATS and it was built;
§21's three were Peleg's constitution; §8's d-separation was two rows and closed
on both of its axes the same day — the `Finset` carrier through `CID.DSepSet`
and the walk reading through `CID.dSepSet_iff_dSepPath`. §26 was opened and
closed in the same stretch without ever entering this count. What is left is 28
cells over the remaining costs. §21's two example rows were the cheapest and went
the same day: one cost — print's Examples 2.7 and 2.10 as constitutions — closed
both, and Example 3.8 was a computation on the second, which is what the sharing
had predicted. §8's expectation layer was the largest of them
at five rows and was paid the same day: `SCM.exoLaw`, built in September for the
probability-law bridge, had never been read by the expectation layer, and
reading it closed Definition 5 and the policy row outright. It closed **two**
rows and not five, because two of the other three — Definition 17 and Theorem 18
— turned out to carry a different axis under the same name, conditioning rather
than summation, and Definition 1 still had domains, which was paid later the
same day. **That is the sweep's own
warning running the other way**: a cost shared by several rows can also turn out
not to be one cost, and the per-cell count hid that as thoroughly as it hid the
sharing. The larger of §8's two remaining costs, domains at two rows, was paid on
2026-09-20; conditioning at two remains, and its own note says the reading of
Definition 17 it needs cannot be priced from print. **§25's index was
the twenty-fourth and is the counterexample to the sharing story**: a singleton,
priced at a measurement — whether the pinned Mathlib bridges the stabilization
index to the minimal polynomial — which came back negative, after which the
identity itself was sixty lines over an arbitrary field. It was the cheapest
cell in the table and it was a singleton, so the two orderings the sweep
produced — by cost and by how many rows a cost carries — do not agree, and
working the shared costs first is a heuristic rather than a rule.

**§23's four were the fourth shared cost paid, on 2026-09-20, and the price note
was half right.** The cost was recorded as one move — a state set, state-indexed
effectivity, an outcome map that is a relation — and it did take all four rows
at once, which is what the sharing predicted. What it got wrong is the object.
Print's frames *without independence* cannot carry per-agent action sets at all:
availability is indexed by coalition, so there is no edit to `GameForm` that
reaches them, and the move is a second carrier with an embedding placing the old
one at the `SID` corner. In the other direction the estimate was pessimistic,
because print's Definition 8 makes the coalition-level outcome and availability functions consequences of the grand
coalition's outcome function, so the carrier arrives with its own constructor
and five further rows closed with the four — Definition 1, Definition 8, Fact 1
item 2, the eight classes and print's caution about them. **Third estimate in a
row to misprice the object rather than the effort**, after §25's two.

**§20's §5.1 lower bound was the cheapest singleton left and closed the same
day.** Its cost note said the closure means *"quantifying over compatible pairs
through the evaluation map, as print does"*, and that was exactly right about
the target and silent about the two obstacles. Evaluation of a planner is
**partial** — nothing makes a planner halt on a reward — so the vendored
invariance lemma, which takes a total computable map, does not reach it; the
partial form had to be proved. And the pair's program slot has to be read off
the string in a way that hits **every** program index, or print's own degenerate
pair is not expressible and the closed bound would quantify over a class nobody
could inhabit. Neither obstacle is visible from print's sentence, and both are
about the *carrier* rather than the effort — the same shape as §23's.

**§11's three were the fifth shared cost paid, and the cost note priced work
that was never this paper's.** It read *"a convergence-rate claim about that
prior"* and *"`2^{-l}` computed from the goal predicate"*, and called the three
Statements one prior-and-convergence layer. Reading print's own *Arguments*
paragraphs settles all three differently. Statement 3's convergence rate is a
**citation** — print's sentence before the Statement sources the error count to
another paper — so the atlas is not owed it and the axis is retracted rather
than paid. Statement 2's constants are values of the **goal-seeking horizon**
`w(t, k) = 2^{t-k}` and the universal prior enters that paragraph nowhere, so
the cost note's attribution was simply wrong. Only Statement 1's branch bounds
touch the environment at all, and they come out of the delusion box in four
short theorems. **Fifth estimate running to misprice the object**, and the first
to price a debt to the wrong paper. It also briefly cost the section a cell it
looked like it had: closing Statements 1 and 3 at print's one-step reading showed
that Statement 2's bounds are **not** one-step quantities, an axis nobody had
separated from the other three. That axis closed the same day, and closing it is
the only thing in this paper that has ever used print's own *"the goal can be
reached at most once"*.

**Three things the sweep changed rather than recorded.** §8's expectation layer
was named as an axis on four rows and costed on none; it is now costed once, on
the Definition 5 row, and the other three point at it. §15's Theorem 3.3 was the
nearest thing in the table to `unclosable` and was deliberately not marked so:
its note argued the narrowing is print's defect rather than the atlas's, but
`Individualistic` was defined on a game form, so the witness that would settle it
could not yet be asked the question, and the row said that instead of implying
the stronger verdict. **It was asked on 2026-09-20 and the answer was the one
the note called the bad branch**: the witness *is* individualistic, print's
Theorem 3.3 is false as printed, and the row is closed by counterexample rather
than marked `unclosable` — which is what the standing rule asks for when the
wider statement is refuted rather than merely unreachable. The lesson is the
cheapness of the measurement: it was one definition lifted off a structure and
one two-line proof, and it had been sitting behind a sentence saying the tree
could not ask the question. §28's Theorem 1 note asserts that print's two-argument
undecidability and the atlas's fixed-input form are equivalent as source
problems; nothing in the tree proves that, so the row is costed rather than
regraded on the strength of its own sentence.

**What the sweep does not claim.** A cost is not a plan and `open, costed` is not
progress: every one of these cells is as open as it was, and four of the shared
costs — the AATS, the prior layer, the SID generalisation and the expectation
layer's product measure — are new substrate rather than edits to the modules
that carry the rows.

**One cell is outside the scope vocabulary, and it is outside it on purpose.**
§18's Theorem 1 row reads `Narrower, and closed`, the only value in the file that
is not one of `Same`, `Wider`, `Wider (repaired)`, `Narrower`, `Mixed` or `—`.
The reason is in its note: *as printed the theorem is false*, and the atlas
states the repaired form, so the narrowing is **closed by counterexample rather
than owed** — a terminal state the five-value vocabulary cannot express. It is
excluded from the 44/17 because counting it as debt would say work is owed where
none is, and rewriting it as `Narrower` would say the same thing more quietly.
**What is owed instead is the vocabulary**: either a sixth value with a gloss
beside the others, or a separate closed-axis column. Recorded here rather than
resolved, because inventing a grading value the table does not declare is
precisely the laundering this file's own rule forbids.

The old warning survives its paragraph and is worth keeping: anything that sorts
rows by matching `Def.` in the label will file a printed *assertion* under
definitions, because two `Mixed` labels end in *"(asserted after Def. 4)"*.

**Where it is weaker, and why — what actually remains:**

1. *(closed)* **The decision layer's rationals.** `AISafetyAtlas.Causal.Decision`
   now carries its value field as a parameter like the rest of the causal layer,
   so the printed real case is an instance. The review that gated this named an
   obstruction which does not exist, and carries a dated addendum saying so.

2. *(closed)* **Ashby's §11/11 capacity.** Both capacities are now formalized:
   the noiseless alphabet ceiling for the four exercises, and §9/12's weighted
   column entropy with §9/15's per-unit-time rate for the general claim. §9/15's
   asserted proportionality is proved too, and sharpened from linear to affine.
3. *(closed)* **Touchette–Lloyd's Theorem 10.** Both halves of this entry are
   gone. `isPurification_purifyMap` connects every printed transition kernel to
   the independent-noise representation and `openLoopMax_purifyMap` shows the two
   reduction sets coincide; `isGreatest_kernelOpenLoopMax` proves eq. (48)'s
   supremum attained, so it is the printed `max`. `OpenLoopBound` still does not
   nest with eq. (48), and is kept only because its hypothesis is incomparable —
   a fact about that definition, not a gap in a claim.

4. **The unmediated projection is structural, not costed.** Decision and utility
   are not vertices of the graph `Causal.Decision` is stated over, so RE24's
   Assumption 1 is a scope fence rather than a hypothesis. **The missing object
   is no longer the CID layer.** `Causal.CID` and `Causal.SCIM` exist, with
   decision and utility vertices, policies as structural functions, and expected
   utility taken in the induced SCM. What is missing is the *wiring*: nothing
   sends a SCIM's decision vertex to `Model.value`, so §2.2's expected utility
   and regret are still the projection. That is a construction, and it is what
   this point now names. Everitt's own graphical criteria need a second thing on
   top of it — d-separation, Definition 6, which has no counterpart here.
5. **Neither identification theorem is reachable.** RE24's Theorems 1 and 2 need
   a chart of a *CID's* parameters carrying an almost-every quantifier, and a
   policy oracle. Neither object exists, which is why §6's thirteen `No` rows are
   `No` and not `Partial`: they fail on a missing object, not on a missing step.
   Since 2026-08-21 the chart half is a narrower gap than it reads: a real
   parameter chart with a Lebesgue estimate over it exists for MAIS's unmediated
   chance-variable tables (`ChartIndex`, `Model.chartOn`, and MAIS-O24's certificate layer).
   It is not RE24's, because `D` and `U` are not vertices in it — so this row
   turns on the same missing wiring as point 4, not on measure theory. A CID with
   those vertices now exists; a chart over *its* parameters does not.

Two entries that used to sit in this list have been removed rather than
softened, because the tree no longer supports them:

* *"No optimal controller is ever constructed."* False since
  `minControlLoss_inputPolicies_attained`, which exhibits a minimizer — the
  deterministic state feedback playing an argmin action at each state. The
  source still does not construct one, so the atlas is now ahead of print here.
* *"Theorems 5, 6 and 9, Corollary 7 and Lemma 8 are a parallel development."*
  All five are now proved. The observability axis is `sensorLoss` and the
  open-loop axis is `openLoopReduction`; Theorem 9 in particular closes the
  internal weakness this list used to name, since Theorem 10's `Δopen` no longer
  has to be a passed-in parameter.


Two further limits are worth naming even though **neither costs a scope verdict**.

*The Fano module's alphabet hypotheses are pointwise* (`∀ ω, X ω ∈ A`), not
almost-everywhere. That is stronger than the proofs need, so it is a limit
against the usual measure-theoretic idiom — but not against print, where `X` is
typed into a finite alphabet `𝒳` and membership is automatic. Taking `A` to be
`𝒳` recovers the printed statement exactly, so scope is still `≥` print, and an
almost-everywhere version would *exceed* it rather than close a gap. It is not
claimed, and would touch every statement in the module.

*"Arbitrary measurable space"* throughout means an arbitrary **sample space**:
the variables are countable of finite range, so the alphabets are finite here as
in print. No `Wider` verdict in this audit rests on infinite alphabets.

**The `No` column was mostly one thing until 2026-09-09**, and is now two.
Through section 8 it is results adjacent to the target — other problems in the
same paper (IT Thm 3/4), or a parallel development. Touchette–Lloyd's
observability half is no longer: Theorems 5 and 6 and Corollary 7 are proved,
leaving only Theorems 1 and 11, whose rows say why they are not worth having.
None of those `No` rows is a gap in a claim the atlas makes.

Sections 9 to 12 are the other kind. **74 of the `No` rows are theirs** — of 105
at the time that was counted, and of **222** as the table stands on 2026-09-13,
the growth being sections 13 to 27 rather than any regression in 9 to 12 — and
they are not adjacent results: they are whole halves of each paper that the
atlas has no substrate for. Section 9's are the stochastic layer — a measure
over histories, a belief over environments, a learning agent — without which
none of the CRMDP paper's positive results can even be stated. Section 10's are
utility self-modification and the hedonistic and ignorant agents, which is
where two of that paper's three theorems live. Section 11's are the delusion box
and the four concrete agents, which is the whole subject of that paper. Section
12's are the delusion types and the appendix development on them. Read the
count as an inventory of the boundary, which is what this table is for, and not
as a defect list.

**One grade rests on a text the publisher has closed.** Section 11 is graded
against the HAL author deposit `hal-01000226v1`, which has not been compared
with the Springer chapter; a second, different author draft is also pinned and
is deliberately not used. Sections 10 and 12 are graded against
arXiv:1605.03142v1 and arXiv:1605.03143v1, and the publisher-typeset AGI 2016
chapters have since been obtained and read: §12's numbering is identical in both
versions, and §10's concordance is tabulated in that section, with the two
statements of the theorem read side by side. Every other row above was graded
against the published text named in its section header, and where a preprint was
used alongside it the two are compared explicitly in this directory's per-source
notes.
