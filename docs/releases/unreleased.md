# Unreleased — since `v0.8.0`

Draft of the next release note. Until a tag is cut this file is where the
history of the work on `main` lives; [`STATE.md`](../../STATE.md) keeps only the
present.

Everything below was moved verbatim from `STATE.md` on 2026-10-01, so dated
sentences keep the dates they were written on, and "this branch" means the
branch the work was done on before it was squashed onto `main`. Some paragraphs
describe work that predates `v0.8.0` and were never removed from `STATE.md`;
they are kept rather than silently dropped.

## Notes on the work since the last release


**The most recent change is the 2026-09-10 integration merge: three worktrees, four
new clusters, and a ledger debt recorded rather than discharged.** Sovereignty
(eight modules, Pauly 2002 and Goranko-Jamroga-Turrini 2013), Goodhart (three,
Manheim-Garrabrant and Zhuang-Hadfield-Menell), Decision (three, the rewardless
MDP carrier and the discounted value layer) and the wireheading precision work
came in together on 2026-09-10. Fourteen of those modules hold **zero rows in
`registry.yaml`** and six of their printed sources have no section in
[`source-coverage-audit.md`](../../docs/provenance/source-coverage-audit.md); the audit
records that under "Outside this ledger" instead of omitting it, and the gate
returns rc=0 *because* the rows are absent. Three adversarial reviews of the
merge were run, and the corrections they forced —
retracted ecosystem-absence claims, a stale NOT HERE on the causal structural
row, a fictitious finite-percept debt, and Goranko-Jamroga-Turrini's Proposition
6 restored to print — landed the same day. **The grading pass that paragraph said was owed is
done as of 2026-09-13**: the audit went from 8 graded sources to 27, and from
113 graded rows to 542. Every source that block named as ungraded now has a
section -- Pauly 15, Goranko-Jamroga-Turrini 14, Turner-Tadepalli 16,
Manheim-Garrabrant 17, Zhuang-Hadfield-Menell 18, Skalse 26.

**The work since `a65e32f` comes to `main` as one squashed change, prepared
on 2026-10-01**, the 2026-09-10 integration included. Measured on that tree: Lean
637 files and 181,824 lines, the public API pin 2,779 names (1,836 before),
registry results 144. Counts are dated because a count written into this file
moves it.

**What the branch is for is closing scope cells, and the metric is the owed
count.** `docs/provenance/source-coverage-audit.md` grades every transcribed
statement against print on two axes, and a row graded `Narrower` or `Mixed` is a
debt until it is closed, proved unclosable, or costed in writing. The audit now
holds **28 sources and 566 graded rows — 300 `Yes`, 17 `Partial`, 208 `No`, 41
`Beyond`** — with **155 `Wider`, 156 `Same`, 1 `Narrower`, 3 `Mixed`**, and
**four cells owed**, every one of them carrying a written cost. The four are
Everitt's Definition 17 and Theorem 18, which turn on how to read a conditional
expectation on a null context and wait on a maintainer's reading rather than on
work; and Turner and Tadepalli's A.12 and A.13, where the audit's own note
argues against paying the cost. Armstrong and Mindermann's Proposition 10, owed
when this paragraph was first written, is now graded `Wider`.

**Three sections closed on this branch in the week to 2026-09-21**, each by
building rather than by regrading. Section 6, Richens and Everitt's agreement
theorem, where the two carriers differed by a hypothesis and the conditional
expectation removed the need for it, so the atlas statement is *wider* than
print's. Section 21, Peleg's Theorem 3.5, where the construction was already in
the tree as `paulyGame` and what was missing was the pair of effectivity-function
conditions pinning the lattice ends where Pauly's converse fails. And section 25,
Klamka, where `determinesStateOn_iff_isObservable` and
`isCompletelyReachable_iff_isControllable` put print's two dynamical properties
in the tree as properties and proved each algebraic criterion equivalent to the
one named for it — the Gramian-free route, with `NC-013` recording that the
six-corpus sweep found the continuous-time reachability equivalence in no proof
assistant. **The finding in section 25 is not the theorem but the costing**: the
cell was priced four times and every price was for machinery the tree already
held or Mathlib already had. All four retractions are in the row.

**Six of the seven unjoined agent notions now sit on one carrier.** Two
private elicitation notes name seven incompatible notions of
agent behaviour in this tree with no transports between any of them, and call
that a present-tense defect — *interoperable, not silos*. On 2026-09-22 a branch
review measured it and found the defect untouched by 365 commits: the six
`Knowability.lean` joins all predate the branch, and the load-bearing fraction
of declarations had fallen 15.5% → 14.2% while the store grew.

`Wireheading.CRMDP` already sat on `Decision.MDP`. Five more joined it, each with
a theorem crossing the join rather than a ledger row recording one:
`Wireheading.AgentHistory` (the interaction history *is* the carrier's, one datum
in front), `Wireheading.GoalPreservationCarrier` (goal preservation at a model
whose policies differ, replacing a `Unit` model where every field was free by
collapse), `Preference.Trajectory` (unidentifiability stated about an observed
run rather than a policy function), `Verification.RobotRun` (a verifier's
acceptability predicate carried onto every step of a run), and
`Compositional.TraceSystem` (a policy set's runs read as a `TraceSystem`, so a
k-safety violation is reported as at most `k` partial trajectories).
`Compositional.Symmetry` is the one still outside, and
`Wireheading.GoalPreservation` is joined at its *histories* and not at its runs,
because `Model.run` steps by its own `next` field rather than by `detRun`. Along
the way `detHistoryUpTo_length` moved into `Decision.MDP` so two consumers share
one proof instead of two.

**The silent-vacuity debt is down by nearly nine tenths, and what is left is a
different kind of work.** A theorem no `Examples/` application reaches is
unfalsifiable by the build: an unsatisfiable antecedent looks exactly like a
witnessed one. On 2026-09-21 that number was **299 unapplied theorems on 185
leaves**, and it had no work queue at all — `check_witness_debt.py` computed the
set and returned only its length. It now prints the leaves, grouped by owning
module, with the `Examples/` file that would hold each witness.

**299 → 36 unapplied, 185 → 23 leaves**, across 34 commits, with the gate
ceiling ratcheted down at every step and never up.

**Two findings ran through it.** First, a cluster of leaves is usually *one
absent object* rather than many tasks: four control-loss theorems were blocked
on nothing carrying `IsPlant` across to `Purified`, four Wolpert device theorems
on nothing inhabiting `LargeSetupFibres`, six network theorems on the only
automorphism in the tree having a fixed point. Each was one construction, and
nothing in the gate distinguishes that case from fifteen separate ones. Second,
**a leaf count is an upper bound**: four leaves already had witnesses the text
scanner could not attribute, because a dot-notation use whose bare name is
shared by another cluster leaves no matching text. Both are recorded in
`scripts/check_witness_debt.py`'s own docstrings.

**A third finding came out of the 2026-09-22 pass, and it is about the tooling
rather than the tree.** The pin `check_witness_debt.py` resolves against is a
*textual* scan that records a theorem's leaf name and throws the enclosing
namespace away. That is lossless only while no two theorems in one module share
a leaf, and `Wireheading.RewardGrid` has two — so every run printed an
unresolved-pin warning nobody could act on, because the pin held no way to tell
the two apart. `scripts/check_public_api.py` now qualifies a leaf when and
only when it is bare and ambiguous; the diff is one line and the pinned count
went 2646 → 2647. **A check that silently declines to check something was in the
queue's own tooling.**

**What remained was 23 leaves that each need a model, not an application** (20
on 2026-10-01), and
they are named in the queue rather than here. The shapes: a game form carrying a
Keiding cycle, a third epistemic device that knows two implications, a
`FormalSystem` witness for Chaitin's bound, an `isOptimalConditional` universal
machine — which nothing in the tree or in the vendored Kolmogorov layer
inhabits, so two leaves wait on one absent object — and two Mathlib instance
diamonds in the no-free-lunch cluster. `CRMDP.Model.everitt_theorem_eleven` is
on the list for a reason worth stating: the only CRMDP model in the tree is over
`Unit`, where its regret bound reads `0/2 ≤ 0`, and witnessing it there would be
the degenerate application this queue exists to catch. Two further ungrounded
leaves are *not* work and are counted separately:
`Causal.O24Solution`'s antecedent is provably uninhabited, with the proof named
in `docs/status/witness-vacuity.json`.

**What the work held beyond that merge, measured on 2026-09-16.** Against the v0.8.0
baseline: Lean 387 -> 535 files and 112,615 -> 147,539 lines; public API pin
1,774 -> 2,207 names (the pin stopped covering `Examples/` on 2026-09-16, which
removed 1,049 worked witnesses from a list whose entries are compatibility
promises); the axiom audit 4,511 -> 6,247 declarations inside
`{propext, Classical.choice, Quot.sound}`; registry results 91 -> 136;
`pytest` 370 -> 386. No `sorry`, no custom axiom, no `native_decide`, no
`plausible`, on either side. Counts are dated because a count
written into this file moves it.

**Since that measurement: the Econlib port, which closes the one external-reuse gap
the branch had costed and left open.** `AISafetyAtlas.Analysis.Blackwell` is
`Econlib/Math/Analysis/Blackwell.lean` at `003655cc`, Apache-2.0, adapted; its
consumer `AISafetyAtlas.Decision.BoundedValue` values a stationary deterministic
policy on an arbitrary `Nonempty` state type in exchange for a uniform bound on
the reward, and `vPiBdd_eq_vPi` proves the wide and narrow value functions are
one function wherever both are defined. Registry row `LAND-BELLMAN-BDD-001`;
provenance `docs/provenance/econlib-blackwell-port.md`. The pin moves 2,207 ->
2,232 and the axiom audit 6,247 -> 6,285, still inside the three standard axioms.
**The port added no witness debt** — 8 ungrounded, 3 leaves and 314 unapplied
before and after — because the witnesses landed with it, on an infinite state
space the narrower development cannot state.

Two things the port corrected about the costing that authorised it, both
recorded rather than quietly fixed. The toolchain delta was measured by checking
Mathlib names and reported as **one** absent name used twice; compiling found
**four** breakages, one of them inside the repair that check proposed. And the
prediction that porting would "touch the `Fintype` binders of twelve
declarations" was wrong in kind: `ContractingWith γ (bellmanPolicyOp …)` is a
statement about `State → ℝ` as a metric space and does not typecheck without
finiteness, so the wider result is a different statement, not the same one with a
binder removed. What did lose the binder is three *definitions* that never used
it.

**Headline claim coverage did not move: 14 claim rows at `EXACT`/`EQUIVALENT` on
both sides, 6 if the Lean must be `IN_TREE`.** That is the first number a reader
should have, because it is the one the rest of this section would otherwise let
them assume. The branch grew the tree by a third — 45 new registry rows, every
one of them an **artifact** row — and moved the survey-coverage figure by zero.
Claim rows are 49 on both sides; claim rows carrying atlas Lean go 21 -> 22, and
that single gain is a row reaching `RELATED`, which `ledger-coverage.md` says
does not increase the count. Twenty-six of the forty-nine claim rows carry no
Lean of any kind. The claim-side movement is triage: `UNTRIAGED` 22 -> 13,
`TRIAGED_DISTINCT` 4 -> 13, `CANDIDATE_LEAD` 1 -> 0.

That shape is defensible — the artifact rows are results in their own right, and
the survey's remaining claims are mostly blocked on primitives rather than on
effort — but it is a maintainer's argument to make explicitly, not something to
leave a reader to infer from a larger tree.

**Witness debt, measured on 2026-09-16: 8 ungrounded of 2,139 pinned theorems, 3
of them leaves; and 314 reach no `Examples/` application at all.** On 2026-10-01
the same check reads 3 of 2,686, 2 of them leaves, and 31. Two numbers, because *grounded* is
weaker than *applied*. A theorem counts as grounded if it is cited in
`registry.yaml` or applied under `Examples/`; a citation is a human saying the
theorem matters, it is not built, and it cannot distinguish a satisfiable
antecedent from an unsatisfiable one. **314 is the vacuity figure** — quote that
one when the question is how much of the library the build exercises.
`scripts/check_witness_debt.py` is the detector, is new on this branch (`main`
has no such check), and is pinned in `agent_gate.sh` at both numbers so neither
can drift up unremarked.

The three remaining leaves, and **the work queue is now one of them**.
`Causal.O24Solution.{marginClass_subset,behaviorEq_imp_eq}` have a provably
uninhabited antecedent, so no witness can be written at all; and
`Control.entropy_outcome_ge_sub_chainEntropy` wants a stationary Markov chain.
That last is a **cost**, not an impossibility: an i.i.d. sequence satisfies its
conditional-independence and stationarity hypotheses and Mathlib carries infinite
product measures, so the honest label is deferred-with-an-estimate rather than
permanent.

**How the tool records a leaf whose antecedent is provably empty is settled, and
the answer is a distinct disposition rather than a distinct count.**
`docs/status/witness-vacuity.json` names the empty type and the declaration that
proves it empty — here `Examples.Causal.O24Refutation.isEmpty_o24Solution` — and
`check_witness_debt.py` **verifies both against the declaration index and fails**
if either is absent, or if the theorem stops being an unwitnessed leaf. The two
rows stay inside the 8 and the 314, because nothing in the build exercises them
and that is true; what they leave is the work queue, with the reason attached.
Counting them as ordinary debt claimed work was owed that nobody can do;
dropping them silently would have made an unsatisfiable antecedent
indistinguishable from an unwitnessed one, which is the failure the whole report
exists to prevent. Inhabit `O24Solution` and the emptiness proof goes with it,
and the check fires — which is what makes this a claim rather than an exemption.

**The scope-debt count grew with the grading, and is now computed rather than
counted by hand.** `check_coverage_audit.py` reports it: 135 `Same`, 107
`Wider`, 32 `Narrower`, 11 `Mixed`, 40 `Beyond`, 235 ungraded, 1 recorded closed
— so **43 cells are owed** a closure, a regrade, an unclosability proof or a
cost, against 4 the audit records as closed. This file previously asserted 42
and 17, totalling 59, and that figure was not derivable from the audit: nothing
computed it, and four hand counts produced four different answers. Separately,
`check_scope_witnesses.py` reports 23 of 147 `Wider`/`Beyond` rows naming a
worked witness, and it is advisory. Its complement
`check_scope_owed.py` landed 2026-09-18 and is advisory too: it asks whether
each owed `Narrower`/`Mixed` cell declares which of the standing rule's three
states it is in — regrade, unclosable, or open and costed — and its first run
reports **0 of 43**. The audit had recorded that check as owed and missing since
the paragraph withdrawing its "no printed claim is narrower" line; the count of
43 was the same whether every cell had been adjudicated or none had.

**The 235 ungraded scope cells are not scope debt, checked 2026-09-18.** All 164
cells that were ungraded before that date were read one by one. 157 are `No`
rows with an empty Atlas cell, where there is no atlas statement to compare and
`—` is the only honest value; six are `No` rows whose notes say what their named
declarations cover instead; one was a real gap and is now graded `Wider`. The
audit had never written down when `—` is the right cell, and 72 further `No`
rows — every one in the five wireheading sections and none anywhere else, none
naming any declaration — carried `Same` instead, asserting a comparison against
a statement that does not exist. The rule is now stated in the audit's counting
section and **the 72 were rewritten to `—` in one pass**: `Same` 207 → 135,
ungraded 163 → 235. No coverage grade moved and the owed count is unchanged at
43, which is why every arithmetic check passed before and after. The scope debt
this repository owes is those 43 `Narrower` and `Mixed` cells, not the ungraded
count.

**Before that, a runnable form of Ashby's counting law, and a set
of ledger surfaces that say what the tree does not have.** `atlas-check` gains a
fifth kind, `regulation`, backed by `Control.RegulationCheck.columnsInjective`
and the agreement theorem `ashby_bound_of_columnsInjective`. It is the first kind
added for the *hypothesis* rather than the conclusion: the counting law is
settled, and what no part of the build tests is whether any table satisfies the
column condition it quantifies over. A `true` verdict is that missing
satisfiability witness, produced by a running program against the four worked
tables in `Examples.Control.RegulationCheck` — which include one where the
hypothesis fails and the bound is *false*, so a `false` verdict can never be read
as a clearance. Five more assertions in `scripts/check_atlas_check.sh`, which now
runs 21.

Beside it, three things the ledger could not previously say. Every row with no
atlas Lean now carries a `statability` verdict saying why — 6 reproduced
elsewhere, 4 triaged distinct, 3 candidate leads, 22 untriaged — and the
validator fails without one, so [`uncovered rows`](../../docs/status/uncovered-rows.md)
cannot develop holes as the ledger grows. Rows may carry `escape_routes`: what
you weaken to get out from under an obstruction, graded `FORMALIZED` / `STATED` /
`NAMED_ONLY` because the build checks none of them. And
[`blueprint.md`](../../docs/status/blueprint.md) with
[`blueprint.json`](../../docs/agent/blueprint.json) indexes claims against the Lean
that realizes them in **both** directions — 131 declarations now resolve back to
the claim they were written for, which no view here could previously answer.

[`intake.yaml`](../../intake.yaml) is the front door below the conjecture board: a
compiling `Prop` and a minimal row, with every grading field refused by name
rather than left optional. It ships empty and reports itself that way.

**A fairness layer is the most recent domain addition, and it is in no
release.** Two modules under `AISafetyAtlas.Fairness`, carrying
Kleinberg–Mullainathan–Raghavan's Theorem 1.1 (arXiv:1609.05807v2) against
`BY-010`: calibration within groups, balance for the negative class and balance
for the positive class cannot hold together unless the instance allows perfect
prediction or the two groups have equal base rates. It is one theorem, not a
domain — there is no aggregating facade and nothing else imports it.

The row is graded `RELATED` for a reason worth stating here, because it is the
kind of thing a reader should not have to dig for. §1.1 never says whether a
feature vector may have frequency zero in **both** groups, and the answer decides
the theorem's own quantifier. If it may, print's *"`p_σ` equal to 0 or 1 for all
`σ`"* is false, and
`Examples.Fairness.RiskAssignment.not_print_perfectPrediction` is the instance
that refutes it — an unpopulated vector is weighted by zero in every sum the
three conditions mention, so nothing constrains its `p σ`. If it may not, print's
sentence holds verbatim and `print_perfectPrediction_of_populated` derives it.
Both directions are in the tree, which is what makes the narrowing forced rather
than chosen. This is not a claim that the paper is wrong: the degenerate instance
is one no analyst would write. It is a claim that excluding it has to be
*written*, because the data §1.1 specifies does not imply it. The reasoning is in
[`kleinberg-fairness-tradeoffs.md`](../../docs/provenance/kleinberg-fairness-tradeoffs.md).

**Theorem 1.2, the approximate characterization, is an unreleased extension.**
§3 relaxes each of (A), (B) and (C) by a multiplicative `ε` and concludes an
`f(ε)`-approximate form of one of the two cases;
`AISafetyAtlas.Fairness.ApproximateRiskAssignment` carries that at print's own
`f(ε) = √ε · max(1, 3√ε + 3/4)`, and re-derives Theorem 1.1 at `ε = 0` for its
adopted predicates. Several page-level repairs are recorded there. Print's
display of (A′) carries `(1 - ε)` on both sides, forcing
`P = (1 - ε)S`, which is exact calibration only when `ε = 0`; the Lean uses
`(1 - ε)P ≤ S ≤ (1 + ε)P`, a defensible reconstruction of the proof's (7),
with the two sides transposed, not a literal or equivalent display. The p. 12
displays of (B′) and (C′) use `n_t` throughout the numerators for both groups;
the Lean uses each group's own score term and swaps whole group expressions.
Finally, §3 divides by `1 - 2ε + ε² - γ₁` without excluding the case where that
is not positive — harmless, since the conclusion already holds there, but it is
a case the Lean has to take and print does not. The approximate records are
`RELATED` for these textual repairs, not for a modelling choice.

The competing, sign-only repair of (A′) is also proved, with a rescaled error
bound: `approx_tradeoff_of_score_relative_calibration` and
`exists_slack_function_score_relative` use
`g(ε) = f(ε / max(1 - ε, 1/2))`. The two calibration orientations are
incomparable at the same `ε`; the main formalization keeps its orientation
because it gives (7) directly and preserves print's explicit `f(ε)`. The
provenance note records both numerical counterexamples, the adjacent (B′)/(C′)
sign convention, and why their repeated numerator cannot compare group averages.

**Under that sits a causal-inference layer, also in no release.** Fourteen library modules and fifteen worked-example modules under
`AISafetyAtlas.Causal`, graded against three printed sources. Two different
objects live there and neither is a special case of the other: `Causal.Model` is
a causal Bayesian network — a graph with conditional probability tables — while
`Causal.StructuralModel` is Everitt's structural causal model, influence diagram
and SCIM, which consign randomness to exogenous variables and relate the
endogenous ones deterministically. On top of the network sit the objects MAIS-A2
phrases its problems over: semialgebraic classes, the `K(G)` parameter chart, a
prefix-free sparse monomial code, the O24 genericity certificate, and a
rational-weight query layer. The newest four modules are the goal layer
MAIS-O33 is stated over — `Causal.Goal` for print's three temporal operators and
`Psi_n`, `Causal.ControlledProcess`, `Causal.GoalDynamics` for trajectory laws by
Ionescu-Tulcea and print's `(delta,n)`-bounded agents, and `Causal.Corruption`
for first-action data and the adaptive randomized query protocol. There is no
aggregating `Causal` facade and that is
deliberate — these are peer modules, so a consumer imports the one it needs.

**On top of that layer sits the MAIS conjecture ledger, also in no release.**
Sixteen MAIS-linked ledger rows span thirteen printed problem numbers -- nine of
agenda A2, plus A3's `prob:samples`, A6's `prob:calibration`, and agenda A7's
opposing-staircases conjecture and fiber-stratification problem, whose rows share
none of the causal vocabulary. Ten are conjectures or graded candidate answers in
`AISafetyAtlas.Conjectures.MAIS`; six are determine-problem specifications over
a candidate answer. **Every row carries Lean.** The atlas covers fifteen printed
problems of agenda A2 in all, but the six it cannot state at all -- MAIS-O2, O28, O29(c),
O30, O32 and O35 -- are recorded in the coverage matrix
`docs/provenance/mais-a2-statement-coverage.md` and in the
`mais-open-problems-2026` source entry, where MAIS-O1 and MAIS-O16 have always
been, rather than as ledger rows. They held one until 2026-08-30; a row with no
`lean`, no `Prop` and no `refutation` states a fact about this repository's
coverage, and putting one on the conjecture board per unstatable problem is how
a selective ledger becomes a coverage index for a single agenda. Seven of the ten
take agenda
clauses as their graded source and three grade candidate statements
submitted to MAIS issues [#4](https://github.com/lionellevine/MAIS/issues/4), [#8](https://github.com/lionellevine/MAIS/issues/8) and [#5](https://github.com/lionellevine/MAIS/issues/5). Eight are resolved and two remain open. An open
conjecture asserts nothing: it is a compiling statement with no proof, and the
ledger records for each one what would refute it. The settled rows are the
exception, and each names the theorem that settled it. Rows graded against a
printed source are stated at that source's own quantifier. A conjecture stated
narrower than its source is a different question wearing the source's name. If
a literal source statement is false, vacuous, ambiguous, or ill-posed, the
ledger records that source problem rather than adding an atlas premise to rescue
it; atlas-original variants and withdrawn encodings stay outside this ledger,
recorded verbatim with their reason in
`docs/provenance/retired-conjecture-rows.md` so that leaving is not an
undocumented decision and the retired `CONJ-` numbers are never reused. Nine
of the sixteen rows are resolved and each says which printed clause it covers
-- a resolved row that answers one clause of three is not a resolved printed
problem. **Eight of those nine say something about their printed problem.** The
ninth is CONJ-003 (MAIS-O26), which is true because it has no instances:
`conj:exact` is stated over the class that `prob:effective`'s *"fix one list
supplied by a solution"* names, `Examples.Causal.O24Refutation.isEmpty_o24Solution`
proves no such solution exists, and a universal over an empty domain holds
without touching the `Theta(K log(1/epsilon))` rate the conjecture is about. It
is counted as a resolved row because its `Prop` is proved, and it is not counted
as a result.

**A singular-learning layer is the newest thing in this tree, and it is in no
release.** Fifty-three library modules under `AISafetyAtlas/SingularLearning/`,
about 23,000 lines, each mirrored by a worked-example module, plus twenty
modules under `AISafetyAtlas/Conjectures/MAIS/`. It exists for three printed
problems the causal vocabulary cannot reach: agenda A6's `prob:calibration`
(MAIS-O70, the local learning coefficients of reduced-rank regression) and
agenda A7's Conjecture 3.10 and Problem 3.9 (MAIS-O7 and MAIS-O77). The
invariant throughout is print's two-sided local pair. **A7 `def:llc` defines it
by the zeta integral** -- `Z(z) = int_{B_d(w*)} |L(w) - L(w*)|^z dw` continued
meromorphically, `-lambda` its largest pole, `m` that pole's order -- and glosses
the band volume `vol{|L(w') - L(w)| < eps} ~ eps^lambda (log 1/eps)^(m-1)`
immediately afterwards, with the words "In words:". Every theorem here is about
the gloss; the substitution between the two is the frontier `A7-ZETA-BRIDGE`,
carried in Lean rather than in a note. A7 writes strict bands, and the atlas
records both the weak and the strict form and proves the strict one.

**Two of the results are unconditional and one is not, and the split is the
point.** `isO7Counterexample` **refutes MAIS-O7** at every positive scalar
target: the rank-zero rung has pair `(1,1)` and the terminal fibre `(1/2,1)`,
so the conjectured increase runs backwards. It proves the whole two-rung
certificate -- the pair at every point of each rung, both exponent sets, both
infima attained. The note is not weaker in quantifier strength -- it proves the
pair at every point of the terminal rung and states that both infima are
attained -- what the atlas adds is that certificate as one unconditional object.
And
`o7RankZeroRung_eq_saddleRung` identifies its rungs against A7's own `C_k`
rather than asserting the specialization. `o77AllSaddlesHavePairOne_holds`
**proves MAIS-O77(b)** at print's own quantifiers: pair `(1,1)` at every point
of every nonterminal critical set, with axioms `propext`, `Classical.choice`
and `Quot.sound` only. **MAIS-O77(a) and MAIS-O70's first two clauses are
conditional**, and CONJ-026 and CONJ-028 stay `OPEN` for that reason alone.

**Four propositions are assumed and not proved, and they are named.**
`O70-EIGEN-LAW` is the real-Wishart density with the eigenvalue Jacobian,
frozen at the test functions the derivation consumes; `O70-EXACT-LOCAL` is the
existence of exact local pairs; `O70-ZETA-BRIDGE` and `A7-ZETA-BRIDGE` carry the
substitution `MAIS-A6` `def:local` and `MAIS-A7` `def:llc` each make between
their zeta definition of the pair and the band-volume gloss that follows it.
Print asserts an equivalence; **each frontier assumes one direction only**,
volume order to zeta-pole order, which is the direction the atlas results need
and the weaker thing for a hypothesis to be. The
last two are separate assumptions and the A7 one is strictly stronger: `O70`'s
consumes `HasExactLocalPair` on a germ that vanishes, A7's consumes
`HasLocalVolumeOrder` on a germ centred at a saddle. Two are owed to the
candidate -- the submitted solution cites them rather than
deriving them, so assuming them leaves its own derivation intact -- and two are
owed to the source, because `def:local` and `def:llc` assert them. All four are on
hold, each with a reason and none by silence. `scripts/check_frontier_evidence.py`
holds each to a frozen surface, a manifest entry and unconditional stress
artifacts, and prints the whole debt on every run; **passing it is not evidence
a frontier is true**. `NC-011` records that none of the six baseline corpora
supplies the eigenvalue law, so the blocker there is availability rather than
effort. Per-problem coverage and the assumption table are generated into
[`docs/status/sources/mais-2026.md`](../../docs/status/sources/mais-2026.md).

**Four results this needed are absent from the Mathlib revision this repository
pins, and were built here** -- `NC-010` and `NC-012` are the searches, both
Mathlib-only, so this is a statement about one pinned corpus and not about every
formalization corpus. A Gromoll-Meyer splitting along an arbitrary subspace whose Hessian
block is nonsingular (`exists_gromoll_meyer_splitting`); print's own Lemma 2 at
its stated generality, an arbitrary nondegenerate indefinite form in `n >= 3`
variables plus an arbitrary continuous germ vanishing at the origin
(`hasLocalVolumeOrder_abs_matrixQuadForm_add_germ`); Sylvester's rank
inequality, which the pinned Mathlib has in no form -- only upper bounds on the
rank of a product; and currying for the product Lebesgue measure. The Morse
lemma itself is not ours: eight modules and 1,396 lines of the Tau Ceti
development are vendored under `vendor/TauCeti/`, Apache-2.0, pinned at
`d7bf8387`, with the scope and the toolchain gap recorded in its `PROVENANCE.md`.

**Both A7 problems have submitted solutions, and neither was found to contain a
mistake.** MAIS issue
[#5](https://github.com/lionellevine/MAIS/issues/5) is `CHECKED` and issue
[#12](https://github.com/lionellevine/MAIS/issues/12) `PARTIAL`. Issue #12's
argument is **followed**: its equation (9) already writes the generalized
splitting, `L - L(w) = Q_alpha(xi) + g(zeta)` with `g(0) = 0` and no
nondegeneracy asked of `g`, which is Gromoll-Meyer, and that is what was built.
Only its name for the tool is loose, and the atlas proves the splitting
`C-infinity` rather than analytic -- everything its Lemma 2 consumes, with the
regularity gap named rather than papered over.
`Examples.Conjectures.MAIS.loss_quartic_on_degenerateNull` rules out a
Morse-Bott normal form at a rung point, which (9) neither claims nor needs. Issue #5 is the one genuinely different route: it takes the
rank-zero pair through the analytic Morse lemma at signature `(2,2)`, which does
apply there, and the atlas proves it by an explicit integral instead. **So for
#5 what is machine-checked is the claim and not the argument; for #12 it is
both, up to the regularity of the chart.** Issue #12's complete-solution claim
is still not verified, because part (a) rests on the frontier above. Verdicts, and what each column
does and does not say, are in
[`docs/status/mais-solutions.md`](../../docs/status/mais-solutions.md).

**Two earlier results in the causal layer are negative, and both are answers to printed problems
this tree could not state a week ago.** `Examples.Causal.O24Refutation.isEmpty_o24Solution`
proves **MAIS-O24 has no solution** -- clauses (a) and (c) of `prob:effective`
are incompatible for any list of polynomials and any constants, and neither (b)
nor the complexity clauses are used. `Examples.Conjectures.MAIS.not_maisO33_etaStarPos`
proves **MAIS-O33's persistent-corruption threshold is not positive**,
unconditionally; the value `eta* = 0` is proved separately and is conditional on
the uncorrupted-recovery baseline print cites and this tree does not formalize.
Both rest on candidates submitted to the MAIS tracker -- issues
[#7](https://github.com/lionellevine/MAIS/issues/7) and
[#9](https://github.com/lionellevine/MAIS/issues/9), both by kumino -- and in
both cases a step of the submitted argument did not survive: O24's final
`mu`-then-`u` choice is circular against print's quantifier order and was
reversed, and O33's `delta = 0` instance was replaced by `delta = 1/2` on
action-independent kernels, which removes two dependencies Mathlib does not
carry. **What is machine-checked in each is the candidate's claim, not the
candidate's proof**, and the upstream comments say so.

CONJ-025 is the other recent one: **MAIS-O38 is true**, under print's own
two hypotheses and at every `m` where the printed sentence has content — every
`m` with `1 ≤ k(m) < m`, not merely on a tail — proved by
`Examples.Conjectures.MAIS.maisO38_polynomialSamplesSuffice_holds`. Two weaker
forms of this row were published first and are gone: one asked for designs only
eventually, and one guarded the conclusion but still assumed an atlas-supplied
premise print does not write. The
construction and the argument are MAIS issue [#30](https://github.com/lionellevine/MAIS/issues/30)'s, submitted by 26david26 and
stated there to have been produced and checked entirely by AI systems with no
human verification; the atlas supplied the transcription, the machine-check, and
four domain-neutral facts Mathlib lacks that the proof needs -- polynomial
genericity, maximal minors of a rectangular matrix, a hyperplane-family null
bound standing in for the semialgebraic dimension theory the argument is usually
phrased in, and measurability of a projection along a sigma-compact factor. Two
readings of quantifiers print leaves unwritten are separately false and are
carried beside the row as findings, not as answers.

MAIS-O29(b) is the case worth reading, because what is claimed about it changed
on 2026-08-23 and the claim before that date was a retraction.
`boltzmann_minimax_floor` bounds a *deterministic* estimator where
`subsec:queries` takes an infimum over randomized ones, so it bounds the wrong
infimum; that retraction stands. What is new is a bound at print's own
quantifier: `AISafetyAtlas.Conjectures.MAIS.O29Experiment` builds the sampled
Boltzmann experiment and
`Examples.Conjectures.MAIS.boltzmannMinimaxRisk_collision_bounds` pins the
randomized minimax risk between `1/2` and `1` at the collision skeleton, at
every budget and every inverse temperature. That answers (b) at one print-legal
instance and at no other -- on a class where the risk decays, none of (b) is
touched -- and it does not move CONJ-008, which stays `prob:boltzmann`(a) only,
because (b) is a determine-clause and no truth-valued `Prop` is `Same` as one.

MAIS-O27 has no *conjecture* row for the same reason -- it has one target row,
CONJ-013, carrying a specification per clause -- and gained two negative
instances
the same day, both at `prob:floor`'s real quantifier now that all three of its
clauses are stated there: `not_o27RealRadiusVanishes_collision` for (a), and
`not_realEdgesSurviveAt_collision` for (c) at edge strength `λ`. Clause (c)'s
*second* half -- print asks to exhibit, at the complementary pairs, a model and a
member of its identified set omitting the edge -- is now
`exists_strong_edge_omitted_collision` rather than a sentence about the proof of
the first half.

**Also unreleased, merged to `main` after `v0.7.0` was tagged**: Ashby's chapter
11 and Touchette–Lloyd's control limits at printed scope behind an
`AISafetyAtlas.Control` facade, the sharp no-free-lunch characterization with the
count that says almost no prior meets its condition, Fano and data processing,
and two joins that spend that material rather than shelve it —
`Knowledge.Entropy` puts Fano's floor on the knowability kernel, and
`Oversight.VarietyBound` separates what an overseer can see from what it can do.
`atlas-check` gains a `variety` kind whose false verdict is proved not to be a
clearance.

A statement-by-statement audit of all thirteen graded sources sits in
[`docs/provenance/source-coverage-audit.md`](../../docs/provenance/source-coverage-audit.md);
sections 6 to 8 are the causal ones, sections 9 to 12, added on 2026-09-09, are
the wireheading ones, and section 13, added on 2026-09-10, is Orseau & Ring's
*Self-Modification and Mortality in Artificial Agents* — the companion half of
the double paper whose other half is section 11, previously pinned and
ungraded. Before that date the whole `AISafetyAtlas.Wireheading`
cluster was outside the ledger.

No version has been cut for it. `Oversight.VarietyBound` was **accepted at
`REVIEWED`** on 2026-08-17, recorded on `BY-004`, which owns the bridge
declaration; the reviewed-bridge count is 3. The signature is scoped to that
bridge and is not a reviewed reading of Ashby's law in general — see
[`docs/interpretation-reviews/review-oversight-varietybound.md`](../../docs/interpretation-reviews/review-oversight-varietybound.md).
Counts in the generated snapshot below are current for the branch; the release
narrative that follows is not about it.

Current phase: `v0.8.0` is **published** — see
[`docs/releases/v0.8.md`](../../docs/releases/v0.8.md). It is a breadth release that
spends its last third on the risk breadth creates. The atlas took on a community:
MAIS open-problem agendas are carried as compiling Lean statements, seven settled
by the build, one submitted candidate conditionally verified against three named
frontier hypotheses, two printed propositions refuted with countermodels. It also
gained a causal layer, the Kleinberg–Mullainathan–Raghavan fairness trade-off with
both escapes realized by witnesses, Ashby's counting law with a runnable check on
its *hypothesis*, and a vendored doubly-efficient debate development, on a
toolchain moved to Lean v4.33.0. Against that, v0.7 had recorded that one joint is
not composition — one *transport* between two domains, which is a different count
from consuming modules and is not conflated with it here. So `report_consumers.py
--hub` now lists 10 modules consuming the knowability kernel, four of them added
this release, and `Causal` and `Compositional.Hyperproperties`, which had no
reference to it in either direction, reach it in one step — the trace
theory that had defined `TraceSystem` and `IsKSafety` for two releases without
anything producing a trace has a producer, and anonymity is a theorem rather than
an absence of identifiers from a structure. The seven notions of agent behaviour
still have no transports between them, and the release note says so in v0.7's own
words. Two MAIS-O70 fidelity adjudications remain unsigned and no gate checks
that file.

Previously: `v0.7.0` — see
[`docs/releases/v0.7.md`](../../docs/releases/v0.7.md). It is a depth release on
Wolpert's *Physical limits of inference*, carried at the source's own
quantifiers with the finiteness restrictions the proofs never used removed and
the places the printed text does not determine a statement recorded as numbered
clashes, together with the probability substrate that material needs. It is also
the first release to join two domains rather than deepen one: `Knowledge.Devices`
transports between the knowability kernel and Wolpert devices without identifying
them, `Knowledge.Check` and the `atlas-check` executable make the kernel runnable
by a consumer who cannot read Lean with agreement theorems behind them, and every
domain gets a generated dependency view. Every source backing Lean was re-checked
against its published text, which fixed a real citation defect (Everitt et al.
cited at the technical report's numbering rather than the published chapter's) and
recorded two version traps. Theorem statements, the public API and the axiom
profile all change; the reviewed-bridge count does not.

`v0.6.0` is tagged and published. It answers one question — what
an observer can recover about a system it is part of — with a knowability kernel
and six specializations over it, adds Breuer's abstract self-measurement core at
`EQUIVALENT`, mechanizes the survey's own §4.3 as BY-044 at `EQUIVALENT`, and ships
the public page. It is the first release since v0.5.1 to change theorem
statements, statement-match grades, and the public import surface. v0.5.0
makes the one-ledger, source-neutral workbench model explicit: absolute
workbench metrics replace survey-row fractions, catalogued sources have
directory/work roles, mathematical-area navigation is generated, conjectures
have a contained intake path, and the contributor task board is maintained in
`tasks.yaml`. Validation checks the process boundaries as well as the ledger
shapes. v0.5.1 is maintenance: the conjecture ledger is empty and reports
itself that way, and the guide around it is cut back to what the mechanism
actually does. No theorem statement, statement-match grade, bridge status,
public API, or axiom profile changed in either release.


## Earlier notes formerly in STATE.md, "Current work"


- v0.5.0 is published. `parsimony` carried the one-ledger merge, the
  de-anchoring, and the process changes described above.
  `atlas-reshape` was squashed into it and archived.
- v0.5.1 empties the conjecture ledger and cuts the guide around it. `v0.5.0`
  stays exactly as published and still carries the withdrawn `CONJ-001`.
- Multi-commit local history remains on the archive branches; public PR history
  is the squash commit only.
- v0.6.0 is published. `self-knowledge-landscape-sweep` carried it and was
  squashed into `main`. What it contains, not the order it arrived in:

  **One spine.** `LAND-KNOW-001` is the exact-knowability kernel: `Knowable` in
  decoder form, the no-collision characterization as a theorem rather than
  definitional unfolding, `Determines` ordering observations by informativeness,
  and the negative certificate. Six rows build on it or instantiate it, which is
  what makes it a spine rather than a definition —
  [`relations.md`](../../docs/status/relations.md) types every such edge.

  **One graded paper core.** `LAND-SELFMEAS-002` (`EQUIVALENT`) is Breuer 1995's
  abstract set-theoretic measurement core: reading sets, inference maps, meshing,
  and abstract Propositions 1–2. Proposition 1 is proved twice — derived from
  Proposition 2 (axiom-free) and by Breuer's own chain (`propext`, `Quot.sound`).
  `LAND-SELFMEAS-001` is the ungraded whole-state specialization;
  `LAND-SELFMEAS-003` is atlas modelling that *derives* proper inclusion from a
  product complement or a finite cardinality gap instead of assuming it, plus the
  bijective positive boundary.

  **One survey-proof audit.** BY-044 (`EQUIVALENT`) now has a process-compositional
  Lean model for §4.3's Proposition 4.7 and Theorem 4.8. It exposes the sketch's
  non-cancellation step as a strict positive awareness-cost law, separates the
  local self-awareness obstruction from the maximal-composite proof, and permits
  ordinary awareness cycles. `AISafetyAtlas.Examples.SelfAwareness` supplies a
  cyclic inhabited model and the flat two-cycle boundary showing why
  irreflexivity alone is insufficient. The fixed-horizon and source-fidelity
  residuals are pinned in
  [`limited-self-awareness.md`](../../docs/provenance/limited-self-awareness.md).

  **Four layers over the spine.** `LAND-TEMPORAL-001` indexes observations by
  time, keeping *the target as of `s` from evidence at `t`* apart from *the
  current target at `t`*; prior art is Mathlib's filtrations, recorded as
  `NC-007`. `LAND-AMBIG-001` counts what an observation leaves open on finite
  state spaces. `LAND-SELFREF-001` makes the observer's model a component of the
  state, and complete self-knowledge holds **iff** nothing else is in it.
  `LAND-ACCUM-001` bounds ambiguity over a window: never decreasing, never
  exceeding the product of the steps.

  **Two domain consumers.** Joint observation's coverage laws are the kernel
  applied to `q.observe`, with every statement and axiom profile unchanged.
  `LAND-CRMDP-KNOW-001` reads the CRMDP complement pair as a knowability
  collision, linking wireheading to the spine by a theorem.

  **External and ledger.** `CLM-LAWVERE-001` wraps Mathlib's types-level Lawvere
  theorem; `CLM-LAWVERE-CCC-001` is a source claim with a candidate lead.
  `LAND-CL-001` reproduces the AFP Chandy–Lamport snapshot proof as the
  contemporaneity boundary — Path A, no Lean surface. The ledger gained typed
  adjacency (`relations`, `result_shape`) with validator guards, and `NC-002` …
  `NC-007` record every absence claim machine-readably.

  **Navigation conventions.** Facade parents are grouped by what one import
  actually supplies — aggregating facades, the partial aggregate
  (`Verification`), and the kernels whose specializations import individually —
  because "open one facade" had been sending readers to `Knowledge` for layers
  it deliberately does not re-export. Module-specific examples mirror their
  module's path, which moved the robot certificate to
  `Examples.Verification.Robot`. Both rules are stated in
  [`AGENTS.md`](../../AGENTS.md); the per-module table is in
  [`AISafetyAtlas.lean`](../../AISafetyAtlas.lean).

  Evidence: [self-measurement kernel](../../docs/provenance/self-measurement-kernel.md),
  [landscape sweep](../../docs/provenance/embedded-self-knowledge-landscape.md).
- v0.7.0 is published. `information-limits-foundation` carried it and was
  squashed into `main` as `1270117`; pre-squash history is kept locally on
  `archive/information-limits-foundation-pre-squash-20260815`. It carries the
  Wolpert 2008/2018 development and, on top of it, the first things that make
  that development usable rather than only correct:

  **The spine–device joint.** `LAND-KNOW-DEVICE-001` states the conditional
  transports between `LAND-KNOW-001`'s `Knowable` and BY-024's `WeaklyInfers`.
  The two are still **not** identified — that non-identification is a theorem,
  witnessed both ways — but a knowability witness for the device's own
  setup-and-conclusion pair, present in every realized block and straddling the
  target value, now refutes Definition 3 and Definition 11 alike, the second for
  every context. `Knowledge.Devices`, with `Examples.Knowledge.Devices` showing
  the straddle clause is load-bearing rather than convenient.

  **One job rather than another witness.**
  `Examples.Oversight.Overseer` asks whether letting an overseer reconfigure
  recovers a hazard bit a fixed monitor cannot read, and answers it both ways on
  one four-state system. The non-obvious half: an overseer satisfying Definition
  3 can emit a report stream from which the hazard cannot be decoded, because
  Definition 3 chooses the configuration per question while a decoder must work
  in all of them at once.

  **A checker someone else can run.** `Knowledge.Check` supplies the executable
  half with agreement theorems, on the pattern `FiniteDecision` set for coverage,
  and `lake exe atlas-check` reads a finite model as JSON and prints the verdict
  with the declaration that certifies it. Three kinds: `knowability`,
  `coalition` (the joint-observation question — `Covers` is definitionally
  `Knowable` on the coalition's observation) and `device`. Every verdict reports
  worst ambiguity, so a failing model says how far off it is.
  `scripts/check_atlas_check.sh` asserts twelve verdicts against the proofs in
  `Examples.Oversight.Overseer` and `…JointObservation.Procurement`, and CI runs
  it. Guide: [`atlas-check`](../../docs/guide/atlas-check.md).

  **Navigation, atlas-wide rather than branch-local.** `docs/agent/by-id.json`
  carries the file and line of all 124 ledger declarations; the declaration
  dependency view went from one domain to all thirteen, derived from the tree so
  a new domain gets one by existing. Both changes turned up latent defects that
  every gate had been green through: a scope-stack bug that made four
  declarations unresolvable, an inference view recording 536 declarations against
  a tree of 682, and two fail-open holes in the view checker that no domain it
  had ever read could trigger.

  **What a runnable check still does not reach.** `atlas-check` answers models
  phrased over `Knowable`/`Covers`, which is Knowledge, Oversight, Inference,
  Wireheading and SelfAwareness. Compositional, Preference, SocialChoice,
  Learning and Explainability have no runnable backend and could have one.
  Logic, Computability and Verification's core are undecidable by construction —
  that is the content of those results, not a gap.

  Not done here, deliberately: nothing is pushed, no tag is cut, and the
  joint-observation-synthesis pin is untouched — it still points at `v0.5.1`,
  107 commits back, and repinning waits for a tag.
- Known-open in that release:
  - **No per-declaration API site.** A `doc-gen4` pipeline was built and removed
    on cost grounds; see [open work](../../docs/guide/open-work.md). The static landing
    page in [`site/`](../../site/) is *not* part of this gap: it is deployed and live at
    <https://mbrcic.github.io/ai-safety-formalization-atlas/>, shipped from `main`
    by [`.github/workflows/pages.yml`](../../.github/workflows/pages.yml) on pushes that
    touch `site/` (verified 2026-08-29).
  - **Reuse is mostly internal, and the share is falling.**
    `scripts/report_consumers.py` reports 38 of 248 declarations consumed
    outside `Examples/` (measured 2026-08-30; 21 of 105 at v0.7, so the share
    fell from 20% to 15% while the corpus more than doubled). Two of the 38 are
    new on this branch and are the only reuse the MAIS ledger created:
    `Causal.Model.ancestors_eq_univ_iff` reaches `Conjectures.BinaryPair` and
    `Conjectures.MAIS.O31Chart`, and `Causal.Skeleton.behaviorEq_of_observed_eq_empty`
    reaches `Conjectures.BinaryPair`. The spine and its
    two domain consumers compose. The accumulation layer consumes the kernel
    without being consumed. Of the physical bridges, one declaration of eleven
    now reaches a sibling module and the rest are exercised only by their own
    witnesses.
  - The knowledge cluster's guide is
    [`docs/guide/knowledge-model.md`](../../docs/guide/knowledge-model.md); paper-level
    residuals stay in `docs/provenance/`. New layers must update its
    *Not proved* section or it becomes the next stale summary.
  - Reviewed AI-system bridges stay at two. BY-044's own bridge status is not
    `REVIEWED`; the release licenses no claim about a deployed system.

