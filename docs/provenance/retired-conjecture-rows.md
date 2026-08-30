# Retired conjecture-ledger rows

Rows removed from `conjectures.yaml` verbatim, with the date and the reason.
**Nothing here is a live ledger row.** A row leaves the ledger for one of three
reasons, and all are recorded rather than deleted:

* the encoding was **withdrawn** — the registered proposition was defective, and
  the source problem it aimed at is unaffected;
* the row was **atlas-original** and the MAIS source-first rule in
  [`docs/guide/conjectures.md`](../guide/conjectures.md#scope-against-the-printed-source)
  keeps atlas-authored variants out of the live MAIS ledger;
* the row held **no Lean and no proposition** — it recorded that a printed
  problem cannot be stated here at all. That is a fact about the atlas's
  coverage, and it belongs in the coverage map and the source directory rather
  than on the conjecture board. See *The six coverage rows* below.

This file exists so that no exit is an undocumented decision. The ledger's
own rule — a terminal state requires a written `resolution` — is honoured by the
entry below rather than by a row that is no longer there. `CONJ-` numbers listed
here are **retired and never reused**. `conjectures.yaml` records the next
unassigned number; `scripts/validate_conjectures.py` parses these headings,
rejects live/retired overlap, and requires every lower number to occur exactly
once across the live ledger and this archive.

The JSON blocks are historical ledger snapshots, not claims about current Lean
types. Current Lean status is stated per row below: CONJ-001's module was
deleted, CONJ-007's withdrawn declaration survives, and CONJ-011's names survive
but their shared O26 assumption bundle later changed.


## CONJ-001 — `RestrictedNFL` (module also removed)

**Withdrawn and removed in v0.5.1, 2026-08-07.** The row entered the ledger already refuted: its statement was a restricted no-free-lunch claim whose refutation was known when it was registered. `v0.5.1` emptied the ledger and removed `AISafetyAtlas/Conjectures/RestrictedNFL.lean` with it, so unlike the rows below **no Lean declaration survives**. The full withdrawal argument is in [`docs/releases/v0.5.1.md`](../releases/v0.5.1.md); the record kept here is the ledger entry as it stood at commit `bc8eac72`.

```json
{
  "id": "CONJ-001",
  "statement": "AISafetyAtlas.Learning.no_free_lunch_supervised averages uniformly over every target function. Real systems are drawn from restricted classes — computable, resource-bounded, finite-precision, tame. Conjecture: for a homogeneous loss, closure of the target family under relabelling targets off the training domain is not only sufficient for learner-independence but necessary, so restricting to any family lacking that symmetry lets some learner beat another on average. The schematic form is deliberate: a specific restriction instantiates it rather than needing its own theorem. The motivating instantiation is definability in an o-minimal structure, which is out of reach today — Mathlib carries finite combinatorial VC dimension and no o-minimal structures.",
  "refutation": "Exhibit a homogeneous loss, a training domain with an off-training point, and a nonempty target family satisfying exactly one side of the biconditional. Either direction failing refutes it. The suspected weak direction is necessity: a family could fail off-training closure and still average symmetrically for accidental reasons.",
  "prior_art": "Distinct from AISafetyAtlas.Learning.homogeneous_iff_learner_indep, which characterises learner-independence in terms of the loss with the target class left unrestricted; this fixes the loss as homogeneous and asks about the target class. Searched: Mathlib (no o-minimality; Combinatorics.SetFamily.Shatter is finite VC only), the atlas Learning surface, and the BY-020/BY-021/BY-022 rows.",
  "lean": "AISafetyAtlas.Conjectures.RestrictedNFL.statement",
  "tags": [
    "learning-theory",
    "computational-complexity"
  ],
  "proposed_by": "mbrcic",
  "status": "WITHDRAWN",
  "resolution": "Withdrawn 2026-08-07, unsound as stated and superseded as intended. (1) The reverse direction is false. Take X = {s, x1, x2}, S = {s}, Y = {0,1}, 0-1 loss, and F = {(x1,x2) = (0,0), (1,1)} — the orbit of one target under a single global permutation applied off S, so OffTrainingClosed holds. The learner predicting (0,0) yields loss vectors {(0,0),(1,1)}; the learner predicting (0,1) yields {(0,1),(1,0)}. Psi = indicator of the zero vector separates them, so learner-independence fails while closure holds. The defect is that OffTrainingClosed applies one permutation simultaneously at every off-training point, which is far weaker than closure under permutation of the domain. (2) The repaired statement is a published theorem, not an open question: Schumacher-Vose-Whitley (GECCO 2001) and Igel-Toussaint (JMMA 2004, doi 10.1023/B:JMMA.0000049381.24625.f7) prove performance is algorithm-independent over a finite family iff it is closed under permutation. The atlas already tracks this as contributor task CT-10, a reproduction rung. The prior-art field the conjecture template requires would have caught this before it was recorded."
}
```

## CONJ-007 — `maisO27_regretFloor_withdrawnThresholdEncoding`

**Withdrawn 2026-08-21, removed from the ledger 2026-08-23.** The registered proposition was false for encoding reasons unrelated to MAIS-O27: empty classes break its `IsLUB` demand, and edge survival need not be a closed threshold cut. It stayed in the ledger as a `Retired` row until the MAIS source-first rule landed, which reserves live ledger rows for statements graded `Same` against their source. MAIS-O27 is a *determine*-problem, so no truth-valued `Prop` is ever `Same` as it, and a row for it can only exist once a truth-valued candidate is submitted to MAIS and graded against that submission — the route CONJ-009 and CONJ-010 already take. The source problem remains open and its targets remain formalized as definitions.

The named withdrawn Lean declaration still exists with its recorded type.

```json
{
  "id": "CONJ-007",
  "statement": "Withdrawn first encoding of MAIS-O27: it required every binary skeleton to admit a complete answer object and required the edge-survival region to be a closed cut generated by one threshold function.",
  "refutation": "The encoding is refuted independently by skeletons with an empty margin class, whose empty real error set has no least upper bound, and by the checked O23 skeleton at regret one, where edge survival forms an open rather than closed strength ray. These are defects in the encoding, not resolutions of MAIS-O27.",
  "prior_art": "MAIS-A2 Problem 4.6 and MAIS-O27 ask to determine a radius asymptotic and the full set of pairs (s,delta) for which edges survive. They do not assert that every nominal skeleton has a nonempty class or that the pair set is generated by a closed threshold. The faithful rational targets now live separately as regretRadius, O27RadiusVanishes, O27HasFirstOrderConstant, and O27EdgeSurvivalRegion; because a determine-problem is not itself truth-valued, no replacement conjecture is invented.",
  "lean": "AISafetyAtlas.Conjectures.MAIS.maisO27_regretFloor_withdrawnThresholdEncoding",
  "tags": [
    "interpretability"
  ],
  "proposed_by": "Atlas statement-only answer specification for MAIS-O27.",
  "status": "WITHDRAWN",
  "resolution": "Withdrawn after adversarial review established that the registered proposition was false for two encoding reasons unrelated to the source problem: empty classes break its IsLUB demand, and edge survival need not be a closed threshold cut. The source problem remains open and its mathematical targets remain formalized as definitions.",
  "source_ref": [
    "mais-a2-2026"
  ],
  "context_source_ref": [],
  "source_scope": "Retired",
  "source_fidelity": "DetermineProblem",
  "source_note": "Withdrawn, and the reason is a category rather than a defect: prob:floor asks for the full set of (s,delta) pairs on which the regret floor vanishes. No truth-valued Prop is the same statement as a determine-problem, so the withdrawn encoding -- a closed threshold cut -- was narrower than print by construction and could not be repaired by widening. What replaces it is a set of named targets rather than an invented truth value: o27ProblemTargets, O27RadiusVanishes, O27HasFirstOrderConstant, O27EdgeSurvivalRegion."
}
```

## CONJ-011 — `maisO26_exactRateWellPosed`

**Removed from the ledger 2026-08-23.** Atlas-original: `conj:exact` with one hypothesis added, that the cut class is nonempty. It was graded `Beyond`/`AtlasOriginal` and could never be `Same`, because print states no such clause. Under the source-first rule an atlas-authored variant stays outside the live MAIS ledger. The question it records — whether print presupposes a nonempty class or leaves the statement false on an empty one — is still open, and the empty-class route is machine-checked by `Examples.Conjectures.MAIS.not_maisO26_exactRate_for_of_empty`. **That route can never be run.** Since 2026-08-30 `Examples.Causal.O24Refutation.isEmpty_o24Solution` proves no `O24Solution` exists, so neither this retired row's antecedent nor CONJ-003's can be inhabited; the verbatim record below predates that and is left as filed.

The block below is the row exactly as retired. Its statement also mentions
compact semialgebraicity because the shared `O26ClassAssumptions` carried that
hypothesis at the time. Removing that source-unprinted hypothesis from live
CONJ-003 later changed the type of the surviving atlas-original declaration as
well: current `O26ClassAssumptionsWellPosed` is current
`O26ClassAssumptions` plus nonemptiness, with no compactness premise. The names
still compile, but they no longer instantiate the historical statement copied
below. No live grade rests on them.

```json
{
  "id": "CONJ-011",
  "statement": "Atlas-original, and deliberately NOT MAIS-O26: print's conj:exact with one hypothesis added, that the cut class MM(sk,lambda,mu) is nonempty. For every solution to MAIS-O24 there are a coefficient and a degree, chosen after the solution and before the diagram, such that for every skeleton over a finite set of binary chance variables with real tables whose cut class is nonempty, compact semialgebraic and has a linear recovery modulus L below an explicit threshold, and where K is def:margin's chart maximum, the randomized exact-policy-probability minimax budget N(epsilon) is Theta(K log(1/epsilon)) as epsilon tends to zero under one uniform polynomial bound in 1/lambda, 1/mu and L.",
  "refutation": "Give an O24 solution, a skeleton and margins whose cut class is NONEMPTY and satisfies O26ClassAssumptionsWellPosed, and for which Causal.exactMinimalBudget fails either side of the stated Theta rate. The empty-cut-class route recorded against CONJ-003 cannot be run here: this row's antecedent requires the class to be nonempty, so an empty class fails it outright. o26ClassAssumptions_of_wellPosed proves this antecedent entails the printed one by projection; it does NOT prove the entailment strict, which would need an instance satisfying O26ClassAssumptions and failing the nonemptiness clause, hence an O24Solution with an empty cut. No O24Solution is exhibited anywhere in the tree, so whether this row asks about fewer instances than CONJ-003 is unknown, and this row's own antecedent has no witness either -- the Prop may be vacuously true.",
  "prior_art": "Math for AI Safety (MAIS), agenda MAIS-A2, conjecture conj:exact (MAIS-O26), in the pinned source. Print states the rate for N = MM(sk,lambda,mu) with mu fixed and attaches no condition on the class being inhabited. No source consulted states the well-posed variant, and none addresses whether the printed sentence is intended to presuppose a nonempty class. The distinction is the standard presupposition-versus-precondition gap and is not specific to this agenda, but the atlas found no statement of it for this conjecture.",
  "lean": "AISafetyAtlas.Conjectures.MAIS.maisO26_exactRateWellPosed",
  "tags": [
    "interpretability",
    "computational-complexity"
  ],
  "proposed_by": "Atlas statement-only formalization of MAIS-A2.",
  "status": "OPEN",
  "resolution": "",
  "source_ref": [
    "mais-a2-2026"
  ],
  "context_source_ref": [],
  "source_scope": "Beyond",
  "source_fidelity": "AtlasOriginal",
  "source_note": "Beyond / AtlasOriginal, created 2026-08-22 when CONJ-003 was returned to print's literal quantifiers. There is no printed sentence here to transcribe: conj:exact states the rate without a nonemptiness condition, and this row states it WITH one. It is therefore the atlas's question about print's, not a rendering of print's, which is what Beyond and AtlasOriginal record together. WHY IT IS WORTH A ROW. Deleting the antecedent from CONJ-003 made that row faithful and also made it refutable by an empty cut class at K >= 1, through sSup over the empty set being 0. That refutation is real and is recorded there. It is also not the question anyone is interested in: whether the Theta(K log(1/eps)) rate holds where the rate has content is still open, and this row is where that question lives. o26ClassAssumptions_of_wellPosed proves the well-posed antecedent entails the printed one, by projection. IT DOES NOT ESTABLISH STRICTNESS: an instance satisfying O26ClassAssumptions and failing O26ClassAssumptionsWellPosed would need an O24Solution with an empty cut, and no O24Solution is exhibited anywhere in the tree, so whether this row really asks about fewer instances than CONJ-003 is currently unknown. The same missing inhabitant means this row's own antecedent has no witness either, so this Prop may be vacuously true. NOT A REPAIR OF PRINT. Nothing here claims print meant this. Whether conj:exact presupposes an inhabited class is a question for the source, and the atlas states both readings rather than choosing one."
}
```


## CONJ-014 — MAIS-O27 clause (b), merged into CONJ-013

**Merged and retired on 2026-08-24, the day they were created.** No Lean
declaration was withdrawn and no grade changed; the specifications these rows
named — `IsO27FirstOrderConstantFunction` and `IsO27EdgeSurvivalRegion` — are
live and are carried by CONJ-013.

`prob:floor` is a **single** `problem` environment with three clauses. Splitting
it into three ledger rows made MAIS-O27 the only printed problem in the ledger
with three rows and read as padding, which is how the split was noticed. The
cause was the schema and not the source: `answer_candidate`,
`answer_admissible` and `answer_correct` were single strings, so a problem with
three clauses could not be one row. It also broke a convention the ledger
already had — CONJ-008 covers all of `prob:boltzmann` in one row whose
`resolution` opens *"Coverage: this row is prob:boltzmann(a) only"* — and the
split was made without saying it was a departure.

The three fields are lists now, one entry per printed clause in print's order,
and `validate_conjectures.py` rejects a row whose populated lists disagree on
length, since the correspondence is positional. **One printed problem, one row**
is the rule that follows, and it is not absolute: a problem whose clauses differ
in `kind` still needs a row each, because a resolved claim and an open target
and a blocked clause cannot share a status. `prob:boltzmann` is that case —
CONJ-008 (claim, resolved, clause (a)), CONJ-016 (target, clause (b)),
CONJ-020 (blocked, clause (c)) — and `prob:floor` is not, since all three of its
clauses are open targets.

These numbers are retired and never reused, like every other number in this
file. They are recorded here rather than renumbered because ids are assigned
monotonically and a reused number makes two different things share an address.


## CONJ-015 — MAIS-O27 clause (c), merged into CONJ-013

**Merged and retired on 2026-08-24, the day it was created**, with CONJ-014 and
for the same reason; the argument is under that heading above and is not
repeated. Its specification `IsO27EdgeSurvivalRegion` is live and is CONJ-013's
third clause entry, together with `isO27EdgeSurvivalRegion_self`, the theorem
that the canonical region satisfies that specification by unfolding and so
records the admissibility gap as a checked fact rather than a note.



## The six coverage rows, retired together

**Retired 2026-08-30.** These six carried no `lean`, no `Prop`, and no
`refutation`. Each recorded that one printed A2 problem cannot be stated in this
tree at all, and named the declarations that are missing.

That record is worth keeping and was never worth a ledger row. The elicitation's
first outcome for a MAIS problem is *"Not statable — recorded (as O1/O16 already
are). The map says why. **No Lean required.**"*, and the atlas already records
exactly that for MAIS-O1 and MAIS-O16 in the `mais-open-problems-2026` source
entry of `registry.yaml`, without minting a `CONJ-` number. Minting one per
unstatable problem is what turns a selective conjecture board into a coverage
index for one agenda — the first item on `ROADMAP_IDEAS.md` §8.5's do-not list.

**Nothing recorded here was lost.** Every `blocked_on` and `absent_declarations`
entry below is stated at greater length, per problem, in the matrix of
[`mais-a2-statement-coverage.md`](mais-a2-statement-coverage.md), which is the
live home of the coverage map; the six problems are also named in the
`mais-open-problems-2026` notes in `registry.yaml`. What changed is the address,
not the content, and none of these problems is closer to or further from being
statable than it was.

`CONJ-018`–`CONJ-022` and `CONJ-024` are retired and never reused. The snapshots
below are the rows as they stood at commit `cfe608e`.

## CONJ-018 — MAIS-O2 (`prob:noisy`)

```json
{
  "id": "CONJ-018",
  "kind": "blocked",
  "problem": "MAIS-O2",
  "statement": "MAIS-A2 prob:noisy replaces the policy-probability oracle by sampled actions, allows positive regret, and asks for the minimax budget, separating switching-surface location, stochastic-policy estimation and the irreducible ambiguity from regret, then adds independent response corruption at a known level.",
  "refutation": "",
  "prior_art": "MAIS-A2 prob:noisy. The randomized perfect-recall analyst and the expected-error minimax risk arrived with AISafetyAtlas.Causal.Query; the oracle did not.",
  "lean": "",
  "lean_module": "",
  "answer_candidate": [],
  "answer_admissible": [],
  "answer_correct": [],
  "admissibility_status": "NotApplicable",
  "blocked_on": "The query layer observes exact real policy probabilities, so a transcript's answers are numbers rather than draws. A sampled-answer transcript exists for one channel -- the Boltzmann experiment in Conjectures.MAIS.O29Experiment -- but its answer is a binary Boltzmann response at Bool, not a sampled action under a supplied policy at an arbitrary action type. Independent response corruption at a known level is a second and unrelated gap.",
  "absent_declarations": [
    "AISafetyAtlas.Causal.SampledActionOracle",
    "AISafetyAtlas.Causal.CorruptedAnswer"
  ],
  "tags": [
    "learning-theory",
    "information-theory"
  ],
  "proposed_by": "Atlas coverage record; the printed problem has no Lean object.",
  "status": "OPEN",
  "resolution": "",
  "source_ref": [
    "mais-a2-2026"
  ],
  "context_source_ref": [],
  "source_scope": "NotFormalized",
  "source_fidelity": "NotFormalized",
  "source_note": ""
}
```

## CONJ-019 — MAIS-O28 (`prob:average`)

```json
{
  "id": "CONJ-019",
  "kind": "blocked",
  "problem": "MAIS-O28",
  "statement": "MAIS-A2 prob:average replaces worst-case regret by an exception mass under a declared distribution and asks for the radius up to constants, the threshold below which the graph stays identified, and the rate at which the zero-regret radius vanishes as the exception mass does.",
  "refutation": "",
  "prior_art": "MAIS-A2 prob:average. Print cites Richens et al. 2025 as empirical evidence and Nayebi 2026 as a goal-based average-case recovery theorem; the interventional version is open.",
  "lean": "",
  "lean_module": "",
  "answer_candidate": [],
  "answer_admissible": [],
  "answer_correct": [],
  "admissibility_status": "NotApplicable",
  "blocked_on": "The admissibility notion is average-case against a declared continuous distribution on pairs of profiles with a uniform real mixing weight and masks. The atlas has worst-case admissibility only, and no measure on profile pairs, so neither the exception mass nor the radius it induces can be written.",
  "absent_declarations": [
    "AISafetyAtlas.Causal.AverageAdmissibleFamily",
    "AISafetyAtlas.Causal.profilePairMeasure"
  ],
  "tags": [
    "learning-theory",
    "decision-theory"
  ],
  "proposed_by": "Atlas coverage record; the printed problem has no Lean object.",
  "status": "OPEN",
  "resolution": "",
  "source_ref": [
    "mais-a2-2026"
  ],
  "context_source_ref": [],
  "source_scope": "NotFormalized",
  "source_fidelity": "NotFormalized",
  "source_note": ""
}
```

## CONJ-020 — MAIS-O29(c) (`prob:boltzmann`(c))

```json
{
  "id": "CONJ-020",
  "kind": "blocked",
  "problem": "MAIS-O29(c)",
  "statement": "MAIS-A2 prob:boltzmann(c) asks which distribution over queries maximizes the minimax rate -- the design problem over mixtures, masks and observations, which print separates from the estimation theory of clause (b).",
  "refutation": "",
  "prior_art": "MAIS-A2 prob:boltzmann(c). Print says the econometric literature supplies the local analysis for (b) but not the design question.",
  "lean": "",
  "lean_module": "",
  "answer_candidate": [],
  "answer_admissible": [],
  "answer_correct": [],
  "admissibility_status": "NotApplicable",
  "blocked_on": "boltzmannMinimaxRisk is already an infimum over analysts, so it optimizes the query strategy away. The design problem needs the risk under a *fixed* query law, and then an extremum over such laws; neither object exists, so there is nothing over which to state a maximization.",
  "absent_declarations": [
    "AISafetyAtlas.Conjectures.MAIS.boltzmannMinimaxRiskUnder",
    "AISafetyAtlas.Conjectures.MAIS.IsOptimalQueryDesign"
  ],
  "tags": [
    "learning-theory",
    "information-theory"
  ],
  "proposed_by": "Atlas coverage record; the printed problem has no Lean object.",
  "status": "OPEN",
  "resolution": "",
  "source_ref": [
    "mais-a2-2026"
  ],
  "context_source_ref": [],
  "source_scope": "NotFormalized",
  "source_fidelity": "NotFormalized",
  "source_note": ""
}
```

## CONJ-021 — MAIS-O30 (`prob:restricted`)

```json
{
  "id": "CONJ-021",
  "kind": "blocked",
  "problem": "MAIS-O30",
  "statement": "MAIS-A2 prob:restricted asks, for almost every parameter choice, which edge indicators and table entries are Sigma_W-identifiable, characterized combinatorially in the graph and the sets W, O and Z, together with the minimal W identifying everything on the ancestors of the utility.",
  "refutation": "",
  "prior_art": "MAIS-A2 prob:restricted, whose flavor print compares to Eberhardt, Glymour and Scheines on how many experiments identify a causal graph.",
  "lean": "",
  "lean_module": "",
  "answer_candidate": [],
  "answer_admissible": [],
  "answer_correct": [],
  "admissibility_status": "NotApplicable",
  "blocked_on": "Sigma_W -- mixtures acting as the identity outside W -- has no general form here. One instance exists: O31LocalMixture is Sigma_W for a single intervenable variable on the chain, built for q:chain. What is missing is the general construction, labels for edge and table functionals, and a combinatorial classifier in (G, W, O, Z). The coverage matrix said 'Sigma_W-identifiability' was missing outright for longer than that was true, which is why the absence is now named at declaration level.",
  "absent_declarations": [
    "AISafetyAtlas.Causal.RestrictedMixture",
    "AISafetyAtlas.Causal.SigmaIdentifiable"
  ],
  "tags": [
    "interpretability",
    "learning-theory"
  ],
  "proposed_by": "Atlas coverage record; the printed problem has no Lean object.",
  "status": "OPEN",
  "resolution": "",
  "source_ref": [
    "mais-a2-2026"
  ],
  "context_source_ref": [],
  "source_scope": "NotFormalized",
  "source_fidelity": "NotFormalized",
  "source_note": ""
}
```

## CONJ-022 — MAIS-O32 (`prob:rate`)

```json
{
  "id": "CONJ-022",
  "kind": "blocked",
  "problem": "MAIS-O32",
  "statement": "MAIS-A2 prob:rate asks whether the 1/n resolution radius is the truth for goal-conditioned agents over a finite communicating controlled Markov process, in the first-action-data setting of the goal-based theorem.",
  "refutation": "",
  "prior_art": "MAIS-A2 prob:rate, in the goal-based setting of the agenda's Theorem thm:rabe.",
  "lean": "",
  "lean_module": "",
  "answer_candidate": [],
  "answer_admissible": [],
  "answer_correct": [],
  "admissibility_status": "NotApplicable",
  "blocked_on": "The goal layer landed 2026-08-30, built for MAIS-O33 and shared with this row: AISafetyAtlas.Causal.ControlledProcess is print's finite stationary controlled Markov process with the communicating condition, AISafetyAtlas.Causal.Goal is composite goals and depth with the trajectory semantics, AISafetyAtlas.Causal.GoalDynamics is deterministic policies at print's own trajectory-prefix history type, the trajectory law, bounded goal-conditioned agents and the first-action map AISafetyAtlas.Causal.firstActionMapFull this row's family is built from, and AISafetyAtlas.Causal.Corruption is the analyst. The congruence lemma this row used to record as missing is no longer needed for MAIS-O33, whose witness runs on action-independent environments where AISafetyAtlas.Causal.trajectoryLaw_congr makes the two laws the same measure; it would be needed again for a family of environments whose transitions read the action, which is what this row's 1/n question is about. What is still absent is this row's own resolution radius over that family. The atlas's causal layer is interventional rather than goal-conditioned, so nothing here is a specialization of what exists.",
  "absent_declarations": [
    "AISafetyAtlas.Causal.resolutionRadius"
  ],
  "tags": [
    "decision-theory",
    "learning-theory"
  ],
  "proposed_by": "Atlas coverage record; the printed problem has no Lean object.",
  "status": "OPEN",
  "resolution": "",
  "source_ref": [
    "mais-a2-2026"
  ],
  "context_source_ref": [],
  "source_scope": "NotFormalized",
  "source_fidelity": "NotFormalized",
  "source_note": ""
}
```

## CONJ-024 — MAIS-O35 (`prob:starter-sample`)

```json
{
  "id": "CONJ-024",
  "kind": "blocked",
  "problem": "MAIS-O35",
  "statement": "MAIS-A2 prob:starter-sample asks, on a compact locus of the two-variable family where the local radius is linear in the regret, for matching upper and lower bounds on the sampled-action budget recovering the graph and all three parameters, then the crossover at positive regret between sampling error and the radius, and finally the sharp cost of independent response corruption.",
  "refutation": "",
  "prior_art": "MAIS-A2 prob:starter-sample, a starter problem beside prob:starter-set. Print suggests the capacity factor 1/(1-H(zeta)) as the corruption cost.",
  "lean": "",
  "lean_module": "",
  "answer_candidate": [],
  "answer_admissible": [],
  "answer_correct": [],
  "admissibility_status": "NotApplicable",
  "blocked_on": "The two-variable real chart exists and the rest does not: a sampled-action minimax risk, regret adversaries, switching surfaces of the optimal policy family, and the binary-channel capacity that print's conjectured corruption cost is stated in. It shares prob:noisy's missing oracle and adds three objects of its own.",
  "absent_declarations": [
    "AISafetyAtlas.Causal.sampledActionBudget",
    "AISafetyAtlas.Causal.SwitchingSurface"
  ],
  "tags": [
    "learning-theory",
    "information-theory"
  ],
  "proposed_by": "Atlas coverage record; the printed problem has no Lean object.",
  "status": "OPEN",
  "resolution": "",
  "source_ref": [
    "mais-a2-2026"
  ],
  "context_source_ref": [],
  "source_scope": "NotFormalized",
  "source_fidelity": "NotFormalized",
  "source_note": ""
}
```
