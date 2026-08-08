# Conjectures

A conjecture is an open question with a compiling Lean statement and no proof.

Stating a safety property exactly enough to be checkable is usually the hard
part, and the statement is useful before anyone proves it: it fixes the objects,
forces the assumptions into the open, and gives the next person something to
attack. So a precise open question is a deliverable here, not a placeholder for
one.

Nothing in the ledger is asserted by the atlas.

## How a conjecture is checked without being believed

`sorry` is banned repo-wide, so a conjecture does not use one. It ships as a
**`Prop`-valued definition**:

```lean
public noncomputable def statement : Prop :=
  ∀ ..., P ↔ Q
```

Defining a proposition asserts nothing about its truth. The generated
[`AISafetyAtlas/Conjectures/Checks.lean`](../../AISafetyAtlas/Conjectures/Checks.lean)
emits `example : Prop := <name>` for every name in the ledger, so "this
conjecture has a compiling statement" is verified rather than claimed — a string
that looks like a declaration is not a declaration, and a declaration that is not
a closed proposition fails to elaborate. `#check` would be too weak here: it
prints whatever type a declaration happens to have rather than requiring one.

**Non-vacuity is checked in Lean, not declared in YAML.** A statement whose
hypotheses cannot be satisfied is true and says nothing. Each conjecture module
carries `example`s witnessing that its antecedents are inhabited. An unverified
"non-vacuity: yes" field would be a claim nothing checks, which is worse than no
field at all.

## Containment

Conjecture modules live under `AISafetyAtlas.Conjectures.*`, are explicit CI
build targets, and are **never reachable from the atlas root import** — the
validator rejects a conjecture whose module the root can see. A badly judged
conjecture therefore cannot reach the public API regardless of who merged it.
The containment is structural, not editorial.

Conjectures never enter theorem counts, statement-match grades, or bridge
review. They are reported on their own line.

## Lifecycle

```
issue  →  OPEN  →  RESOLVED
                →  WITHDRAWN
```

Everything before `OPEN` lives in a GitHub issue. Issues already have open,
closed, labels, and duplicate handling; rebuilding that in YAML would be
bureaucracy for its own sake. A conjecture enters
[`conjectures.yaml`](../../conjectures.yaml) only when a Lean statement
compiles.

- **OPEN** — statement compiles, nobody has settled it.
- **RESOLVED** — proved or refuted. A refutation is also a theorem (`¬ P`), and
  a proof graduates into an appropriate `registry.yaml` claim or artifact row by
  the normal admission rules. `resolution` records which, and where the proof
  went.
- **WITHDRAWN** — the proposer or a maintainer retired it. Malformed and
  duplicate proposals are closed as issues and never reach the ledger.

Both terminal states require a written `resolution`, withdrawal included: a
conjecture that leaves the queue without a recorded argument is an
undocumented decision, and the next person re-proposes it. `CONJ-001` is the
worked example — proposed, refuted by an explicit counterexample, and found to
have a published answer already tracked as a contributor task.

## Contributing one

Open a [conjecture issue](../../.github/ISSUE_TEMPLATE/conjecture.yml). Three
fields are required and they are the whole filter:

1. **The conjecture**, stated precisely enough to be false.
2. **What would refute it.** If nothing could, it is not a conjecture. This is
   the single most useful thing you can write, and the cheapest to check.
3. **Prior art checked**, naming the nearest known result and how yours differs.
   A keyword search is not a search. If your conjecture asserts that no
   formalization or proof exists, that is a claim of absence and needs a
   recorded `novelty_checks` entry in
   [`formalization-search.json`](../provenance/formalization-search.json) —
   what was searched, at which revision, on what date, and what it did not
   cover. See [methodology](methodology.md#formal-library-discovery-evidence).

**You do not need Lean.** Prose in, statement out — writing the Lean form for
someone else's conjecture is a distinct contribution, and both are recorded:
`proposed_by` names who asked the question.

## What gets accepted

One question, the same one that governs everything else here: *does settling it
make something else easier to state or prove?*

"I find it interesting and nothing else depends on it" is an acceptable answer
if the question is precise. A vague question with enormous stakes is not.

## Record shape

```yaml
- id: CONJ-001
  statement: <prose, precise>
  refutation: <what would show it false>
  prior_art: <what was searched, nearest known result>
  lean: AISafetyAtlas.Conjectures.<Module>.<name>
  tags: [<from the shared vocabulary in registry.yaml>]
  proposed_by: <name or handle>
  status: OPEN | RESOLVED | WITHDRAWN
  resolution: <free text, required exactly when RESOLVED or WITHDRAWN>
```

Validated by [`scripts/validate_conjectures.py`](../../scripts/validate_conjectures.py),
which runs in `scripts/agent_gate.sh`.

## Prior art for this mechanism

Hales' [`formalabstracts`](https://github.com/formalabstracts/formalabstracts)
is the closest precedent for compiling statements without proofs; the
[Erdős problems](https://www.erdosproblems.com/) Lean effort and Wiedijk's
100-theorems list are neighbours. What is different here is the discipline
attached: provenance grading, and interpretation held separate from mathematics,
so a conjecture about AI safety can be precise without smuggling in a claim
about any real system.
