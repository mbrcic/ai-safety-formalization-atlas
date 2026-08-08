# Conjectures

A conjecture is an open question with a compiling Lean statement and no proof.

Stating a safety property exactly enough to be checkable is usually the hard
part, and the statement is useful before anyone proves it: it fixes the objects,
forces the assumptions into the open, and gives the next person something to
attack. So a precise open question is a deliverable here, not a placeholder for
one.

Nothing in the ledger is asserted by the atlas. **Zero conjectures are currently
recorded.**

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
conjecture has a compiling statement" is verified rather than claimed. Each
conjecture module also carries `example`s witnessing that its antecedents are
inhabited: a statement whose hypotheses cannot be satisfied is true and says
nothing.

## Containment

Conjecture modules live under `AISafetyAtlas.Conjectures.*`, are explicit CI
build targets, and are **never reachable from the atlas root import** — the
validator rejects a conjecture whose module the root can see. A badly judged
conjecture therefore cannot reach the public API regardless of who merged it.

Conjectures never enter theorem counts, statement-match grades, or bridge
review. They are reported on their own line.

## Contributing one

Open a [conjecture issue](../../.github/ISSUE_TEMPLATE/conjecture.yml). Three
questions carry the filter:

1. **The conjecture**, stated precisely enough to be false.
2. **What would refute it.** If nothing could, it is not a conjecture.
3. **Prior art checked**, naming the nearest known result and how yours differs.
   If your conjecture asserts that no formalization or proof exists, that is a
   claim of absence and needs a recorded `novelty_checks` entry in
   [`formalization-search.json`](../provenance/formalization-search.json).
   See [methodology](methodology.md#formal-library-discovery-evidence).

The form asks for two more so a maintainer can triage without a round trip —
the nearest atlas declaration or area, and what would change if it were
settled — plus a Lean statement if you have one, which is optional. Its
checkboxes restate the three questions above; they add no obligation.

**You do not need Lean.** Prose in, statement out — writing the Lean form for
someone else's conjecture is a distinct contribution, and both are recorded:
`proposed_by` names who asked the question.

## Record shape

A conjecture enters [`conjectures.yaml`](../../conjectures.yaml) only once its
Lean statement compiles; everything before that lives in the GitHub issue.
`OPEN` means unsettled, `RESOLVED` means proved or refuted, `WITHDRAWN` means
retired. Both terminal states require a written `resolution`, so a conjecture
never leaves the queue as an undocumented decision.

```yaml
- id: CONJ-00N
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
which runs in `scripts/agent_gate.sh`. Closest precedent for compiling
statements without proofs: Hales'
[`formalabstracts`](https://github.com/formalabstracts/formalabstracts).
