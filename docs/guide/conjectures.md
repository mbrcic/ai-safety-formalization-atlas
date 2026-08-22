# Conjectures

A conjecture is an open question with a compiling Lean statement and no proof.

Stating a safety property exactly enough to be checkable is usually the hard
part, and the statement is useful before anyone proves it: it fixes the objects,
forces the assumptions into the open, and gives the next person something to
attack. So a precise open question is a deliverable here, not a placeholder for
one.

Nothing in the ledger is asserted by the atlas. **One conjecture record is
currently present, and it is open.**

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
  source_ref: [<the one registry source whose statement is transcribed>]
  context_source_ref: [<registry sources the work draws on, graded against nothing>]
  source_scope: Same | Narrower | Mixed | Retired | Beyond
  source_fidelity: <one kind, or a list of them>
  source_note: <required unless Same and Literal; optional and welcome when it is>
```

## Scope against the printed source

**A conjecture must say what the source says.** It is the thing being doubted
and proved, so a specialization the atlas finds convenient changes the question
rather than answering it. Definitions transcribing a source definition are held
to the same bar, for the same reason — they are the objects under discussion.
Theorems are exempt and preferred **wider**: a proved lemma that reaches further
only increases what the tooling is good for.

That is a claim about a specific artifact, so `source_ref` must name one, and
it names **the artifact whose statement is being transcribed** — not everything
the work draws on. Everything else goes in `context_source_ref`, where nothing
claims to be `Same` as it: a definition the `Prop` reuses, an agenda clause that
sets up the question, a GitHub issue that supplied a witness construction.
Listing an artifact in `source_ref` submits the statement to being graded
against it, and a `Same` or `Beyond` grade may name only one — a single verdict
cannot answer to several artifacts at once, and the two are rarely the same
genre. The case that forced this rule was a row graded against a GitHub issue's
criterion *and* an agenda clause reading "Determine … an explicit semialgebraic
condition", which no truth-valued `Prop` is the same statement as.

The graded source must be *pinned* — a DOI locator, or a `content_sha256` of the
bytes that were read. A repository file on a branch, or a GitHub issue body, is
rewritten without notice; grading against one is unfalsifiable. See
[`docs/provenance/mais-source-pin.md`](../provenance/mais-source-pin.md) for how
MAIS is pinned.

`source_scope` compares the Lean `Prop`'s generality to the printed statement.
`Same` is the target. `Retired` is reserved for `WITHDRAWN` entries, where
there is no live claim to be `Same` as; it is required there and rejected
everywhere else, and its `source_note` must say what was retired and why.
`Beyond` is for a question the atlas originated, where the source contains no
counterpart sentence to be `Same` as — it pairs with `AtlasOriginal` and the two
are required together, being one fact seen from two sides. `Narrower` and
`Mixed` are debts, and the validator will not accept a label in place of an
argument: `source_note` must name each axis and say what closing it would take.
**`Mixed` includes widenings.** A `Prop` that drops a restriction print imposes —
quantifying over classes print requires to be compact, say — is as far from
`Same` as one that adds a hypothesis, and naming only the narrowings while
calling the row `Narrower` hides half the gap. A statement that announces its own
specialization while claiming `Same` is rejected outright.

`source_fidelity` records how the `Prop` relates to the printed sentence, as a
kind rather than a grade:

| value | meaning |
|---|---|
| `Literal` | the `Prop` transcribes the printed statement |
| `Selected` | print says *decide whether X*; the atlas states one branch — itself a truth-valued statement print asked for |
| `Bridged` | an atlas-supplied object stands in for something print leaves implicit or defers to an unsolved problem |
| `DetermineProblem` | print asks to *determine* a quantity or a set. No truth-valued `Prop` is the same statement. This is a category, not a defect, and the entry must say what shape replaces it |
| `AtlasOriginal` | the source has no counterpart sentence at all. The question is the atlas's, usually asked *about* a printed result rather than transcribed from one |

A `Prop` can stand in more than one of these relations at once — one branch of a
decide-clause, stated over an atlas stand-in for a class print defers to an
unsolved problem — so the field accepts a list. `AtlasOriginal` is the exception
and never combines: if the source says nothing here, there is no printed sentence
for another kind to describe.

**`source_note` is not a confession field.** It is required when the grade is not
`Same`/`Literal`, and *welcome* when it is — a row at the printed quantifier
often still made reading choices worth recording, and an earlier version of this
schema rejected a note on such a row, which pushed every one of those
disclosures into Lean docstrings where no reader of the ledger sees them. What is
still rejected is a fragment: a note is an argument or it is absent.

A narrow *witness* is fine and always was. State the conjecture at the printed
quantifier and put the witness's shape in `resolution`: for an existential, a
narrow witness proves the general statement outright, so generality is free.

Validated by [`scripts/validate_conjectures.py`](../../scripts/validate_conjectures.py),
which runs in `scripts/agent_gate.sh`. Closest precedent for compiling
statements without proofs: Hales'
[`formalabstracts`](https://github.com/formalabstracts/formalabstracts).
