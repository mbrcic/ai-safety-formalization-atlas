# Conjectures

A conjecture is an open question with a compiling Lean statement and no proof.

Stating a safety property exactly enough to be checkable is usually the hard
part, and the statement is useful before anyone proves it: it fixes the objects,
forces the assumptions into the open, and gives the next person something to
attack. So a precise open question is a deliverable here, not a placeholder for
one.

An open conjecture asserts nothing — defining a `Prop` is not claiming it, and
that is the whole point of the mechanism. **Nine conjecture records are currently
present: three open and six resolved**, and each resolved row
names the proof that settled it.

## Four kinds of row, because not every printed problem is a conjecture

MAIS-A2 contains one printed `conjecture`, two `question`s and eleven
`problem`s. A problem reading *"determine the asymptotics"* is resolved by
determining them — what it cannot have is a `Prop` that is `Same` as the
instruction, since existence is not exhibition and a proposition asserting that
a solution exists asks a different question from an instruction to produce one.
That is a fact about **transcription**, not about solvability.

Keeping such problems out of the ledger left the atlas with no single index of
what it covers, and a reader who opened `conjectures.yaml` could reasonably
conclude the formalization stopped where the rows did. Since 2026-08-24 every
printed A2 target has a row, and the `kind` field says what sort of row it is.

**The ledger is no longer A2-only.** CONJ-025 grades MAIS-O38 against agenda
**A3**'s `prob:samples`, a dictionary-learning uniqueness question that shares
none of the causal vocabulary the other rows are built on; every rule below
applies to it unchanged, including the `Same`-scope requirement. Its
transcription is recorded in
[`mais-o38-transcription.md`](../provenance/mais-o38-transcription.md).

| `kind` | What the source does | What `lean` points at | Resolved by |
|---|---|---|---|
| `claim` | states something true-or-false | the doubted `Prop` | a proof |
| `answer` | someone proposed an answer to a determine-problem | a `Prop` grading *that answer is correct* | a proof |
| `target` | says *determine* / *exhibit*, nobody has answered | the **specification** — a predicate over a candidate answer | an answer arriving, which then gets its own `answer` row |
| `blocked` | the atlas cannot state it at all | nothing; `absent_declarations` names what is missing | building the substrate |

A `target` row may not point at a record whose fields carry **no proof
obligations**. Inhabiting such a structure proves nothing, which is the failure
the answer-construction literature names first. A record whose fields *are* the
obligations is a different object and is exactly right for an exhibit-problem:
`Causal.O24Solution` carries a Turing machine and a `TM2OutputsInTime` bound
among its fields, so a term of it is a solution and nothing is left to check
separately. The validator enforces the weaker half of this — every clause must
register the predicate that decides whether a proposed answer is right, so a row
cannot advertise a type a solver could inhabit for free. The `answer_candidate`, `answer_admissible` and `answer_correct` fields
carry that triple, and `admissibility_status` records whether a **circular**
answer is excluded — `{x | P x}` satisfies any find-all specification of itself,
and no Lean check rejects it. `Unformalized` there is an open formalization gap
and not a clean state.

One row excludes the restatement with a demand taken directly from print.
MAIS-O24 says *"exhibit … in time polynomial in `S`"*, and `O24Constructor`
carries a Turing machine with a certified time bound, which a bare description
cannot inhabit.

A finite carrier is not enough. MAIS-O31 asks which of `2(m-1)+1` coordinates
are identifiable, and `card_o31Coordinate` proves the answer space has exactly
that many inhabitants, so a proposed list can be represented as a `Finset`.
But classical filtering converts any predicate on a finite type into a
`Finset`; `isO31IdentifiableAnswer_of_set` proves that every correct `Set`
specification therefore yields the finite-list form. O31 remains
`Unformalized` on admissibility because print supplies no combinatorial answer
grammar that would exclude this restatement.

The demand has to constrain how the data are obtained, not merely change their
container. An existential — *there is some finite family of polynomial pieces
cutting this set out* — also fails: the canonical set together with a proof of
the existential satisfies it, and the restatement survives. That is why
`IsO27EdgeSurvivalAnswer` sits in the tree as an atlas strengthening offered for
study and is named in **no** admissibility field.

MAIS-O27, MAIS-O29(b), and MAIS-O31 are `Unformalized`, and the reason is the
source rather than the tooling. *Semialgebraic* appears twice in MAIS-A2 — as a hypothesis on
the model class in `prob:exact`, and as a demand on the answer in
`prob:starter-set`(a) — and neither is `prob:floor`, which says only *"decide
for which pairs `(s, δ)`"* and, for clause (b), *"as an explicit function"*
without defining *explicit*. `prob:boltzmann`(b) presumes a rate grammar in
saying *"up to constants"* and never names one. A hypothesis in one printed
problem does not impose an answer language on another; grading either row
against a language print does not state would make it **narrower than print**.
Both rows say what a solver would have to fix, and the right way to close them
is to ask the MAIS authors what counts as an answer.

`Partial` exists for a multi-clause row whose clauses differ on this axis. No
row uses it today; the positional `answer_admissible` list is what it is checked
against, so it cannot be asserted of a row whose clauses agree.

`scripts/validate_conjectures.py` prints the breakdown rather than one number,
because *"eight recorded"* over a 20-row file is how this confusion started. Counts elsewhere in this guide are over conjecture rows — kinds
`claim` and `answer` — since a blocked row is not an open conjecture.

## Who proposed what

**Four of the five resolved rows rest on constructions submitted to MAIS by
other people, and the fifth reuses one of them.** The ledger records this per
row in `proposed_by`; it is repeated here because a reader who meets the atlas
through a "resolved" count will otherwise read the constructions as its own.

| Row | Target | The construction is | The atlas's part |
|---|---|---|---|
| CONJ-004 | MAIS-O23 | MAIS [issue #6](https://github.com/lionellevine/MAIS/issues/6), Svyatoslav Novikov (kumino) | transcription, transport of the rational witness to the real chart, machine-check |
| CONJ-005 | MAIS-O34(a), margin clause | the same two-variable construction, MAIS issues [#4](https://github.com/lionellevine/MAIS/issues/4)/[#6](https://github.com/lionellevine/MAIS/issues/6) | transcription, real-chart transport, machine-check |
| CONJ-008 | MAIS-O29(a) | issue [#6](https://github.com/lionellevine/MAIS/issues/6)'s collision pair again | the transfer step — that the pair is also a Boltzmann collision at every positive inverse temperature — and its proof |
| CONJ-009 | MAIS-O34(a), fibre criterion | Rob Sneiderman (Robby955), MAIS [issue #4](https://github.com/lionellevine/MAIS/issues/4) | both directions of the equivalence, the non-vacuity witnesses on each side, the restatement against the printed class, and the semialgebraicity of the criterion |
| CONJ-010 | MAIS-O31 | Svyatoslav Novikov (kumino) with OpenAI Codex, MAIS [issue #8](https://github.com/lionellevine/MAIS/issues/8) | transcription only; the row is `OPEN` |
| CONJ-025 | MAIS-O38 | David Holmes (26david26) with GPT 5.6 Sol, MAIS [issue #30](https://github.com/lionellevine/MAIS/issues/30) | transcription and the machine-check, together with four domain-neutral facts Mathlib lacked that the proof needs |

The MAIS-O24 row is a fifth submitted antecedent — Svyatoslav Novikov (kumino)
with OpenAI Codex, MAIS [issue #7](https://github.com/lionellevine/MAIS/issues/7)
— where what the atlas added is the transcription, the machine-check, and one
repair to the argument's last step; see
[`mais-o24-refutation.md`](../provenance/mais-o24-refutation.md).

**What is the atlas's own** is the statement layer and the proofs, which is a
smaller claim than resolving the problems and a different one. Named results
with no submitted antecedent: the MAIS-O24 certificate bundle and the `K(G)`
parameter chart it is stated over; `Causal.measureMinimalBudget_eq_exactMinimalBudget`,
which removes the last scope gap on MAIS-O25 by proving the minimal budget is
the same number whether the analyst's output law is a `PMF` or an arbitrary
probability measure; the negative MAIS-O27(a) instance
`Examples.Conjectures.MAIS.not_o27RealRadiusVanishes_collision`, at print's own
real quantifier; the sampled Boltzmann experiment, which pins MAIS-O29(b)'s
randomized minimax risk between `1/2` and `1` at one skeleton, at every budget
and every inverse temperature; and CONJ-009's proof, whose opposite-orientation half could have
refuted the submitted criterion and does not.

**Source text beside Lean text.**
[`mais-conjecture-source-vs-lean.md`](../provenance/mais-conjecture-source-vs-lean.md)
prints every MAIS-linked row three ways — what the source prints, what the Lean
says, and what the Lean says read back from its binders rather than from its
intent — with a per-row statement of what differs. It is the document to open
before believing a `Same` grade.

**A resolved row is not a resolved problem**, and every resolution field says
which clause it covers. MAIS-O29 has three clauses and CONJ-008 answers (a);
MAIS-O34 has two and CONJ-005 and CONJ-009 together answer part of (a).

**CONJ-025 is the exception, and it is worth stating plainly.** MAIS-O38 has one
clause and no sub-parts, and it is now **true** at every non-degenerate `m` while
retaining print's growth hypotheses —
`Examples.Conjectures.MAIS.maisO38_polynomialSamplesSuffice_holds`. The
construction and the argument are MAIS [issue #30](https://github.com/lionellevine/MAIS/issues/30)'s,
submitted by 26david26 and stated there to have been produced and checked
entirely by AI systems with no human verification; the machine-check is now that
verification. Two readings of quantifiers print leaves unwritten are separately
false and are carried beside the row as findings, not as answers.

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
conjecture has a compiling statement" is verified rather than claimed.

**Compiling is not non-vacuity, and the two are checked separately.** A statement
whose hypotheses cannot be satisfied is true and says nothing, so each row must
either cite a witness inhabiting its antecedent or disclose that none exists.
Most do carry one. The row transcribing MAIS-O26 does not, and since 2026-08-30
that is settled rather than suspected: its antecedent needs a solution to
MAIS-O24, and `Examples.Causal.O24Refutation.isEmpty_o24Solution` proves there
are none, so `maisO26_exactRate` **is** vacuously true. The row is `RESOLVED`
and its entry says which kind of resolution that is — a fact about `conj:exact`
as printed, and nothing about the rate the conjecture is asking after.

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

**A row may also leave the ledger entirely**, and the same obligation follows
it. A withdrawn encoding whose source is a *determine*-problem has no `Same`
grade available to it, and the source-first rule below keeps atlas-original
variants out; in both cases the row is removed rather than carried at a grade
the rule rejects. The removed entry is copied verbatim into
[`docs/provenance/retired-conjecture-rows.md`](../provenance/retired-conjecture-rows.md)
together with the date and the reason, and its `CONJ-` number is **retired and
never reused**. `conjectures.yaml` records the next unassigned number;
`scripts/validate_conjectures.py` parses the archive headings, rejects a number
appearing both live and retired, and requires every lower number to occur
exactly once across the live ledger and the archive. So "not in the ledger" is
never the same as "never happened". The archive states the Lean status
separately for each row: one historical module was deleted, one withdrawn
encoding survives unchanged, and one atlas-original declaration survives under
a type that later changed with its shared assumptions.

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

**For MAIS, this is enforced as a source-first rule.** Every live ledger row
whose graded source is the MAIS agenda or a pinned MAIS issue must have
`source_scope: Same`, and it may not use `Bridged`. If the literal source
statement is false, vacuous, ambiguous, or ill-posed, that is a result about the
source; the atlas does not add a premise or substitute an object to repair it.
An atlas-original variant or a retired encoding may still be useful Lean, but it
stays outside the live MAIS ledger. `Selected` remains available only for a
truth-valued branch that MAIS itself explicitly asks the reader to decide.

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
