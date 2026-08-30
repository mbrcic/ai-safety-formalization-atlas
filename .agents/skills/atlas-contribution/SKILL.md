---
name: atlas-contribution
description: 'Land a change in the AI Safety Formalization Atlas so it satisfies the repository''s rules without the contributor having to learn them. Use this whenever the work is a contribution to this repository — adding or editing a Lean theorem, definition or example, a registry or conjecture row, provenance, documentation, or tooling — and whenever the request is "how do I contribute", "add this to the atlas", "is this ready to submit", "open a PR", or "what do I still owe". It routes rather than instructs: three commands decide what applies to this particular change, and the rules stay in AGENTS.md where they are enforced.'
---

# Contributing to the atlas

You write the mathematics. This walks the procedure.

**This file contains no rules.** They live in `AGENTS.md` and `CONTRIBUTING.md`,
and a second copy would drift from them silently. What is here is the order to
do things in and which command answers which question.

## The three commands

```console
python3 scripts/preflight.py     # what does THIS change oblige?
./scripts/agent_gate.sh          # is it mechanically correct?
python3 scripts/preflight.py --brief    # the cheap re-read on a retry
```

`preflight.py` reads the diff, decides which of six contribution kinds it
contains — Lean library · example or witness · ledger · generated file · docs ·
tooling — and prints only the governing sections, **sliced verbatim out of
`AGENTS.md` and `CONTRIBUTING.md` at runtime**. What you read is what binds. Run
it with nothing changed and it tells you where to find an unclaimed target
instead.

## The order

1. **Write the theorem, definition or row.** This is the part that is yours.
2. **`python3 scripts/preflight.py`** — it names the obligations and the
   commands for what you actually touched, and nothing else.
3. **Do what it names.** Every kind has a build or regeneration step; generated
   files are regenerated, never hand-edited.
4. **`./scripts/agent_gate.sh`** — the verdict. `--fast` is the retry loop after
   it has failed once; the full gate is owed before the commit either way.
5. **Open the PR**, and answer in its body the one question no gate can:
   *what does your statement say, what does the source say, and where do they
   differ?* A reviewer needs a claim they can disagree with, not silence.

## What decides, and what only advises

`agent_gate.sh` decides. `preflight.py` advises and always exits 0 — it is a
briefing, not a gate. Two of the checks inside the gate are advisory too and say
so in their output: a changed graded statement and an unwitnessed scope claim are
**questions**, not verdicts. Answer them in the change that raises them.

## What no script can do for you

Whether a Lean statement says what its source says. Whether a witness inhabits
the hypotheses or merely compiles. Whether a second formalization earns its
place. These are why the repository has human review, and they are where a PR
is actually accepted or rejected — so put your reasoning in the PR body rather
than leaving it to be reconstructed.

## If a statement looks wrong

Say so and stop. A `sorry` with a note naming the suspected defect is a better
outcome than a proof of something else. An agent that may edit statements can
always close a goal by editing the goal, and every gate stays green when it does.
