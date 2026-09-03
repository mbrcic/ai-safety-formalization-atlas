## Validation

Cheap preflight:

```console
./scripts/agent_gate.sh
# repeated agent iterations: one-line success, full output on failure
./scripts/agent_gate.sh --quiet
```

The gate ends with `pytest tests/` (malformed-shape regressions) and
`ty check scripts/ tests/`. Both are skipped with a notice when the tool is not
installed, so the gate still runs without them; CI installs both, so neither is
optional on a pull request. `check_conjecture_grade_prose` needs PyYAML and is
skipped the same way. Install all three with
`python3 -m pip install pytest ty pyyaml`. Everything else in the gate is the
standard library of Python 3.9 or newer, which the gate checks before it starts.

### The `--fast` lane (`--lean` is the old name)

```console
./scripts/agent_gate.sh --fast          # skips the five self-test steps
./scripts/agent_gate.sh --fast --quiet  # both flags compose
```

`--fast` skips exactly five steps: `test_validators`, `test_source_neutral_views`,
`test_a1_a3_pattern_a_harness`, `pytest tests/`, and `ty check`. Those five
exercise the validator scripts themselves.

Those five are **not** independent of repository content, and the lane must not
be justified that way. `test_validators` copies `registry.yaml`,
`conjectures.yaml`, `tasks.yaml`, `formalization-search.json`,
`AISafetyAtlas.lean`, the whole `AISafetyAtlas/` tree and several `docs/` trees
into a temporary tree and runs the validators against them;
`test_source_neutral_views` reads the live registry; the a1–a3 harness reads a
reproduction script and provenance documents; and `tests/` reaches declaration
locations and repository Markdown. So a `--fast` run can be green over a change
they would reject.

What justifies the lane is **when** it is used, not independence — see the
retry-loop paragraph below — and the full gate is owed before the commit.

Everything that reads the tree, the ledgers, or the generated views *directly*
still runs, so `--fast` still catches a rename that orphaned a docstring name, a
module missing from the root import, a stale dependency graph, a mislaid example
file, a changed graded statement, or a registry `line:` field that shifted.

**Numbers are measurements, not constants.** Whole-gate timings vary by roughly
threefold run to run, so no figure is quoted here. Measure; do not inherit a
number from this file.

**This is a retry loop, not an iteration loop.** The gate belongs before a
commit, not between edits, so `--fast` earns nothing on the first run — you owe
the full gate anyway. Where it pays is the second run and after: the gate fails
on a Lean-facing check, you fix, and you want to know whether the fix took. That
retry is a fraction of the full gate, and the failures that put you in that loop are
exactly the ones `--fast` still watches — a shifted registry `line:` field, a
regenerated view that did not get regenerated, a docstring name orphaned by a
rename. Fix, `--fast`, fix, `--fast`, then the full gate once to commit.

**The full gate is mandatory before you commit**, and non-negotiable whenever
you touched anything under `scripts/`, `tests/`, or the ledger schemas — those
are precisely the inputs `--fast` stops watching, and its own last line says so.
A green `--fast` is never a green change. CI runs the full gate regardless, so
skipping it locally only moves the failure later.

If you are reaching for the gate to find out whether Lean is happy, that is the
wrong tool and the real cost. Ask the language server
(`lean_diagnostic_messages` and friends): it answers per-file in seconds what a
build reports minutes later, and unresolved names after a rename are exactly its
job. When you do build, build the cone you changed —
`lake build AISafetyAtlas.Causal.Query` — rather than bare `lake build`, which
elaborates the root's whole closure. A no-op full build is ~4 s, so once the
tree is warm the build is not what costs; the generators and the gate are, and
both are once-per-commit.

Full green (Lean + axioms):

```console
./scripts/agent_gate.sh
python3 scripts/check_print_axioms.py
lake build
xargs lake build < scripts/lean_build_targets.txt
lake exe axiom-audit --root AISafetyAtlas --modules-from AISafetyAtlas
python3 scripts/generate_declaration_index.py --write   # after adding or renaming
```

`axiom-audit` is upstream -- inherited through Foundation's lakefile and in
`lake-manifest.json` all along -- so it is the one axiom check here that this
repository did not write, and the reason to run it is that it shares no code
with the two that it did. `--modules-from` is not optional: the root does not
transitively import the whole library, and auditing by root import alone
reaches 5957 declarations against 9439 for the module sweep, with the 3482 it
misses being exactly the off-root material `lean_build_targets.txt` exists for.

`generate_declaration_index.py` walks the **elaborated environment** and writes
`docs/status/declaration-index.json`, which is what lets
`check_docstring_identifiers.py` tell a real declaration from a name that merely
appears somewhere in the source. It costs a full elaboration, so it belongs
here rather than in the cheap gate; the cheap gate reads the committed file and
says nothing when it is absent.

Two worklists exist for the step *after* a gap closes. Neither can fail and
neither is in the gate, because both ask a question a regex cannot answer:

```console
python3 scripts/where_is_graded.py CONJ-002   # every line restating a grade
python3 scripts/list_absence_claims.py        # every "X is not here" sentence
```

Run them after landing anything that closes a gap. The recurring defect on this
repository is not a broken proof — it is a sentence that outlived the field or
the declaration it described, and these print the sentences to re-read.

Historical v0.1 only: `python3 scripts/audit_release_v0_1.py` (must not block
genuine post-v0.1 bridge graduation).
