## Statement freeze

**A reviewed statement is frozen. Proofs are not.** A statement is reviewed
once it carries a fidelity grade in `registry.yaml` or `conjectures.yaml`, or a
pinned source in `docs/provenance/`.

| may change freely | frozen |
|---|---|
| proof bodies, `have`/`let` structure, tactic choice | the binders, hypotheses, quantifiers and conclusion of the declaration |
| new private helper lemmas | the axiom set — nothing may be added |
| docstring prose that does not restate the claim | the claim a docstring or grade asserts |

Weakening a hypothesis, narrowing a quantifier, adding a side condition, or
specializing the conclusion is **not** a proof step, even when it makes the
proof go through. It is a **schema event**: revise the statement in its own
change, say which direction fidelity moved, and re-grade the row. A grade
earned by the old statement does not transfer to the new one.

The reason is that the kernel cannot see this failure. Every fidelity defect
this repository has shipped and later fixed was in a definition or a statement,
and every one compiled. An agent that may edit statements can always close a
goal by editing the goal, and the build reports success either way.

If a statement looks wrong, say so and stop — a `sorry` with a note naming the
suspected defect is a better outcome than a proof of something else.

`scripts/check_statement_freeze.py` hashes the signature of every ledger-graded
declaration against `docs/status/statement-lock.json` and reports drift in the
cheap gate. It is advisory and compares source text, so reformatting reports a
change that is not one — the report is a question, never a verdict. Answer it,
re-grade the row if fidelity moved, then `--write` to record the new statement.

### Conditional results, and the debt they create

A result proved under a proposition the atlas does not prove is a **conditional
verification**, and the assumed proposition is a debt. `CONTRIBUTING.md` says how
to report the result; this says how the debt is tracked.

Every assumed proposition gets a row in the `FRONTIERS` registry at the top of
`scripts/check_frontier_evidence.py`, which the cheap gate runs. The row names the
frozen `..._iff` surface, the unconditional stress artifacts, and three fields no script
can check: `owed_to`, `decision`, `reason`. The gate prints all of it on every run,
which is the whole reason the registry is a literal in the checker rather than a
fourth ledger with a validator and a generated view — three rows do not earn that,
and the debt is more discoverable printed beside its own evidence than filed away.

`owed_to` must not be collapsed. `"candidate"` means a submitted solution cites the
proposition rather than deriving it, so assuming it leaves that derivation intact
and verifying the submission does not require paying the debt. `"source"` means the
printed problem statement asserts it. `"atlas"` means we chose a formulation the
source did not, and the gap is of our own making — the expensive kind. Never report
a total across the three.

`decision` is `hold` or `discharge`, and a hold is a decision rather than a
silence: the `reason` must say what discharging would cost and record that no
maintainer has ruled, if none has. An artifact counts only when it does not itself
assume the frontier — a theorem `frontier → X` reads exactly as strong whether the
frontier is true or false, and the check enforces that. Passing this check does not
show that the frontier is satisfiable: an artifact may only probe a formula, rule
out a cheap branch, or verify that the asserted setting has a required property.

### The layer a text diff cannot reach

Every check above reads source. On a toolchain bump the dangerous change is the
one where the source does not move: an upstream rename behind an alias, a
different instance chosen, a definition made reducible. The text is identical,
the build is green, `axiom-audit` still says proved — of something else.

`scripts/check_elaboration_drift.py` compares declarations by their **elaborated
type**. It emits a normal form from Lean and hashes it in Python, never in Lean,
because `String.hash` belongs to the toolchain under comparison and hashing there
would make every declaration look changed in exactly the situation the tool
exists for.

```bash
python3 scripts/check_elaboration_drift.py --self-test              # on either tree
python3 scripts/check_elaboration_drift.py --dump out.json --raw    # on each tree
python3 scripts/check_elaboration_drift.py --compare old.json new.json
python3 scripts/check_elaboration_drift.py --classify old.json new.json

# the standing check, and what CI runs on every branch that touches Lean
python3 scripts/check_elaboration_drift.py --dump out.json --raw
python3 scripts/check_elaboration_drift.py --compare \
  docs/status/elab-baseline-v4330.json out.json --fatal silent
```

Dump `--raw`, which keeps the normal form instead of a digest of it, and commit
that. A hashed dump halves to ~3 MB and loses the only thing `--classify` can
work from, so the recorded class breakdown stops being reproducible from this
repository.

Commit them as **plain text, never gzipped**. Git already zlib-compresses every
blob and deltas each dump against the one before it; a `.gz` defeats both, and
this pair measured 734,042 bytes packed gzipped against 391,190 bytes packed as
text. The 42,000-line diff that compression was meant to solve is handled by
`.gitattributes` instead: `-diff` renders a migration as one `Bin` line and
costs nothing. Nothing but `--compare` and `--classify` ever reads a dump.

Run `--self-test` first on any tree you dump: it decides four known-answer cases
against a real elaborator, and a fingerprint that never changes and one that
always changes are both useless. `--dump` needs everything built, including
`scripts/lean_build_targets.txt`, because module discovery is artifact-based — a
target you did not build is silently not compared.

A dump selects declarations **by the module they compiled into**, not by their
name, and records which it did under `selector`. Selecting on the `AISafetyAtlas`
name prefix misses everything our modules compile under someone else's namespace
— the vendored `Kolmogorov.*` and debate `Comp.*` layers, 636 declarations, 72 of
them on the public API pin, including the theorem
`AISafetyAtlas.Logic.chaitin_incompleteness` is assigned from. `--compare` warns
when the two dumps disagree on `selector`, because then the report counts the
difference between the selectors as well as the difference between the trees.

The bucket that matters is **silent**: printed type identical, elaborated type
not. A hashed dump can only say *that* something moved, which is why the
committed dumps are `--raw`.

That bucket is also the only one a branch can be **gated** on, which is what
`--fatal silent` selects. A plain `--compare` fails on any movement at all —
the right question for a migration, and red on every ordinary pull request,
since adding statements is what a branch is for. A declaration whose printed
type is unchanged cannot have changed meaning through an edit, so a silent
change is never work anyone asked for, and CI holds this tree to
`docs/status/elab-baseline-v4330.json` on that bucket alone. It catches what no
source-reading check can: a Mathlib rebuild against a moved artifact, an
upstream alias, a different instance chosen.

Expect it to go red on a toolchain bump. That is the tool working. Re-adjudicate
the silent set, re-dump both sides, record the classes — do not widen the flag.
`agent_gate.sh` separately runs `--classify` over the committed pair, which needs
no toolchain and holds the recorded accounting to the class registry, so a class
widened or a dump edited turns the cheap gate red without waiting for CI.

The silent count grows with the library — 131 at 5358 declarations, 171 at 5994
— because it counts declarations that happen to touch whatever upstream renamed.
The number of *reasons* does not: there were eleven, and they come from upstream's
churn. So a class is adjudicated once against an anchor that holds at both
toolchains, recorded in `docs/status/elaboration-classes.json`, and never
re-litigated; `--classify` matches a migration's silent set against the registry
and exits non-zero only on what is left over.

A class states its verdict as `removes` and `adds`, and both are enforced: a
declaration is classified only when the classes that fired account for every
constant that left *and* every constant that arrived. The `change` string is
prose for a reader and is checked by nothing. Matching on the departure alone is
unsound: `setOf` leaving would match the `setOf` class whatever replaced it, so
`setOf -> Evil` would certify clean and an unrelated substitution in the same
statement would be swallowed. A class excuses a
*replacement*; a check that never reads the replacement is not checking it. **Reading two new classes is work
that stays the same size as this library grows; reading 171 names is not.** A
silent change that kept every constant and rearranged them is reported apart and
can never be excused by a registry entry — that is a binder kind, an argument
order or a universe moving, and it needs its own verdict.

`docs/status/elab-baseline-v4310.json` and
`docs/status/elab-baseline-v4330.json` are the two sides of the last
migration, both module-selected and both kept because a dump cannot be
regenerated once its tree moves; compare the next toolchain against the v4.33.0
one. **Keep two.** When a bump lands, its two sides replace the previous pair;
Foundation moves monthly, and a dump per toolchain we ever pinned turns a fixed
cost into an accruing one. `tests/test_elaboration_drift.py` enforces the two.
`docs/provenance/elaboration-adjudication-v4310-v4330.lean` holds the anchors,
checkable at either toolchain, and `docs/status/migration-baseline.json` records
the per-class counts for the migration itself.
