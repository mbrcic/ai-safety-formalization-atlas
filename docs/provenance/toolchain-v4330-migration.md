# The v4.33.0 toolchain migration

**Status.** Done, 2026-08-31. The whole tree builds, the kernel axiom audit is
green, and no graded statement changed. This note records what moved, what broke,
what is owed back, and — as importantly — which records were deliberately *not*
rewritten.

## What moved

| Pin | Before | After |
|-----|--------|-------|
| Lean | `leanprover/lean4:v4.31.0` | `leanprover/lean4:v4.33.0` |
| Mathlib | `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` (tag `v4.31.0`) | `db584cd6d46c92f209a44c0f1c829460d327499d` (tag `v4.33.0`) |
| PFR | `38e94172b72c8ee8ad64b6365dfc22e559c62ebe` | `7d6404b79b11b1a89dd1b6f997a10b14c208c4ed` |
| Foundation | `b47cf447255addf88a5d72781d0d29641948eb6e` | `30a16ffa93d79d73ab4d02427fa00f50e039bf29` |
| AddCombi | `v4.31.0` | `v4.33.0` |

PFR and Foundation are pinned by commit, not by tag, and both revisions were
chosen because they resolve against the same Mathlib commit this file pins — the
same constraint that governed the v4.31.0 pins, checked the same way.

## Why

Not for a feature. `Causalean` (CausalForge) is on `v4.33.0`, and
[`d-separation-build-or-depend.md`](d-separation-build-or-depend.md) had named
"revisit if this repository moves to `v4.33.0` for other reasons" as the
condition under which depending on it becomes the cheapest of three options for
the causal layer's missing d-separation. Moving first and deciding later is
cheaper than the reverse, because the migration cost is paid once whatever the
verdict, and it grows with every module added at the old pin.

## Evidence

Measured on this tree:

| Check | Result |
|-------|--------|
| `lake build` | 3411 jobs, success |
| `lake build $(cat scripts/lean_build_targets.txt)` | 4086 jobs, success |
| `scripts/check_print_axioms.py` | 2847 declarations ⊆ `{propext, Classical.choice, Quot.sound}` |
| `scripts/agent_gate.sh` | exit 0, in an environment carrying the Python dev dependencies |
| `scripts/check_statement_freeze.py` | 262 graded statements unchanged |
| `scripts/kernel_replay.sh` | 239 modules replayed through the kernel, 16 aggregators skipped, peak 18354 MB, 1961 s |

Two properties of the gate are worth stating, neither introduced by this
migration. It runs under `pipefail`, so truncating a check with `head` closes
the pipe early: the writer takes SIGPIPE, Python raises `BrokenPipeError`, and
an advisory check fails the gate for producing more rows than were displayed —
`check_scope_witnesses` prints 44 and grows with the registry. Truncation is
`awk 'NR <= n'`, which reads its input to the end. Separately, `ty check`
cannot resolve `pytest` outside a virtual environment that has it installed, so
a bare checkout exits 1 there; CI installs it.

The declaration count is the number to read first, but not for the reason it
looks like. `check_print_axioms` derives its list from the **sources**, by regex
over the facade closure, not from the build — so equal counts mean the same
declarations were *asked about*, and a module that failed to build would surface
as an `Unknown constant` failure rather than as a smaller number. The two halves
together are what make the line worth reading.

Both halves were checked against the baseline rather than assumed. The scanner
was run over both trees: the v4.31.0 tree yields **2847** audited names
and the v4.33.0 tree yields **2847**, with an empty difference in both
directions, and the public API sets are **1703** on each side, likewise empty
both ways. The sets are not merely the same size, they are identical name for
name. That comparison needs no v4.31.0 build, because the list is computed from
source.

The scanner has to be read before its count is. `PUBLIC_THEOREM_RE` must admit a
leading attribute: a pattern that does not sees no `@[simp] public theorem` at
all, and 51 declarations reach neither `#print axioms` nor the public API pin in
`docs/status/public-api.txt`, which reads the same pattern. Counts published
before this was repaired are recorded under `measured.erratum` in
`migration-baseline.json` with what they omitted.

That class of bug is invisible to a comparison, and the reason generalizes:
**a check that derives its expected answer the same way the subject does cannot
find it.** Both sides of a name-for-name comparison computed by one pattern
agree exactly where the pattern is blind. `tests/test_public_theorem_regex.py`
pins the name grammar case by case — primes, subscripts, Greek letters, every
delimiter — and must also vary what *precedes* `public`.
`tests/test_seeded_defects.py` tests the other direction, that a tree with a
defect in it turns the gate red, and `scripts/check_audit_coverage.py` reaches
the same surface by a different route: it walks the elaborated environment via
`Lean.collectAxioms` rather than the source, and reports 3824 declarations
inside the same three axioms.

The comparisons below are against `4edc04182b931a3ac0941d3b98120a6f1ca4fe85`,
the pre-migration tip, named by SHA rather than as `origin/main` — that ref
stops meaning the pre-migration tree the moment this branch merges. The same SHA,
the pins, the measured counts and the four adjudications with their verdicts are
recorded in [`migration-baseline.json`](../status/migration-baseline.json), and
`tests/test_statement_drift.py` re-runs the checker against it, so the table
below fails a test rather than merely going stale. That file is a reproduction
pin for this one bump: the live reference for the next migration is this
branch's tip, not the tree before it.

The migration touches 72 Lean files: 54 are the repair itself, the rest vendored
header comments that state a toolchain.

## What broke, by kind

`warningAsError = true` is this package's option, so a deprecation or a new
linter suggestion is a build error here. That inflated the apparent breakage by
roughly four times, and it is worth knowing before reading the numbers above.

1. **Deprecation renames.** Mechanical, except one:
   `Equiv.apply_eq_iff_eq_symm_apply → Equiv.eq_symm_apply` is **not** a drop-in.
   The replacement states the `iff` in the other direction; two of the three
   sites needed `← Equiv.eq_symm_apply` and one did not. The failure surfaces as
   `unsolved goals` several lines away from the rewrite, not at it.
2. **New linters.** `letI`/`haveI` are now flagged in favour of `let`/`have` in
   `Prop`-valued goals, and `linter.checkUnivs` is new.
3. **`simp` unfolds further and closes less.** The single largest category. Six
   waves of it.
4. **`rw` refuses goals that are not type-correct at `implicit` transparency.**
   This is the subtle one, and the technique that closes it is worth carrying:

   > Where `rw` or `simp only` will not match a pattern that is visibly present,
   > apply the lemma as a **term**. Elaboration unifies up to defeq; `rw` gives
   > up at implicit transparency.

   In `Upstream/Debate/Cost.lean` the rewrite failed with "did not find an
   occurrence of the pattern" even though the pattern was in the goal, because
   `StateV`, `State` and `Vera` are plain `def` type synonyms that do not unfold
   at that transparency — the real error, printed below the note, was
   `function expected: vera n.fst`. `congrArg (· >>= postV vera) (Comp.allow_all_pure _)`
   and `(bind_assoc _ _ _).trans (bind_congr fun x => pure_bind _ _)` do what the
   rewrites were meant to do. Marking the synonyms `reducible` also works, but it
   changes `simp`'s term indexing and breaks a sibling bullet, so it is not used.
   The same shape hit `PFun` (`ℕ →. Bool`), which is semireducible and so blocks
   keyed matching against bare `ℕ → Part Bool` lambdas.

## Faithfulness audit

A toolchain migration is faithful when proof bodies may change and **statements
may not**. That is checkable, so `scripts/check_statement_drift.py` checks it
rather than a reviewer asserting it. The rule it applies:

* `theorem`, `lemma` and `example` carry a proof, and the kernel checks it. A
  wrong proof does not compile, so its text is not evidence — only the signature
  is compared.
* `def`, `abbrev`, `instance`, `structure`, `inductive`, `class`, `axiom`,
  notation and macros carry meaning in their bodies, so the whole declaration is
  compared — with `by` blocks masked wherever they appear, including a `Finset`
  membership argument buried inside a term, because those are proofs too.
* `import`, `open`, `variable`, `set_option` and `attribute` change what the
  declarations around them mean, so they are compared whole.

Masking is a heuristic and **not sound in general**: a tactic block can build
data, so `def f : Nat := by exact 0` and `by exact 1` mask to the same text.
The tool therefore never drops such a pair silently — a non-theorem declaration
differing *only* inside a masked block is reported for adjudication. This
migration produced four, and all four are `Prop`-valued fields:
`instMeasurableSingletonClassModel` (`measurableSet_singleton`), `qCD` and `qDE`
(`Finset` membership arguments), and `knowsTrueWitness`, whose only data field
`selector` is untouched while two proof obligations move from
`Set.mem_setOf_eq` to `Set.mem_ofPred_eq` — one more Mathlib rename.

Run against the baseline it reports **31 differences and 135 rewritten proof
bodies**. Every one of the 31 is accounted for:

| # | Where | What | Why it is not a weakening |
|---|-------|------|---------------------------|
| 6 | `Analysis/PolynomialGenericity.lean`, 3 theorems | `[NoAtoms (μ i)]` → `[NullSingletonClass (μ i)]` | Mathlib declares `alias NoAtoms := NullSingletonClass`, deprecated `2026-06-09`. Same class; `warningAsError = true` leaves no choice. |
| 4 | `Causal/StructuralModel.lean`, `submodel` and `removeInfoLink` | `hv.mono f` → `Relation.TransGen.mono f _ _ hv` | The field is `acyclic : ∀ v, ¬ Relation.TransGen … v v` — a `Prop`. Its value is a proof written in term mode, which the masker cannot see. Same field, different proof. |
| 12 | `Portfolio.lean` ×4, `Procurement.lean` ×2 | `deriving DecidableEq, Fintype` → `deriving DecidableEq` | The derive handler does not elaborate at this Mathlib revision. The inductives are unchanged. |
| 6 | the same two files | six written `Fintype` instances | `complete` forces `elems` to hold every element and a `Finset` carries no duplicates, so any two `Fintype` instances on a type agree on `univ` and on `card`. |
| 2 | `Inference/SelfAware.lean`, `Oversight/JointObservation/Architecture.lean` | `set_option linter.checkUnivs false in` | The new linter wants two universe parameters merged — `SelfAwareDevice: universes v, w only occur together`. Merging changes a **public** declaration's universe signature, which is an API change, refused during a version bump. |
| 1 | `Upstream/Debate/Cost.lean` | added `private lemma verabind_cost_eq_zero` | An addition. It changes no existing statement. |

Nothing else differs. Beyond that the diff was searched for every other way a
migration can be made to pass: it adds no `axiom`, no `native_decide`, no
`nolint`, no `maxHeartbeats` or `maxRecDepth` bump, changes no `@[simp]`
attribute, and adds or deletes no Lean file — all 54 are modifications.

**Scope is unchanged, checked field by field.** `conjectures.yaml` and all 48
files under `docs/status/` are byte-identical to the baseline except the
declaration index, below. `tasks.yaml` is not: four lines of CT-7 and CT-9
prose stated the toolchain and are corrected. No task's
identity, status or acceptance criteria changed. `registry.yaml` differs in 116 leaves and they fall
in exactly three fields — 101 `build_environment`, 10 `version`, 5 `notes` — with
**zero** differences in `source_scope`, `coverage`, `status`, `relationship`,
`kind`, `declarations`, `module` or any other graded field. Nothing was regraded
to make the migration land.

**One real scope change, in generated scaffolding.** Regenerating
`docs/status/declaration-index.json` against the v4.33.0 build drops the names it
carries from 4687 to 4669 (the file's own `count` field, which also counts module
entries, goes 4692 to 4674). All eighteen are `deriving Fintype` by-products —
`X.enumList`, `X.enumList_nodup` and `X.enumList_getElem?_ctorIdx_eq` for the six
inductives that lost their `deriving` clause. Nothing in the repository refers to
any of them, and all eleven `Fintype` instances survive under their original
names, `instFintypePrincipal` among them. The index had been stale since the
`Fintype` workaround landed; CI regenerates it and diffs with `--exit-code`, so
the push would have caught it, but the cheap gate cannot because the index needs
a built environment.

**No guard was touched.** `docs/status/public-api.txt`,
`docs/status/statement-lock.json`, `scripts/lean_build_targets.txt`,
`scripts/check_print_axioms.py`, `scripts/check_statement_freeze.py`,
`scripts/check_public_api.py` and `AISafetyAtlas.lean` are all byte-identical to
`origin/main`: nothing was relaxed to make the build pass.

Two `by ring` calls in the vendored debate cost proofs are left alone. Rewriting
them to `by ring_nf` to quiet an advisory would be a mistake: `ring` is
`first | ring1 | try_this ring_nf …`, so it *was* proving the goal through its
second branch while printing the suggestion. Upstream text that still compiles
does not get touched.

`check_statement_drift.py` now runs in `agent_gate.sh` as an advisory — on a
feature branch new theorems are the point — and takes `--fail-on-drift` for the
next migration, where the answer is supposed to be none.

## Owed back: the `deriving Fintype` workaround

`Mathlib.Tactic.DeriveFintype` does not elaborate at this Mathlib revision: the
instance it generates hands `Finset.mk` a `List.Nodup` proof where a
`Multiset.Nodup` one is wanted. It reproduces outside this repository in three
lines, and `DeriveFintype.lean` is byte-identical at `v4.33.0` and `v4.33.1`, so
the point release does not fix it.

Six `Fintype` instances are therefore written out by hand, with five
`inferInstanceAs` forwarders alongside them:

| File | Written instances |
|------|-------------------|
| `AISafetyAtlas/Examples/Oversight/JointObservation/Portfolio.lean` | `Principal`, `Exec`, `HazardIx`, `CandIx` |
| `AISafetyAtlas/Examples/Oversight/JointObservation/Procurement.lean` | `Principal`, `Exec` |

Each carries the reason in a comment above it. `decide` and `Finset.univ` behave
identically either way, so nothing downstream depends on the workaround — it is
a diff to revert, not a design. **To revert:** restore `deriving DecidableEq,
Fintype` on the six inductives and delete the written instances and the
comments; the forwarders stay.

## Records updated, and records deliberately left alone

`registry.yaml` carries a `build_environment` string per reproduction record —
111 of them. The split is not a judgement call: a record's `build_command` says
which build it describes.

- **100 in-tree**, built by `lake build …` in this checkout or by a reproduction
  script's `--in-tree` lane. All of them named the v4.31.0 environment and now
  name this one, because the whole tree was rebuilt and re-audited here — that
  is the claim the field makes.
- **11 external**, built by `scripts/reproduce_*.sh` against another project's
  own checkout and own toolchain, which did not move and were not re-run: eight
  Isabelle entries, debate **Path A** at `leanprover/lean4:v4.8.0`,
  `reproduce_chaitin.sh` (upstream `kolmogorov-complexity-lean@005ac4c8` pins
  `v4.31.0` with Mathlib `fabf563a…`, verified against the repository), and
  `reproduce_vnm.sh`. Rewriting any of those would have been a false claim about
  a build nobody ran.

Classifying on the shape of the environment string instead of on
`build_command` gets two of the 111 wrong in opposite directions: the Chaitin
record describes an upstream checkout that merely happens to pin the same Lean
release, and the vendored SocialChoiceLean record's command is
`lake build AISafetyAtlas`. `scripts/validate_registry.py` now refuses the whole
class: an in-tree record whose `build_environment` does not name the toolchain
in `lean-toolchain`, or which names a 40-hex revision `lake-manifest.json` does
not pin, is a gate failure. External records stay exempt, deliberately.

Six `version` fields named the pre-migration Mathlib and Foundation revisions
while the `build_environment` beside them named the new ones — the same record
contradicting itself. Those are corrected too.

## Reproduction lanes, re-run

Both in-tree lanes were re-run at the new pins:

- `scripts/reproduce_debate.sh --in-tree` — trust scan clean across 20 vendored
  Lean sources, 2742 jobs, and all six facade declarations
  (`completeness`, `soundness`, `correctness`, `alice_fast`, `bob_fast`,
  `vera_fast`) depend only on `[propext, Classical.choice, Quot.sound]`.
- `scripts/reproduce_foundation.sh` — `AISafetyAtlas.Logic` builds against the
  new Foundation pin, 1229 jobs.

That script had the old Foundation revision hard-coded in an `echo`, so it
printed a false pin while building the right one. It now reads the revision from
`lake-manifest.json`, which is the copy that cannot go stale.

The external lanes — Isabelle, debate Path A, vNM — were **not** re-run, because
they build other projects at other toolchains that did not move. See the previous
section.

## Where the ports now stand

Checked 2026-08-31, because the cheapest migration is one somebody else already
did:

| Repository | Branch | Toolchain | Tip |
|---|---|---|---|
| `google-deepmind/debate` | `main` | `v4.8.0` | `de3a6e500a`, 2024-10-08 |
| `LukaHobor/debate` | `port-lean-4.31` | `v4.31.0` | `dafe25df02`, unchanged since vendoring |
| `mbrcic/SocialChoiceLean` | `port/lean-4.31` | `v4.31.0` | `74f491bada` |
| `AlexeyMilovanov/kolmogorov-complexity-lean` | pinned rev | `v4.31.0` | `005ac4c81e` |
| `DrakeCaraker/dash-impossibility-lean` | `main` | `v4.29.0-rc8` | `97a8451f25` |

**Nothing upstream is on v4.33.0.** There was no port to copy, and this
repository's vendored trees are now the most advanced version of each of these
developments — which is a contribution owed upstream rather than an asset, and
a maintenance cost until it is made.
