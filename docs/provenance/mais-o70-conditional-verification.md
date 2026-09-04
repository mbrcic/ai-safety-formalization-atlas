# MAIS-O70: a conditional formal verification, and its exact boundaries

This branch is prepared for publication as a **conditional formal verification** of the MAIS
issue #3 candidate solution to MAIS-O70. This file is the release note: what is
claimed, what is assumed, what a reviewer should read, and in what order.

It is written to stand alone: everything it refers to is in this repository.

---

## 1. The claim, stated once

**A Lean-verified derivation of the candidate's P1, P2 and P3 from two named
hypotheses.** All three of the printed problem's clauses are inhabited in Lean,
each conditional on `EigenvalueLawStatement` and `O70ExactLocalPairsExist` and
nothing else, throughout in the ball-volume normalization. The restatement of P2
in the problem statement's *primary*, zeta-pole normalization additionally
assumes `O70ZetaPoleBridge`.

**None of the three hypotheses is proved in the atlas, and the atlas holds no
unconditional inhabitant of any of them.** `CONJ-026` is `OPEN`, in
[`conjectures.yaml`](../../conjectures.yaml), and this branch does not change
that. Nothing here is a claim that MAIS-O70 has been solved, resolved or fully
formally verified; what is verified is an implication, together with an
independently proved unconditional fragment listed in §3.

---

## 2. The conditional results, by declaration

Every name below is a `public theorem` and resolves in
`docs/status/declaration-index.json`.

| clause | declaration | binders | file |
|---|---|---|---|
| P1 — the pair depends only on the ranks | `AISafetyAtlas.Conjectures.MAIS.o70DependsOnRanksOnly_of_frontiers` | eigenvalue law, exact-local | [`Conjectures/MAIS/O70Proof.lean`](../../AISafetyAtlas/Conjectures/MAIS/O70Proof.lean) |
| P2 — the resulting table | `AISafetyAtlas.Conjectures.MAIS.isO70RankTable_o70Pair` | eigenvalue law, exact-local | [same](../../AISafetyAtlas/Conjectures/MAIS/O70Proof.lean) |
| P3 — the minimising strata, at the germs | `AISafetyAtlas.Conjectures.MAIS.isO70MinimizerCharacterization_o70Minimizers` | eigenvalue law, exact-local | [same](../../AISafetyAtlas/Conjectures/MAIS/O70Proof.lean) |
| P2 in print's primary normalization | `AISafetyAtlas.Conjectures.MAIS.hasZetaPoleOrder_o70Pair` | eigenvalue law, exact-local, **zeta bridge** | [same](../../AISafetyAtlas/Conjectures/MAIS/O70Proof.lean) |

The source-facing correctness propositions registered positionally for P1--P3 are —
`AISafetyAtlas.Conjectures.MAIS.O70DependsOnRanksOnly`,
`AISafetyAtlas.Conjectures.MAIS.IsO70RankTable` and
`AISafetyAtlas.Conjectures.MAIS.IsO70AWValueStratumTable` — and are stated in
[`Conjectures/MAIS/O70.lean`](../../AISafetyAtlas/Conjectures/MAIS/O70.lean),
together with the candidate answers `o70Pair` and `o70Minimizers` they are
applied to. The conditional P3 theorem additionally inhabits
`IsO70MinimizerCharacterization o70Minimizers`, which connects that positional
answer to the actual germs; this germ-level semantic predicate is complementary
to, rather than a replacement for, the ledger's positional P3 predicate.

One reading caution, recorded in its own docstring and repeated because the word
invites more than it carries: `IsO70MinimizerCharacterization` probes a stratum
set only at strata realized by an actual factorization with positive dimensions,
so it does not pin the set — that is
`AISafetyAtlas.Conjectures.MAIS.IsO70AWValueStratumTable`'s job, and the two are
complementary. It also takes `HasExactLocalPair` in hypothesis position only, so
were exact pairs to exist nowhere, every set would satisfy it vacuously. The
anti-vacuity witness — under the two hypotheses, `Set.univ` does *not* satisfy it
— is at the end of
[`Examples/Conjectures/MAIS/O70Proof.lean`](../../AISafetyAtlas/Examples/Conjectures/MAIS/O70Proof.lean).

---

## 3. What is unconditional

These carry no frontier hypothesis at all.

| what | declaration |
|---|---|
| P3's arithmetic half: the printed Aoyagi–Watanabe value is the attained minimum of the candidate table over the admissible strata | `AISafetyAtlas.Conjectures.MAIS.o70_fiber_minimum_correct` |
| the realisation theorem: every feasible rank stratum is realised by an actual factorization of the given truth matrix | `AISafetyAtlas.SingularLearning.exists_factorization_of_feasible` |
| the local pair of the first *singular* germ of the family, `x²y²`, by an elementary one-dimensional split | `AISafetyAtlas.SingularLearning.hasLocalVolumeOrder_residualGerm_one` |
| nondegeneracy: the O70 loss vanishes on no neighbourhood of any point, at every positive shape and every `(C, A, B)`, with no factorization hypothesis | `AISafetyAtlas.Conjectures.MAIS.not_eventually_rrrLossCoords_eq_zero_of_pos` |

Also unconditional, and listed in full in the manifest: the minimiser-set
characterisation *against the table*
(`AISafetyAtlas.Conjectures.MAIS.o70_aw_value_strata_correct`), the bounds
carried to actual matrices
(`AISafetyAtlas.Conjectures.MAIS.awLambda_le_of_factorization`,
`AISafetyAtlas.Conjectures.MAIS.awLambda_le_on_fiber`), Theorem 5.1 at every
feasible stratum (`AISafetyAtlas.SingularLearning.isEliminationChart_of_feasible`),
and the whole localization and Tauberian chain.

These are claims about the *candidate table* and about the analytic machinery.
None of them is a claim about the model's actual local learning coefficients.

---

## 4. The three frontier hypotheses

Full statements, match grades, risk assessments, stress evidence and
per-declaration consumer tables are in
[`o70-frontier-manifest.md`](o70-frontier-manifest.md). One line each here.

* **`O70-EIGEN-LAW`** — `AISafetyAtlas.SingularLearning.EigenvalueLawStatement`,
  in [`SingularLearning/EigenvalueLaw.lean`](../../AISafetyAtlas/SingularLearning/EigenvalueLaw.lean):
  the real-Wishart density together with the eigenvalue Jacobian, which the
  candidate **cites** to Muirhead Theorems 3.2.1 and 3.2.17 after James (1954).
  It is the analytic core of the residual-germ theorem and every conditional
  result above stands on it.
* **`O70-EXACT-LOCAL`** — `AISafetyAtlas.Conjectures.MAIS.O70ExactLocalPairsExist`,
  in [`Conjectures/MAIS/O70.lean`](../../AISafetyAtlas/Conjectures/MAIS/O70.lean):
  the value-free claim that *some* exact local pair exists at these germs, which
  the candidate **cites** as the single non-elementary step of its derivation.
  It is what upgrades the two-sided volume *order* to print's exact table.
* **`O70-ZETA-BRIDGE`** — `AISafetyAtlas.Conjectures.MAIS.O70ZetaPoleBridge`, same
  file: that at the O70 germs the ball-volume pair is the zeta threshold and pole
  order. This one is **not** a citation of the candidate's. It is the gap between
  the atlas and the **problem statement's own primary definition** — `MAIS-A6.tex`
  `def:local` fixes the pair by zeta poles and only afterwards calls the volume
  form equivalent. Print asserts it; neither the candidate nor the atlas proves it
  for print's sharp ball. Only `hasZetaPoleOrder_o70Pair` consumes it.

A reader who groups all three together will misread the third.

**Consumers, measured on this tree** over `AISafetyAtlas/` with `Examples/`
excluded (`grep -rn ": EigenvalueLawStatement)" --include=*.lean AISafetyAtlas`
and the two analogues): seventeen declarations carry the eigenvalue law, six
carry the exact-local hypothesis, one carries the bridge. The manifest tabulates
them and books the three-binder theorem `hasZetaPoleOrder_o70Pair` under the
bridge only, so its per-frontier tables list sixteen and five.

Each frontier has a **frozen surface** — `eigenvalueLawStatement_iff`,
`o70ExactLocalPairsExist_iff`, `o70ZetaPoleBridge_iff` — an `Iff.rfl` that writes
out every quantifier with `HasExactLocalPair` and `HasZetaPoleOrder` expanded
rather than named, so the degenerate branch, the countable exceptional set of
radii, the analyticity clause and the sign of the pole order sit on the lock
rather than behind it. All three are registered in
`scripts/check_statement_freeze.py`.

---

## 5. Source pins and fidelity

Grading artifacts, from [`registry.yaml`](../../registry.yaml)'s source catalog.
All three are pinned at MAIS repository commit
`9dd29f8bf5ccd1e7701e300039b09ed4096b6516`, the same revision
[`mais-source-pin.md`](mais-source-pin.md) fixes for the other MAIS rows.

| id | artifact | sha256 | read |
|---|---|---|---|
| `mais-a6-2026` | `agendas/A6/MAIS-A6.tex` — the statement source (`prob:calibration`, with `def:local`, `thm:aw`, `rem:conventions`) | `3da2eda1b1fa9633d09e48c4ce3bab34bc22aeea4bfc72eeb04b6b919b1c1d3e` | 2026-09-03 |
| `mais-o70-2026` | `open-problems/MAIS-O70.md` — the one-page restatement | `69a47687da280365ac2023ef4b69d571b472ccae5543251f00058d3683c7a47e` | 2026-09-03 |
| `mais-issue-3-2026` | MAIS issue #3 (Sneiderman, 2026), the candidate — hash is of the **attached PDF**, which carries the mathematics, not of the issue page | `405c8cb324884607f3e827cdd915d8ac10ce01b969a7739616474b3fb8401cbe` | 2026-09-02 |

`mais-source-pin.md` covers agendas A2 and A3 and issues #4, #6, #7, #8, #9 and
#30; it does not yet carry the A6 row, so the three pins above are held in
`registry.yaml` alone. Both agendas are AI-written and not human-peer-reviewed,
and the candidate is not peer-reviewed; the ledger notes say so.

**Fidelity grade of `CONJ-026`**, from `conjectures.yaml`: `source_scope: Same`,
`source_fidelity: DetermineProblem`, `status: OPEN`, graded declaration
`AISafetyAtlas.Conjectures.MAIS.IsO70RankTable`. Three printed clauses, three
graded propositions, quantified as print quantifies them. Two normalization
decisions are recorded there rather than hidden: the pair is fixed by the
ball-volume asymptotic `eq:volume` rather than by `def:local`'s primary zeta
poles — that substitution is `O70ZetaPoleBridge` — and `HasExactLocalPair` asks
for exact asymptotics at all but countably many small radii, matching
`def:local`'s assertion that the pair does not depend on the radius while making
no claim about the constant.

Two interpretive readings sit under those decisions: the **radius quantifier**
(generic-radius exact, `HasExactLocalPair` as written) and the **P3 reading**
(the fiber minimum). Both are drafts. See §8.

---

## 6. Reproduction

Every command is run from the repository root. The Lean-free checks are first,
so a reviewer without a toolchain can still run most of this.

**Arithmetic, no Lean, no network.**

```
python3 scripts/reproduce_o70_table.py
```
Ends with `PASS: every check above succeeded.` after eight numbered checks —
among them the candidate's five-branch residual table against its own
discrete-minimisation form on 68921 triples, the minimum over strata against
Aoyagi–Watanabe on 657 tuples, and print's own `N=M=H=2` worked example. It
re-derives everything from the *printed* formulas and uses none of the
candidate's scripts, which are not public. **It establishes nothing about any
germ**: it is arithmetic about the candidate's table, and it is not evidence for
any frontier.

```
python3 scripts/reproduce_eigenvalue_law_probe.py
```
Stdlib only, deterministically seeded. Fifteen checks, ending with `PASS: every
check above succeeded.` At `k = 1` it is exact and pins `Z = π^(d/2)/Γ(d/2)`
constant across five `(T, ρ)` at `d ∈ {1,2,3,5}`; at `k = 2` it is Monte-Carlo
and measures its own power — the ratio is constant to about `10⁻³` with the
Vandermonde and moves by about `0.26` with it deleted. It is a **falsification
attempt on `O70-EIGEN-LAW` that failed to falsify**, over `k ∈ {1,2}` and
`d ≤ 5`. It is **not** a proof and **not** an inhabitant; passing does not make
the frontier true, and it bears on neither of the other two frontiers.

**Ledger, prose and shape checks.**

```
./scripts/agent_gate.sh
```
`check_scope_witnesses` and `check_statement_drift` are advisory and may print
review work. Every blocking stage must finish green. In particular,
`check_migration_adjudicated` recognizes branches descending from the completed
v4.33.0 migration, so ordinary post-migration statements do not rewrite that
historical human countersignature; a new toolchain move still fails until it has
its own adjudication.

**Lean.**

```
lake build
xargs lake build < scripts/lean_build_targets.txt
python3 scripts/check_print_axioms.py
python3 scripts/check_audit_coverage.py
lake exe axiom-audit --root AISafetyAtlas --modules-from AISafetyAtlas
```
The second line is not optional: the atlas root does not transitively import the
whole library, and everything under `AISafetyAtlas/Conjectures` is off-root. The
file names 199 explicit targets, of which the singular-learning layer and the two
O70 modules are the new ones. The three axiom stages are three independent
implementations of one question — a generated `#print axioms` harness, an
environment walk, and an upstream tool this repository did not write — and each
asserts that every audited declaration depends only on
`{propext, Classical.choice, Quot.sound}`. No declaration count is quoted for
this branch, because it was not measured on this tree; the recorded figure at
`origin/main` and the v4.33.0 pin is 2847, in
[`toolchain-v4330-migration.md`](toolchain-v4330-migration.md), and this branch
adds 74 modules.

An axiom audit reports the *binders* a theorem carries. It does not, and cannot,
report whether a binder's proposition is satisfiable. See §8.

---

## 7. A reviewer's reading order

The branch is 107 files against `origin/main`: 74 new Lean modules, 3 modified,
plus ledgers, generated views and two reproduction scripts. Read it in five
layers. The generated map of the whole layer is
[`singularlearning-dependency-graph.md`](../status/singularlearning-dependency-graph.md);
the layer's own overview docstring, which says in as many words what is still
missing, is [`AISafetyAtlas/SingularLearning.lean`](../../AISafetyAtlas/SingularLearning.lean).

1. **Foundations — start here.**
   [`SingularLearning/LocalPair.lean`](../../AISafetyAtlas/SingularLearning/LocalPair.lean)
   defines `HasExactLocalPair` and `HasLocalVolumeOrder`, the two objects
   everything else is about;
   [`Loss.lean`](../../AISafetyAtlas/SingularLearning/Loss.lean) is print's
   Gaussian-expectation loss `rrrLoss` (the Frobenius form is derived, not
   substituted) and [`Coordinates.lean`](../../AISafetyAtlas/SingularLearning/Coordinates.lean)
   transports the parameter space to Euclidean coordinates by a reindexing proved
   measure-preserving, so no Jacobian is absorbed silently.
   [`AoyagiWatanabe.lean`](../../AISafetyAtlas/SingularLearning/AoyagiWatanabe.lean)
   transcribes `thm:aw` as arithmetic — `awLambda`, `awMultiplicity` — and
   nothing more.
2. **Reduction and chart.**
   [`OrbitNormalForm.lean`](../../AISafetyAtlas/SingularLearning/OrbitNormalForm.lean)
   (Lemma 3.2: the orbit of a factorization is its three ranks) and
   [`RankRealization.lean`](../../AISafetyAtlas/SingularLearning/RankRealization.lean)
   (the converse: every feasible stratum is realised). Then Theorem 5.1, stated
   in [`EliminationChart.lean`](../../AISafetyAtlas/SingularLearning/EliminationChart.lean)
   and assembled at a general stratum in
   [`ChartAssembly.lean`](../../AISafetyAtlas/SingularLearning/ChartAssembly.lean).
3. **Chamber analysis — the heaviest layer.**
   [`ChamberIntegral.lean`](../../AISafetyAtlas/SingularLearning/ChamberIntegral.lean)
   is the candidate's Appendix A end to end and is the largest module on the
   branch; [`EigenvalueLaw.lean`](../../AISafetyAtlas/SingularLearning/EigenvalueLaw.lean)
   is where the frontier is stated, frozen, and given its four proved anchors;
   [`ResidualLaplace.lean`](../../AISafetyAtlas/SingularLearning/ResidualLaplace.lean)
   is where it is spent. The Abelian/Tauberian bridge that turns a Laplace
   transform back into a sublevel volume is
   [`Tauberian.lean`](../../AISafetyAtlas/SingularLearning/Tauberian.lean) and
   `TauberianLog.lean`, and
   [`ResidualScalar.lean`](../../AISafetyAtlas/SingularLearning/ResidualScalar.lean)
   is the one germ done without any of it.
4. **O70 assembly.**
   [`Conjectures/MAIS/O70.lean`](../../AISafetyAtlas/Conjectures/MAIS/O70.lean) —
   statements, candidate answers, the three frontier definitions and their frozen
   surfaces — then
   [`O70Proof.lean`](../../AISafetyAtlas/Conjectures/MAIS/O70Proof.lean), which is
   print's section 10 in order and ends with the four theorems of §2.
   [`SingularLearning/ZetaPair.lean`](../../AISafetyAtlas/SingularLearning/ZetaPair.lean)
   is short and worth reading in full: it holds print's primary definition, the
   candidate's weaker sharp-ball result, and a recorded counterexample, and it
   claims nothing.
5. **Examples and provenance.**
   [`Examples/Conjectures/MAIS/O70.lean`](../../AISafetyAtlas/Examples/Conjectures/MAIS/O70.lean)
   pins the table at small shapes;
   [`Examples/Conjectures/MAIS/O70Proof.lean`](../../AISafetyAtlas/Examples/Conjectures/MAIS/O70Proof.lean)
   carries the semantic instances, the cross-check of the conditional chain
   against the unconditional `x²y²` germ, and the anti-vacuity witness. Then the
   [frontier manifest](o70-frontier-manifest.md), and this file.

---

## 8. Known limitations

Stated plainly, because a conditional verification is only as useful as its
boundary is legible.

* **One primary citation remains unpinned.** Muirhead (`O70-EIGEN-LAW`) is a
  copyrighted monograph nobody in this review opened, so the candidate's theorem
  numbers remain unchecked. Greenblatt, Lin and both versions of `[lau2023]` are
  now bibliographically identified and SHA-256 pinned in the frontier manifest;
  their PDFs live in the sibling evidence store and are not distributed by this
  repository. Watanabe (2009), to which `[lau2023]` delegates the continuation
  and volume results, also remains unpinned and its hypotheses were not checked.
* **Nothing in the repository establishes that a frontier proposition is
  satisfiable, and no check can.** The statement freeze locks the *surface* of
  each hypothesis; the axiom stages report the *binders* a theorem carries.
  Neither says the antecedent can be inhabited. The frontier gate requires an
  unconditional stress artifact for each row, but those artifacts do different
  jobs: a numerical attack, a cheap-branch exclusion, or a witness that the
  conclusion is meaningful outside the frontier. Passing it is explicitly not a
  satisfiability proof. A frontier that is false would make every theorem standing
  on it unapplicable rather than merely conditional, and the mechanical gates can
  still all stay green. That is not hypothetical — see the next item.
* **The general form of the zeta bridge is false, which is why the one stated
  here is narrow.** Quantified over every germ the substitution fails, because
  `HasExactLocalPair` constrains only the leading behaviour of the sublevel
  volume and a logarithmic correction turns the pole into a branch point. What
  was missing is the hypothesis print itself carries: a nonnegative
  *real-analytic* `K`. The narrow form now on file is quantified only at the O70
  germs, which are polynomial and so satisfy that hypothesis. The defect was in a
  quantifier rather than in a proof, so no build failed on it. Narrowing removed
  a known-false region; it produced no evidence that what remains holds. The
  counterexample is recorded in `ZetaPair.lean`, and its `ε → 0` half is
  machine-checked in
  [`Examples/SingularLearning/ZetaPair.lean`](../../AISafetyAtlas/Examples/SingularLearning/ZetaPair.lean);
  the branch-point half is prose and is not formalized.
* **The two fidelity adjudications await a human countersign.** The radius
  quantifier and the P3 reading (§5) were drafted by an agent against
  `MAIS-A6.tex` read verbatim. The project's rule is that agents draft and a
  human adjudicates against print, and neither verdict has been signed. Any grade
  that depends on them inherits that provisional status. Reversing either would
  require rewriting the Lean statements it governs before any grade attached to
  them could stand — it would not falsify a proved theorem, but it would change
  what the proved theorem is about.
* **Evidence is asymmetric across the three frontiers.** `O70-EIGEN-LAW` has four
  proved anchors and a probe that could have falsified it and did not;
  `O70-EXACT-LOCAL` has only a negative result — its cheap `(0,1)` branch is
  closed off everywhere, unconditionally — and no positive evidence at all;
  `O70-ZETA-BRIDGE` has no O70 anchor, no probe and no inhabitant. The atlas now
  proves `HasZetaPoleOrder` for the unrelated quadratic germ `x₀²`, showing only
  that the conclusion is meaningful somewhere; it still proves neither
  `HasZetaPoleOrder` nor `HasZetaRealAxisOrder` at an O70 germ. None of these
  artifacts inhabits a frontier proposition.
