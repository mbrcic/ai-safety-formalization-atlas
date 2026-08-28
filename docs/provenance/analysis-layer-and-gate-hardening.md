# The analysis layer and the gate hardening — initial state, final state, and how to reproduce

**What this file is.** A reproduction record, not a changelog. For each thing the
tree now asserts that it did not assert before, it gives the state the tree was
in, the state it is in, the reason the change is what it is, and the command that
checks the final state. Read it to re-derive the current tree, not to follow the
path taken to it. The path is in `git log` and is deliberately not repeated here:
two of the changes below reverse an earlier decision, and a reader reproducing
the tree needs the destination, not the detour.

## 1. `AISafetyAtlas.Analysis.PolynomialGenericity` — new

| | |
|---|---|
| **Initial** | No module. Genericity arguments in `Causal` asserted almost-everywhere non-vanishing without a proof of it. |
| **Final** | A nonzero real polynomial in finitely many variables is nonzero almost everywhere, for any product of atomless measures — hence for Lebesgue and for any additive Haar measure. |

Declarations: `AISafetyAtlas.Analysis.ae_eval_ne_zero_pi`,
`AISafetyAtlas.Analysis.measure_setOf_eval_eq_zero_pi`,
`AISafetyAtlas.Analysis.ae_eval_ne_zero`,
`AISafetyAtlas.Analysis.ae_eval_ne_zero_fintype`,
`AISafetyAtlas.Analysis.volume_setOf_eval_eq_zero`,
`AISafetyAtlas.Analysis.ae_eval_ne_zero_addHaar`.

**Why this generality and no more.** The statement is at the generality
genericity arguments actually use — a product of atomless measures — rather than
the widest form provable. Mathlib at the pinned revision carries only the
finite-grid sibling `MvPolynomial.schwartz_zippel_totalDegree`, so this is a
build rather than a reuse, and it is written domain-neutral to be lifted
upstream.

**Verify:** `lake build AISafetyAtlas.Examples.Analysis.PolynomialGenericity`

## 2. `AISafetyAtlas.Analysis.Semialgebraic` — moved and extended

| | |
|---|---|
| **Initial** | `AISafetyAtlas.Causal.Semialgebraic`, carrying basic sign conditions only. |
| **Final** | `AISafetyAtlas.Analysis.Semialgebraic`, closed under the Boolean operations. |

Added: `AISafetyAtlas.Analysis.IsSemialgebraic.union`, `.inter`, `.compl`,
`.sdiff`, `AISafetyAtlas.Analysis.isSemialgebraic_biUnion`,
`AISafetyAtlas.Analysis.isSemialgebraic_biInter`,
`AISafetyAtlas.Analysis.isSemialgebraic_compl_basic`, and the closed-box lemmas
with their compactness.

**Why it moved.** A semialgebraic set is not a causal notion. Living under
`Causal` made the cluster boundary claim a piece of real algebraic geometry, and
made the generated causal dependency view report it as causal substrate.
`AISafetyAtlas.Causal.ParameterChart` remains its consumer, for MAIS-A2
`prob:exact`; the dependency edge is unchanged and only its direction across the
cluster boundary is now stated correctly.

**Verify:** `lake build AISafetyAtlas.Examples.Analysis.Semialgebraic`

## 3. `AISafetyAtlas.InformationTheory.PrefixCode` — moved

| | |
|---|---|
| **Initial** | Under `Causal`. |
| **Final** | Under `InformationTheory`. |

Same reason as §2: a prefix-free code is source coding, not a causal notion.
`AISafetyAtlas.Causal.EffectiveGenericity` remains its consumer, for MAIS-O24's
construction-time clause.

**Verify:** `lake build AISafetyAtlas.Examples.InformationTheory.PrefixCode`

## 4. `Causal.Query` and `Causal.Decision` — two expectation bounds

| | |
|---|---|
| **Initial** | Expectation manipulations inlined at each use site. |
| **Final** | `AISafetyAtlas.Causal.pmfExpect_add`, `AISafetyAtlas.Causal.le_pmfExpect`, `AISafetyAtlas.Causal.exactAnalystRisk_empty`, `AISafetyAtlas.Causal.inIdentifiedSet_mono`, `AISafetyAtlas.Causal.one_le_modelError_add`. |

## 5. Axiom audit scope — widened, and the scope is now itself checked

| | |
|---|---|
| **Initial** | `scripts/check_print_axioms.py` covered *headline* atlas theorems. Which declarations counted as headline was a description in prose, and could drift from the tree without any gate noticing. |
| **Final** | Every public theorem and lemma in the facade closure, **and** every public theorem, lemma and definition in the off-root build targets and their import closure, is checked axiom-clean up to the three standard classical axioms. The same script asserts that no `.lean` under `AISafetyAtlas/` sits outside that set. |

The second half is the point: the audit's coverage is a checked property rather
than a claim, so it cannot silently shrink as the tree grows. `docs/guide/methodology.md`
states the same scope, and the two are meant to be read together.

**Verify:** `python3 scripts/check_print_axioms.py`

## 6. Independent kernel re-verification — release tags and manual runs only

| | |
|---|---|
| **Initial** | No kernel replay. `#print axioms` was the strongest available check. |
| **Final** | `lake env leanchecker` replays every module the atlas compiles, on release tags and `workflow_dispatch` only. |

**Why it is gated rather than continuous.** The replay is expensive: measured on
a warm local tree, replaying the atlas's modules ran past fifteen minutes without
finishing, against roughly forty seconds for the axiom check. Running it per pull
request would stall development for a guarantee that is a property of a release.
Two facts a reproducer needs: the tool ships with the toolchain from Lean
v4.28.0 — the separate `leanprover/lean4checker` repository is archived and must
not be cloned — and the scope is the atlas's own oleans under
`.lake/build/lib/lean`, because passing no module argument walks Lean core and
Mathlib as well.

**Verify:** push a `v*` tag, or dispatch the `CI` workflow manually.

## 7. Statement freeze — a repository rule

| | |
|---|---|
| **Initial** | Nothing stopped a proof agent from closing a goal by editing the goal. |
| **Final** | `AGENTS.md` §Statement freeze: once a statement carries a fidelity grade or a pinned source, its binders, hypotheses, quantifiers, conclusion and axiom set are frozen; proof bodies are not. |

The reason is that the kernel cannot see this failure — every fidelity defect
this repository has shipped and later fixed was in a definition or a statement,
and every one compiled.

## 8. No rows are held out

| | |
|---|---|
| **Initial** | Nothing reserved. |
| **Final** | Nothing reserved. |

Recorded because the intermediate state was different and a reader may encounter
it in the history: ten registry rows were briefly reserved as a control group for
a measurement of whether the accumulated corpus makes new results cheaper, and
that reservation was withdrawn. **Every registry row is free to formalize.** No
gate, file or docstring in this repository excludes any row, and the reservation
should not be reinstated from the commit that created it.
