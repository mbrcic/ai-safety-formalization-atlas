# Reproduction — DeepMind doubly-efficient debate (LAND-DEBATE-001)

Reproduction of the Lean 4 correctness proof of the doubly-efficient debate
protocol (Brown-Cohen–Irving–Piliouras 2023, *Scalable AI Safety via
Doubly-Efficient Debate*, [arXiv 2311.14125](https://arxiv.org/abs/2311.14125)).
This is a **possibility / scalable-oversight guarantee** — a live landscape
anchor dual to the survey's impossibility rows. It never counts toward headline
`EXACT`/`EQUIVALENT` coverage.

Task: [CT-7](../guide/contributor-tasks.md). Landscape record:
[`LAND-DEBATE-001`](../../registry.yaml). Reproduction driver:
[`scripts/reproduce_debate.sh`](../../scripts/reproduce_debate.sh). Vendoring
detail: [`vendor/debate/PROVENANCE.md`](../../vendor/debate/PROVENANCE.md).

Two lanes, both live:

| Lane | What it checks | Driver |
|---|---|---|
| **Path A** (2026-07-20) | upstream, at its own toolchain, from a separate checkout | `scripts/reproduce_debate.sh` |
| **Path B** (2026-08-20) | the Lean 4.31 port, vendored inside the atlas build closure, with an atlas import surface | `scripts/reproduce_debate.sh --in-tree` |

Path A is not superseded: a port that silently broke something would still pass
it, which is exactly why the lane is kept.

## Coordinates

| Field | Path A | Path B |
|-------|--------|--------|
| Repository | `github.com/google-deepmind/debate` | `github.com/LukaHobor/debate`, branch `port-lean-4.31` |
| Revision | `de3a6e500ae1a65dfeea2f91ef519ebad9704be0` (single `main`, no release tag; last commit 2024-10-08) | `dafe25df02300c0ebecf436aab32e953006cb0a1` |
| Toolchain | `leanprover/lean4:v4.8.0`, Mathlib `v4.8.0` | `leanprover/lean4:v4.31.0`, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Module | `Debate/Correct.lean` | `AISafetyAtlas.Upstream.Debate.Correct` |
| Theorems | `completeness`, `soundness`, `correctness` (paper Theorem 6.2) | those three, plus `alice_fast`, `bob_fast`, `vera_fast` |
| Atlas surface | none | `AISafetyAtlas.Oversight.Debate` |
| License | Apache-2.0 | Apache-2.0 (unchanged) |

## Path A — reproduce at the upstream toolchain

`scripts/reproduce_debate.sh`:

1. fetches the pinned revision and asserts the exact commit hash;
2. asserts `completeness`, `soundness`, `correctness` are present in
   `Debate/Correct.lean`;
3. runs the strict-trust scan (no `sorry`, `admit`, `axiom`, `sorryAx`,
   `native_decide`, `implemented_by`, `@[extern` in upstream sources);
4. builds `Debate.Correct` at the upstream toolchain (`lake exe cache get` for
   Mathlib oleans, then `lake build`).

Result (2026-07-20): clean build, `Debate.Correct`, 1721/1721 targets; trust scan
clean across 19 upstream Lean sources.

## Path B — vendored into the atlas 4.31 tree

The original record deferred a port-then-wrap "until something downstream needs
to build *on* debate"; the port arrived first. The atlas's Mathlib pin resolves
to the exact commit the port pins, so the two build closures are identical and
the development compiles in-tree unchanged. Pins, the three header adaptations
and statement fidelity are in
[`vendor/debate/PROVENANCE.md`](../../vendor/debate/PROVENANCE.md).

What landed: 18 vendored modules under `AISafetyAtlas/Upstream/Debate/`; a
facade, `AISafetyAtlas.Oversight.Debate`, publishing six declarations — Path A
only ever checked the correctness half, and the query-complexity half is the
*doubly efficient* part; and a worked model,
`AISafetyAtlas/Examples/Oversight/Debate.lean`. Upstream exhibits no oracle at
all, so `every_oracle_lipschitz_zero` is proved there rather than vendored:
without it `Debate.Lipschitz o t k` would be unwitnessed in the tree and the
guarantees would be statements about a possibly empty hypothesis.

The facade is deliberately off the root import — the vendored tree declares
roughly 157 root-namespace names — so `root_import` stays `false`, and
`scripts/check_print_axioms.py` reaches it through an explicit
`OFF_ROOT_FACADES` list instead of through the root closure. The facade's module
docstring carries the reasoning.

### What the `--in-tree` driver checks

1. strict-trust scan over the vendored tree, the facade and the worked model
   (`axiom` matched in declaration position, so module prose cannot trip it and
   cannot hide a real `axiom` command either);
2. `lake build` of the vendored tree, the facade, and the example;
3. kernel `#print axioms` on all six facade declarations, asserting only
   `propext`, `Classical.choice`, `Quot.sound`.

Result (2026-08-20): trust scan clean across 20 vendored Lean sources; build
completed (2710 jobs); all six facade declarations depend only on `propext`,
`Classical.choice`, `Quot.sound`.

## Honest scope — upstream's own caveats

- **Correctness only.** Space complexity is not formalized.
- **Time counts oracle queries only** — not full computational cost.
- The **Lipschitz oracle machine** is defined slightly differently from the
  paper: a stronger variant.
- No AI-system reading follows from this record without a **separate reviewed
  bridge**. It is a machine-checked statement about the protocol model, not a
  claim about any deployed oversight scheme.
