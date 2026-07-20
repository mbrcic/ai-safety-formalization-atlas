# Reproduction — DeepMind doubly-efficient debate (LAND-DEBATE-001)

Path-A reproduction of the Lean 4 correctness proof of the doubly-efficient
debate protocol (Brown-Cohen–Irving–Piliouras 2023, *Scalable AI Safety via
Doubly-Efficient Debate*, [arXiv 2311.14125](https://arxiv.org/abs/2311.14125)).
This is a **possibility / scalable-oversight guarantee** — a live landscape
anchor dual to the survey's impossibility rows. It never counts toward headline
`EXACT`/`EQUIVALENT` coverage.

Task: [CT-7](../guide/contributor-tasks.md). Landscape record:
[`LAND-DEBATE-001`](../../landscape.yaml). Reproduction driver:
[`scripts/reproduce_debate.sh`](../../scripts/reproduce_debate.sh).

## Coordinates

| Field | Value |
|-------|-------|
| Repository | `github.com/google-deepmind/debate` |
| Revision | `de3a6e500ae1a65dfeea2f91ef519ebad9704be0` (single `main`, no release tag; last commit 2024-10-08) |
| Upstream toolchain | `leanprover/lean4:v4.8.0`, Mathlib `v4.8.0` |
| Module | `Debate/Correct.lean` |
| Theorems | `completeness`, `soundness`, `correctness` (paper Theorem 6.2) |
| License | Apache-2.0 |

## Why Path A (reproduce, not vendor)

Upstream pins Lean/Mathlib `v4.8.0`; the atlas is on `v4.31.0`. The version gap
(notably Mathlib probability/measure drift) makes a `require` into the 4.31 tree
impractical. So the development is **reproduced at its own toolchain from a
separate checkout** — the same discipline as the Chaitin (`reproduce_chaitin.sh`)
and Isabelle (`reproduce_isabelle.sh`) anchors — and carries **no atlas Lean
import surface** (`atlas_declaration: null`, `root_import: false`). A future
port-then-wrap (like the Gibbard–Satterthwaite `LAND-GS-002` facade) is deferred
until something downstream needs to build *on* debate.

## What the driver checks

`scripts/reproduce_debate.sh`:

1. fetches the pinned revision and asserts the exact commit hash;
2. asserts `completeness`, `soundness`, `correctness` are present in
   `Debate/Correct.lean`;
3. runs the strict-trust scan (no `sorry`, `admit`, `axiom`, `sorryAx`,
   `native_decide`, `implemented_by`, `@[extern` in upstream sources);
4. builds `Debate.Correct` at the upstream toolchain (`lake exe cache get` for
   Mathlib oleans, then `lake build`).

## Honest scope — upstream's own caveats

- **Correctness only.** Space complexity is not formalized.
- **Time counts oracle queries only** — not full computational cost.
- The **Lipschitz oracle machine** is defined slightly differently from the
  paper: a stronger variant.
- No AI-system reading follows from this record without a **separate reviewed
  bridge**. It is a machine-checked statement about the protocol model, not a
  claim about any deployed oversight scheme.
