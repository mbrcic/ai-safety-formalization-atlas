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

Path A is not superseded. It checks the upstream artifact; Path B checks the
atlas's copy of it. A port that silently broke something would still pass Path A,
which is exactly why the lane is kept.

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

The original record said a port-then-wrap was deferred "until something
downstream needs to build *on* debate". The port arrived first. Because the
atlas's Mathlib pin `v4.31.0` resolves to `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f`
— the exact commit the port pins — the two build closures are identical and the
development compiles in-tree unchanged.

What landed:

- **18 vendored modules** under `AISafetyAtlas/Upstream/Debate/`. Every atlas
  change is confined to the file header: `module`, `public import` at the atlas
  module path, one `@[expose] public section`, and a `set_option linter.*` block
  (the package builds with `warningAsError = true`; upstream does not). No
  statement, proof script, notation, or declaration name in any body is altered.
- **A facade**, `AISafetyAtlas.Oversight.Debate`, publishing six declarations:
  `completeness`, `soundness`, `correctness`, `alice_fast`, `bob_fast`,
  `vera_fast`. Path A only ever checked the correctness half; the
  query-complexity half — the *doubly efficient* part, and the reason the result
  is interesting for oversight — is now checked as well.
- **A worked model**, `AISafetyAtlas/Examples/Oversight/Debate.lean`. Upstream
  exhibits no oracle at all, so `every_oracle_lipschitz_zero` is proved here, not
  vendored: every stochastic oracle is 1-Lipschitz over a one-round debate. Without
  it the hypothesis `Debate.Lipschitz o t k` would be unwitnessed in the tree and
  the guarantees would be statements about a possibly empty hypothesis.

### Why the facade is off the root import

The vendored development declares roughly 157 names in the **root** namespace —
`count`, `close`, `final`, `trace`, `estimate`, `step`, `L`, `Correct` among
them. Re-exporting those through `import AISafetyAtlas` would put them in front
of every downstream user, so `AISafetyAtlas.Oversight.Debate` is imported on its
own, the contract `AISafetyAtlas.Explore` already keeps. `root_import` stays
`false` on the ledger row, which is what the registry validator independently
checks against the real import graph.

`scripts/check_print_axioms.py` walks the root closure, so it would not have
reached these theorems. Rather than leave a published declaration unaudited, the
script now takes an explicit `OFF_ROOT_FACADES` list and audits those facades
too — so the invariant "everything the ledger publishes is kernel-audited" holds
unchanged, and the six declarations are pinned in
[`docs/status/public-api.txt`](../status/public-api.txt) like any other.

### What the `--in-tree` driver checks

1. strict-trust scan over the vendored tree, the facade and the worked model
   (`axiom` matched in declaration position, so module prose cannot trip it and
   cannot hide a real `axiom` command either);
2. `lake build` of the vendored tree, the facade, and the example;
3. kernel `#print axioms` on all six facade declarations, asserting only
   `propext`, `Classical.choice`, `Quot.sound`.

Result (2026-08-20):

```
trust scan: no forbidden tokens in 20 vendored Lean sources
Build completed successfully (2710 jobs).
'AISafetyAtlas.Oversight.Debate.completeness' depends on axioms: [propext, Classical.choice, Quot.sound]
'AISafetyAtlas.Oversight.Debate.soundness'    depends on axioms: [propext, Classical.choice, Quot.sound]
'AISafetyAtlas.Oversight.Debate.correctness'  depends on axioms: [propext, Classical.choice, Quot.sound]
'AISafetyAtlas.Oversight.Debate.alice_fast'   depends on axioms: [propext, Classical.choice, Quot.sound]
'AISafetyAtlas.Oversight.Debate.bob_fast'     depends on axioms: [propext, Classical.choice, Quot.sound]
'AISafetyAtlas.Oversight.Debate.vera_fast'    depends on axioms: [propext, Classical.choice, Quot.sound]
debate in-tree check ok: 6 facade declarations depend only on [propext, Classical.choice, Quot.sound]
```

### Statement fidelity

The port is a toolchain migration only. Its `PORTING.md` diffed every declaration
signature against upstream and found exactly three differences, none a weakening:
`Vector` → `List.Vector` (a Mathlib namespace move), a renamed *local* helper in
`Prob/Chernoff.lean` that had collided with a new Mathlib name, and the removal
of a manual `Prob.ext_iff` now generated by `@[ext]`. `Debate/Correct.lean` is
byte-identical to upstream apart from the atlas header.

## Honest scope — upstream's own caveats

- **Correctness only.** Space complexity is not formalized.
- **Time counts oracle queries only** — not full computational cost.
- The **Lipschitz oracle machine** is defined slightly differently from the
  paper: a stronger variant.
- No AI-system reading follows from this record without a **separate reviewed
  bridge**. It is a machine-checked statement about the protocol model, not a
  claim about any deployed oversight scheme.
