# Doubly-efficient debate provenance (vendored)

| Field | Value |
|---|---|
| Upstream | https://github.com/google-deepmind/debate |
| Upstream revision | `de3a6e500ae1a65dfeea2f91ef519ebad9704be0` (single `main`, no release tag; last commit 2024-10-08) |
| Fork / port | https://github.com/LukaHobor/debate branch `port-lean-4.31` |
| Pin revision | `dafe25df02300c0ebecf436aab32e953006cb0a1` (2026-08-20) |
| License | Apache-2.0 (upstream `LICENSE`; text at repository root `LICENSE`) |
| Original toolchain | `leanprover/lean4:v4.8.0`, Mathlib `v4.8.0` |
| Port toolchain | `leanprover/lean4:v4.31.0`, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| Principal declarations | `completeness`, `soundness`, `correctness` (root namespace) |
| Atlas facade | `AISafetyAtlas.Oversight.Debate.{completeness,soundness,correctness,alice_fast,bob_fast,vera_fast}` |
| Landscape record | `LAND-DEBATE-001` |
| Paper | Brown-Cohen, Irving & Piliouras, *Scalable AI Safety via Doubly-Efficient Debate*, [arXiv 2311.14125](https://arxiv.org/abs/2311.14125), Theorem 6.2 |
| Scope | The whole upstream development (`Debate/`, `Comp/`, `Prob/`, `Misc/`). Nothing dropped. |

The atlas pins Mathlib as `rev = "v4.31.0"`, which resolves to
`fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` in `lake-manifest.json` — the exact
commit the port pins. The two build closures are therefore identical, which is
what makes vendoring possible at all; see "Why this is now Path B" below.

## Packaging note — no duplicate source tree

Unlike `vendor/SocialChoiceLean/`, this directory holds **no** copy of the
sources. The build-participating tree under
[`AISafetyAtlas/Upstream/Debate/`](../../AISafetyAtlas/Upstream/Debate/) *is* the
port, file for file, with only a mechanical header rewrite. A second copy here
would add nothing but a place for the two to drift apart, so the ledger keeps
the mapping instead of the bytes.

There is no separate `Debate` Lake library and no `require` on this directory in
`lakefile.toml`. The modules are part of the `AISafetyAtlas` Lake library.

## File mapping

Upstream `Debate/X.lean` flattens into the vendored directory root; the other
three source directories keep their names.

| Port path | Atlas module |
|---|---|
| `Debate.lean` | `AISafetyAtlas.Upstream.Debate` |
| `Debate/Protocol.lean` | `AISafetyAtlas.Upstream.Debate.Protocol` |
| `Debate/Details.lean` | `AISafetyAtlas.Upstream.Debate.Details` |
| `Debate/Cost.lean` | `AISafetyAtlas.Upstream.Debate.Cost` |
| `Debate/Correct.lean` | `AISafetyAtlas.Upstream.Debate.Correct` |
| `Comp/{Oracle,Defs,Basic}.lean` | `AISafetyAtlas.Upstream.Debate.Comp.*` |
| `Prob/{Defs,Basics,Arith,Cond,Estimate,Bernoulli,Chernoff,Pmf}.lean` | `AISafetyAtlas.Upstream.Debate.Prob.*` |
| `Misc/{Finset,If}.lean` | `AISafetyAtlas.Upstream.Debate.Misc.*` |

`lakefile.lean`, `lake-manifest.json`, `lean-toolchain`, CI configuration and
the port's own prose are not vendored; the atlas supplies its own.

## Atlas adaptations

Every change is in the file header. No statement, proof script, notation,
declaration name, or namespace in any body is altered — the diff against the
port is exactly the header block in every file, and nothing else.

1. `module`, and each `import` rewritten to `public import` at the atlas module
   path. The atlas package uses the Lean 4.31 module system; upstream does not.
2. One `@[expose] public section` per file. Cross-module `simp`/`rfl` steps in
   this development unfold definitions from other files, which the module system
   requires to be exposed. `AISafetyAtlas/Upstream/GibbardSatterthwaite.lean`
   solved the same problem by collapsing its upstream tree into a single module;
   a section-level `@[expose] public` keeps the file structure instead, which
   here is what makes the port diffable against its own upstream.
3. A `set_option linter.*` block. The atlas package builds with
   `warningAsError = true` and upstream does not, so seven style linters that
   fire on the vendored proofs are disabled per file:
   `unusedSimpArgs`, `unusedSectionVars`, `unusedVariables`, `deprecated`,
   `style.longLine`, `unnecessarySeqFocus`, `unusedTactic`. Silencing them keeps
   the proofs identical to the port rather than rewriting proofs to satisfy a
   policy they were not written under. No correctness linter is touched, and
   `sorry` remains an error.

## Why this is now Path B

`LAND-DEBATE-001` was first recorded as a Path-A reproduction: built at the
upstream toolchain from a separate checkout, with no atlas import surface,
because upstream pinned Lean/Mathlib `v4.8.0` against the atlas's `v4.31.0`.
[`docs/provenance/debate-reproduction.md`](../../docs/provenance/debate-reproduction.md)
recorded a port-then-wrap as deferred.

The port closes that gap: it moves the development to the atlas's own Mathlib
commit without weakening a theorem, so the development now compiles inside the
atlas build closure. Both lanes are kept —
[`scripts/reproduce_debate.sh`](../../scripts/reproduce_debate.sh) still
reproduces upstream at `v4.8.0`, and `--in-tree` checks the vendored copy.

## Statement fidelity

The port's own `PORTING.md` diffed every declaration signature against upstream
and found exactly three differences, none of them a weakening:

1. `Vector` → `List.Vector` — a Mathlib namespace move, same type.
2. `iteratedDerivWithin_eq_iteratedDeriv` →
   `iteratedDerivWithin_eq_iteratedDeriv_of_contDiff` — a *local* helper in
   `Prob/Chernoff.lean`, renamed because Mathlib now occupies the old name.
3. `Prob.ext_iff` removed — now generated by `@[ext]`; the generated statement
   was checked identical to the deleted manual one.

`Debate/Correct.lean`, which carries the three headline results, is
byte-identical to upstream apart from the atlas header.

## Verification in the atlas tree

```console
lake build AISafetyAtlas.Upstream.Debate      # 18 modules, exit 0
lake build AISafetyAtlas.Oversight.Debate
lake build AISafetyAtlas.Examples.Oversight.Debate
scripts/reproduce_debate.sh --in-tree         # axiom + trust scan on the vendored tree
```

`#print axioms` on the facade declarations, all six:

```
'AISafetyAtlas.Oversight.Debate.completeness' depends on axioms: [propext, Classical.choice, Quot.sound]
'AISafetyAtlas.Oversight.Debate.soundness'    depends on axioms: [propext, Classical.choice, Quot.sound]
'AISafetyAtlas.Oversight.Debate.correctness'  depends on axioms: [propext, Classical.choice, Quot.sound]
'AISafetyAtlas.Oversight.Debate.alice_fast'   depends on axioms: [propext, Classical.choice, Quot.sound]
'AISafetyAtlas.Oversight.Debate.bob_fast'     depends on axioms: [propext, Classical.choice, Quot.sound]
'AISafetyAtlas.Oversight.Debate.vera_fast'    depends on axioms: [propext, Classical.choice, Quot.sound]
```

No `sorry`, `admit`, `sorryAx`, `native_decide`, `@[implemented_by]`,
`@[extern]`, or added `axiom` anywhere in the vendored tree.

## Honest scope — upstream's own caveats, carried unchanged

- **Correctness only.** Space complexity is not formalized.
- **Time counts oracle queries only** — not full computational cost.
- The **Lipschitz oracle machine** is defined slightly differently from the
  paper: a stronger variant.
- No AI-system reading follows from these theorems without a separate reviewed
  bridge. They are machine-checked statements about the protocol model, not
  claims about any deployed oversight scheme.

## Reproducing the vendored tree

```console
git clone --branch port-lean-4.31 https://github.com/LukaHobor/debate
git -C debate checkout dafe25df02300c0ebecf436aab32e953006cb0a1
# every difference is the header block described above
diff debate/Debate/Correct.lean AISafetyAtlas/Upstream/Debate/Correct.lean
```
