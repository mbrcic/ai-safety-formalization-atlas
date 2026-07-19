# Vendored KolmogorovMathlib (incompleteness closure)

This tree is a **minimal, attributed vendoring** of Alexey Milovanov's
[kolmogorov-complexity-lean](https://github.com/AlexeyMilovanov/kolmogorov-complexity-lean)
(Apache-2.0), pinned at revision
`005ac4c81eefe09642ef561057199d489cd79485`.

## Why it is vendored

The atlas public library uses Lean 4.31's `module` system. Upstream
KolmogorovMathlib is a classical (non-`module`) package, so it cannot be
`public import`ed into `AISafetyAtlas`. The same pattern is used for the
vendored Arrow proof under `AISafetyAtlas/Upstream/Arrow.lean`.

Only the **import closure** needed for Chaitin incompleteness is present
(Foundation, Core, Complexity). Prefix complexity, algorithmic probability, and
algorithmic statistics from upstream are **not** vendored. (Gödel first and
second incompleteness are covered separately via the
`FormalizedFormalLogic/Foundation` Lake dependency, not this tree; the earlier
Kritchman–Raz second-incompleteness modules have been removed.)

## What was changed relative to upstream

- `module` header and `public import` of dependencies
- `public` on declarations required at the module boundary
- `@[expose]` on definitions that must unfold across modules
- Atlas-facing documentation comments

Mathematical statements and proofs are upstream's. Prefer the public aliases in
`AISafetyAtlas.Logic` over importing this tree directly.

## Reproduction of the external pin

```console
scripts/reproduce_chaitin.sh
```

That script clones the pinned upstream revision (Lean 4.31 toolchain as
recorded upstream), runs a strict-trust source scan, and builds the Chaitin
modules. It does not use this vendored tree.

## Atlas surface

See [`docs/guide/logic-incompleteness.md`](../../../docs/guide/logic-incompleteness.md) and
[`docs/provenance/external-formalizations.md`](../../../docs/provenance/external-formalizations.md).
