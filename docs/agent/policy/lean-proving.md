## Proving: tactic order and the exploration target

Try automation before writing a proof by hand, in this order:

1. **`grind`** — Lean core, so it needs no import and is available even inside
   `Inference/Device.lean`'s two-module import surface. Measured, not assumed.
2. **`aesop (rule_sets := [inference])`** — for goals about devices, after
   `import AISafetyAtlas.Inference.Search`. That module is deliberately not on the
   public root import: the core's narrow imports are what keep it cheap to audit.
3. **`decide`** — on finite models. `native_decide` stays banned; the gate rejects it.

**Test a conjecture before proving it.** `AISafetyAtlas.Explore` imports the full
`Mathlib.Tactic` surface plus `Plausible` and is built by CI as an explicit target,
so the discovery tactics stay available without widening any shipped import graph.

**`plausible` may never appear in committed code.** On a goal it cannot refute it
reports *"Unable to find a counter-example"* and closes the goal with `sorry`. Use
it interactively; commit the counterexample it found as a real theorem, or the
proof it failed to refute.

**To search over devices, not just over values:** `InferenceDevice` carries its
setup type as a field, so a statement quantifying over devices ranges over a proper
class and nothing can enumerate it. `Examples.Inference.Enumerable.FinDevice` fixes both types
(`U = Fin m`, `Setup = Fin n`), is a `Fintype`, and carries a `Decidable` instance
for `WeaklyInfers`. `decide` then settles *"no device of this shape does X"* in the
kernel — exhaustive and trusted, where sampling would be neither. The instance has
to unfold `WeaklyInfers`, `Realized` and `IsProbe` by hand, because instance search
runs at reducible transparency and those are `def`s.

**Before adding a hypothesis, check the ones already there:**

```console
python3 scripts/minimize_hypotheses.py <module.lean> --decl <name>
python3 scripts/minimize_hypotheses.py <module.lean> --dead-haves-only
```

`REMOVABLE` means the statement is true without that hypothesis — drop it, or say
in the docstring why print fidelity keeps it. A hypothesis consumed only by a
`have _x` the proof then discards reports `USED` and is really removable, which is
what `--dead-haves-only` finds. This is an offline audit, not a gate: each
candidate costs a full elaboration.
