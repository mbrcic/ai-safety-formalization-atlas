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

## Witness search: using a refutation tool to inhabit a hypothesis

`scripts/check_witness_debt.py` reports theorems nothing instantiates. Closing
one means exhibiting a model that satisfies its hypotheses. That is a search
problem, and the repository's refutation tooling solves it under one negation:

> To inhabit `H`, refute `∀ m, ¬ H m`. The counterexample **is** the witness.

**Look for a witnessed sibling before searching.** A theorem often ships in
several strengths — a cardinality equality, a `Fintype.card` equality and a
bijection; a weighted form and a set form — and the weaker ones tend to get the
worked example while the strongest goes uninstantiated. `thm7_equiv` was
ungrounded while `thm7_mk` and `thm7_card` both had witnesses on `saSelfProbe`
discharging the *same four premises*; the fix was that argument list pointed at
the other conclusion. One grep for the shared premise names answers this, and it
costs nothing when it fails.

**The cost is usually elaboration, not search.** Measured on the first two
attempts: neither needed a model, both needed the instance to typecheck.
`no_free_lunch_stochastic_of_sharp` states a raw double sum where its sibling
keeps the same content folded inside `stochasticTrace`, and matching the
unfolded form exhausted `maxHeartbeats` at 200000, 400000 and 1000000 — the
budget was not the problem and raising it again would not have been the fix. A
lemma whose own proof runs `classical` carries a `Classical.propDecidable`-derived
`Fintype` in its conclusion, which is defeq to the real instance and not
syntactically equal, so `exact` refuses and `convert` may too. Budget the work
accordingly: the witness is cheap, the restatement is not.

### Where `/lean4:disprove` comes in — third, not first

Search is the last of three steps, because the first two close most leaves and
cost a grep each.

1. **Is there a witnessed sibling?** Above. Reuse its argument list.
2. **Is the model already in the file?** Most leaves are lemmas *about* a model
   the `Examples/` module already builds — `saSelfProbe`, `coinRule`, `figSCIM`,
   `undelegated`/`delegated`. Then there is nothing to search for: the premises
   are proved nearby and the work is applying the lemma to them. Both attempts
   measured so far were this case.
3. **Only when you do not know a model that satisfies `H`** is this a search
   problem, and that is where `/lean4:disprove` belongs.

**The case where search genuinely earns its keep is a `False` conclusion.** When
the theorem is `H₁ → ⋯ → Hₙ → False`, the full antecedent is *unsatisfiable* —
that is the result — so no existing model satisfies it and none ever will. What
the obligation needs instead is, for each `i`, a model satisfying every `Hⱼ` with
`j ≠ i`, which shows the impossibility does not rest on one already-impossible
premise. Those leave-one-out models are objects nobody had a reason to build, so
there is nothing to reuse and the sibling check cannot help. Six leaves are in
this class.

Method by shape, complementary rather than ranked: `decide-cascade` is exhaustive
and kernel-trusted but explodes past small `Fin n`; `external` reaches SAT/SMT
(`sat-z3`, `sat-cvc5`, `smt-z3`, `smt-cvc5`) and needs the hypotheses encoded for
a solver, so it suits arithmetic side conditions; `plausible` samples structured
types where neither is practical — function-valued fields, devices carrying their
own setup type.

### What running it actually showed

Measured on four leaves, and three predictions above did not survive.

**`plausible` cannot run on `ℝ` or `ℝ≥0∞` at all.** *"Failed to create a
`testable` instance"* — there is no `SampleableExt ℝ`, and `2/3 ≤ p` is not
decidable. `decide-cascade` is dead on the same types for the same reason:
nothing finite to exhaust. That removes both from most of `OutcomeLaw`,
`Causal` and `Inference.Stochastic`, which is where the numeric hypotheses are.

**A `False` conclusion is not where search earns its keep.** The claim above was
written before testing and `not_both_two_thirds` refuted it on first contact:
its three leave-one-out models are `(1,1)`, `(0,1)` and `(1,0)`, visible by
inspection and one `norm_num` each. A `False` conclusion means no model can
satisfy the whole antecedent, but the *subsets* are usually easy, because a
premise that is hard to satisfy alone is rare.

**Where SMT did earn its keep: non-degenerate parameters.** On
`not_isObservable_of_ceil_div_gt_height`, whose arithmetic is `ℕ` floor division
over a truncated subtraction, asking z3 for any feasible point returns the
degenerate corner — `k = 1`, `p = 0`, an empty output matrix and a trivial
eigenspace condition, which is also what a hand search reaches for. Adding
`k > 1 ∧ p > 0` returns `n = 4, p = 1, k = 3, m = 4`. That is a witness worth
having and not one a person finds by inspection. **Ask the solver for the
constraint that rules out the degenerate corner, not merely for feasibility.**

**But it moves the cost, it does not remove it.** The non-degenerate point then
has to be realized: `k = 3` at `m = 4` needs a matrix whose maximal generalized
eigenspace first stabilizes at index 3, so a size-3 Jordan block beside a 1×1
one, plus the proof that it does. The degenerate witness is nearly free. Budget
for the construction, and say in the docstring which of the two a witness is.

**Availability.** The `z3` binary answers SMT-LIB2 on stdin and the `z3` Python
bindings are installed; either is enough, and `lean-smt` as a lake dependency is
not needed for this. Nothing from the solver enters the repository — it supplies
the numbers, and the Lean witness is then written and proved in the ordinary
way.

**`plausible` is admissible here, and the reason is not a relaxation.** It is
banned from commits because on a goal it cannot refute it prints *"Unable to find
a counter-example"* and closes the goal with `sorry` — a failure shaped like a
success. In witness search the directions reverse. A found assignment is a
concrete term that either checks or does not, so a false positive is impossible;
finding nothing costs a hand construction and nothing else. The property that
makes the tactic dangerous in a proof is the property that makes it safe as a
generator. Run it in `AISafetyAtlas.Explore`, which exists for this.

**The search tool never appears in the result.** Three outcomes, and conflating
them is the whole risk:

1. **Found and liftable.** Commit the assignment as an explicit `Examples/` term
   with its own proof — `decide`, `rfl`, or by hand. No `plausible`, no
   `native_decide`, no external-solver call survives into the file.
2. **Found, not liftable.** When the residual is not decidable the assignment
   cannot be turned into a term mechanically. It is still a lead; the proof that
   it satisfies `H` is hand work. Say so rather than weakening the statement to
   fit the tool.
3. **Not found.** A null result. It is recorded nowhere, and it is **never**
   evidence that the antecedent is uninhabited — an unsuccessful search and an
   empty antecedent are the two things this whole report exists to keep apart.
   A theorem whose antecedent is genuinely unsatisfiable needs a proof of that,
   not a failed search for its witness.

**A witness is not a consumer.** `report_consumers.py` asks whether anything
depends on a declaration, and zero there is not a defect for a shared law built
ahead of its consumers. This asks whether anything instantiates the hypotheses.
The remedy is an `Examples/` witness — never a manufactured consumer, and never
deleting the lemma. ("Witness" here is a worked example that instantiates the
hypotheses, distinct from a Lean typeclass instance, which is the other sense
this document uses the bare word "instance" for above.)
