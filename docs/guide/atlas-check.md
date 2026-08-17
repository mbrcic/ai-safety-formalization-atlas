# `atlas-check` — answer a finite model, name the theorem

The atlas states its obstructions as theorems. A consumer usually arrives with a
model instead: *these states, this monitor, this hazard — is it covered?*
Answering that has meant writing Lean.

`atlas-check` reads the model from a JSON file and prints the verdict together
with the declaration that certifies it.

```console
lake build atlas-check
.lake/build/bin/atlas-check docs/examples/atlas-check/report-stream-is-blind.json
```

```
verdict: NOT KNOWABLE
witness: states 0 and 3 share an observation and differ in the property
worst ambiguity: 2 (one property value per observation is exact knowledge)
certified by: AISafetyAtlas.Knowledge.Check.not_knowable_of_findCollision_eq_some
the obstruction itself: AISafetyAtlas.Knowledge.not_knowable_of_collision
the counting form: AISafetyAtlas.Knowledge.knowable_iff_worstAmbiguity_le_one
```

## What it decides

| `kind` | Question | Backed by |
|---|---|---|
| `knowability` | Is the property recoverable from the observation? | [`Knowledge.Check.findCollision`](../../AISafetyAtlas/Knowledge/Check.lean) and its two agreement theorems |
| `coalition` | Does what a coalition of principals can read determine the hazard? | [`Oversight.JointObservation.Covers`](../../AISafetyAtlas/Oversight/JointObservation/Coverage.lean), which is *definitionally* `Knowable` on the coalition's observation |
| `device` | Does a Wolpert device answer probes of a target, and can it physically know a value? | [`Knowledge.Devices.BlockwiseCollision`](../../AISafetyAtlas/Knowledge/Devices.lean) and the two refutations it discharges |
| `variety` | Can **any** overseer hold the outcome to a single target? | [`Oversight.VarietyCheck.cannotForce`](../../AISafetyAtlas/Oversight/VarietyCheck.lean) and `not_forces_of_cannotForce`, whose quantifier runs over every observation type |

Every verdict also reports **worst ambiguity** — how many values one observation
leaves open at its worst point. `1` is exact knowledge, and anything larger is the
shortfall, so a failing model says *how far off* it is rather than only that it
failed. The counting form is
[`knowable_iff_worstAmbiguity_le_one`](../../AISafetyAtlas/Knowledge/Ambiguity.lean).

`variety` is the only kind here whose verdict is **one-sided by design**, and it
says so in its own output. A `true` result rules out every policy over every
observation, because the agreement theorem quantifies over the observation type
rather than fixing one. A `false` result means the counting bound does not apply
to this table — not that oversight succeeds. The bound is necessary and not
sufficient, and
[`exists_cannotForce_false_and_forces`](../../AISafetyAtlas/Oversight/VarietyCheck.lean)
exhibits a table where the checker is silent and forcing does succeed, so the
distinction is a theorem rather than a caveat in the printout.

Its input is rectangular rather than square: `effect` has one row per situation
and one column per intervention, entries being outcome codes compared for
equality only.

```json
{ "schema": "atlas-check/1", "kind": "variety",
  "situations": 3, "interventions": 2, "effect": [[0,0],[1,1],[2,2]] }
```

## Input

States are `0 … states-1`; every array is indexed by state. Setup and target
values are compared for equality only, so their numbering carries no other
meaning. The seven models under
[`docs/examples/atlas-check/`](../examples/atlas-check/) are runnable, and each names
the Lean theorem it mirrors.

```json
{ "schema": "atlas-check/1", "kind": "knowability",
  "states": 4, "observation": [0,0,1,1], "property": [0,1,0,1] }
```

```json
{ "schema": "atlas-check/1", "kind": "coalition",
  "states": 4, "emitted": [[0,0,1,1],[0,1,0,1]],
  "coalition": [0], "hazard": [false,true,false,true] }
```

`emitted` has one row per principal, each row indexed by state; `coalition` names
principals by row index. The coalition's observation in a state is the tuple of
its members' rows there.

```json
{ "schema": "atlas-check/1", "kind": "device",
  "states": 4, "setup": [0,0,1,1], "conclusion": [false,false,true,true],
  "target": [0,1,0,1], "value": 1 }
```

Arrays whose length does not match `states` are refused rather than padded, and a
conclusion array that does not take both values is refused because Definition 1
requires it to be onto `Bool`. A reader that quietly repairs its input decides a
different model than the one it was given.

This format is the atlas's own. It is deliberately **not** any downstream
project's schema: partial compatibility with a foreign format is worse than none,
and a project-specific serialization belongs in that project.

## What the output is not

The verdict is what the kernel would give, and the named theorem is why. It is
**not** a proof term the kernel has checked for this instance: the program
evaluates a decision procedure the kernel has verified correct, which is a weaker
thing than a checked proof of the case in front of you. To get that, instantiate
the named declaration in Lean.

Nothing here decides anything about an infinite state space, and no verdict is a
statement about a deployed system. A model is a model.

One step between your JSON and the certified predicates deserves naming: the
reader relabels setup and target values into finite types, keeping only which
states share a value. If that normalization were not invariant, a verdict could
be about a different model than the one you wrote.

It is invariant, and proved so.
[`knowable_congr_observation`](../../AISafetyAtlas/Knowledge/Check.lean) and
`knowable_congr_property` take exactly the reader's guarantee as their hypothesis
— two states share a relabelled value precisely when they shared a raw one — and
conclude that knowability is the same question before and after. Neither needs
the relabelling to be injective, surjective, or into any particular type; only
the partition has to survive, which is what the reader preserves.
`knowable_comp_left_iff` is the special case a caller is most likely to reason
about, renaming values by an injection.

What that leaves is narrower and worth stating separately: the theorems cover the
*normalization*, not the JSON parse. A reader that mis-parses your file, or that
drops a row, is producing a different model, and no invariance theorem can see
that. It is not the kind of claim a proof can carry, so it is carried by test.

[`scripts/check_atlas_check_parse.py`](../../scripts/check_atlas_check_parse.py)
runs two batteries against every shipped fixture. One asserts that malformations
are **refused** rather than decided — arrays of the wrong length, ragged rows,
non-numeric or negative entries, a missing field, an unknown schema or kind, a
declared count that disagrees with the data, a coalition member that is not a
principal. The other asserts the mirror image: renaming values must leave the
verdict **unchanged**, because every predicate here depends on the partition the
names induce and on nothing else. That is the same property `knowable_congr_observation`
proves, driven end to end through the binary instead of assumed of it.

The second battery is not decoration. The failure it rules out is a reader that
merges two outcome labels — capping them, say, rather than renumbering them. Two
merged outcomes make an intervention look as though it flattens two situations,
and a `NO OVERSEER CAN FORCE THE OUTCOME` finding decays into `THE COUNTING BOUND
DOES NOT APPLY`: the reader contradicting the theorem it prints. `runVariety`
renumbers canonically, which preserves the partition exactly, and the battery is
what keeps it that way. Note the direction: merging outcomes only makes a column
*less* separating, so this class of bug buries a real obstruction rather than
inventing one.

## Why the answers can be trusted

Every checker is paired with a theorem saying it agrees with the `Prop` — the
pattern [`Oversight.JointObservation.FiniteDecision`](../../AISafetyAtlas/Oversight/JointObservation/FiniteDecision.lean)
already sets for coverage. Without that theorem the output would be a report
rather than evidence.

`scripts/check_atlas_check.sh` runs the shipped models and asserts the verdicts
the tree already proves:
[`Examples.Oversight.Overseer`](../../AISafetyAtlas/Examples/Oversight/Overseer.lean)
for the two devices, and
[`Procurement`](../../AISafetyAtlas/Examples/Oversight/JointObservation/Procurement.lean)
for the coalitions — including that the emitted-interface failure witness is
`(sigma10, sigma11)`, which the program independently reports as states 1 and 3.
If the program and the proofs ever disagree, one of them is wrong and CI says so.

## Scale

The intended use is many small models, not one large one.

`knowability` and `coalition` are quadratic in the state count — every ordered
pair is examined.

`device` is quadratic in the state count and **exponential in the number of
distinct values the target takes**, because Definition 3 quantifies over every
probe `f : G → Bool` and the decision procedure enumerates all `2^|G|` of them.
The state count is not what drives it. Measured on this build:

| Distinct target values | States | Time |
|---|---|---|
| 2 | 400 | 1.4 s |
| 8 | 16 | 0.04 s |
| 14 | 28 | 0.2 s |
| 18 | 36 | 0.6 s |
| 20 | 40 | 2.8 s |

So a hazard bit over hundreds of states is fine, and a target with more than
about twenty distinct values is not. This is worth stating because the first
version of the tool relabelled the target into the state count, which made the
state count the exponent and put a hard wall at 22 states — 11 s where the same
model now takes 0.2 s. If a future change reintroduces that, this table is how
it shows up.
