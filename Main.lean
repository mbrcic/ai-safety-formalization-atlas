module

public import AISafetyAtlas.Knowledge.Check
public import AISafetyAtlas.Knowledge.Ambiguity
public import AISafetyAtlas.Oversight.VarietyCheck
public import Lean.Data.Json

/-!
# `atlas-check` — answer a finite model, name the theorem that settles it

The atlas states its obstructions as theorems and proves them by hand. A consumer
usually arrives with a model instead: these states, this monitor, this hazard, is
it covered. Answering that has meant writing Lean.

This reads the model from a JSON file and prints the verdict together with the
declaration that certifies it, so the answer is traceable back into the tree
rather than being a number from a program.

## What it decides

`knowability` — is the property recoverable from the observation? Backed by
`Knowledge.Check.findCollision` and its two agreement theorems. A returned pair
is an indistinguishability witness; returning nothing over a complete
enumeration *is* `Knowable`.

`coalition` — does what a coalition of principals can read determine the hazard?
This is the joint-observation question. `Covers` is definitionally `Knowable` on
the coalition's observation, so it is decided by the same certified search, and
the output names both.

`device` — does a Wolpert inference device answer probes of a target, and does it
physically know a value? Backed by `Knowledge.Devices.BlockwiseCollision` and the
two refutations it discharges, evaluated through the `Decidable` instances in
`Knowledge.Check`.

`variety` — can any overseer hold the outcome to one target? This is the *doing*
question rather than the seeing one, and it is the only kind here whose verdict
is one-sided by design. `Oversight.VarietyCheck.cannotForce` decides the counting
obstruction; a `true` verdict rules out every policy over every observation, by
`not_forces_of_cannotForce`. A `false` verdict is **not** a clearance: the bound
is necessary and not sufficient, so it means this argument does not apply, and
`exists_cannotForce_false_and_forces` is why that distinction is recorded in the
tree rather than only in the output.

## Input

Self-describing, and deliberately **not** any downstream project's format. States
are `0 … states-1`; every array is indexed by state. Setup and target values are
compared for equality only, so their numbering carries no other meaning.

```json
{ "schema": "atlas-check/1", "kind": "knowability",
  "states": 4, "observation": [0,0,1,1], "property": [0,1,0,1] }

{ "schema": "atlas-check/1", "kind": "coalition",
  "states": 4, "emitted": [[0,0,1,1],[0,1,0,1]],
  "coalition": [0], "hazard": [false,true,false,true] }

{ "schema": "atlas-check/1", "kind": "device",
  "states": 4, "setup": [0,0,1,1], "conclusion": [false,false,true,true],
  "target": [0,1,0,1], "value": 1 }

{ "schema": "atlas-check/1", "kind": "variety",
  "situations": 3, "interventions": 2, "effect": [[0,0],[1,1],[2,2]] }
```

`effect` has one row per situation and one column per intervention; entries are
outcome codes, compared for equality only.

`emitted` has one row per principal, each row indexed by state; `coalition`
names principals by row index.

## What the output is, and is not

The verdict is what the kernel would give, and the named theorem is why. It is
**not** a proof term the kernel has checked: the program evaluates a decision
procedure the kernel has verified correct, which is a different and weaker thing
than a checked proof of this instance. To get the latter, instantiate the named
declaration in Lean.

Exit status is `0` when the model was read and decided, `1` when it was not.
The verdict is on stdout; a verdict of "not covered" is not an error.

## The one unproved step

Setup and target values are relabelled into finite types, keeping only which
states share a value. Every predicate here depends on nothing else — probes and
blocks see fibres, never labels — so the normalization should be invariant. That
invariance is asserted here and not proved, and it is the only place between the
input and the certified predicates where a verdict could be about a different
model than the one that was written down.
-/

open Lean (Json)
open AISafetyAtlas.Inference
open AISafetyAtlas.Knowledge
open AISafetyAtlas.Knowledge.Check

namespace AtlasCheck

/-- Field lookups return a reason rather than a default: a missing array read as
all-zeroes would decide a different model and report success. -/
private def field (j : Json) (name : String) : Except String Json :=
  match j.getObjVal? name with
  | .ok v => .ok v
  | .error _ => .error s!"missing required field '{name}'"

private def natField (j : Json) (name : String) : Except String Nat := do
  match (← field j name).getNat? with
  | .ok n => .ok n
  | .error _ => .error s!"field '{name}' must be a non-negative integer"

private def natArray (j : Json) (name : String) (states : Nat) :
    Except String (Array Nat) := do
  let arr ← match (← field j name).getArr? with
    | .ok a => pure a
    | .error _ => throw s!"field '{name}' must be an array"
  if arr.size ≠ states then
    throw s!"field '{name}' has {arr.size} entries but the model has {states} states"
  arr.mapM fun v =>
    match v.getNat? with
    | .ok n => .ok n
    | .error _ => .error s!"field '{name}' must contain non-negative integers"

private def boolArray (j : Json) (name : String) (states : Nat) :
    Except String (Array Bool) := do
  let arr ← match (← field j name).getArr? with
    | .ok a => pure a
    | .error _ => throw s!"field '{name}' must be an array"
  if arr.size ≠ states then
    throw s!"field '{name}' has {arr.size} entries but the model has {states} states"
  arr.mapM fun v =>
    match v.getBool? with
    | .ok b => .ok b
    | .error _ => .error s!"field '{name}' must contain booleans"

private def natList (j : Json) (name : String) : Except String (List Nat) := do
  let arr ← match (← field j name).getArr? with
    | .ok a => pure a
    | .error _ => throw s!"field '{name}' must be an array"
  (arr.toList).mapM fun v =>
    match v.getNat? with
    | .ok n => .ok n
    | .error _ => .error s!"field '{name}' must contain non-negative integers"

/-- A rectangular table: `rows` rows of `cols` entries. Separate from
`natMatrix` because that one is square by intent — one row per principal, one
column per state — and an effect table is not. -/
private def natTable (j : Json) (name : String) (rows : Nat) (cols : Nat) :
    Except String (Array (Array Nat)) := do
  let raw ← match (← field j name).getArr? with
    | .ok a => pure a
    | .error _ => throw s!"field '{name}' must be an array of arrays"
  if raw.size ≠ rows then
    throw s!"field '{name}' has {raw.size} rows but the model declares {rows}"
  raw.mapM fun row => do
    let entries ← match row.getArr? with
      | .ok a => pure a
      | .error _ => throw s!"field '{name}' must contain arrays, one per row"
    if entries.size ≠ cols then
      throw s!"a row of '{name}' has {entries.size} entries but the model declares {cols} columns"
    entries.mapM fun v =>
      match v.getNat? with
      | .ok n => .ok n
      | .error _ => .error s!"field '{name}' must contain non-negative integers"

/-- One row per principal, each row indexed by state. Rows of the wrong length
are refused for the same reason short arrays are: a padded row is a different
model. -/
private def natMatrix (j : Json) (name : String) (states : Nat) :
    Except String (Array (Array Nat)) := do
  let rows ← match (← field j name).getArr? with
    | .ok a => pure a
    | .error _ => throw s!"field '{name}' must be an array of arrays"
  if rows.isEmpty then throw s!"field '{name}' declares no principals"
  rows.mapM fun row => do
    let entries ← match row.getArr? with
      | .ok a => pure a
      | .error _ => throw s!"field '{name}' must contain arrays, one per principal"
    if entries.size ≠ states then
      throw s!"a row of '{name}' has {entries.size} entries but the model has {states} states"
    entries.mapM fun v =>
      match v.getNat? with
      | .ok n => .ok n
      | .error _ => .error s!"field '{name}' must contain non-negative integers"

/--
Relabel a raw array as a map into `Fin n`, sending each state to the first state
carrying the same raw value.

Only the partition into equal-valued blocks matters to every predicate here, and
this makes the codomain finite without the caller having to declare its size. The
`else` branch is unreachable — the search always finds the state it started
from — and is present so the function is total without a proof obligation.
-/
private def relabel {n : Nat} (raw : Array Nat) : Fin n → Fin n := fun i =>
  let idx := (List.range n).findIdx fun j => raw[j]! == raw[i.1]!
  if h : idx < n then ⟨idx, h⟩ else i

/-- The raw values actually present, in first-appearance order. -/
private def distinctValues (raw : Array Nat) : Array Nat :=
  raw.foldl (fun seen v => if seen.contains v then seen else seen.push v) #[]

/--
The outcomes an effect table carries, in first-appearance order.

An outcome label is a **name**. `Oversight.cannotForce` asks only whether each
intervention's column is injective, so the verdict depends on the partition the
labels induce and on nothing else — which makes renumbering them the one
normalization guaranteed to leave the answer alone. Capping them instead is not:
a cap merges two names into one and asks a different question. -/
private def tableOutcomes (rows : Array (Array Nat)) : Array Nat :=
  distinctValues (rows.foldl (fun acc row => acc ++ row) #[])

/--
Relabel a raw array into `Fin k`, where `k` is how many distinct values it
carries rather than how many states there are.

For the target this is not cosmetic. `WeaklyInfers` quantifies over every
`f : G → Bool`, so the decision procedure enumerates `2 ^ |G|` probe functions.
Relabelling into `Fin states` makes `|G|` the state count, which put a hard wall
at about 22 states — measured, not estimated: 16 states took 0.3s, 20 took 2.7s,
22 took 11s. Relabelling into the distinct values instead makes `|G|` the number
of values the target actually takes, which for a hazard bit is two whatever the
state count is.

The `else` branch is unreachable: every state's value is in `distinctValues` by
construction. It is present so the function is total without a proof obligation.
-/
private def relabelValues {n k : Nat} (raw : Array Nat) (values : Array Nat)
    (hk : 0 < k) : Fin n → Fin k := fun i =>
  let idx := (values.findIdx? (· == raw[i.1]!)).getD 0
  if h : idx < k then ⟨idx, h⟩ else ⟨0, hk⟩

private def enumOf (n : Nat) : List (Fin n) := (List.finRange n)

private theorem enumOf_complete (n : Nat) : ∀ i : Fin n, i ∈ enumOf n := by
  intro i
  simp [enumOf]

/-! ## The two checks

The state count arrives at runtime, so `Fin states` is only known to be inhabited
after the input has been read. Each check therefore takes the count as a
parameter with `NeZero` in scope, and the reader establishes it once.
-/

private def knowabilityAt {I Y : Type} [DecidableEq I] [DecidableEq Y] [Nonempty Y]
    (states : Nat) [NeZero states] (noun : String)
    (obs : Fin states → I) (prop : Fin states → Y) : List String :=
  -- A yes/no answer hides how far off a failing observation is. The worst
  -- ambiguity is how many values one observation leaves open at its worst point,
  -- and `1` is exactly knowability — so it reports the verdict and the shortfall
  -- in one number.
  let worst := worstAmbiguity obs prop
  let shortfall :=
    s!"worst ambiguity: {worst} (one {noun} value per observation is exact knowledge)"
  match hfind : findCollision (enumOf states) obs prop with
  | some p =>
      -- Naming the refutation is the point: the verdict below is this Prop.
      let _ : ¬ Knowable obs prop := not_knowable_of_findCollision_eq_some hfind
      [ "verdict: NOT KNOWABLE",
        s!"witness: states {p.1.1} and {p.2.1} share an observation and differ in the {noun}",
        shortfall,
        "certified by: AISafetyAtlas.Knowledge.Check.not_knowable_of_findCollision_eq_some",
        "the obstruction itself: AISafetyAtlas.Knowledge.not_knowable_of_collision",
        "the counting form: AISafetyAtlas.Knowledge.knowable_iff_worstAmbiguity_le_one" ]
  | none =>
      let _ : Knowable obs prop :=
        knowable_of_findCollision_eq_none (enumOf_complete states) hfind
      [ "verdict: KNOWABLE",
        s!"searched: every ordered pair of the {states} states",
        shortfall,
        "certified by: AISafetyAtlas.Knowledge.Check.knowable_of_findCollision_eq_none",
        "the characterization: AISafetyAtlas.Knowledge.knowable_iff_no_collision" ]

private def runKnowability (j : Json) : Except String (List String) := do
  let states ← natField j "states"
  if hz : states = 0 then
    throw "a model needs at least one state"
  else
    let observation ← natArray j "observation" states
    let property ← natArray j "property" states
    haveI : NeZero states := ⟨hz⟩
    pure (knowabilityAt states "property" (relabel observation) (relabel property))

/--
Coalition coverage: does what a coalition of principals can read determine the
hazard?

`Covers` is *definitionally* `Knowable q.observe h`, so once the coalition's
observation is assembled the question is the one `findCollision` already decides.
The reader assembles it rather than reconstructing an `EvidenceArchitecture` at
runtime: the observation of a coalition in an execution is the tuple of its
members' emitted views there, and a tuple is compared for equality only.
-/
private def runCoalition (j : Json) : Except String (List String) := do
  let states ← natField j "states"
  if hz : states = 0 then
    throw "a model needs at least one state"
  else
    let emitted ← natMatrix j "emitted" states
    let coalition ← natList j "coalition"
    for member in coalition do
      if member ≥ emitted.size then
        throw s!"coalition names principal {member} but only {emitted.size} are declared"
    let hazard ← boolArray j "hazard" states
    haveI : NeZero states := ⟨hz⟩
    let observe : Fin states → List Nat := fun σ =>
      coalition.map fun member => (emitted[member]!)[σ.1]!
    let hazardAt : Fin states → Bool := fun σ => hazard[σ.1]!
    pure (
      [ s!"coalition: {coalition} of {emitted.size} principals" ] ++
      knowabilityAt states "hazard" observe hazardAt ++
      [ "the coverage predicate this decides: AISafetyAtlas.Oversight.JointObservation.Covers",
        "which is definitionally Knowable on the coalition's observation" ])

private def runDevice (j : Json) : Except String (List String) := do
  let states ← natField j "states"
  if states = 0 then throw "a model needs at least one state"
  let setupRaw ← natArray j "setup" states
  let conclusion ← boolArray j "conclusion" states
  let targetRaw ← natArray j "target" states
  let value ← natField j "value"
  let setup : Fin states → Fin states := relabel setupRaw
  let targetValues := distinctValues targetRaw
  let concl : Fin states → Bool := fun i => conclusion[i.1]!
  if hk : 0 < targetValues.size then
  if hsurj : Function.Surjective concl then
    -- The target's codomain is the values it takes, not the state count. That
    -- choice is what keeps the probe enumeration proportional to the model
    -- rather than to the number of states; see `relabelValues`.
    let target : Fin states → Fin targetValues.size :=
      relabelValues targetRaw targetValues hk
    let C : InferenceDevice (Fin states) :=
      { Setup := Fin states, setup := setup, concl := concl, concl_surjective := hsurj }
    match (List.finRange states).find? (fun i => targetRaw[i.1]! == value) with
    | none => throw s!"no state carries target value {value}, so nothing can be known about it"
    | some witness =>
        let γ := target witness
        let weak := decide (WeaklyInfers C target)
        let blockwise := decide (Devices.BlockwiseCollision C target γ)
        pure ([
          s!"weak inference (Definition 3): {if weak then "HOLDS" else "FAILS"}",
          "decided by: AISafetyAtlas.Knowledge.Check.decidableWeaklyInfers"
        ] ++ (if blockwise then [
          s!"blockwise collision at value {value}: PRESENT",
          "so weak inference is refuted: AISafetyAtlas.Knowledge.Devices.BlockwiseCollision.not_weaklyInfers",
          "and physical knowledge is refuted in every context: AISafetyAtlas.Knowledge.Devices.BlockwiseCollision.not_physicallyKnows"
        ] else [
          s!"blockwise collision at value {value}: ABSENT",
          "so neither Wolpert refutation applies; this is not a claim that the device knows the value"
        ]))
  else
    throw "the conclusion array must take both values — Definition 1 requires it to be onto Bool"
  else
    throw "the target array carries no values, so there is nothing to probe"

/--
The variety bound: can any overseer hold the outcome to a single target?

The effect table is read as `situations x interventions`, and the verdict comes
from `Oversight.VarietyCheck.cannotForce`, whose agreement theorem quantifies
over every observation type. So a `true` verdict is about every possible
overseer, which is why the output says so rather than naming a policy.

The `false` branch reports what it does *not* establish. The counting bound is a
necessary condition, and a checker that printed "forcing is possible" here would
be asserting its converse.

Outcome labels are renumbered by `tableOutcomes` rather than capped. Capping
merges any two labels above the cap into one, which silently decides a
**different** model: `cannotForce` tests only column injectivity, so relabelling
a table must leave the verdict alone, and a merge can turn a real obstruction
into silence. `scripts/check_atlas_check_parse.py` tests that invariance.
-/
private def runVariety (j : Json) : Except String (List String) := do
  let situations ← natField j "situations"
  let interventions ← natField j "interventions"
  if situations = 0 then
    throw "a model needs at least one situation"
  else if interventions = 0 then
    throw "an overseer with no interventions is not a model of oversight"
  else
    let rows ← natTable j "effect" situations interventions
    let outcomes := tableOutcomes rows
    if hk : 0 < outcomes.size then
    let table : Fin situations → Fin interventions → Fin outcomes.size :=
      fun s a =>
        let raw := (rows[s.1]!)[a.1]?.getD 0
        let idx := (outcomes.findIdx? (· == raw)).getD 0
        if h : idx < outcomes.size then ⟨idx, h⟩ else ⟨0, hk⟩
    if AISafetyAtlas.Oversight.cannotForce table then
      pure [
        "verdict: NO OVERSEER CAN FORCE THE OUTCOME",
        s!"  {interventions} interventions for {situations} situations, and every intervention still separates them",
        "  certified by AISafetyAtlas.Oversight.not_forces_of_cannotForce",
        "  the bound quantifies over every observation, so this rules out every policy"
      ]
    else
      pure [
        "verdict: THE COUNTING BOUND DOES NOT APPLY",
        "  this is NOT a finding that oversight succeeds",
        "  the bound is necessary and not sufficient; see",
        "  AISafetyAtlas.Oversight.exists_cannotForce_false_and_forces"
      ]
    else
      throw "the effect table carries no outcomes, so there is nothing to force"

private def run (j : Json) : Except String (List String) := do
  let schema ← match (← field j "schema").getStr? with
    | .ok s => pure s
    | .error _ => throw "field 'schema' must be a string"
  if schema ≠ "atlas-check/1" then
    throw s!"unknown schema '{schema}'; this build reads 'atlas-check/1'"
  let kind ← match (← field j "kind").getStr? with
    | .ok s => pure s
    | .error _ => throw "field 'kind' must be a string"
  match kind with
  | "knowability" => runKnowability j
  | "coalition" => runCoalition j
  | "device" => runDevice j
  | "variety" => runVariety j
  | other =>
      throw s!"unknown kind '{other}'; this build reads 'knowability', 'coalition', 'device' and 'variety'"

public def main (args : List String) : IO UInt32 := do
  match args with
  | [path] =>
      match ← (IO.FS.readFile path).toBaseIO with
      | .error e => do IO.eprintln s!"atlas-check: cannot read {path}: {e}"; pure 1
      | .ok text =>
      match Json.parse text with
      | .error e => do IO.eprintln s!"atlas-check: {path} is not valid JSON: {e}"; pure 1
      | .ok j =>
          match run j with
          | .error e => do IO.eprintln s!"atlas-check: {e}"; pure 1
          | .ok lines => do
              for line in lines do IO.println line
              pure 0
  | _ => do
      IO.eprintln "usage: atlas-check MODEL.json"
      IO.eprintln "  reads a finite model and prints the verdict with the theorem that certifies it"
      pure 1

end AtlasCheck

public def main (args : List String) : IO UInt32 := AtlasCheck.main args
