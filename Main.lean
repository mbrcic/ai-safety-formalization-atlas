module

public import AISafetyAtlas.Knowledge.Check
public import AISafetyAtlas.Knowledge.Ambiguity
public import AISafetyAtlas.Oversight.VarietyCheck
public import AISafetyAtlas.Control.RegulationCheck
public import AISafetyAtlas.Sovereignty.EnforcementCheck
public import AISafetyAtlas.Sovereignty.ShieldCheck
public import AISafetyAtlas.Sovereignty.ConformityCheck
public import AISafetyAtlas.Sovereignty.Refusal
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

`unlearning`, `membership` and `access` are the same collision search under three
readings, and they are separate kinds because the same obstruction is good news
or bad news depending on who is asking. For unlearning a collision is **success**
— the released evidence cannot tell a retained world from a removed one. For
membership the same collision is the verifier's failure. For access the search is
run twice, at the access level being narrowed and at what would actually be
released, so that a question which already failed at full access is not reported
as a redaction failure.

`enforcement` — can a rule bind, given what the log records? A forbidden act and
a permitted act sharing a log entry admit no sanction of any kind. **Its positive
branch is constructive**: a clean search returns the monitoring rule itself,
proved correct by
`Sovereignty.Enforcement.enforces_sanctionOf_of_findUnenforceable_eq_none`.

`shield` — synthesise a runtime safety envelope. The only kind whose answer is an
artifact rather than a verdict: it returns one permitted action per state of the
envelope, and `Sovereignty.SafetyGame.exists_maintaining_of_isShield` turns that
into a controller holding for all time. The iteration that proposes the envelope
is **untrusted**; only the certificate is checked, so a smaller envelope is
correct and more conservative, never wrong.

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

{ "schema": "atlas-check/1", "kind": "unlearning",
  "states": 4, "observation": [0,0,1,1], "retained": [true,false,true,false] }

{ "schema": "atlas-check/1", "kind": "membership",
  "states": 4, "observation": [0,0,1,1], "included": [true,false,true,false] }

{ "schema": "atlas-check/1", "kind": "access",
  "states": 4, "full": [0,1,2,3], "released": [0,0,1,1], "question": [0,1,0,1] }

{ "schema": "atlas-check/1", "kind": "enforcement", "acts": 4,
  "log": [0,1,2,3], "forbidden": [true,false,true,false],
  "permitted": [false,true,false,true] }

{ "schema": "atlas-check/1", "kind": "shield",
  "states": 3, "actions": 2, "answers": 2,
  "step": [ [[0,0],[1,2]], [[1,0],[2,2]], [[2,2],[2,2]] ],
  "safe": [true,true,false] }

{ "schema": "atlas-check/1", "kind": "conformity",
  "outcomes": 2, "policies": 2, "environments": 2,
  "outcome": [[0,0],[1,1]],
  "requirements": [[true,false],[false,true]] }

{ "schema": "atlas-check/1", "kind": "fairness",
  "positives_group0": 1, "total_group0": 4,
  "positives_group1": 3, "total_group1": 4,
  "perfect_prediction_available": false }

{ "schema": "atlas-check/1", "kind": "goodhart",
  "observed_indicator": [1,1,0], "threshold": 2 }

{ "schema": "atlas-check/1", "kind": "refusal",
  "outcomes": 2, "safety": [[true,false]], "requests": [[false,true]] }
```

`outcome` has one row per operating policy and one column per environment move;
`requirements` and the two `refusal` families are arrays of booleans indexed by
outcome. `observed_indicator` is the evidence base as measured indicator values.

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

/-- A three-dimensional table: `outer` blocks of `mid` rows of `inner` entries.
Used by `shield`, whose transition reads a state, an action and an answer. -/
private def natCube (j : Json) (name : String) (outer mid inner : Nat) :
    Except String (Array (Array (Array Nat))) := do
  let raw ← match (← field j name).getArr? with
    | .ok a => pure a
    | .error _ => throw s!"field '{name}' must be an array of arrays of arrays"
  if raw.size ≠ outer then
    throw s!"field '{name}' has {raw.size} blocks but the model declares {outer} states"
  raw.mapM fun block => do
    let rows ← match block.getArr? with
      | .ok a => pure a
      | .error _ => throw s!"each block of '{name}' must be an array, one row per action"
    if rows.size ≠ mid then
      throw s!"a block of '{name}' has {rows.size} rows but the model declares {mid} actions"
    rows.mapM fun row => do
      let entries ← match row.getArr? with
        | .ok a => pure a
        | .error _ => throw s!"each row of '{name}' must be an array, one entry per answer"
      if entries.size ≠ inner then
        throw s!"a row of '{name}' has {entries.size} entries but the model declares {inner} answers"
      entries.mapM fun v =>
        match v.getNat? with
        | .ok x => .ok x
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

/-- `kind: "regulation"` — Ashby's counting law on a finite regulation table.

Distinct from `variety` and deliberately so. `variety` decides whether *any*
overseer can force one outcome; this decides whether Ashby's column hypothesis
holds on a given table and, when it does, reports the bound the law certifies
against the variety the strategy actually achieves. The interesting half is the
hypothesis: a `true` verdict exhibits a model satisfying it, which is the one
thing a compiling theorem cannot do for itself. -/
private def runRegulation (j : Json) : Except String (List String) := do
  let disturbances ← natField j "disturbances"
  let responses ← natField j "responses"
  if disturbances = 0 then
    throw "a regulation table needs at least one disturbance"
  else if hresp : responses = 0 then
    throw "a regulator with no responses has no repertoire to count"
  else
    let rows ← natTable j "table" disturbances responses
    let strategyRaw ← natList j "strategy"
    if strategyRaw.length ≠ disturbances then
      throw s!"'strategy' has {strategyRaw.length} entries but the model declares {disturbances} disturbances"
    else if strategyRaw.any (· ≥ responses) then
      throw "'strategy' names a response outside the declared repertoire"
    else
      let outcomes := tableOutcomes rows
      if hk : 0 < outcomes.size then
      let table : Fin disturbances → Fin responses → Fin outcomes.size :=
        fun d r =>
          let raw := (rows[d.1]!)[r.1]?.getD 0
          let idx := (outcomes.findIdx? (· == raw)).getD 0
          if h : idx < outcomes.size then ⟨idx, h⟩ else ⟨0, hk⟩
      let strategyArr := strategyRaw.toArray
      let strategy : Fin disturbances → Fin responses :=
        fun d =>
          let raw := strategyArr[d.1]!
          if h : raw < responses then ⟨raw, h⟩ else ⟨0, Nat.pos_of_ne_zero hresp⟩
      let achieved := AISafetyAtlas.Control.achievedVariety table strategy
      if AISafetyAtlas.Control.columnsInjective table then
        pure [
          "verdict: THE COUNTING LAW APPLIES, AND THIS TABLE SATISFIES IT",
          s!"  no response column repeats an outcome, so the hypothesis is witnessed here",
          s!"  bound: {disturbances}/{responses} outcomes are forced; this strategy admits {achieved}",
          "  certified by AISafetyAtlas.Control.ashby_bound_of_columnsInjective",
          "  the bound holds for every strategy on this table, not only the one given"
        ]
      else
        pure [
          "verdict: ASHBY'S HYPOTHESIS FAILS ON THIS TABLE",
          s!"  some response column repeats an outcome, so the law says nothing here",
          s!"  this strategy admits {achieved} outcome(s), reported and not certified",
          "  this is NOT a finding that the regulator does better",
          "  see AISafetyAtlas.Control.exists_columnsInjective_false_and_bound_fails,",
          "  which exhibits a table where the bound is false rather than merely unproved"
        ]
      else
        throw "the table carries no outcomes, so there is no variety to count"

/-! ## Three readings of one search

`unlearning`, `membership` and `access` all run the collision search
`runKnowability` runs. They are separate kinds because **the same obstruction is
good news or bad news depending on who is asking**, and a checker that printed
one verdict for all three would leave the reader to work out which. Saying so is
half the value of having them.
-/

/-- `kind: "unlearning"` — did removal actually remove it?

Reuel, Bucknall et al. Open Problem 84: *"How should the success of different
model unlearning techniques be evaluated?"*

A world here is a way things could be as far as the released evidence can tell.
`observation` is what the deployed model exposes in that world; `retained` says
whether the target fact is still present in it. Unlearning has *succeeded*
against this evidence exactly when a retained world and a removed world look the
same — so a **collision is the success condition**, and the polarity is the
opposite of every other kind here.

A `KNOWABLE` verdict is the finding that something still recovers the fact. -/
private def runUnlearning (j : Json) : Except String (List String) := do
  let states ← natField j "states"
  if hz : states = 0 then
    throw "an unlearning model needs at least one world"
  else
    let observation ← natArray j "observation" states
    let retained ← boolArray j "retained" states
    haveI : NeZero states := ⟨hz⟩
    let obs : Fin states → Fin states := relabel observation
    let ret : Fin states → Bool := fun i => retained[i.1]!
    match hfind : findCollision (enumOf states) obs ret with
    | some p =>
        let _ : ¬ Knowable obs ret := not_knowable_of_findCollision_eq_some hfind
        pure [
          "verdict: REMOVAL IS NOT DETECTABLE FROM THIS EVIDENCE",
          s!"witness: worlds {p.1.1} and {p.2.1} expose the same observation and differ in whether the fact was retained",
          "  so no procedure on this evidence decides whether removal happened",
          "certified by: AISafetyAtlas.Knowledge.Check.not_knowable_of_findCollision_eq_some",
          "SCOPE: this is evidence-relative and world-set-relative. It says the",
          "  released evidence does not distinguish the two worlds you listed.",
          "  It is NOT a proof that the fact is gone from the weights, and a richer",
          "  probe, or a world you did not list, may separate them."
        ]
    | none =>
        let _ : Knowable obs ret :=
          knowable_of_findCollision_eq_none (enumOf_complete states) hfind
        pure [
          "verdict: THE EVIDENCE STILL DETERMINES WHETHER THE FACT WAS RETAINED",
          s!"searched: every ordered pair of the {states} worlds",
          "  a decoder on the observation recovers retention, so removal is detectable",
          "  and an unlearning claim made against this evidence is refutable by it",
          "certified by: AISafetyAtlas.Knowledge.Check.knowable_of_findCollision_eq_none"
        ]

/-- `kind: "membership"` — can it be verified what a model was trained on?

Reuel, Bucknall et al. Open Problem 45: *"How can it be verified that a model
was (not) trained on a given dataset?"*

The same search as `unlearning`, asked by the other party. `observation` is what
a verifier can measure; `included` says whether the dataset was in the training
set. A collision is the **auditor's** failure here and the developer's privacy,
which is why it gets its own verdict text. -/
private def runMembership (j : Json) : Except String (List String) := do
  let states ← natField j "states"
  if hz : states = 0 then
    throw "a membership model needs at least one world"
  else
    let observation ← natArray j "observation" states
    let included ← boolArray j "included" states
    haveI : NeZero states := ⟨hz⟩
    let obs : Fin states → Fin states := relabel observation
    let inc : Fin states → Bool := fun i => included[i.1]!
    match hfind : findCollision (enumOf states) obs inc with
    | some p =>
        let _ : ¬ Knowable obs inc := not_knowable_of_findCollision_eq_some hfind
        pure [
          "verdict: MEMBERSHIP CANNOT BE VERIFIED FROM THIS EVIDENCE",
          s!"witness: worlds {p.1.1} and {p.2.1} measure identically and differ in whether the dataset was used",
          "  no verification procedure on this evidence decides it, however it is built",
          "certified by: AISafetyAtlas.Knowledge.Check.not_knowable_of_findCollision_eq_some",
          "THE SAME COLLISION IS THE SUCCESS CONDITION OF kind 'unlearning'.",
          "  Which party it favours is not a property of the mathematics."
        ]
    | none =>
        let _ : Knowable obs inc :=
          knowable_of_findCollision_eq_none (enumOf_complete states) hfind
        pure [
          "verdict: MEMBERSHIP IS DETERMINED BY THIS EVIDENCE",
          s!"searched: every ordered pair of the {states} worlds",
          "  a decoder exists; this does NOT say it is computable or cheap",
          "certified by: AISafetyAtlas.Knowledge.Check.knowable_of_findCollision_eq_none",
          "  decoder existence and decidability are different questions --",
          "  see AISafetyAtlas.Computability.rice_code_iff"
        ]

/-- `kind: "access"` — does a proposed redaction preserve the audit question?

Reuel, Bucknall et al. Open Problems 30 and 31: *"How can data access be
structured so as to preserve privacy while enabling meaningful auditing?"* and
its privacy-preserving-ML counterpart.

Three verdicts rather than two, because the practitioner's decision has three
outcomes. `full` is what the auditor would see at the access level being
narrowed; `released` is what the proposal would actually hand over; `question`
is what the audit has to settle. If the question already fails at full access,
the redaction is not what broke it -- and reporting that as a redaction failure
would send the reader to fix the wrong thing. -/
private def runAccess (j : Json) : Except String (List String) := do
  let states ← natField j "states"
  if hz : states = 0 then
    throw "an access model needs at least one state"
  else
    let full ← natArray j "full" states
    let released ← natArray j "released" states
    let question ← natArray j "question" states
    haveI : NeZero states := ⟨hz⟩
    let fullObs : Fin states → Fin states := relabel full
    let relObs : Fin states → Fin states := relabel released
    let q : Fin states → Fin states := relabel question
    let fullFind := findCollision (enumOf states) fullObs q
    let relFind := findCollision (enumOf states) relObs q
    match fullFind, relFind with
    | some p, _ =>
        pure [
          "verdict: THE QUESTION FAILS ALREADY AT FULL ACCESS",
          s!"witness: states {p.1.1} and {p.2.1} are identical even at the wider access level",
          "  the redaction is not what breaks this audit, and narrowing access",
          "  costs nothing here because there was nothing to lose",
          "certified by: AISafetyAtlas.Knowledge.Check.not_knowable_of_findCollision_eq_some",
          "  the informativeness order: AISafetyAtlas.Knowledge.Access.whiteBox_determines_blackBox"
        ]
    | none, some p =>
        pure [
          "verdict: THE REDACTION DESTROYS THE AUDIT QUESTION",
          s!"witness: states {p.1.1} and {p.2.1} are separated at full access and identical after release",
          "  so the question is answerable in principle and not from what is handed over,",
          "  and no methodology over the released view recovers it -- adaptive probing,",
          "  unbounded queries and any statistic are all functions of this evidence",
          "certified by: AISafetyAtlas.Knowledge.Access.no_blackBox_methodology",
          "  the witness pair is the deliverable of AISafetyAtlas.Knowledge.Access.exists_indistinguishable_behaviour"
        ]
    | none, none =>
        pure [
          "verdict: THE REDACTION PRESERVES THE AUDIT QUESTION",
          s!"searched: every ordered pair of the {states} states, at both access levels",
          "  the released view already determines the answer, so the wider access",
          "  buys nothing FOR THIS QUESTION -- it may buy something for another",
          "certified by: AISafetyAtlas.Knowledge.Check.knowable_of_findCollision_eq_none"
        ]

/-- `kind: "enforcement"` — can this rule bind, given what the log records?

Reuel, Bucknall et al. Open Problems 90 and 91: reliably detecting a dual-use
capability request, and gating on authorization.

The obstruction is a forbidden act and a permitted act that the log cannot tell
apart: no response function sanctions the first and spares the second, whatever
the response type. The **positive** answer is the unusual one in this program --
a clean search returns the monitoring rule itself, already proved correct, rather
than a verdict about monitoring rules. -/
private def runEnforcement (j : Json) : Except String (List String) := do
  let acts ← natField j "acts"
  if hz : acts = 0 then
    throw "a regime needs at least one act"
  else
    let logRaw ← natArray j "log" acts
    let forbiddenRaw ← boolArray j "forbidden" acts
    let permittedRaw ← boolArray j "permitted" acts
    haveI : NeZero acts := ⟨hz⟩
    let observe : Fin acts → Nat := fun e => logRaw[e.1]!
    let forbidden : Fin acts → Bool := fun e => forbiddenRaw[e.1]!
    let permitted : Fin acts → Bool := fun e => permittedRaw[e.1]!
    let conflicted := (List.finRange acts).filter fun e => forbidden e && permitted e
    let header :=
      if conflicted.isEmpty then []
      else [s!"note: {conflicted.length} act(s) are both permitted and forbidden; the rule is inconsistent there"]
    match hfind : AISafetyAtlas.Sovereignty.Enforcement.findUnenforceable
        (List.finRange acts) observe forbidden permitted with
    | some p =>
        let _ := AISafetyAtlas.Sovereignty.Enforcement.not_enforces_of_findUnenforceable_eq_some hfind
        pure (header ++ [
          "verdict: THIS RULE CANNOT BE ENFORCED",
          s!"witness: act {p.1.1} is forbidden, act {p.2.1} is permitted, and the log records {observe p.1} for both",
          "  no response function sanctions the first and spares the second,",
          "  for ANY response type -- this is not a statement about the sanctions considered",
          "certified by: AISafetyAtlas.Sovereignty.Enforcement.not_enforces_of_findUnenforceable_eq_some",
          "  the obstruction: AISafetyAtlas.Sovereignty.Enforcement.unenforceable_of_indistinguishable",
          "the repair is the LOG, not the rule and not the penalty"
        ])
    | none =>
        let flagged := ((List.finRange acts).filter fun e =>
          AISafetyAtlas.Sovereignty.Enforcement.sanctionOf
            (List.finRange acts) observe forbidden (observe e)).map fun e => observe e
        let distinctFlagged := flagged.foldl (fun seen v => if seen.contains v then seen else seen ++ [v]) []
        pure (header ++ [
          "verdict: ENFORCEABLE, AND HERE IS THE RULE",
          s!"sanction exactly these log values: {distinctFlagged}",
          "  and treat every other value as benign",
          "  this rule is proved to sanction every forbidden act and spare every permitted one",
          "certified by: AISafetyAtlas.Sovereignty.Enforcement.enforces_sanctionOf_of_findUnenforceable_eq_none",
          "  the rule itself: AISafetyAtlas.Sovereignty.Enforcement.sanctionOf",
          "SCOPE: over the acts listed. An act outside this enumeration is one the rule never saw."
        ])

/-- `kind: "shield"` — synthesise a runtime safety envelope and return the controller.

Reuel, Bucknall et al. Open Problem 64: *"How can the implementation of safety
measures be verified at deployment?"* The shape is the shield-synthesis one of
Bloem et al. 2015 and Humphrey et al. 2019.

This is the only kind here whose answer is an artifact rather than a verdict. The
iteration that proposes the envelope is **untrusted**; what is certified is the
result, by two decidable checks and `subset_safetyKernel_of_isShield`. So a
smaller envelope is still correct — it refuses more often than it must — and an
empty one is not a finding that the system cannot be shielded. -/
private def runShield (j : Json) : Except String (List String) := do
  let states ← natField j "states"
  let actions ← natField j "actions"
  let answers ← natField j "answers"
  if states = 0 then throw "a shield model needs at least one state"
  else if hm : actions = 0 then throw "a controller with no actions has nothing to choose"
  else if hk : answers = 0 then throw "an environment with no answers is not adversarial"
  else
    let cube ← natCube j "step" states actions answers
    let safeRaw ← boolArray j "safe" states
    for block in cube do
      for row in block do
        for v in row do
          if v ≥ states then
            throw s!"'step' names state {v} but the model declares {states}"
    haveI : NeZero actions := ⟨hm⟩
    haveI : NeZero answers := ⟨hk⟩
    let table : Fin states → Fin actions → Fin answers → Fin states :=
      fun s a b =>
        let raw := ((cube[s.1]!)[a.1]!)[b.1]!
        if h : raw < states then ⟨raw, h⟩ else s
    let V : Fin states → Bool := fun s => safeRaw[s.1]!
    let W := AISafetyAtlas.Sovereignty.SafetyGame.shieldCandidate table V
    let kept := (List.finRange states).filter fun s => W s
    let unsafeDropped := (List.finRange states).filter fun s => V s && !(W s)
    if h : AISafetyAtlas.Sovereignty.SafetyGame.IsShield table V W then
      let _ := AISafetyAtlas.Sovereignty.SafetyGame.subset_safetyKernel_of_isShield h
      if kept.isEmpty then
        pure [
          "verdict: NO ENVELOPE CERTIFIED",
          "  every safe state was dropped: from each of them the environment has an",
          "  answer that leaves the safe set whatever the controller does",
          "  this is NOT a proof that no shield exists -- completeness is not claimed",
          "certified by: the certificate is empty, which passes vacuously"
        ]
      else
        let rule := kept.map fun s =>
          s!"    state {s.1} -> action {(AISafetyAtlas.Sovereignty.SafetyGame.shieldAction table W s).1}"
        pure ([
          "verdict: SHIELD CERTIFIED",
          s!"envelope: {kept.length} of {states} states, holding forever against every answer",
          s!"  dropped from the safe set: {unsafeDropped.map (fun s => s.1)}",
          "  the controller:"
        ] ++ rule ++ [
          "certified by: AISafetyAtlas.Sovereignty.SafetyGame.subset_safetyKernel_of_isShield",
          "  and AISafetyAtlas.Sovereignty.SafetyGame.exists_maintaining_of_isShield,",
          "  which turns membership into a positional controller holding for all time",
          "SCOPE: the search is untrusted and only the certificate is checked, so the",
          "  envelope may be smaller than the largest one. Smaller is safe, not wrong."
        ])
    else
      pure [
        "verdict: THE CANDIDATE DID NOT CHECK",
        "  the iteration budget was too small to reach a self-closed set",
        "  this is a limitation of the search, not a finding about the system",
        "  the check that failed: AISafetyAtlas.Sovereignty.SafetyGame.IsShield"
      ]

/-- `kind: "conformity"` — does passing the checklist mean the system can be run?

The operator picks a row of the outcome table and the environment picks a column,
so a row's footprint is what that operating policy still admits. The two searches
are run separately and reported separately, because the whole point is that they
can disagree. -/
private def runConformity (j : Json) : Except String (List String) := do
  let outcomes ← natField j "outcomes"
  let policies ← natField j "policies"
  let environments ← natField j "environments"
  if ho : outcomes = 0 then throw "a conformity model needs at least one outcome"
  else if policies = 0 then throw "an operator with no policies has nothing to commit to"
  else if hq : environments = 0 then
    throw "an environment with no moves makes every footprint a point"
  else
    let rows ← natTable j "outcome" policies environments
    for row in rows do
      for v in row do
        if v ≥ outcomes then
          throw s!"'outcome' names outcome {v} but the model declares {outcomes}"
    let reqRaw ← match (← field j "requirements").getArr? with
      | .ok a => pure a
      | .error _ => throw "field 'requirements' must be an array of arrays"
    if reqRaw.isEmpty then throw "a checklist with no requirements certifies nothing"
    let reqs ← reqRaw.toList.mapM fun r => do
      let entries ← match r.getArr? with
        | .ok a => pure a
        | .error _ => throw "each requirement must be an array of booleans, one per outcome"
      if entries.size ≠ outcomes then
        throw s!"a requirement has {entries.size} entries but the model declares {outcomes} outcomes"
      entries.mapM fun v =>
        match v.getBool? with
        | .ok b => .ok b
        | .error _ => .error "requirements must contain booleans"
    haveI : NeZero environments := ⟨hq⟩
    let out : Fin policies → Fin environments → Fin outcomes := fun a jx =>
      let raw := (rows[a.1]!)[jx.1]!
      if h : raw < outcomes then ⟨raw, h⟩ else ⟨0, Nat.pos_of_ne_zero ho⟩
    let reqFns : List (Fin outcomes → Bool) := reqs.map fun r => fun x => r[x.1]!
    let passes := AISafetyAtlas.Sovereignty.Conformity.passesEachB out reqFns
    let operable := AISafetyAtlas.Sovereignty.Conformity.operableB out reqFns
    let failing := (List.range reqs.length).filter fun i =>
      !((List.finRange policies).any fun a =>
        AISafetyAtlas.Sovereignty.Conformity.footprintSubset out (reqFns[i]!) a)
    match passes, operable with
    | true, false =>
        pure [
          "verdict: PASSES EVERY ITEM, AND CANNOT BE RUN",
          s!"  each of the {reqs.length} requirements has a policy that meets it",
          "  and no single policy meets them all",
          "  a certificate of this shape is evidence about the assessment, not the deployment",
          "certified by: AISafetyAtlas.Sovereignty.Conformity.demandwise_of_passesEachB",
          "  and AISafetyAtlas.Sovereignty.Conformity.not_demandwiseUniform_of_operableB_eq_false",
          "  the gap: AISafetyAtlas.Sovereignty.Conformity.passes_every_check_and_not_operable"
        ]
    | true, true =>
        pure [
          "verdict: PASSES, AND ONE POLICY SERVES THE WHOLE CATALOGUE",
          "  the checklist and the deployment agree here",
          "certified by: AISafetyAtlas.Sovereignty.Conformity.demandwise_of_passesEachB",
          "  operability is REPORTED and not certified by this program:",
          "  only the refutation direction is proved, see the module header"
        ]
    | false, _ =>
        pure [
          "verdict: THE CHECKLIST ITSELF DOES NOT PASS",
          s!"  requirement(s) {failing} have no policy that meets them at all",
          "  this is a finding about those requirements, before any question of operability",
          "  no certificate is claimed: only the passing direction is proved"
        ]

/-- `kind: "fairness"` — which of calibration and the two balances must fail?

Kleinberg, Mullainathan and Raghavan's Theorem 1.1 as carried by
`AISafetyAtlas.Fairness.RiskAssignment`, read through the citation form in
`AISafetyAtlas.Fairness.Tradeoff`. Base rates are given as a positive count and a
total per group, so the comparison is exact. -/
private def runFairness (j : Json) : Except String (List String) := do
  let pos0 ← natField j "positives_group0"
  let tot0 ← natField j "total_group0"
  let pos1 ← natField j "positives_group1"
  let tot1 ← natField j "total_group1"
  let perfect ← match (← field j "perfect_prediction_available").getBool? with
    | .ok b => pure b
    | .error _ => throw "field 'perfect_prediction_available' must be a boolean"
  if tot0 = 0 || tot1 = 0 then throw "a group with no members has no base rate"
  else if pos0 = 0 || pos1 = 0 then
    throw "Theorem 1.1 assumes each group has a positive class; a group with none is outside it"
  else if pos0 ≥ tot0 || pos1 ≥ tot1 then
    throw "Theorem 1.1 assumes each positive class is a proper subset of its group"
  else
    let equal := pos0 * tot1 == pos1 * tot0
    if equal then
      pure [
        "verdict: EQUAL BASE RATES -- THE THEOREM PERMITS ALL THREE",
        s!"  {pos0}/{tot0} and {pos1}/{tot1} are the same rate",
        "  calibration and both balances are not excluded here",
        "  this is NOT a finding that they are achievable: the theorem's escape",
        "  hatch is open, and nothing here builds an assignment through it"
      ]
    else if perfect then
      pure [
        "verdict: UNEQUAL BASE RATES, BUT PERFECT PREDICTION IS DECLARED AVAILABLE",
        s!"  {pos0}/{tot0} differs from {pos1}/{tot1}",
        "  the other escape is the one in play, and it is an empirical claim about",
        "  the task that this program takes from the input and does not check"
      ]
    else
      pure [
        "verdict: NO RISK ASSIGNMENT SATISFIES ALL THREE",
        s!"  base rates {pos0}/{tot0} and {pos1}/{tot1} differ, and no perfect predictor exists",
        "  so calibration within groups, balance for the positive class and balance",
        "  for the negative class are JOINTLY unsatisfiable -- over every assignment,",
        "  not merely the ones anyone has tried",
        "certified by: AISafetyAtlas.Fairness.cannot_have_all_three",
        "  print's own form: AISafetyAtlas.Fairness.perfect_prediction_or_equal_base_rates",
        "which condition to give up is a normative choice the mathematics is silent on"
      ]

/-- `kind: "goodhart"` — is this threshold already outside its own evidence?

`AISafetyAtlas.Goodhart.RegulatoryTarget`'s structural hypothesis is that the bar
sits above everything the evidence base exhibits. This decides that hypothesis on
a given evidence base, which is the one thing a compiling theorem cannot do for
itself. -/
private def runGoodhart (j : Json) : Except String (List String) := do
  let observed ← natList j "observed_indicator"
  let threshold ← natField j "threshold"
  if observed.isEmpty then throw "an evidence base with no systems fits nothing"
  else
    let ceiling := observed.foldl Nat.max 0
    if ceiling < threshold then
      pure [
        "verdict: EXTREMAL REGIME -- THE BAR IS OUTSIDE ITS OWN EVIDENCE",
        s!"  the evidence base tops out at {ceiling}; the bar is {threshold}",
        "  every certified system is one the evidence never covered, and the true",
        "  risk at those systems is unconstrained by ANY amount, uniformly",
        "certified by: AISafetyAtlas.Goodhart.RegulatoryTarget.certified_systems_were_never_examined",
        "  and AISafetyAtlas.Goodhart.RegulatoryTarget.risk_unconstrained_on_certified",
        "raising the bar makes this worse, not better:",
        "  AISafetyAtlas.Goodhart.RegulatoryTarget.raising_the_bar_does_not_help",
        "the repair is a wider evidence base, not a higher number"
      ]
    else
      pure [
        "verdict: THE BAR SITS INSIDE THE EVIDENCE BASE",
        s!"  the evidence base reaches {ceiling}; the bar is {threshold}",
        "  the extremal argument does not apply, and this module says nothing further",
        "  this is NOT a finding that the rule is sound",
        "  what IS available inside the evidence base:",
        "  AISafetyAtlas.Goodhart.RegulatoryTarget.risk_bounded_on_evidence_base"
      ]

/-- `kind: "refusal"` — does your safety suite admit a do-nothing pass?

A system that always returns the same thing retains **every** safety property
that outcome satisfies, at every coalition, with no hypothesis about the system
beyond inertness. If the suite also carries a request that outcome misses, then a
system that refuses everything passes the suite and serves nobody.

The defect is in the **suite**, and deciding it needs no system at all. -/
private def runRefusal (j : Json) : Except String (List String) := do
  let outcomes ← natField j "outcomes"
  if outcomes = 0 then throw "a suite over no outcomes constrains nothing"
  else
    let readFamily (name : String) : Except String (List (Array Bool)) := do
      let raw ← match (← field j name).getArr? with
        | .ok a => pure a
        | .error _ => throw s!"field '{name}' must be an array of arrays"
      raw.toList.mapM fun r => do
        let entries ← match r.getArr? with
          | .ok a => pure a
          | .error _ => throw s!"each entry of '{name}' must be an array of booleans"
        if entries.size ≠ outcomes then
          throw s!"an entry of '{name}' has {entries.size} values but the model declares {outcomes} outcomes"
        entries.mapM fun v =>
          match v.getBool? with
          | .ok b => .ok b
          | .error _ => .error s!"'{name}' must contain booleans"
    let safetyRaw ← readFamily "safety"
    let requestsRaw ← readFamily "requests"
    if safetyRaw.isEmpty then throw "a safety suite with no properties passes everything"
    if requestsRaw.isEmpty then
      throw "with no requests, refusing is correct and this check does not apply"
    let safety : List (Fin outcomes → Bool) := safetyRaw.map fun P => fun x => P[x.1]!
    let requests : List (Fin outcomes → Bool) := requestsRaw.map fun R => fun x => R[x.1]!
    if h : AISafetyAtlas.Sovereignty.Refusal.admitsRefusal safety requests = true then
      let _ := AISafetyAtlas.Sovereignty.Refusal.exists_refusal_hole_of_admitsRefusal h
      let holes := (List.finRange outcomes).filter
        (AISafetyAtlas.Sovereignty.Refusal.isRefusalHole safety requests)
      pure [
        "verdict: THE SUITE ADMITS A DO-NOTHING PASS",
        s!"witness outcome(s): {holes.map (fun x => x.1)}",
        "  a system that always returns one of these retains EVERY safety property",
        "  in the suite, at every coalition, and meets no request that outcome misses",
        "certified by: AISafetyAtlas.Sovereignty.Refusal.exists_refusal_hole_of_admitsRefusal",
        "  the obstruction: AISafetyAtlas.Sovereignty.Refusal.safety_suite_admits_a_refusal",
        "the defect is in the SUITE, and no system had to be examined to find it"
      ]
    else
      pure [
        "verdict: NO DO-NOTHING PASS",
        s!"searched: every one of the {outcomes} outcomes",
        "  every outcome either fails some safety property or serves every request",
        "certified by: AISafetyAtlas.Sovereignty.Refusal.not_exists_refusal_hole_of_admitsRefusal_eq_false",
        "this rules out ONE way for a suite to be vacuous and says nothing else about it"
      ]

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
  | "regulation" => runRegulation j
  | "unlearning" => runUnlearning j
  | "membership" => runMembership j
  | "access" => runAccess j
  | "enforcement" => runEnforcement j
  | "shield" => runShield j
  | "conformity" => runConformity j
  | "fairness" => runFairness j
  | "goodhart" => runGoodhart j
  | "refusal" => runRefusal j
  | other =>
      throw s!"unknown kind '{other}'; this build reads 'knowability', 'coalition', 'device', 'variety', 'regulation', 'unlearning', 'membership', 'access', 'enforcement', 'shield', 'conformity', 'fairness', 'goodhart' and 'refusal'"

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
