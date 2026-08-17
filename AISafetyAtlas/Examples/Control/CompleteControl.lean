module

public import AISafetyAtlas.Control.CompleteControl

/-!
# Ashby's Table 11/3/1, and his own answer to §11/14's Ex. 1

W. Ross Ashby, *An Introduction to Cybernetics*, Table 11/3/1 (printed p. 202)
and the answers to §11/14's exercises (printed p. 285, absent from the pinned
scan and read from the Martino Fine Books 2015 reprint — see
`docs/provenance/ashby-requisite-variety.md`).

Table 11/3/1 is the table the whole chapter is played on:

```
        R
     α  β  γ
 1   b  a  c
D2   a  c  b
 3   c  b  a
```

§11/14 Ex. 1 asks the reader to *"form the set of transformations, with c as
parameter, that must be used by R if C is to have complete control over the
outcome"*, and Ashby's answer is

```
     ↓   1   2   3
 a       β   α   γ
 b       α   γ   β
 c       γ   β   α
```

`ashbyControlStrategy` is that table and `ashbyControl_isPerfectRegulator` checks
it: every one of the nine entries lands the outcome on the target that indexes
its row. So Ashby's answer is right, and it is a `IsPerfectRegulator` with the
controller's dial `g` the identity — his targets *are* outcomes.

## What this example settles

The regulator uses **three** moves. Ashby's answer to Ex. 4 reasons that the
`R → T` link must carry the load from `C` *plus* the load from `D` because the
two are uncorrelated; here both loads are `log 3` and the link carries `log 3`,
not `log 9`. `ashbyControl_capacity_eq` and
`ashbyControl_capacity_lt_sum` state exactly that, so the sum in Ex. 4's answer
is not a consequence of the model — `max_channelCapacity_le_channelCapacity_regulator`
is what the model forces.

This is not a correction to Ashby's arithmetic. Ex. 4 inherits Ex. 2's `T`, which
attenuates — *"if R is constant, E will vary at 2 bits/second"* against 5
bits/second emitted at `D` — whereas Table 11/3/1 attenuates nothing: hold `R` at
`α` and the outcome still ranges over all three values. The two exercises are
about different tables. What the example shows is that the additivity is a
property of the table, not of the diagram.
-/

namespace AISafetyAtlas.Examples.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.Control
open AISafetyAtlas.InformationTheory

/-- Ashby's three-element alphabet, used for the disturbance `D = {1,2,3}`, the
regulator's move `R = {α,β,γ}` and the outcome `E = {a,b,c}` alike — the table is
square. Index `0,1,2` throughout, in Ashby's printed order. -/
public abbrev Three := Fin 3

/-- **Table 11/3/1.** `ashbyControlTable d r` is the outcome when `D` plays `d`
and `R` plays `r`; rows are `1,2,3` and columns `α,β,γ`, with outcomes `a,b,c`
as `0,1,2`. -/
@[expose] public def ashbyControlTable : Three → Three → Three
  | 0 => ![1, 0, 2]
  | 1 => ![0, 2, 1]
  | _ => ![2, 1, 0]

/-- **Ashby's answer to §11/14 Ex. 1.** `ashbyControlStrategy c d` is the move `R`
must make when the controller has set target `c` and the disturbance is `d` —
his table read with the target as parameter and `D`'s move as operand. -/
@[expose] public def ashbyControlStrategy : Three → Three → Three
  | 0 => ![1, 0, 2]
  | 1 => ![0, 2, 1]
  | _ => ![2, 1, 0]

/--
**Ashby's Ex. 1 answer is correct.** Each of the nine entries holds the outcome
at the target indexing its row, whatever the disturbance plays — the hypothesis
§11/14 argues from.
-/
public theorem ashbyControl_isPerfectRegulator :
    IsPerfectRegulator ashbyControlTable ashbyControlStrategy id := by
  unfold IsPerfectRegulator
  decide

/-- Table 11/3/1's columns separate the disturbances: it is a Latin square, so
no outcome repeats in a column. This is the chapter's standing hypothesis. -/
public theorem ashbyControlTable_columns_injective (r : Three) :
    Injective fun d => ashbyControlTable d r := by
  fin_cases r <;> decide

/--
**Complete control on Ashby's own table.** *"Table 11/3/1 enables R not only to
achieve a as outcome in spite of all D's variations; but equally to achieve b or
c at will."* Every outcome is forced by some setting, against every disturbance.
-/
public theorem ashbyControl_complete (e : Three) :
    ∃ c : Three, ∀ d : Three, ashbyControlTable d (ashbyControlStrategy c d) = e :=
  exists_strategy_forcing ashbyControl_isPerfectRegulator surjective_id e

/-- §11/14's printed compound target, *"a, b, a, c, c, a"*. -/
@[expose] public def ashbySequence : Fin 6 → Three := ![0, 1, 0, 2, 2, 0]

/--
**The compound target is produced, whatever the disturbances.** *"then that
sequence will be produced, regardless of D's values during the sequence."* The
disturbance history `ds` is arbitrary and universally quantified.
-/
public theorem ashbyControl_sequence (ds : Fin 6 → Three) :
    (fun i => ashbyControlTable (ds i) (ashbyControlStrategy (ashbySequence i) (ds i)))
      = ashbySequence :=
  seq_outcome_eq ashbyControl_isPerfectRegulator ashbySequence ds

/-- The regulator's whole repertoire on this table is three moves. -/
public theorem ashbyControl_capacity_eq : channelCapacity Three = Real.log 3 := by
  rw [channelCapacity, Fintype.card_fin]
  norm_num

/--
**Requisite variety, charged twice, and both charges met exactly.** §11/14's two
costs are live here — the regulator serves three targets and cancels three
disturbances — and Ashby's answer pays both with three moves, so the bound the
model forces is attained with nothing to spare.

Stated in capacities rather than counts because the counts are equal by
construction on a square table; what the elaborator checks is that both general
theorems apply, their hypotheses discharged by Ashby's own table.
-/
public theorem ashbyControl_max_bound :
    max (channelCapacity Three) (channelCapacity Three) ≤ channelCapacity Three :=
  max_channelCapacity_le_channelCapacity_regulator ashbyControl_isPerfectRegulator
    injective_id ashbyControlTable_columns_injective

/--
**Ex. 4's sum is not necessary.** Ashby answers that the `R → T` link must carry
the controller's load *plus* the disturbance's, *"as these two are independent
(D's values and C's not correlated)"*. On Table 11/3/1 both loads are `log 3`, so
that reasoning demands `log 9` — and `ashbyControl_isPerfectRegulator` exhibits a
perfect regulator whose entire repertoire is `log 3`.

So additivity is not forced by §11/14's diagram. It is a property of the table:
Ex. 2's `T` attenuates and Table 11/3/1 does not, which is why this is a limit on
what the general model implies rather than a correction to Ashby's arithmetic.
The bound the model does force is
`max_channelCapacity_le_channelCapacity_regulator`.
-/
public theorem ashbyControl_capacity_lt_sum :
    channelCapacity Three < Real.log 3 + Real.log 3 := by
  rw [ashbyControl_capacity_eq]
  have : (0 : ℝ) < Real.log 3 := Real.log_pos (by norm_num)
  linarith

end AISafetyAtlas.Examples.Control
