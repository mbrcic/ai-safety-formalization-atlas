module

public import AISafetyAtlas.Control.RegulationCheck

/-!
# Worked tables for the regulation checker

Each of these is a satisfiability witness, and that is the whole point rather
than a side effect. `Control.ashby_variety_ge` quantifies over tables whose every
response column is injective, and nothing in the build tests that any table is
one — the theorem would compile, pass the axiom audit, and be transcribed
correctly if no such table existed. These exhibit some.

The tables are also the fixtures `scripts/check_atlas_check.sh` runs the
`kind: "regulation"` checker against, so the executable and the proofs are
checked to agree on the same objects rather than on two descriptions of them.

## What each one is for

| Table | Shape | Shows |
|---|---|---|
| `latinSquare` | 3 disturbances, 3 responses, 3 outcomes | the hypothesis is satisfiable, and the bound `3/3 ≤ 3` is slack |
| `identityColumn` | 4 × 1 | one response, so the bound `4/1 ≤ 4` is **tight**: the regulator has no repertoire and every disturbance shows through |
| `wideTable` | 2 × 4 | more responses than disturbances, so the bound is below 1 and says nothing; the hypothesis still holds |
| `repeatedColumn` | 2 × 1 | the hypothesis **fails**, and the bound is false here — a `false` verdict is not a clearance |

The third and fourth are the ones worth keeping. A witness file that only
contained tables where the bound is interesting would leave the reader unable to
tell a vacuous region from an informative one.
-/

namespace AISafetyAtlas.Examples.Control

open AISafetyAtlas.Control

/-! ## A Latin square: the hypothesis holds and the bound is slack -/

/-- Three disturbances, three responses, outcome `d + r` in `ZMod 3` shape. -/
@[expose] public def latinSquare : Fin 3 → Fin 3 → Fin 3 :=
  fun d r => ⟨(d.val + r.val) % 3, Nat.mod_lt _ (by norm_num)⟩

/-- The column condition holds: each response is a bijection on disturbances. -/
public theorem latinSquare_columnsInjective : columnsInjective latinSquare = true := by
  decide

/-- Every response is available, and the strategy picks the first. -/
@[expose] public def latinStrategy : Fin 3 → Fin 3 := fun _ => 0

/-- Three outcomes are admitted, so Ashby's `3/3 ≤ 3` holds with room to spare. -/
public theorem latinSquare_achievedVariety :
    achievedVariety latinSquare latinStrategy = 3 := by
  decide

/-! ## One response: the bound is tight -/

/-- Four disturbances, a single response, four distinct outcomes. -/
@[expose] public def identityColumn : Fin 4 → Fin 1 → Fin 4 := fun d _ => d

public theorem identityColumn_columnsInjective : columnsInjective identityColumn = true := by
  decide

/--
**The bound is attained.** With one response the regulator has no repertoire, so
every disturbance reaches the outcome: `4/1 ≤ 4` with equality. This is the case
Ashby's slogan is about.
-/
public theorem identityColumn_achievedVariety :
    achievedVariety identityColumn (fun _ => 0) = 4 := by
  decide

/-! ## More responses than disturbances: the hypothesis holds and says little -/

/-- Two disturbances, four responses. The bound is `2/4`, below one outcome. -/
@[expose] public def wideTable : Fin 2 → Fin 4 → Fin 2 := fun d _ => d

public theorem wideTable_columnsInjective : columnsInjective wideTable = true := by
  decide

/--
The checker reports a `true` verdict here and the bound it certifies is `1/2 ≤ 1`
— satisfied by any table at all. A `true` verdict is a statement about the
hypothesis, not a measure of how much the law constrains this instance.
-/
public theorem wideTable_achievedVariety :
    achievedVariety wideTable (fun _ => 0) = 2 := by
  decide

/-! ## A repeated column: the hypothesis fails -/

/-- Two disturbances collapsed onto one outcome under the only response. -/
@[expose] public def repeatedColumn : Fin 2 → Fin 1 → Fin 1 := fun _ _ => 0

public theorem repeatedColumn_columnsInjective : columnsInjective repeatedColumn = false := by
  decide

/--
And the bound genuinely fails here, which is why the checker refuses to read a
`false` verdict as a clearance: one outcome is admitted where `2/1` would be
demanded.
-/
public theorem repeatedColumn_bound_fails :
    ¬ ((2 : ℚ) / 1 ≤ achievedVariety repeatedColumn (fun _ => 0)) := by
  have hone : achievedVariety repeatedColumn (fun _ => 0) = 1 := by decide
  rw [hone]
  norm_num

end AISafetyAtlas.Examples.Control
