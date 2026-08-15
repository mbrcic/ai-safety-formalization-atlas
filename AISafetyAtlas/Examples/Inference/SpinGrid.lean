module

public import AISafetyAtlas.Inference

/-!
# Worked model: Example 5's grid of paired spins

Wolpert 2008 Example 5 builds two devices from one grid and asserts three things
about them: that they are distinguishable, that the purple one infers the yellow
one when an agreeing and an anti-agreeing row both exist, and that the yellow one
therefore cannot infer the purple one.

The general statements are in `Inference/Existence.lean`, over an arbitrary index
pair. What is here is the half a general theorem cannot give: a grid that actually
meets the hypotheses, so none of the three statements is vacuous.

The smallest such grid is `2 × 2`. Row `0` agrees with the yellow spins and row
`1` inverts them, which is exactly the source's `i'` and `i''`.

|        | `j = 0` | `j = 1` |
|--------|---------|---------|
| purple `i = 0` | up   | down |
| purple `i = 1` | down | up   |
| yellow `i = 0` | up   | down |
| yellow `i = 1` | up   | down |
-/

namespace AISafetyAtlas.Examples.Inference.SpinGrid

open AISafetyAtlas.Inference

/-- Purple spins: row `0` copies the yellow row, row `1` inverts it. -/
public abbrev gridPurple : Fin 2 → Fin 2 → Bool := ![![true, false], ![false, true]]

/-- Yellow spins: both rows read up-then-down. -/
public abbrev gridYellow : Fin 2 → Fin 2 → Bool := ![![true, false], ![true, false]]

/-- Definition 1's surjectivity — the source's *"at least one purple spin is up
and at least one is down"*. -/
public theorem gridPurple_surjective :
    Function.Surjective fun p : Fin 2 × Fin 2 => gridPurple p.1 p.2 := by decide

/-- The same for the yellow particles. -/
public theorem gridYellow_surjective :
    Function.Surjective fun p : Fin 2 × Fin 2 => gridYellow p.1 p.2 := by decide

/-- The source's `i'`: a row where the two colours agree everywhere. -/
public theorem gridAgreeingRow : ∃ i : Fin 2, ∀ j : Fin 2, gridPurple i j = gridYellow i j :=
  ⟨0, by decide⟩

/-- The source's `i''`: a row where they disagree everywhere. -/
public theorem gridAntiRow : ∃ i : Fin 2, ∀ j : Fin 2, gridPurple i j = !(gridYellow i j) :=
  ⟨1, by decide⟩

/-- *"These two devices are distinguishable."* -/
public theorem gridDevices_distinguishable :
    Distinguishable (rowSpinDevice gridPurple gridPurple_surjective)
      (colSpinDevice gridYellow gridYellow_surjective) :=
  rowSpinDevice_distinguishable_colSpinDevice _ _ _ _

/-- *"`C_p > C_y`."* -/
public theorem gridPurple_infersDevice_gridYellow :
    InfersDevice (rowSpinDevice gridPurple gridPurple_surjective)
      (colSpinDevice gridYellow gridYellow_surjective) :=
  rowSpinDevice_infersDevice_colSpinDevice _ _ _ _ gridAgreeingRow gridAntiRow

/-- *"There cannot also be both a value `j'` and a value `j''` that the yellow
inference device can use…"* — the impossibility, on a grid that exists. -/
public theorem not_gridYellow_infersDevice_gridPurple :
    ¬ InfersDevice (colSpinDevice gridYellow gridYellow_surjective)
      (rowSpinDevice gridPurple gridPurple_surjective) :=
  not_colSpinDevice_infersDevice_rowSpinDevice _ _ _ _ gridAgreeingRow gridAntiRow

end AISafetyAtlas.Examples.Inference.SpinGrid
