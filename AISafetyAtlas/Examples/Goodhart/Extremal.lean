module

public import AISafetyAtlas.Goodhart.Extremal

/-!
# Worked models for Extremal Goodhart

The library statements quantify over a state type, a proxy, an observed region, a
learned relationship and a tolerance. This file inhabits them twice, once for
each sub-variant, using the two examples print itself gives.

## Model insufficiency: print's underfitted polynomial

Print's machine-learning example is underfitting -- "a relationship is assumed to
be a low degree polynomial because higher order polynomial terms are small in the
observed region. Selection on the basis of the approximated metric moves towards
regions where the higher-order terms are more important."

The state is a real number, the proxy is the state itself, and the observed
region is `Set.Icc (-1) 1`. The learned relationship is the identity -- the
linear fit. `underfitGoal` is the cubic the fit dropped: `x + x ^ 3 / 10`. On
the observed region the cubic term never exceeds `1 / 10` in size, so the linear
fit is accurate to `1 / 10` there and so is the identity; the two candidate goals
are indistinguishable to a regulator who only ever looked inside `[-1, 1]` at
that tolerance. At the threshold `10` the state `10` is selected, and there the
two goals differ by `100` -- a thousand times the tolerance that the observations
allowed.

That pair is print's own, and it is why the library theorem's conclusion is worth
having. It is *not* an instance of that conclusion, which asks for exact
agreement on the observed region rather than agreement to within `ε`;
`underdetermined_at_ten` applies the theorem to the same data to produce the
exact-agreement witness, which exists for every displacement.

## Change in regime: print's wind-speed instrument

Print's example is an instrument that reads low above its design tolerance --
"wind-speed measurements may be systematically biased downwards when the
wind-speed exceeds the design tolerances of the instruments". Take the tolerance
at `30`, no bias below it and a bias of `5` above: `regimeGoal 30 0 5`. At a
measured `20` the true speed is `20`; at a measured `40` it is `45`. A regulator
who fitted the relationship on measurements below `30`, correctly, and then
selects for measurements above `30`, is wrong by exactly `5` on every selected
state -- and no amount of further data below `30` would have revealed it.
-/

namespace AISafetyAtlas.Examples.Goodhart.Extremal

open AISafetyAtlas.Goodhart.Extremal
open Set

/-! ## Model insufficiency -/

/-- The proxy: the state itself. -/
@[expose] public def proxy : ℝ → ℝ := fun x => x

/-- The learned relationship: the linear fit, which is the identity here. -/
@[expose] public def linearFit : ℝ → ℝ := fun m => m

/-- The goal print's linear fit dropped a term of: a cubic whose coefficient is
small enough that the term is invisible at the observed tolerance. -/
@[expose] public noncomputable def underfitGoal : ℝ → ℝ := fun x => x + x ^ 3 / 10

/-- The observed region: print's "initial region", where the fit was made. -/
@[expose] public def observed : Set ℝ := Icc (-1) 1

/-- The cubic goal fits the linear relationship to `1 / 10` on the observed
region: the dropped term is bounded by the tolerance exactly there. -/
public theorem underfitGoal_fitsOn :
    FitsOn observed proxy underfitGoal linearFit (1 / 10) := by
  intro x hx
  obtain ⟨hx1, hx2⟩ := hx
  have h : underfitGoal x - linearFit (proxy x) = x ^ 3 / 10 := by
    simp only [underfitGoal, linearFit, proxy]; ring
  rw [h, abs_le]
  constructor <;> nlinarith [sq_nonneg x, sq_nonneg (x - 1), sq_nonneg (x + 1)]

/-- The linear fit read as a goal in its own right fits itself exactly, so it
also fits within the same tolerance. The regulator's evidence cannot separate
this from `underfitGoal`. -/
public theorem linearFit_fitsOn :
    FitsOn observed proxy linearFit linearFit (1 / 10) := by
  intro x _
  simp [linearFit, proxy]

/-- At the selected state the two goals the evidence could not separate differ by
`100`, a thousand times the tolerance that permitted them both. -/
public theorem underfitGoal_sub_linearFit_at_ten :
    underfitGoal 10 - linearFit 10 = 100 := by
  simp only [underfitGoal, linearFit]
  norm_num

/-- The selection event is not empty: the state `10` clears the threshold `10`.
Without this the theorems below hold of nothing.

Routed through `mem_selectedAt` by name rather than closed by `simp [selectedAt]`.
The two are the same proof — `mem_selectedAt` is `@[simp]` and is what `simp`
would have used — but a lemma reached only through a simp set is never named, so
the witness-debt report cannot see that anything exercises it. A second theorem
restating the characterization was added here for that reason on 2026-09-15 and
has been removed: writing a declaration so a string appears in a grep is the one
move that makes the number stop meaning what it says. -/
public theorem ten_mem_selectedAt : (10 : ℝ) ∈ selectedAt proxy 10 :=
  mem_selectedAt.mpr (by norm_num [proxy])

/-- Selection at threshold `10` leaves the observed region, because the proxy is
bounded by `1` there. This discharges the hypothesis of
`fits_underdetermined_off_observed` on this data. -/
public theorem selectedAt_disjoint_observed :
    Disjoint (selectedAt proxy 10) observed := by
  refine selected_disjoint_observed proxy observed (b := 1) (fun x hx => ?_) (by norm_num)
  exact hx.2

/-- The library theorem at print's data: whatever the goal is, so long as it fits
the linear relationship on `[-1, 1]` to within `1 / 10`, there is a second goal
that fits just as well, is *equal* to it on the whole of `[-1, 1]`, and is off by
`1000` at every state the threshold `10` selects. -/
public theorem underdetermined_at_ten :
    ∃ G', FitsOn observed proxy G' linearFit (1 / 10) ∧
      EqOn underfitGoal G' observed ∧
      ∀ s ∈ selectedAt proxy 10, underfitGoal s - G' s = 1000 :=
  fits_underdetermined_off_observed proxy linearFit (1 / 10)
    selectedAt_disjoint_observed underfitGoal underfitGoal_fitsOn 1000

/-! ## Change in regime -/

/-- Print's wind-speed instrument: unbiased at or below its design tolerance of
`30`, and reading `5` low above it. -/
@[expose] public noncomputable def windGoal : ℝ → ℝ := regimeGoal 30 0 5

/-- Below the tolerance the instrument is right. -/
public theorem windGoal_twenty : windGoal 20 = 20 := by
  simp only [windGoal, regimeGoal_eq_of_le 30 0 5 (by norm_num : (20:ℝ) ≤ 30)]
  norm_num

/-- Above it the true speed exceeds the reading by the bias. -/
public theorem windGoal_forty : windGoal 40 = 45 := by
  simp only [windGoal, regimeGoal_eq_of_lt 30 0 5 (by norm_num : (30:ℝ) < 40)]
  norm_num

/-- A measured `40` clears a threshold of `31`, so the selection event of the
regime model is not empty either. -/
public theorem forty_mem_selectedAt : (40 : ℝ) ∈ selectedAt proxy 31 := by
  simp [selectedAt, proxy]
  norm_num

/-- The extrapolation error at that selected state, exactly: predicting from the
regime that was observed gives `40`, the truth is `45`, and the gap is the
difference of the two offsets. -/
public theorem wind_prediction_error :
    (proxy 40 + 0) - regimeGoal 30 0 5 (proxy 40) = 0 - 5 :=
  regime_prediction_error proxy 30 0 5 (by norm_num : (30:ℝ) < 31) forty_mem_selectedAt

/-- The library's regime underdetermination at print's data: a second instrument
model, agreeing with this one on every reading at or below `30` and fitting the
same relationship there exactly, reads `5` further off on every selected state.
Data below the tolerance cannot choose between them. -/
public theorem wind_underdetermines :
    ∃ G', FitsOn {s : ℝ | proxy s ≤ 30} proxy G' (fun m => m + 0) 0 ∧
      EqOn (fun s => regimeGoal 30 0 5 (proxy s)) G' {s : ℝ | proxy s ≤ 30} ∧
      ∀ s ∈ selectedAt proxy 31, regimeGoal 30 0 5 (proxy s) - G' s = 5 :=
  regime_underdetermines proxy 30 0 5 (by norm_num : (30:ℝ) < 31) 5

/-- And the regime model's own escape: every threshold above the boundary selects
only readings print's fitted regime never covered. -/
public theorem wind_selected_disjoint :
    Disjoint (selectedAt proxy 31) {s : ℝ | proxy s ≤ 30} :=
  regime_selected_disjoint_observed proxy 30 (by norm_num : (30:ℝ) < 31)

end AISafetyAtlas.Examples.Goodhart.Extremal
