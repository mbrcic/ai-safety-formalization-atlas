module

public import AISafetyAtlas.Analysis.NullImage
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Worked examples for the null-image lemma

Two witnesses that `AISafetyAtlas.Analysis.NullImage` says something, and says
the right thing.

The first is the statement in its smallest interesting shape: a curve traced in
the plane by one parameter covers no area. The second records the sharpness of
the hypothesis `p < q` — dropping it makes the conclusion false, since the
identity map on `ℝ` is `C¹` and its range is everything.
-/

namespace AISafetyAtlas.Examples.Analysis.NullImage

open MeasureTheory AISafetyAtlas.Analysis

/-- **A one-parameter `C¹` family in the plane is null.** The diagonal line is
the smallest witness: one parameter, two ambient dimensions. -/
public theorem volume_range_diagonal_eq_zero :
    volume (Set.range fun s : Fin 1 → ℝ => (fun _ : Fin 2 => s 0)) = 0 :=
  volume_range_eq_zero_of_contDiff (contDiff_pi.2 fun _ => contDiff_apply ℝ ℝ 0) (by norm_num)

/-- **The dimension hypothesis is not decoration.** At `p = q` the conclusion
fails: the identity is `C¹` and its range is the whole space, which is not null.
This is why `volume_image_eq_zero_of_card_lt` asks for a *strict* inequality. -/
public theorem volume_range_id_ne_zero :
    volume (Set.range fun s : Fin 1 → ℝ => s) ≠ 0 := by
  rw [Set.range_id']
  haveI := isAddHaarMeasure_volume_pi (Fin 1)
  exact (isOpen_univ.measure_pos volume Set.univ_nonempty).ne'

end AISafetyAtlas.Examples.Analysis.NullImage
