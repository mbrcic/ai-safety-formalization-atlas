module

public import AISafetyAtlas.Sovereignty.Disturbance
public import AISafetyAtlas.Examples.LinearSystems.Criteria
public import Mathlib.Data.Rat.Defs

/-!
# A plant that can reach anything and cannot hold anything

`shaky` is the smallest counterexample to reading a rank condition as a
guarantee: one input coordinate, one disturbance coordinate, one state
coordinate, all of them the identity over `ℚ`.

`shaky_surjective` says its input map is onto, so it reaches every terminal
state when the disturbance is fixed -- the rank condition passes.
`shaky_not_robust` says it cannot hold the target `0` against the two
admissible disturbances `0` and `1`, because holding both would need the same
input to be `0` and `-1`.

`steady` is the other corner: the same plant with a disturbance map that is
blind, so `robustReachesEvery_of_disturbance_constant` applies and every target
is held. The difference between the two is entirely in the disturbance map, and
nothing about the input map or its rank distinguishes them.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Disturbance

open AISafetyAtlas.Sovereignty

/-- Input and disturbance both move the state one for one. -/
@[expose] public def shaky : Plant ℚ ℚ ℚ ℚ where
  drift := 0
  input := LinearMap.id
  disturbance := LinearMap.id

/-- The same plant with a disturbance that does not reach the state. -/
@[expose] public def steady : Plant ℚ ℚ ℚ ℚ where
  drift := 0
  input := LinearMap.id
  disturbance := 0

/-- **The rank condition passes**: every terminal state is reachable. -/
public theorem shaky_surjective : Function.Surjective shaky.input :=
  fun y => ⟨y, rfl⟩

/-- **And nothing is held.** Holding `0` against both admissible disturbances
would need the one precommitted input to be `0` and `-1`. -/
public theorem shaky_not_robust :
    ¬ ∃ u : ℚ, shaky.RobustInput {0, 1} 0 u := by
  rintro ⟨u, hu⟩
  have h0 : (0 : ℚ) + u + 0 = 0 := hu 0 (by simp)
  have h1 : (0 : ℚ) + u + 1 = 0 := hu 1 (by simp)
  rw [show (0 : ℚ) + u + 0 = u by ring] at h0
  rw [h0] at h1
  norm_num at h1

/-- So surjectivity of the input map does not give a robust input, which is the
whole of print's warning about the disturbance quantifier. -/
public theorem surjective_not_robust :
    Function.Surjective shaky.input ∧ ¬ ∃ u : ℚ, shaky.RobustInput {0, 1} 0 u :=
  ⟨shaky_surjective, shaky_not_robust⟩

/-- **The other corner.** A blind disturbance map annihilates every difference,
so every target is held. -/
public theorem steady_robust (z : ℚ) :
    ∃ u : ℚ, steady.RobustInput {0, 1} z u :=
  Plant.robustReachesEvery_of_disturbance_constant steady (w₀ := 0) (by simp)
    (fun _ _ => rfl) (fun y => ⟨y, rfl⟩) z

/-! ## Controllability, read as reaching every terminal state

`isControllable_iff_reachesEvery` is the bridge between the matrix criterion and
the plant picture: a controllable pair is exactly one whose controllability
matrix, read as a plant's input map, can be driven to any state at all. It is
stated for every field and every pair, and until now nothing instantiated it.

The pair is the shift with a drive on the second coordinate, already carried by
`AISafetyAtlas.Examples.LinearSystems.Criteria`, where `reachable_isControllable`
proves the matrix side. -/

/-- **The shift with a second-coordinate drive reaches every terminal state**,
from any drift. The matrix criterion and the reachability reading agree, which
is what the equivalence asserts and what a controllability argument silently
relies on whenever it moves between the two. -/
public theorem shift_reachesEvery (c : Fin 2 → ℚ) (z : Fin 2 → ℚ) :
    ∃ u : Fin 2 × Fin 1 → ℚ,
      (Plant.mk (𝕜 := ℚ) (W := PUnit) c
        (AISafetyAtlas.LinearSystems.controllabilityMatrix
          AISafetyAtlas.Examples.LinearSystems.shift
          AISafetyAtlas.Examples.LinearSystems.driveSecond).mulVecLin 0).terminal
        u PUnit.unit = z :=
  (isControllable_iff_reachesEvery AISafetyAtlas.Examples.LinearSystems.shift
    AISafetyAtlas.Examples.LinearSystems.driveSecond c).mp
    AISafetyAtlas.Examples.LinearSystems.reachable_isControllable z

end AISafetyAtlas.Examples.Sovereignty.Disturbance
