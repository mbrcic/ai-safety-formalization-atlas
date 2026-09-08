module

public import AISafetyAtlas.SingularLearning.ParamSplit

/-!
# A worked subspace-adapted splitting

`ParamSplit.lean` is stated for an arbitrary subspace of an arbitrary Euclidean parameter
space, so nothing there ever meets a subspace that is neither `⊥` nor `⊤`. This file supplies
one: the first coordinate axis of the plane, a proper nonzero subspace with a proper nonzero
orthogonal complement, and checks the splitting on it.

Three things are exercised, and they are the three a Morse–Bott consumer will ask for.

* **The dimension count is not vacuous.** `dim Vᗮ = 1` and `dim V = 1` here, so the splitting
  really does have two nonempty blocks. A statement about `dim Vᗮ + dim V = n` is true and
  useless when one block is empty, which is what `⊥` and `⊤` would give.

* **"Adapted" is checked against a witness.** The second axis lies in `Vᗮ`, and
  `mem_orthogonal_iff_paramSplitEquiv_natAdd_eq_zero` then says its last block of coordinates
  vanishes — the direction of the characterization that a spanning argument, not orthogonality,
  has to supply.

* **The two transport properties are available at the concrete instance**, not only in the
  abstract statement: the splitting is analytic and preserves Lebesgue measure.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning
open Module (finrank)
open MeasureTheory

/-! ## The generic statements -/

/-- The dimension count holds for every subspace of every Euclidean parameter space. -/
example (V : Submodule ℝ (EuclideanSpace ℝ (Fin 5))) : finrank ℝ Vᗮ + finrank ℝ V = 5 :=
  finrank_orthogonal_add_finrank V

/-- The splitting is analytic everywhere, for every subspace. -/
example (V : Submodule ℝ (EuclideanSpace ℝ (Fin 5))) :
    AnalyticOnNhd ℝ (paramSplitEquiv V) Set.univ :=
  analyticOnNhd_paramSplitEquiv V Set.univ

/-- So is its inverse. -/
example (V : Submodule ℝ (EuclideanSpace ℝ (Fin 5))) :
    AnalyticOnNhd ℝ (paramSplitEquiv V).symm Set.univ :=
  analyticOnNhd_paramSplitEquiv_symm V Set.univ

/-- And it preserves Lebesgue measure, which is what an arbitrary complement would not give. -/
example (V : Submodule ℝ (EuclideanSpace ℝ (Fin 5))) :
    MeasurePreserving (paramSplitEquiv V) volume volume :=
  measurePreserving_paramSplitEquiv V

/-! ## A proper nonzero subspace: the first coordinate axis of the plane -/

/-- The first coordinate axis in `ℝ²`. -/
@[expose] public noncomputable def coordAxis : Submodule ℝ (EuclideanSpace ℝ (Fin 2)) :=
  Submodule.span ℝ {EuclideanSpace.single (0 : Fin 2) (1 : ℝ)}

public theorem euclideanSingle_ne_zero (i : Fin 2) :
    EuclideanSpace.single i (1 : ℝ) ≠ 0 := by
  simp [PiLp.single_eq_zero_iff]

/-- The axis is one-dimensional, so neither block of the splitting is empty. -/
public theorem finrank_coordAxis : finrank ℝ coordAxis = 1 :=
  finrank_span_singleton (euclideanSingle_ne_zero 0)

/-- And so is its orthogonal complement, by the dimension count. -/
public theorem finrank_coordAxis_orthogonal : finrank ℝ coordAxisᗮ = 1 := by
  have h := finrank_orthogonal_add_finrank coordAxis
  rw [finrank_coordAxis] at h
  omega

/-- The second axis is orthogonal to the first, so the complement is inhabited by something
other than `0`. -/
public theorem single_one_mem_coordAxis_orthogonal :
    EuclideanSpace.single (1 : Fin 2) (1 : ℝ) ∈ coordAxisᗮ := by
  rw [coordAxis, Submodule.mem_orthogonal]
  intro u hu
  rw [Submodule.mem_span_singleton] at hu
  obtain ⟨c, rfl⟩ := hu
  rw [inner_smul_left]
  simp [EuclideanSpace.inner_single_left]

/-- **The adapted characterization, at the witness.** Because the second axis lies in
`coordAxisᗮ`, its last block of coordinates in the split frame vanishes. This is the direction
of the characterization that orthogonality alone does not give — it needs the right half of the
adapted basis to span `coordAxis`. -/
example (j : Fin (finrank ℝ coordAxis)) :
    paramSplitEquiv coordAxis (EuclideanSpace.single (1 : Fin 2) (1 : ℝ))
        (Fin.natAdd (finrank ℝ coordAxisᗮ) j) = 0 :=
  (mem_orthogonal_iff_paramSplitEquiv_natAdd_eq_zero coordAxis _).mp
    single_one_mem_coordAxis_orthogonal j

/-- The converse direction is available too: vanishing of the first block of coordinates
characterizes membership in the axis itself. -/
example (x : EuclideanSpace ℝ (Fin 2))
    (h : ∀ i : Fin (finrank ℝ coordAxisᗮ),
      paramSplitEquiv coordAxis x (Fin.castAdd (finrank ℝ coordAxis) i) = 0) :
    x ∈ coordAxis :=
  (mem_iff_paramSplitEquiv_castAdd_eq_zero coordAxis x).mpr h

/-- The axis itself is carried onto the span of the last block's standard basis vector. -/
example :
    Submodule.map (paramSplitEquiv coordAxis).toLinearEquiv.toLinearMap coordAxis
      = Submodule.span ℝ (Set.range fun j : Fin (finrank ℝ coordAxis) =>
          EuclideanSpace.single (Fin.natAdd (finrank ℝ coordAxisᗮ) j) (1 : ℝ)) :=
  map_paramSplitEquiv_eq coordAxis

/-- The complement is carried onto the span of the first block's standard basis vector. -/
example :
    Submodule.map (paramSplitEquiv coordAxis).toLinearEquiv.toLinearMap coordAxisᗮ
      = Submodule.span ℝ (Set.range fun i : Fin (finrank ℝ coordAxisᗮ) =>
          EuclideanSpace.single (Fin.castAdd (finrank ℝ coordAxis) i) (1 : ℝ)) :=
  map_orthogonal_paramSplitEquiv_eq coordAxis

/-- The concrete splitting is an isometry, so no radius is distorted when a germ is read in
the adapted frame. -/
example : Isometry (paramSplitEquiv coordAxis) := isometry_paramSplitEquiv coordAxis

end AISafetyAtlas.Examples.SingularLearning
