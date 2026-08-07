module

public import AISafetyAtlas.Learning

/-!
# CONJ-001 — Which restriction on the target family breaks No Free Lunch?

**This module states a conjecture. It proves nothing.**

`AISafetyAtlas.Learning.no_free_lunch_supervised` averages uniformly over *every*
target `f : X → Y`. Real systems are not drawn from every function: they are
computable, resource-bounded, finite-precision, or otherwise tame. Whenever an
impossibility is proved by averaging over an unrestricted class, the question of
which restriction breaks it is the question of whether the impossibility binds
anything real — and every restriction that breaks it is a possibility result
about systems people actually build.

This states the schematic version over an arbitrary restricted family
`F : Finset (X → Y)`, so a specific restriction (definable, poly-time,
finite-precision) instantiates it rather than requiring its own theorem. The
o-minimal instantiation is the motivating case and is out of reach today:
Mathlib has finite combinatorial VC dimension
(`Mathlib.Combinatorics.SetFamily.Shatter`) and no o-minimal structures.

Known nearby, and **not** what this asks: `homogeneous_iff_learner_indep`
characterises learner-independence in terms of the *loss*, with the target class
left unrestricted. This asks about the *target class*, with the loss homogeneous.

Refutation condition: a homogeneous `ℓ`, a training domain `S` with an
off-training point, and a nonempty `F` satisfying exactly one side of the
biconditional. Either direction failing refutes it.

Status and provenance: `conjectures.yaml`, `CONJ-001`.
This module is not on the atlas root import.
-/

namespace AISafetyAtlas.Conjectures.RestrictedNFL

open AISafetyAtlas.Learning

/--
A target family closed under relabelling targets **off** the training domain.

This is the symmetry the uniform-averaging NFL proof consumes. `Finset.univ` has
it; a family of computable or low-complexity targets generally does not, since
composing with an arbitrary permutation of `Y` need not stay in the family.
-/
public def OffTrainingClosed {X Y : Type*} (S : Set X) [DecidablePred (· ∈ S)]
    (F : Finset (X → Y)) : Prop :=
  ∀ f ∈ F, ∀ π : Y ≃ Y, (fun z => if z ∈ S then f z else π (f z)) ∈ F

/--
Learner-independence relative to a restricted target family: every functional of
the off-training-set loss vector has the same sum over `F` for all learners.

With `F = Finset.univ` and homogeneous `ℓ` this is
`AISafetyAtlas.Learning.lossConfig_sum_learner_indep`.
-/
public noncomputable def LearnerIndepOn {X Y : Type*}
    (ℓ : Y → Y → ℝ) (S : Set X) (F : Finset (X → Y)) : Prop :=
  ∀ (A B : SupervisedLearner X Y S) (Ψ : ((Sᶜ : Set X) → ℝ) → ℝ),
    ∑ f ∈ F, Ψ (lossConfig ℓ S A f) = ∑ f ∈ F, Ψ (lossConfig ℓ S B f)

/--
**CONJ-001.** For a homogeneous loss, closure of the target family under
off-training relabelling is not merely sufficient for learner-independence but
necessary: restricting the targets to any family lacking that symmetry lets some
learner beat another on average.

Stated, not proved. Nothing in the atlas asserts this.
-/
public noncomputable def statement : Prop :=
  ∀ (X Y : Type) [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]
    (ℓ : Y → Y → ℝ), HomogeneousLoss ℓ →
    ∀ (S : Set X) [DecidablePred (· ∈ S)] (x : X), x ∉ S →
    ∀ F : Finset (X → Y), F.Nonempty →
      (LearnerIndepOn ℓ S F ↔ OffTrainingClosed S F)

/-! ## Non-vacuity

The statement quantifies over hypotheses that could in principle be
unsatisfiable, in which case it would hold trivially and say nothing. Each
antecedent is inhabited.
-/

/-- A homogeneous loss exists: 0-1 loss is one. -/
example : HomogeneousLoss (fun a y : Fin 2 => if a = y then (0 : ℝ) else 1) :=
  homogeneous_zeroOne

/-- A training domain with an off-training point exists. -/
example : (0 : Fin 2) ∉ ({1} : Set (Fin 2)) := by decide

/-- A nonempty target family exists. -/
example : (Finset.univ : Finset (Fin 2 → Fin 2)).Nonempty :=
  Finset.univ_nonempty

/-- The closure condition is satisfiable: the full family has it. -/
example : OffTrainingClosed ({1} : Set (Fin 2)) (Finset.univ : Finset (Fin 2 → Fin 2)) :=
  fun _ _ _ => Finset.mem_univ _

end AISafetyAtlas.Conjectures.RestrictedNFL
