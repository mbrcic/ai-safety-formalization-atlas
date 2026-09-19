module

public import AISafetyAtlas.SingularLearning.IndefiniteQuadratic
public import AISafetyAtlas.SingularLearning.TwoSidedBand
public import AISafetyAtlas.SingularLearning.Loss
public import AISafetyAtlas.SingularLearning.OrbitNormalForm

/-!
# MAIS-O7 — scalar opposing staircases

MAIS-O7 asks whether the two-sided local learning coefficients increase along
the critical rungs of reduced-rank matrix factorization.  The issue #5
candidate gives the smallest counterexample: input and output dimensions one,
hidden width two, and target `(s)` with `s > 0`.

This file states that scalar model without assuming any local pair.  The loss
is still `rrrLoss`, the Gaussian-expectation definition used by the atlas; its
elementary scalar polynomial form is derived in `O7Proof.lean`.

The source uses strict bands.  `HasO7PairAt` deliberately records both the
atlas's weak-sublevel operational relation and the strict-band relation from
`TwoSidedBand.lean`.  Thus the source boundary is visible in the type instead
of being discharged only in prose.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning
open scoped Matrix

/-- Parameter space for the scalar `M = N = 1`, `H = 2` model. -/
public abbrev O7Space := EuclideanSpace ℝ (Fin (2 * 1 + 1 * 2))

/-- The positive scalar target, represented as a `1×1` matrix. -/
@[expose] public noncomputable def o7Target (s : ℝ) : Matrix (Fin 1) (Fin 1) ℝ :=
  s • partialIdMatrix 1 1 1

/-- The source loss `L(A,B) = 1/2 E[‖(BA-Φ)x‖²]` in Euclidean pair
coordinates. -/
@[expose] public noncomputable def o7Loss (s : ℝ) (w : O7Space) : ℝ :=
  rrrLoss (o7Target s) (residualX 1 1 2 w) (residualY 1 1 2 w)

/-- The specialized critical equations from the issue #5 candidate. -/
@[expose] public def IsO7Critical (s : ℝ) (w : O7Space) : Prop :=
  (residualAmplitude w - s) • residualX 1 1 2 w = 0 ∧
    (residualAmplitude w - s) • residualY 1 1 2 w = 0

/-- The rank-zero rung after specializing the discarded-mode conditions in
MAIS-A7: both scalar-factor vectors annihilate the only target mode. -/
@[expose] public def o7RankZeroRung : Set O7Space :=
  {w | residualX 1 1 2 w = 0 ∧ residualY 1 1 2 w = 0}

/-- The terminal rung, i.e. the exact-factorization fiber. -/
@[expose] public def o7TerminalRung (s : ℝ) : Set O7Space :=
  {w | residualAmplitude w = s}

/-- Both operational readings of the issue's two-sided pair at a point. -/
@[expose] public def HasO7PairAt (s : ℝ) (w : O7Space) (lam : ℝ) (m : ℕ) : Prop :=
  HasLocalVolumeOrder (centeredBandGerm (o7Loss s) w) w lam m ∧
    HasStrictLocalVolumeOrder (centeredBandGerm (o7Loss s) w) w lam m

/-- Exponents actually certified on a rung.  The existential multiplicity is
not pre-filled; uniqueness follows from `volumeOrder_unique`. -/
@[expose] public def o7RungExponents (s : ℝ) (C : Set O7Space) : Set ℝ :=
  {lam | ∃ w ∈ C, ∃ m, HasO7PairAt s w lam m}

/-- The infimum of the certified exponents on a rung. -/
@[expose] public noncomputable def o7RungInfimum (s : ℝ) (C : Set O7Space) : ℝ :=
  sInf (o7RungExponents s C)

/-- The rung infimum is attained by an actual point and pair. -/
@[expose] public def O7RungInfimumAttained (s : ℝ) (C : Set O7Space) : Prop :=
  ∃ w ∈ C, ∃ m, HasO7PairAt s w (o7RungInfimum s C) m

/-- Source-facing certificate for the issue #5 counterexample.

It contains the complete two-rung geometry, the pair at every point, the exact
sets of possible exponents, attainment of both infima, and the negation of the
printed strict staircase inequality.  Consequently it cannot be inhabited by
proving only the numerical fact `¬ 1 < 1/2`. -/
@[expose] public def IsO7Counterexample (s : ℝ) : Prop :=
  o7RankZeroRung = {0} ∧
    (∀ w ∈ o7RankZeroRung, HasO7PairAt s w 1 1) ∧
    (o7TerminalRung s).Nonempty ∧
    (∀ w ∈ o7TerminalRung s, HasO7PairAt s w (1 / 2) 1) ∧
    o7RungExponents s o7RankZeroRung = {1} ∧
    o7RungExponents s (o7TerminalRung s) = {1 / 2} ∧
    O7RungInfimumAttained s o7RankZeroRung ∧
    O7RungInfimumAttained s (o7TerminalRung s) ∧
    ¬ o7RungInfimum s o7RankZeroRung <
      o7RungInfimum s (o7TerminalRung s)

/-- **The closed refutation proposition.**  `IsO7Counterexample` is stated at a
single target scale because every clause of it is; the printed conjecture is
universal over the positive target singular value, so the ledger row grades this
`∀`-form.  Quantifying here rather than fixing a convenient `s` is what stops the
refutation from being read as "some scale is exceptional". -/
@[expose] public def O7CounterexampleAtEveryScale : Prop :=
  ∀ s : ℝ, 0 < s → IsO7Counterexample s

end AISafetyAtlas.Conjectures.MAIS
