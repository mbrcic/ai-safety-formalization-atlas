module

public import AISafetyAtlas.Conjectures.MAIS.O77Proof
public import AISafetyAtlas.Conjectures.MAIS.O7Proof

/-!
# Worked table for MAIS-O77(a)

The example exercises the input/output relabeling on the candidate PDF's
`M = N = H = 2`, `r = 1` table.  The analytic theorem remains conditional on
`EigenvalueLawStatement`; the arithmetic evaluations are unconditional.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.SingularLearning

/-- The scalar target's one-mode singular frame, with no theorem hidden in its
fields.

Public because the MAIS-O7 mirror identifies its own two rungs against
MAIS-A7's `C_k` at this frame, and a second copy of the same object would be
duplication rather than a second witness. -/
@[expose] public noncomputable def scalarFrame (s : ℝ) (hs : 0 < s) :
    O77SpectralFrame 1 1 1 where
  target := o7Target s
  singularValue := fun _ => s
  leftMode := fun _ _ => 1
  rightMode := fun _ _ => 1
  singularValue_pos := fun _ => hs
  singularValue_strict := by
    intro i j hij
    fin_cases i
    fin_cases j
    contradiction
  left_orthonormal := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num
  right_orthonormal := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num
  target_eq := by
    ext i j
    fin_cases i
    fin_cases j
    simp [o7Target, partialIdMatrix]
  target_rank := o7Target_rank hs

example (s : ℝ) (hs : 0 < s) :
    IsO77SaddleRungPoint (scalarFrame s hs) 0 (0 : Matrix (Fin 2) (Fin 1) ℝ)
      (0 : Matrix (Fin 1) (Fin 2) ℝ) := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · simp [O77SpectralFrame.truncation]
  · simp
  · simp

/-- **Issue #12's printed consistency table, reproduced from `o77Pair`.**

The note's section "Checks on the fiber table" prints two neighbouring
instances in full and states their values.  Both are pinned here.

The point is the relabeling.  `o77Pair M N H r a b` is `o70Pair N M H r a b`,
because the note's part (a) is issue #3's multiplication-slice theorem with the
input and output dimension names exchanged; the atlas reuses that
implementation rather than transcribing the note's closed form twice.  An
exchange applied in the wrong direction still typechecks, still elaborates, and
still produces a plausible table.  These ten values are what make it break the
build instead.

The `(1,1)` stratum at `r = 1` is the entry that carries the parity tie: it is
the only one of the ten whose multiplicity is `2`. -/
public theorem o77Pair_candidate_check_table :
    o77Pair 2 2 2 0 0 0 = (3 / 2, 1) ∧
      o77Pair 2 2 2 0 1 0 = (3 / 2, 1) ∧
      o77Pair 2 2 2 0 0 1 = (3 / 2, 1) ∧
      o77Pair 2 2 2 0 1 1 = (3 / 2, 1) ∧
      o77Pair 2 2 2 0 2 0 = (2, 1) ∧
      o77Pair 2 2 2 0 0 2 = (2, 1) ∧
      o77Pair 2 2 2 1 1 1 = (2, 2) ∧
      o77Pair 2 2 2 1 1 2 = (2, 1) ∧
      o77Pair 2 2 2 1 2 1 = (2, 1) ∧
      o77Pair 2 2 2 2 2 2 = (2, 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · norm_num [o77Pair, o70Pair, o70Lambda, o70Multiplicity, o70Q, o70Shape,
        residualMinCost_eq_argmin, residualArgmin, residualCost, residualMultiplicity,
        residualIndices]
      try decide

/-- The note reads the `r = 0` table as saying that `(I₂, 0)` sits on the
`(2,0)` stratum with local coefficient `2` while the global minimum is `3/2`.
Both halves are in the table above; this records the comparison itself, which
is the sentence the note actually draws from it. -/
public theorem o77Pair_minimum_below_partial_identity_stratum :
    (o77Pair 2 2 2 0 2 0).1 = 2 ∧ awLambda 2 2 2 0 = 3 / 2 ∧
      awLambda 2 2 2 0 < (o77Pair 2 2 2 0 2 0).1 := by
  refine ⟨?_, awLambda_two_two_two_zero, ?_⟩
  · norm_num [o77Pair, o70Pair, o70Lambda, o70Q, o70Shape,
      residualMinCost_eq_argmin, residualArgmin, residualCost]
  · norm_num [o77Pair, o70Pair, o70Lambda, o70Q, o70Shape, awLambda,
      awBalancedNumerator, AWBalanced, residualMinCost_eq_argmin, residualArgmin,
      residualCost]

/-- The note's `Λ₀(1,1,1)`: the balanced regime at odd parity, coefficient
`1/2` and the tie multiplicity `2`.  It is what produces the `(2,2)` entry of
the check table above, and the only shape among the ten where the parity
correction is visible. -/
public theorem zeroTargetClosedFormPair_one_one_one :
    zeroTargetClosedFormPair 1 1 1 = (1 / 2, 2) := by
  norm_num [zeroTargetClosedFormPair]

/-- The table the atlas computes is the note's printed formula, at every
stratum and with no feasibility hypothesis. -/
example (M N H r a b : ℕ) :
    o77Pair M N H r a b
      = ((o77RegularCount M N a b : ℚ) / 2
            + (zeroTargetClosedFormPair (N - b) (M - a) (H + r - a - b)).1,
          (zeroTargetClosedFormPair (N - b) (M - a) (H + r - a - b)).2) :=
  o77Pair_eq_candidate_closed_form M N H r a b

example : IsO77FiberMinimumTable o77Pair := o77_fiber_minimum_correct

example : IsO77MaximumMultiplicityOnMinimizers o77Pair :=
  o77_maximum_multiplicity_on_minimizers

example (hEigen : EigenvalueLawStatement) : IsO77FiberVolumeOrderTable o77Pair :=
  isO77FiberVolumeOrderTable_o77Pair hEigen

/-! ## The full-space expansion at the worked rung

The rank-zero rung of the scalar frame is the most degenerate point there is:
both factors vanish, so every variation is "discarded", and the criticality
equations hold for the trivial reason that the residual is the whole target.
Instantiating the full-space expansion there is what shows it is a statement
about arbitrary variations of both factors and not about a chosen slice. -/

example (s : ℝ) (hs : 0 < s) (X : Matrix (Fin 2) (Fin 1) ℝ) (Y : Matrix (Fin 1) (Fin 2) ℝ) :
    frobeniusSq (((0 : Matrix (Fin 1) (Fin 2) ℝ) + Y) * ((0 : Matrix (Fin 2) (Fin 1) ℝ) + X)
        - (scalarFrame s hs).target)
      = frobeniusSq ((0 : Matrix (Fin 1) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 1) ℝ)
          - (scalarFrame s hs).target)
        + (2 * froIP ((0 : Matrix (Fin 1) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 1) ℝ)
              - (scalarFrame s hs).target) (Y * X)
            + frobeniusSq ((0 : Matrix (Fin 1) (Fin 2) ℝ) * X
                + Y * (0 : Matrix (Fin 2) (Fin 1) ℝ) + Y * X)) := by
  refine frobeniusSq_rung_full_variation (k := 0) ?_ X Y
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · simp [O77SpectralFrame.truncation]
  · simp
  · simp

/-! ## The Hessian's null space is not trivially empty

`o77HessianPolar_eq_zero_of_rungTangent` says every direction tangent to the rung
set lies in the null space of the Hessian.  That is worth nothing if the tangent
space is always `{0}`, and at the scalar frame it *is*: with `M = N = r = 1` the
annihilation clauses force `X = 0` and `Y = 0`, so the smallest example is
degenerate and proves nothing about the theorem's reach.

The `2 x 2` frame below is the smallest one that is not.  There the tangent space
at the rank-zero rung contains a nonzero direction, so the theorem has content:
it says something about a direction that exists. -/

/-- A rank-one target on a two-dimensional space, with the single mode along the
first coordinate. -/
@[expose] public noncomputable def wideFrame (s : ℝ) (hs : 0 < s) : O77SpectralFrame 2 2 1 where
  target := s • partialIdMatrix 2 2 1
  singularValue := fun _ => s
  leftMode := fun _ x => if (x : ℕ) = 0 then 1 else 0
  rightMode := fun _ y => if (y : ℕ) = 0 then 1 else 0
  singularValue_pos := fun _ => hs
  singularValue_strict := by
    intro i j hij
    fin_cases i
    fin_cases j
    contradiction
  left_orthonormal := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [Fin.sum_univ_two]
  right_orthonormal := by
    intro i j
    fin_cases i
    fin_cases j
    norm_num [Fin.sum_univ_two]
  target_eq := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [partialIdMatrix]
  target_rank := by
    rw [Matrix.rank_smul_of_mem_nonZeroDivisors _ (mem_nonZeroDivisors_of_ne_zero hs.ne')]
    exact rank_partialIdMatrix (by norm_num) (by norm_num)

/-- The origin is a rank-zero rung point of that frame. -/
example (s : ℝ) (hs : 0 < s) :
    IsO77SaddleRungPoint (wideFrame s hs) 0 (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · simp [O77SpectralFrame.truncation]
  · simp
  · simp

/-- A variation of `A` in the second input coordinate: annihilated by the
discarded right mode, and not moving the product. -/
def tangentWitness : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = 1 ∧ (j : ℕ) = 1 then (1 : ℝ) else 0

/-- **The tangent space carries a nonzero direction**, so
`o77HessianPolar_eq_zero_of_rungTangent` is not a statement about the zero
variation only. -/
example (s : ℝ) (hs : 0 < s) :
    IsO77RungTangent (wideFrame s hs) 0 (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) tangentWitness (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro i _
    funext x
    fin_cases x <;> simp [wideFrame, tangentWitness, Matrix.mulVec, dotProduct]
  · intro i _
    simp

example : tangentWitness ≠ 0 := by
  intro hcon
  have := congrFun (congrFun hcon 1) 1
  norm_num [tangentWitness] at this

/-- And the Hessian really does vanish on it. -/
example (s : ℝ) (hs : 0 < s) (X' Y' : Matrix (Fin 2) (Fin 2) ℝ) :
    o77HessianPolar (wideFrame s hs) 0 0 tangentWitness 0 X' Y' = 0 := by
  refine o77HessianPolar_eq_zero_of_rungTangent (k := 0) ?_ ?_ X' Y'
  · exact ⟨by norm_num, by simp [O77SpectralFrame.truncation], by simp, by simp⟩
  · refine ⟨by simp, ?_, ?_⟩
    · intro i _
      funext x
      fin_cases x <;> simp [wideFrame, tangentWitness, Matrix.mulVec, dotProduct]
    · intro i _
      simp

/-! ## The Morse–Bott statement has content in both directions

`isO77RungTangent_iff_null` is an equivalence, and an equivalence is only worth
having if neither side is constant.  The tangent witness above shows the tangent
space is not `{0}`; this shows the null space is not everything. -/

/-- A variation of `A` along the *kept* mode: not tangent to the rung set, because
the kept right mode does not annihilate it. -/
def nonTangentWitness : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℝ) else 0

example (s : ℝ) (hs : 0 < s) :
    ¬ IsO77RungTangent (wideFrame s hs) 0 (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) nonTangentWitness (0 : Matrix (Fin 2) (Fin 2) ℝ) := by
  rintro ⟨-, hX, -⟩
  have h := congrFun (hX 0 (Nat.zero_le 0)) 0
  simp [wideFrame, nonTangentWitness, Matrix.mulVec, dotProduct] at h

/-- **So it is not in the null space of the Hessian.**  Some test direction
detects it — which is exactly what `isO77RungTangent_of_null` buys, and what the
tangent-space inclusion alone could never give. -/
example (s : ℝ) (hs : 0 < s) :
    ¬ (∀ X' Y', o77HessianPolar (wideFrame s hs) 0 0 nonTangentWitness 0 X' Y' = 0) := by
  intro hnull
  have hrung : IsO77SaddleRungPoint (wideFrame s hs) 0 (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) :=
    ⟨by norm_num, by simp [O77SpectralFrame.truncation], by simp, by simp⟩
  obtain ⟨-, hX, -⟩ := isO77RungTangent_of_null hrung hnull
  have h := congrFun (hX 0 (Nat.zero_le 0)) 0
  simp [wideFrame, nonTangentWitness, Matrix.mulVec, dotProduct] at h

/-! ## The saddle really is a saddle

At the rank-zero rung of the wide frame both factors vanish, so every vector is
killed by `B` and by `Aᵀ` and the common-kernel hypothesis is free. The Hessian
takes both signs there, which is what pair `(1,1)` needs and what a definite form
would not give. -/

example (s : ℝ) (hs : 0 < s) :
    (∃ (X : Matrix (Fin 2) (Fin 2) ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ),
        o77HessianForm (wideFrame s hs) (0 : Matrix (Fin 2) (Fin 2) ℝ)
          (0 : Matrix (Fin 2) (Fin 2) ℝ) X Y < 0)
      ∧ (∃ (X : Matrix (Fin 2) (Fin 2) ℝ) (Y : Matrix (Fin 2) (Fin 2) ℝ),
        0 < o77HessianForm (wideFrame s hs) (0 : Matrix (Fin 2) (Fin 2) ℝ)
          (0 : Matrix (Fin 2) (Fin 2) ℝ) X Y) := by
  have hrung : IsO77SaddleRungPoint (wideFrame s hs) 0 (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) :=
    ⟨by norm_num, by simp [O77SpectralFrame.truncation], by simp, by simp⟩
  refine o77HessianForm_indefinite (k := 0) (by norm_num) hrung
    (c := fun i => if (i : ℕ) = 0 then (1 : ℝ) else 0) ?_ (by simp) (by simp)
  intro hcon
  have := congrFun hcon 0
  norm_num at this


/-! ## The Morse-Bott route provably fails at some rung points

A Morse-Bott normal form needs the loss to be **constant** along every null
direction of the Hessian: that is what makes the null space the tangent space of
a critical manifold, and it is what lets the free-coordinate lemma discharge
those directions without a splitting argument.

At the rank-zero rung of the wide frame both factors vanish, and the two
witnesses below are a null direction of the Hessian along which the loss is
quartic and nonzero.  So the rung set is not a critical manifold there, and no
Morse-Bott normal form exists at that point.

`isO77RungTangent_iff_null` is unaffected.  It identifies the null space with
the *linearized* rung conditions, which is exactly what it states.  What fails
is the geometric reading of that linearization as a tangent space: at this rung
point the rung set is singular, and its linearization is strictly larger than
any manifold through it.
-/

/-- The first half of a degenerate null direction: `X` carries the second input
coordinate to the first hidden coordinate. -/
@[expose] public def degenerateNullX : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 1 then (1 : ℝ) else 0

/-- The second half: `Y` carries the first hidden coordinate to the second
output coordinate.  Neither factor alone moves the product; their composite
`Y * X` is the second diagonal cell, which the target does not see. -/
@[expose] public def degenerateNullY : Matrix (Fin 2) (Fin 2) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = 1 ∧ (j : ℕ) = 0 then (1 : ℝ) else 0

/-- The pair is tangent to the rung set in the sense the Hessian theorem uses:
the discarded mode annihilates both factors and the product does not move to
first order. -/
public theorem isO77RungTangent_degenerateNull (s : ℝ) (hs : 0 < s) (t : ℝ) :
    IsO77RungTangent (wideFrame s hs) 0 (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) (t • degenerateNullX) (t • degenerateNullY) := by
  refine ⟨by simp, ?_, ?_⟩
  · intro i _
    ext x
    fin_cases x <;>
      simp [wideFrame, degenerateNullX, Matrix.mulVec, dotProduct]
  · intro i _
    ext x
    fin_cases x <;>
      simp [wideFrame, degenerateNullY, Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- **The loss is not constant along that null direction**, and its exact growth
is quartic.  This is the obstruction: a Morse-Bott normal form would make the
left-hand side identically zero. -/
public theorem loss_quartic_on_degenerateNull (s : ℝ) (hs : 0 < s) (t : ℝ) :
    frobeniusSq (((0 : Matrix (Fin 2) (Fin 2) ℝ) + t • degenerateNullY)
        * ((0 : Matrix (Fin 2) (Fin 2) ℝ) + t • degenerateNullX) - (wideFrame s hs).target)
      - frobeniusSq ((0 : Matrix (Fin 2) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 2) ℝ)
          - (wideFrame s hs).target)
      = t ^ 4 := by
  simp [frobeniusSq, wideFrame, degenerateNullX, degenerateNullY, partialIdMatrix,
    Matrix.mul_apply, Fin.sum_univ_two, Matrix.sub_apply]
  ring

/-! ## The unconditional indefiniteness theorem is inhabited

`o77HessianForm_indefinite_of_rung` asks only for a rung point and `r < H`, both
of which print supplies. The wide frame satisfies them, so the theorem is not a
statement about an empty class. -/

public theorem o77_indefinite_of_rung_wideFrame (s : ℝ) (hs : 0 < s) :
    (∃ X Y, o77HessianForm (wideFrame s hs) (0 : Matrix (Fin 2) (Fin 2) ℝ)
        (0 : Matrix (Fin 2) (Fin 2) ℝ) X Y < 0) ∧
      (∃ X Y, 0 < o77HessianForm (wideFrame s hs) (0 : Matrix (Fin 2) (Fin 2) ℝ)
        (0 : Matrix (Fin 2) (Fin 2) ℝ) X Y) := by
  have hrung : IsO77SaddleRungPoint (wideFrame s hs) 0 (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) :=
    ⟨by norm_num, by simp [O77SpectralFrame.truncation], by simp, by simp⟩
  exact o77HessianForm_indefinite_of_rung hrung (by norm_num) 0 (Nat.zero_le 0)

/-! ## The exact block variation, read off at the wide frame

`frobeniusSq_rung_blockVariation` says the loss on print's `2H` block is the
`Kα` form plus one quartic. At the wide frame both Gram blocks vanish (`A` and
`B` are zero at this rung), so the identity collapses to a two-term closed form
in the single scalar `x · y`, which can be checked against the loss by hand. -/

public theorem loss_blockVariation_wideFrame (s : ℝ) (hs : 0 < s) (x y : Fin 2 → ℝ) :
    frobeniusSq (((0 : Matrix (Fin 2) (Fin 2) ℝ)
            + (o77BlockVariation (wideFrame s hs) 0 x y).2)
          * ((0 : Matrix (Fin 2) (Fin 2) ℝ)
            + (o77BlockVariation (wideFrame s hs) 0 x y).1)
          - (wideFrame s hs).target)
        - frobeniusSq ((0 : Matrix (Fin 2) (Fin 2) ℝ) * (0 : Matrix (Fin 2) (Fin 2) ℝ)
            - (wideFrame s hs).target)
      = -(2 * s * (x ⬝ᵥ y)) + (x ⬝ᵥ y) ^ 2 := by
  have hrung : IsO77SaddleRungPoint (wideFrame s hs) 0 (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) :=
    ⟨by norm_num, by simp [O77SpectralFrame.truncation], by simp, by simp⟩
  rw [frobeniusSq_rung_blockVariation hrung 0 (Nat.zero_le 0) x y]
  simp [wideFrame]


/-! ## A rung that is not the rank-zero one

Both frames above have `r = 1`, and `IsO77SaddleRungPoint` requires `k < r`, so
the only rung they have is `k = 0` — where `truncation 0 = 0`, both witnesses take
`A = B = 0`, and the spectral step of §7.2 is true for a reason that has nothing to
do with print's argument. There `BᵀB` and `A Aᵀ` both vanish, so
`det (P R − s_α² I)` collapses to `det (−s_α² I)`, and
`truncation_gram_no_eigenvector` rules `s_α²` out of the spectrum of the zero
operator.

`o77AllSaddlesHavePairOne_holds` is proved for every `k < r`, so nothing above is
unsound. But until this frame the theorem's whole spectral apparatus was exercised
only where it says nothing, which is the defect shape this repository has shipped
before: every check passes on a statement whose only models are degenerate.

`rank2Frame` is the smallest frame with a rung of its own. It needs two distinct
singular values, so the target is a genuine diagonal rather than a multiple of a
partial identity, and `r < H` then forces `H ≥ 3`. -/

/-- A rank-two diagonal target with distinct singular values `a > b > 0`, and the
two modes along the coordinate axes. -/
@[expose] public noncomputable def rank2Frame (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    O77SpectralFrame 2 2 2 where
  target := Matrix.diagonal ![a, b]
  singularValue := ![a, b]
  leftMode := fun i x => if (x : ℕ) = (i : ℕ) then 1 else 0
  rightMode := fun i y => if (y : ℕ) = (i : ℕ) then 1 else 0
  singularValue_pos := by intro i; fin_cases i <;> simp <;> linarith
  singularValue_strict := by intro i j hij; fin_cases i <;> fin_cases j <;> simp_all
  left_orthonormal := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_two]
  right_orthonormal := by intro i j; fin_cases i <;> fin_cases j <;> norm_num [Fin.sum_univ_two]
  target_eq := by
    ext x y
    fin_cases x <;> fin_cases y <;> simp [Matrix.diagonal, Fin.sum_univ_two]
  target_rank := by
    rw [Matrix.rank_diagonal]
    have : ∀ i : Fin 2, ![a, b] i ≠ 0 := by intro i; fin_cases i <;> simp <;> linarith
    simp [this]

/-- `A` at the `k = 1` rung: rank one, annihilating the discarded right mode. -/
@[expose] public def rank2A (a : ℝ) : Matrix (Fin 3) (Fin 2) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then a else 0

/-- `B` at the `k = 1` rung: rank one, with the discarded left mode in `ker Bᵀ`. -/
@[expose] public def rank2B : Matrix (Fin 2) (Fin 3) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = 0 ∧ (j : ℕ) = 0 then (1 : ℝ) else 0

/-- **A point of `C_1`**, where the product is the top-one truncation rather than
zero. -/
public theorem rungPoint_rank2 (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    IsO77SaddleRungPoint (rank2Frame a b hb hab) 1 (rank2A a) rank2B := by
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · rw [O77SpectralFrame.truncation_eq_sum_row, Fin.sum_univ_two,
      if_pos (by norm_num : ((0 : Fin 2) : ℕ) < 1),
      if_neg (by norm_num : ¬((1 : Fin 2) : ℕ) < 1), add_zero]
    ext x y
    fin_cases x <;> fin_cases y <;>
      norm_num [rank2A, rank2B, rank2Frame, O77SpectralFrame.row, Matrix.mul_apply,
        Matrix.vecMulVec_apply, Fin.sum_univ_three]
  · intro i hi
    have hi1 : i = 1 := by fin_cases i <;> simp_all
    subst hi1
    ext x
    fin_cases x <;> norm_num [rank2A, rank2Frame, Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · intro i hi
    have hi1 : i = 1 := by fin_cases i <;> simp_all
    subst hi1
    ext x
    fin_cases x <;>
      norm_num [rank2B, rank2Frame, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Fin.sum_univ_three]

/-- **Neither factor vanishes, and neither does the truncation.** This is what
separates the rung from the rank-zero one, and it is stated rather than assumed
because the whole point of the frame is that the degenerate reading is excluded. -/
public theorem rank2_nondegenerate (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    rank2A a ≠ 0 ∧ rank2B ≠ 0 ∧ (rank2Frame a b hb hab).truncation 1 ≠ 0 := by
  have ha : a ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have := congrArg (fun P : Matrix (Fin 3) (Fin 2) ℝ => P 0 0) h
    simp [rank2A] at this
    exact ha this
  · intro h
    have := congrArg (fun P : Matrix (Fin 2) (Fin 3) ℝ => P 0 0) h
    simp [rank2B] at this
  · intro h
    have := congrArg (fun P : Matrix (Fin 2) (Fin 2) ℝ => P 0 0) h
    rw [O77SpectralFrame.truncation_eq_sum_row, Fin.sum_univ_two,
      if_pos (by norm_num : ((0 : Fin 2) : ℕ) < 1),
      if_neg (by norm_num : ¬((1 : Fin 2) : ℕ) < 1), add_zero] at this
    simp [O77SpectralFrame.row, rank2Frame, Matrix.vecMulVec_apply] at this
    exact ha this

/-- **The Gram blocks print's step 2 multiplies are both nonzero here.** At the
rank-zero rung both vanish and their product is `0`, so
`o77_saddle_spectral_det_ne_zero` reduces to `det (−s_α² I) ≠ 0`. -/
public theorem rank2_gram_blocks_ne_zero (a : ℝ) (ha : a ≠ 0) :
    rank2B.transpose * rank2B ≠ 0 ∧ rank2A a * (rank2A a).transpose ≠ 0 ∧
      (rank2B.transpose * rank2B) * (rank2A a * (rank2A a).transpose) ≠ 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> intro h <;>
    have := congrArg (fun P : Matrix (Fin 3) (Fin 3) ℝ => P 0 0) h <;>
    simp [rank2A, rank2B, Matrix.mul_apply, Fin.sum_univ_two] at this
  exact ha this
  exact ha this

/-- **Print's eigenvalue sentence, discharged where it has content.** The
truncation's Gram is now a rank-one operator with the nonzero eigenvalue `a²`, and
what `truncation_gram_no_eigenvector` rules out is `b²` — a value the discarded
mode actually carries, ruled out by the printed strict decrease of the singular
values rather than by the spectrum being `{0}`. -/
public theorem rank2_spectral_det_ne_zero (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    ((rank2B.transpose * rank2B) * (rank2A a * (rank2A a).transpose)
        - ((rank2Frame a b hb hab).singularValue 1 ^ 2) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det
      ≠ 0 :=
  o77_saddle_spectral_det_ne_zero (rungPoint_rank2 a b hb hab) 1 (by norm_num)

/-- **The truncation's Gram is nonzero**, so the theorem above rules `s_α²` out of
a real spectrum rather than out of `{0}`. -/
public theorem rank2_truncation_gram_ne_zero (a b : ℝ) (hb : 0 < b) (hab : b < a) :
    ((rank2Frame a b hb hab).truncation 1).transpose
        * (rank2Frame a b hb hab).truncation 1 ≠ 0 := by
  have ha : a ≠ 0 := by linarith
  intro h
  have := congrArg (fun P : Matrix (Fin 2) (Fin 2) ℝ => P 0 0) h
  rw [O77SpectralFrame.truncation_eq_sum_row, Fin.sum_univ_two,
    if_pos (by norm_num : ((0 : Fin 2) : ℕ) < 1),
    if_neg (by norm_num : ¬((1 : Fin 2) : ℕ) < 1), add_zero] at this
  simp [O77SpectralFrame.row, rank2Frame, Matrix.vecMulVec_apply, Matrix.mul_apply] at this
  exact ha this

/-! ## The minimal stratum, at the germs

`isO77MinimizerCharacterization_o77Minimizers` says the candidate's stratum set
is exactly where the realized coefficient is least over the fiber. Two things
have to be shown for that to be worth stating: that its hypothesis is
inhabited, and that its conclusion is not satisfied by every set.
-/

/-- The rank-zero frame on a two-dimensional space. `r = 0 < H` is inside
Problem 3.9's hypothesis, and it is the smallest frame whose fiber carries more
than one rank stratum -- at `r = 1` with `M = N = 2` every admissible stratum
has coefficient `2`, so no separation exists there to exhibit. -/
@[expose] public noncomputable def zeroFrame : O77SpectralFrame 2 2 0 where
  target := 0
  singularValue := Fin.elim0
  leftMode := Fin.elim0
  rightMode := Fin.elim0
  singularValue_pos := fun i => i.elim0
  singularValue_strict := fun i => i.elim0
  left_orthonormal := fun i => i.elim0
  right_orthonormal := fun i => i.elim0
  target_eq := by ext x y; simp
  target_rank := Matrix.rank_zero

@[simp]
public theorem zeroFrame_target : zeroFrame.target = 0 := rfl

/-- **The characterisation's hypothesis is inhabited.** Under the eigenvalue
law the fiber pair is realized at every factorization, so this is not a
predicate whose antecedent is empty. -/
example (hEigen : EigenvalueLawStatement) :
    HasO77FiberPairAt zeroFrame.target
      (matrixPairCoords (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ))
      (((o77Pair 2 2 2 0 (1 : Matrix (Fin 2) (Fin 2) ℝ).rank
          (0 : Matrix (Fin 2) (Fin 2) ℝ).rank).1 : ℚ) : ℝ)
      (o77Pair 2 2 2 0 (1 : Matrix (Fin 2) (Fin 2) ℝ).rank
        (0 : Matrix (Fin 2) (Fin 2) ℝ).rank).2 :=
  isO77SourceFiberVolumeOrderTable_o77Pair hEigen 2 2 2 0 (by norm_num) (by norm_num)
    (by norm_num) zeroFrame 1 0 (by simp)

/-- The arithmetic separation the next example turns into a refutation: at the
identity/zero factorization the table gives `2`, at the zero/zero factorization
it gives `3/2`. Both are strata of the same fiber. -/
public theorem o77Pair_zeroFrame_split :
    (o77Pair 2 2 2 0 2 0).1 = 2 ∧ (o77Pair 2 2 2 0 0 0).1 = 3 / 2 := by
  refine ⟨?_, ?_⟩
  · norm_num [o77Pair, o70Pair, o70Lambda, o70Q, o70Shape,
      residualMinCost, residualIndices, residualCost]
  · norm_num [o77Pair, o70Pair, o70Lambda, o70Q, o70Shape,
      residualMinCost, residualIndices, residualCost]
    decide

/-- **The characterisation is not satisfied by everything.** `Set.univ` contains
the stratum of `(1, 0)`, so it would force that point's coefficient `2` to be a
lower bound over the whole fiber, while the balanced factorization `(0, 0)` of
the same zero target has coefficient `3/2`.

Only `EigenvalueLawStatement` is used. The O70 counterpart needs
`O70ExactLocalPairsExist` as well, because its predicate quantifies over
`HasExactLocalPair` and nothing in the tree produces one; here both comparison
points come from the fiber table. -/
example (hEigen : EigenvalueLawStatement) :
    ¬ IsO77MinimizerCharacterization (Set.univ : Set O77RankStratum) := by
  intro h
  have htable := isO77SourceFiberVolumeOrderTable_o77Pair hEigen 2 2 2 0
    (by norm_num) (by norm_num) (by norm_num) zeroFrame
  have h₁ := htable (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp)
  have h₀ := htable (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp)
  have hle := (h 2 2 2 0 (by norm_num) (by norm_num) (by norm_num) zeroFrame
      (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp) _ _ h₁).mp
    (Set.mem_univ _) (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ)
    (by simp) _ _ h₀
  rw [Matrix.rank_zero, Matrix.rank_one, Fintype.card_fin] at hle
  rw [o77Pair_zeroFrame_split.1, o77Pair_zeroFrame_split.2] at hle
  norm_num at hle

end AISafetyAtlas.Examples.Conjectures.MAIS
