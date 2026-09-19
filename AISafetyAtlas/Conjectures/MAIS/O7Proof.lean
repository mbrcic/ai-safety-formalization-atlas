module

public import AISafetyAtlas.Conjectures.MAIS.O7
public import AISafetyAtlas.SingularLearning.ChartGerm
public import AISafetyAtlas.SingularLearning.StratumTransport
public import AISafetyAtlas.SingularLearning.OrbitTransport

/-!
# MAIS-O7 — unconditional verification of the scalar counterexample

This module proves the issue #5 candidate at the two-sided volume-order level,
in both its strict and weak threshold conventions.  There is no literature
frontier, eigenvalue-law assumption, analytic Morse lemma, or candidate-shaped
hypothesis.

At the origin the centered loss is locally comparable to the absolute dot
product; `IndefiniteQuadratic.lean` proves that germ has pair `(1,1)` by an
explicit integral.  On the terminal fiber the residual block in the atlas's
elimination chart is empty, so the existing chart and orbit transports give
`(1/2,1)` unconditionally at every factorization.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning
open Set Filter Topology
open scoped Matrix

public theorem o7Target_rank {s : ℝ} (hs : 0 < s) : (o7Target s).rank = 1 := by
  rw [o7Target, Matrix.rank_smul_of_mem_nonZeroDivisors _
    (mem_nonZeroDivisors_of_ne_zero hs.ne')]
  exact rank_partialIdMatrix (by norm_num) (by norm_num)

/-- The Gaussian-expectation loss is exactly the polynomial printed by the
candidate. -/
public theorem o7Loss_eq (s : ℝ) (w : O7Space) :
    o7Loss s w = (1 / 2) * (residualAmplitude w - s) ^ 2 := by
  rw [o7Loss, rrrLoss_eq_sum_sq]
  simp [o7Target, residualAmplitude, partialIdMatrix, Matrix.mul_apply]

public theorem continuous_residualAmplitude : Continuous residualAmplitude :=
  (continuous_residualY.matrix_mul continuous_residualX).matrix_elem 0 0

@[simp] public theorem residualAmplitude_zero : residualAmplitude 0 = 0 := by
  simp [residualAmplitude, residualX, residualY]

/-- The candidate's two first-order equations have exactly the origin and the
terminal fiber as solutions. -/
public theorem isO7Critical_iff {s : ℝ} (w : O7Space) :
    IsO7Critical s w ↔ w ∈ o7RankZeroRung ∨ w ∈ o7TerminalRung s := by
  constructor
  · rintro ⟨hX, hY⟩
    by_cases hd : residualAmplitude w - s = 0
    · exact Or.inr (by simpa [o7TerminalRung] using sub_eq_zero.mp hd)
    · left
      constructor
      · exact (smul_eq_zero.mp hX).resolve_left hd
      · exact (smul_eq_zero.mp hY).resolve_left hd
  · rintro (hzero | hfiber)
    · rcases hzero with ⟨hX, hY⟩
      simp [IsO7Critical, hX, hY]
    · have hd : residualAmplitude w - s = 0 := sub_eq_zero.mpr hfiber
      simp [IsO7Critical, hd]

/-- The specialized rank-zero rung is one point, rather than an assumed
singleton. -/
public theorem o7RankZeroRung_eq_singleton : o7RankZeroRung = {0} := by
  ext w
  constructor
  · rintro ⟨hX, hY⟩
    have hp : (matrixPairEquiv 1 1 2).symm w = (0, 0) := Prod.ext hX hY
    have hw := congrArg (matrixPairEquiv 1 1 2) hp
    change w = 0
    simpa only [LinearEquiv.apply_symm_apply, show
      ((0, 0) : Matrix (Fin 2) (Fin 1) ℝ × Matrix (Fin 1) (Fin 2) ℝ) = 0 from rfl,
      map_zero] using hw
  · intro hw
    simp only [Set.mem_singleton_iff] at hw
    subst w
    simp [o7RankZeroRung, residualX, residualY]

/-- Centering at the origin factors into the absolute dot product and a smooth
positive local multiplier. -/
public theorem centeredBandGerm_o7_origin_eq (s : ℝ) (w : O7Space) :
    centeredBandGerm (o7Loss s) 0 w =
      |residualAmplitude w| * |s - residualAmplitude w / 2| := by
  rw [centeredBandGerm, o7Loss_eq, o7Loss_eq, residualAmplitude_zero]
  rw [show (1 / 2 : ℝ) * (residualAmplitude w - s) ^ 2 -
      1 / 2 * (0 - s) ^ 2 =
      residualAmplitude w * (residualAmplitude w / 2 - s) by ring]
  rw [abs_mul, abs_sub_comm]

/-- The origin has the candidate pair `(1,1)`, unconditionally. -/
public theorem hasLocalVolumeOrder_o7_origin {s : ℝ} (hs : 0 < s) :
    HasLocalVolumeOrder (centeredBandGerm (o7Loss s) 0) 0 1 1 := by
  have hnear : ∀ᶠ w in nhds (0 : O7Space), |residualAmplitude w| < s := by
    have ht := (continuous_abs.comp continuous_residualAmplitude).tendsto 0
    have hmem : Iio s ∈ nhds ((abs ∘ residualAmplitude) 0) := by
      simpa [Function.comp_apply] using Iio_mem_nhds hs
    have hev := ht hmem
    change ∀ᶠ w in nhds (0 : O7Space), |residualAmplitude w| < s at hev
    exact hev
  refine hasLocalVolumeOrder_of_comparable
    (c₁ := s / 2) (c₂ := 3 * s / 2) (by positivity) (by linarith) ?_
    hasLocalVolumeOrder_abs_residualAmplitude
  filter_upwards [hnear] with w hw
  rw [centeredBandGerm_o7_origin_eq]
  have hdlo : -s < residualAmplitude w := (abs_lt.mp hw).1
  have hdhi : residualAmplitude w < s := (abs_lt.mp hw).2
  have hpos : 0 < s - residualAmplitude w / 2 := by linarith
  rw [abs_of_pos hpos]
  constructor <;> nlinarith [abs_nonneg (residualAmplitude w)]

private theorem hasLocalVolumeOrder_o7_canonical :
    HasLocalVolumeOrder
      (fun x => rrrLoss (partialIdMatrix 1 1 1)
        ((matrixPairEquiv 1 1 2).symm x).1
        ((matrixPairEquiv 1 1 2).symm x).2)
      (matrixPairCoords (canonicalA 1 2 1 1 1) (canonicalB 1 2 1 1))
      (1 / 2) 1 := by
  have hchart : HasLocalVolumeOrder
      (chartGerm (elimQ 1 1 1 1) (elimP 1 1) (elimH 2 1 1 1)
        (elimN 1 1) (elimGauge 1 1 2 1 1 1)) 0
      ((elimQ 1 1 1 1 : ℝ) / 2) 1 :=
    hasLocalVolumeOrder_chartGerm_residual_zero (by norm_num [elimQ])
      (Or.inl (by norm_num [elimP]))
  have h := hasLocalVolumeOrder_rrrLoss_canonical
    (M := 1) (N := 1) (H := 2) (r := 1) (a := 1) (b := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) hchart
  norm_num [elimQ] at h
  exact h

public theorem o7Loss_at_factorization
    (s : ℝ) (A : Matrix (Fin 2) (Fin 1) ℝ) (B : Matrix (Fin 1) (Fin 2) ℝ)
    (hAB : B * A = o7Target s) : o7Loss s (matrixPairCoords A B) = 0 := by
  rw [o7Loss]
  simp only [matrixPairCoords, residualX, residualY, LinearEquiv.symm_apply_apply]
  rw [rrrLoss_eq_sum_sq, hAB]
  simp

/-- Every exact scalar factorization has pair `(1/2,1)`.  This specializes the
proved elimination chart and orbit transport, not the conditional O70 table. -/
public theorem hasLocalVolumeOrder_o7_factorization {s : ℝ} (hs : 0 < s)
    (A : Matrix (Fin 2) (Fin 1) ℝ) (B : Matrix (Fin 1) (Fin 2) ℝ)
    (hAB : B * A = o7Target s) :
    HasLocalVolumeOrder (centeredBandGerm (o7Loss s) (matrixPairCoords A B))
      (matrixPairCoords A B) (1 / 2) 1 := by
  have hCrank : (o7Target s).rank = 1 := o7Target_rank hs
  have hra : (o7Target s).rank ≤ A.rank := by
    rw [← hAB]
    exact Matrix.rank_mul_le_right B A
  have hrb : (o7Target s).rank ≤ B.rank := by
    rw [← hAB]
    exact Matrix.rank_mul_le_left B A
  have hab : A.rank + B.rank ≤ 2 + (o7Target s).rank := by
    rw [← hAB]
    exact rank_add_rank_le_of_mul A B
  have ha1 : A.rank = 1 := by
    have hu := Matrix.rank_le_card_width A
    rw [hCrank] at hra
    norm_num at hu
    omega
  have hb1 : B.rank = 1 := by
    have hu := Matrix.rank_le_card_height B
    rw [hCrank] at hrb
    norm_num at hu
    omega
  have hraw : HasLocalVolumeOrder
      (fun x => rrrLoss (o7Target s) ((matrixPairEquiv 1 1 2).symm x).1
        ((matrixPairEquiv 1 1 2).symm x).2)
      (matrixPairCoords A B) (1 / 2) 1 := by
    apply hasLocalVolumeOrder_rrrLoss_of_canonical hAB hra hrb hab
    simpa [hCrank, ha1, hb1] using hasLocalVolumeOrder_o7_canonical
  have hz := o7Loss_at_factorization s A B hAB
  have hfun : centeredBandGerm (o7Loss s) (matrixPairCoords A B) = o7Loss s := by
    funext w
    rw [centeredBandGerm, hz, sub_zero, abs_of_nonneg]
    exact rrrLoss_nonneg _ _ _
  rw [hfun]
  exact hraw

private theorem o7_factorization_of_terminal {s : ℝ} {w : O7Space}
    (hw : w ∈ o7TerminalRung s) :
    residualY 1 1 2 w * residualX 1 1 2 w = o7Target s := by
  ext i j
  fin_cases i
  fin_cases j
  simpa [o7TerminalRung, residualAmplitude, o7Target, partialIdMatrix]
    using hw

/-- Every point of the terminal rung has the candidate pair. -/
public theorem hasLocalVolumeOrder_o7_terminal {s : ℝ} (hs : 0 < s)
    (w : O7Space) (hw : w ∈ o7TerminalRung s) :
    HasLocalVolumeOrder (centeredBandGerm (o7Loss s) w) w (1 / 2) 1 := by
  let A := residualX 1 1 2 w
  let B := residualY 1 1 2 w
  have hAB : B * A = o7Target s := o7_factorization_of_terminal hw
  have hcoords : matrixPairCoords A B = w := by
    exact (matrixPairEquiv 1 1 2).apply_symm_apply w
  simpa [hcoords] using hasLocalVolumeOrder_o7_factorization hs A B hAB

private theorem o7_terminal_nonempty {s : ℝ} :
    (o7TerminalRung s).Nonempty := by
  let A := canonicalA 1 2 1 1 1
  let B := s • canonicalB 1 2 1 1
  refine ⟨matrixPairCoords A B, ?_⟩
  have hBA : B * A = o7Target s := by
    rw [show B = s • canonicalB 1 2 1 1 from rfl,
      Matrix.smul_mul, canonicalB_mul_canonicalA (by norm_num) (by norm_num)
        (by norm_num)]
    rfl
  have hamp : residualAmplitude (matrixPairCoords A B) = s := by
    have hentry := congrFun (congrFun hBA 0) 0
    simpa [residualAmplitude, matrixPairCoords, residualX, residualY, o7Target,
      partialIdMatrix]
      using hentry
  exact hamp

private theorem hasO7PairAt_of_volumeOrder {s lam : ℝ} {w : O7Space} {m : ℕ}
    (h : HasLocalVolumeOrder (centeredBandGerm (o7Loss s) w) w lam m) :
    HasO7PairAt s w lam m :=
  ⟨h, hasStrictLocalVolumeOrder_of_hasLocalVolumeOrder h⟩

private theorem o7RungExponents_eq_singleton {s lam : ℝ} {C : Set O7Space}
    (hne : C.Nonempty)
    (hpair : ∀ w ∈ C, HasO7PairAt s w lam 1) :
    o7RungExponents s C = {lam} := by
  ext lam'
  constructor
  · rintro ⟨w, hw, m, hm⟩
    have hu := volumeOrder_unique hm.1 (hpair w hw).1
    simpa using hu.1
  · intro hlam'
    have heq : lam' = lam := by simpa using hlam'
    subst lam'
    obtain ⟨w, hw⟩ := hne
    exact ⟨w, hw, 1, hpair w hw⟩

/-- **MAIS-O7, issue #5 candidate.**  For every positive scalar target the
two-rung model is an unconditional counterexample to the printed strict
staircase inequality. -/
public theorem isO7Counterexample {s : ℝ} (hs : 0 < s) : IsO7Counterexample s := by
  have hzeroEq := o7RankZeroRung_eq_singleton
  have hzeroNe : o7RankZeroRung.Nonempty := by
    rw [hzeroEq]
    exact Set.singleton_nonempty 0
  have hzeroPair : ∀ w ∈ o7RankZeroRung, HasO7PairAt s w 1 1 := by
    intro w hw
    rw [hzeroEq] at hw
    have hweq : w = 0 := by simpa using hw
    subst w
    exact hasO7PairAt_of_volumeOrder (hasLocalVolumeOrder_o7_origin hs)
  have htermNe := o7_terminal_nonempty (s := s)
  have htermPair : ∀ w ∈ o7TerminalRung s, HasO7PairAt s w (1 / 2) 1 := by
    intro w hw
    exact hasO7PairAt_of_volumeOrder (hasLocalVolumeOrder_o7_terminal hs w hw)
  have hzeroExp := o7RungExponents_eq_singleton hzeroNe hzeroPair
  have htermExp := o7RungExponents_eq_singleton htermNe htermPair
  refine ⟨hzeroEq, hzeroPair, htermNe, htermPair, hzeroExp, htermExp, ?_, ?_, ?_⟩
  · rw [O7RungInfimumAttained, o7RungInfimum, hzeroExp, csInf_singleton]
    obtain ⟨w, hw⟩ := hzeroNe
    exact ⟨w, hw, 1, hzeroPair w hw⟩
  · rw [O7RungInfimumAttained, o7RungInfimum, htermExp, csInf_singleton]
    obtain ⟨w, hw⟩ := htermNe
    exact ⟨w, hw, 1, htermPair w hw⟩
  · simp only [o7RungInfimum, hzeroExp, htermExp, csInf_singleton]
    norm_num

/-- **MAIS-O7 is refuted at every positive target scale.**  The printed
conjecture asserts a strict increase along the saddle chain; the final clause of
`IsO7Counterexample` is its negation, and the two rung calculations that feed it
are unconditional. -/
public theorem o7CounterexampleAtEveryScale : O7CounterexampleAtEveryScale :=
  fun _s hs => isO7Counterexample hs

end AISafetyAtlas.Conjectures.MAIS
