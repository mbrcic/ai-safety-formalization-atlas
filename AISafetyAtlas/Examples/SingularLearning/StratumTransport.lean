module

public import AISafetyAtlas.SingularLearning.StratumTransport

/-!
# Worked models: the pair carried through the chart

The transport is instantiated at a nondegenerate stratum, `(M, N, H, r, a, b) = (2, 2, 2, 1, 1,
1)`, where every one of print's five feasibility inequalities is strict enough to be checked by
`decide` and none of the six `ℕ` subtractions is truncated. The chart germ's pair is the
hypothesis; everything else — the chart, the coordinate conjugation, the two-sided comparison —
is discharged.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-- **The dimension count closes at that stratum**: `q + (hn + ph) + g = HN + MH = 8`. -/
example : elimQ 2 2 1 1 + (elimH 2 1 1 1 * elimN 2 1 + elimP 2 1 * elimH 2 1 1 1)
    + elimGauge 2 2 2 1 1 1 = 2 * 2 + 2 * 2 := by decide

/-- **The transport at that stratum.** -/
example (lam : ℝ) (m : ℕ)
    (hpair : HasLocalVolumeOrder
      (chartGerm (elimQ 2 2 1 1) (elimP 2 1) (elimH 2 1 1 1) (elimN 2 1) (elimGauge 2 2 2 1 1 1))
      0 lam m) :
    HasLocalVolumeOrder
      (fun x => rrrLoss (partialIdMatrix 2 2 1) ((matrixPairEquiv 2 2 2).symm x).1
        ((matrixPairEquiv 2 2 2).symm x).2)
      (matrixPairCoords (canonicalA 2 2 1 1 1) (canonicalB 2 2 1 1)) lam m :=
  hasLocalVolumeOrder_rrrLoss_canonical (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hpair

/-- **And at the degenerate stratum** `(r, a, b) = (0, 0, 0)`, where the truth matrix and both
canonical factors vanish. -/
example (M N H : ℕ) (lam : ℝ) (m : ℕ)
    (hpair : HasLocalVolumeOrder
      (chartGerm (elimQ M N 0 0) (elimP M 0) (elimH H 0 0 0) (elimN N 0) (elimGauge M N H 0 0 0))
      0 lam m) :
    HasLocalVolumeOrder
      (fun x => rrrLoss (partialIdMatrix M N 0) ((matrixPairEquiv M N H).symm x).1
        ((matrixPairEquiv M N H).symm x).2)
      (matrixPairCoords (canonicalA N H 0 0 0) (canonicalB M H 0 0)) lam m :=
  hasLocalVolumeOrder_rrrLoss_canonical (Nat.le_refl 0) (Nat.le_refl 0) (Nat.zero_le _)
    (Nat.zero_le _) (Nat.zero_le _) hpair

end AISafetyAtlas.Examples.SingularLearning
