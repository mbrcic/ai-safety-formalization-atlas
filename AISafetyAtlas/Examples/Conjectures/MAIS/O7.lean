module

public import AISafetyAtlas.Conjectures.MAIS.O7Proof
public import AISafetyAtlas.Examples.Conjectures.MAIS.O77

/-!
# Worked MAIS-O7 counterexample

The target scalar `s = 1` satisfies the source's positivity condition.  The
complete source-facing counterexample certificate is therefore inhabited.

## The rungs are MAIS-A7's own critical sets

`IsO7Counterexample` is a statement about `o7RankZeroRung` and
`o7TerminalRung`, and about nothing else.  Both are written directly in the
scalar model, so until the identification below they were transcriptions: a
reader had to check by eye that they specialize MAIS-A7's `C_k` correctly, and
a mis-transcription would have produced a valid theorem about the wrong two
sets.  Nothing in the build could have reported it.

`AISafetyAtlas.Conjectures.MAIS.IsO77SaddleRungPoint` is the general `C_k`
membership predicate, and `isO77SaddleRungPoint_iff_critical` proves it
equivalent to criticality-plus-membership in both directions.  Instantiating
that predicate at the scalar frame and comparing it to `o7RankZeroRung` moves
the identification from prose into the kernel.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.SingularLearning
open AISafetyAtlas.Conjectures.MAIS

example : IsO7Counterexample 1 :=
  isO7Counterexample (by norm_num)

example (w : O7Space) :
    IsO7Critical 1 w ↔ w ∈ o7RankZeroRung ∨ w ∈ o7TerminalRung 1 :=
  isO7Critical_iff w

/-! ## The scalar target as an A7 spectral frame

`scalarFrame` is the MAIS-A7 certified frame of this target, defined in the
MAIS-O77 mirror and reused here rather than restated: one mode, one singular
value `s`, both unit modes the scalar `1`.  Its `singularValue_strict` field is
vacuous, which is the note's own observation that the distinct-singular-values
hypothesis is automatic at `r = 1`.
-/

/-- The scalar frame's only truncation below its rank is the zero one. -/
public theorem scalarFrame_truncation_zero (s : ℝ) (hs : 0 < s) :
    (scalarFrame s hs).truncation 0 = 0 := by
  ext x y
  simp [O77SpectralFrame.truncation]

@[simp] public theorem scalarFrame_target (s : ℝ) (hs : 0 < s) :
    (scalarFrame s hs).target = o7Target s := rfl

/-! ## The two rungs, identified against MAIS-A7 -/

/-- **The rank-zero rung is MAIS-A7's `C_0`.**

Both annihilation clauses collapse to the vanishing of a factor, because the
single right mode and the single left mode of the scalar frame are units: `A`
kills the right mode exactly when `A = 0`, and `Bᵀ` kills the left mode
exactly when `B = 0`.  The product clause then holds for free.  So the set
`IsO7Counterexample` quantifies over is the printed critical set and not a
convenient neighbourhood of it. -/
public theorem o7RankZeroRung_eq_saddleRung (s : ℝ) (hs : 0 < s) :
    o7RankZeroRung
      = {w : O7Space | IsO77SaddleRungPoint (scalarFrame s hs) 0
          (residualX 1 1 2 w) (residualY 1 1 2 w)} := by
  ext w
  simp only [o7RankZeroRung, Set.mem_ofPred_eq, IsO77SaddleRungPoint,
    scalarFrame_truncation_zero]
  constructor
  · rintro ⟨hX, hY⟩
    refine ⟨Nat.zero_lt_one, ?_, ?_, ?_⟩
    · rw [hX, hY, Matrix.mul_zero]
    · intro i _
      rw [hX]
      simp
    · intro i _
      rw [hY]
      simp
  · rintro ⟨-, -, hA, hB⟩
    have hA0 := congrFun (hA 0 (Nat.zero_le _))
    have hB0 := congrFun (hB 0 (Nat.zero_le _))
    constructor
    · ext x y
      have hx := hA0 x
      simp only [scalarFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
        mul_one, Pi.zero_apply] at hx
      simpa [Subsingleton.elim y 0] using hx
    · ext x y
      have hy := hB0 y
      simp only [scalarFrame, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
        mul_one, Matrix.transpose_apply, Pi.zero_apply] at hy
      simpa [Subsingleton.elim x 0] using hy

/-- **The terminal rung is the exact-factorization fibre of the same frame.**
MAIS-A7's terminal rung is `F_Φ = {(A,B) : BA = Φ}`, and this is that set. -/
public theorem o7TerminalRung_eq_fiber (s : ℝ) (hs : 0 < s) :
    o7TerminalRung s
      = {w : O7Space | residualY 1 1 2 w * residualX 1 1 2 w
          = (scalarFrame s hs).target} := by
  ext w
  simp only [o7TerminalRung, Set.mem_ofPred_eq, residualAmplitude,
    scalarFrame_target]
  constructor
  · intro h
    ext x y
    fin_cases x
    fin_cases y
    simpa [o7Target, partialIdMatrix] using h
  · intro h
    have := congrFun (congrFun h 0) 0
    simpa [o7Target, partialIdMatrix] using this

/-! ## The instance sits inside print's setting

MAIS-A7 states the saddle chain with its losses falling, `L₀ > L₁ > … > L_r`.
A counterexample outside that setting would not refute the conjecture, so the
descending step is checked here rather than assumed. -/

/-- **The loss falls from the rank-zero rung to the terminal one**, which is
the descending half of print's setting at `r = 1`. -/
public theorem o7Loss_terminal_lt_rankZero (s : ℝ) (hs : 0 < s) {w : O7Space}
    (hw : w ∈ o7TerminalRung s) : o7Loss s w < o7Loss s 0 := by
  have hval : residualAmplitude w = s := hw
  rw [o7Loss_eq, o7Loss_eq, residualAmplitude_zero, hval]
  have : (0 : ℝ) < s ^ 2 := by positivity
  simp only [sub_self, zero_sub, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, mul_zero, neg_sq]
  linarith

end AISafetyAtlas.Examples.Conjectures.MAIS
