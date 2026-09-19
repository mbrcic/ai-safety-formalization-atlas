module

public import AISafetyAtlas.Conjectures.MAIS.O70
public import AISafetyAtlas.SingularLearning.TwoSidedBand

/-!
# MAIS-O77(a) — the matrix-factorization fiber

MAIS-A7 Problem 3.9(a) asks for the two-sided local pair at every point of the
fiber `BA = Φ`, with `A : ℝ^{H×M}` and `B : ℝ^{N×H}`, and asks whether it
depends only on `(rank A, rank B)`.  The issue #12 candidate observes that this
is the MAIS-O70 multiplication-slice table with its input and output dimension
names exchanged.

This is the statement and arithmetic layer.  `o77Pair` is the submitted table;
defining it asserts nothing about the analytic claim.  The order-level proof is
in `O77Proof.lean` and visibly retains `EigenvalueLawStatement`.

The two notes write the same table two ways.  Issue #3 gives the zero-target
pair as a discrete minimisation over an integer index, which is what `o70Pair`
and hence `o77Pair` compute; issue #12 gives it as a four-case closed formula
with a parity correction, its equation (3).  `o77Pair_eq_candidate_closed_form`
proves the two agree at every stratum, so the reuse is an identity rather than a
citation.

## Scope

The source assumes `H > rank Φ` and a simple nonzero target spectrum.  The
table below is stated for every real target matrix satisfying the width and
dimension hypotheses: this is broader on the target-spectrum axis, because the
multiplication-fiber germ is invariant under invertible row and column changes
and needs no ordering of singular modes.  The saddle clause in O77(b) is not
part of this module.

The source writes strict bands; the atlas operational interface uses weak
sublevels.  The public fidelity note records this normalization boundary.  No
claim about strict bands is hidden in the definitions below.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning

/-- The issue #12 table, with `M` the input and `N` the output dimension.

O70 names these dimensions in the opposite order, so this adapter is exactly
the candidate's relabeling and contains no new singular-learning formula. -/
@[expose] public def o77Pair (M N H r a b : ℕ) : ℚ × ℕ :=
  o70Pair N M H r a b

/-- The residual zero-target shape in O77's dimension convention. -/
@[expose] public def o77Shape (M N H r a b : ℕ) : ℕ × ℕ × ℕ :=
  (N - b, M - a, H + r - a - b)

/-- The number of regular residual coordinates, formed in `ℤ` to avoid
truncated subtraction.  This is `NM - (N-b)(M-a)` on feasible ranks. -/
@[expose] public def o77RegularCount (M N a b : ℕ) : ℤ :=
  (N : ℤ) * a + (b : ℤ) * M - (a : ℤ) * b

@[simp]
public theorem o77Shape_eq_o70Shape (M N H r a b : ℕ) :
    o77Shape M N H r a b = o70Shape N M H r a b := rfl

@[simp]
public theorem o77RegularCount_eq_o70Q (M N a b : ℕ) :
    o77RegularCount M N a b = o70Q N M a b := rfl

/-- On actual rank bounds, the integer regular-coordinate count is the
candidate's natural-number expression `NM - (N-b)(M-a)`. -/
public theorem o77RegularCount_eq_sub {M N a b : ℕ} (ha : a ≤ M) (hb : b ≤ N) :
    o77RegularCount M N a b = (N * M - (N - b) * (M - a) : ℕ) := by
  have hprod : (N - b) * (M - a) ≤ N * M :=
    Nat.mul_le_mul (Nat.sub_le N b) (Nat.sub_le M a)
  rw [o77RegularCount, Nat.cast_sub hprod, Nat.cast_mul, Nat.cast_mul,
    Nat.cast_sub hb, Nat.cast_sub ha]
  ring

/-- **Issue #12's equation (4) with its equation (3) substituted.**

The note states the fiber pair as `(s/2 + Λ₀(p,q,h), m₀(p,q,h))` for its own
`p = N - b`, `q = M - a`, `h = H - a - b + r` and `s = NM - pq`, and gives `Λ₀`
and `m₀` by a four-case closed formula with a parity correction.

`o77Pair` is `o70Pair` with the input and output dimension names exchanged, so
what it actually computes is issue #3's discrete minimisation over an integer
index.  Both notes claim the same table and the overlap is disclosed in issue
#12's own scope section, but agreement between the two representations is a
mathematical fact, not a citation.  This identity is that fact: what the atlas
machine-checks for MAIS-O77(a) is the formula issue #12 printed, and not merely
a function that matches it wherever someone evaluated both. -/
public theorem o77Pair_eq_candidate_closed_form (M N H r a b : ℕ) :
    o77Pair M N H r a b
      = ((o77RegularCount M N a b : ℚ) / 2
            + (zeroTargetClosedFormPair (N - b) (M - a) (H + r - a - b)).1,
          (zeroTargetClosedFormPair (N - b) (M - a) (H + r - a - b)).2) := by
  have hpair := residualPair_eq_zeroTargetClosedFormPair (N - b) (M - a) (H + r - a - b)
  have h1 : ((residualMinCost (N - b) (M - a) (H + r - a - b) : ℚ)) / 2
      = (zeroTargetClosedFormPair (N - b) (M - a) (H + r - a - b)).1 :=
    congrArg Prod.fst hpair
  have h2 : residualMultiplicity (N - b) (M - a) (H + r - a - b)
      = (zeroTargetClosedFormPair (N - b) (M - a) (H + r - a - b)).2 :=
    congrArg Prod.snd hpair
  simp only [o77Pair, o70Pair, o70Lambda, o70Multiplicity, o70Shape,
    o77RegularCount_eq_o70Q, Prod.mk.injEq]
  refine ⟨?_, h2⟩
  rw [← h1]
  push_cast
  ring

/-- A bundled O77 fiber rank stratum, in the source's dimension convention. -/
public structure O77RankStratum where
  M : ℕ
  N : ℕ
  H : ℕ
  r : ℕ
  a : ℕ
  b : ℕ
  deriving DecidableEq

/-- O77 feasibility is O70 feasibility after exchanging input and output
dimension names. -/
@[expose] public def O77RankStratum.Admissible (s : O77RankStratum) : Prop :=
  AdmissibleRankData s.N s.M s.H s.r s.a s.b

public instance (s : O77RankStratum) : Decidable s.Admissible := by
  unfold O77RankStratum.Admissible
  infer_instance

/-- The finite rank-table formulation of O77(a)'s minimum assertion. -/
@[expose] public def IsO77FiberMinimumTable
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ) : Prop :=
  ∀ M N H r : ℕ, 0 < M → 0 < N → 0 < H → r ≤ min N (min M H) →
    (∀ a b, AdmissibleRankData N M H r a b →
        awLambda N M H r ≤ (f M N H r a b).1) ∧
      ∃ a b, AdmissibleRankData N M H r a b ∧
        (f M N H r a b).1 = awLambda N M H r

/-- The issue #12 candidate's finite description of the minimum-coefficient
rank strata. -/
@[expose] public def o77Minimizers : Set O77RankStratum :=
  {s | s.Admissible ∧
    (o77Pair s.M s.N s.H s.r s.a s.b).1 = awLambda s.N s.M s.H s.r}

/-- Correctness predicate for a proposed set of minimum-coefficient rank
strata, against a proposed O77 table. -/
@[expose] public def IsO77AWValueStratumTable
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ) (S : Set O77RankStratum) : Prop :=
  ∀ s : O77RankStratum, s ∈ S ↔ s.Admissible ∧
    (f s.M s.N s.H s.r s.a s.b).1 = awLambda s.N s.M s.H s.r

/-- The submitted table has the printed Aoyagi--Watanabe value as its attained
minimum.  This is arithmetic and is unconditional. -/
public theorem o77_fiber_minimum_correct : IsO77FiberMinimumTable o77Pair := by
  intro M N H r hM hN hH hr
  simpa only [o77Pair] using o70_fiber_minimum_correct N M H r hN hM hH hr

/-- The candidate minimizer set is exactly the admissible set on which its
table equals the printed global value. -/
public theorem o77_aw_value_strata_correct :
    IsO77AWValueStratumTable o77Pair o77Minimizers := by
  intro s
  rfl

/-- The issue #12 attachment's additional multiplicity assertion: among the
rank strata whose coefficient attains the printed Aoyagi--Watanabe value, no
table multiplicity exceeds the printed global multiplicity, and some such
stratum attains it.  This is kept separate from O77(a)'s printed correctness
predicate because it is an extra assertion of the submitted solution. -/
@[expose] public def IsO77MaximumMultiplicityOnMinimizers
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ) : Prop :=
  ∀ M N H r : ℕ, 0 < M → 0 < N → 0 < H → r ≤ min N (min M H) →
    (∀ a b, AdmissibleRankData N M H r a b →
        (f M N H r a b).1 = awLambda N M H r →
        (f M N H r a b).2 ≤ awMultiplicity N M H r) ∧
      ∃ a b, AdmissibleRankData N M H r a b ∧
        (f M N H r a b).1 = awLambda N M H r ∧
        (f M N H r a b).2 = awMultiplicity N M H r

/-- The submitted O77 table satisfies its extra maximal-tie-multiplicity claim.
The upper bound is an injection between residual minimizer sets; the uniform
rank witness `(r,r)` attains equality. -/
public theorem o77_maximum_multiplicity_on_minimizers :
    IsO77MaximumMultiplicityOnMinimizers o77Pair := by
  intro M N H r hM hN hH hr
  constructor
  · intro a b hab heq
    simpa only [o77Pair, o70Pair] using
      (o70Multiplicity_le_self_of_lambda_eq N M H r a b hab heq).trans_eq
        (o70Multiplicity_self N M H r hr)
  · refine ⟨r, r, admissible_self N M H r hN hM hH hr, ?_, ?_⟩
    · simpa only [o77Pair, o70Pair] using o70Lambda_self N M H r hr
    · simpa only [o77Pair, o70Pair] using o70Multiplicity_self N M H r hr

/-- O77's loss in Euclidean coordinates, with source dimension names. -/
@[expose] public noncomputable def o77LossCoords (M N H : ℕ)
    (C : Matrix (Fin N) (Fin M) ℝ) : EuclideanSpace ℝ (Fin (H * M + N * H)) → ℝ :=
  rrrLossCoords N M H C

/-- A certified ordered singular frame for the target in MAIS-A7.

The fields are only the powers print gives this object: positive, strictly
decreasing singular values; orthonormal left and right modes; the displayed
rank-`r` expansion; and the assertion that the resulting matrix has rank `r`.
No critical-point, Hessian, Morse-splitting, or volume conclusion is stored in
the certificate. -/
public structure O77SpectralFrame (M N r : ℕ) where
  target : Matrix (Fin N) (Fin M) ℝ
  singularValue : Fin r → ℝ
  leftMode : Fin r → Fin N → ℝ
  rightMode : Fin r → Fin M → ℝ
  singularValue_pos : ∀ i, 0 < singularValue i
  singularValue_strict : ∀ i j, i < j → singularValue j < singularValue i
  left_orthonormal : ∀ i j,
    ∑ x, leftMode i x * leftMode j x = if i = j then 1 else 0
  right_orthonormal : ∀ i j,
    ∑ x, rightMode i x * rightMode j x = if i = j then 1 else 0
  target_eq : target = ∑ i, fun x y => singularValue i * leftMode i x * rightMode i y
  target_rank : target.rank = r

/-- The ordered rank-`k` truncation printed in the definition of `C_k`. -/
@[expose] public noncomputable def O77SpectralFrame.truncation
    {M N r : ℕ} (frame : O77SpectralFrame M N r) (k : ℕ) :
    Matrix (Fin N) (Fin M) ℝ :=
  ∑ i : Fin r, if (i : ℕ) < k then
    (fun x y => frame.singularValue i * frame.leftMode i x * frame.rightMode i y)
  else 0

/-- The exact source-facing membership predicate for a point of the
nonterminal critical set `C_k`: the product is the ordered top-`k` truncation,
and every discarded singular direction is annihilated by `A` and `Bᵀ`.

The annihilation clauses are data already present in MAIS-A7's definition of
the critical sets, not extra hypotheses supplied to make the Hessian proof go
through. -/
@[expose] public def IsO77SaddleRungPoint {M N H r : ℕ}
    (frame : O77SpectralFrame M N r) (k : ℕ)
    (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ) : Prop :=
  k < r ∧ B * A = frame.truncation k ∧
    (∀ i : Fin r, k ≤ i → A.mulVec (frame.rightMode i) = 0) ∧
    (∀ i : Fin r, k ≤ i → B.transpose.mulVec (frame.leftMode i) = 0)

/-- The two operational readings of the two-sided pair at an arbitrary point
of the O77 loss. -/
@[expose] public def HasO77TwoSidedPairAt {M N H : ℕ}
    (C : Matrix (Fin N) (Fin M) ℝ)
    (w : EuclideanSpace ℝ (Fin (H * M + N * H))) (lam : ℝ) (m : ℕ) : Prop :=
  HasLocalVolumeOrder (centeredBandGerm (o77LossCoords M N H C) w) w lam m ∧
    HasStrictLocalVolumeOrder (centeredBandGerm (o77LossCoords M N H C) w) w lam m

/-- Both operational readings of O77(a)'s two-sided pair at a fiber point. -/
@[expose] public def HasO77FiberPairAt {M N H : ℕ}
    (C : Matrix (Fin N) (Fin M) ℝ)
    (w : EuclideanSpace ℝ (Fin (H * M + N * H))) (lam : ℝ) (m : ℕ) : Prop :=
  HasO77TwoSidedPairAt C w lam m

/-- O77(a)'s source-facing two-sided table assertion.  Both the weak atlas
interface and the strict band printed by A7 are recorded.  The strict width
hypothesis is the one printed in A7; no simple-spectrum hypothesis is required
for this stronger target-uniform theorem. -/
@[expose] public def IsO77FiberVolumeOrderTable
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ) : Prop :=
  ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
    ∀ (C : Matrix (Fin N) (Fin M) ℝ), C.rank < H →
      ∀ (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ), B * A = C →
        HasO77FiberPairAt C (matrixPairCoords A B)
          (((f M N H C.rank A.rank B.rank).1 : ℚ) : ℝ)
          (f M N H C.rank A.rank B.rank).2

/-- O77(a) at exactly the target class printed in MAIS-A7: a certified target
with distinct positive nonzero singular values and rank `r < H`.  The stronger
target-uniform predicate above is the reusable theorem interface; this is the
surface graded against the source. -/
@[expose] public def IsO77SourceFiberVolumeOrderTable
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ) : Prop :=
  ∀ M N H r : ℕ, 0 < M → 0 < N → r < H →
    ∀ frame : O77SpectralFrame M N r,
      ∀ (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ),
        B * A = frame.target →
          HasO77FiberPairAt frame.target (matrixPairCoords A B)
            (((f M N H r A.rank B.rank).1 : ℚ) : ℝ)
            (f M N H r A.rank B.rank).2

/-- **O77(a)'s minimal stratum, at the germs.**  Print's part (a) asks three
things of the fiber, and `MAIS-O77.md` fixes what the second one means: “this
global minimum is attained at the most degenerate points of the fiber, so the
minimal stratum in part (a) means the stratum on which `λ` attains it”.  That
is a statement about the actual local invariant at points of the fiber, not
about a table.

`IsO77AWValueStratumTable` grades a proposed stratum set against a proposed
*table*, and `o77_aw_value_strata_correct` proves it by `rfl` — which is the
right shape for checking that a candidate described its own set correctly, and
no evidence at all that the set is the one print asks for.  This predicate is
the one that carries print's clause: a stratum lies in `S` exactly when the
two-sided pair actually realized there has the least coefficient realized
anywhere on the same fiber.

It is stated at the class printed in A7 — a certified target of rank `r < H`
— rather than at an arbitrary matrix, so it grades the same objects as
`IsO77SourceFiberVolumeOrderTable`.

Unlike its O70 counterpart `IsO70MinimizerCharacterization`, this needs no
existence frontier.  That one quantifies over `HasExactLocalPair`, which the
tree does not produce, so its `←` direction has to import
`O70ExactLocalPairsExist` to get a comparison point at the attaining stratum.
Here the comparison point comes from the fiber table itself, which delivers a
`HasO77FiberPairAt` at *every* factorization; `volumeOrder_unique` then pins the
value.  So the germ-level clause costs exactly what the table costs, and
nothing more.

*`HasO77FiberPairAt` occurs in hypothesis position*, so a set could satisfy
this vacuously were the fiber pair nowhere realized.  It is realized — under
`EigenvalueLawStatement`, everywhere on the fiber — and
`Examples/Conjectures/MAIS/O77.lean` shows the predicate has teeth by refuting
it for `Set.univ`. -/
@[expose] public def IsO77MinimizerCharacterization (S : Set O77RankStratum) : Prop :=
  ∀ M N H r : ℕ, 0 < M → 0 < N → r < H →
    ∀ frame : O77SpectralFrame M N r,
      ∀ (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ),
        B * A = frame.target →
        ∀ (lam : ℝ) (m : ℕ),
          HasO77FiberPairAt frame.target (matrixPairCoords A B) lam m →
          ((⟨M, N, H, r, A.rank, B.rank⟩ : O77RankStratum) ∈ S ↔
            ∀ (A' : Matrix (Fin H) (Fin M) ℝ) (B' : Matrix (Fin N) (Fin H) ℝ),
              B' * A' = frame.target →
              ∀ (lam' : ℝ) (m' : ℕ),
                HasO77FiberPairAt frame.target (matrixPairCoords A' B') lam' m' →
                lam ≤ lam')

/-- The order-level meaning of “the fiber invariants depend only on the two
factor ranks”, kept separate from the source's stronger exact-asymptotic
notion. -/
@[expose] public def O77FiberDependsOnRanksOnlyAtVolumeOrder : Prop :=
  ∃ f, IsO77FiberVolumeOrderTable f

/-- O77(b)'s full all-saddle assertion at the operational two-sided volume
order.  It quantifies over every certified source target, every nonterminal
rung, and every point of that rung; no Hessian or Morse certificate occurs in
the statement.

`r < H` is the only dimension hypothesis, which is the only one MAIS-A7
Problem 3.9 states.  Positivity of the input and output dimensions is not
assumed here and would add nothing if it were: a zero input or output dimension
forces `frame.target.rank = 0`, hence `r = 0`, and `IsO77SaddleRungPoint` then
has no inhabitant because it requires `k < r`.  So the excluded models are
already empty, and the surface is exactly print's.

Part (a)'s `IsO77SourceFiberVolumeOrderTable` does carry both, and the asymmetry
is real rather than an oversight: its proof passes them to the O70 fiber table,
where `rem:conventions` excludes the vacuous model outright.

Part (a)'s `IsO77SourceFiberVolumeOrderTable` keeps both, and the asymmetry is
real rather than an oversight: its proof passes them to the O70 fiber table,
where `rem:conventions` excludes the vacuous model outright. -/
@[expose] public def O77AllSaddlesHavePairOne : Prop :=
  ∀ M N H r : ℕ, r < H →
    ∀ (frame : O77SpectralFrame M N r) (k : ℕ),
      ∀ (A : Matrix (Fin H) (Fin M) ℝ) (B : Matrix (Fin N) (Fin H) ℝ),
        IsO77SaddleRungPoint frame k A B →
          HasO77TwoSidedPairAt frame.target (matrixPairCoords A B) 1 1

end AISafetyAtlas.Conjectures.MAIS
