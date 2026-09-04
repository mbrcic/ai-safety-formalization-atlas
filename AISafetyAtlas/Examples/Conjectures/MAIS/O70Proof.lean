module

public import AISafetyAtlas.Conjectures.MAIS.O70Proof
public import AISafetyAtlas.SingularLearning.ResidualScalar

/-!
# Worked models: the O70 exponent bridge, and the two gates

The candidate's Proposition 8.14 says the chamber integral's decay exponent and the candidate
table's residual objective are the same optimisation, reindexed by `s = k − t`. The first
sections check that identity at the strata where both sides can be evaluated by hand, and at the
boundaries of the index range.

The last two sections restate the gates. Gate BΘ is `isO70VolumeOrderTable_o70Pair`, the
two-sided volume order under the eigenvalue law alone; Gate BExact is the three printed clauses
together, under that law and `O70ExactLocalPairsExist`. Both frontiers stay visible as binders on
every example there, and neither is proved in the atlas.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.SingularLearning

/-! ### The vertex exponent -/

/-- At `s = 0` every coordinate sits at scale one and the exponent is `kρ`. -/
example (k : ℕ) (α ρ : ℝ) : chamberVertexExponent k α ρ 0 = (k : ℝ) * ρ :=
  chamberVertexExponent_zero k α ρ

/-- **Proposition 8.14**, at the parameters of the residual germ. -/
example (p k d : ℕ) {s : ℕ} (hs : s ≤ k) :
    chamberVertexExponent k (((d : ℝ) - k - 1) / 2) ((p : ℝ) / 2) s
      = (chamberExponentNum p k d s : ℝ) / 2 :=
  chamberVertexExponent_eq_chamberExponentNum p k d hs

/-- **A scalar stratum**, `(p, n, h) = (1, 1, 1)`, so `k = d = 1` and `α = −1/2`, `ρ = 1/2`. At
`s = 0` the exponent is `ρ = 1/2` and at `s = 1` it is `α + 1 = 1/2`: the two vertices tie, which
is the multiplicity-two case. -/
example : chamberVertexExponent 1 (-(1/2 : ℝ)) ((1 : ℝ) / 2) 0 = 1 / 2 := by
  rw [chamberVertexExponent_zero]
  norm_num

example : chamberVertexExponent 1 (-(1/2 : ℝ)) ((1 : ℝ) / 2) 1 = 1 / 2 := by
  have h := chamberVertexExponent_succ (k := 1) (-(1/2 : ℝ)) ((1 : ℝ) / 2) (j := 0)
    (by norm_num)
  rw [chamberVertexExponent_zero] at h
  norm_num at h
  linarith [h]

/-! ### The minimum -/

/-- **The chamber minimum is the residual minimum, halved**, at every shape. -/
example (p n h : ℕ) :
    chamberMinExponent (min h n) ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2) ((p : ℝ) / 2)
      = (residualMinCost p n h : ℝ) / 2 :=
  chamberMinExponent_eq_residualMinCost p n h

/-- **A degenerate shape**: `h = 0` forces `k = 0`, the only index is `t = 0`, and the residual
cost is `hn = 0`. The chamber exponent is a sum over `Fin 0`, hence `0`. -/
example (p n : ℕ) :
    chamberMinExponent (min 0 n) ((((max 0 n : ℕ) : ℝ) - (min 0 n : ℕ) - 1) / 2) ((p : ℝ) / 2)
      = (residualMinCost p n 0 : ℝ) / 2 :=
  chamberMinExponent_eq_residualMinCost p n 0

/-- **The `ℤ`-level identity it rests on**, at the top of the index range `t = k`. -/
example (p n h : ℕ) :
    chamberExponentNum p (min h n) (max h n) 0 = residualCost p n h (min h n) := by
  have h0 := chamberExponentNum_eq_residualCost p n h (min h n) le_rfl
  rwa [Nat.sub_self] at h0


/-! ### The multiplicity -/

/-- **The candidate's multiplicity is print's `N⋆`.** -/
example (p n h : ℕ) :
    residualMultiplicity p n h
      = chamberResonanceCount (min h n) ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2)
          ((p : ℝ) / 2) + 1 :=
  residualMultiplicity_eq_chamberResonanceCount_succ p n h

/-- **The scalar stratum `(1,1,1)` is the multiplicity-two case**: `p + n + h = 3` is odd and
`|h − n| = 0 < 1 < 2 = h + n`, so both vertices tie. The candidate's arithmetic says the
multiplicity is `2`; the bridge says the chamber integral therefore carries one logarithm. -/
example : residualMultiplicity 1 1 1 = 2 := by decide

example :
    residualMultiplicity 1 1 1
      = chamberResonanceCount (min 1 1) ((((max 1 1 : ℕ) : ℝ) - (min 1 1 : ℕ) - 1) / 2)
          (((1 : ℕ) : ℝ) / 2) + 1 :=
  residualMultiplicity_eq_chamberResonanceCount_succ 1 1 1

/-- **A degenerate shape**: `h = 0` leaves one index and one vertex. -/
example (p n : ℕ) :
    residualMultiplicity p n 0
      = chamberResonanceCount (min 0 n) ((((max 0 n : ℕ) : ℝ) - (min 0 n : ℕ) - 1) / 2)
          ((p : ℝ) / 2) + 1 :=
  residualMultiplicity_eq_chamberResonanceCount_succ p n 0

/-- The candidate's own bound, recovered through the bridge: the multiplicity is at most two
because at most one coordinate resonates. -/
example (p n h : ℕ) : residualMultiplicity p n h ≤ 2 := by
  rw [residualMultiplicity_eq_chamberResonanceCount_succ]
  have := chamberResonanceCount_le_one (min h n)
    ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2) ((p : ℝ) / 2)
  omega


/-! ### The residual germ is O70's own loss at rank zero -/

/-- **`f(Y, X) = 2K` at `C = 0`.** Print's Section 7, Step 5: at rank zero the truth is `C = 0`
and `2K = f(B, A)` with `(p, n, h) = (M, N, H)`. Because `ResidualGerm.lean` packs through the
same `matrixPairEquiv` that `O70.lean` states `rrrLossCoords` through, the identification is a
rewrite and not a transport. -/
example (p n h : ℕ) (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    residualGerm p n h w = 2 * rrrLossCoords p n h 0 w :=
  residualGerm_eq_two_mul_rrrLossCoords p n h w

/-- The same, solved for `K`. -/
example (p n h : ℕ) (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    rrrLossCoords p n h 0 w = residualGerm p n h w / 2 :=
  rrrLossCoords_zero_eq p n h w

/-- **The germ vanishes at the origin**, which is where its local pair is taken: `K(0) = 0`. -/
example (p n h : ℕ) : residualGerm p n h 0 = 0 := by
  rw [residualGerm, residualY, residualX, map_zero]
  simp


/-! ### Theorem 8.1 in the candidate's table -/

/-- **The residual pair is the candidate's residual table**, conditional on `O70-EIGEN-LAW`. -/
example (hEigen : EigenvalueLawStatement) (p n h : ℕ) (hp : 0 < p) (hn : 0 < n) (hh : 0 < h) :
    HasLocalVolumeOrder (residualGerm p n h) 0
      ((residualMinCost p n h : ℝ) / 2) (residualMultiplicity p n h) :=
  hasLocalVolumeOrder_residualGerm_table hEigen p n h hp hn hh

/-- **The scalar germ.** At `(p, n, h) = (1, 1, 1)` the candidate's table gives
`minₜ c_t = 1` and multiplicity `2`, so the pair is `(1/2, 2)` — the case that carries a
logarithm. That value is `decide`-checked here against the arithmetic, not assumed. -/
example : residualMinCost 1 1 1 = 1 ∧ residualMultiplicity 1 1 1 = 2 := by
  constructor
  · decide
  · decide

/-- **A cross-check on the whole conditional chain.** The two routes to the pair of `x²y²` share
no machinery: one runs through the Wishart eigenvalue law, Proposition 8.9, the chamber
calculus and the Tauberian bridge; the other splits a single one-dimensional integral by hand.
`volumeOrder_unique` says a germ has at most one local volume order, so the arithmetic below is
*derived* from the two analytic facts rather than computed — and had the chamber calculus or
the exponent bridge been wrong at this shape, this would instead be a refutation of
`EigenvalueLawStatement`.

That is real V7 evidence for `O70-EIGEN-LAW`: a place where the frontier's consequences are
checkable against something proved without it. -/
example (hEigen : EigenvalueLawStatement) :
    (residualMinCost 1 1 1 : ℝ) / 2 = 1 / 2 ∧ residualMultiplicity 1 1 1 = 2 :=
  volumeOrder_unique
    (hasLocalVolumeOrder_residualGerm_table hEigen 1 1 1 one_pos one_pos one_pos)
    hasLocalVolumeOrder_residualGerm_one

/-- **The same pair, the conditional way.** `residualGerm 1 1 1` is `x²y²`, and its local pair
is now available *unconditionally* as
`AISafetyAtlas.SingularLearning.hasLocalVolumeOrder_residualGerm_one` — that is the verification
plan's V2b, and it is what makes the anti-vacuity witness worth anything, since a witness
standing behind a hypothesis with no known inhabitant witnesses nothing.

This example is kept because it is the `p = n = h = 1` instance of the *general* table
`hasLocalVolumeOrder_residualGerm_table`, and agreement between the two is a real check: the
general route runs through the Wishart eigenvalue law and the chamber calculus, the
unconditional one through an elementary split of a single one-dimensional integral. They meet
at `(1/2, 2)`. -/
example (hEigen : EigenvalueLawStatement) :
    HasLocalVolumeOrder (residualGerm 1 1 1) 0 ((1 : ℝ) / 2) 2 := by
  have h := hasLocalVolumeOrder_residualGerm_table hEigen 1 1 1 one_pos one_pos one_pos
  rw [show residualMinCost 1 1 1 = 1 from by decide,
    show residualMultiplicity 1 1 1 = 2 from by decide] at h
  simpa using h

/-- **A wide shape.** `(p, n, h) = (3, 5, 2)`: `k = 2`, and the table's minimum is `6` with a
unique minimiser, so the pair is `(3, 1)`. -/
example (hEigen : EigenvalueLawStatement) :
    HasLocalVolumeOrder (residualGerm 3 5 2) 0 ((residualMinCost 3 5 2 : ℝ) / 2)
      (residualMultiplicity 3 5 2) :=
  hasLocalVolumeOrder_residualGerm_table hEigen 3 5 2 (by norm_num) (by norm_num) (by norm_num)

/-- **A tall shape**, `n < h`: the frontier is read at the transposed matrix, and the table is
indexed at `k = min h n = 2` all the same. -/
example (hEigen : EigenvalueLawStatement) :
    HasLocalVolumeOrder (residualGerm 3 2 5) 0 ((residualMinCost 3 2 5 : ℝ) / 2)
      (residualMultiplicity 3 2 5) :=
  hasLocalVolumeOrder_residualGerm_table hEigen 3 2 5 (by norm_num) (by norm_num) (by norm_num)

/-- **The residual objective is strictly positive** at every admissible index once the shape is
nondegenerate — checked here at the endpoint, where the factored form loses its first term. -/
example : 0 < residualCost 3 5 2 2 :=
  residualCost_pos (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **The printed table at a canonical representative.** `(M, N, H, r, a, b) = (3, 3, 4, 1, 2, 2)`
is feasible and its residual shape `(1, 1, 1)` is nondegenerate, so the loss at
`(canonicalA, canonicalB)` has the printed pair. -/
example (hEigen : EigenvalueLawStatement) :
    HasLocalVolumeOrder
      (fun x => rrrLoss (partialIdMatrix 3 3 1) ((matrixPairEquiv 3 3 4).symm x).1
        ((matrixPairEquiv 3 3 4).symm x).2)
      (matrixPairCoords (canonicalA 3 4 2 2 1) (canonicalB 3 4 2 1))
      ((o70Lambda 3 3 4 1 2 2 : ℚ) : ℝ) (o70Multiplicity 3 3 4 1 2 2) :=
  hasLocalVolumeOrder_rrrLoss_canonical_table hEigen (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- And the printed value there is `(9/2, 2)`: the transverse block contributes
`q = 3·2 + 2·3 − 2·2 = 8`, the residual minimum is `1`, and the pair is `((8 + 1)/2, 2)`. -/
example : o70Pair 3 3 4 1 2 2 = (9 / 2, 2) := by
  norm_num [o70Pair, o70Lambda, o70Multiplicity, o70Shape, o70Q,
    show residualMinCost 1 1 1 = 1 from by decide, show residualMultiplicity 1 1 1 = 2 from by decide]

/-- The stratum's residual shape really is the scalar one, which is why the multiplicity is two
and the pair carries a logarithm. -/
example : o70Shape 3 3 4 1 2 2 = (1, 1, 1) := by decide

/-- **The degenerate residual shapes agree with the printed table.** With `h = 0` the objective
is zero at its only admissible index, so the minimum is `0` and the multiplicity is `1` — which
is the value the transverse-only branch of the chart germ produces. -/
example (p n : ℕ) : residualMinCost p n 0 = 0 ∧ residualMultiplicity p n 0 = 1 :=
  ⟨residualMinCost_eq_zero_of_degenerate (Or.inr (Or.inr rfl)),
    residualMultiplicity_eq_one_of_degenerate (Or.inr (Or.inr rfl))⟩

/-- And with `p = 0`, where the argument is the one that needs the factored form. -/
example (n h : ℕ) : residualMinCost 0 n h = 0 ∧ residualMultiplicity 0 n h = 1 :=
  ⟨residualMinCost_eq_zero_of_degenerate (Or.inl rfl),
    residualMultiplicity_eq_one_of_degenerate (Or.inl rfl)⟩

/-- **Gate BΘ, restated.** -/
example (hEigen : EigenvalueLawStatement) : IsO70VolumeOrderTable o70Pair :=
  isO70VolumeOrderTable_o70Pair hEigen

/-- **The table at the zero factorization.** `C = 0`, `A = 0`, `B = 0` at `M = N = H = 1`: every
rank is zero, so the stratum is `(r, a, b) = (0, 0, 0)`, the transverse block is empty and the
residual shape is `(1, 1, 1)`. -/
example (hEigen : EigenvalueLawStatement) :
    HasLocalVolumeOrder (rrrLossCoords 1 1 1 0) (matrixPairCoords 0 0)
      (((o70Pair 1 1 1 (0 : Matrix (Fin 1) (Fin 1) ℝ).rank
          (0 : Matrix (Fin 1) (Fin 1) ℝ).rank (0 : Matrix (Fin 1) (Fin 1) ℝ).rank).1 : ℚ) : ℝ)
      (o70Pair 1 1 1 (0 : Matrix (Fin 1) (Fin 1) ℝ).rank
        (0 : Matrix (Fin 1) (Fin 1) ℝ).rank (0 : Matrix (Fin 1) (Fin 1) ℝ).rank).2 :=
  isO70VolumeOrderTable_o70Pair hEigen 1 1 1 one_pos one_pos one_pos 0 0 0 (by simp)

/-- **P1 and P2 under both frontiers.** -/
example (hEigen : EigenvalueLawStatement) (hex : O70ExactLocalPairsExist) :
    IsO70RankTable o70Pair ∧ O70DependsOnRanksOnly :=
  ⟨isO70RankTable_o70Pair hEigen hex, o70DependsOnRanksOnly_of_frontiers hEigen hex⟩


/-! ### The semantic anchor at `N = M = H = 2`

`Examples/Conjectures/MAIS/O70.lean` computes `o70Pair 2 2 2 0 2 0 = (2, 1)` and
`awLambda 2 2 2 0 = 3/2`, and observes that the gap between them is the phenomenon O70 exists
to explain. That is the *arithmetic* half of print's semantic anchor. This is the other half:
the two-sided volume order of the actual loss germ, at the actual point `(I₂, 0)` of the zero
fibre, against `sublevelVolume` on a metric ball and nothing more abstract.

The point is genuinely singular — `B = 0` kills every direction of `A` — and it is not the
degenerate branch of `HasLocalVolumeOrder`, since the exponent is `2 > 0`.

`hEigen` stays visible. This is Gate BΘ strength: the order relation, conditional on the
Wishart frontier. Upgrading it to `HasExactLocalPair` would additionally need
`O70ExactLocalPairsExist`, and belongs to Gate BExact. -/
example (hEigen : EigenvalueLawStatement) :
    HasLocalVolumeOrder (rrrLossCoords 2 2 2 (0 : Matrix (Fin 2) (Fin 2) ℝ))
      (matrixPairCoords (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ))
      (2 : ℝ) 1 := by
  have h := isO70VolumeOrderTable_o70Pair hEigen 2 2 2 (by norm_num) (by norm_num) (by norm_num)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp)
  have hval : o70Pair 2 2 2 0 2 0 = (2, 1) := by
    norm_num [o70Pair, o70Lambda, o70Multiplicity, o70Q, o70Shape,
      residualMinCost_eq_argmin, residualArgmin, residualCost, residualMultiplicity,
      residualIndices]
    decide
  rw [Matrix.rank_zero, Matrix.rank_one, Fintype.card_fin, hval] at h
  simpa using h

/-! ### Gate BExact

The three printed clauses together, under the two hypotheses the candidate itself cites and
proves nowhere: `EigenvalueLawStatement` (Muirhead 3.2.1/3.2.17, after James 1954) and
`O70ExactLocalPairsExist` (the paper's own section 13 names it the single non-elementary
citation in the derivation). Everything the candidate derives is inside the proof.
-/

/-- **MAIS-O70's three clauses, conditional on the two citations.** P1 is the rank dependence,
P2 the table, P3 the characterisation of the minimising strata at the germs. -/
example (hEigen : EigenvalueLawStatement) (hex : O70ExactLocalPairsExist) :
    O70DependsOnRanksOnly ∧ IsO70RankTable o70Pair
      ∧ IsO70MinimizerCharacterization o70Minimizers :=
  ⟨o70DependsOnRanksOnly_of_frontiers hEigen hex,
    isO70RankTable_o70Pair hEigen hex,
    isO70MinimizerCharacterization_o70Minimizers hEigen hex⟩

/-- **The printed gap, semantically.** `Examples/Conjectures/MAIS/O70.lean` computes
`o70Lambda 2 2 2 0 2 0 = 2` and `awLambda 2 2 2 0 = 3/2`, an arithmetic gap. Read through P3 it is
a statement about actual germs: since `(I₂, 0)` is not in the minimiser set, and its own local
coefficient is `2`, *some other* factorization of the same zero truth matrix has a strictly
smaller local coefficient. No table appears in the conclusion.

This conclusion is also reachable without the characterisation at all — take `A' = B' = 0`, get a
pair from the frontier, and read its value off the order table at ranks `(0, 0, 0)`. So it is not
evidence that P3 adds deductive strength. What it does show is that the right-hand side of the
characterisation is not always true, which is what the next example turns into an anti-vacuity
witness. -/
example (hEigen : EigenvalueLawStatement) (hex : O70ExactLocalPairsExist) :
    ∃ (A' B' : Matrix (Fin 2) (Fin 2) ℝ) (lam' : ℝ) (m' : ℕ),
      B' * A' = 0 ∧
        HasExactLocalPair (rrrLossCoords 2 2 2 0) (matrixPairCoords A' B') lam' m' ∧
        lam' < 2 := by
  obtain ⟨lam, m, hpair⟩ :=
    hex 2 2 2 (by norm_num) (by norm_num) (by norm_num)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp)
  have hchar := isO70MinimizerCharacterization_o70Minimizers hEigen hex 2 2 2
    (by norm_num) (by norm_num) (by norm_num)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp) lam m hpair
  have horder := isO70VolumeOrderTable_o70Pair hEigen 2 2 2
    (by norm_num) (by norm_num) (by norm_num)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp)
  have hval : o70Pair 2 2 2 0 2 0 = (2, 1) := by
    norm_num [o70Pair, o70Lambda, o70Multiplicity, o70Q, o70Shape,
      residualMinCost_eq_argmin, residualArgmin, residualCost, residualMultiplicity,
      residualIndices]
    decide
  rw [Matrix.rank_zero, Matrix.rank_one, Fintype.card_fin, hval] at horder
  rw [Matrix.rank_zero, Matrix.rank_one, Fintype.card_fin] at hchar
  have hlam : lam = 2 := by
    have h := (exactLocalPair_eq_volumeOrder hpair horder).1
    simpa using h
  have hnot : (⟨2, 2, 2, 0, 2, 0⟩ : O70RankStratum) ∉ o70Minimizers := by
    simp only [o70Minimizers, Set.mem_ofPred_eq, O70RankStratum.Admissible, not_and]
    intro _
    refine ne_of_gt ?_
    norm_num [o70Lambda, o70Q, o70Shape, awLambda, awBalancedNumerator, AWBalanced,
      residualMinCost_eq_argmin, residualArgmin, residualCost, residualIndices]
  have hfail : ¬ ∀ (A' B' : Matrix (Fin 2) (Fin 2) ℝ), B' * A' = 0 →
      ∀ (lam' : ℝ) (m' : ℕ),
        HasExactLocalPair (rrrLossCoords 2 2 2 0) (matrixPairCoords A' B') lam' m' →
          lam ≤ lam' := fun h => hnot (hchar.mpr h)
  push Not at hfail
  obtain ⟨A', B', hC', lam', m', hpair', hlt⟩ := hfail
  exact ⟨A', B', lam', m', hC', hpair', hlam ▸ hlt⟩

/-- **The P3 predicate is not satisfied by everything.** `IsO70MinimizerCharacterization` puts
`HasExactLocalPair` in hypothesis position only, so if no germ of the family had an exact pair
then every `S` would satisfy it vacuously — the empty set included, which would make the P3
theorem an empty artifact. Under the frontier that cannot happen, and `Set.univ` is the witness:
the stratum of `(I₂, 0)` lies in `Set.univ`, so the characterisation would force its local
coefficient `2` to be a lower bound over the fiber, while the balanced factorization `(0, 0)` of
the same truth matrix has coefficient `3/2`.

This is also the only place the `→` direction of the characterisation is exercised. -/
example (hEigen : EigenvalueLawStatement) (hex : O70ExactLocalPairsExist) :
    ¬ IsO70MinimizerCharacterization (Set.univ : Set O70RankStratum) := by
  intro h
  obtain ⟨lam, m, hpair⟩ :=
    hex 2 2 2 (by norm_num) (by norm_num) (by norm_num)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp)
  obtain ⟨lam₀, m₀, hpair₀⟩ :=
    hex 2 2 2 (by norm_num) (by norm_num) (by norm_num)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp)
  have hle := (h 2 2 2 (by norm_num) (by norm_num) (by norm_num)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
      (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp) lam m hpair).mp (Set.mem_univ _)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp) lam₀ m₀ hpair₀
  have horder := isO70VolumeOrderTable_o70Pair hEigen 2 2 2
    (by norm_num) (by norm_num) (by norm_num)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp)
  have horder₀ := isO70VolumeOrderTable_o70Pair hEigen 2 2 2
    (by norm_num) (by norm_num) (by norm_num)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp)
  have hval : o70Pair 2 2 2 0 2 0 = (2, 1) := by
    norm_num [o70Pair, o70Lambda, o70Multiplicity, o70Q, o70Shape,
      residualMinCost_eq_argmin, residualArgmin, residualCost, residualMultiplicity,
      residualIndices]
    decide
  have hval₀ : o70Pair 2 2 2 0 0 0 = (3 / 2, 1) := by
    norm_num [o70Pair, o70Lambda, o70Multiplicity, o70Q, o70Shape,
      residualMinCost_eq_argmin, residualArgmin, residualCost, residualMultiplicity,
      residualIndices]
    decide
  rw [Matrix.rank_zero, Matrix.rank_one, Fintype.card_fin, hval] at horder
  rw [Matrix.rank_zero, hval₀] at horder₀
  have h1 : lam = 2 := by
    have := (exactLocalPair_eq_volumeOrder hpair horder).1
    simpa using this
  have h2 : lam₀ = 3 / 2 := by
    have := (exactLocalPair_eq_volumeOrder hpair₀ horder₀).1
    simpa using this
  rw [h1, h2] at hle
  norm_num at hle

/-- **The table in print's primary normalization.** `MAIS-A6.tex` `def:local` defines the local pair
by the zeta function first and calls the volume form equivalent. Under the substitution named
`O70ZetaPoleBridge`, the candidate's table is the zeta pair as well.

Three binders now, not two, and the third is different in kind: `EigenvalueLawStatement` and
`O70ExactLocalPairsExist` are results the candidate cites, so assuming them leaves its own
derivation intact. `O70ZetaPoleBridge` is a gap between the atlas and the problem statement's own
primary definition — print asserts it, citing `[lau2023]`, and neither the candidate nor the atlas
proves it for print's sharp ball. Whether `[lau2023]` reaches a sharp-ball cutoff has not been
checked here; the source is named in the manifest and not pinned. -/
example (hbridge : O70ZetaPoleBridge) (hEigen : EigenvalueLawStatement)
    (hex : O70ExactLocalPairsExist) :
    HasZetaPoleOrder (rrrLossCoords 2 2 2 (0 : Matrix (Fin 2) (Fin 2) ℝ))
      (matrixPairCoords (1 : Matrix (Fin 2) (Fin 2) ℝ) (0 : Matrix (Fin 2) (Fin 2) ℝ))
      (2 : ℝ) 1 := by
  have h := hasZetaPoleOrder_o70Pair hbridge hEigen hex 2 2 2
    (by norm_num) (by norm_num) (by norm_num)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (0 : Matrix (Fin 2) (Fin 2) ℝ) (by simp)
  have hval : o70Pair 2 2 2 0 2 0 = (2, 1) := by
    norm_num [o70Pair, o70Lambda, o70Multiplicity, o70Q, o70Shape,
      residualMinCost_eq_argmin, residualArgmin, residualCost, residualMultiplicity,
      residualIndices]
    decide
  rw [Matrix.rank_zero, Matrix.rank_one, Fintype.card_fin, hval] at h
  simpa using h

end AISafetyAtlas.Examples.Conjectures.MAIS
