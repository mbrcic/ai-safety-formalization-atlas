module

public import AISafetyAtlas.Conjectures.MAIS.O70
public import AISafetyAtlas.SingularLearning.EigenvalueLaw
public import AISafetyAtlas.SingularLearning.ResidualGerm
public import AISafetyAtlas.SingularLearning.ResidualLaplace
public import AISafetyAtlas.SingularLearning.ChartAssembly
public import AISafetyAtlas.SingularLearning.OrbitTransport
public import AISafetyAtlas.SingularLearning.ReducedRank
public import AISafetyAtlas.SingularLearning.StratumTransport
public import AISafetyAtlas.SingularLearning.LossAnalytic

/-!
# O70: the assembly

`O70.lean` states the source's clauses and proves the arithmetic ones. This module is where the
singular-learning machinery is pointed at them. It imports `O70.lean` and the singular-learning
facade; `O70.lean` must not import it, so that the statement of the conjecture never depends on
the state of its proof.

## What is here

### The exponent bridge `ChamberIntegral.lean` computes the chamber integral's decay through
`chamberVertexExponent`, `chamberMinExponent` and `chamberResonanceCount`, all of which are
functions of the abstract parameters `(k, α, ρ)`. `O70.lean` computes the candidate's table
through `residualCost`, `residualMinCost` and `residualMultiplicity`, functions of `(p, n, h)`.
Proposition 8.14 of the candidate says the two are the same optimisation under

    k = min h n,   d = max h n,   α = (d − k − 1)/2,   ρ = p/2,   s = k − t .

`chamberExponentNum_eq_residualCost` in `O70.lean` already proves the `ℤ`-level identity between
the two objectives. What was missing is that `chamberVertexExponent` — the analytic object, a
sum over `Fin k` of a branch — is that numerator halved. That is
`chamberVertexExponent_eq_chamberExponentNum` below, and `chamberMinExponent_eq_residualMinCost`
is its consequence for the minima.

The proof is an induction on `s` using `chamberVertexExponent_succ`, print's Proposition 8.18
increment `E_{s+1} − E_s = α + s + 1 − ρ`. At the O70 parameters that increment is
`(d − k − p + 2s + 1)/2`, which is exactly half the increment of `chamberExponentNum`. No sum
over a filtered `Finset` is needed, and no `ℕ`-subtraction occurs: `s` only ever increases.

### The residual pair, and the table

`hasLocalVolumeOrder_residualGerm_table` reads Theorem 8.1 in the candidate's own table, at every
positive shape and with no ordering between `h` and `n`. On top of it the section headed *The
printed table at the canonical representative* runs the candidate's §10 to
`isO70VolumeOrderTable_o70Pair`: the printed pair is the local volume order of the loss at every
factorization of every truth matrix.

### The three printed clauses

The last two sections cross from the order relation to print's own.
`isO70RankTable_o70Pair` is P2 and `o70DependsOnRanksOnly_of_frontiers` is P1;
`isO70MinimizerCharacterization_o70Minimizers` is P3 read at the germs rather than at the table —
a stratum lies in `o70Minimizers` exactly when the actual local coefficient there is a lower
bound for the actual local coefficient everywhere on the zero fiber.

## What is not here

An *unconditional* exact asymptotic. The analytic work below is the two-sided *order* relation
`HasLocalVolumeOrder` throughout; `HasExactLocalPair` enters only in the last two sections, and
every result there carries `O70ExactLocalPairsExist` — through `isO70RankTable_of_volumeOrder`
for P1 and P2, and directly for P3, where it is what produces a point of the fiber to compare
against. That hypothesis is a frontier and is not proved anywhere in the atlas.
`EigenvalueLawStatement` is the other frontier, and it is a hypothesis of every result in the
last three sections. Both remain assumed, so MAIS-O70 is not resolved here.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.SingularLearning

/-! ## Proposition 8.14: the chamber exponent is the residual objective -/

/-- The vertex exponent at `s = 0` is `k ρ`: every coordinate sits at scale one. -/
public theorem chamberVertexExponent_zero (k : ℕ) (α ρ : ℝ) :
    chamberVertexExponent k α ρ 0 = (k : ℝ) * ρ := by
  rw [chamberVertexExponent]
  have h : ∀ i : Fin k, (if (i : ℕ) + 1 ≤ 0 then α + (i : ℕ) + 1 else ρ) = ρ := fun i =>
    if_neg (by omega)
  rw [Finset.sum_congr rfl fun i _ => h i, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- **Proposition 8.14, at the analytic exponent.** With `α = (d − k − 1)/2` and `ρ = p/2`, the
vertex exponent is the candidate's `chamberExponentNum` halved.

Print's `E_s = (pk + s(d − k − p) + s²)/2`; the induction step is print's Proposition 8.18
increment. -/
public theorem chamberVertexExponent_eq_chamberExponentNum (p k d : ℕ) {s : ℕ} (hs : s ≤ k) :
    chamberVertexExponent k (((d : ℝ) - k - 1) / 2) ((p : ℝ) / 2) s
      = (chamberExponentNum p k d s : ℝ) / 2 := by
  induction s with
  | zero =>
      rw [chamberVertexExponent_zero, chamberExponentNum]
      push_cast
      ring
  | succ j ih =>
      have hj : j < k := by omega
      rw [chamberVertexExponent_succ _ _ hj, ih (by omega), chamberExponentNum,
        chamberExponentNum]
      push_cast
      ring

/-- The vertex exponent at `s` is the residual cost at `t = k − s`, halved. This is
`chamberExponentNum_eq_residualCost` read through `chamberVertexExponent_eq_chamberExponentNum`,
and it is the form both the minimum and the multiplicity comparisons use. -/
public theorem chamberVertexExponent_eq_residualCost (p n h : ℕ) {s : ℕ} (hs : s ≤ min h n) :
    chamberVertexExponent (min h n) ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2)
        ((p : ℝ) / 2) s
      = (residualCost p n h (min h n - s) : ℝ) / 2 := by
  rw [chamberVertexExponent_eq_chamberExponentNum p (min h n) (max h n) hs]
  congr 1
  have hks : min h n - (min h n - s) = s := by omega
  have hid := chamberExponentNum_eq_residualCost p n h (min h n - s) (by omega)
  rw [hks] at hid
  exact_mod_cast hid

/-- **The chamber minimum is the residual minimum, halved.** Print's `E⋆ = ½ minₜ c_t`.

The reindexing `s ↦ k − t` is a bijection of `{0, …, k}` with itself, so the two minima are over
the same finite family. -/
public theorem chamberMinExponent_eq_residualMinCost (p n h : ℕ) :
    chamberMinExponent (min h n) ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2)
        ((p : ℝ) / 2)
      = (residualMinCost p n h : ℝ) / 2 := by
  classical
  set k := min h n with hk
  set d := max h n with hd
  have hvert : ∀ s ∈ Finset.range (k + 1),
      chamberVertexExponent k (((d : ℝ) - k - 1) / 2) ((p : ℝ) / 2) s
        = (residualCost p n h (k - s) : ℝ) / 2 := by
    intro s hs
    rw [Finset.mem_range, Nat.lt_succ_iff] at hs
    exact chamberVertexExponent_eq_residualCost p n h hs
  refine le_antisymm ?_ ?_
  · -- the chamber minimum is at most every residual value, hence at most the residual minimum
    obtain ⟨t, ht, hval⟩ := exists_residualMinCost p n h
    have htk : t ≤ k := by
      simpa only [residualIndices, Finset.mem_range, Nat.lt_succ_iff] using ht
    have hmem : k - t ∈ Finset.range (k + 1) := by
      rw [Finset.mem_range]; omega
    have hle := Finset.inf'_le
      (chamberVertexExponent k (((d : ℝ) - k - 1) / 2) ((p : ℝ) / 2)) hmem
    rw [← chamberMinExponent] at hle
    have hkk : k - (k - t) = t := by omega
    rw [hvert _ hmem, hkk, hval] at hle
    exact hle
  · refine Finset.le_inf' _ _ ?_
    intro s hs
    rw [hvert s hs]
    have hsk : s ≤ k := by
      simpa only [Finset.mem_range, Nat.lt_succ_iff] using hs
    have hmem : k - s ∈ residualIndices n h := by
      simp only [residualIndices, Finset.mem_range, Nat.lt_succ_iff, ← hk]
      omega
    have := residualMinCost_le p n h (k - s) hmem
    have hcast : ((residualMinCost p n h : ℝ)) ≤ ((residualCost p n h (k - s) : ℝ)) := by
      exact_mod_cast this
    linarith

/-! ## The multiplicity

`chamberMinimizers_card` proves `N⋆ = #{i : A_i = ρ} + 1` for the abstract chamber parameters.
Composing it with the reindexing `t ↦ k − t` gives the candidate's multiplicity. -/

/-- **The candidate's multiplicity is print's `N⋆`.** The reindexing `t ↦ k − t` is an involution
of `{0, …, k}`, and it matches the two minimisations term by term, so it matches their sets of
minimisers. -/
public theorem residualMultiplicity_eq_chamberResonanceCount_succ (p n h : ℕ) :
    residualMultiplicity p n h
      = chamberResonanceCount (min h n) ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2)
          ((p : ℝ) / 2) + 1 := by
  classical
  rw [← chamberMinimizers_card (min h n) ((((max h n : ℕ) : ℝ) - (min h n : ℕ) - 1) / 2)
    ((p : ℝ) / 2), residualMultiplicity]
  have hmin := chamberMinExponent_eq_residualMinCost p n h
  have hmemI : ∀ t : ℕ, t ∈ residualIndices n h ↔ t ≤ min h n := by
    intro t
    rw [residualIndices, Finset.mem_range, Nat.lt_succ_iff]
  refine Finset.card_nbij' (fun t => min h n - t) (fun s => min h n - s) ?_ ?_ ?_ ?_
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht
    obtain ⟨htI, hval⟩ := ht
    have htk : t ≤ min h n := (hmemI t).1 htI
    rw [Finset.mem_coe]
    simp only []
    refine mem_chamberMinimizers.2 ⟨by omega, ?_⟩
    have hks : min h n - (min h n - t) = t := by omega
    rw [chamberVertexExponent_eq_residualCost p n h (show min h n - t ≤ min h n by omega),
      hks, hval, hmin]
  · intro s hs
    obtain ⟨hsk, hval⟩ := mem_chamberMinimizers.1 (Finset.mem_coe.1 hs)
    rw [Finset.mem_coe, Finset.mem_filter]
    simp only []
    refine ⟨(hmemI _).2 (by omega), ?_⟩
    have hstep := chamberVertexExponent_eq_residualCost p n h (show s ≤ min h n from hsk)
    rw [hval, hmin] at hstep
    have hEq : ((residualCost p n h (min h n - s) : ℝ)) = ((residualMinCost p n h : ℝ)) := by
      linarith
    exact_mod_cast hEq
  · intro t ht
    rw [Finset.mem_coe, Finset.mem_filter] at ht
    have htk : t ≤ min h n := (hmemI t).1 ht.1
    simp only []
    omega
  · intro s hs
    obtain ⟨hsk, -⟩ := mem_chamberMinimizers.1 (Finset.mem_coe.1 hs)
    simp only []
    omega

/-! ## The residual germ is O70's own loss at rank zero

`ResidualGerm.lean` defines print's `f(Y, X) = ‖YX‖²_F` through `matrixPairEquiv`, the same
packing `O70.lean` states `rrrLossCoords` through. So the two are not merely isomorphic objects
in isomorphic coordinates — they are the same function up to the factor `2`, and the
identification is a rewrite rather than a transport.

This is print's own Step 5 of Section 7 (p. 28): "at rank `r = 0` the truth is `C = 0` and
`2K = f(B, A)` with `(p, n, h) = (M, N, H)`". -/

/-- **`f(Y, X) = 2K` at the zero truth matrix.** -/
public theorem residualGerm_eq_two_mul_rrrLossCoords (p n h : ℕ)
    (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    residualGerm p n h w = 2 * rrrLossCoords p n h 0 w := by
  rw [rrrLossCoords, two_mul_rrrLoss_eq_frobeniusSq, sub_zero, residualGerm, residualX,
    residualY]

/-- Equivalently, `K = ½ f`. -/
public theorem rrrLossCoords_zero_eq (p n h : ℕ)
    (w : EuclideanSpace ℝ (Fin (h * n + p * h))) :
    rrrLossCoords p n h 0 w = residualGerm p n h w / 2 := by
  rw [residualGerm_eq_two_mul_rrrLossCoords]
  ring

/-! ## Theorem 8.1 in the candidate's own arithmetic

`hasLocalVolumeOrder_residualGerm` states the residual pair through the chamber quantities
`chamberMinExponent` and `chamberResonanceCount`. The two bridges above rewrite them as the
candidate's `residualMinCost / 2` and `residualMultiplicity`, at `k = min h n` and
`d = max h n`. On the wide shape `h ≤ n` those are `h` and `n`, so the rewrite is immediate. -/

/-- **Theorem 8.1, in the candidate's table.** The local pair of `‖YX‖²_F` at the origin is
`(½ minₜ c_t, #argmin)`, at every positive shape, conditional on `O70-EIGEN-LAW` and nothing
else.

No ordering between `h` and `n` is assumed: the wide case is the frontier read directly and the
tall case is the frontier read at the transposed matrix, and both land at `k = min h n`,
`d = max h n`, which is where the candidate's table is indexed. -/
public theorem hasLocalVolumeOrder_residualGerm_table (hEigen : EigenvalueLawStatement)
    (p n h : ℕ) (hp : 0 < p) (hn : 0 < n) (hh : 0 < h) :
    HasLocalVolumeOrder (residualGerm p n h) 0
      ((residualMinCost p n h : ℝ) / 2) (residualMultiplicity p n h) := by
  rw [← chamberMinExponent_eq_residualMinCost p n h,
    residualMultiplicity_eq_chamberResonanceCount_succ p n h]
  exact hasLocalVolumeOrder_residualGerm_min hEigen p n h hp hn hh

/-! ## The printed table at the canonical representative

Everything the candidate's §10 assembles is now available: the chart at every feasible stratum
(`isEliminationChart_of_feasible`), the pair of the comparison germ in chart coordinates
(`hasLocalVolumeOrder_chartGerm_any`), the transport across the chart
(`hasLocalVolumeOrder_rrrLoss_canonical`) and the residual pair above. What remains is the
arithmetic identification of the assembled pair with the printed one, and one positivity fact
the product rule needs.
-/

/-- With every shape parameter positive the residual objective is strictly positive at every
admissible index. Factored, it is `(h − t)(n − t) + t p`: below the endpoint the first term is
at least one, and at the endpoint `t` is `min h n > 0` and the second term is `t p > 0`.

This is what the product rule needs. `HasLocalVolumeOrder`'s degenerate branch is reserved for a
germ vanishing on a whole neighbourhood, so a zero exponent there would be a different claim. -/
public theorem residualCost_pos {p n h t : ℕ} (hp : 0 < p) (hn : 0 < n) (hh : 0 < h)
    (ht : t ≤ min h n) : 0 < residualCost p n h t := by
  rw [residualCost_factored]
  rcases lt_or_eq_of_le ht with hlt | heq
  · have h1 : (1 : ℤ) ≤ (h : ℤ) - t := by omega
    have h2 : (1 : ℤ) ≤ (n : ℤ) - t := by omega
    have h3 : (0 : ℤ) ≤ (t : ℤ) * p := by positivity
    nlinarith
  · have htp : 0 < t := by omega
    have h1 : (0 : ℤ) ≤ (h : ℤ) - t := by omega
    have h2 : (0 : ℤ) ≤ (n : ℤ) - t := by omega
    have h3 : (0 : ℤ) < (t : ℤ) * p := by positivity
    nlinarith [mul_nonneg h1 h2]

public theorem residualMinCost_pos {p n h : ℕ} (hp : 0 < p) (hn : 0 < n) (hh : 0 < h) :
    0 < residualMinCost p n h := by
  rw [residualMinCost_eq_argmin]
  exact residualCost_pos hp hn hh (by rw [residualArgmin]; exact min_le_left _ _)

/-- **The printed local volume order, at the canonical representative of a feasible stratum.** The
exponent is
`(q + E⋆)/2` with `q = Ma + bN − ab` from the transverse block and `E⋆` the residual minimum, and
the multiplicity is the number of residual minimisers — which is exactly `o70Pair`.

The three positivity hypotheses are the nondegeneracy of the residual shape; the degenerate
shapes have their own pair (`hasLocalVolumeOrder_chartGerm_residual_zero`) and a different
printed value. `hEigen` is the Wishart frontier and the only hypothesis that is not arithmetic. -/
public theorem hasLocalVolumeOrder_rrrLoss_canonical_table (hEigen : EigenvalueLawStatement)
    {M N H r a b : ℕ} (hra : r ≤ a) (hrb : r ≤ b) (hab : a + b ≤ H + r)
    (haN : a ≤ N) (hbM : b ≤ M)
    (hp : 0 < M - b) (hn : 0 < N - a) (hh : 0 < H + r - a - b) :
    HasLocalVolumeOrder
      (fun x => rrrLoss (partialIdMatrix M N r) ((matrixPairEquiv M N H).symm x).1
        ((matrixPairEquiv M N H).symm x).2)
      (matrixPairCoords (canonicalA N H a b r) (canonicalB M H b r))
      ((o70Lambda M N H r a b : ℚ) : ℝ) (o70Multiplicity M N H r a b) := by
  have hres := hasLocalVolumeOrder_residualGerm_table hEigen (M - b) (N - a) (H + r - a - b)
    hp hn hh
  have hlamR : (0 : ℝ) < (residualMinCost (M - b) (N - a) (H + r - a - b) : ℝ) / 2 := by
    have := residualMinCost_pos (p := M - b) (n := N - a) (h := H + r - a - b) hp hn hh
    have hcast : (0 : ℝ) < (residualMinCost (M - b) (N - a) (H + r - a - b) : ℝ) := by
      exact_mod_cast this
    linarith
  have hchart := hasLocalVolumeOrder_chartGerm_any (q := elimQ M N a b) (g := elimGauge M N H r a b)
    hlamR hres
  have hloss := hasLocalVolumeOrder_rrrLoss_canonical hra hrb hab haN hbM hchart
  have hlam : ((o70Lambda M N H r a b : ℚ) : ℝ)
      = (elimQ M N a b : ℝ) / 2 + (residualMinCost (M - b) (N - a) (H + r - a - b) : ℝ) / 2 := by
    rw [o70Lambda]
    simp only [o70Shape, o70Q]
    rw [← elimQ_cast hbM]
    push_cast
    ring
  rw [hlam]
  exact hloss

/-! ## P3 at actual matrices

`O70.lean` proves the arithmetic half of P3 — `awLambda` is a lower bound for the candidate table
on every admissible rank stratum, and is attained. Composing it with `admissible_of_mul_eq`
carries it to actual factorizations. These two live here rather than in `O70.lean` because
`admissible_of_mul_eq` is in `ReducedRank.lean`, which the statement layer deliberately does not
import.
-/

/-- **Every factorization's candidate value is at least the printed Aoyagi–Watanabe value.**
Unconditional: no eigenvalue law, no exact-local-pair existence, no Aoyagi–Watanabe hypothesis.

It is a claim about the *candidate table*, not about the model's actual local learning
coefficients. -/
public theorem awLambda_le_of_factorization {M N H : ℕ} (hM : 0 < M) (hN : 0 < N) (hH : 0 < H)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    awLambda M N H (B * A).rank ≤ o70Lambda M N H (B * A).rank A.rank B.rank :=
  awLambda_le_o70Lambda _ _ _ _ _ _ (admissible_of_mul_eq hM hN hH A B)

/-- The same, phrased over the zero fiber of a fixed truth matrix `C`. -/
public theorem awLambda_le_on_fiber {M N H : ℕ} (hM : 0 < M) (hN : 0 < N) (hH : 0 < H)
    {C : Matrix (Fin M) (Fin N) ℝ}
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) (hC : B * A = C) :
    awLambda M N H C.rank ≤ o70Lambda M N H C.rank A.rank B.rank := by
  subst hC
  exact awLambda_le_of_factorization hM hN hH A B

/-! ## The degenerate residual shapes

`p = 0`, `n = 0` or `h = 0` are legitimate strata — `b = M`, `a = N` and `a + b = H + r`
respectively — and there the residual germ vanishes identically. The printed table agrees: the
objective is zero at `t = min h n` and nowhere else, so the minimum is `0` and the multiplicity
is `1`, and the printed pair reduces to the transverse pair `(q/2, 1)`.
-/

public theorem residualCost_eq_zero_iff_of_degenerate {p n h t : ℕ}
    (hdeg : p = 0 ∨ n = 0 ∨ h = 0) (ht : t ≤ min h n) :
    residualCost p n h t = 0 ↔ t = min h n := by
  constructor
  · intro hz
    rw [residualCost_factored] at hz
    have h1 : (0 : ℤ) ≤ ((h : ℤ) - t) * ((n : ℤ) - t) :=
      mul_nonneg (by omega) (by omega)
    have h2 : (0 : ℤ) ≤ (t : ℤ) * p := by positivity
    have h3 : ((h : ℤ) - t) * ((n : ℤ) - t) = 0 := by linarith
    rcases mul_eq_zero.1 h3 with h4 | h4 <;> omega
  · rintro rfl
    rw [residualCost_factored]
    rcases hdeg with rfl | rfl | rfl
    · rcases Nat.le_total h n with hle | hle
      · rw [min_eq_left hle]; simp
      · rw [min_eq_right hle]; simp
    · simp
    · simp

public theorem residualMinCost_eq_zero_of_degenerate {p n h : ℕ}
    (hdeg : p = 0 ∨ n = 0 ∨ h = 0) : residualMinCost p n h = 0 := by
  refine le_antisymm ?_ (residualMinCost_nonneg p n h)
  have hmem : min h n ∈ residualIndices n h := Finset.self_mem_range_succ _
  have := residualMinCost_le p n h (min h n) hmem
  rwa [(residualCost_eq_zero_iff_of_degenerate hdeg (le_refl _)).2 rfl] at this

public theorem residualMultiplicity_eq_one_of_degenerate {p n h : ℕ}
    (hdeg : p = 0 ∨ n = 0 ∨ h = 0) : residualMultiplicity p n h = 1 := by
  rw [residualMultiplicity, residualMinCost_eq_zero_of_degenerate hdeg]
  rw [Finset.card_eq_one]
  refine ⟨min h n, Finset.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩⟩
  · refine Finset.mem_filter.2 ⟨Finset.self_mem_range_succ _, ?_⟩
    exact (residualCost_eq_zero_iff_of_degenerate hdeg (le_refl _)).2 rfl
  · intro t ht
    obtain ⟨htmem, htz⟩ := Finset.mem_filter.1 ht
    have htle : t ≤ min h n := Nat.lt_succ_iff.1 (Finset.mem_range.1 htmem)
    exact (residualCost_eq_zero_iff_of_degenerate hdeg htle).1 htz

/-! ## The printed table at the canonical representative, at every stratum -/

/-- **The printed local volume order at the canonical representative, with no *residual*-shape
hypothesis.** The three positivity hypotheses on the shape are traded for `0 < M`, `0 < N`,
`0 < H`, all three of which are load-bearing.

The proof splits on whether the residual block is degenerate. In the degenerate branch the
printed value degenerates with it — the objective is zero exactly at `t = min h n`, so the
minimum is `0` and the multiplicity is `1` — and what has to be supplied instead is
`0 < elimQ M N a b`, so that the transverse block can carry the pair. That is where the
positivity of `M`, `N` and `H` is spent: `elimQ = a(M − b) + bN` vanishes only at `a = b = 0`,
which forces `r = 0` and residual shape `(M, N, H)`, and that shape is degenerate only if one of
`M`, `N`, `H` is zero. So an empty transverse block and an empty residual block never occur
together, and the degenerate branch always has a nonempty transverse block to fall back on. -/
public theorem hasLocalVolumeOrder_rrrLoss_canonical_table_all (hEigen : EigenvalueLawStatement)
    {M N H r a b : ℕ} (hM : 0 < M) (hN : 0 < N) (hH : 0 < H) (hra : r ≤ a) (hrb : r ≤ b)
    (hab : a + b ≤ H + r) (haN : a ≤ N) (hbM : b ≤ M) :
    HasLocalVolumeOrder
      (fun x => rrrLoss (partialIdMatrix M N r) ((matrixPairEquiv M N H).symm x).1
        ((matrixPairEquiv M N H).symm x).2)
      (matrixPairCoords (canonicalA N H a b r) (canonicalB M H b r))
      ((o70Lambda M N H r a b : ℚ) : ℝ) (o70Multiplicity M N H r a b) := by
  by_cases hdeg : M - b = 0 ∨ N - a = 0 ∨ H + r - a - b = 0
  · -- the residual block is empty; the pair is the transverse pair
    have hab0 : 0 < a ∨ 0 < b := by
      rcases hdeg with hd | hd | hd
      · exact Or.inr (by omega)
      · exact Or.inl (by omega)
      · omega
    have hq : 0 < elimQ M N a b := by
      simp only [elimQ]
      rcases Nat.eq_zero_or_pos b with rfl | hb
      · have ha : 0 < a := by omega
        have : 0 < a * (M - 0) := Nat.mul_pos ha (by omega)
        omega
      · have : 0 < b * N := Nat.mul_pos hb hN
        omega
    have hchart := hasLocalVolumeOrder_chartGerm_residual_zero
      (q := elimQ M N a b) (p := M - b) (h := H + r - a - b) (n := N - a)
      (g := elimGauge M N H r a b) hq hdeg
    have hloss := hasLocalVolumeOrder_rrrLoss_canonical hra hrb hab haN hbM hchart
    have hlam : ((o70Lambda M N H r a b : ℚ) : ℝ) = (elimQ M N a b : ℝ) / 2 := by
      rw [o70Lambda]
      simp only [o70Shape, o70Q, residualMinCost_eq_zero_of_degenerate hdeg]
      rw [← elimQ_cast hbM]
      push_cast
      ring
    have hmul : o70Multiplicity M N H r a b = 1 := by
      rw [o70Multiplicity]
      simp only [o70Shape]
      exact residualMultiplicity_eq_one_of_degenerate hdeg
    rw [hlam, hmul]
    exact hloss
  · simp only [not_or] at hdeg
    obtain ⟨hp, hn, hh⟩ := hdeg
    exact hasLocalVolumeOrder_rrrLoss_canonical_table hEigen hra hrb hab haN hbM
      (Nat.pos_of_ne_zero hp) (Nat.pos_of_ne_zero hn) (Nat.pos_of_ne_zero hh)

/-! ## The order-level table

Print's five feasibility inequalities hold at the actual ranks of any factorization: three are
`Matrix.rank_mul_le_left`, `Matrix.rank_mul_le_right` and the shape bounds, and the fourth is
Sylvester's rank inequality (`rank_add_rank_le_of_mul`, `ReducedRank.lean`). So no admissibility hypothesis is
needed — the table is claimed at *every* factorization of *every* truth matrix, which is print's
own quantifier.
-/

/-- **Gate BΘ.** The candidate's table is the local volume order of the reduced-rank loss at
every factorization of every truth matrix, under the Wishart frontier and nothing else.

The chain is print's section 10 in order: step 1 is the orbit reduction
(`hasLocalVolumeOrder_rrrLoss_of_canonical`), which normalises the truth matrix at the same time
because the action preserves the product; steps 2 to 6 are the chart and the block calculus
(`hasLocalVolumeOrder_rrrLoss_canonical_table_all`).

This is the two-sided *order* relation, not print's exact asymptotic. Upgrading it to
`IsO70RankTable` is `isO70RankTable_of_volumeOrder` and needs `O70ExactLocalPairsExist`, which
remains a frontier. -/
public theorem isO70VolumeOrderTable_o70Pair (hEigen : EigenvalueLawStatement) :
    IsO70VolumeOrderTable o70Pair := by
  intro M N H hM hN hH C A B hC
  have hra : C.rank ≤ A.rank := by rw [← hC]; exact Matrix.rank_mul_le_right B A
  have hrb : C.rank ≤ B.rank := by rw [← hC]; exact Matrix.rank_mul_le_left B A
  have hab : A.rank + B.rank ≤ H + C.rank := by
    rw [← hC]; exact rank_add_rank_le_of_mul A B
  have haN : A.rank ≤ N := by
    simpa using Matrix.rank_le_card_width A
  have hbM : B.rank ≤ M := by
    simpa using Matrix.rank_le_card_height B
  have hcan := hasLocalVolumeOrder_rrrLoss_canonical_table_all hEigen hM hN hH hra hrb hab haN hbM
  exact hasLocalVolumeOrder_rrrLoss_of_canonical hC hra hrb hab hcan

/-- **P2 under both frontiers.** The order table upgrades to print's exact table as soon as
exact local pairs are known to exist — the value-free hypothesis `O70ExactLocalPairsExist`, which
assumes nothing about *what* the pair is. -/
public theorem isO70RankTable_o70Pair (hEigen : EigenvalueLawStatement)
    (hex : O70ExactLocalPairsExist) : IsO70RankTable o70Pair :=
  isO70RankTable_of_volumeOrder o70Pair hex (isO70VolumeOrderTable_o70Pair hEigen)

/-- **P1 under both frontiers.** The local pair depends only on the three ranks, witnessed by the
printed table rather than by an anonymous existential. -/
public theorem o70DependsOnRanksOnly_of_frontiers (hEigen : EigenvalueLawStatement)
    (hex : O70ExactLocalPairsExist) : O70DependsOnRanksOnly :=
  ⟨o70Pair, isO70RankTable_o70Pair hEigen hex⟩

/-! ## P3 at the germs

`o70_aw_value_strata_correct` characterises `o70Minimizers` against the *table*, and holds by
construction. This characterises it against the actual germs, which is print's clause: the strata
on which the local coefficient attains its minimum over the zero fiber.
-/

/-- **P3 under both frontiers, at the germs.** A stratum lies in the candidate's minimiser set
exactly when the actual local coefficient there is a lower bound for the local coefficient
everywhere on the zero fiber of the same truth matrix.

The two frontiers enter for different reasons. `hEigen` identifies the actual local coefficient
with the table, through `isO70VolumeOrderTable_o70Pair` and `exactLocalPair_eq_volumeOrder`. `hex`
is used only in the `←` direction, to produce an actual point of the fiber at the stratum where
the printed value is attained; without it the minimality hypothesis would have nothing to compare
against and the direction would fail.

`hex` is assumed at full strength — an exact pair at every factorization of every truth matrix —
and this proof calls it once, at the balanced realization `(a, b) = (r, r)` of the given `C`. The
frontier is stated as the candidate cites it, not pared down to what one consumer happens to
need.

The arithmetic is `o70_fiber_minimum_correct`, which is unconditional.
`exists_factorization_of_feasible` is what turns the attaining stratum from an arithmetic tuple
into an actual pair of matrices. -/
public theorem isO70MinimizerCharacterization_o70Minimizers
    (hEigen : EigenvalueLawStatement) (hex : O70ExactLocalPairsExist) :
    IsO70MinimizerCharacterization o70Minimizers := by
  intro M N H hM hN hH C A B hC lam m hpair
  have hadm : AdmissibleRankData M N H C.rank A.rank B.rank := by
    have h := admissible_of_mul_eq hM hN hH A B
    rwa [hC] at h
  have hlam : lam = ((o70Lambda M N H C.rank A.rank B.rank : ℚ) : ℝ) :=
    (exactLocalPair_eq_volumeOrder hpair
      (isO70VolumeOrderTable_o70Pair hEigen M N H hM hN hH C A B hC)).1
  obtain ⟨hlb, a, b, habm, hattain⟩ :=
    o70_fiber_minimum_correct M N H C.rank hM hN hH hadm.2.2.2.1
  simp only [o70Pair] at hlb hattain
  constructor
  · rintro hmem A' B' hC' lam' m' hpair'
    have hadm' : AdmissibleRankData M N H C.rank A'.rank B'.rank := by
      have h := admissible_of_mul_eq hM hN hH A' B'
      rwa [hC'] at h
    have hlam' : lam' = ((o70Lambda M N H C.rank A'.rank B'.rank : ℚ) : ℝ) :=
      (exactLocalPair_eq_volumeOrder hpair'
        (isO70VolumeOrderTable_o70Pair hEigen M N H hM hN hH C A' B' hC')).1
    simp only [o70Minimizers, Set.mem_ofPred_eq, O70RankStratum.Admissible] at hmem
    rw [hlam, hlam', hmem.2]
    exact_mod_cast hlb A'.rank B'.rank hadm'
  · intro hmin
    simp only [o70Minimizers, Set.mem_ofPred_eq, O70RankStratum.Admissible]
    refine ⟨hadm, le_antisymm ?_ (hlb A.rank B.rank hadm)⟩
    obtain ⟨A', B', hC', hA', hB'⟩ := exists_factorization_of_feasible C habm.2.2.2.2
    obtain ⟨lam', m', hpair'⟩ := hex M N H hM hN hH C A' B' hC'
    have hlam' : lam' = ((o70Lambda M N H C.rank A'.rank B'.rank : ℚ) : ℝ) :=
      (exactLocalPair_eq_volumeOrder hpair'
        (isO70VolumeOrderTable_o70Pair hEigen M N H hM hN hH C A' B' hC')).1
    have hle := hmin A' B' hC' lam' m' hpair'
    rw [hlam, hlam', hA', hB'] at hle
    rw [← hattain]
    exact_mod_cast hle

/-! ## P2 in print's primary normalization

`MAIS-A6.tex` `def:local` defines the local pair by the zeta function and only then says the
volume form is equivalent. Everything above is about the volume form. `O70ZetaPoleBridge` names
that substitution and does not prove it; this is what it buys.
-/

/-- **The candidate's table is the zeta pair too, under three hypotheses.** `isO70RankTable_o70Pair`
gives the volume pair; the bridge carries it to print's threshold and pole order.

The three binders are not the same kind of debt. `EigenvalueLawStatement` (Muirhead 3.2.1/3.2.17
after James 1954) and `O70ExactLocalPairsExist` (the candidate's own section 13 names it as the
single non-elementary citation in the derivation) are results the *candidate* cites, so assuming
them leaves its derivation inside the cone. `O70ZetaPoleBridge` is a gap between the atlas and the
*problem statement's* own primary definition — print asserts it, citing `[lau2023]`, and the
candidate's Lemma 6.1(ii) reaches only `C^∞` compactly supported weights, not print's sharp ball.

The neutral branch, on which the bridge would be false rather than unproved, is unreachable here:
`not_eventually_rrrLossCoords_eq_zero_of_pos` is unconditional and needs no factorization
hypothesis, and the bridge's own quantifiers already carry the positivity that invokes it. -/
public theorem hasZetaPoleOrder_o70Pair (hbridge : O70ZetaPoleBridge)
    (hEigen : EigenvalueLawStatement) (hex : O70ExactLocalPairsExist)
    (M N H : ℕ) (hM : 0 < M) (hN : 0 < N) (hH : 0 < H)
    (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) (hC : B * A = C) :
    HasZetaPoleOrder (rrrLossCoords M N H C) (matrixPairCoords A B)
      (((o70Pair M N H C.rank A.rank B.rank).1 : ℚ) : ℝ)
      (o70Pair M N H C.rank A.rank B.rank).2 :=
  hbridge M N H hM hN hH C A B hC _ _
    (isO70RankTable_o70Pair hEigen hex M N H hM hN hH C A B hC)

/-- **The O70 germ is real-analytic.** Print's `def:local` takes the local pair of a nonnegative
*real-analytic* `K`. `rrrLoss_nonneg` supplies the first adjective and this the second, so the
germs `O70ZetaPoleBridge` is quantified over do lie in the class print's definition is about.

That is not a decoration. The general form of the bridge — over every nonnegative germ, with no
analyticity — is false, and this is the hypothesis whose absence makes it false. Narrowing the
frontier to these germs is only defensible if these germs satisfy it, and now that is
kernel-checked rather than asserted. -/
public theorem analyticAt_rrrLossCoords {M N H : ℕ} (C : Matrix (Fin M) (Fin N) ℝ)
    (x : EuclideanSpace ℝ (Fin (H * N + M * H))) :
    AnalyticAt ℝ (rrrLossCoords M N H C) x :=
  analyticAt_rrrLoss_symm_coords C x

end AISafetyAtlas.Conjectures.MAIS
