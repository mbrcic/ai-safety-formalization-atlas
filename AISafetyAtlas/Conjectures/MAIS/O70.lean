module

public import AISafetyAtlas.SingularLearning.AoyagiWatanabe
public import AISafetyAtlas.SingularLearning.Coordinates
public import AISafetyAtlas.SingularLearning.LocalPair
public import AISafetyAtlas.SingularLearning.Loss
public import AISafetyAtlas.SingularLearning.ZetaPair
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.FinCases

/-!
# MAIS-O70 — local coefficients on the reduced-rank template

`prob:calibration`, `MAIS-A6.tex` line 491. Print asks three things:

> "For reduced-rank regression with parameters `(N,M,H,r)`, **prove that** the
> local pair `(λ(w*),m(w*))` at a factorization `w* = (A,B) ∈ W₀` **depends only
> on** `(rank A, rank B)`, and **compute the resulting table**. **Hence
> characterize the strata** on which `λ(w*)` equals the minimum in Theorem
> `thm:aw`."

That is a structural consequence (P1), an explicit answer (P2), and a second
explicit answer (P3). This module is the **arithmetic layer**: the candidate's
proposed table as computable data, and the propositions that grade it.

## What this module does and does not assert

Defining a proposition asserts nothing about its truth. `o70Pair` is a
*candidate*, transcribed from the issue attachment; the propositions
`IsO70FiberMinimumTable` and `IsO70AWValueStratumTable` say what it would mean
for that candidate to be right. Nothing here claims `o70Pair` is the local pair
of the model — that is the analytic layer, and it lives in `O70Proof.lean`, where
it holds only under two frontier hypotheses the atlas does not discharge.

## Why P3 needs no Aoyagi–Watanabe hypothesis

`thm:aw` states its case list and then, in the same sentence:

> "Equivalently, `λ` is the minimum of `λ(w)` over `w ∈ W₀`, and `m` is the
> largest `m(w)` among the minimizers."

So "the minimum in Theorem `thm:aw`" *is* `min_{w ∈ W₀} λ(w)`, by print. P3 is
therefore a statement about the factorization fiber, provable from the table
itself, and not an import of the published theorem. Assuming Aoyagi–Watanabe
here would be assuming an identification print supplies.

## The `ℕ`-subtraction trap in the residual shape

The residual shape is `(p, n, h) = (M - b, N - a, H - a - b + r)`. Written that
way in `ℕ` the third is wrong: `H - a - b + r` parses as `((H - a) - b) + r`, and
at `H = a = b = r = 2` — which is feasible, since `a + b = 4 ≤ H + r = 4` — that
gives `2` where the true value is `0`. It is written `H + r - a - b` below, which
is exact whenever `a + b ≤ H + r`, i.e. on every feasible stratum.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open Finset
open AISafetyAtlas.SingularLearning

/-! ## The candidate's residual table

Corollary 1.3 of the issue attachment gives the residual pair of the shape
`(p, n, h)` as a discrete minimisation:

    λ₀ = ½ · min { hn + t(p - h - n) + t² : 0 ≤ t ≤ min(h, n) },   m₀ = #argmin.

The objective is formed in `ℤ`: `p - h - n` is a genuine difference of unknown
sign, and truncating it in `ℕ` changes the minimum. -/

/-- The objective of the candidate's residual minimisation, at index `t`. -/
@[expose] public def residualCost (p n h t : ℕ) : ℤ :=
  (h : ℤ) * n + t * ((p : ℤ) - h - n) + (t : ℤ) ^ 2

/-- The index set `{0, 1, …, min h n}` of the residual minimisation. -/
@[expose] public def residualIndices (n h : ℕ) : Finset ℕ := range (min h n + 1)

public theorem residualIndices_nonempty (n h : ℕ) : (residualIndices n h).Nonempty :=
  ⟨0, mem_range.mpr (Nat.succ_pos _)⟩

public theorem zero_mem_residualIndices (n h : ℕ) : 0 ∈ residualIndices n h :=
  mem_range.mpr (Nat.succ_pos _)

/-- The candidate's residual threshold numerator: the minimum of `residualCost`
over `0 ≤ t ≤ min h n`. -/
@[expose] public def residualMinCost (p n h : ℕ) : ℤ :=
  (residualIndices n h).inf' (residualIndices_nonempty n h) (residualCost p n h)

/-- The candidate's residual multiplicity: the number of minimisers. -/
@[expose] public def residualMultiplicity (p n h : ℕ) : ℕ :=
  ((residualIndices n h).filter fun t => residualCost p n h t = residualMinCost p n h).card

public theorem residualMinCost_le (p n h t : ℕ) (ht : t ∈ residualIndices n h) :
    residualMinCost p n h ≤ residualCost p n h t :=
  inf'_le _ ht

public theorem le_residualMinCost {p n h : ℕ} {c : ℤ}
    (H : ∀ t ∈ residualIndices n h, c ≤ residualCost p n h t) :
    c ≤ residualMinCost p n h :=
  le_inf' _ _ H

/-- The minimum is attained: some index realises it. -/
public theorem exists_residualMinCost (p n h : ℕ) :
    ∃ t ∈ residualIndices n h, residualCost p n h t = residualMinCost p n h := by
  obtain ⟨t, ht, hval⟩ :=
    exists_mem_eq_inf' (residualIndices_nonempty n h) (residualCost p n h)
  exact ⟨t, ht, hval.symm⟩

/-- At least one minimiser, so the candidate multiplicity is positive. -/
public theorem residualMultiplicity_pos (p n h : ℕ) : 0 < residualMultiplicity p n h := by
  obtain ⟨t, ht, hval⟩ := exists_residualMinCost p n h
  refine card_pos.mpr ⟨t, ?_⟩
  simp only [mem_filter]
  exact ⟨ht, hval⟩

/-! ## Closing the residual minimisation

`residualCost p n h` is a convex integer quadratic in `t` with real vertex at
`(h + n - p)/2`. Its minimum over `0 ≤ t ≤ min h n` is therefore attained at that
vertex clamped to the range, and when the vertex is a half-integer the two
neighbouring indices give *equal* values — which is exactly why the candidate's
multiplicity is `2` in the odd-parity case.

`ℕ` arithmetic does the clamping for free: `h + n - p` truncates to `0` when
`p > h + n`, which is the correct left endpoint, and `/2` is the floor. -/

/-- The closed-form minimiser of the residual objective. -/
@[expose] public def residualArgmin (p n h : ℕ) : ℕ := min (min h n) ((h + n - p) / 2)

public theorem residualArgmin_mem (p n h : ℕ) :
    residualArgmin p n h ∈ residualIndices n h := by
  simp only [residualIndices, residualArgmin, mem_range, Nat.lt_succ_iff]
  exact min_le_left _ _

/-- The difference of two costs factors. This is the whole convexity argument. -/
public theorem residualCost_sub (p n h s t : ℕ) :
    residualCost p n h t - residualCost p n h s
      = ((t : ℤ) - s) * ((t : ℤ) + s + p - h - n) := by
  unfold residualCost; ring

public theorem residualCost_argmin_le (p n h t : ℕ) (ht : t ∈ residualIndices n h) :
    residualCost p n h (residualArgmin p n h) ≤ residualCost p n h t := by
  have hrange : t ≤ min h n := by
    simpa only [residualIndices, mem_range, Nat.lt_succ_iff] using ht
  set s := residualArgmin p n h with hs
  have hsmin : s ≤ min h n := by rw [hs, residualArgmin]; exact min_le_left _ _
  have hsdiv : s ≤ (h + n - p) / 2 := by rw [hs, residualArgmin]; exact min_le_right _ _
  have hsdef : s = min (min h n) ((h + n - p) / 2) := hs
  have key : 0 ≤ ((t : ℤ) - s) * ((t : ℤ) + s + p - h - n) := by
    rcases Nat.lt_trichotomy t s with hc | hc | hc
    · -- below the vertex: both factors are nonpositive
      have h1 : (t : ℤ) - s ≤ 0 := by omega
      have h2 : (t : ℤ) + s + p - h - n ≤ 0 := by omega
      nlinarith
    · subst hc; simp
    · -- above the vertex: `s` cannot be the clamped endpoint, so it is the floor
      have hsne : s < min h n := lt_of_lt_of_le hc hrange
      have hfloor : s = (h + n - p) / 2 := by omega
      have h1 : (0 : ℤ) ≤ (t : ℤ) - s := by omega
      have h2 : (0 : ℤ) ≤ (t : ℤ) + s + p - h - n := by omega
      positivity
  have := residualCost_sub p n h s t
  linarith

public theorem residualMinCost_eq_argmin (p n h : ℕ) :
    residualMinCost p n h = residualCost p n h (residualArgmin p n h) :=
  le_antisymm (residualMinCost_le _ _ _ _ (residualArgmin_mem p n h))
    (le_residualMinCost fun t ht => residualCost_argmin_le p n h t ht)

/-! ### The residual minimum, regime by regime

Three unbalanced regimes clamp the vertex to an endpoint of `[0, min h n]`, and
`ℕ` arithmetic already encodes the clamp, so `omega` identifies `residualArgmin`
in each. The balanced regime is handled inline, where its parity split lives. -/

private theorem residualMinCost_of_lt_left (p n h : ℕ) (hlt : n + h < p) :
    residualMinCost p n h = (h : ℤ) * n := by
  have h0 : residualArgmin p n h = 0 := by unfold residualArgmin; omega
  rw [residualMinCost_eq_argmin, h0]
  unfold residualCost
  push_cast
  ring

private theorem residualMinCost_of_lt_mid (p n h : ℕ) (hlt : p + h < n) :
    residualMinCost p n h = (h : ℤ) * p := by
  have h0 : residualArgmin p n h = h := by unfold residualArgmin; omega
  rw [residualMinCost_eq_argmin, h0]
  unfold residualCost
  ring

private theorem residualMinCost_of_lt_right (p n h : ℕ) (hlt : p + n < h) :
    residualMinCost p n h = (n : ℤ) * p := by
  have h0 : residualArgmin p n h = n := by unfold residualArgmin; omega
  rw [residualMinCost_eq_argmin, h0]
  unfold residualCost
  ring

/-! ## The candidate's local table

Theorem 1.1 of the issue attachment: at a stratum with `(rank A, rank B) = (a,b)`
over a truth of rank `r`, the local pair is `½(q + λ₀-numerator)` and `m₀`, with

    q = Ma + bN - ab,   (p, n, h) = (M - b, N - a, H + r - a - b). -/

/-- The candidate's `q = Ma + bN - ab`, formed in `ℤ`. It does not depend on the
truth rank `r`; only the residual shape does. -/
@[expose] public def o70Q (M N a b : ℕ) : ℤ := (M : ℤ) * a + (b : ℤ) * N - (a : ℤ) * b

/-- The residual shape at a stratum. `H + r - a - b` is exact on feasible
strata; see the module docstring for why it is not written `H - a - b + r`. -/
@[expose] public def o70Shape (M N H r a b : ℕ) : ℕ × ℕ × ℕ := (M - b, N - a, H + r - a - b)

/-- The candidate's local learning coefficient at a rank stratum. -/
@[expose] public def o70Lambda (M N H r a b : ℕ) : ℚ :=
  let s := o70Shape M N H r a b
  ((o70Q M N a b + residualMinCost s.1 s.2.1 s.2.2 : ℤ) : ℚ) / 2

/-- The candidate's local multiplicity at a rank stratum. -/
@[expose] public def o70Multiplicity (M N H r a b : ℕ) : ℕ :=
  let s := o70Shape M N H r a b
  residualMultiplicity s.1 s.2.1 s.2.2

/-- **The candidate answer to P2**, transcribed from the issue attachment.
Computable and `ℚ`-valued, so finite checks exercise the same object the
propositions below grade. -/
@[expose] public def o70Pair (M N H r a b : ℕ) : ℚ × ℕ :=
  (o70Lambda M N H r a b, o70Multiplicity M N H r a b)

public theorem o70Multiplicity_pos (M N H r a b : ℕ) : 0 < o70Multiplicity M N H r a b :=
  residualMultiplicity_pos _ _ _

/-! ## P3, the arithmetic layer

Two propositions. The first says the printed Aoyagi–Watanabe value really is the
attained minimum of the table over the admissible strata — lower bound plus
attainment, which avoids an `sInf` encoding and its empty-set side conditions.
The second identifies exactly which strata attain it.

Both range over `AdmissibleRankData`, the single shared domain: `Feasible` alone
admits zero ambient dimensions, and every such stratum satisfies the numeric
equality, so an unguarded predicate would silently force degenerate strata into
the minimiser set. -/

/-- A rank stratum of the fiber, bundled. -/
public structure O70RankStratum where
  M : ℕ
  N : ℕ
  H : ℕ
  r : ℕ
  a : ℕ
  b : ℕ
  deriving DecidableEq

/-- The bundled projection onto the shared admissibility predicate. -/
@[expose] public def O70RankStratum.Admissible (s : O70RankStratum) : Prop :=
  AdmissibleRankData s.M s.N s.H s.r s.a s.b

public instance (s : O70RankStratum) : Decidable s.Admissible := by
  unfold O70RankStratum.Admissible; infer_instance

/-- **P3, lower bound and attainment.** `awLambda` is a lower bound for the table
on every admissible stratum, and some admissible stratum attains it. By print's
own gloss on `thm:aw`, this is exactly "λ is the minimum of λ(w) over W₀". -/
@[expose] public def IsO70FiberMinimumTable (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ) : Prop :=
  ∀ M N H r : ℕ, 0 < M → 0 < N → 0 < H → r ≤ min M (min N H) →
    (∀ a b, AdmissibleRankData M N H r a b →
        awLambda M N H r ≤ (f M N H r a b).1) ∧
      ∃ a b, AdmissibleRankData M N H r a b ∧
        (f M N H r a b).1 = awLambda M N H r

/-- **P3, the characterisation.** The strata whose table value equals the number
printed by `thm:aw`. -/
@[expose] public def IsO70AWValueStratumTable
    (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ) (S : Set O70RankStratum) : Prop :=
  ∀ s : O70RankStratum, s ∈ S ↔ s.Admissible ∧
    (f s.M s.N s.H s.r s.a s.b).1 = awLambda s.M s.N s.H s.r

/-- The candidate's proposed minimiser set: exactly the admissible strata whose
table value is the printed one. -/
@[expose] public def o70Minimizers : Set O70RankStratum :=
  {s | s.Admissible ∧ o70Lambda s.M s.N s.H s.r s.a s.b = awLambda s.M s.N s.H s.r}

/-- The candidate's minimiser set satisfies the characterisation by construction.
This is P3's *classification* half; it carries no arithmetic content on its own,
and is worth nothing without `IsO70FiberMinimumTable`, which is what makes the
value a minimum rather than merely a number. -/
public theorem o70_aw_value_strata_correct :
    IsO70AWValueStratumTable o70Pair o70Minimizers := by
  intro s
  simp only [o70Minimizers, Set.mem_ofPred_eq, o70Pair]

/-! ## The uniform attainment witness

`(a, b) = (r, r)` is admissible whenever `r ≤ min M (min N H)` and the dimensions
are positive, and it attains the printed value. That collapses the attainment
half of `IsO70FiberMinimumTable` from a search over the rank polytope to a single
closed-form identity, verified on all 1808 dimension/rank tuples through
dimension 8 by `scripts/reproduce_o70_table.py`. -/

public theorem admissible_self (M N H r : ℕ) (hM : 0 < M) (hN : 0 < N) (hH : 0 < H)
    (hr : r ≤ min M (min N H)) : AdmissibleRankData M N H r r r :=
  ⟨hM, hN, hH, hr, feasible_self M N H r hr⟩

/-- The residual shape at the uniform witness `(a,b) = (r,r)` is `(M-r, N-r, H-r)`. -/
public theorem o70Shape_self (M N H r : ℕ) : o70Shape M N H r r r = (M - r, N - r, H - r) := by
  unfold o70Shape
  have : H + r - r - r = H - r := by omega
  rw [this]


/-! ## P3, proved

Two obligations. **Attainment** is a closed-form identity: the value of the
candidate table at the uniform witness `(r, r)` equals the number printed by
`thm:aw`. Under the substitution `(p, n, h) = (M - r, N - r, H - r)` the four
Aoyagi–Watanabe cases become exactly the four regimes of the residual
minimisation — `M + r ≤ N + H` is `p ≤ n + h`, and the parity of `M + N + H + r`
is the parity of `p + n + h`.

**The lower bound** is the substantial one: a minimisation over the
two-dimensional rank polytope of a function that itself contains the inner
minimisation closed above. -/

/-- **Attainment.** The candidate table at the uniform witness `(a,b) = (r,r)`
equals the printed Aoyagi–Watanabe value. -/
public theorem o70Lambda_self (M N H r : ℕ) (hr : r ≤ min M (min N H)) :
    o70Lambda M N H r r r = awLambda M N H r := by
  simp only [le_min_iff] at hr
  obtain ⟨hrM, hrN, hrH⟩ := hr
  obtain ⟨p, rfl⟩ : ∃ p, M = p + r := ⟨M - r, by omega⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + r := ⟨N - r, by omega⟩
  obtain ⟨h, rfl⟩ : ∃ h, H = h + r := ⟨H - r, by omega⟩
  have hshape : o70Shape (p + r) (n + r) (h + r) r r r = (p, n, h) := by
    simp only [o70Shape, Prod.mk.injEq]
    omega
  simp only [o70Lambda, hshape]
  unfold awLambda
  by_cases hA : n + h < p
  · have hnb : ¬ AWBalanced (p + r) (n + r) (h + r) r := by unfold AWBalanced; omega
    rw [if_neg hnb, if_pos (show (n + r) + (h + r) < (p + r) + r by omega),
      residualMinCost_of_lt_left p n h hA]
    unfold o70Q
    push_cast
    ring
  · by_cases hB : p + h < n
    · have hnb : ¬ AWBalanced (p + r) (n + r) (h + r) r := by unfold AWBalanced; omega
      rw [if_neg hnb, if_neg (show ¬ (n + r) + (h + r) < (p + r) + r by omega),
        if_pos (show (p + r) + (h + r) < (n + r) + r by omega),
        residualMinCost_of_lt_mid p n h hB]
      unfold o70Q
      push_cast
      ring
    · by_cases hC : p + n < h
      · have hnb : ¬ AWBalanced (p + r) (n + r) (h + r) r := by unfold AWBalanced; omega
        rw [if_neg hnb, if_neg (show ¬ (n + r) + (h + r) < (p + r) + r by omega),
          if_neg (show ¬ (p + r) + (h + r) < (n + r) + r by omega),
          residualMinCost_of_lt_right p n h hC]
        unfold o70Q
        push_cast
        ring
      · have hbal : AWBalanced (p + r) (n + r) (h + r) r := by unfold AWBalanced; omega
        rw [if_pos hbal]
        have htval : residualArgmin p n h = (h + n - p) / 2 := by unfold residualArgmin; omega
        set t := (h + n - p) / 2 with htdef
        have hcost : residualMinCost p n h
            = (h : ℤ) * n + (t : ℤ) * ((p : ℤ) - h - n) + (t : ℤ) ^ 2 := by
          rw [residualMinCost_eq_argmin, htval]
          unfold residualCost
          ring
        by_cases hpar : ((p + r) + (n + r) + (h + r) + r) % 2 = 0
        · rw [if_pos hpar]
          have hp : (p : ℤ) = (h : ℤ) + (n : ℤ) - 2 * (t : ℤ) := by omega
          have key : (4 : ℤ) * (o70Q (p + r) (n + r) r r + residualMinCost p n h)
              = awBalancedNumerator (p + r) (n + r) (h + r) r := by
            rw [hcost]
            unfold o70Q awBalancedNumerator
            push_cast
            rw [hp]
            ring
          have hq := congrArg (fun z : ℤ => (z : ℚ)) key
          push_cast at hq ⊢
          linarith
        · rw [if_neg hpar]
          have hp : (p : ℤ) = (h : ℤ) + (n : ℤ) - 2 * (t : ℤ) - 1 := by omega
          have key : (4 : ℤ) * (o70Q (p + r) (n + r) r r + residualMinCost p n h)
              = awBalancedNumerator (p + r) (n + r) (h + r) r + 1 := by
            rw [hcost]
            unfold o70Q awBalancedNumerator
            push_cast
            rw [hp]
            ring
          have hq := congrArg (fun z : ℤ => (z : ℚ)) key
          push_cast at hq ⊢
          linarith

/-! ### The rank polytope: shifting a stratum back to the uniform witness

The lower bound is a discrete minimisation over `(a, b)`, but it collapses: with
`A = a - r` and `B = b - r`, the stratum shape is `(P - B, Q - A, Hh - A - B)`
over the witness shape `(P, Q, Hh) = (M - r, N - r, H - r)`, and expanding

    o70Q M N a b + residualCost (M-b) (N-a) (H+r-a-b) t

turns it into `o70Q M N r r + residualCost (M-r) (N-r) (H-r) (t + A)` — an
*identity*, with `B` cancelling entirely. So every index of the stratum's inner
minimisation is an index of the witness's, shifted by `A`; feasibility supplies
`t + A ≤ min (H - r) (N - r)`, so the shifted index is admissible there and the
witness minimum is a lower bound. No monotonicity argument is needed. -/

private theorem o70Q_add_residualMinCost_self_le (M N H r a b : ℕ)
    (hra : r ≤ a) (hrb : r ≤ b) (haN : a ≤ N) (hbM : b ≤ M) (hrH : r ≤ H)
    (hsum : a + b ≤ H + r) :
    o70Q M N r r + residualMinCost (M - r) (N - r) (H - r)
      ≤ o70Q M N a b + residualMinCost (M - b) (N - a) (H + r - a - b) := by
  set p := M - b with hpdef
  set n := N - a with hndef
  set h := H + r - a - b with hhdef
  set t := residualArgmin p n h with htdef
  have htle : t ≤ min h n := by rw [htdef, residualArgmin]; exact min_le_left _ _
  have hth : t ≤ h := le_trans htle (min_le_left _ _)
  have htn : t ≤ n := le_trans htle (min_le_right _ _)
  have hmem : t + (a - r) ∈ residualIndices (N - r) (H - r) := by
    simp only [residualIndices, mem_range, Nat.lt_succ_iff, le_min_iff]
    omega
  have hbase := residualMinCost_le (M - r) (N - r) (H - r) (t + (a - r)) hmem
  have hcost : residualMinCost p n h = residualCost p n h t := residualMinCost_eq_argmin p n h
  have hid : o70Q M N r r + residualCost (M - r) (N - r) (H - r) (t + (a - r))
      = o70Q M N a b + residualCost p n h t := by
    unfold o70Q residualCost
    have e1 : ((M - r : ℕ) : ℤ) = (M : ℤ) - r := by omega
    have e2 : ((N - r : ℕ) : ℤ) = (N : ℤ) - r := by omega
    have e3 : ((H - r : ℕ) : ℤ) = (H : ℤ) - r := by omega
    have e4 : ((t + (a - r) : ℕ) : ℤ) = (t : ℤ) + a - r := by omega
    have e5 : ((p : ℕ) : ℤ) = (M : ℤ) - b := by omega
    have e6 : ((n : ℕ) : ℤ) = (N : ℤ) - a := by omega
    have e7 : ((h : ℕ) : ℤ) = (H : ℤ) + r - a - b := by omega
    rw [e1, e2, e3, e4, e5, e6, e7]
    ring
  linarith

/-- **Lower bound.** No admissible stratum beats the printed value. -/
public theorem awLambda_le_o70Lambda (M N H r a b : ℕ)
    (hab : AdmissibleRankData M N H r a b) :
    awLambda M N H r ≤ o70Lambda M N H r a b := by
  obtain ⟨hM, hN, hH, hr, hrab, haHN, hbHM, hsum⟩ := hab
  rw [← o70Lambda_self M N H r hr]
  have hshape : o70Shape M N H r a b = (M - b, N - a, H + r - a - b) := rfl
  simp only [o70Lambda, hshape, o70Shape_self]
  simp only [le_min_iff] at hr hrab haHN hbHM
  have key := o70Q_add_residualMinCost_self_le M N H r a b hrab.1 hrab.2 haHN.2 hbHM.2
    hr.2.2 hsum
  have hcast : ((o70Q M N r r + residualMinCost (M - r) (N - r) (H - r) : ℤ) : ℚ)
      ≤ ((o70Q M N a b + residualMinCost (M - b) (N - a) (H + r - a - b) : ℤ) : ℚ) := by
    exact_mod_cast key
  linarith

/-- **P3's arithmetic half.** The printed Aoyagi–Watanabe value is the attained
minimum of the candidate table over the admissible rank strata. With print's own
gloss on `thm:aw` — "λ is the minimum of λ(w) over W₀" — this is what makes
`o70Minimizers` a set of *minimisers* rather than a set of strata hitting some
number. It carries no frontier hypothesis. -/
public theorem o70_fiber_minimum_correct : IsO70FiberMinimumTable o70Pair := by
  intro M N H r hM hN hH hr
  refine ⟨fun a b hab => awLambda_le_o70Lambda M N H r a b hab, ?_⟩
  exact ⟨r, r, admissible_self M N H r hM hN hH hr, o70Lambda_self M N H r hr⟩

/-! ## Anti-vacuity: the printed bounds and non-triviality

A compiling statement is a weak signal. These are the obligations that make the
table say something: it is bounded where print says it is bounded, its
multiplicity cannot exceed `2`, and it is not secretly constant.

The residual objective factors as `(h - t)(n - t) + t·p` on the index range,
which gives nonnegativity and the `t = 0` bound in one step. -/

/-- The residual objective, factored. Valid as a ring identity; the *sign*
information it carries needs `t ≤ min h n`. -/
public theorem residualCost_factored (p n h t : ℕ) :
    residualCost p n h t = ((h : ℤ) - t) * ((n : ℤ) - t) + (t : ℤ) * p := by
  unfold residualCost; ring

public theorem residualCost_nonneg (p n h t : ℕ) (ht : t ≤ min h n) :
    0 ≤ residualCost p n h t := by
  simp only [le_min_iff] at ht
  rw [residualCost_factored]
  have h1 : (0 : ℤ) ≤ (h : ℤ) - t := by omega
  have h2 : (0 : ℤ) ≤ (n : ℤ) - t := by omega
  have h3 : (0 : ℤ) ≤ (t : ℤ) * p := by positivity
  nlinarith [mul_nonneg h1 h2]

public theorem residualMinCost_nonneg (p n h : ℕ) : 0 ≤ residualMinCost p n h := by
  rw [residualMinCost_eq_argmin]
  exact residualCost_nonneg _ _ _ _ (by rw [residualArgmin]; exact min_le_left _ _)

/-- The `t = 0` endpoint bounds the minimum. -/
public theorem residualMinCost_le_hn (p n h : ℕ) : residualMinCost p n h ≤ (h : ℤ) * n := by
  have := residualMinCost_le p n h 0 (zero_mem_residualIndices n h)
  simpa [residualCost] using this

/-- **V6, multiplicity.** A minimiser satisfies `t = t₀` or `t + t₀ = h + n - p`,
so there are at most two. Print's own bound is `m ≤ H(N+M)`; this is sharp, and
implies it whenever the dimensions are positive. -/
public theorem residualMultiplicity_le_two (p n h : ℕ) : residualMultiplicity p n h ≤ 2 := by
  set s := residualArgmin p n h with hs
  have hsub :
      ((residualIndices n h).filter
        fun t => residualCost p n h t = residualMinCost p n h) ⊆ {s, h + n - p - s} := by
    intro t ht
    simp only [mem_filter] at ht
    obtain ⟨-, hval⟩ := ht
    have hcost : residualCost p n h t = residualCost p n h s := by
      rw [hval, hs, ← residualMinCost_eq_argmin]
    have hzero : ((t : ℤ) - s) * ((t : ℤ) + s + p - h - n) = 0 := by
      rw [← residualCost_sub]; omega
    rcases mul_eq_zero.mp hzero with h1 | h2
    · simp only [mem_insert, mem_singleton]
      exact Or.inl (by omega)
    · simp only [mem_insert, mem_singleton]
      exact Or.inr (by omega)
  calc residualMultiplicity p n h
      ≤ ({s, h + n - p - s} : Finset ℕ).card := card_le_card hsub
    _ ≤ 2 := by
        refine le_trans (card_insert_le _ _) ?_
        simp

public theorem o70Multiplicity_le_two (M N H r a b : ℕ) :
    o70Multiplicity M N H r a b ≤ 2 :=
  residualMultiplicity_le_two _ _ _

/-- `q = Ma + bN - ab` is nonnegative on any stratum whose `a` respects its shape
bound, since `q = Ma + b(N - a)`. -/
public theorem o70Q_nonneg (M N a b : ℕ) (ha : a ≤ N) : 0 ≤ o70Q M N a b := by
  unfold o70Q
  have : (0 : ℤ) ≤ (b : ℤ) * ((N : ℤ) - a) := by
    have : (0 : ℤ) ≤ (N : ℤ) - a := by omega
    positivity
  nlinarith [Nat.cast_nonneg (α := ℤ) M, Nat.cast_nonneg (α := ℤ) a]

/-- **V6, positivity.** The local coefficient is strictly positive on every
admissible stratum. Vanishing would mean the zero fiber had full dimension
locally, which `rem:conventions` excludes as the vacuous case `K ≡ 0`. -/
public theorem o70Lambda_pos (M N H r a b : ℕ) (hab : AdmissibleRankData M N H r a b) :
    0 < o70Lambda M N H r a b := by
  obtain ⟨hM, hN, hH, hr, hfeas⟩ := hab
  obtain ⟨hr', ha, hb, hsum⟩ := hfeas
  simp only [le_min_iff] at hr' ha hb hr
  have hq : 0 ≤ o70Q M N a b := o70Q_nonneg M N a b (by omega)
  have hmin : 0 ≤ residualMinCost (M - b) (N - a) (H + r - a - b) :=
    residualMinCost_nonneg _ _ _
  have hstrict : 0 < o70Q M N a b + residualMinCost (M - b) (N - a) (H + r - a - b) := by
    rcases Nat.eq_zero_or_pos a with rfl | hapos
    · rcases Nat.eq_zero_or_pos b with rfl | hbpos
      · -- a = b = 0 forces r = 0, and then the residual is the full shape
        have hr0 : r = 0 := by omega
        subst hr0
        have hcost : residualMinCost (M - 0) (N - 0) (H + 0 - 0 - 0) ≠ 0 := by
          rw [residualMinCost_eq_argmin, residualCost_factored]
          have hle : residualArgmin (M - 0) (N - 0) (H + 0 - 0 - 0) ≤ min (H + 0 - 0 - 0) (N - 0) := by
            rw [residualArgmin]; exact min_le_left _ _
          simp only [le_min_iff] at hle
          rcases Nat.eq_zero_or_pos (residualArgmin (M - 0) (N - 0) (H + 0 - 0 - 0)) with heq | hpos
          · rw [heq]; push_cast; simp; omega
          · have : (0 : ℤ) < residualArgmin (M - 0) (N - 0) (H + 0 - 0 - 0) := by exact_mod_cast hpos
            have h1 : (0 : ℤ) ≤ ((H + 0 - 0 - 0 : ℕ) : ℤ) - residualArgmin (M - 0) (N - 0) (H + 0 - 0 - 0) := by omega
            have h2 : (0 : ℤ) ≤ ((N - 0 : ℕ) : ℤ) - residualArgmin (M - 0) (N - 0) (H + 0 - 0 - 0) := by omega
            have h3 : (0 : ℤ) < (residualArgmin (M - 0) (N - 0) (H + 0 - 0 - 0) : ℤ) * ((M - 0 : ℕ) : ℤ) := by
              have : (0 : ℤ) < ((M - 0 : ℕ) : ℤ) := by omega
              positivity
            nlinarith [mul_nonneg h1 h2]
        have := hmin
        omega
      · have : 0 < o70Q M N 0 b := by unfold o70Q; push_cast; nlinarith
        omega
    · have : 0 < o70Q M N a b := by
        unfold o70Q
        have h1 : (0 : ℤ) < (M : ℤ) * a := by
          have : (0 : ℤ) < (a : ℤ) := by exact_mod_cast hapos
          have : (0 : ℤ) < (M : ℤ) := by exact_mod_cast hM
          positivity
        have h2 : (0 : ℤ) ≤ (b : ℤ) * ((N : ℤ) - a) := by
          have : (0 : ℤ) ≤ (N : ℤ) - a := by omega
          positivity
        nlinarith
      omega
  unfold o70Lambda
  simp only []
  rw [o70Shape]
  have hQ : (0 : ℚ) <
      ((o70Q M N a b + residualMinCost (M - b) (N - a) (H + r - a - b) : ℤ) : ℚ) := by
    exact_mod_cast hstrict
  linarith

/-- **V6, the printed upper bound.** `λ ≤ d/2` where `d = H(N + M)` is the
parameter dimension — `MAIS-A6.tex` line 182 fixes `d = H(N+M)`. -/
public theorem o70Lambda_le_dim_half (M N H r a b : ℕ)
    (hab : AdmissibleRankData M N H r a b) :
    o70Lambda M N H r a b ≤ (H * (N + M) : ℚ) / 2 := by
  obtain ⟨hM, hN, hH, hr, hfeas⟩ := hab
  obtain ⟨hr', ha, hb, hsum⟩ := hfeas
  simp only [le_min_iff] at hr' ha hb hr
  have hcheap : residualMinCost (M - b) (N - a) (H + r - a - b)
      ≤ ((H + r - a - b : ℕ) : ℤ) * ((N - a : ℕ) : ℤ) := residualMinCost_le_hn _ _ _
  have hbound : o70Q M N a b + ((H + r - a - b : ℕ) : ℤ) * ((N - a : ℕ) : ℤ)
      ≤ (H : ℤ) * ((N : ℤ) + M) := by
    unfold o70Q
    have e1 : ((H + r - a - b : ℕ) : ℤ) = (H : ℤ) + r - a - b := by omega
    have e2 : ((N - a : ℕ) : ℤ) = (N : ℤ) - a := by omega
    rw [e1, e2]
    nlinarith [Nat.cast_nonneg (α := ℤ) r, Nat.cast_nonneg (α := ℤ) a,
      Nat.cast_nonneg (α := ℤ) b, sub_nonneg.mpr (show (r : ℤ) ≤ a by omega),
      sub_nonneg.mpr (show (r : ℤ) ≤ b by omega),
      sub_nonneg.mpr (show (a : ℤ) ≤ N by omega),
      sub_nonneg.mpr (show (b : ℤ) ≤ M by omega),
      sub_nonneg.mpr (show (a : ℤ) + b ≤ (H : ℤ) + r by omega)]
  have hZ : o70Q M N a b + residualMinCost (M - b) (N - a) (H + r - a - b)
      ≤ (H : ℤ) * ((N : ℤ) + M) := by linarith
  unfold o70Lambda
  simp only []
  rw [o70Shape, div_le_div_iff_of_pos_right (by norm_num : (0:ℚ) < 2)]
  exact_mod_cast hZ

/-! ## V5 — the table is not constant

Print's own example already separates two strata at the same dimensions: at
`N = M = H = 2`, `r = 0` the origin gives `3/2` and `(I₂, 0)` gives `2`. -/

public theorem o70Lambda_not_constant :
    o70Lambda 2 2 2 0 0 0 ≠ o70Lambda 2 2 2 0 2 0 := by
  norm_num [o70Lambda, o70Q, o70Shape, residualMinCost_eq_argmin, residualArgmin,
    residualCost, residualIndices]

/-! ## P1, P2 and P3: the clauses about the actual local pair

Everything above grades the candidate *table* as arithmetic. Print's first two
clauses are about the local pair of the actual reduced-rank loss germ, and
stating them needs three things the arithmetic layer does not: print's loss
(`rrrLoss`), the transport of the matrix-pair parameter space to the Euclidean
coordinates on which the local-pair relations are stated (`matrixPairEquiv`,
proved measure-preserving so no Jacobian is silently discarded), and the source
relation itself (`HasExactLocalPair`).

**Nothing below is proved in this file.** These are the propositions that decide
whether a proposed table answers P1 and P2, and — for
`IsO70MinimizerCharacterization` — whether a proposed set of strata answers P3
against the germs rather than against the table. `O70Proof.lean` inhabits the
order-level one, `IsO70VolumeOrderTable o70Pair`, under the Wishart frontier
alone. It inhabits all three source-level ones too — that is Gate BExact — but
each of those additionally depends on `O70ExactLocalPairsExist`, which the atlas
does not have, so none of them is unconditional. -/

/-- Print's loss, transported to Euclidean coordinates.

`HasExactLocalPair` is stated on `EuclideanSpace ℝ (Fin d)` because the pinned
Mathlib puts no `MeasureSpace` on `Matrix`. The transport is a coordinate
reindexing and `measurePreserving_matrixPairEquiv` proves it carries Lebesgue
measure to Lebesgue measure, so the volume asymptotics `HasExactLocalPair` speaks
about are the ones on the matrix-pair space. -/
@[expose] public noncomputable def rrrLossCoords (M N H : ℕ)
    (C : Matrix (Fin M) (Fin N) ℝ) : EuclideanSpace ℝ (Fin (H * N + M * H)) → ℝ :=
  fun x => rrrLoss C ((matrixPairEquiv M N H).symm x).1 ((matrixPairEquiv M N H).symm x).2

/-- **P2 correctness.** The named table gives the source local pair at every
factorization of every truth matrix, at print's own quantifiers.

`rem:conventions` excludes the vacuous case `K ≡ 0`, which for reduced-rank
regression is exactly a vanishing ambient dimension; hence the positivity. -/
@[expose] public def IsO70RankTable (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ) : Prop :=
  ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
    ∀ (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
      (B : Matrix (Fin M) (Fin H) ℝ), B * A = C →
      HasExactLocalPair (rrrLossCoords M N H C) (matrixPairCoords A B)
        (((f M N H C.rank A.rank B.rank).1 : ℚ) : ℝ)
        (f M N H C.rank A.rank B.rank).2

/-- **P1.** The local pair depends only on `(rank A, rank B)` — derived from an
explicit correct table rather than used as its wrapper, because a theorem whose
type is only this existential does not expose which table was proved. -/
@[expose] public def O70DependsOnRanksOnly : Prop := ∃ f, IsO70RankTable f

/-- The intermediate two-sided interface, for the order-level milestone. -/
@[expose] public def IsO70VolumeOrderTable (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ) : Prop :=
  ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
    ∀ (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
      (B : Matrix (Fin M) (Fin H) ℝ), B * A = C →
      HasLocalVolumeOrder (rrrLossCoords M N H C) (matrixPairCoords A B)
        (((f M N H C.rank A.rank B.rank).1 : ℚ) : ℝ)
        (f M N H C.rank A.rank B.rank).2

/-- **`O70-ZETA-BRIDGE`.** Print's "Equivalently", at the germs it is used on.

`MAIS-A6.tex` `def:local` defines the local pair *primarily* by the zeta function
and only then calls the ball-volume form equivalent, citing `[lau2023]`. Every
O70 result in the atlas is about the volume form. This is that substitution,
stated and **not proved anywhere in the atlas**.

Two things about its shape, both deliberate.

*It is narrow on purpose.* The general proposition — that for every nonnegative
germ the volume pair is the zeta pair — is **false**, and `ZetaPair.lean` records
the counterexample: `HasExactLocalPair` constrains only the leading behaviour of
the sublevel volume, and a logarithmic correction to it turns the pole into a
branch point. Print's own setting carries the hypothesis that repairs this, a
nonnegative *real-analytic* `K`; the O70 germs are polynomial, so they satisfy it,
and stating the bridge here rather than in general keeps the frontier at
something that could be true.

*The degenerate branch is excluded by the positivity of the shape.* At `0 < M`,
`0 < N`, `0 < H` the loss vanishes on no neighbourhood
(`not_eventually_rrrLossCoords_eq_zero_of_pos`, unconditional), so the neutral
`(0, 1)` branch of `HasExactLocalPair` — on which the bridge would be false — is
unreachable, and no separate hypothesis is needed to say so. -/
@[expose] public def O70ZetaPoleBridge : Prop :=
  ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
    ∀ (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
      (B : Matrix (Fin M) (Fin H) ℝ), B * A = C →
      ∀ lam : ℝ, ∀ m : ℕ,
        HasExactLocalPair (rrrLossCoords M N H C) (matrixPairCoords A B) lam m →
          HasZetaPoleOrder (rrrLossCoords M N H C) (matrixPairCoords A B) lam m

/-- **The frozen surface of `O70-ZETA-BRIDGE`.** Every quantifier written out,
with `HasExactLocalPair` and `HasZetaPoleOrder` expanded rather than named, so the
degenerate branch, the countable exceptional set of radii, the analyticity clause
and the sign of the pole order are all on the lock rather than behind it. -/
public theorem o70ZetaPoleBridge_iff :
    O70ZetaPoleBridge ↔
      ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
        ∀ (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
          (B : Matrix (Fin M) (Fin H) ℝ), B * A = C →
          ∀ lam : ℝ, ∀ m : ℕ,
            (((∀ᶠ x in nhds (matrixPairCoords A B), rrrLossCoords M N H C x = 0)
                  ∧ lam = 0 ∧ m = 1) ∨
                (0 < lam ∧ 1 ≤ m ∧ ∃ δ₀ > 0, ∃ Exceptional : Set ℝ,
                  Exceptional.Countable ∧
                    ∀ δ ∈ Set.Ioo 0 δ₀, δ ∉ Exceptional → ∃ c > 0,
                      Filter.Tendsto
                        (fun ε ↦ sublevelVolume (rrrLossCoords M N H C)
                            (matrixPairCoords A B) δ ε /
                          (c * volumeScale lam m ε))
                        (nhdsWithin 0 (Set.Ioi 0)) (nhds 1))) →
              ∃ δ > 0, ∃ Z : ℂ → ℂ,
                (∀ x : ℝ, -lam < x →
                    Z (x : ℂ) =
                      (zetaIntegral (rrrLossCoords M N H C)
                        (matrixPairCoords A B) δ x : ℂ)) ∧
                  (∀ z : ℂ, -lam < z.re → AnalyticAt ℂ Z z) ∧
                    MeromorphicAt Z (-(lam : ℂ)) ∧
                      meromorphicOrderAt Z (-(lam : ℂ)) = ((-(m : ℤ) : ℤ) : WithTop ℤ) :=
  Iff.rfl

/-- **P3, the characterisation at the germs.** Print asks which strata carry the
*minimum* of the local coefficient over the zero fiber `W₀`.
`IsO70AWValueStratumTable` answers that against a table and a printed number;
this answers it against the germs themselves.

For a factorization `B * A = C` whose actual local pair is `(lam, m)`, the
stratum of `(A, B)` belongs to `S` exactly when `lam` is a lower bound for the
local coefficient at every other point of the zero fiber
`{(A', B') : B' * A' = C}`. A lower bound attained at the point itself is the
minimum, so this is print's clause with no table and no number inside it.

The table does not appear, and that is the point.
`IsO70AWValueStratumTable o70Pair o70Minimizers` holds by construction — it is a
definitional unfolding — so it carries no content until something ties the table
to the germs. This predicate is that something: every quantifier ranges over
actual matrices and actual sublevel volumes, and the proof on file
(`isO70MinimizerCharacterization_o70Minimizers`) consumes the order-level table
and the exact-pair frontier both. Whether some other route could inhabit it with
less is not claimed here, and has no witness either way.

Two limits, so the name is not read for more than it carries.

*This does not pin `S`.* The set is probed only at strata of the form
`⟨M, N, H, C.rank, A.rank, B.rank⟩` with positive dimensions, and those are
exactly the `AdmissibleRankData` strata; anything outside is invisible, so
`o70Minimizers` with an inadmissible stratum adjoined satisfies this too.
`IsO70AWValueStratumTable` is what quantifies over every `s : O70RankStratum`.
The two are complementary — one fixes the set, the other gives it meaning at the
germs — and neither replaces the other.

*`HasExactLocalPair` occurs here in hypothesis position only.* Were exact pairs to
exist nowhere, every `S` would satisfy this vacuously, the empty set included. The
content is on loan from `O70ExactLocalPairsExist`, and the anti-vacuity witness is
in `Examples/Conjectures/MAIS/O70Proof.lean`: under the frontier, `Set.univ` does
*not* satisfy it. -/
@[expose] public def IsO70MinimizerCharacterization (S : Set O70RankStratum) : Prop :=
  ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
    ∀ (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
      (B : Matrix (Fin M) (Fin H) ℝ), B * A = C →
      ∀ (lam : ℝ) (m : ℕ),
        HasExactLocalPair (rrrLossCoords M N H C) (matrixPairCoords A B) lam m →
        ((⟨M, N, H, C.rank, A.rank, B.rank⟩ : O70RankStratum) ∈ S ↔
          ∀ (A' : Matrix (Fin H) (Fin N) ℝ) (B' : Matrix (Fin M) (Fin H) ℝ),
            B' * A' = C →
            ∀ (lam' : ℝ) (m' : ℕ),
              HasExactLocalPair (rrrLossCoords M N H C) (matrixPairCoords A' B')
                lam' m' → lam ≤ lam')

/-- `O70-EXACT-LOCAL`. The **value-free** frontier hypothesis: exact local pairs
exist for these germs. It says only that *some* pair exists, never what it is —
assuming the value would assume the candidate's contribution. -/
@[expose] public def O70ExactLocalPairsExist : Prop :=
  ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
    ∀ (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
      (B : Matrix (Fin M) (Fin H) ℝ), B * A = C →
      ∃ lam m, HasExactLocalPair (rrrLossCoords M N H C) (matrixPairCoords A B) lam m

/-- **The frozen surface of `O70-EXACT-LOCAL`.** Every quantifier of the frontier
written out, with `HasExactLocalPair` expanded rather than named.

Freezing the alias alone would freeze nothing that matters: `HasExactLocalPair`
is itself a `def`, so a consumer of `O70ExactLocalPairsExist` sees only a
constant, and the degenerate branch, the countable exceptional set of radii and
the radius quantifier — the three places where this frontier could silently
weaken — would all sit *behind* the lock rather than on it. Written this way they
are on the surface, and `Iff.rfl` is what certifies that the surface and the
proposition the conditional theorems consume are the same proposition. -/
public theorem o70ExactLocalPairsExist_iff :
    O70ExactLocalPairsExist ↔
      ∀ M N H : ℕ, 0 < M → 0 < N → 0 < H →
        ∀ (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
          (B : Matrix (Fin M) (Fin H) ℝ), B * A = C →
          ∃ lam m,
            ((∀ᶠ x in nhds (matrixPairCoords A B), rrrLossCoords M N H C x = 0)
                ∧ lam = 0 ∧ m = 1) ∨
              (0 < lam ∧ 1 ≤ m ∧ ∃ δ₀ > 0, ∃ Exceptional : Set ℝ, Exceptional.Countable ∧
                ∀ δ ∈ Set.Ioo 0 δ₀, δ ∉ Exceptional → ∃ c > 0,
                  Filter.Tendsto (fun ε =>
                      sublevelVolume (rrrLossCoords M N H C) (matrixPairCoords A B) δ ε
                        / (c * volumeScale lam m ε))
                    (nhdsWithin 0 (Set.Ioi 0)) (nhds 1)) :=
  Iff.rfl

/-! ### Stress evidence for `O70-EXACT-LOCAL`

The frontier is an existential, so it could in principle be satisfied cheaply: every
`HasExactLocalPair` carries a neutral first branch `(lam, m) = (0, 1)` for a germ that vanishes
on a whole neighbourhood. If the O70 germs took that branch, `O70ExactLocalPairsExist` would be
true and worthless, and the conditional theorems would be carrying a hypothesis with no
content.

They do not. The one-dimensional slice below is the smallest member of the family, and there
the neutral branch is unavailable: the loss does not vanish on any neighbourhood of the origin
of the zero fibre, so every witness the frontier could supply lies in the second branch, with
`0 < lam` and `1 ≤ m`.

This is a consequence of the frontier, not an inhabitant of it, and it settles only this one
`(C, A, B)`. It is not evidence that `O70ExactLocalPairsExist` is true. -/

open Filter in
/-- **The neutral branch is unavailable anywhere in the family.** For every positive shape and
*every* `(C, A, B)` — no factorization hypothesis needed — the loss fails to vanish on any
neighbourhood of `matrixPairCoords A B`.

The obstruction is a single quadratic. Perturb along `(A + t·F, B + t·E)` with `E` and `F` the
all-ones matrices; then the `(0,0)` entry of `(B + tE)(A + tF) − C` is

    d + t·S + t²·H ,   d = (BA − C)₀₀,  S = Σₖ B₀ₖ + Σₖ Aₖ₀ ,

and the `t²` coefficient is `H` because the inner sum runs over `Fin H`. If the loss vanished
on a ball of radius `ε`, the entry would vanish at `0` and at `±ε/2`; the first gives `d = 0`
and the other two sum to `2d + H·ε²/2 = 0`, so `H·ε² = 0`, against `0 < H` and `0 < ε`. The
linear coefficient never has to be computed.

This is a consequence of the definitions, not of the frontier, and it is unconditional. -/
public theorem not_eventually_rrrLossCoords_eq_zero_of_pos {M N H : ℕ}
    (hM : 0 < M) (hN : 0 < N) (hH : 0 < H) (C : Matrix (Fin M) (Fin N) ℝ)
    (A : Matrix (Fin H) (Fin N) ℝ) (B : Matrix (Fin M) (Fin H) ℝ) :
    ¬ ∀ᶠ x in nhds (matrixPairCoords A B), rrrLossCoords M N H C x = 0 := by
  intro h
  set i : Fin M := ⟨0, hM⟩ with hi
  set j : Fin N := ⟨0, hN⟩ with hj
  set E : Matrix (Fin M) (Fin H) ℝ := Matrix.of fun _ _ => 1 with hE
  set F : Matrix (Fin H) (Fin N) ℝ := Matrix.of fun _ _ => 1 with hF
  have hcont : Continuous fun t : ℝ => matrixPairCoords (A + t • F) (B + t • E) := by
    unfold matrixPairCoords
    exact (matrixPairEquiv M N H).toLinearMap.continuous_of_finiteDimensional.comp (by fun_prop)
  have hzero : matrixPairCoords (A + (0:ℝ) • F) (B + (0:ℝ) • E) = matrixPairCoords A B := by
    simp
  have hcurve : ∀ᶠ t : ℝ in nhds 0,
      rrrLossCoords M N H C (matrixPairCoords (A + t • F) (B + t • E)) = 0 :=
    (hcont.tendsto' 0 _ hzero).eventually h
  rw [Metric.eventually_nhds_iff] at hcurve
  obtain ⟨ε, hε, hball⟩ := hcurve
  -- On the ball the factorization is exact, so the `(0,0)` entry of the residual vanishes.
  have key : ∀ t : ℝ, |t| < ε →
      ((B * A) i j - C i j) + t * ((∑ k, B i k) + (∑ k, A k j)) + t ^ 2 * (H : ℝ) = 0 := by
    intro t ht
    have hmul := hball (y := t) (by simpa [Real.dist_eq] using ht)
    rw [rrrLossCoords, matrixPairCoords, LinearEquiv.symm_apply_apply,
      rrrLoss_eq_zero_iff] at hmul
    have hentry := congrFun (congrFun hmul i) j
    simp only [Matrix.mul_apply, Matrix.add_apply, Matrix.smul_apply, hE, hF, Matrix.of_apply,
      smul_eq_mul, mul_one] at hentry
    have hexp : ∀ k : Fin H, (B i k + t) * (A k j + t)
        = B i k * A k j + t * B i k + t * A k j + t ^ 2 := by
      intro k; ring
    rw [Finset.sum_congr rfl fun k _ => hexp k] at hentry
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hentry
    have hBA : (B * A) i j = ∑ k, B i k * A k j := by simp [Matrix.mul_apply]
    rw [hBA]
    linarith [hentry]
  -- Three evaluations. The linear term cancels between `±ε/2`.
  have h0 := key 0 (by simpa using hε)
  have hp := key (ε / 2) (by rw [abs_of_pos (by linarith)]; linarith)
  have hm := key (-(ε / 2)) (by rw [abs_neg, abs_of_pos (by linarith)]; linarith)
  have hHpos : (0:ℝ) < (H : ℝ) := by exact_mod_cast hH
  simp only [zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow] at h0
  have hquad : (ε / 2) ^ 2 * (H : ℝ) = 0 := by nlinarith [hp, hm, h0]
  have hpos : 0 < (ε / 2) ^ 2 * (H : ℝ) :=
    mul_pos (pow_pos (by linarith) 2) hHpos
  linarith [hquad, hpos]

/-- **Every witness the frontier could supply is nondegenerate.** `O70ExactLocalPairsExist` is
an existential, and `HasExactLocalPair` offers a cheap way to satisfy it: the neutral branch
`(lam, m) = (0, 1)`, available to any germ vanishing on a neighbourhood. This rules that branch
out at *every* instance the frontier quantifies over, so the hypothesis cannot be satisfied
trivially anywhere in the family.

It does not show a pair exists. It shows that if one does, it is not the free one. -/
public theorem exactLocalPair_nondegenerate_of_frontier (hex : O70ExactLocalPairsExist)
    {M N H : ℕ} (hM : 0 < M) (hN : 0 < N) (hH : 0 < H)
    (C : Matrix (Fin M) (Fin N) ℝ) (A : Matrix (Fin H) (Fin N) ℝ)
    (B : Matrix (Fin M) (Fin H) ℝ) (hC : B * A = C) :
    ∃ lam : ℝ, ∃ m : ℕ, 0 < lam ∧ 1 ≤ m ∧
      HasExactLocalPair (rrrLossCoords M N H C) (matrixPairCoords A B) lam m := by
  obtain ⟨lam, m, hpair⟩ := hex M N H hM hN hH C A B hC
  rcases hpair with ⟨hvan, -, -⟩ | ⟨hlam, hm, hrest⟩
  · exact absurd hvan (not_eventually_rrrLossCoords_eq_zero_of_pos hM hN hH C A B)
  · exact ⟨lam, m, hlam, hm, Or.inr ⟨hlam, hm, hrest⟩⟩

/-- The order table upgrades to the source table under the value-free existence
hypothesis. This is the whole content of Gate BExact's transport step.

Both halves are now available: this implication, and — in `O70Proof.lean`, under
the Wishart frontier — an inhabitant of `IsO70VolumeOrderTable o70Pair`. What is
still missing is `O70ExactLocalPairsExist` itself. -/
public theorem isO70RankTable_of_volumeOrder (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ)
    (hex : O70ExactLocalPairsExist) (horder : IsO70VolumeOrderTable f) :
    IsO70RankTable f := by
  intro M N H hM hN hH C A B hC
  exact hasExactLocalPair_of_volumeOrder (hex M N H hM hN hH C A B hC)
    (horder M N H hM hN hH C A B hC)

/-- And an exact table is in particular an order table, by the bridge. -/
public theorem isO70VolumeOrderTable_of_rankTable (f : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℚ × ℕ)
    (h : IsO70RankTable f) : IsO70VolumeOrderTable f := fun M N H hM hN hH C A B hC =>
  exactLocalPair_imp_volumeOrder (h M N H hM hN hH C A B hC)

/-! ## C1: the chamber exponent is the residual cost

The candidate's Appendix A minimises an affine functional over the order simplex
`P = {1 ≥ β₁ ≥ … ≥ β_k ≥ 0}`, whose `k+1` vertices are the prefix indicators.
Lemma A.3 reduces that to a minimum over `{0, …, k}` of

    E_s = (p·k + s·(d − k − p) + s²) / 2,   k = min h n,  d = max h n,

and defines `E* = minₛ E_s`, `N* = #{s : E_s = E*}`. Proposition 8.14 records
that `E_{k−t} = c_t / 2`, where `c_t` is the residual objective already minimised
above.

**So this is the same optimisation, reindexed by `s = k − t`** — no polytope is
needed, and `residualMinCost_eq_argmin` and `residualMultiplicity_le_two` already
supply `E*` and `N* ∈ {1,2}`. Lemma A.3(iv) states exactly that dichotomy.

The identity below is checked on 18600 index pairs by
`scripts/reproduce_o70_table.py`. -/

/-- The numerator of the chamber exponent `E_s`, formed in `ℤ`: `d − k − p` is a
difference of unconstrained sign. -/
@[expose] public def chamberExponentNum (p k d s : ℕ) : ℤ :=
  (p : ℤ) * k + (s : ℤ) * ((d : ℤ) - k - p) + (s : ℤ) ^ 2

/-- **Proposition 8.14.** The chamber exponent at `s = k - t` is the residual
objective at `t`. Both sides are `ℤ`-valued; the printed `E_s` is this over `2`. -/
public theorem chamberExponentNum_eq_residualCost (p n h t : ℕ) (ht : t ≤ min h n) :
    chamberExponentNum p (min h n) (max h n) (min h n - t) = residualCost p n h t := by
  unfold chamberExponentNum residualCost
  simp only [le_min_iff] at ht
  rcases le_total h n with hle | hle
  · rw [min_eq_left hle, max_eq_right hle]
    have hk : ((h - t : ℕ) : ℤ) = (h : ℤ) - t := by omega
    rw [hk]; ring
  · rw [min_eq_right hle, max_eq_left hle]
    have hk : ((n - t : ℕ) : ℤ) = (n : ℤ) - t := by omega
    rw [hk]; ring

/-- Consequently the chamber minimum `E*` is the residual minimum, halved: the
atlas's `residualMinCost` already computes it. -/
public theorem residualMinCost_le_chamberExponentNum (p n h s : ℕ) (hs : s ≤ min h n) :
    residualMinCost p n h ≤ chamberExponentNum p (min h n) (max h n) s := by
  have hts : min h n - s ≤ min h n := Nat.sub_le _ _
  have := chamberExponentNum_eq_residualCost p n h (min h n - s) hts
  have hss : min h n - (min h n - s) = s := by omega
  rw [hss] at this
  rw [this]
  exact residualMinCost_le p n h _ (by
    simp only [residualIndices, mem_range, Nat.lt_succ_iff]; exact hts)

end AISafetyAtlas.Conjectures.MAIS
