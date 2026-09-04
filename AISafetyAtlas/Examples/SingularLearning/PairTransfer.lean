module

public import AISafetyAtlas.SingularLearning.PairTransfer
public import AISafetyAtlas.Examples.SingularLearning.LocalPair

/-!
# Worked models for the local-pair transfer calculus

`AISafetyAtlas/SingularLearning/PairTransfer.lean` supplies the two transfer
combinators the candidate's Section 6 needs: comparability of germs (Lemma 6.2)
and free coordinates (Lemma 6.4(ii)). Both are implications between
`HasLocalVolumeOrder` claims, so on their own they say nothing about any
particular germ. This module applies them to the one germ whose pair is known
outright, `x₀²` on `EuclideanSpace ℝ (Fin 1)` with pair `(1/2, 1)`
(`hasLocalVolumeOrder_sq`), and so exhibits the first pairs in this development
obtained by *computation* rather than by a direct volume integral.

## What the two transfers buy here

* `hasLocalVolumeOrder_two_mul_sq` — the germ `2x₀²` has pair `(1/2, 1)`. Its
  sublevel volume is never computed: `2x₀²` is comparable to `x₀²` with
  `c₁ = c₂ = 2`, and Lemma 6.2 moves the pair across. This is the smallest case
  of print's point that *the multiplicity, not only the exponent, survives
  comparability* — an additive shift of `log(1/ε)` is a multiplicative
  perturbation by a constant, so the power `m − 1` is untouched.
* `hasLocalVolumeOrder_sq_freeCoord` — the germ on `EuclideanSpace ℝ (Fin (1+1))`
  that reads only the first split coordinate has pair `(1/2, 1)`. The ambient
  dimension is `2` and the pair is the one-dimensional pair: the free coordinate
  contributes volume but no scaling in `ε`.
* `hasLocalVolumeOrder_two_mul_sq_freeCoord` — the two combinators compose, on
  the germ that is `2x₀²` in the first split coordinate and ignores the second.

## Why these are stated at a definite pair rather than as implications

The transfer theorems are implications, and an implication is inhabited by
anything that refutes its antecedent. Each statement below therefore names the
resulting `lam` and `m` explicitly, and `eq_half_one_of_hasLocalVolumeOrder_sq`
is *not* used to obtain them — they come from the transfer, and uniqueness
(`volumeOrder_unique`) is then applied to confirm that no other pair is possible
for the transferred germ either.

## The `u`-block

`hasExactLocalPair_quadraticGerm` computes the pair of the `q`-dimensional
quadratic germ `‖x‖²` outright: `(q/2, 1)`. This is print's "each transverse
direction contributes `1/2`", and it is the reason `λ = ½(q + min{…})` carries
the `q/2`. It is the second germ in this development whose pair is known, and
unlike `x₀²` it is known in every dimension, so the supply for the transfer
combinators is no longer a single one-dimensional example.

## What is still not here

The combinator Stage 4 actually needs next is the **product rule**: the pair of
`(x, y) ↦ f x + g y` in disjoint variables, which is what would combine the
`u`-block's `(q/2, 1)` with the residual block's pair into the pair of
`‖u‖² + ‖Y₀S_Z‖²_F`. That is a genuine theorem — Fubini on the sublevel volumes,
then a convolution of the two scales — and it is not formalized. Neither is
print's regular-quadratic-factor combinator, nor Lemma 6.1, which is what would
supply a pair to transfer for a germ not computed by hand. All are recorded gaps
rather than papered over.
-/

namespace AISafetyAtlas.Examples.SingularLearning

open AISafetyAtlas.SingularLearning

/-! ## Comparability: the pair of `2x₀²` -/

/-- `2x₀²` is comparable to `x₀²` with both constants equal to `2` — everywhere,
hence in particular on a neighbourhood of the origin. -/
public theorem comparable_two_mul_sq :
    ∀ᶠ x in nhds (0 : EuclideanSpace ℝ (Fin 1)),
      2 * (x 0 ^ 2) ≤ 2 * x 0 ^ 2 ∧ 2 * x 0 ^ 2 ≤ 2 * (x 0 ^ 2) :=
  Filter.Eventually.of_forall fun _ => ⟨le_refl _, le_refl _⟩

/-- **The first pair obtained by transfer.** `2x₀²` has local pair `(1/2, 1)`, by
Lemma 6.2 from `hasLocalVolumeOrder_sq`. No sublevel volume of `2x₀²` is
computed anywhere. -/
public theorem hasLocalVolumeOrder_two_mul_sq :
    HasLocalVolumeOrder (fun x : EuclideanSpace ℝ (Fin 1) => 2 * x 0 ^ 2) 0 (1/2) 1 :=
  hasLocalVolumeOrder_of_comparable (c₁ := 2) (c₂ := 2) two_pos (le_refl 2)
    comparable_two_mul_sq hasLocalVolumeOrder_sq

/-- The transferred pair is the only one: `(1/2, 1)` is forced for `2x₀²` too. -/
public theorem eq_half_one_of_hasLocalVolumeOrder_two_mul_sq {lam : ℝ} {m : ℕ}
    (h : HasLocalVolumeOrder (fun x : EuclideanSpace ℝ (Fin 1) => 2 * x 0 ^ 2) 0 lam m) :
    lam = 1/2 ∧ m = 1 :=
  volumeOrder_unique h hasLocalVolumeOrder_two_mul_sq

/-! ## Free coordinates: the pair does not move when the dimension grows

The germ is built as `f ∘ (first split coordinate)`, which is the shape in which
`hasLocalVolumeOrder_freeCoords` states its hypothesis; the hypothesis then holds
by `Equiv.symm_apply_apply` and nothing else. -/

/-- The germ on `EuclideanSpace ℝ (Fin (1+1))` that reads only the first split
coordinate of `euclideanProdEquiv 1 1`. -/
@[expose] public noncomputable def freeCoordGerm
    (f : EuclideanSpace ℝ (Fin 1) → ℝ) (z : EuclideanSpace ℝ (Fin (1 + 1))) : ℝ :=
  f ((euclideanProdEquiv 1 1).symm z).1

public theorem freeCoordGerm_apply (f : EuclideanSpace ℝ (Fin 1) → ℝ)
    (x : EuclideanSpace ℝ (Fin 1)) (y : EuclideanSpace ℝ (Fin 1)) :
    freeCoordGerm f (euclideanProdEquiv 1 1 (x, y)) = f x := by
  rw [freeCoordGerm, (euclideanProdEquiv 1 1).symm_apply_apply]

/-- **Lemma 6.4(ii) applied.** The germ on `EuclideanSpace ℝ (Fin (1+1))` given by
`x₀²` in the first split coordinate has pair `(1/2, 1)` — the pair of the
one-dimensional germ, at a base point with an arbitrary free component. -/
public theorem hasLocalVolumeOrder_sq_freeCoord (v : EuclideanSpace ℝ (Fin 1)) :
    HasLocalVolumeOrder (freeCoordGerm (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2))
      (euclideanProdEquiv 1 1 (0, v)) (1/2) 1 :=
  hasLocalVolumeOrder_freeCoords
    (freeCoordGerm_apply (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2)) hasLocalVolumeOrder_sq

/-- **The two combinators compose.** `2x₀²` in the first split coordinate, ignoring
the second, still has pair `(1/2, 1)`: comparability first, then a free
coordinate. -/
public theorem hasLocalVolumeOrder_two_mul_sq_freeCoord (v : EuclideanSpace ℝ (Fin 1)) :
    HasLocalVolumeOrder (freeCoordGerm (fun x : EuclideanSpace ℝ (Fin 1) => 2 * x 0 ^ 2))
      (euclideanProdEquiv 1 1 (0, v)) (1/2) 1 :=
  hasLocalVolumeOrder_freeCoords
    (freeCoordGerm_apply (fun x : EuclideanSpace ℝ (Fin 1) => 2 * x 0 ^ 2))
    hasLocalVolumeOrder_two_mul_sq

/-! ## The supporting infrastructure, exercised

The three infrastructure lemmas `PairTransfer` proves on the way are used above
only inside the two transfers. They are pinned here at concrete values so that a
change to any of them breaks loudly rather than silently weakening a transfer. -/

/-- Sublevel volumes are monotone under a pointwise implication inside the ball:
`x₀² ≤ ε` implies `x₀² ≤ 2ε`, so the first sublevel volume is at most the
second. -/
public theorem sublevelVolume_sq_le_two_mul (δ ε : ℝ) (hε : 0 ≤ ε) :
    sublevelVolume (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2) 0 δ ε
      ≤ sublevelVolume (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2) 0 δ (2 * ε) :=
  sublevelVolume_le_sublevelVolume fun _ _ h => by linarith

/-- Dividing by a positive constant is a self-map of the punctured right filter at
`0`, which is what lets a bound stated at `ε` be read off at `ε / c`. -/
public theorem tendsto_div_two_nhdsGT :
    Filter.Tendsto (fun ε : ℝ => ε / 2) (nhdsWithin 0 (Set.Ioi 0))
      (nhdsWithin 0 (Set.Ioi 0)) :=
  tendsto_div_const_nhdsGT two_pos

/-- The scale rescaling is inhabited at `c = 2`: `volumeScale lam m (ε/2)` is
two-sided comparable to `volumeScale lam m ε`, with the multiplicity preserved. -/
public theorem exists_volumeScale_div_two_bounds (lam : ℝ) (m : ℕ) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ b ∧ ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a * volumeScale lam m ε ≤ volumeScale lam m (ε / 2) ∧
        volumeScale lam m (ε / 2) ≤ b * volumeScale lam m ε :=
  exists_volumeScale_div_bounds lam m two_pos

/-! ## The `u`-block: the quadratic germ in every dimension -/

/-- **The pair of `‖u‖²` on `ℝ^q` is `(q/2, 1)`.** Print's transverse directions contribute
`q/2` to `λ` and nothing to the multiplicity. -/
public theorem hasExactLocalPair_quadraticGerm_example {q : ℕ} (hq : 0 < q) :
    HasExactLocalPair (quadraticGerm q) 0 ((q : ℝ) / 2) 1 :=
  hasExactLocalPair_quadraticGerm hq

/-- At `q = 1` this is the germ `x₀²` of `LocalPair.lean`'s worked model, on the nose. -/
public theorem quadraticGerm_one :
    quadraticGerm 1 = fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2 := by
  funext x
  rw [quadraticGerm, Fin.sum_univ_one]

/-- And the two computations agree: `(1/2, 1)` either way. The `q`-dimensional computation is
therefore a genuine generalization of the one-dimensional one, not a parallel claim. -/
public theorem quadraticGerm_one_pair_eq :
    HasExactLocalPair (fun x : EuclideanSpace ℝ (Fin 1) => x 0 ^ 2) 0 (1 / 2) 1 := by
  have h := hasExactLocalPair_quadraticGerm (q := 1) one_pos
  rw [quadraticGerm_one] at h
  simpa using h

/-- The dimension really does move the exponent: `q = 4` gives `λ = 2`. -/
public theorem hasExactLocalPair_quadraticGerm_four :
    HasExactLocalPair (quadraticGerm 4) 0 2 1 := by
  have h := hasExactLocalPair_quadraticGerm (q := 4) (by norm_num)
  norm_num at h
  exact h

/-- The pair is forced, so the value `(q/2, 1)` is not merely one admissible reading. -/
public theorem eq_of_quadraticGerm {q : ℕ} (hq : 0 < q) {lam : ℝ} {m : ℕ}
    (h : HasLocalVolumeOrder (quadraticGerm q) 0 lam m) : lam = (q : ℝ) / 2 ∧ m = 1 :=
  eq_of_hasLocalVolumeOrder_quadraticGerm hq h

/-- **The `u`-block composes with the transfer combinators.** `2‖u‖²` — the shape Step 7's
constants produce — has the same pair, by comparability. -/
public theorem hasLocalVolumeOrder_two_mul_quadraticGerm {q : ℕ} (hq : 0 < q) :
    HasLocalVolumeOrder (fun x : EuclideanSpace ℝ (Fin q) => 2 * quadraticGerm q x) 0
      ((q : ℝ) / 2) 1 :=
  hasLocalVolumeOrder_of_comparable (c₁ := 2) (c₂ := 2) two_pos (le_refl 2)
    (Filter.Eventually.of_forall fun _ => ⟨le_refl _, le_refl _⟩)
    (hasLocalVolumeOrder_quadraticGerm hq)


/-! ## The product rule, and the check that it is consistent

`hasLocalVolumeOrder_add` is the combinator Stage 4 needs, in the case one factor has
multiplicity `1`. The examples below pin it and then check it against a computation it does not
use: the pair of `‖·‖²` on `ℝ^{n+k}`, obtained directly. -/

/-- **The product rule.** `f + g` in disjoint variables, with `f` of multiplicity `1`. -/
public theorem hasLocalVolumeOrder_add_example {n k : ℕ}
    {f : EuclideanSpace ℝ (Fin n) → ℝ} {g : EuclideanSpace ℝ (Fin k) → ℝ}
    {F : EuclideanSpace ℝ (Fin (n + k)) → ℝ} {w : EuclideanSpace ℝ (Fin n)}
    {v : EuclideanSpace ℝ (Fin k)} {lam₁ lam₂ : ℝ} {m : ℕ}
    (hF : ∀ x y, F (euclideanProdEquiv n k (x, y)) = f x + g y)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ y, 0 ≤ g y) (h1 : 0 < lam₁) (h2 : 0 < lam₂)
    (hf : HasLocalVolumeOrder f w lam₁ 1) (hg : HasLocalVolumeOrder g v lam₂ m) :
    HasLocalVolumeOrder F (euclideanProdEquiv n k (w, v)) (lam₁ + lam₂) m :=
  hasLocalVolumeOrder_add hF hf0 hg0 h1 h2 hf hg

/-- **The consistency check.** Feeding the product rule the two factors `‖x‖²` on `ℝ^1` and
`‖y‖²` on `ℝ^1` returns `(1/2 + 1/2, 1)` for the germ on `ℝ^2`; the direct computation returns
`(2/2, 1)`. Uniqueness of the pair forces the two exponents equal — the equality below is
*derived*, not asserted — so the multiplicity rule `m = m₂` is not off by one. -/
public theorem product_rule_consistent_one_one :
    ((1 : ℕ) : ℝ) / 2 + ((1 : ℕ) : ℝ) / 2 = ((1 + 1 : ℕ) : ℝ) / 2 :=
  (eq_of_hasLocalVolumeOrder_quadraticGerm (q := 1 + 1) (by norm_num)
    (hasLocalVolumeOrder_quadraticGerm_add (n := 1) (k := 1) one_pos one_pos)).1

/-- The same at `n = 3`, `k = 5`: the product rule's `3/2 + 5/2` is the direct `8/2`. -/
public theorem product_rule_consistent_three_five :
    ((3 : ℕ) : ℝ) / 2 + ((5 : ℕ) : ℝ) / 2 = ((3 + 5 : ℕ) : ℝ) / 2 :=
  (eq_of_hasLocalVolumeOrder_quadraticGerm (q := 3 + 5) (by norm_num)
    (hasLocalVolumeOrder_quadraticGerm_add (n := 3) (k := 5) (by norm_num) (by norm_num))).1

/-- The multiplicity is carried through unchanged: the product of two multiplicity-one germs
still has multiplicity one, and the statement says so rather than deriving it. -/
public theorem hasLocalVolumeOrder_quadraticGerm_add_one_one :
    HasLocalVolumeOrder (quadraticGerm (1 + 1)) 0
      (((1 : ℕ) : ℝ) / 2 + ((1 : ℕ) : ℝ) / 2) 1 :=
  hasLocalVolumeOrder_quadraticGerm_add one_pos one_pos

/-- `‖·‖²` splits over a coordinate decomposition — the identity that makes the two routes
comparable at all. -/
public theorem quadraticGerm_add_example (n k : ℕ) (x : EuclideanSpace ℝ (Fin n))
    (y : EuclideanSpace ℝ (Fin k)) :
    quadraticGerm (n + k) (euclideanProdEquiv n k (x, y))
      = quadraticGerm n x + quadraticGerm k y :=
  quadraticGerm_add n k x y

/-- The scale factorization that makes the multiplicity-one case sharp:
`ε^{λ₁} · ε^{λ₂}(log(1/ε))^{m−1} = ε^{λ₁+λ₂}(log(1/ε))^{m−1}`, with no cross term. -/
public theorem volumeScale_mul_one_example {lam₁ lam₂ : ℝ} {m : ℕ} {ε : ℝ} (hε : 0 < ε) :
    volumeScale lam₁ 1 ε * volumeScale lam₂ m ε = volumeScale (lam₁ + lam₂) m ε :=
  volumeScale_mul_one hε


end AISafetyAtlas.Examples.SingularLearning
