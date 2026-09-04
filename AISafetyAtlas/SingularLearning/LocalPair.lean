module

public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
public import Mathlib.Topology.Algebra.Module.Cardinality
public import Mathlib.Topology.Order.OrderClosed
public import Mathlib.Order.Filter.Basic

/-!
# The local pair: volume normalization

`MAIS-A6.tex` `def:local` defines the **local learning coefficient** `λ(w*)` and
**local multiplicity** `m(w*)` at a zero `w*` of a nonnegative real-analytic `K`
as the threshold and pole order of the zeta function
`ζ_{w*}(z) = ∫_{B_ε(w*)} K(w)^z dw`, and then says:

> "**They do not depend on ε**, nor on inserting any smooth positive density into
> the integral. Equivalently, `λ(w*)` is **the exponent** in \eqref{eq:volume}
> with the volume computed over `B_ε(w*)`."

`eq:volume` is `vol(ε) = c ε^λ (log(1/ε))^{m-1} (1 + o(1))` as `ε ↓ 0`.

**This module declares no theorem about any particular model.** It fixes the two
relations that a local-pair claim can be made in, and the bridge between them.

## Which normalization, and why

Print's *primary* definition is the zeta pair. This module takes the **volume**
form as primary, which print licenses in its own words ("Equivalently"). The
reasons, in order of weight: print says it; the volume form needs no prior, no
meromorphic continuation and no resolution of singularities; and it is the form
in which the reduced-rank results are proved unconditionally.

That substitution is the one deviation from print's primary definition, and it is
recorded rather than hidden. Nothing here proves the equivalence.

## The radius quantifier

Two relations, deliberately not identified:

* `HasExactLocalPair` — the **source** specification. Exact `c(1 + o(1))`
  asymptotics at all but countably many sufficiently small radii. This is print's
  content: `def:local` asserts that *the pair* is radius-independent and says
  nothing whatever about the constant `c`, so demanding exactness at *every*
  radius would be a claim on an axis print does not have.
* `HasLocalVolumeOrder` — a weaker, operational two-sided order, at every
  sufficiently small radius.

An earlier draft quantified the radius as a bare `∃ δ > 0`. That does not
determine the pair: for `K(x) = x²(x-1)⁴` at `w = 0`, the ball of radius `1/2`
sees only the zero at `0` and gives `(1/2, 1)`, while the ball of radius `2` also
sees the zero at `1` and gives `(1/4, 1)`. Both are witnesses for a bare `∃ δ`,
so uniqueness — the property every "the table is `f`" claim leans on — would be
unprovable.

Both relations carry a neutral `(0, 1)` branch for a germ that vanishes on a
whole neighbourhood, so that residual subproblems with a degenerate shape stay
inside the relation.
-/

namespace AISafetyAtlas.SingularLearning

open MeasureTheory Filter Topology

variable {n : ℕ}

/-- `V(δ, ε)`: the volume of the `ε`-sublevel set of `K` inside the ball of
radius `δ` about `w`. -/
@[expose] public noncomputable def sublevelVolume (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (δ ε : ℝ) : ℝ :=
  (volume {x ∈ Metric.ball w δ | K x ≤ ε}).toReal

/-- The asymptotic scale `ε ^ lam * log(1/ε) ^ (m - 1)` of `eq:volume`. -/
@[expose] public noncomputable def volumeScale (lam : ℝ) (m : ℕ) (ε : ℝ) : ℝ :=
  ε ^ lam * Real.log (1 / ε) ^ (m - 1)

/-- **The source specification.** `eq:volume` holds exactly, with some positive
constant, at all but countably many sufficiently small radii.

The `(0, 1)` first branch is the neutral convention for a germ vanishing on a
neighbourhood of `w`. -/
@[expose] public noncomputable def HasExactLocalPair (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (m : ℕ) : Prop :=
  ((∀ᶠ x in nhds w, K x = 0) ∧ lam = 0 ∧ m = 1) ∨
    (0 < lam ∧ 1 ≤ m ∧ ∃ δ₀ > 0, ∃ Exceptional : Set ℝ, Exceptional.Countable ∧
      ∀ δ ∈ Set.Ioo 0 δ₀, δ ∉ Exceptional → ∃ c > 0,
        Tendsto (fun ε ↦ sublevelVolume K w δ ε / (c * volumeScale lam m ε))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 1))

/-- **The operational interface.** Two-sided order bounds at every sufficiently
small radius. Weaker than `HasExactLocalPair`; not silently identified with it. -/
@[expose] public noncomputable def HasLocalVolumeOrder (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (lam : ℝ) (m : ℕ) : Prop :=
  ((∀ᶠ x in nhds w, K x = 0) ∧ lam = 0 ∧ m = 1) ∨
    (0 < lam ∧ 1 ≤ m ∧ ∃ δ₀ > 0, ∀ δ ∈ Set.Ioo 0 δ₀, ∃ cLower cUpper : ℝ,
      0 < cLower ∧ cLower ≤ cUpper ∧
      ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
        cLower * volumeScale lam m ε ≤ sublevelVolume K w δ ε ∧
          sublevelVolume K w δ ε ≤ cUpper * volumeScale lam m ε)

/-! ## The bridge

Exact asymptotics off a countable set imply two-sided order bounds at **every**
sufficiently small radius — including the exceptional ones. A radius in the
exceptional set has no exact premise of its own, but it is squeezed between two
radii that do: the complement of a countable subset of `ℝ` is dense, so good
radii exist on both sides, and `δ ↦ sublevelVolume K w δ ε` is monotone because a
larger ball contains a larger sublevel set.

This makes `exactLocalPair_unique` and the cross-interface comparison corollaries
of `volumeOrder_unique` rather than three separate radius-picking arguments.
-/

/-- The sublevel set sits inside a ball, so its volume is finite. No measurability
hypothesis is needed: `measure_mono` is monotone on all sets. -/
public theorem sublevelVolume_ne_top (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (w : EuclideanSpace ℝ (Fin n)) (δ ε : ℝ) :
    volume {x ∈ Metric.ball w δ | K x ≤ ε} ≠ ⊤ := by
  have hsub : {x ∈ Metric.ball w δ | K x ≤ ε} ⊆ Metric.ball w δ := fun _ hx => hx.1
  have hle := measure_mono (μ := (volume : Measure (EuclideanSpace ℝ (Fin n)))) hsub
  exact ne_top_of_le_ne_top (measure_ball_lt_top (x := w) (r := δ)).ne hle

/-- The sublevel set grows with the radius. -/
public theorem sublevelVolume_mono (K : EuclideanSpace ℝ (Fin n) → ℝ)
    (w : EuclideanSpace ℝ (Fin n)) {δ₁ δ₂ ε : ℝ} (h : δ₁ ≤ δ₂) :
    sublevelVolume K w δ₁ ε ≤ sublevelVolume K w δ₂ ε := by
  refine ENNReal.toReal_mono (sublevelVolume_ne_top K w δ₂ ε) (measure_mono ?_)
  rintro x ⟨hx, hKx⟩
  exact ⟨Metric.ball_subset_ball h hx, hKx⟩

/-- Between any two reals there is one outside a given countable set. -/
public theorem exists_notMem_of_countable {E : Set ℝ} (hE : E.Countable) {x y : ℝ} (h : x < y) :
    ∃ z ∈ Set.Ioo x y, z ∉ E := by
  obtain ⟨z, hz, hzmem⟩ := (hE.dense_compl ℝ).exists_between h
  exact ⟨z, hzmem, hz⟩

/-- **The bridge.** The source specification implies the operational two-sided order.

This is what makes the two-sided interface a strict consequence of print's own
specification rather than an independent postulate: with it, `exactLocalPair_unique`
and the cross-interface comparison (one relation exact, the other only two-sided)
are corollaries of a single uniqueness proof for `HasLocalVolumeOrder`, instead of
three separate arguments each having to pick its own good radii.

The point of the statement is that the conclusion holds *at every* radius below
`δ₀`, including the exceptional ones, where `HasExactLocalPair` supplies no
premise at all. A radius `δ` in the exceptional set is squeezed between two
non-exceptional radii `δ₁ < δ < δ₂`, which exist because a countable subset of
`ℝ` has dense complement, and `δ ↦ sublevelVolume K w δ ε` is monotone; the exact
asymptotics at `δ₁` and `δ₂` then bound `sublevelVolume K w δ ε` from below and
above. The two constants obtained this way are unrelated, so the upper constant
is taken to be `max` of the two rather than the second one: no comparison between
`c₁` and `c₂` is available, and none is needed. -/
public theorem exactLocalPair_imp_volumeOrder {K : EuclideanSpace ℝ (Fin n) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {lam : ℝ} {m : ℕ}
    (h : HasExactLocalPair K w lam m) : HasLocalVolumeOrder K w lam m := by
  rcases h with hzero | ⟨hlam, hm, δ₀, hδ₀, E, hE, hex⟩
  · exact Or.inl hzero
  refine Or.inr ⟨hlam, hm, δ₀, hδ₀, fun δ hδ => ?_⟩
  obtain ⟨δ₁, hδ₁, hδ₁E⟩ := exists_notMem_of_countable hE hδ.1
  obtain ⟨δ₂, hδ₂, hδ₂E⟩ := exists_notMem_of_countable hE hδ.2
  obtain ⟨c₁, hc₁, ht₁⟩ := hex δ₁ ⟨hδ₁.1, hδ₁.2.trans hδ.2⟩ hδ₁E
  obtain ⟨c₂, hc₂, ht₂⟩ := hex δ₂ ⟨hδ.1.trans hδ₂.1, hδ₂.2⟩ hδ₂E
  have hpos : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < volumeScale lam m ε := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with ε hε
    have h1 : 0 < ε ^ lam := Real.rpow_pos_of_pos hε.1 lam
    have h2 : (0 : ℝ) < Real.log (1 / ε) := Real.log_pos (by rw [lt_div_iff₀ hε.1]; linarith [hε.2])
    exact mul_pos h1 (pow_pos h2 _)
  refine ⟨c₁ / 2, max (c₁ / 2) (2 * c₂), by positivity, le_max_left _ _, ?_⟩
  filter_upwards [hpos, ht₁.eventually_const_lt (by norm_num : (1 : ℝ) / 2 < 1),
    ht₂.eventually_lt_const (by norm_num : (1 : ℝ) < 2)] with ε hs h1 h2
  rw [lt_div_iff₀ (mul_pos hc₁ hs)] at h1
  rw [div_lt_iff₀ (mul_pos hc₂ hs)] at h2
  have hmono₁ : sublevelVolume K w δ₁ ε ≤ sublevelVolume K w δ ε :=
    sublevelVolume_mono K w hδ₁.2.le
  have hmono₂ : sublevelVolume K w δ ε ≤ sublevelVolume K w δ₂ ε :=
    sublevelVolume_mono K w hδ₂.1.le
  have hmax : 2 * c₂ * volumeScale lam m ε ≤ max (c₁ / 2) (2 * c₂) * volumeScale lam m ε :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) hs.le
  exact ⟨by linarith, by linarith⟩

/-! ## Uniqueness of the operational pair -/

/-- The asymptotic scale vanishes at `0⁺` whenever the exponent is positive: the
power beats any fixed power of the logarithm. -/
public theorem tendsto_volumeScale (lam : ℝ) (hlam : 0 < lam) (m : ℕ) :
    Tendsto (volumeScale lam m) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hlit := isLittleO_abs_log_rpow_rpow_nhdsGT_zero (s := -lam) (((m - 1 : ℕ) : ℝ))
    (neg_lt_zero.2 hlam)
  refine hlit.tendsto_div_nhds_zero.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := hx.1
  have hlogneg : Real.log x < 0 := Real.log_neg hx.1 hx.2
  rw [Real.rpow_neg hx0.le, div_eq_mul_inv, inv_inv, abs_of_neg hlogneg, Real.rpow_natCast,
    volumeScale, one_div, Real.log_inv]
  ring

/-- `log(1/ε) → ∞` as `ε ↓ 0`. -/
public theorem tendsto_log_one_div :
    Tendsto (fun ε : ℝ => Real.log (1 / ε)) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
  (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero).congr fun x => by
    rw [one_div, Real.log_inv]; rfl

/-- A strictly larger exponent cannot dominate a smaller one from below: no
positive constants make `a · ε^lam log(1/ε)^(m-1) ≤ A · ε^lam' log(1/ε)^(m'-1)`
hold near `0⁺` when `lam < lam'`. -/
public theorem not_eventually_volumeScale_le {lam lam' : ℝ} (h : lam < lam') {m m' : ℕ}
    {a A : ℝ} (ha : 0 < a) (hA : 0 < A) :
    ¬ ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a * volumeScale lam m ε ≤ A * volumeScale lam' m' ε := by
  intro hcon
  have hsmall := (tendsto_volumeScale _ (sub_pos.2 h) m').eventually_lt_const
    (show (0 : ℝ) < a / A by positivity)
  have hLge : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0), (1 : ℝ) ≤ Real.log (1 / ε) :=
    tendsto_log_one_div.eventually_ge_atTop 1
  obtain ⟨ε, hle, hs, hLε, hε⟩ :=
    (hcon.and (hsmall.and (hLge.and (Ioo_mem_nhdsGT (zero_lt_one' ℝ))))).exists
  simp only [volumeScale] at hle hs
  rw [lt_div_iff₀ hA] at hs
  have hεlam : (0 : ℝ) < ε ^ lam := Real.rpow_pos_of_pos hε.1 lam
  have hpow : (1 : ℝ) ≤ Real.log (1 / ε) ^ (m - 1) := one_le_pow₀ hLε
  have hsplit : ε ^ lam' = ε ^ lam * ε ^ (lam' - lam) := by
    rw [← Real.rpow_add hε.1]; ring_nf
  rw [hsplit] at hle
  have h1 := mul_le_mul_of_nonneg_left hpow (mul_nonneg ha.le hεlam.le)
  have h2 := mul_lt_mul_of_pos_left hs hεlam
  linarith

/-- With equal exponents, a strictly larger multiplicity cannot be dominated: the
extra power of `log(1/ε)` is unbounded. -/
public theorem not_eventually_volumeScale_le_of_mult_lt {lam : ℝ} {m m' : ℕ} (hm' : 1 ≤ m')
    (h : m' < m) {a A : ℝ} (ha : 0 < a) :
    ¬ ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a * volumeScale lam m ε ≤ A * volumeScale lam m' ε := by
  intro hcon
  have hk : m - 1 = (m' - 1) + (m - m') := by omega
  have hLtop : Tendsto (fun ε : ℝ => Real.log (1 / ε) ^ (m - m'))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop :=
    (tendsto_pow_atTop (by omega)).comp tendsto_log_one_div
  have hbig := hLtop.eventually_gt_atTop (A / a)
  obtain ⟨ε, hle, hb, hε⟩ := (hcon.and (hbig.and (Ioo_mem_nhdsGT (zero_lt_one' ℝ)))).exists
  simp only [volumeScale] at hle
  have hεlam : (0 : ℝ) < ε ^ lam := Real.rpow_pos_of_pos hε.1 lam
  have hLpos : (0 : ℝ) < Real.log (1 / ε) :=
    Real.log_pos (by rw [lt_div_iff₀ hε.1]; linarith [hε.2])
  have hP : (0 : ℝ) < ε ^ lam * Real.log (1 / ε) ^ (m' - 1) :=
    mul_pos hεlam (pow_pos hLpos _)
  have hb' : A < a * Real.log (1 / ε) ^ (m - m') := by
    rw [div_lt_iff₀ ha] at hb; linarith
  rw [hk, pow_add] at hle
  nlinarith [mul_pos hP (sub_pos.2 hb')]

/-- A germ vanishing on a neighbourhood of `w` admits only the neutral pair: the
sublevel volume is then the full volume of the ball, a positive constant in `ε`,
which no vanishing scale can dominate. -/
public theorem eq_zero_pair_of_eventually_zero {K : EuclideanSpace ℝ (Fin n) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {lam : ℝ} {m : ℕ} (hK : ∀ᶠ x in nhds w, K x = 0)
    (h : HasLocalVolumeOrder K w lam m) : lam = 0 ∧ m = 1 := by
  rcases h with ⟨-, hl, hm⟩ | ⟨hlam, -, δ₀, hδ₀, hb⟩
  · exact ⟨hl, hm⟩
  exfalso
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.1 hK
  have hδpos : 0 < min δ₀ r / 2 := by have := lt_min hδ₀ hr; linarith
  have hδlt : min δ₀ r / 2 < δ₀ := by have := min_le_left δ₀ r; linarith
  have hδr : min δ₀ r / 2 < r := by have := min_le_right δ₀ r; linarith
  obtain ⟨a, A, ha, haA, hbd⟩ := hb _ ⟨hδpos, hδlt⟩
  have hV0 : 0 < (volume (Metric.ball w (min δ₀ r / 2))).toReal := by
    rw [ENNReal.toReal_pos_iff]
    exact ⟨Metric.measure_ball_pos volume w hδpos, measure_ball_lt_top⟩
  have hsmall : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      A * volumeScale lam m ε < (volume (Metric.ball w (min δ₀ r / 2))).toReal := by
    refine Filter.Tendsto.eventually_lt_const hV0 ?_
    simpa using (tendsto_volumeScale lam hlam m).const_mul A
  obtain ⟨ε, hbdε, hsε, hεpos⟩ := (hbd.and (hsmall.and self_mem_nhdsWithin)).exists
  have hset : {x ∈ Metric.ball w (min δ₀ r / 2) | K x ≤ ε} = Metric.ball w (min δ₀ r / 2) := by
    ext x
    refine ⟨fun hx => hx.1, fun hx => ⟨hx, ?_⟩⟩
    rw [hball (lt_trans (Metric.mem_ball.1 hx) hδr)]
    exact le_of_lt hεpos
  rw [sublevelVolume, hset] at hbdε
  linarith [hbdε.2]

/-- **Uniqueness of the operational pair.** Two-sided bounds at a common radius
pin down both the exponent and the multiplicity: a mismatch in either would make
the ratio of the two scales unbounded on one side. -/
public theorem volumeOrder_unique {K : EuclideanSpace ℝ (Fin n) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {lam lam' : ℝ} {m m' : ℕ}
    (h : HasLocalVolumeOrder K w lam m) (h' : HasLocalVolumeOrder K w lam' m') :
    lam = lam' ∧ m = m' := by
  rcases h with ⟨hK, hl, hm⟩ | hmain
  · obtain ⟨hl', hm'⟩ := eq_zero_pair_of_eventually_zero hK h'
    exact ⟨hl.trans hl'.symm, hm.trans hm'.symm⟩
  rcases h' with ⟨hK', hl', hm'⟩ | hmain'
  · obtain ⟨hl, hm⟩ := eq_zero_pair_of_eventually_zero hK' (Or.inr hmain)
    exact ⟨hl.trans hl'.symm, hm.trans hm'.symm⟩
  obtain ⟨hlam, hm, δ₀, hδ₀, hb⟩ := hmain
  obtain ⟨hlam', hm', δ₀', hδ₀', hb'⟩ := hmain'
  have hδpos : 0 < min δ₀ δ₀' / 2 := by have := lt_min hδ₀ hδ₀'; linarith
  have hδ1 : min δ₀ δ₀' / 2 < δ₀ := by have := min_le_left δ₀ δ₀'; linarith
  have hδ2 : min δ₀ δ₀' / 2 < δ₀' := by have := min_le_right δ₀ δ₀'; linarith
  obtain ⟨a, A, ha, haA, hbd⟩ := hb _ ⟨hδpos, hδ1⟩
  obtain ⟨a', A', ha', ha'A', hbd'⟩ := hb' _ ⟨hδpos, hδ2⟩
  have hApos : 0 < A := ha.trans_le haA
  have hApos' : 0 < A' := ha'.trans_le ha'A'
  have hcross : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a * volumeScale lam m ε ≤ A' * volumeScale lam' m' ε := by
    filter_upwards [hbd, hbd'] with ε h1 h2 using le_trans h1.1 h2.2
  have hcross' : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
      a' * volumeScale lam' m' ε ≤ A * volumeScale lam m ε := by
    filter_upwards [hbd, hbd'] with ε h1 h2 using le_trans h2.1 h1.2
  have hlameq : lam = lam' := by
    rcases lt_trichotomy lam lam' with hlt | heq | hgt
    · exact absurd hcross (not_eventually_volumeScale_le hlt ha hApos')
    · exact heq
    · exact absurd hcross' (not_eventually_volumeScale_le hgt ha' hApos)
  subst hlameq
  refine ⟨rfl, ?_⟩
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd hcross' (not_eventually_volumeScale_le_of_mult_lt hm hlt ha')
  · exact heq
  · exact absurd hcross (not_eventually_volumeScale_le_of_mult_lt hm' hgt ha)

/-! ## The two corollaries the bridge buys

An earlier plan for this module listed three separate uniqueness obligations —
one for the exact relation, one for the two-sided one, and one comparing them —
each to be proved by its own radius-picking argument. Only `volumeOrder_unique`
needs a proof. The other two follow from it through the bridge, because the
bridge is valid *at* the exceptional radii. -/

/-- The source specification determines the pair. -/
public theorem exactLocalPair_unique {K : EuclideanSpace ℝ (Fin n) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {lam lam' : ℝ} {m m' : ℕ}
    (h : HasExactLocalPair K w lam m) (h' : HasExactLocalPair K w lam' m') :
    lam = lam' ∧ m = m' :=
  volumeOrder_unique (exactLocalPair_imp_volumeOrder h) (exactLocalPair_imp_volumeOrder h')

/-- Cross-interface comparison: a two-sided order computation transports to the
source specification whenever an exact pair is known to exist. This is the step
that upgrades an order-level result to a source-level one. -/
public theorem exactLocalPair_eq_volumeOrder {K : EuclideanSpace ℝ (Fin n) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {lam lam' : ℝ} {m m' : ℕ}
    (h : HasExactLocalPair K w lam m) (h' : HasLocalVolumeOrder K w lam' m') :
    lam = lam' ∧ m = m' :=
  volumeOrder_unique (exactLocalPair_imp_volumeOrder h) h'

/-- The transport in the form the O70 assembly needs: if *some* exact pair exists
for a germ whose two-sided order is known, the exact pair is the computed one. -/
public theorem hasExactLocalPair_of_volumeOrder {K : EuclideanSpace ℝ (Fin n) → ℝ}
    {w : EuclideanSpace ℝ (Fin n)} {lam : ℝ} {m : ℕ}
    (hex : ∃ lam' m', HasExactLocalPair K w lam' m')
    (h : HasLocalVolumeOrder K w lam m) :
    HasExactLocalPair K w lam m := by
  obtain ⟨lam', m', hex'⟩ := hex
  obtain ⟨hlam, hm⟩ := exactLocalPair_eq_volumeOrder hex' h
  exact hlam ▸ hm ▸ hex'

end AISafetyAtlas.SingularLearning
