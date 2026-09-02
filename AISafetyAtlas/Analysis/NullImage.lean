module

public import Mathlib.MeasureTheory.Measure.Hausdorff
public import Mathlib.Topology.MetricSpace.HausdorffDimension
public import Mathlib.Analysis.Calculus.ContDiff.RCLike
public import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# A lower-dimensional parametrized family is null

If a set in `ℝ^q` is covered by the image of a locally Lipschitz map from `ℝ^p`
with `p < q`, it is Lebesgue null. This is the measure-theoretic content of *"a
family with fewer parameters than the ambient dimension misses almost every
point"*, and it is the substitute this repository uses for the semialgebraic
dimension theory such arguments are usually phrased in.

## Primary surface

| declaration | says |
|---|---|
| `volume_image_eq_zero_of_card_lt` | the image of any set under a locally Lipschitz `ι → ℝ` to `κ → ℝ` is null when `card ι < card κ` |
| `volume_image_eq_zero_of_contDiffOn` | the same for a `C¹` map on an open chart, which is what a rational parametrization gives |
| `volume_image_eq_zero_of_contDiff` | the global `C¹` form |
| `volume_range_eq_zero_of_contDiff` | the range form |
| `volume_setOf_exists_forall_dotProduct_eq_zero` | `L` hyperplanes whose normals share a parameter with fewer than `L` coordinates meet almost no point |
| `measurableSet_exists_of_isClosed` | a projection along a σ-compact factor of a closed set is measurable |

The parameter is restricted by a predicate `P`, because the applications only
know the normals are nonzero at the parameters they actually produce.

## Why this and not semialgebraic dimension

Mathlib carries no semialgebraic sets, no o-minimality and no Tarski–Seidenberg,
so the usual route — *the bad set is a projection of a semialgebraic set of
dimension `< q`, hence null* — is unavailable. Mathlib does carry Hausdorff
dimension, including `dimH_image_le_of_locally_lipschitzOn` and
`measure_zero_of_dimH_lt`, and for an argument that can exhibit an explicit
Euclidean parametrization of the bad set that is enough: the fibre-dimension and
product-dimension facts of semialgebraic geometry are only needed to *find* the
parameter count, and a proof that writes the parametrization down does not need
them.

`MeasureTheory.hausdorffMeasure_pi_real` identifies `hausdorffMeasure q` with
`volume` on `κ → ℝ`, which is what turns the dimension bound into a statement
about Lebesgue measure.

## Provenance

Written to be lifted upstream: the declarations are named as Mathlib would name
them and the proofs use no atlas definitions.
-/

namespace AISafetyAtlas.Analysis

open MeasureTheory
open scoped ENNReal NNReal

/-- **A locally Lipschitz image of a lower-dimensional space is null.**

Stated at arbitrary finite index types rather than at `Fin p`, because the
parametrizations that use it are indexed by products and sums and reindexing them
by hand is pure friction.

No hypothesis is placed on `s`: it need not be measurable, and the conclusion is
about the image rather than about `s`. -/
public theorem volume_image_eq_zero_of_card_lt {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) → (κ → ℝ)} (s : Set (ι → ℝ))
    (hf : ∀ x ∈ s, ∃ C, ∃ t ∈ nhdsWithin x s, LipschitzOnWith C f t)
    (hlt : Fintype.card ι < Fintype.card κ) :
    volume (f '' s) = 0 := by
  have hdim : dimH (f '' s) ≤ (Fintype.card ι : ℝ≥0∞) := by
    refine le_trans (dimH_image_le_of_locally_lipschitzOn hf) ?_
    calc dimH s ≤ dimH (Set.univ : Set (ι → ℝ)) := dimH_mono (Set.subset_univ _)
      _ = (Fintype.card ι : ℝ≥0∞) := Real.dimH_univ_pi ι
  refine measure_zero_of_dimH_lt (d := (Fintype.card κ : NNReal)) ?_ ?_
  · rw [show (MeasureTheory.Measure.hausdorffMeasure
        (((Fintype.card κ : NNReal)) : ℝ)) = (volume : Measure (κ → ℝ)) by
      simp]
  · exact lt_of_le_of_lt hdim (by exact_mod_cast hlt)

/-- **The `C¹` form**, which is what a polynomial or rational parametrization
supplies. `s` is typically the open chart on which a denominator does not
vanish, so `ContDiffOn` is the hypothesis that fits. -/
public theorem volume_image_eq_zero_of_contDiffOn {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) → (κ → ℝ)} {s : Set (ι → ℝ)} (hs : IsOpen s) (hf : ContDiffOn ℝ 1 f s)
    (hlt : Fintype.card ι < Fintype.card κ) :
    volume (f '' s) = 0 := by
  refine volume_image_eq_zero_of_card_lt s (fun x hx => ?_) hlt
  obtain ⟨K, t, ht, hlip⟩ :=
    ((hf.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith)
  exact ⟨K, t, nhdsWithin_le_nhds ht, hlip⟩

/-- The global `C¹` form. -/
public theorem volume_image_eq_zero_of_contDiff {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) → (κ → ℝ)} (hf : ContDiff ℝ 1 f)
    (hlt : Fintype.card ι < Fintype.card κ) (s : Set (ι → ℝ)) :
    volume (f '' s) = 0 :=
  volume_image_eq_zero_of_card_lt s
    (fun x _ => by
      obtain ⟨K, t, ht, hlip⟩ := hf.contDiffAt.exists_lipschitzOnWith
      exact ⟨K, t, nhdsWithin_le_nhds ht, hlip⟩)
    hlt

/-- The range form: a locally Lipschitz map from a strictly lower-dimensional
space misses almost every point. -/
public theorem volume_range_eq_zero_of_contDiff {ι κ : Type*} [Fintype ι] [Fintype κ]
    {f : (ι → ℝ) → (κ → ℝ)} (hf : ContDiff ℝ 1 f)
    (hlt : Fintype.card ι < Fintype.card κ) : volume (Set.range f) = 0 := by
  rw [← Set.image_univ]
  exact volume_image_eq_zero_of_contDiff hf hlt _

/-! ## A parametrized family of hyperplane products

The shape a genericity argument actually meets: `L` linear conditions, one per
factor, whose normals all depend on a *single* parameter with fewer than `L`
coordinates. Each condition costs its factor one dimension, so the total is
`card α + L·k'` against an ambient `L·(k'+1)`, and the family misses almost every
point exactly when `card α < L`.

The charts are indexed by which coordinate each equation is solved for, and
`Fin.insertNth` does the solving, so no subtype bookkeeping appears. -/

section HyperplaneFamily

variable {α : Type*} [Fintype α] {L k' : ℕ}

/-- Solve the `ℓ`-th equation for the `i ℓ`-th coordinate. -/
private noncomputable def chartMap (w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ))
    (i : Fin L → Fin (k' + 1)) (p : (α ⊕ (Fin L × Fin k')) → ℝ) :
    Fin L × Fin (k' + 1) → ℝ :=
  fun q =>
    (Fin.insertNth (i q.1)
        (-(∑ j : Fin k', p (.inr (q.1, j)) *
            w (fun x => p (.inl x)) (q.1, (i q.1).succAbove j))
          / w (fun x => p (.inl x)) (q.1, i q.1))
        (fun j => p (.inr (q.1, j))) : Fin (k' + 1) → ℝ) q.2

/-- The chart on which that division is legitimate. -/
private def chartSet (w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ)) (i : Fin L → Fin (k' + 1)) :
    Set ((α ⊕ (Fin L × Fin k')) → ℝ) :=
  {p | ∀ ℓ, w (fun x => p (.inl x)) (ℓ, i ℓ) ≠ 0}

private theorem contDiff_restrict :
    ContDiff ℝ 1 fun p : (α ⊕ (Fin L × Fin k')) → ℝ => fun x : α => p (.inl x) :=
  contDiff_pi.2 fun x => contDiff_apply ℝ ℝ (Sum.inl x)

private theorem contDiff_wcomp {w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ)} (hw : ContDiff ℝ 1 w)
    (q : Fin L × Fin (k' + 1)) :
    ContDiff ℝ 1 fun p : (α ⊕ (Fin L × Fin k')) → ℝ => w (fun x => p (.inl x)) q :=
  (contDiff_apply ℝ ℝ q).comp (hw.comp contDiff_restrict)

private theorem isOpen_chartSet {w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ)}
    (hw : ContDiff ℝ 1 w) (i : Fin L → Fin (k' + 1)) : IsOpen (chartSet w i) := by
  rw [show chartSet w i
      = ⋂ ℓ : Fin L, {p : (α ⊕ (Fin L × Fin k')) → ℝ |
          w (fun x => p (.inl x)) (ℓ, i ℓ) ≠ 0} from by ext p; simp [chartSet]]
  exact isOpen_iInter_of_finite fun ℓ =>
    isOpen_ne_fun ((contDiff_wcomp hw (ℓ, i ℓ)).continuous) continuous_const

private theorem contDiffOn_chartMap {w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ)}
    (hw : ContDiff ℝ 1 w) (i : Fin L → Fin (k' + 1)) :
    ContDiffOn ℝ 1 (chartMap w i) (chartSet w i) := by
  refine contDiffOn_pi.2 fun q => ?_
  by_cases hq : q.2 = i q.1
  · have hrw : ∀ p : (α ⊕ (Fin L × Fin k')) → ℝ, chartMap w i p q
        = -(∑ j : Fin k', p (.inr (q.1, j)) *
              w (fun x => p (.inl x)) (q.1, (i q.1).succAbove j))
            / w (fun x => p (.inl x)) (q.1, i q.1) := by
      intro p
      rw [chartMap, hq, Fin.insertNth_apply_same]
    simp only [hrw]
    refine ContDiffOn.div ?_ ?_ ?_
    · refine ContDiffOn.neg (ContDiff.contDiffOn (ContDiff.sum fun j _ =>
        (contDiff_apply ℝ ℝ (Sum.inr (q.1, j))).mul
          (contDiff_wcomp hw (q.1, (i q.1).succAbove j))))
    · exact (contDiff_wcomp hw (q.1, i q.1)).contDiffOn
    · exact fun p hp => hp q.1
  · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hq
    have hrw : ∀ p : (α ⊕ (Fin L × Fin k')) → ℝ,
        chartMap w i p q = p (.inr (q.1, j)) := by
      intro p
      rw [chartMap, ← hj, Fin.insertNth_apply_succAbove]
    simp only [hrw]
    exact (contDiff_apply ℝ ℝ (Sum.inr (q.1, j))).contDiffOn

/-- **A hyperplane family with fewer parameters than factors is null.**

`w a ℓ` is the normal of the `ℓ`-th hyperplane at parameter `a`; the hypothesis
`hne` says each is a genuine hyperplane. The conclusion is that almost no point
lies on all `L` of them simultaneously, for any value of the parameter. -/
public theorem volume_setOf_exists_forall_dotProduct_eq_zero
    {w : (α → ℝ) → (Fin L × Fin (k' + 1) → ℝ)} (hw : ContDiff ℝ 1 w)
    {P : (α → ℝ) → Prop}
    (hne : ∀ a : α → ℝ, P a → ∀ ℓ : Fin L, ∃ j, w a (ℓ, j) ≠ 0)
    (hcard : Fintype.card α + L * k' < L * (k' + 1)) :
    volume {c : Fin L × Fin (k' + 1) → ℝ |
      ∃ a, P a ∧ ∀ ℓ, ∑ j, c (ℓ, j) * w a (ℓ, j) = 0} = 0 := by
  classical
  have hsub : {c : Fin L × Fin (k' + 1) → ℝ | ∃ a, P a ∧ ∀ ℓ, ∑ j, c (ℓ, j) * w a (ℓ, j) = 0}
      ⊆ ⋃ i : Fin L → Fin (k' + 1), chartMap w i '' chartSet w i := by
    rintro c ⟨a, hPa, hc⟩
    choose i hi using fun ℓ => hne a hPa ℓ
    refine Set.mem_iUnion.2 ⟨i, ⟨Sum.elim a fun q => c (q.1, (i q.1).succAbove q.2), ?_, ?_⟩⟩
    · intro ℓ; simpa using hi ℓ
    · funext q
      have hrestrict : (fun x : α => (Sum.elim a
          (fun q : Fin L × Fin k' => c (q.1, (i q.1).succAbove q.2))) (.inl x)) = a := rfl
      rw [chartMap, hrestrict]
      have hkey := hc q.1
      rw [Fin.sum_univ_succAbove (fun j => c (q.1, j) * w a (q.1, j)) (i q.1)] at hkey
      refine congrFun (?_ : (Fin.insertNth (i q.1)
        (-(∑ j : Fin k', c (q.1, (i q.1).succAbove j) * w a (q.1, (i q.1).succAbove j))
          / w a (q.1, i q.1))
        (fun j => c (q.1, (i q.1).succAbove j)) : Fin (k' + 1) → ℝ)
          = fun j => c (q.1, j)) q.2
      funext r
      have hv : w a (q.1, i q.1) ≠ 0 := hi q.1
      refine Fin.succAboveCases (i q.1) ?_ ?_ r
      · rw [Fin.insertNth_apply_same]
        field_simp
        linarith
      · intro j
        rw [Fin.insertNth_apply_succAbove]
  refine measure_mono_null hsub ?_
  refine measure_iUnion_null fun i => ?_
  refine volume_image_eq_zero_of_contDiffOn (isOpen_chartSet hw i) (contDiffOn_chartMap hw i) ?_
  simpa using hcard

end HyperplaneFamily

/-! ## Projections that stay measurable

A genericity argument states its bad set as *"there exists a rival such that…"*,
and a Tonelli step then needs that set to be measurable. The projection of a
Borel set is analytic, and Mathlib has analytic sets but **not** their universal
measurability — only Suslin's analytic-plus-coanalytic criterion. What it does
have is that projection along a compact factor is closed, and every finite-
dimensional real space is σ-compact, which is enough. -/

/-- **A projection along a σ-compact factor of a closed set is measurable.**

Exhaust the projected-away factor by compacts; projection along each is a closed
map, so the projection is a countable union of closed sets. -/
public theorem measurableSet_exists_of_isClosed {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [MeasurableSpace X] [OpensMeasurableSpace X] [SigmaCompactSpace Y]
    {F : Set (Y × X)} (hF : IsClosed F) : MeasurableSet {x | ∃ y, (y, x) ∈ F} := by
  have hcov : {x | ∃ y, (y, x) ∈ F}
      = ⋃ i : ℕ, SetRel.image F (compactCovering Y i) := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, SetRel.image]
    constructor
    · rintro ⟨y, hy⟩
      obtain ⟨i, hi⟩ := exists_mem_compactCovering y
      exact ⟨i, y, hi, hy⟩
    · rintro ⟨i, y, _, hy⟩
      exact ⟨y, hy⟩
  rw [hcov]
  exact MeasurableSet.iUnion fun i =>
    (hF.relImage_of_isCompact (isCompact_compactCovering Y i)).measurableSet

end AISafetyAtlas.Analysis
