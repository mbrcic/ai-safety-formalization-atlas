module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Regressional Goodhart: selection on the proxy inflates the proxy-goal gap

## What is stated

A goal and a noise term are independent real random variables, the proxy is
their sum, and the regulator selects the states where the proxy clears a
threshold. The theorems say that selection on the proxy raises the expected
proxy-goal gap:

* `gap_selection_ge` -- the selected gap mass is at least the unconditional mean
  gap times the selected mass. Written in product form rather than as a
  conditional expectation, so that nothing divides by the selected mass and the
  statement survives a selection event of measure zero.
* `gap_selection_gt` -- the same, strictly, given a set of goal values of
  positive mass at which the threshold cuts the noise law properly.
* `gap_selection_gaussianReal_gt` -- the printed Gaussian case, where that cut
  hypothesis discharges itself.

The carrier is a product of two copies of the line, with `goal`, `gap` and
`proxy` as coordinate functions and `proxy = goal + gap`, so the two-variable
structure and the independence of the two variables are built into the space
rather than asserted about it. `selected` is the selection event, and
`measureReal_selected` and `integral_gap_selected` reduce both of its
one-dimensional summaries to integrals over the goal law alone.

## Provenance

The model is Manheim and Garrabrant, *Categorizing Variants of Goodhart's Law*,
arXiv:1803.04585v4, section 1, equation (1), the whole of Regressional Goodhart:
the proxy is the goal plus normal noise, and "when M is large, you can expect G
to be predictably smaller than M". The paper is pinned at
`manheim-garrabrant-arxiv-v4-2018-categorizing-variants-of-goodhart-s-law.pdf`
sha256 7691af8a05ed88262d0eaebebf082f5d028979445a0cd586acc29c861a7a012a.

**This does not reproduce a printed theorem.** The paper numbers no theorem, no
proposition, no lemma and no corollary — confirmed on 2026-09-11 by scanning the
whole document, not its front matter. What it numbers is nine equations, each a
generative *Simple Model* with its consequences asserted in running prose;
section 1 is two such sentences attached to one model. What is proved here is
this atlas's sharpening of that prose into a checkable statement, routed as
atlas-original work citing the paper for the model. See
`docs/provenance/by037-by038-goodhart-campbell-plan.md`, decision D3.

**Amended 2026-09-11.** This paragraph opened *"this is not coverage of that
paper"*, which now reads as a contradiction: the paper **is** graded, in section
17 of `docs/provenance/source-coverage-audit.md`, and
`LAND-GOODHART-SELECTION-001` hosts this module. Nothing has changed about the
routing — the sentence was conflating two things. The audit grades *what print
claims and what the atlas holds against it*, and print's claims here are prose;
the routing decision is that an unnumbered gloss is not booked as coverage of a
printed **result**. Both hold at once, and section 17 says so in its own header.
That section also records what this module does **not** prove: print's second
consequence, that the goal itself is higher under selection, which is a distinct
claim from the gap growing and is a short step from `tail_integral_ge`.

## Scope against print

* **Wider on the noise.** Print writes normal noise; the theorems need only
  independence and integrability. The Gaussian case is recovered by
  `gap_selection_gaussianReal_gt` through `ProbabilityTheory.gaussianReal`.
* **The Gaussian case owes one hypothesis print leaves implicit.** At variance
  zero `gaussianReal` is a Dirac measure, there is no noise, and no inequality
  is strict; the corollary therefore asks for a nonzero variance. That is the
  reading under which the printed sentence is true, not a narrowing of it.
* **The threshold is strict.** The paper's setup paragraph writes the
  permissible region with a non-strict inequality, while section 1 -- the
  sentence this module formalizes -- writes "the values of G when M > c". The
  strict form is section 1's. A non-strict selection event would take the same
  proof: the argument uses only that the selected slice lies above the
  threshold and its complement below.

## Strictness is not implied by non-degenerate noise

An earlier informal statement of this result claimed strictness whenever the
noise is non-degenerate. That is false. Take the goal uniform on the two values
0 and 10, the noise uniform on 0 and 1, and the threshold at 5: the selected
event is exactly the goal value 10, which by independence says nothing about the
noise, and the inequality is an equality. Strictness needs the threshold to cut
the noise law on a set of goal values of positive mass, which is what
`gap_selection_gt` asks for and what the worked model exhibits.

## Reuse

The one-dimensional cores `tail_integral_ge` and `tail_integral_gt` are the
association inequality between the identity and a tail indicator, specialised.
Mathlib at the pinned revision has no measure-theoretic form of it. Searched by
declaration shape (a product of two integrals bounded by an integral of a
product), by natural language, and by name across the tree: the association
family is `Mathlib.Combinatorics.SetFamily.FourFunctions`, over a finite
distributive lattice with `Finset` sums, and `Mathlib.Algebra.Order.Chebyshev`,
Chebyshev's sum inequality, also over a `Finset`. Neither transfers to a measure
on the line, and nothing under `Mathlib.MeasureTheory` or `Mathlib.Probability`
mentions monovariance or positive association. So the cores are proved here,
directly, from the threshold split.

They are generic mathematics under `docs/agent/policy/lean-routing.md`, kept
here because the consumers are here. An upstream offer of the measure-theoretic
association inequality would be a reasonable draft, but publication outside this
repository is maintainer-authorized and none has been opened.
-/

namespace AISafetyAtlas.Goodhart

open MeasureTheory Set

/-- **The one-dimensional core.** For an integrable random variable on the line,
the mass carried above a threshold is at least the unconditional mean times the
probability of clearing it. This is the association inequality between the
identity and the indicator of an upper ray. **Searched 2026-09-16 in Mathlib at
the pinned revision and not found**: the `Chebyshev` files there are the
polynomial and trigonometric ones, and FKG appears only for set families
(`Combinatorics/SetFamily/FourFunctions.lean`), not measure-theoretically. That
is one corpus, not the six a novelty-search record would name, so this is a
statement about where it was looked for rather than a novelty claim. It is
proved here from the split at the threshold. -/
public theorem tail_integral_ge (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun x : ℝ => x) ν) (t : ℝ) :
    (∫ x, x ∂ν) * ν.real (Ioi t) ≤ ∫ x in Ioi t, x ∂ν := by
  have hmeas : MeasurableSet (Ioi t) := measurableSet_Ioi
  have hcompl : (Ioi t)ᶜ = Iic t := compl_Ioi
  have hsplit : (∫ x in Ioi t, x ∂ν) + (∫ x in Iic t, x ∂ν) = ∫ x, x ∂ν := by
    rw [← hcompl]; exact integral_add_compl hmeas hν
  have hp0 : (0:ℝ) ≤ ν.real (Ioi t) := measureReal_nonneg
  have hq0 : (0:ℝ) ≤ ν.real (Iic t) := measureReal_nonneg
  have hsum : ν.real (Ioi t) + ν.real (Iic t) = 1 := by
    rw [← hcompl]
    exact probReal_add_probReal_compl hmeas
  -- the tail integral dominates `t` times the tail mass
  have hA : t * ν.real (Ioi t) ≤ ∫ x in Ioi t, x ∂ν := by
    have h1 : (0:ℝ) ≤ ∫ x in Ioi t, (x - t) ∂ν := by
      refine setIntegral_nonneg hmeas ?_
      intro x hx
      exact le_of_lt (sub_pos.mpr hx)
    have h2 : (∫ x in Ioi t, (x - t) ∂ν)
        = (∫ x in Ioi t, x ∂ν) - t * ν.real (Ioi t) := by
      rw [integral_sub (hν.restrict) (integrable_const t), setIntegral_const]
      simp [mul_comm]
    linarith [h1, h2.symm.le, h2.le]
  -- the lower integral is dominated by `t` times the lower mass
  have hB : (∫ x in Iic t, x ∂ν) ≤ t * ν.real (Iic t) := by
    have h1 : (∫ x in Iic t, (x - t) ∂ν) ≤ 0 := by
      refine setIntegral_nonpos measurableSet_Iic ?_
      intro x hx
      exact sub_nonpos.mpr hx
    have h2 : (∫ x in Iic t, (x - t) ∂ν)
        = (∫ x in Iic t, x ∂ν) - t * ν.real (Iic t) := by
      rw [integral_sub (hν.restrict) (integrable_const t), setIntegral_const]
      simp [mul_comm]
    linarith
  have key : (∫ x in Iic t, x ∂ν) * ν.real (Ioi t)
      ≤ (∫ x in Ioi t, x ∂ν) * ν.real (Iic t) :=
    calc (∫ x in Iic t, x ∂ν) * ν.real (Ioi t)
        ≤ (t * ν.real (Iic t)) * ν.real (Ioi t) := by
          exact mul_le_mul_of_nonneg_right hB hp0
      _ = (t * ν.real (Ioi t)) * ν.real (Iic t) := by ring
      _ ≤ (∫ x in Ioi t, x ∂ν) * ν.real (Iic t) :=
          mul_le_mul_of_nonneg_right hA hq0
  have hone : (∫ x in Ioi t, x ∂ν) * (ν.real (Ioi t) + ν.real (Iic t))
      = ∫ x in Ioi t, x ∂ν := by rw [hsum]; ring
  rw [← hsplit]
  nlinarith [key, hone]


/-- **The one-dimensional core, strictly.** Strictness needs only that the
threshold is a genuine cut: both the tail and its complement carry mass. -/
public theorem tail_integral_gt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun x : ℝ => x) ν) (t : ℝ)
    (h0 : 0 < ν.real (Ioi t)) (h1 : ν.real (Ioi t) < 1) :
    (∫ x, x ∂ν) * ν.real (Ioi t) < ∫ x in Ioi t, x ∂ν := by
  have hmeas : MeasurableSet (Ioi t) := measurableSet_Ioi
  have hcompl : (Ioi t)ᶜ = Iic t := compl_Ioi
  have hsplit : (∫ x in Ioi t, x ∂ν) + (∫ x in Iic t, x ∂ν) = ∫ x, x ∂ν := by
    rw [← hcompl]; exact integral_add_compl hmeas hν
  have hsum : ν.real (Ioi t) + ν.real (Iic t) = 1 := by
    rw [← hcompl]; exact probReal_add_probReal_compl hmeas
  have hq0 : 0 < ν.real (Iic t) := by linarith
  have hmass : ν (Ioi t) ≠ 0 := by
    intro h
    rw [Measure.real, h] at h0
    simp at h0
  have hA : t * ν.real (Ioi t) < ∫ x in Ioi t, x ∂ν := by
    have hint : IntegrableOn (fun x : ℝ => x - t) (Ioi t) ν :=
      (hν.restrict).sub (integrable_const t)
    have h1' : (0:ℝ) < ∫ x in Ioi t, (x - t) ∂ν := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
      · have hsupp : (Function.support (fun x : ℝ => x - t)) ∩ Ioi t = Ioi t := by
          ext x
          simp only [Function.mem_support, mem_inter_iff, mem_Ioi, ne_eq, sub_eq_zero]
          exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h, h⟩⟩
        rw [hsupp]
        exact pos_iff_ne_zero.mpr hmass
      · filter_upwards [ae_restrict_mem hmeas] with x hx
        exact le_of_lt (sub_pos.mpr hx)
    have h2 : (∫ x in Ioi t, (x - t) ∂ν)
        = (∫ x in Ioi t, x ∂ν) - t * ν.real (Ioi t) := by
      rw [integral_sub (hν.restrict) (integrable_const t), setIntegral_const]
      simp [mul_comm]
    linarith
  have hB : (∫ x in Iic t, x ∂ν) ≤ t * ν.real (Iic t) := by
    have hh1 : (∫ x in Iic t, (x - t) ∂ν) ≤ 0 := by
      refine setIntegral_nonpos measurableSet_Iic ?_
      intro x hx
      exact sub_nonpos.mpr hx
    have hh2 : (∫ x in Iic t, (x - t) ∂ν)
        = (∫ x in Iic t, x ∂ν) - t * ν.real (Iic t) := by
      rw [integral_sub (hν.restrict) (integrable_const t), setIntegral_const]
      simp [mul_comm]
    linarith
  have key : (∫ x in Iic t, x ∂ν) * ν.real (Ioi t)
      < (∫ x in Ioi t, x ∂ν) * ν.real (Iic t) :=
    calc (∫ x in Iic t, x ∂ν) * ν.real (Ioi t)
        ≤ (t * ν.real (Iic t)) * ν.real (Ioi t) :=
          mul_le_mul_of_nonneg_right hB h0.le
      _ = (t * ν.real (Ioi t)) * ν.real (Iic t) := by ring
      _ < (∫ x in Ioi t, x ∂ν) * ν.real (Iic t) :=
          (mul_lt_mul_of_pos_right hA hq0)
  have hone : (∫ x in Ioi t, x ∂ν) * (ν.real (Ioi t) + ν.real (Iic t))
      = ∫ x in Ioi t, x ∂ν := by rw [hsum]; ring
  rw [← hsplit]
  nlinarith [key, hone]


/-! ## The two-variable carrier -/

/-- The goal: what the regulator actually wants, the first coordinate. -/
@[expose] public def goal : ℝ × ℝ → ℝ := fun p => p.1

/-- The proxy-goal gap: the noise the proxy adds to the goal, the second
coordinate. Independence of the goal is the product structure of the measure. -/
@[expose] public def gap : ℝ × ℝ → ℝ := fun p => p.2

/-- The proxy: the goal plus the gap, which is print's equation (1). -/
@[expose] public def proxy : ℝ × ℝ → ℝ := fun p => p.1 + p.2

/-- The selection event: the states whose proxy clears the threshold. Print's
setup paragraph writes this with a non-strict inequality and its section 1 with
a strict one; the strict reading is section 1's, and is the one taken here. -/
@[expose] public def selected (c : ℝ) : Set (ℝ × ℝ) := {p | c < proxy p}

public theorem measurableSet_selected (c : ℝ) : MeasurableSet (selected c) :=
  measurableSet_lt measurable_const (measurable_fst.add measurable_snd)

private theorem indicator_slice (c g : ℝ) (f : ℝ → ℝ) :
    (fun n => (selected c).indicator (fun p => f p.2) (g, n))
      = (Ioi (c - g)).indicator f := by
  funext n
  by_cases h : c - g < n
  · rw [Set.indicator_of_mem (by simp [selected, proxy]; linarith),
      Set.indicator_of_mem (by simpa using h)]
  · rw [Set.indicator_of_notMem (by simp [selected, proxy]; linarith),
      Set.indicator_of_notMem (by simpa using h)]

private theorem integral_slice_gap (ν : Measure ℝ) (c g : ℝ) :
    (∫ n, (selected c).indicator gap (g, n) ∂ν) = ∫ n in Ioi (c - g), n ∂ν := by
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  exact congrFun (indicator_slice c g (fun n => n)) n

private theorem integral_slice_one (ν : Measure ℝ) (c g : ℝ) :
    (∫ n, (selected c).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (g, n) ∂ν)
      = ν.real (Ioi (c - g)) := by
  rw [show (∫ n, (selected c).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (g, n) ∂ν)
      = ∫ n in Ioi (c - g), (1:ℝ) ∂ν from ?_, setIntegral_const, smul_eq_mul, mul_one]
  rw [← integral_indicator measurableSet_Ioi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  exact congrFun (indicator_slice c g (fun _ => (1:ℝ))) n

section Prod

variable (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The selected mass, reduced to a one-dimensional integral over the goal. -/
public theorem measureReal_selected (c : ℝ) :
    (μ.prod ν).real (selected c) = ∫ g, ν.real (Ioi (c - g)) ∂μ := by
  have hS : MeasurableSet (selected c) := measurableSet_selected c
  have hmi : Integrable ((selected c).indicator (fun _ : ℝ × ℝ => (1:ℝ))) (μ.prod ν) :=
    (integrable_const (1:ℝ)).indicator hS
  have h0 : (μ.prod ν).real (selected c)
      = ∫ p, (selected c).indicator (fun _ : ℝ × ℝ => (1:ℝ)) p ∂(μ.prod ν) := by
    rw [integral_indicator hS, setIntegral_const]
    simp
  rw [h0, integral_prod _ hmi]
  simp only [integral_slice_one ν c]

/-- The selected gap mass, reduced to a one-dimensional integral over the goal. -/
public theorem integral_gap_selected
    (hν : Integrable (fun x : ℝ => x) ν) (c : ℝ) :
    (∫ p in selected c, gap p ∂(μ.prod ν)) = ∫ g, (∫ n in Ioi (c - g), n ∂ν) ∂μ := by
  have hS : MeasurableSet (selected c) := measurableSet_selected c
  have hgi : Integrable ((selected c).indicator gap) (μ.prod ν) :=
    (hν.comp_snd μ).indicator hS
  rw [← integral_indicator hS, integral_prod _ hgi]
  simp only [integral_slice_gap ν c]

private theorem integrable_tail_gap (hν : Integrable (fun x : ℝ => x) ν) (c : ℝ) :
    Integrable (fun g => ∫ n in Ioi (c - g), n ∂ν) μ := by
  have hS : MeasurableSet (selected c) := measurableSet_selected c
  have hgi : Integrable ((selected c).indicator gap) (μ.prod ν) :=
    (hν.comp_snd μ).indicator hS
  simpa only [integral_slice_gap ν c] using hgi.integral_prod_left

private theorem integrable_tail_mass (c : ℝ) :
    Integrable (fun g => ν.real (Ioi (c - g))) μ := by
  have hS : MeasurableSet (selected c) := measurableSet_selected c
  have hmi : Integrable ((selected c).indicator (fun _ : ℝ × ℝ => (1:ℝ))) (μ.prod ν) :=
    (integrable_const (1:ℝ)).indicator hS
  simpa only [integral_slice_one ν c] using hmi.integral_prod_left

/-- **Selecting on the proxy inflates the expected proxy-goal gap.** In product
form: the selected gap mass is at least the unconditional mean gap times the
selected mass. Dividing through by a positive selected mass turns this into the
conditional-expectation reading, that the expected gap among selected states is
at least the expected gap overall. -/
public theorem gap_selection_ge
    (hν : Integrable (fun x : ℝ => x) ν) (c : ℝ) :
    (∫ x, x ∂ν) * (μ.prod ν).real (selected c)
      ≤ ∫ p in selected c, gap p ∂(μ.prod ν) := by
  rw [measureReal_selected μ ν c, integral_gap_selected μ ν hν c, ← integral_const_mul]
  refine integral_mono ((integrable_tail_mass μ ν c).const_mul _)
    (integrable_tail_gap μ ν hν c) (fun g => ?_)
  exact tail_integral_ge ν hν (c - g)

/-- **The same, strictly.** The extra hypothesis is a set of goal values of
positive mass at which the threshold genuinely cuts the noise law. Some such
hypothesis is needed: non-degenerate noise alone does not give strictness, since
a threshold the goal alone decides filters no noise at all. -/
public theorem gap_selection_gt
    (hν : Integrable (fun x : ℝ => x) ν) (c : ℝ)
    {A : Set ℝ} (hA : μ A ≠ 0)
    (hcut : ∀ g ∈ A, 0 < ν.real (Ioi (c - g)) ∧ ν.real (Ioi (c - g)) < 1) :
    (∫ x, x ∂ν) * (μ.prod ν).real (selected c)
      < ∫ p in selected c, gap p ∂(μ.prod ν) := by
  have hFi := integrable_tail_gap μ ν hν c
  have hHi := (integrable_tail_mass μ ν c).const_mul (∫ x, x ∂ν)
  have hnn : (0 : ℝ → ℝ)
      ≤ fun g => (∫ n in Ioi (c - g), n ∂ν) - (∫ x, x ∂ν) * ν.real (Ioi (c - g)) :=
    fun g => sub_nonneg.mpr (tail_integral_ge ν hν (c - g))
  have hpos : 0 < ∫ g, ((∫ n in Ioi (c - g), n ∂ν)
      - (∫ x, x ∂ν) * ν.real (Ioi (c - g))) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnn (hFi.sub hHi)]
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr hA) (measure_mono ?_)
    intro g hg
    have h := tail_integral_gt ν hν (c - g) (hcut g hg).1 (hcut g hg).2
    exact ne_of_gt (sub_pos.mpr h)
  rw [integral_sub hFi hHi] at hpos
  rw [measureReal_selected μ ν c, integral_gap_selected μ ν hν c, ← integral_const_mul]
  linarith

end Prod

section Gaussian

open ProbabilityTheory
open scoped NNReal

private theorem gaussianReal_tail_mem (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    0 < (gaussianReal m v).real (Ioi t) ∧ (gaussianReal m v).real (Ioi t) < 1 := by
  have hac : volume ≪ gaussianReal m v := gaussianReal_absolutelyContinuous' m hv
  have hIoi : gaussianReal m v (Ioi t) ≠ 0 := by
    intro h
    have h' := hac h
    rw [Real.volume_Ioi] at h'
    exact ENNReal.top_ne_zero h'
  have hIic : gaussianReal m v (Iic t) ≠ 0 := by
    intro h
    have h' := hac h
    rw [Real.volume_Iic] at h'
    exact ENNReal.top_ne_zero h'
  have hsum : (gaussianReal m v).real (Ioi t) + (gaussianReal m v).real (Iic t) = 1 := by
    rw [← compl_Ioi]
    exact probReal_add_probReal_compl measurableSet_Ioi
  have h1 : 0 < (gaussianReal m v).real (Ioi t) :=
    ENNReal.toReal_pos hIoi (measure_ne_top _ _)
  have h2 : 0 < (gaussianReal m v).real (Iic t) :=
    ENNReal.toReal_pos hIic (measure_ne_top _ _)
  exact ⟨h1, by linarith⟩

/-- **Print's Gaussian instance.** With the noise normal at nonzero variance,
every threshold cuts the noise law, so the cut hypothesis discharges itself and
the inequality is strict for every goal law and every threshold. The mean of the
noise is what the left-hand side multiplies. Nonzero variance is the hypothesis
print leaves implicit: at variance zero `gaussianReal` is a Dirac measure and
there is no noise to select on. -/
public theorem gap_selection_gaussianReal_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    m * (μ.prod (gaussianReal m v)).real (selected c)
      < ∫ p in selected c, gap p ∂(μ.prod (gaussianReal m v)) := by
  have hν : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  have h := gap_selection_gt μ (gaussianReal m v) hν c (A := Set.univ)
    (by simp) (fun g _ => gaussianReal_tail_mem m hv (c - g))
  rwa [integral_id_gaussianReal] at h

end Gaussian

end AISafetyAtlas.Goodhart
