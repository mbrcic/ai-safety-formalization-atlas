module

public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.Probability.Distributions.Gaussian.Real
public import AISafetyAtlas.Goodhart.Extremal

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
* `goal_selection_ge`, `goal_selection_gt`, `goal_selected_compl_le`,
  `goal_selected_compl_lt`, `goal_selection_gaussianReal_gt` -- selection raises
  the expected goal too, and above its value on the unselected states.
* `goal_selected_compl_gaussianReal_lt` -- "higher than otherwise", strictly, at
  Gaussian noise, for every goal law that is not a point mass.
* `selectedGe` and `gap_selectionGe_ge`, `gap_selectionGe_gt`,
  `gap_selectionGe_gaussianReal_gt` -- the gap statements at the non-strict event `M ≥ c` of print's setup paragraph.

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
That section recorded print's second consequence, that the goal itself is
higher under selection, as not proved here. **Added 2026-11-21:** it now is, as
`goal_selection_ge`, `goal_selection_gt` and the "than otherwise" forms
`goal_selected_compl_le`/`goal_selected_compl_lt`, read off the gap statements
through the coordinate swap; and print's setup inequality `M(s) ≥ c` has its own
event `selectedGe` with the gap statements restated at it.

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

/-! ### Selection raises the goal too (print's first component)

Print, PDF p. 2: *"Despite the lack of bias, for large values of `c` the values
of `G` when `M > c` is expected to be higher than otherwise."* The carrier is
symmetric in its two coordinates — the proxy is their sum and the law is a
product — so the goal statements are the gap statements read through the
coordinate swap, with the roles of `μ` and `ν` exchanged. -/

private theorem swap_preimage_selected (c : ℝ) : Prod.swap ⁻¹' selected c = selected c := by
  ext p
  simp only [Set.mem_preimage, selected, proxy, Prod.fst_swap, Prod.snd_swap,
    Set.mem_ofPred_eq]
  rw [add_comm]

private theorem measureReal_selected_swap (c : ℝ) :
    (μ.prod ν).real (selected c) = (ν.prod μ).real (selected c) := by
  have h := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).measureReal_preimage
    (measurableSet_selected c).nullMeasurableSet
  rw [swap_preimage_selected] at h
  exact h.symm

private theorem integral_goal_selected_swap (c : ℝ) :
    (∫ p in selected c, goal p ∂(μ.prod ν)) = ∫ p in selected c, gap p ∂(ν.prod μ) := by
  have h := (Measure.measurePreserving_swap (μ := ν) (ν := μ)).setIntegral_preimage_emb
    (MeasurableEquiv.prodComm (α := ℝ) (β := ℝ)).measurableEmbedding goal (selected c)
  rw [swap_preimage_selected] at h
  exact h.symm

/-- **Selecting on the proxy raises the expected goal.** In product form: the
selected goal mass is at least the unconditional mean goal times the selected
mass, at every threshold. With independent noise, this is print's claim that
`G` is expected to be higher when `M > c`; `goal_selected_compl_le` is the
comparison with the unselected states that print's "than otherwise" names. -/
public theorem goal_selection_ge
    (hμ : Integrable (fun x : ℝ => x) μ) (c : ℝ) :
    (∫ x, x ∂μ) * (μ.prod ν).real (selected c)
      ≤ ∫ p in selected c, goal p ∂(μ.prod ν) := by
  rw [measureReal_selected_swap, integral_goal_selected_swap]
  exact gap_selection_ge ν μ hμ c

/-- **The same, strictly.** The hypothesis is a set of noise values of positive
mass at which the threshold genuinely cuts the goal law. -/
public theorem goal_selection_gt
    (hμ : Integrable (fun x : ℝ => x) μ) (c : ℝ)
    {B : Set ℝ} (hB : ν B ≠ 0)
    (hcut : ∀ n ∈ B, 0 < μ.real (Ioi (c - n)) ∧ μ.real (Ioi (c - n)) < 1) :
    (∫ x, x ∂μ) * (μ.prod ν).real (selected c)
      < ∫ p in selected c, goal p ∂(μ.prod ν) := by
  rw [measureReal_selected_swap, integral_goal_selected_swap]
  exact gap_selection_gt ν μ hμ c hB hcut

private theorem goal_split (hμ : Integrable (fun x : ℝ => x) μ) (c : ℝ) :
    (∫ p in selected c, goal p ∂(μ.prod ν)) + (∫ p in (selected c)ᶜ, goal p ∂(μ.prod ν))
        = ∫ x, x ∂μ ∧
      (μ.prod ν).real (selected c) + (μ.prod ν).real (selected c)ᶜ = 1 := by
  refine ⟨?_, probReal_add_probReal_compl (measurableSet_selected c)⟩
  rw [integral_add_compl (f := goal) (measurableSet_selected c) (hμ.comp_fst ν)]
  have h := integral_fun_fst (μ := μ) (ν := ν) (fun x : ℝ => x)
  simp only [probReal_univ, one_smul] at h
  exact h

/-- **Print's "higher than otherwise"**, cross-multiplied so that no conditional
expectation needs a positive denominator: the goal mass on the unselected states
times the selected mass is at most the goal mass on the selected states times
the unselected mass. Where both masses are positive this is
`E[G | M ≤ c] ≤ E[G | M > c]`. -/
public theorem goal_selected_compl_le
    (hμ : Integrable (fun x : ℝ => x) μ) (c : ℝ) :
    (∫ p in (selected c)ᶜ, goal p ∂(μ.prod ν)) * (μ.prod ν).real (selected c)
      ≤ (∫ p in selected c, goal p ∂(μ.prod ν)) * (μ.prod ν).real (selected c)ᶜ := by
  obtain ⟨hI, hP⟩ := goal_split μ ν hμ c
  have hge := goal_selection_ge μ ν hμ c
  set IS := ∫ p in selected c, goal p ∂(μ.prod ν)
  set IC := ∫ p in (selected c)ᶜ, goal p ∂(μ.prod ν)
  set PS := (μ.prod ν).real (selected c)
  set PC := (μ.prod ν).real (selected c)ᶜ
  have h1 : IC * PS = (∫ x, x ∂μ) * PS - IS * PS := by rw [← hI]; ring
  have h2 : IS * PC = IS - IS * PS := by rw [show PC = 1 - PS by linarith]; ring
  rw [h1, h2]
  linarith

/-- **"Higher than otherwise", strictly**, under `goal_selection_gt`'s cut
hypothesis. -/
public theorem goal_selected_compl_lt
    (hμ : Integrable (fun x : ℝ => x) μ) (c : ℝ)
    {B : Set ℝ} (hB : ν B ≠ 0)
    (hcut : ∀ n ∈ B, 0 < μ.real (Ioi (c - n)) ∧ μ.real (Ioi (c - n)) < 1) :
    (∫ p in (selected c)ᶜ, goal p ∂(μ.prod ν)) * (μ.prod ν).real (selected c)
      < (∫ p in selected c, goal p ∂(μ.prod ν)) * (μ.prod ν).real (selected c)ᶜ := by
  obtain ⟨hI, hP⟩ := goal_split μ ν hμ c
  have hgt := goal_selection_gt μ ν hμ c hB hcut
  set IS := ∫ p in selected c, goal p ∂(μ.prod ν)
  set IC := ∫ p in (selected c)ᶜ, goal p ∂(μ.prod ν)
  set PS := (μ.prod ν).real (selected c)
  set PC := (μ.prod ν).real (selected c)ᶜ
  have h1 : IC * PS = (∫ x, x ∂μ) * PS - IS * PS := by rw [← hI]; ring
  have h2 : IS * PC = IS - IS * PS := by rw [show PC = 1 - PS by linarith]; ring
  rw [h1, h2]
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

/-- **The goal mirror at a Gaussian goal.** With the goal normal at nonzero
variance, every threshold cuts the goal law, so for every noise law and every
threshold the selected states have strictly higher expected goal than the
unconditional mean `m`. -/
public theorem goal_selection_gaussianReal_gt (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    m * ((gaussianReal m v).prod ν).real (selected c)
      < ∫ p in selected c, goal p ∂((gaussianReal m v).prod ν) := by
  have hμ : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  have h := goal_selection_gt (gaussianReal m v) ν hμ c (B := Set.univ)
    (by simp) (fun n _ => gaussianReal_tail_mem m hv (c - n))
  rwa [integral_id_gaussianReal] at h

/-- A goal law that is integrable and not a point mass is cut by an interval of
thresholds: some `t₀ < t₁` have `μ (Ioi t₁) > 0` and `μ (Ioi t₀) < 1`. The cut is at
the mean `t₀`: a law with no mass at or below its mean, or none above it, is the
Dirac measure at the mean; `t₁` comes from `Ioi t₀ = ⋃ n, Ioi (t₀ + 1/(n+1))`. -/
private theorem exists_tail_cut (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (hdeg : ∀ a : ℝ, μ ≠ Measure.dirac a) :
    ∃ t₀ t₁, t₀ < t₁ ∧ 0 < μ.real (Ioi t₁) ∧ μ.real (Ioi t₀) < 1 := by
  set t₀ := ∫ x, x ∂μ with ht₀
  -- the part at or below the mean carries mass
  have hIic : μ (Iic t₀) ≠ 0 := by
    intro h
    have hae : ∀ᵐ x ∂μ, t₀ < x := by
      rw [ae_iff]; convert h using 2; ext x; simp
    have hzero : ∫ x, (x - t₀) ∂μ = 0 := by
      rw [integral_sub hμ (integrable_const t₀)]; simp [← ht₀]
    have hpos : 0 < ∫ x, (x - t₀) ∂μ := by
      rw [integral_pos_iff_support_of_nonneg_ae
        (hae.mono fun x hx => (sub_pos.mpr hx).le) (hμ.sub (integrable_const t₀))]
      have : (Function.support fun x : ℝ => x - t₀) = {t₀}ᶜ := by
        ext x; simp [sub_eq_zero]
      rw [this]
      refine pos_iff_ne_zero.mpr fun h0 => ?_
      have h1 : μ {t₀} = 1 := by
        rwa [prob_compl_eq_zero_iff (measurableSet_singleton _)] at h0
      have h2 : μ {t₀} ≤ μ (Iic t₀) := measure_mono (by simp)
      rw [h, h1] at h2; simp at h2
    linarith
  -- the part above the mean carries mass, else the law is the Dirac measure at it
  have hIoi : μ (Ioi t₀) ≠ 0 := by
    intro h
    have hae : ∀ᵐ x ∂μ, x ≤ t₀ := by
      rw [ae_iff]; convert h using 2; ext x; simp
    have hz : ∫ x, (t₀ - x) ∂μ = 0 := by
      rw [integral_sub (integrable_const t₀) hμ]; simp [← ht₀]
    have heq := (integral_eq_zero_iff_of_nonneg_ae (hae.mono fun x hx => sub_nonneg.mpr hx)
      ((integrable_const t₀).sub hμ)).mp hz
    have hconst : (fun x : ℝ => x) =ᵐ[μ] fun _ => t₀ :=
      heq.mono fun x hx => by simp only [Pi.zero_apply, sub_eq_zero] at hx; exact hx.symm
    exact hdeg t₀ (by simpa using (hasLaw_dirac_of_ae_eq hconst).map_eq)
  -- some ray strictly above the mean still carries mass
  have hex : ∃ n : ℕ, μ (Ioi (t₀ + 1 / (n + 1))) ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    apply hIoi
    have : Ioi t₀ = ⋃ n : ℕ, Ioi (t₀ + 1 / (n + 1)) := by
      ext x
      simp only [mem_Ioi, mem_iUnion]
      constructor
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hx)
        exact ⟨n, by linarith⟩
      · rintro ⟨n, hn⟩
        have : (0:ℝ) < 1 / (n + 1) := by positivity
        linarith
    rw [this]
    exact measure_iUnion_null hcon
  obtain ⟨n, hn⟩ := hex
  refine ⟨t₀, t₀ + 1 / (n + 1), lt_add_of_pos_right _ (by positivity),
    ENNReal.toReal_pos hn (measure_ne_top _ _), ?_⟩
  have hsum : μ.real (Ioi t₀) + μ.real (Iic t₀) = 1 := by
    rw [← compl_Ioi]; exact probReal_add_probReal_compl measurableSet_Ioi
  have : 0 < μ.real (Iic t₀) := ENNReal.toReal_pos hIic (measure_ne_top _ _)
  linarith

/-- **Print's "higher than otherwise", strictly, at print's Simple Model, for every
goal that is not a point mass.** Manheim and Garrabrant, PDF p. 2, the paragraph
after equation (1) `M = G + normal(μ, σ²)`: *"for large values of `c` the values of
`G` when `M > c` is expected to be higher than otherwise."* With the noise normal
at nonzero variance and independent of the goal (the product carrier), and the goal
law integrable and not a Dirac measure, the goal mass on the unselected states times
the selected mass is strictly below the goal mass on the selected states times the
unselected mass; where both masses are positive this is
`E[G | M ≤ c] < E[G | M > c]`. It holds at every threshold, not only large ones.

Non-degeneracy is the one hypothesis print does not write: at a constant goal both
conditional means are that constant and the strict inequality fails
(`docs/provenance/refutations/manheim-garrabrant-regressional-literal.lean`). The
proof discharges the cut hypothesis of `goal_selected_compl_lt` with an interval of
noise values: a non-degenerate goal law is cut by every threshold in some interval
`[t₀, t₁]`, and the Gaussian charges every nonempty interval. -/
public theorem goal_selected_compl_gaussianReal_lt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (hdeg : ∀ a : ℝ, μ ≠ Measure.dirac a)
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    (∫ p in (selected c)ᶜ, goal p ∂(μ.prod (gaussianReal m v))) *
        (μ.prod (gaussianReal m v)).real (selected c)
      < (∫ p in selected c, goal p ∂(μ.prod (gaussianReal m v))) *
        (μ.prod (gaussianReal m v)).real (selected c)ᶜ := by
  obtain ⟨t₀, t₁, h01, h1, h0⟩ := exists_tail_cut μ hμ hdeg
  refine goal_selected_compl_lt μ (gaussianReal m v) hμ c
    (B := Icc (c - t₁) (c - t₀)) ?_ ?_
  · intro h
    have h' := gaussianReal_absolutelyContinuous' m hv h
    rw [Real.volume_Icc] at h'
    simp at h'
    linarith
  · rintro n ⟨hl, hr⟩
    exact ⟨lt_of_lt_of_le h1 (measureReal_mono (Ioi_subset_Ioi (by linarith))),
      lt_of_le_of_lt (measureReal_mono (Ioi_subset_Ioi (by linarith))) h0⟩

end Gaussian

/-! ## The non-strict selection event

Print's setup paragraph (mg-setup, PDF p. 2) writes the permissible states with a
non-strict inequality, *"`s ∈ A` if `M(s) ≥ c`"*, and its section 1 with a strict
one. `selected` takes the strict reading. `selectedGe` is the setup paragraph's,
and the gap statements hold at it too; at a proxy law with an atom at the
threshold the two events differ in mass. -/

/-- **The permissible states at print's setup inequality**: the states whose
proxy is at least the threshold (mg-setup, PDF p. 2). -/
@[expose] public def selectedGe (c : ℝ) : Set (ℝ × ℝ) := {p | c ≤ proxy p}

public theorem measurableSet_selectedGe (c : ℝ) : MeasurableSet (selectedGe c) :=
  measurableSet_le measurable_const (measurable_fst.add measurable_snd)

/-! ### The carrier at print's arbitrary system

Print's setup (Manheim and Garrabrant, mg-setup, PDF p. 2) takes *"a system `S`
with a set of possible states"*, a goal `G : S → ℝ` and a proxy `M : S → ℝ`, with
no finiteness or countability. The carrier above is one instance. Every instance
maps into it along `s ↦ (G s, M s − G s)`, and the map carries print's objects
to the carrier's: the goal to `goal`, the difference `M − G` to `gap`, the proxy
to `proxy`, and print's region `A = {s | M s ≥ c}`
(`AISafetyAtlas.Goodhart.Extremal.selectedAt`) to the preimage of `selectedGe c`.
-/

/-- **Print's system, read into the carrier**: a state goes to its goal value and
its proxy-goal difference. -/
public theorem goalGap_comp (S : Type*) (G M : S → ℝ) :
    goal ∘ (fun s => (G s, M s - G s)) = G ∧
      gap ∘ (fun s => (G s, M s - G s)) = M - G ∧
      proxy ∘ (fun s => (G s, M s - G s)) = M := by
  refine ⟨rfl, rfl, ?_⟩
  funext s
  simp [proxy]

/-- **Print's selection region is the carrier's, pulled back** (mg-setup, PDF
p. 2: *"`s ∈ A` if `M(s) ≥ c`"*): for any system `S`, goal `G` and proxy `M`,
selecting on `M` selects exactly the states whose image clears `selectedGe c`,
a selection on the sum of the goal and the difference `M − G` (S17-R02). -/
public theorem preimage_selectedGe (S : Type*) (G M : S → ℝ) (c : ℝ) :
    (fun s => (G s, M s - G s)) ⁻¹' selectedGe c = Extremal.selectedAt M c := by
  ext s
  simp [selectedGe, proxy]

/-- **The one-dimensional core at a closed upper ray**: the mass carried at or
above a threshold is at least the mean times the probability of reaching it. -/
public theorem tail_integral_ge_Ici (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun x : ℝ => x) ν) (t : ℝ) :
    (∫ x, x ∂ν) * ν.real (Ici t) ≤ ∫ x in Ici t, x ∂ν := by
  have hmeas : MeasurableSet (Ici t) := measurableSet_Ici
  have hcompl : (Ici t)ᶜ = Iio t := compl_Ici
  have hsplit : (∫ x in Ici t, x ∂ν) + (∫ x in Iio t, x ∂ν) = ∫ x, x ∂ν := by
    rw [← hcompl]; exact integral_add_compl hmeas hν
  have hp0 : (0:ℝ) ≤ ν.real (Ici t) := measureReal_nonneg
  have hq0 : (0:ℝ) ≤ ν.real (Iio t) := measureReal_nonneg
  have hsum : ν.real (Ici t) + ν.real (Iio t) = 1 := by
    rw [← hcompl]; exact probReal_add_probReal_compl hmeas
  have hA : t * ν.real (Ici t) ≤ ∫ x in Ici t, x ∂ν := by
    have h1 : (0:ℝ) ≤ ∫ x in Ici t, (x - t) ∂ν :=
      setIntegral_nonneg hmeas fun x hx => sub_nonneg.mpr hx
    have h2 : (∫ x in Ici t, (x - t) ∂ν)
        = (∫ x in Ici t, x ∂ν) - t * ν.real (Ici t) := by
      rw [integral_sub (hν.restrict) (integrable_const t), setIntegral_const]
      simp [mul_comm]
    linarith
  have hB : (∫ x in Iio t, x ∂ν) ≤ t * ν.real (Iio t) := by
    have h1 : (∫ x in Iio t, (x - t) ∂ν) ≤ 0 :=
      setIntegral_nonpos measurableSet_Iio fun x hx => sub_nonpos.mpr (le_of_lt hx)
    have h2 : (∫ x in Iio t, (x - t) ∂ν)
        = (∫ x in Iio t, x ∂ν) - t * ν.real (Iio t) := by
      rw [integral_sub (hν.restrict) (integrable_const t), setIntegral_const]
      simp [mul_comm]
    linarith
  have key : (∫ x in Iio t, x ∂ν) * ν.real (Ici t)
      ≤ (∫ x in Ici t, x ∂ν) * ν.real (Iio t) :=
    calc (∫ x in Iio t, x ∂ν) * ν.real (Ici t)
        ≤ (t * ν.real (Iio t)) * ν.real (Ici t) := mul_le_mul_of_nonneg_right hB hp0
      _ = (t * ν.real (Ici t)) * ν.real (Iio t) := by ring
      _ ≤ (∫ x in Ici t, x ∂ν) * ν.real (Iio t) := mul_le_mul_of_nonneg_right hA hq0
  have hone : (∫ x in Ici t, x ∂ν) * (ν.real (Ici t) + ν.real (Iio t))
      = ∫ x in Ici t, x ∂ν := by rw [hsum]; ring
  rw [← hsplit]
  nlinarith [key, hone]

/-- **The same, strictly**, when the closed ray and its complement both carry
mass. The strictness now comes from the part strictly below the threshold. -/
public theorem tail_integral_gt_Ici (ν : Measure ℝ) [IsProbabilityMeasure ν]
    (hν : Integrable (fun x : ℝ => x) ν) (t : ℝ)
    (h0 : 0 < ν.real (Ici t)) (h1 : ν.real (Ici t) < 1) :
    (∫ x, x ∂ν) * ν.real (Ici t) < ∫ x in Ici t, x ∂ν := by
  have hmeas : MeasurableSet (Ici t) := measurableSet_Ici
  have hcompl : (Ici t)ᶜ = Iio t := compl_Ici
  have hsplit : (∫ x in Ici t, x ∂ν) + (∫ x in Iio t, x ∂ν) = ∫ x, x ∂ν := by
    rw [← hcompl]; exact integral_add_compl hmeas hν
  have hsum : ν.real (Ici t) + ν.real (Iio t) = 1 := by
    rw [← hcompl]; exact probReal_add_probReal_compl hmeas
  have hq0 : 0 < ν.real (Iio t) := by linarith
  have hmass : ν (Iio t) ≠ 0 := by
    intro h
    rw [Measure.real, h] at hq0
    simp at hq0
  have hA : t * ν.real (Ici t) ≤ ∫ x in Ici t, x ∂ν := by
    have hh1 : (0:ℝ) ≤ ∫ x in Ici t, (x - t) ∂ν :=
      setIntegral_nonneg hmeas fun x hx => sub_nonneg.mpr hx
    have hh2 : (∫ x in Ici t, (x - t) ∂ν)
        = (∫ x in Ici t, x ∂ν) - t * ν.real (Ici t) := by
      rw [integral_sub (hν.restrict) (integrable_const t), setIntegral_const]
      simp [mul_comm]
    linarith
  have hB : (∫ x in Iio t, x ∂ν) < t * ν.real (Iio t) := by
    have hint : IntegrableOn (fun x : ℝ => t - x) (Iio t) ν :=
      (integrable_const t).sub (hν.restrict)
    have hh1 : (0:ℝ) < ∫ x in Iio t, (t - x) ∂ν := by
      rw [setIntegral_pos_iff_support_of_nonneg_ae _ hint]
      · have hsupp : (Function.support (fun x : ℝ => t - x)) ∩ Iio t = Iio t := by
          ext x
          simp only [Function.mem_support, mem_inter_iff, mem_Iio, ne_eq, sub_eq_zero]
          exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h, h⟩⟩
        rw [hsupp]
        exact pos_iff_ne_zero.mpr hmass
      · filter_upwards [ae_restrict_mem measurableSet_Iio] with x hx
        exact le_of_lt (sub_pos.mpr hx)
    have hh2 : (∫ x in Iio t, (t - x) ∂ν)
        = t * ν.real (Iio t) - ∫ x in Iio t, x ∂ν := by
      rw [integral_sub (integrable_const t) (hν.restrict), setIntegral_const]
      simp [mul_comm]
    linarith
  have key : (∫ x in Iio t, x ∂ν) * ν.real (Ici t)
      < (∫ x in Ici t, x ∂ν) * ν.real (Iio t) :=
    calc (∫ x in Iio t, x ∂ν) * ν.real (Ici t)
        < (t * ν.real (Iio t)) * ν.real (Ici t) := mul_lt_mul_of_pos_right hB h0
      _ = (t * ν.real (Ici t)) * ν.real (Iio t) := by ring
      _ ≤ (∫ x in Ici t, x ∂ν) * ν.real (Iio t) := mul_le_mul_of_nonneg_right hA hq0.le
  have hone : (∫ x in Ici t, x ∂ν) * (ν.real (Ici t) + ν.real (Iio t))
      = ∫ x in Ici t, x ∂ν := by rw [hsum]; ring
  rw [← hsplit]
  nlinarith [key, hone]

private theorem indicator_sliceGe (c g : ℝ) (f : ℝ → ℝ) :
    (fun n => (selectedGe c).indicator (fun p => f p.2) (g, n))
      = (Ici (c - g)).indicator f := by
  funext n
  by_cases h : c - g ≤ n
  · rw [Set.indicator_of_mem (by simp [selectedGe, proxy]; linarith),
      Set.indicator_of_mem (by simpa using h)]
  · rw [Set.indicator_of_notMem (by simp [selectedGe, proxy]; linarith),
      Set.indicator_of_notMem (by simpa using h)]

private theorem integral_sliceGe_gap (ν : Measure ℝ) (c g : ℝ) :
    (∫ n, (selectedGe c).indicator gap (g, n) ∂ν) = ∫ n in Ici (c - g), n ∂ν := by
  rw [← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  exact congrFun (indicator_sliceGe c g (fun n => n)) n

private theorem integral_sliceGe_one (ν : Measure ℝ) (c g : ℝ) :
    (∫ n, (selectedGe c).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (g, n) ∂ν)
      = ν.real (Ici (c - g)) := by
  rw [show (∫ n, (selectedGe c).indicator (fun _ : ℝ × ℝ => (1:ℝ)) (g, n) ∂ν)
      = ∫ n in Ici (c - g), (1:ℝ) ∂ν from ?_, setIntegral_const, smul_eq_mul, mul_one]
  rw [← integral_indicator measurableSet_Ici]
  refine integral_congr_ae (Filter.Eventually.of_forall fun n => ?_)
  exact congrFun (indicator_sliceGe c g (fun _ => (1:ℝ))) n

section ProdGe

variable (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]

/-- The mass of the non-strict selection event, reduced to a one-dimensional
integral over the goal. -/
public theorem measureReal_selectedGe (c : ℝ) :
    (μ.prod ν).real (selectedGe c) = ∫ g, ν.real (Ici (c - g)) ∂μ := by
  have hS : MeasurableSet (selectedGe c) := measurableSet_selectedGe c
  have hmi : Integrable ((selectedGe c).indicator (fun _ : ℝ × ℝ => (1:ℝ))) (μ.prod ν) :=
    (integrable_const (1:ℝ)).indicator hS
  have h0 : (μ.prod ν).real (selectedGe c)
      = ∫ p, (selectedGe c).indicator (fun _ : ℝ × ℝ => (1:ℝ)) p ∂(μ.prod ν) := by
    rw [integral_indicator hS, setIntegral_const]
    simp
  rw [h0, integral_prod _ hmi]
  simp only [integral_sliceGe_one ν c]

/-- The gap mass on the non-strict selection event, reduced to a
one-dimensional integral over the goal. -/
public theorem integral_gap_selectedGe
    (hν : Integrable (fun x : ℝ => x) ν) (c : ℝ) :
    (∫ p in selectedGe c, gap p ∂(μ.prod ν)) = ∫ g, (∫ n in Ici (c - g), n ∂ν) ∂μ := by
  have hS : MeasurableSet (selectedGe c) := measurableSet_selectedGe c
  have hgi : Integrable ((selectedGe c).indicator gap) (μ.prod ν) :=
    (hν.comp_snd μ).indicator hS
  rw [← integral_indicator hS, integral_prod _ hgi]
  simp only [integral_sliceGe_gap ν c]

private theorem integrable_tailGe_gap (hν : Integrable (fun x : ℝ => x) ν) (c : ℝ) :
    Integrable (fun g => ∫ n in Ici (c - g), n ∂ν) μ := by
  have hS : MeasurableSet (selectedGe c) := measurableSet_selectedGe c
  have hgi : Integrable ((selectedGe c).indicator gap) (μ.prod ν) :=
    (hν.comp_snd μ).indicator hS
  simpa only [integral_sliceGe_gap ν c] using hgi.integral_prod_left

private theorem integrable_tailGe_mass (c : ℝ) :
    Integrable (fun g => ν.real (Ici (c - g))) μ := by
  have hS : MeasurableSet (selectedGe c) := measurableSet_selectedGe c
  have hmi : Integrable ((selectedGe c).indicator (fun _ : ℝ × ℝ => (1:ℝ))) (μ.prod ν) :=
    (integrable_const (1:ℝ)).indicator hS
  simpa only [integral_sliceGe_one ν c] using hmi.integral_prod_left

/-- **Selecting on the proxy inflates the expected proxy-goal gap, at print's
setup inequality `M(s) ≥ c`.** `gap_selection_ge` at `selectedGe`. -/
public theorem gap_selectionGe_ge
    (hν : Integrable (fun x : ℝ => x) ν) (c : ℝ) :
    (∫ x, x ∂ν) * (μ.prod ν).real (selectedGe c)
      ≤ ∫ p in selectedGe c, gap p ∂(μ.prod ν) := by
  rw [measureReal_selectedGe μ ν c, integral_gap_selectedGe μ ν hν c, ← integral_const_mul]
  refine integral_mono ((integrable_tailGe_mass μ ν c).const_mul _)
    (integrable_tailGe_gap μ ν hν c) (fun g => ?_)
  exact tail_integral_ge_Ici ν hν (c - g)

/-- **The same, strictly**, given a set of goal values of positive mass at which
the closed ray genuinely cuts the noise law. -/
public theorem gap_selectionGe_gt
    (hν : Integrable (fun x : ℝ => x) ν) (c : ℝ)
    {A : Set ℝ} (hA : μ A ≠ 0)
    (hcut : ∀ g ∈ A, 0 < ν.real (Ici (c - g)) ∧ ν.real (Ici (c - g)) < 1) :
    (∫ x, x ∂ν) * (μ.prod ν).real (selectedGe c)
      < ∫ p in selectedGe c, gap p ∂(μ.prod ν) := by
  have hFi := integrable_tailGe_gap μ ν hν c
  have hHi := (integrable_tailGe_mass μ ν c).const_mul (∫ x, x ∂ν)
  have hnn : (0 : ℝ → ℝ)
      ≤ fun g => (∫ n in Ici (c - g), n ∂ν) - (∫ x, x ∂ν) * ν.real (Ici (c - g)) :=
    fun g => sub_nonneg.mpr (tail_integral_ge_Ici ν hν (c - g))
  have hpos : 0 < ∫ g, ((∫ n in Ici (c - g), n ∂ν)
      - (∫ x, x ∂ν) * ν.real (Ici (c - g))) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg hnn (hFi.sub hHi)]
    refine lt_of_lt_of_le (pos_iff_ne_zero.mpr hA) (measure_mono ?_)
    intro g hg
    have h := tail_integral_gt_Ici ν hν (c - g) (hcut g hg).1 (hcut g hg).2
    exact ne_of_gt (sub_pos.mpr h)
  rw [integral_sub hFi hHi] at hpos
  rw [measureReal_selectedGe μ ν c, integral_gap_selectedGe μ ν hν c, ← integral_const_mul]
  linarith

end ProdGe

section GaussianGe

open ProbabilityTheory
open scoped NNReal

private theorem gaussianReal_tail_mem_Ici (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (t : ℝ) :
    0 < (gaussianReal m v).real (Ici t) ∧ (gaussianReal m v).real (Ici t) < 1 := by
  have hac : volume ≪ gaussianReal m v := gaussianReal_absolutelyContinuous' m hv
  have hIci : gaussianReal m v (Ici t) ≠ 0 := by
    intro h
    have h' := hac h
    rw [Real.volume_Ici] at h'
    exact ENNReal.top_ne_zero h'
  have hIio : gaussianReal m v (Iio t) ≠ 0 := by
    intro h
    have h' := hac h
    rw [Real.volume_Iio] at h'
    exact ENNReal.top_ne_zero h'
  have hsum : (gaussianReal m v).real (Ici t) + (gaussianReal m v).real (Iio t) = 1 := by
    rw [← compl_Ici]
    exact probReal_add_probReal_compl measurableSet_Ici
  have h1 : 0 < (gaussianReal m v).real (Ici t) :=
    ENNReal.toReal_pos hIci (measure_ne_top _ _)
  have h2 : 0 < (gaussianReal m v).real (Iio t) :=
    ENNReal.toReal_pos hIio (measure_ne_top _ _)
  exact ⟨h1, by linarith⟩

/-- **Print's Gaussian instance at print's setup inequality.** With the noise
normal at nonzero variance, selecting `M ≥ c` strictly inflates the expected gap
over its mean `m`, for every goal law and every threshold. -/
public theorem gap_selectionGe_gaussianReal_gt (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) (c : ℝ) :
    m * (μ.prod (gaussianReal m v)).real (selectedGe c)
      < ∫ p in selectedGe c, gap p ∂(μ.prod (gaussianReal m v)) := by
  have hν : Integrable (fun x : ℝ => x) (gaussianReal m v) :=
    (memLp_id_gaussianReal 1).integrable (by norm_num)
  have h := gap_selectionGe_gt μ (gaussianReal m v) hν c (A := Set.univ)
    (by simp) (fun g _ => gaussianReal_tail_mem_Ici m hv (c - g))
  rwa [integral_id_gaussianReal] at h

end GaussianGe

end AISafetyAtlas.Goodhart
