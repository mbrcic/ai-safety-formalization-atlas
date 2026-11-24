import AISafetyAtlas.Goodhart.Regressional

/-!
# Manheim and Garrabrant's consequences of Regressional Goodhart, read universally, are false

David Manheim and Scott Garrabrant, *Categorizing Variants of Goodhart's Law*,
arXiv:1803.04585v4 (24 Feb 2019), §1, p. 2 (PDF p. 2; audit row S17-R04), the
paragraph after the Simple Model `M = G + normal(μ, σ²)` (eq. (1)):

    Due to the noise, a point with a large M value will likely have a large G
    value, but also a large noise value. Thus, when M is large, you can expect G
    to be predictably smaller than M. Despite the lack of bias, for large values
    of c the values of G when M > c is expected to be higher than otherwise.
    While this is the simplest Goodhart effect, it is also the most fundamental:
    it cannot be avoided. No matter what measure is chosen for optimization, an
    inexact metric necessarily leads to a divergence between the goal and the
    metric in the tail.

with footnote 2 (same page): "In general, a mapping from s → ℝ is a measaure, and if
used for decision-making, it is known as a metric." (Transcribed from the page image
in `docs/provenance/printed-statements/manheim-2018-goodhart-variants.yaml`, entries
`mg-regressional-consequence`, `mg-eq-1` and `mg-fn2-metric`.) The paper states no
independence of `G` and the noise and no non-degeneracy of `G` (the yaml's
`source.standing`).

Two of the paragraph's claims are refuted as printed, and the accepted repair of
each is proved (ruling 2026-11-21, row 091):

* **(3), the last sentence**, read universally as footnote 2 licenses: every inexact
  metric `M` diverges from `G` in the tail. Refuted at `M = G + 1_{G<0}` with `G`
  standard normal (`not_literalTail`). Repaired: a claim about the Simple Model of
  eq. (1), proxy = goal + independent normal noise, where the library's
  `gap_selection_gaussianReal_gt` proves it at every threshold.
* **(2), "for large values of c the values of G when M > c is expected to be higher
  than otherwise"**, read for every goal. Refuted at a constant goal
  (`not_literalHigher`), where both conditional means are the constant. Repaired: a
  goal law that is not a point mass, where the library's
  `goal_selected_compl_gaussianReal_lt` proves it at every threshold.

**Vocabulary.** The library's (`AISafetyAtlas.Goodhart`): states are pairs
(goal value, gap value) on `ℝ × ℝ`, `proxy = goal + gap`, `selected c = {proxy > c}`
(print's `M > c` in this paragraph). Print's arbitrary system (states `S`, goal
`G`, metric `M`) maps onto it along `s ↦ (G s, M s − G s)` (library `goalGap_comp`),
so an arbitrary probability law `P` on `ℝ × ℝ` is print's universal reading of (3),
with no coupling between the goal and the gap. Print's Simple Model is the product
law `μ.prod (gaussianReal m v)`, independence included.

**Readings fixed before refuting.**

* "Divergence between the goal and the metric in the tail" is read as the previous
  sentence's "when M is large, you can expect G to be predictably smaller than M":
  the expected gap `M − G` on `{M > c}` strictly exceeds its unconditional mean, in
  the library's product form `E[M − G] · P(M > c) < E[M − G ; M > c]`
  (`DivergesInTail`). This is the reading the repair is proved at. The same witness
  also refutes the weakest reading, that `M ≠ G` on a non-null part of the tail
  (`not_literalTailWeak`): for `c ≥ 1` the set `{M > c, M ≠ G}` is null
  (`witness_no_tail_divergence`), while
  the tail itself is not (`witness_tail_mass`), so the refutation is not the
  vacuous one of an empty tail.
* "Higher than otherwise" is `E[G | M ≤ c] < E[G | M > c]`, cross-multiplied so that
  nothing divides by a mass (`HigherThanOtherwise`, the form of the library's
  `goal_selected_compl_lt`).
* "For large values of c" and "in the tail" are read as `∃ᶠ c in atTop`
  (arbitrarily large thresholds), the weakest of the readings; refuting it refutes
  the "eventually" and "every c" readings. Both repairs are proved at every `c`,
  which implies all three.
* The literal (2) keeps the noise normal at nonzero variance (`v ≠ 0`, the library's
  standing presupposition that variance zero is no noise) and the goal integrable
  (print's `E[G]`). It is therefore weaker than print's sentence over all of eq.
  (1), so its refutation is the stronger one, and the only thing the witness
  breaks is goal degeneracy.
* The literal (3) asks of `P` only that it be a probability law, that the gap be
  integrable (so `E[M − G]` exists) and that the metric be inexact,
  `P {M ≠ G} ≠ 0`.

**Why the repairs are the necessary ones.**

* (2): the witness is every point mass (`not_higher_dirac`, at every `a`, `m`, `v`,
  `c`), and the repaired statement holds at every other integrable goal law. So
  among integrable goals at Gaussian noise, the strict inequality holds at every
  threshold exactly when the goal is not a point mass
  (`higher_everywhere_iff_not_point_mass`): the added hypothesis is necessary and
  sufficient.
* (3): the witness's error `1_{G<0}` is a function of the goal, so some restriction
  on how the error relates to the goal is necessary. The repair restricts to print's
  own eq. (1) with the error independent of `G` (independence is not printed; the
  yaml's note on `mg-eq-1`) and at nonzero variance. At variance zero eq. (1) is the
  deterministic shift `M = G + μ`, inexact when `μ ≠ 0`, with constant gap and so no
  strict divergence (`zero_variance_no_divergence`); so `v ≠ 0`, the library's
  standing presupposition recorded in its module note, is necessary at the reading
  of `DivergesInTail`. Weaker sufficient
  conditions than independence (some positive-association condition, say) are not
  ruled out, so minimality among couplings is not claimed.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/manheim-garrabrant-regressional-literal.lean`.
Grading context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired
slips); final grade: id 091 in
`docs/provenance/regrade-2026-11/final-grades.tsv`.
-/

open MeasureTheory Set Filter ProbabilityTheory AISafetyAtlas.Goodhart
open scoped NNReal

namespace ManheimGarrabrantRegressionalLiteral

/-! ## The readings -/

/-- **Divergence in the tail at threshold `c`** (print, PDF p. 2: "when M is large,
you can expect G to be predictably smaller than M"): the expected gap `M − G` on the
selected states `{M > c}` strictly exceeds its unconditional mean, in product form. -/
def DivergesInTail (P : Measure (ℝ × ℝ)) (c : ℝ) : Prop :=
  (∫ p, gap p ∂P) * P.real (selected c) < ∫ p in selected c, gap p ∂P

/-- **"Higher than otherwise" at threshold `c`** (print, PDF p. 2: "the values of G
when M > c is expected to be higher than otherwise"): `E[G | M ≤ c] < E[G | M > c]`,
cross-multiplied. -/
def HigherThanOtherwise (P : Measure (ℝ × ℝ)) (c : ℝ) : Prop :=
  (∫ p in (selected c)ᶜ, goal p ∂P) * P.real (selected c)
    < (∫ p in selected c, goal p ∂P) * P.real (selected c)ᶜ

/-- **Print's (3), universally** (PDF p. 2: "No matter what measure is chosen for
optimization, an inexact metric necessarily leads to a divergence between the goal
and the metric in the tail"; footnote 2: any mapping `s → ℝ` used for decisions is a
metric): for every law of (goal, gap) with an integrable gap and an inexact metric,
the metric diverges from the goal at arbitrarily large thresholds. -/
def LiteralTail : Prop :=
  ∀ (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P], Integrable gap P →
    P {p | gap p ≠ 0} ≠ 0 → ∃ᶠ c in atTop, DivergesInTail P c

/-- **Print's (2), for every goal** (PDF p. 2: "for large values of c the values of G
when M > c is expected to be higher than otherwise"), at eq. (1)'s Simple Model
`M = G + normal(m, v)` with independent noise at nonzero variance, at arbitrarily
large thresholds. -/
def LiteralHigher : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable (fun x : ℝ => x) μ →
    ∀ (m : ℝ) (v : ℝ≥0), v ≠ 0 →
      ∃ᶠ c in atTop, HigherThanOtherwise (μ.prod (gaussianReal m v)) c

/-- The two printed claims as read above. -/
def LiteralPrint : Prop := LiteralTail ∧ LiteralHigher

/-! ## The witness against (3): `M = G + 1_{G<0}`, `G` standard normal -/

/-- A state of the witness: goal value `g`, gap `1` when `g < 0` and `0` otherwise,
so the metric is `M = G + 1_{G<0}`. -/
noncomputable def shift (g : ℝ) : ℝ × ℝ := (g, if g < 0 then 1 else 0)

theorem measurable_shift : Measurable shift :=
  measurable_id.prodMk (Measurable.ite measurableSet_Iio measurable_const measurable_const)

theorem measurable_gap : Measurable gap := measurable_snd

theorem measurableSet_gap_ne : MeasurableSet {p : ℝ × ℝ | gap p ≠ 0} :=
  (measurableSet_eq_fun measurable_gap measurable_const).compl

/-- The witness law: the image of a standard normal goal under `shift`. The error
`M − G = 1_{G<0}` is a function of the goal, not independent of it. -/
noncomputable def witnessLaw : Measure (ℝ × ℝ) := (gaussianReal 0 1).map shift

instance : IsProbabilityMeasure witnessLaw :=
  Measure.isProbabilityMeasure_map measurable_shift.aemeasurable

theorem gap_comp_shift : gap ∘ shift = (Iio (0:ℝ)).indicator 1 := by
  funext g; simp [shift, gap, Set.indicator_apply]

theorem integrable_gap_witness : Integrable gap witnessLaw := by
  rw [witnessLaw, integrable_map_measure measurable_gap.aestronglyMeasurable
    measurable_shift.aemeasurable, gap_comp_shift]
  exact (integrable_const 1).indicator measurableSet_Iio

/-- **The witness metric is inexact**: `M ≠ G` exactly when `G < 0`, which has
probability `1/2`, in particular not zero. -/
theorem witness_inexact : witnessLaw {p | gap p ≠ 0} ≠ 0 := by
  rw [witnessLaw, Measure.map_apply measurable_shift measurableSet_gap_ne]
  have : shift ⁻¹' {p | gap p ≠ 0} = Iio 0 := by
    ext g; simp [shift, gap]
  rw [this]
  intro h
  have h' := gaussianReal_absolutelyContinuous' 0 one_ne_zero h
  rw [Real.volume_Iio] at h'
  exact ENNReal.top_ne_zero h'

/-- **The tail is never empty**: every threshold is exceeded with positive
probability, since `M ≥ G` and `G` is normal. -/
theorem witness_tail_mass (c : ℝ) : 0 < witnessLaw.real (selected c) := by
  refine ENNReal.toReal_pos ?_ (measure_ne_top _ _)
  rw [witnessLaw, Measure.map_apply measurable_shift (measurableSet_selected c)]
  intro h
  have hsub : Ioi c ⊆ shift ⁻¹' selected c := by
    intro g hg
    simp only [mem_Ioi] at hg
    simp only [mem_preimage, selected, proxy, shift, mem_ofPred_eq]
    split_ifs <;> linarith
  have h' := gaussianReal_absolutelyContinuous' 0 one_ne_zero (measure_mono_null hsub h)
  rw [Real.volume_Ioi] at h'
  exact ENNReal.top_ne_zero h'

/-- **No divergence in the tail, on the weakest reading**: for `c ≥ 1` the metric
equals the goal almost surely on `{M > c}`, since `M ≠ G` forces `M = G + 1 < 1`. -/
theorem witness_no_tail_divergence {c : ℝ} (hc : 1 ≤ c) :
    witnessLaw (selected c ∩ {p | gap p ≠ 0}) = 0 := by
  rw [witnessLaw, Measure.map_apply measurable_shift
    ((measurableSet_selected c).inter measurableSet_gap_ne)]
  have : shift ⁻¹' (selected c ∩ {p | gap p ≠ 0}) = ∅ := by
    ext g
    simp only [mem_preimage, mem_inter_iff, selected, proxy, shift, gap, mem_ofPred_eq,
      mem_empty_iff_false, iff_false, not_and]
    split_ifs with h
    · intro h1; linarith
    · simp
  rw [this, measure_empty]

/-- The gap carried by the tail is zero for `c ≥ 1`. -/
theorem witness_tail_gap_zero {c : ℝ} (hc : 1 ≤ c) :
    ∫ p in selected c, gap p ∂witnessLaw = 0 := by
  rw [witnessLaw, setIntegral_map (measurableSet_selected c)
    measurable_gap.aestronglyMeasurable measurable_shift.aemeasurable]
  refine setIntegral_eq_zero_of_forall_eq_zero fun g hg => ?_
  simp only [mem_preimage, selected, proxy, shift, mem_ofPred_eq] at hg
  simp only [shift, gap]
  split_ifs at hg ⊢ with h
  · linarith
  · rfl

/-- The unconditional mean gap is nonnegative (it is `1/2`; not computed here). -/
theorem witness_mean_gap_nonneg : 0 ≤ ∫ p, gap p ∂witnessLaw := by
  rw [witnessLaw, integral_map measurable_shift.aemeasurable
    measurable_gap.aestronglyMeasurable]
  exact integral_nonneg fun g => by simp only [shift, gap]; split_ifs <;> norm_num

/-- **The witness does not diverge in the tail**, on the reading of
`DivergesInTail`, at any `c ≥ 1`: the right-hand side is `0` and the left-hand side
is nonnegative. -/
theorem witness_not_diverges {c : ℝ} (hc : 1 ≤ c) : ¬ DivergesInTail witnessLaw c := by
  intro h
  unfold DivergesInTail at h
  rw [witness_tail_gap_zero hc] at h
  exact absurd h (not_lt.mpr (mul_nonneg witness_mean_gap_nonneg measureReal_nonneg))

/-- **(3), read universally, is false.** `M = G + 1_{G<0}` with `G` standard normal
is an inexact metric with integrable error, and from threshold `1` on it never
diverges from the goal in the tail. -/
theorem not_literalTail : ¬ LiteralTail := by
  intro h
  obtain ⟨c, hdiv, hc⟩ :=
    ((h witnessLaw integrable_gap_witness witness_inexact).and_eventually
      (eventually_ge_atTop 1)).exists
  exact witness_not_diverges hc hdiv

/-- **Divergence in the tail, weakest reading**: the metric differs from the goal on
a non-null part of `{M > c}`. -/
def DivergesInTailWeak (P : Measure (ℝ × ℝ)) (c : ℝ) : Prop :=
  P (selected c ∩ {p | gap p ≠ 0}) ≠ 0

/-- Print's (3), universally, at the weakest reading of "divergence". -/
def LiteralTailWeak : Prop :=
  ∀ (P : Measure (ℝ × ℝ)) [IsProbabilityMeasure P], Integrable gap P →
    P {p | gap p ≠ 0} ≠ 0 → ∃ᶠ c in atTop, DivergesInTailWeak P c

/-- **(3) is false at the weakest reading too**, at the same witness: from threshold
`1` on, the metric equals the goal almost surely on the (non-null,
`witness_tail_mass`) tail. -/
theorem not_literalTailWeak : ¬ LiteralTailWeak := by
  intro h
  obtain ⟨c, hdiv, hc⟩ :=
    ((h witnessLaw integrable_gap_witness witness_inexact).and_eventually
      (eventually_ge_atTop 1)).exists
  exact hdiv (witness_no_tail_divergence hc)

/-! ## The witness against (2): a constant goal -/

/-- At a goal that is a point mass at `a`, the goal is `a` almost surely. -/
theorem goal_ae_dirac (a m : ℝ) (v : ℝ≥0) :
    ∀ᵐ p ∂((Measure.dirac a).prod (gaussianReal m v)), goal p = a :=
  (Measure.quasiMeasurePreserving_fst).ae ((ae_eq_dirac (fun x : ℝ => x)).mono fun _ hx => hx)

/-- **At a constant goal, "higher than otherwise" fails at every threshold**: both
conditional means are the constant `a`, so the two sides are equal. -/
theorem not_higher_dirac (a m : ℝ) (v : ℝ≥0) (c : ℝ) :
    ¬ HigherThanOtherwise ((Measure.dirac a).prod (gaussianReal m v)) c := by
  have hS : ∀ s : Set (ℝ × ℝ), ∫ p in s, goal p ∂((Measure.dirac a).prod (gaussianReal m v))
      = ((Measure.dirac a).prod (gaussianReal m v)).real s * a := by
    intro s
    rw [integral_congr_ae (g := fun _ => a) (ae_restrict_of_ae (goal_ae_dirac a m v)),
      setIntegral_const, smul_eq_mul]
  unfold HigherThanOtherwise
  rw [hS, hS]
  intro h
  linarith [h, show ((Measure.dirac a).prod (gaussianReal m v)).real (selected c) * a *
    ((Measure.dirac a).prod (gaussianReal m v)).real (selected c)ᶜ =
    ((Measure.dirac a).prod (gaussianReal m v)).real (selected c)ᶜ * a *
    ((Measure.dirac a).prod (gaussianReal m v)).real (selected c) by ring]

/-- **(2), read for every goal, is false**, at the constant goal `0` and standard
normal noise: no threshold, large or not, makes `G` higher on `{M > c}`. -/
theorem not_literalHigher : ¬ LiteralHigher := by
  intro h
  obtain ⟨c, hc⟩ := (h (Measure.dirac 0) (integrable_dirac (by finiteness)) 0 1
    one_ne_zero).exists
  exact not_higher_dirac 0 0 1 c hc

/-- **Both printed claims, as read, are false**, each at its own witness. -/
theorem literal_false : ¬ LiteralTail ∧ ¬ LiteralHigher :=
  ⟨not_literalTail, not_literalHigher⟩

theorem not_literalPrint : ¬ LiteralPrint := fun h => not_literalTail h.1

/-! ## The repairs -/

/-- **Repaired (3)**: (3) as a claim about eq. (1)'s Simple Model, the goal law `μ`
arbitrary and the noise normal at nonzero variance and independent of the goal (the
product law). Divergence then holds at every threshold, hence in every reading of
"in the tail". -/
def RepairedTail : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ) (v : ℝ≥0), v ≠ 0 →
    ∀ c, DivergesInTail (μ.prod (gaussianReal m v)) c

/-- **Repaired (2)**: `LiteralHigher` with one hypothesis added, the goal law is not
a point mass; it then holds at every threshold. -/
def RepairedHigher : Prop :=
  ∀ (μ : Measure ℝ) [IsProbabilityMeasure μ], Integrable (fun x : ℝ => x) μ →
    (∀ a : ℝ, μ ≠ Measure.dirac a) → ∀ (m : ℝ) (v : ℝ≥0), v ≠ 0 →
      ∀ c, HigherThanOtherwise (μ.prod (gaussianReal m v)) c

/-- The mean gap of the Simple Model is the noise mean `m`. -/
theorem integral_gap_prod_gaussianReal (μ : Measure ℝ) [IsProbabilityMeasure μ] (m : ℝ)
    (v : ℝ≥0) : ∫ p, gap p ∂(μ.prod (gaussianReal m v)) = m := by
  have := integral_fun_snd (μ := μ) (ν := gaussianReal m v) (fun x : ℝ => x)
  simp only [probReal_univ, one_smul, integral_id_gaussianReal] at this
  exact this

/-- **Nonzero variance is needed in repaired (3).** At variance zero eq. (1) is the
deterministic shift `M = G + m`: for `m ≠ 0` the metric is inexact with integrable
error, yet the gap is the constant `m`, so it never diverges in the tail on the
reading of `DivergesInTail`, at any goal law and any threshold. -/
theorem zero_variance_no_divergence (μ : Measure ℝ) [IsProbabilityMeasure μ] {m : ℝ}
    (hm : m ≠ 0) :
    Integrable gap (μ.prod (gaussianReal m 0)) ∧
      (μ.prod (gaussianReal m 0)) {p | gap p ≠ 0} ≠ 0 ∧
      ∀ c, ¬ DivergesInTail (μ.prod (gaussianReal m 0)) c := by
  rw [gaussianReal_zero_var]
  refine ⟨(integrable_dirac (by finiteness) : Integrable (fun x : ℝ => x) _).comp_snd μ,
    ?_, fun c => ?_⟩
  · have hs : MeasurableSet {x : ℝ | x ≠ 0} := (measurableSet_singleton 0).compl
    have : {p : ℝ × ℝ | gap p ≠ 0} = Prod.fst ⁻¹' Set.univ ∩ Prod.snd ⁻¹' {x : ℝ | x ≠ 0} := by
      ext p; simp [gap]
    rw [this, ← Set.prod_eq, Measure.prod_prod, Measure.dirac_apply' _ hs]
    simp [hm]
  · have hae : ∀ᵐ p ∂(μ.prod (Measure.dirac m)), gap p = m :=
      (Measure.quasiMeasurePreserving_snd).ae
        ((ae_eq_dirac (fun x : ℝ => x)).mono fun _ hx => hx)
    unfold DivergesInTail
    rw [integral_congr_ae (g := fun _ => m) hae,
      integral_congr_ae (g := fun _ => m) (ae_restrict_of_ae hae), integral_const,
      setIntegral_const, probReal_univ, smul_eq_mul, smul_eq_mul, one_mul, mul_comm]
    exact lt_irrefl _

/-- **Both repaired claims hold**, as the library proves them:
`gap_selection_gaussianReal_gt` for (3) and `goal_selected_compl_gaussianReal_lt`
for (2). -/
theorem repaired_holds : RepairedTail ∧ RepairedHigher := by
  refine ⟨fun μ _ m v hv c => ?_, fun μ _ hμ hdeg m v hv c =>
    goal_selected_compl_gaussianReal_lt μ hμ hdeg m hv c⟩
  unfold DivergesInTail
  rw [integral_gap_prod_gaussianReal]
  exact gap_selection_gaussianReal_gt μ m hv c

/-- **The added hypothesis of (2) is exactly the right one**: for an integrable goal
at Gaussian noise of nonzero variance, "higher than otherwise" holds at every
threshold if and only if the goal law is not a point mass. -/
theorem higher_everywhere_iff_not_point_mass (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable (fun x : ℝ => x) μ) (m : ℝ) {v : ℝ≥0} (hv : v ≠ 0) :
    (∀ c, HigherThanOtherwise (μ.prod (gaussianReal m v)) c) ↔
      ∀ a : ℝ, μ ≠ Measure.dirac a := by
  refine ⟨fun h a ha => ?_, fun hdeg c => repaired_holds.2 μ hμ hdeg m v hv c⟩
  subst ha
  exact not_higher_dirac a m v 0 (h 0)

end ManheimGarrabrantRegressionalLiteral
