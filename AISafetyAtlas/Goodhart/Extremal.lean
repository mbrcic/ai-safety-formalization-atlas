module

public import Mathlib.Algebra.Order.Group.Indicator
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
# Extremal Goodhart: selection leaves the region where the link was observed

## What is stated

Two objects, as everywhere on this cluster: a goal the regulator intends and a
proxy standing in for it. Extremal Goodhart is the failure mode in which the
proxy-goal link is *fitted on one region and used on another*. Three theorems
say what that costs, and two more instantiate them at print's second model.

* `selected_disjoint_observed` -- if the proxy is bounded above on the region
  where the link was observed, every threshold above that bound selects only
  states outside it. This is print's "selection pressure moves the metric away
  from the region in which the relationship is most accurate", and it is the
  only place the word *extremal* does any work.
* `fits_underdetermined_off_observed` -- once selection has left that region,
  the observations do not constrain the goal there. For **any** goal fitting the
  learned relationship on the observed region, and **any** displacement `d`,
  there is a second goal that fits the same relationship equally well, agrees
  with the first on the whole observed region, and differs from it by exactly
  `d` at every selected state. This is the collapse: not that the fitted
  relationship is known to be wrong outside its region, but that nothing
  observed inside it says otherwise.
* `CollapsesOn`, `exists_collapsesOn_of_disjoint` -- print's word for the
  failure itself: the relationship misses the goal by more than its tolerance at
  every selected state. The theorem says the observations never rule that out;
  `Examples.Goodhart.Extremal.underfit_extremal_collapse` shows it happening at
  print's own underfitted polynomial, all three clauses at one instance.
* `regime_prediction_error` -- at print's regime model, the size of that error
  is not a matter of luck: extrapolating the lower regime's relationship into
  the selected region is wrong by exactly the difference of the two offsets, at
  every selected state.
* `regime_underdetermines` -- and print's own regime model realises the
  underdetermination above, with any prescribed displacement. Its witness is not
  a spike planted at one state: two regime models differing only in the upper
  offset are equal on the whole lower regime and differ by a constant on the
  whole upper one.
* `regimeGoal_eq_of_le`, `regimeGoal_eq_of_lt` -- print's equation (3), read off
  its two branches.

`selectedAt` is the selection event, `FitsOn` is agreement with the learned
relationship on the observed region, and `regimeGoal` is print's equation (3).
`SimpleModel` is print's equation (2) transcribed, with no bound on the error
term; `fitsOn_id_iff_of_simpleModel` says `FitsOn` at the identity relationship
is a bound on that error term.

## Provenance

Manheim and Garrabrant, *Categorizing Variants of Goodhart's Law*,
arXiv:1803.04585v4, section 2, both sub-variants: *Model Insufficiency*,
equation (2), and *Change in Regime*, equation (3). The paper is pinned at
`manheim-garrabrant-arxiv-v4-2018-categorizing-variants-of-goodhart-s-law.pdf`
sha256 7691af8a05ed88262d0eaebebf082f5d028979445a0cd586acc29c861a7a012a, and
both equations were read from a rendered image of page 3 rather than from
extracted text.

**This does not reproduce a printed theorem**, for the reason recorded on
`AISafetyAtlas.Goodhart.Regressional`: the paper numbers no theorem, no
proposition, no lemma and no corollary, and section 2 is four paragraphs of prose
attached to two generative specifications. What is proved here is this atlas's
sharpening of that prose, routed as atlas-original work citing the paper for the
models. See `docs/provenance/by037-by038-goodhart-campbell-plan.md`, arrow C and
the amendments under it.

**Amended 2026-09-11**, in step with that module: this opened *"this is not
coverage of that paper"*, and the paper is now graded in section 17 of
`docs/provenance/source-coverage-audit.md`, with
`LAND-GOODHART-SELECTION-001` hosting this module. The routing is unchanged; the
old wording conflated grading a source with booking an unnumbered gloss as a
printed result. Section 17 grades **equation (2) as `Partial`** for the reason
the next section here gives — as printed it names the residual and asserts
nothing, so what this module carries is `FitsOn`, the relation it is about —
and grades the extrapolation error and the underdetermination **`Beyond`**,
since print states no quantity at all.

## Where a formal reading was chosen that print did not fix

Section 2 is prose, so these are choices, not transcriptions. Each is the
narrowest reading found that leaves the statement non-vacuous.

* **`G'` is read as model error.** Print's equation (2) is `M = G(sᵢ) + G'(sᵢ)`
  and never says what `G'` is. The surrounding paragraph -- "the error is
  induced by model simplification and inaccuracy" -- is what fixes the reading
  taken here: `G'` is the discrepancy between the goal and the fitted
  relationship, small where the fit was made and unconstrained elsewhere. Print
  does not say it is small there either; `FitsOn` supplies the bound `ε`, and it
  is `ε` that makes "approximately accurate in the initial region" a hypothesis
  rather than a mood. The unbounded equation itself is `SimpleModel`, kept
  beside `FitsOn`; `simpleModel_iff` records that it holds for every `M` and
  `G` once `G'` is the residual, which is why it carries no content alone.
* **The learned relationship is a parameter, not a third object.** `FitsOn`
  carries `f : ℝ → ℝ`, print's "learned relationship between the goal and the
  metric". It is a relationship between the two objects, not a third quantity:
  the model-insufficiency reading takes `f` the identity, so that print's
  equation (2) is `|G s - M s| ≤ ε` on the observed region, and the regime
  reading takes `f = (· + x)`, which is print's equation (3) on its lower
  branch. One statement, two printed models.
* **Nothing here is probabilistic.** Print's equations (2) and (3) are
  deterministic functions of the state; the randomness in this paper is in
  section 1, which `AISafetyAtlas.Goodhart.Regressional` already carries. That
  is print's choice, not a narrowing of it.
* **The selection event is non-strict.** `selectedAt` takes the setup
  paragraph's `M(s) ≥ c`, because section 2 states no inequality of its own.
  `AISafetyAtlas.Goodhart.Regressional` takes the strict form, because its
  section 1 writes `M > c` explicitly. Neither argument depends on the choice.

## Scope against print

* **Wider on the escape.** `fits_underdetermined_off_observed` asks only that
  the selection event miss the observed region -- print's own assertion -- and
  not that the proxy be bounded there. `selected_disjoint_observed` is the
  sufficient condition, offered separately, so a reader who has a different
  reason for the escape may use the collapse theorem without it.
* **Wider on the state space.** Print writes `s ∈ S` for an unstructured set;
  the theorems here take an arbitrary type with no structure at all.
* **Narrower on the regime model, and named as such.** Print's equation (3)
  fixes the two branches as `M + x` and `M + y`. `regimeGoal` transcribes that
  literally. The general statement -- two relationships agreeing below the
  boundary and differing above it -- is `fits_underdetermined_off_observed`,
  which is what the regime model is then shown to instantiate; the constant
  offsets are print's, not a restriction this module imposes on the general
  statement.
* **What print asserts and this module does not prove.** Print says selection
  *causes* the collapse. Nothing here is causal: `selected_disjoint_observed`
  says where selection lands, and `fits_underdetermined_off_observed` says the
  observations are silent there. Read together they say the optimizer walks off
  the edge of its evidence, which is the content the taxonomy uses. A statement
  in which the act of selecting changes the relationship is Manheim and
  Garrabrant's *third* category, not this one, and it needs an interventional
  layer this module does not have.

## Reuse

Nothing was built here that Mathlib has. The two carriers are `Set.EqOn` and
`Set.indicator`, both used directly, and the arithmetic is `linarith`. There was
no search to run: the content is the arrangement of the hypotheses, not a lemma.
-/

namespace AISafetyAtlas.Goodhart.Extremal

open Set

variable {S : Type*}

/-- **The selection event.** The states whose proxy reaches the threshold. This
is print's setup paragraph, "the permissible states are defined such that
`s ∈ A` if `M(s) ≥ c`"; section 2 states no inequality of its own, so the
non-strict form is taken here. -/
@[expose] public def selectedAt (M : S → ℝ) (c : ℝ) : Set S := {s | c ≤ M s}

@[simp] public theorem mem_selectedAt {M : S → ℝ} {c : ℝ} {s : S} :
    s ∈ selectedAt M c ↔ c ≤ M s := Iff.rfl

/-- **Agreement with the learned relationship, on the region where it was
learned.** `f` is print's "learned relationship between the goal and the
metric", `R` the "initial region", and `ε` the tolerance within which print
calls it "approximately accurate" there. Print's equation (2) is the case
`f = id`, where the bound reads `|G s - M s| ≤ ε` and `ε` bounds the error term
`G'` on `R`. -/
@[expose] public def FitsOn (R : Set S) (M G : S → ℝ) (f : ℝ → ℝ) (ε : ℝ) : Prop :=
  ∀ s ∈ R, |G s - f (M s)| ≤ ε

/-- **Print's Simple Model** (Manheim and Garrabrant, §2, equation (2),
`mg-eq-2`, PDF p. 3): `M = G(sᵢ) + G'(sᵢ)`, the metric is the goal plus an error
term `G'`, which print attributes to "model simplification and inaccuracy" and
does not bound. Transcribed with no bound on `G'`, on an arbitrary state type.

As printed the equation constrains nothing: for any `M` and `G` it holds with
`G' = M − G` (`simpleModel_iff`). That is why `FitsOn`, the bounded reading of
the residual on the observed region, carries the content the theorems below use;
`fitsOn_id_iff_of_simpleModel` ties the two together. -/
@[expose] public def SimpleModel (M G G' : S → ℝ) : Prop :=
  ∀ s, M s = G s + G' s

/-- The Simple Model holds exactly when the error term is the residual `M − G`;
in particular every pair `M`, `G` has one. -/
public theorem simpleModel_iff {M G G' : S → ℝ} : SimpleModel M G G' ↔ G' = M - G := by
  constructor
  · intro h; funext s; simp only [Pi.sub_apply, h s]; ring
  · rintro rfl s; simp only [Pi.sub_apply]; ring

/-- **`FitsOn` at print's model-insufficiency relationship is a bound on print's
error term.** Under the Simple Model, fitting the identity relationship within
`ε` on `R` says exactly that `|G'| ≤ ε` on `R`. -/
public theorem fitsOn_id_iff_of_simpleModel {M G G' : S → ℝ} (h : SimpleModel M G G')
    (R : Set S) (ε : ℝ) :
    FitsOn R M G id ε ↔ ∀ s ∈ R, |G' s| ≤ ε := by
  refine forall₂_congr fun s _ => ?_
  have : G s - id (M s) = -G' s := by simp only [id, h s]; ring
  rw [this, abs_neg]

/-- **Selection leaves the region where the relationship was observed.** If the
proxy is bounded above by `b` on that region, then every threshold above `b`
selects only states outside it. This is the whole of print's "selection pressure
moves the metric away from the region in which the relationship is most
accurate", and it is what makes the failure mode *extremal* rather than merely
epistemic. -/
public theorem selected_disjoint_observed (M : S → ℝ) (R : Set S) {b c : ℝ}
    (hR : ∀ s ∈ R, M s ≤ b) (hc : b < c) :
    Disjoint (selectedAt M c) R := by
  rw [Set.disjoint_left]
  intro s hs hsR
  have h1 : c ≤ M s := hs
  have h2 : M s ≤ b := hR s hsR
  linarith

/-- **The relationship collapses because the observations were never about the
selected region.** Take any goal that fits the learned relationship on the
observed region, and any displacement `d`. There is a second goal that fits that
relationship just as well, is *equal* to the first everywhere on the observed
region -- so no observation there can tell them apart -- and differs from it by
exactly `d` at every selected state.

The hypothesis is print's own assertion that selection has left the observed
region; `selected_disjoint_observed` discharges it whenever the proxy is bounded
there. The quantifier is the point: this is not "some pair of models disagrees",
which any two functions satisfy, but "whatever the truth is, the evidence
permits it to be off by any amount you name, everywhere selection reaches". -/
public theorem fits_underdetermined_off_observed
    (M : S → ℝ) {R : Set S} (f : ℝ → ℝ) (ε : ℝ) {c : ℝ}
    (hdisj : Disjoint (selectedAt M c) R)
    (G : S → ℝ) (hG : FitsOn R M G f ε) (d : ℝ) :
    ∃ G', FitsOn R M G' f ε ∧ EqOn G G' R ∧
      ∀ s ∈ selectedAt M c, G s - G' s = d := by
  classical
  refine ⟨fun s => G s - (selectedAt M c).indicator (fun _ => d) s, ?_, ?_, ?_⟩
  · intro s hs
    have hsel : s ∉ selectedAt M c := Set.disjoint_right.mp hdisj hs
    simpa [Set.indicator_of_notMem hsel] using hG s hs
  · intro s hs
    have hsel : s ∉ selectedAt M c := Set.disjoint_right.mp hdisj hs
    simp [Set.indicator_of_notMem hsel]
  · intro s hs
    simp [Set.indicator_of_mem hs]

/-- **The relationship collapses on a region**: print's *"so that the relationship
collapses"* (§2, PDF p. 3). At every state of `A` the learned relationship `f` misses
the goal by more than the tolerance `ε` within which it was accurate where it was
learned. Stated at every state of `A`, not at one, so a collapse on the selection
event is a collapse wherever selection lands. -/
@[expose] public def CollapsesOn (A : Set S) (M G : S → ℝ) (f : ℝ → ℝ) (ε : ℝ) : Prop :=
  ∀ s ∈ A, ε < |G s - f (M s)|

/-- **The evidence cannot rule the collapse out.** Whatever goal fits the learned
relationship on the observed region, once selection has left that region there is a
goal equal to it on the whole observed region, so fitting just as well, for which the
relationship collapses at every selected state, by more than any margin `δ` named in
advance. -/
public theorem exists_collapsesOn_of_disjoint
    (M : S → ℝ) {R : Set S} (f : ℝ → ℝ) (ε : ℝ) {c : ℝ}
    (hdisj : Disjoint (selectedAt M c) R)
    (G : S → ℝ) (hG : FitsOn R M G f ε) (δ : ℝ) :
    ∃ G', FitsOn R M G' f ε ∧ EqOn G G' R ∧
      CollapsesOn (selectedAt M c) M G' f (max ε δ) := by
  classical
  refine ⟨fun s => if s ∈ selectedAt M c then f (M s) + (|max ε δ| + 1) else G s,
    ?_, ?_, ?_⟩
  · intro s hs
    have hsel : s ∉ selectedAt M c := Set.disjoint_right.mp hdisj hs
    simpa [hsel] using hG s hs
  · intro s hs
    have hsel : s ∉ selectedAt M c := Set.disjoint_right.mp hdisj hs
    simp [hsel]
  · intro s hs
    simp only [hs, if_true, add_sub_cancel_left]
    rw [abs_of_pos (by positivity)]
    linarith [le_abs_self (max ε δ)]

/-! ## Change in Regime

Print's equation (3) is a goal that is a function of the proxy with a break at a
boundary: `G = M + x` below it and `G = M + y` above it. -/

/-- **Print's equation (3).** The goal as a function of the proxy, with one
offset below the regime boundary `a` and another above it. Print writes the
lower branch's guard as `M <= a`, so the boundary itself belongs to the lower
regime. -/
@[expose] public noncomputable def regimeGoal (a x y : ℝ) (m : ℝ) : ℝ :=
  if m ≤ a then m + x else m + y

/-- Equation (3), lower branch. -/
@[simp] public theorem regimeGoal_eq_of_le (a x y : ℝ) {m : ℝ} (h : m ≤ a) :
    regimeGoal a x y m = m + x := if_pos h

/-- Equation (3), upper branch. -/
@[simp] public theorem regimeGoal_eq_of_lt (a x y : ℝ) {m : ℝ} (h : a < m) :
    regimeGoal a x y m = m + y := if_neg (not_le.mpr h)

/-- **Extrapolating the observed regime into the selected region is wrong by a
fixed amount.** A regulator who has learned the lower regime's relationship
perfectly predicts `M s + x`; the goal is `M s + y`. Above the boundary the
prediction is off by `x - y` at every selected state -- not on average, not with
high probability, and not by an amount that shrinks with more data below the
boundary. This is print's "even if the correct relationship is learned for the
observed region, in the region where the proxy takes an extreme value the
relationship to the goal may be fundamentally different". -/
public theorem regime_prediction_error (M : S → ℝ) (a x y : ℝ) {c : ℝ} (hc : a < c)
    {s : S} (hs : s ∈ selectedAt M c) :
    (M s + x) - regimeGoal a x y (M s) = x - y := by
  have h : a < M s := lt_of_lt_of_le hc hs
  rw [regimeGoal_eq_of_lt a x y h]
  ring

/-- **Print's own model realises the underdetermination.** The witness in
`fits_underdetermined_off_observed` is a displacement planted on the selection
event, which is honest but cheap. Print's equation (3) supplies a better one:
two regime models sharing the lower offset `x` and differing in the upper offset
are *equal* on the whole lower regime, fit its relationship exactly there, and
differ by a prescribed constant on the whole upper regime. Nothing observed at
or below `a` distinguishes them.

The observed region here is print's own -- the states whose proxy lies in the
lower regime -- and the fit is exact, so `ε = 0`. -/
public theorem regime_underdetermines (M : S → ℝ) (a x y : ℝ) {c : ℝ} (hc : a < c) (d : ℝ) :
    ∃ G', FitsOn {s | M s ≤ a} M G' (fun m => m + x) 0 ∧
      EqOn (fun s => regimeGoal a x y (M s)) G' {s | M s ≤ a} ∧
      ∀ s ∈ selectedAt M c, regimeGoal a x y (M s) - G' s = d := by
  refine ⟨fun s => regimeGoal a x (y - d) (M s), ?_, ?_, ?_⟩
  · intro s hs
    have h : M s ≤ a := hs
    simp only [regimeGoal_eq_of_le a x (y - d) h, sub_self, abs_zero, le_refl]
  · intro s hs
    have h : M s ≤ a := hs
    simp only [regimeGoal_eq_of_le a x y h, regimeGoal_eq_of_le a x (y - d) h]
  · intro s hs
    have h : a < M s := lt_of_lt_of_le hc hs
    simp only [regimeGoal_eq_of_lt a x y h, regimeGoal_eq_of_lt a x (y - d) h]
    ring

/-- **The regime model escapes its observed region.** The proxy is bounded above
by `a` on the lower regime by definition, so `selected_disjoint_observed` applies
at `b = a`: every threshold above the boundary selects only states print never
observed. -/
public theorem regime_selected_disjoint_observed (M : S → ℝ) (a : ℝ) {c : ℝ} (hc : a < c) :
    Disjoint (selectedAt M c) {s | M s ≤ a} :=
  selected_disjoint_observed M {s | M s ≤ a} (fun _ hs => hs) hc

end AISafetyAtlas.Goodhart.Extremal
