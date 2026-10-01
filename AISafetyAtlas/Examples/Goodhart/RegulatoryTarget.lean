module

public import AISafetyAtlas.Goodhart.RegulatoryTarget

/-!
# A bar set one unit above everything anyone measured

`AISafetyAtlas.Goodhart.RegulatoryTarget` states both halves conditionally, and
its structural hypothesis — the bar sits above the evidence base — has to be
inhabited or the whole module says nothing. This module inhabits it at the
smallest honest scheme.

## The setting

A system is a real number, and the indicator is that number: the model commits
to nothing about what is being measured. The link between indicator and risk was
established on systems scoring at most `1`, and the rule certifies systems
scoring at least `2`.

On the evidence base the link is **exact** — `ε = 0`, risk equals the indicator
— which is the strongest case for the indicator and is deliberately chosen.
Nothing below comes from a sloppy fit.

* `scheme_risk_bounded_on_evidence_base` — on the studied systems the indicator
  gives risk exactly.
* `scheme_certified_were_never_examined` — and no certified system was studied.
  `(3 : ℝ)` is certified and outside the evidence base, concretely.
* `scheme_risk_unconstrained_on_certified` — at every certified system the
  evidence permits the risk to be off by any amount named, with a second risk
  function that fits the same link exactly and agrees everywhere it was checked.
* `scheme_raising_the_bar_does_not_help` — at a bar of `100` as much as at `2`.

The gap is not a measurement error and not a modelling shortcut. The fit is
perfect where it was taken, and that is the point.
-/

namespace AISafetyAtlas.Examples.Goodhart.RegulatoryTarget

open Set
open AISafetyAtlas.Goodhart.Extremal
open AISafetyAtlas.Goodhart.RegulatoryTarget

/-- A system is its own score; the model says nothing about what is measured. -/
public abbrev ToySystem := ℝ

/-- The rule: the link was established at or below `1`, and certification
requires `2`. -/
@[expose] public def scheme : RegulatoryScheme ToySystem where
  indicator := id
  evidenceBase := {s | s ≤ 1}
  observedCeiling := 1
  threshold := 2
  indicator_le_observedCeiling := fun _ hs => hs
  observedCeiling_lt_threshold := by norm_num

/-- The established link: risk is the indicator itself. -/
@[expose] public def toyLink : ℝ → ℝ := id

/-- The true risk, on the reading the evidence supports. -/
@[expose] public def toyRisk : ToySystem → ℝ := id

/-- **The fit is exact on the evidence base.** `ε = 0`: this is the best case for
the indicator, not a strained one. -/
public theorem scheme_fits_exactly :
    FitsOn scheme.evidenceBase scheme.indicator toyRisk toyLink 0 := by
  intro s _
  simp [toyRisk, toyLink, scheme]

/-- **So the indicator predicts risk exactly, where it was checked.** -/
public theorem scheme_risk_bounded_on_evidence_base {s : ToySystem}
    (hs : s ∈ scheme.evidenceBase) :
    |toyRisk s - toyLink (scheme.indicator s)| ≤ 0 :=
  risk_bounded_on_evidence_base scheme scheme_fits_exactly hs

/-! ## And nowhere it certifies -/

/-- The certified systems and the studied ones do not meet. -/
public theorem scheme_certified_disjoint_evidenceBase :
    Disjoint (certified scheme) scheme.evidenceBase :=
  certified_disjoint_evidenceBase scheme

/-- A concrete certified system, to show the set is not empty. -/
public theorem scheme_three_is_certified : (3 : ToySystem) ∈ certified scheme :=
  (mem_certified scheme).mpr (by show (2 : ℝ) ≤ id (3 : ℝ); norm_num)

/-- **And it was never examined.** -/
public theorem scheme_certified_were_never_examined :
    (3 : ToySystem) ∉ scheme.evidenceBase :=
  certified_systems_were_never_examined scheme scheme_three_is_certified

/-- **The evidence permits any displacement at every certified system**, while
still fitting the link exactly on everything that was checked. -/
public theorem scheme_risk_unconstrained_on_certified (d : ℝ) :
    ∃ risk', FitsOn scheme.evidenceBase scheme.indicator risk' toyLink 0 ∧
      EqOn toyRisk risk' scheme.evidenceBase ∧
      ∀ s ∈ certified scheme, toyRisk s - risk' s = d :=
  risk_unconstrained_on_certified scheme toyLink 0 toyRisk scheme_fits_exactly d

/-! ## Tightening -/

/-- **Demanding a score of `100` does not close the gap** — it widens the
distance from the evidence. -/
public theorem scheme_raising_the_bar_does_not_help :
    Disjoint (selectedAt scheme.indicator 100) scheme.evidenceBase :=
  raising_the_bar_does_not_help scheme (by show (2 : ℝ) ≤ 100; norm_num)

/-- And the underdetermination is there too, at the higher bar. -/
public theorem scheme_risk_unconstrained_at_the_higher_bar (d : ℝ) :
    ∃ risk', FitsOn scheme.evidenceBase scheme.indicator risk' toyLink 0 ∧
      EqOn toyRisk risk' scheme.evidenceBase ∧
      ∀ s ∈ selectedAt scheme.indicator 100, toyRisk s - risk' s = d :=
  risk_unconstrained_at_every_higher_bar scheme (by show (2 : ℝ) ≤ 100; norm_num)
    toyLink 0 toyRisk
    scheme_fits_exactly d

/-- **Open Problem 92's second half at a witness.** The indicator is exact where
it was measured and the certification is unconstrained where it is used, at the
same scheme and with the same fit. -/
public theorem scheme_informative_and_certification_unconstrained (d : ℝ) :
    (∀ s ∈ scheme.evidenceBase, |toyRisk s - toyLink (scheme.indicator s)| ≤ 0) ∧
      ∃ risk', FitsOn scheme.evidenceBase scheme.indicator risk' toyLink 0 ∧
        EqOn toyRisk risk' scheme.evidenceBase ∧
        ∀ s ∈ certified scheme, toyRisk s - risk' s = d :=
  indicator_informative_and_certification_unconstrained scheme toyLink 0 toyRisk
    scheme_fits_exactly d

end AISafetyAtlas.Examples.Goodhart.RegulatoryTarget
