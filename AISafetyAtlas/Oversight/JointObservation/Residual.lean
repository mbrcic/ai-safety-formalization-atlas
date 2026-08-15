module

public import AISafetyAtlas.Oversight.JointObservation.RepairBoundary
public import AISafetyAtlas.Knowledge.Ambiguity

/-!
# Joint observation — residual, the quantitative face of coverage

`Covers` is a yes/no test. On a finite execution space it has a distribution-free
refinement: count how many executions an observation still cannot tell apart.

## What this adds, and what it does not

`Covers q h` is definitionally `Knowledge.Knowable q.observe h`, so
[`Ambiguity`](../../Knowledge/Ambiguity.lean) applies to oversight verbatim. This
module fixes the oversight-facing names and states the two facts a consumer needs:
coverage is the residual-at-most-one case, and post-processing never lowers the
residual.

The second is the repair boundary as a **comparable number**.
`postprocess_cannot_repair_collision` says a failed decode stays failed;
`worstResidual_le_postprocess` says by how much, and that it never improves.

## Why the target is not always the hazard

`residual` is stated for an arbitrary target `Ω → Y`, not only for a `Hazard`.
That is the point of the quantity: two portfolios can agree on every declared
hazard and still differ on how much they leave open about the execution itself,
which is exactly what a later hazard, or an attribution question, would need. The
declared hazard family is what coverage sees; the residual is what it misses.

## Explicit non-claims

**No probability anywhere.** `residual` counts executions, it does not weigh them.
There is no measure, no prior, no expectation, and no entropy. A residual of `n`
says `n` executions remain consistent with the reports — it says nothing about how
likely any of them is, and it is therefore a worst-case quantity rather than an
average one.

**Not accountability.** A residual of `1` means every property of the execution is
fixed by the observation, so every *state* attribution question is answerable. It
says nothing about whether a principal reported honestly: everything here is under
the truthful mechanism `M0` (see `observe_truthful`), where misreporting cannot be
expressed at all. Detecting a dishonest reporter needs a strategic reporting layer
that this module does not have and does not approximate.

No survey coverage row is claimed here; this is landscape infrastructure.
-/

namespace AISafetyAtlas.Oversight.JointObservation

open AISafetyAtlas.Knowledge

universe u v w w'

variable {A : EvidenceArchitecture.{u, v}}

/-! ## Residual -/

/--
The **residual** at one observed output: how many target values are still
consistent with reading `o`.

`1` is exact knowledge, `0` is an output nothing realizes, and anything larger is
the shortfall.
-/
@[expose] public def residual [Fintype A.Execution] [DecidableEq Y]
    (q : CandidateObservation.{u, v, w} A) [DecidableEq q.Output]
    (target : A.Execution → Y) (o : q.Output) : ℕ :=
  ambiguity q.observe target o

/--
The **worst-case residual** of a candidate observation against a target: the
largest number of target values any single output leaves open.

One scalar per candidate, which is what ranking two candidates requires.
-/
@[expose] public def worstResidual [Fintype A.Execution] [DecidableEq Y]
    (q : CandidateObservation.{u, v, w} A) [DecidableEq q.Output]
    (target : A.Execution → Y) : ℕ :=
  worstAmbiguity q.observe target

/-! ## Coverage is the residual-at-most-one case -/

/--
**Coverage, quantitatively.** A candidate covers a hazard exactly when its
worst-case residual against that hazard is at most one.

This is the honest distribution-free statement of "coverage is the zero case of a
quantity". It needs no measure, no support hypothesis, and no entropy.
-/
public theorem covers_iff_worstResidual_le_one
    [Fintype A.Execution]
    (q : CandidateObservation.{u, v, w} A) [DecidableEq q.Output]
    (h : Hazard A) :
    Covers q h ↔ worstResidual q h ≤ 1 :=
  knowable_iff_worstAmbiguity_le_one q.observe h

/-- The per-output form, for a consumer that wants the offending output. -/
public theorem covers_iff_residual_le_one
    [Fintype A.Execution]
    (q : CandidateObservation.{u, v, w} A) [DecidableEq q.Output]
    (h : Hazard A) :
    Covers q h ↔ ∀ o, residual q h o ≤ 1 :=
  knowable_iff_ambiguity_le_one q.observe h

/-! ## The repair boundary, as a number -/

/--
A post-processed candidate reports in `β`, so it inherits `β`'s decidable
equality. Stated as an instance because the `Output` field is definitionally `β`
but not syntactically, which instance search alone will not see through.
-/
public instance decidableEqPostprocessOutput
    {q : CandidateObservation.{u, v, w} A} {β : Type w'} [DecidableEq β]
    {g : q.Output → β} : DecidableEq (q.postprocess g).Output :=
  inferInstanceAs (DecidableEq β)

/--
**Post-processing never lowers the residual.**

The quantitative companion of `postprocess_cannot_repair_collision`: applying any
further computation to an unchanged observation can only merge outputs, so the
worst case moves up, never down. Repair must refine evidence — and this says by
how much refusing to do so costs.
-/
public theorem worstResidual_le_postprocess
    [Fintype A.Execution] [DecidableEq Y]
    (q : CandidateObservation.{u, v, w} A) [DecidableEq q.Output]
    (target : A.Execution → Y)
    {β : Type w'} [DecidableEq β] (g : q.Output → β) :
    worstResidual q target ≤ worstResidual (q.postprocess g) target := by
  show worstAmbiguity q.observe target ≤ worstAmbiguity (q.postprocess g).observe target
  have hobs : (q.postprocess g).observe = fun σ => g (q.observe σ) :=
    funext (observe_postprocess q g)
  simp only [hobs]
  exact worstAmbiguity_le_of_comp q.observe target g

end AISafetyAtlas.Oversight.JointObservation
