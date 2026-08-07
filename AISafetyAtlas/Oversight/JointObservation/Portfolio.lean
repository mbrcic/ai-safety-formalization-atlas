module

public import AISafetyAtlas.Oversight.JointObservation.Coverage
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Portfolios: covering a hazard family, and choosing between covers

The rest of the kernel answers a question about **one** candidate and **one** hazard:
does this observation determine that hazard? That is the obstruction this surface
characterizes, and it is not the object a synthesis procedure would compute.

This module supplies the missing referents. A hazard family is an indexed collection of
hazards; a portfolio is a selected finite set of candidate indices; a portfolio covers the family
when every hazard has some selected candidate covering it. Two orderings on covers are
then defined and are deliberately kept apart:

* **inclusion-minimality** — no proper subportfolio still covers;
* **cost-optimality** — no covering portfolio has lower declared cost.

They are not the same, and conflating them is a modelling error rather than a
simplification. A single broad observation can be inclusion-minimal while two narrow
predicates are cheaper, because breadth is exactly what a cost function is there to
penalise: the broad observation reveals more. `Examples.Oversight.JointObservation.Portfolio`
exhibits that case concretely, with two inclusion-minimal covers of different cost.

## What this is not

This is a **target specification**, not a synthesizer. Nothing here generates candidates,
searches a design space, infers a cost function, or establishes optimality outside a
declared finite family. What it does is make a synthesis procedure's output type
checkable: given a proposed portfolio, these definitions say what it would mean for it to
be right, and the example shows the definitions have the intended content.

The cost function is a *declared* objective. `PortfolioCost` sums it over the selection.
That privacy loss, disclosure burden, latency, audit cost, and concentration risk admit
a common scalar unit is an assumption of the instance, not a theorem — and where multiple
objectives resist scalarization, the honest output is a Pareto frontier rather than a
minimum.

Everything remains under the truthful mechanism `M0`: `Covers` is informational, so a
covering portfolio says what *would* suffice if the evidence were produced. Whether it is
produced is the separate question `observe_truthful` marks the boundary of.
-/

namespace AISafetyAtlas.Oversight.JointObservation

universe u v w t

variable {A : EvidenceArchitecture.{u, v}}

/-! ## Hazard families -/

/--
An indexed family of hazards.

Indexed rather than a `Finset (Hazard A)`: hazards are functions, so a `Finset` would
demand `DecidableEq (A.Execution → Bool)`, which is exactly the kind of incidental
requirement `CandidateFamily` avoids for the same reason.

Deliberately carries **no** `Fintype Index`. `PortfolioCovers` is `∀ j : H.Index, …`,
which needs no finiteness, and an unread instance field is generality that looks present
without being exercised — the same defect `CandidateFamily.instFintype` had, which this
structure originally reproduced. A future result that genuinely quantifies over the family
(a certified "no portfolio covers this hazard family") should add the constraint where it
is used, not carry it unread here.
-/
public structure HazardFamily (A : EvidenceArchitecture.{u, v}) where
  /-- Index of the family. -/
  Index : Type t
  /-- The indexed hazards. -/
  hazard : Index → Hazard A

/-! ## Portfolios -/

/--
A **portfolio**: a selection of candidates from a declared family.

A `Finset` of *indices*, never of candidates. Candidate structures contain functions, so
a `Finset (CandidateObservation A)` would require deciding equality of functions. Indexing
sidesteps that entirely and is why `CandidateFamily` was built this way.
-/
public abbrev Portfolio (F : CandidateFamily.{u, v, t, w} A) : Type _ :=
  Finset F.Index

/--
The portfolio covers the hazard family: every hazard is covered by some selected
candidate.

Note the quantifier shape — `∀ hazard, ∃ selected candidate`. Each hazard may be covered
by a *different* member, which is the entire point of a portfolio. Demanding one candidate
that covers everything would be a strictly stronger and usually unsatisfiable condition.
-/
@[expose] public def PortfolioCovers
    (F : CandidateFamily.{u, v, t, w} A)
    (H : HazardFamily.{u, v, t} A)
    (K : Portfolio F) : Prop :=
  ∀ j : H.Index, ∃ i ∈ K, Covers (F.candidate i) (H.hazard j)

/--
Two executions are indistinguishable under a portfolio when every selected candidate
produces the same output on both executions.

This is stated pointwise over the indexed family so candidate output types may remain
heterogeneous. It does not package the outputs into an unmodelled fusion tuple.
-/
@[expose] public def PortfolioIndistinguishable
    (F : CandidateFamily.{u, v, t, w} A)
    (K : Portfolio F)
    (x y : A.Execution) : Prop :=
  ∀ i, i ∈ K → (F.candidate i).observe x = (F.candidate i).observe y

/--
Per-candidate portfolio coverage entails hazard-equivalence of the selected outputs.

For each hazard, `PortfolioCovers` supplies one explicit selected candidate and one
uniform decision rule through which that hazard factors. Agreement on every selected
candidate therefore forces agreement on every hazard. The converse is intentionally not
claimed: collectively fusing individually insufficient outputs requires an explicit
candidate describing the recipient, permitted computation, and production mechanism.
-/
public theorem portfolioCovers_implies_hazardEquivalent
    {F : CandidateFamily.{u, v, t, w} A}
    {H : HazardFamily.{u, v, t} A}
    {K : Portfolio F}
    {x y : A.Execution}
    (hCover : PortfolioCovers F H K)
    (hSame : PortfolioIndistinguishable F K x y) :
    ∀ j : H.Index, H.hazard j x = H.hazard j y := by
  intro j
  obtain ⟨i, hi, decideHazard, hdecide⟩ := hCover j
  calc
    H.hazard j x = decideHazard ((F.candidate i).observe x) := hdecide x
    _ = decideHazard ((F.candidate i).observe y) := congrArg decideHazard (hSame i hi)
    _ = H.hazard j y := (hdecide y).symm

/--
**Inclusion-minimality**: covering, and no proper subportfolio covers.

This is the ordering most readers assume when they hear "minimal", and on its own it does
not determine a preferred portfolio — there can be several inclusion-minimal covers, of
very different quality.
-/
@[expose] public def InclusionMinimalCovering
    (F : CandidateFamily.{u, v, t, w} A)
    (H : HazardFamily.{u, v, t} A)
    (K : Portfolio F) : Prop :=
  PortfolioCovers F H K ∧ ∀ K' : Portfolio F, K' ⊂ K → ¬ PortfolioCovers F H K'

/--
The declared cost of a portfolio: the sum of its members' declared costs.

Additive by declaration. Real objectives need not be — shared infrastructure makes costs
sub-additive, and concentration risk makes them super-additive — so this is a property of
the declared instance, not a claim about observation cost in general.
-/
@[expose] public def PortfolioCost
    (F : CandidateFamily.{u, v, t, w} A)
    (cost : F.Index → Nat)
    (K : Portfolio F) : Nat :=
  ∑ i ∈ K, cost i

/--
**Cost-optimality**: covering, and no covering portfolio costs less.

Quantifies over *every* portfolio of the declared family, not merely over the
inclusion-minimal ones — a cheaper cover that happens not to be inclusion-minimal would
still refute optimality, and excluding it would make the definition weaker than its name.

Relative to the declared family and the declared cost throughout. It says nothing about
candidates nobody wrote down.
-/
@[expose] public def CostOptimalCovering
    (F : CandidateFamily.{u, v, t, w} A)
    (H : HazardFamily.{u, v, t} A)
    (cost : F.Index → Nat)
    (K : Portfolio F) : Prop :=
  PortfolioCovers F H K ∧
    ∀ K' : Portfolio F,
      PortfolioCovers F H K' → PortfolioCost F cost K ≤ PortfolioCost F cost K'

/-! ## The two orderings are genuinely different -/

/--
Cost-optimality does not imply inclusion-minimality, and inclusion-minimality does not
imply cost-optimality. Neither direction is provable in general, so neither is stated
here; the separation is exhibited by the example instance instead, which is the honest
way to establish a non-implication.

What *is* provable is the one direction that holds: a cost-optimal cover cannot contain a
strictly cheaper covering subportfolio, because that subportfolio would refute optimality.
With strictly positive costs this yields inclusion-minimality.
-/
public theorem inclusionMinimal_of_costOptimal
    {F : CandidateFamily.{u, v, t, w} A}
    {H : HazardFamily.{u, v, t} A}
    {cost : F.Index → Nat}
    {K : Portfolio F}
    (hpos : ∀ i, 0 < cost i)
    (hopt : CostOptimalCovering F H cost K) :
    InclusionMinimalCovering F H K := by
  classical
  refine ⟨hopt.1, fun K' hsub hcov => ?_⟩
  -- `K'` is a strictly smaller cover, so it omits some member of `K`, and every cost is
  -- positive; its total is therefore strictly less than `K`'s, contradicting optimality.
  obtain ⟨i, hiK, hiK'⟩ := Finset.exists_of_ssubset hsub
  have hsum : PortfolioCost F cost K' ≤ ∑ x ∈ K.erase i, cost x :=
    Finset.sum_le_sum_of_subset (fun x hx =>
      Finset.mem_erase.mpr ⟨fun h => hiK' (h ▸ hx), hsub.1 hx⟩)
  have hadd : cost i + ∑ x ∈ K.erase i, cost x = ∑ x ∈ K, cost x :=
    Finset.add_sum_erase K cost hiK
  have hi := hpos i
  have hle := hopt.2 K' hcov
  -- `hle` and `hsum` are about `PortfolioCost`, which is the sum by definition; unfolding
  -- lets `omega` see both as the same atom.
  simp only [PortfolioCost] at hle hsum
  omega

end AISafetyAtlas.Oversight.JointObservation
