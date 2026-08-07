module

public import AISafetyAtlas.Oversight.JointObservation.Architecture
public import AISafetyAtlas.Oversight.JointObservation.Coverage
public import AISafetyAtlas.Oversight.JointObservation.Portfolio
public import AISafetyAtlas.Oversight.JointObservation.FiniteDecision
public import AISafetyAtlas.Oversight.JointObservation.RepairBoundary

/-!
# Joint observation — public facade

When can a hazard be detected at all, given who is allowed to see what? Principals
hold private evidence and expose strictly coarser declared views. A candidate
observation is a computation over the private evidence of one coalition. This module
supplies the vocabulary, the coverage/collision characterization, a certified finite
checker, and the boundary separating repairs that can work from repairs that cannot.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `EvidenceArchitecture` | Principals, executions, private evidence, declared `emit` projection |
| **Model** | `CoalitionInput` | Exactly the member private fields — coalition access is a type, not a hypothesis |
| **Model** | `CandidateObservation` | A coalition, an output type, and a computation out of `CoalitionInput` |
| **Model** | `CandidateFamily` | Indexed family with heterogeneous outputs; finiteness is required only by bounded consumers |
| **Model** | `localCandidate` | One principal's declared emitted view |
| **Model** | `emittedArchitectureCandidate` | The tuple of all currently emitted views |
| **Law (C1)** | `covers_iff_no_collision` | Factorization of the hazard ⟺ no safe/hazardous collision |
| **Model** | `ExecutionEnum` | The enumeration the checker runs on -- finiteness as data |
| **Law (C2)** | `decideCoverage` | Executable check returning a coverage proof or a concrete witness |
| **Law (C2)** | `decideCoverage_covered_iff` | The checker agrees with `Covers` |
| **Boundary (C3)** | `postprocess_cannot_repair_collision` | Computation over an unchanged interface inherits every collision |
| **Law (C3)** | `covers_of_refines` | Genuine refinement never loses established coverage |
| **Scope (C4)** | `observe_truthful` | Everything is stated under the fixed truthful mechanism `M0` |
| **Model** | `privateSingletonCandidate` | One principal's *full private evidence* -- distinct from its declared view |

## Synthesis target (bounded)

`Portfolio.lean` supplies the referents the rest of the kernel lacks: indexed
`HazardFamily` and `CandidateFamily` structures, a `Portfolio` as a `Finset` of candidate
indices, per-candidate `PortfolioCovers`, `PortfolioIndistinguishable`, a derived
`portfolioCovers_implies_hazardEquivalent` theorem, `InclusionMinimalCovering`, a declared
`PortfolioCost`, and `CostOptimalCovering`. Finiteness is imposed by bounded enumeration,
not by the semantic family structures. The two orderings are kept apart deliberately —
`inclusionMinimal_of_costOptimal` gives the one implication that holds under positive costs,
and the non-implication is exhibited rather than claimed.

The checked portfolio instance uses a second architecture with three principals and eight
executions. Two observations over different overlapping coalitions cover different hazards;
a grand-coalition observation covers both. Both resulting portfolios are inclusion-minimal,
but the declared coordination-plus-disclosure cost selects the two narrow observations.

This is a **target specification**, not a synthesizer. Nothing generates candidates,
searches a design space, infers a cost function, or establishes optimality outside a
declared finite family. It makes a proposed portfolio checkable; producing one is separate.

## Explicit non-claims

- **Not** a strategic result. `M0` is a fixed idealized truthful informational
  mechanism. Incentive compatibility, equilibrium reporting, and robustness to
  deception are out of scope; `observe_truthful` marks that boundary at the point of
  use.
- **Not** a claim that joint observation is *safe*, *legal*, or *desirable*. `Covers`
  is an informational statement about what a coalition's evidence determines. Whether
  such a coalition should be formed is a governance question this file does not touch.
- **Not** a general design-space result. Candidate *generation*, search over a design
  space, cost-function inference, and certified uncovered-family results are future work.
  `Portfolio.lean` defines what a correct portfolio would be and checks one bounded
  instance; it does not find portfolios, and its cost function is declared rather than
  derived.
- **Not** an AI-system bridge. No `ai_bridge_status` graduation from this facade.
- **Not** a generalization of `AISafetyAtlas.Compositional.Rectangularity`, and not
  generalized by it. Rectangularity asks whether an admissibility *relation* decomposes
  into local product constraints; coverage asks whether a hazard *label* is constant on
  the fibres of an observation. Both implications fail: the procurement hazard
  `{(a, b) | a ∧ b} = {true} × {true}` is rectangular yet uncovered by the emitted
  interface, and two-agent agreement is non-rectangular yet covered by an observation
  reporting both coordinates. The surfaces share proof patterns — indistinguishability
  as in `Compositional.Networks.runFor_eq_of_view_eq`, bounded witnesses as in
  `Compositional.Hyperproperties.IsKSafety` — not results.

Machine-checked consumers live at
`AISafetyAtlas.Examples.Oversight.JointObservation.Procurement` and
`AISafetyAtlas.Examples.Oversight.JointObservation.Portfolio`. They are regression
examples for the interface, not part of the reusable kernel: no empirics, schemas,
harnesses, or downstream application material belongs in this repository.

No survey coverage row is claimed here; this is oversight infrastructure.
-/
