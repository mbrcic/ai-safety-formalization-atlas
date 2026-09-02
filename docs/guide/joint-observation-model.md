# Joint observation: what a coalition's evidence can decide

**Status: machine-checked.** Every Lean statement referenced here compiles with no
`sorry`, `admit`, local `axiom`, `native_decide`, or `@[implemented_by]` in its
trusted path, under Lean 4.33.0. The kernel theorems depend only on `propext`,
`Classical.choice`, and `Quot.sound`.

## The question

Oversight arrangements are usually specified as *interfaces*: each party declares
what it will disclose, and monitors are built on those declarations. That framing
silently assumes the declared interfaces contain enough information to detect the
hazards anyone cares about.

Often they do not — and the failure is not a failure of the monitor's cleverness.
When a hazard depends on how two parties' hidden states *relate*, no amount of
computation over separately declared views can see it. The information is not there
to be computed with.

This module makes that distinction precise and machine-checkable: which hazards a
given observation arrangement can decide, and what kind of change is required when it
cannot.

## The model

An `EvidenceArchitecture` has principals, executions, the **private evidence** each
principal holds (`privateState`), and the **declared view** each principal exposes
(`emit`). Keeping private evidence and emitted views as distinct types, related only
through `emit`, is what gives "the declared interface is insufficient" any content:
if the two coincided, the claim would be a restatement of the definitions.

A `CandidateObservation` is a coalition `C`, an output type, and a computation

```text
joint : (Π i ∈ C, PrivateField i) → Output
```

The coalition appears in the *type* of the input. A candidate therefore cannot read
the execution, and cannot read a principal outside its coalition — not "must not", but
*cannot*: the alternative would be a type error.

This is the one structural commitment worth stating twice. The tempting alternative is
an unrestricted function over all principals plus a `RespectsCoalition` side
condition. That version is strictly weaker in practice: the hypothesis can be
forgotten in a lemma, weakened during refactoring, or discharged in the wrong place,
and the result still compiles.

Under the fixed truthful informational mechanism `M0`, observing an execution feeds
each member's actual private field to `joint`. Here `M0` is a label for this fixed
path, not an additional mechanism datatype: in the API it is
`CandidateObservation.observe`, and `observe_truthful` makes that convention explicit.

## Coverage

A candidate **covers** a hazard when the hazard decision factors through the
candidate's output:

```lean
Covers q h ↔ ∃ decideHazard : q.Output → Bool, ∀ σ, h σ = decideHazard (q.observe σ)
```

One rule, uniform in the execution. This is deliberately *not* defined as "no
collision exists", which would reduce the central characterization below to
unfolding a definition and would leave nothing connecting an observation's
informational content to a usable decision rule.

**C1 — characterization.** `Covers q h` holds exactly when no two executions with the
same observation differ in hazard status. The forward direction is immediate; the
converse assembles a decision rule from the hazard values on each fibre of `observe`,
which is well defined precisely when no fibre mixes safe and hazardous executions.

The negative certificate is a `CollisionWitness`: a concrete pair of executions the
candidate cannot tell apart, one safe and one hazardous. It answers "why not" with a
specific pair rather than a failed proof attempt.

**C2 — certified finite decision.** For finitely many executions and decidable output
equality, `decideCoverage` is an executable check returning either a coverage proof or
a concrete witness. Both branches carry their evidence, so a consumer never has to
trust the checker; `decideCoverage_covered_iff` connects it back to `Covers` through
C1. The trusted path uses no `native_decide` and no `@[implemented_by]`.

## The repair boundary

**C3, part 1.** Post-processing inherits every collision of the observation it
post-processes. Applied to the candidate that reports the tuple of *all* currently
emitted views, this upgrades "the declared interface fails" to "**arbitrary
computation over** the complete declared interface fails".

**C3, part 2.** Refinement — an observation that determines the old one — preserves
coverage already established.

Read together:

> More computation over unchanged interfaces cannot recover missing information.
> Repair must refine evidence access, admit an appropriate joint predicate, enlarge
> the coalition, or otherwise change the observation architecture — and doing so
> cannot destroy coverage that already held.

Neither half is deep alone. The first is nearly a computation, and it is not
advertised as more than that. The value is the architectural conclusion they license
jointly, and that downstream consumers can cite them instead of re-deriving them.

## A minimal instance

`AISafetyAtlas.Examples.Oversight.JointObservation.Procurement` instantiates the API
on four executions and two principals: a data owner who knows whether the training
dataset is access restricted, and a model owner who knows whether the checkpoint is.
Neither restriction is hazardous alone; the conjunction is, because it leaves the
deployed system externally unauditable.

The asymmetry in the declared interface is what makes the example worth checking.
Dataset restriction *is* disclosed — the data owner's emitted view is its actual
bit — so the interface carries real information and rules out most potential
collisions. Checkpoint access policy is not disclosed: the checkpoint bit exists
privately throughout, but never appears in the declared interface.

The example keeps two failures apart, because they say different things. A *local*
candidate sees only what its principal declares, so its failure is partly about the
interface being lossy. A *private singleton* candidate sees its principal's full
private evidence, so its failure is about the hazard being relational — no single
party can see it, however much of its own evidence it is granted. Without that
distinction a reader could conclude that the positive joint result recovers
information the architecture says is absent. It does not: a permitted coalition
computation uses the checkpoint bit without publishing it.

The example machine-checks that:

* no local monitor covers the hazard;
* neither principal covers it alone even with unrestricted access to its own private
  evidence, with witnesses `(sigma10, sigma11)` for the data owner and
  `(sigma01, sigma11)` for the model owner;
* the complete emitted interface still fails, with witness `(sigma10, sigma11)`, and
  hence so does any computation over it;
* one narrowly permitted joint predicate over coalition-indexed private evidence
  covers the hazard on all four executions.

## Relation to `AISafetyAtlas.Compositional`

Both surfaces study local/global factorization, but they factor different things, and
**neither subsumes the other**.

`Compositional.Rectangularity` asks whether a global admissibility *relation*
decomposes into local product constraints — whether membership has the form
`P x ∧ Q y`. Joint observation asks whether a hazard *label* factors through an
available observation — whether it is constant on the fibres of `observe`. These are
orthogonal questions, and each direction of implication fails:

- A rectangular hazard relation need not be covered. The procurement hazard is
  `{(a, b) | a ∧ b} = {true} × {true}` — rectangular — yet the complete emitted
  interface does not cover it, and neither singleton does.
- A non-rectangular relation can be covered. Two-agent agreement is not a rectangle
  (`Compositional.LocalContractBoundary.not_isRectangle_agreement`), but it is covered
  by any observation that reports both coordinates.

What the modules genuinely share are *proof patterns*, not theorems:

- **Indistinguishability.** `Compositional.Networks.runFor_eq_of_view_eq` — nodes with
  equal views are in equal states — and `no_unique_leader_of_fixedPointFree` run the
  same argument that `covers_iff_no_collision` runs: identical observations force
  identical outputs, so nothing that differs across an indistinguishable pair can be
  decided.
- **Bounded witnesses.** `Compositional.Hyperproperties.IsKSafety` at `k = 2` and
  `CollisionWitness` are both finite violation certificates, though they certify
  different things — a hyperproperty violation versus a coverage failure.

Nothing in this paragraph is machine-checked. A later bridge would formalize the two
non-implications above; that is future work, deliberately out of scope here.

## Proved / not proved

This section describes what compiles at this commit.

### Proved

- Coverage factorizes through a candidate observation exactly when no safe/hazardous
  execution pair shares that candidate's output — `covers_iff_no_collision`.
- A finite checker over an explicit complete execution enumeration returns either
  coverage evidence or a concrete collision witness — `decideCoverage`, specified by
  `decideCoverage_covered_iff`.
- Post-processing an unchanged observation cannot remove an existing collision —
  `postprocess_cannot_repair_collision`.
- Coverage is preserved under genuine observation refinement — `covers_of_refines`.
- In the four-state reference architecture:
  - neither principal covers the hazard alone, **even with unrestricted access to its
    own private evidence**, with witnesses `(sigma10, sigma11)` and
    `(sigma01, sigma11)`;
  - the family of local monitors built on declared views is blind — `localFamily_blind`;
  - the complete existing emitted interface fails, with witness `(sigma10, sigma11)`,
    and therefore so does arbitrary computation over it;
  - the restricted two-principal joint predicate covers the hazard.
- The checker *reduces* on that instance: both `decideCoverage` results are proved by
  `decide`, not merely typechecked.
- No `sorry`, `admit`, project-local `axiom`, `sorryAx`, `native_decide`, or
  `@[implemented_by]` anywhere in the trusted path. Kernel theorems depend only on
  `propext`, `Classical.choice`, and `Quot.sound`.

### Proved — bounded synthesis target

Added after the informational kernel, so that the model's central nouns have formal
referents:

- `HazardFamily`, `Portfolio` (a `Finset` of candidate indices), and `PortfolioCovers`
  with the `∀ hazard, ∃ selected candidate` shape a portfolio actually needs;
- `PortfolioIndistinguishable` and
  `portfolioCovers_implies_hazardEquivalent` — if every selected candidate agrees on two
  executions, every covered hazard agrees too. This is derived from per-candidate coverage;
  no converse or free fusion of individually insufficient outputs is claimed;
- `InclusionMinimalCovering` and `CostOptimalCovering`, kept apart deliberately;
- `inclusionMinimal_of_costOptimal` — under strictly positive costs, cost-optimality
  implies inclusion-minimality. The converse is **false**, and is refuted by instance
  rather than asserted;
- a checked second architecture with three principals, eight executions, and two hazards
  (`a ∧ b`, `b ⊕ c`). Candidate `qCD` reads coalition `{C,D}`, `qDE` reads `{D,E}`, and
  `qCDE` reads `{C,D,E}`. The narrow portfolio `{qCD,qDE}` (declared cost 6) and broad
  singleton `{qCDE}` (declared cost 7) both cover and are both inclusion-minimal, while
  only the narrow portfolio is cost-optimal.

That last fact is the point: **inclusion-minimality alone does not determine a preferred
cover**, so a synthesis target stated only in those terms is underspecified.

This is a **target specification**, not a synthesizer. It says what a correct portfolio
would be and checks one; it does not find one. See the next section for what that
excludes.

### Not proved

- **Strategic truthfulness or incentive compatibility.** The instance fixes an
  idealized truthful informational mechanism `M0`.
- **Robustness to deceptive reporting.**
- **Candidate generation or search.** No predicate templates, no enumeration of a
  candidate space, no solver. Every candidate and every cost is supplied by hand.
- **Minimality or optimality outside a declared finite family.** Both are defined and
  checked *relative to* an explicitly listed candidate family and an explicitly declared
  cost function. Nothing establishes optimality over candidates nobody wrote down, and
  the cost function is stipulated rather than derived or validated.
- **Certified uncovered-family results.** Nothing returns the set of hazards no
  admissible candidate can cover.
- **Architecture-level generality.** The portfolio result exercises one additional bounded
  architecture; two hand-built examples do not establish broad generality.
- **Dynamic or recursive delegation.**
- **Empirical generalization** beyond the reference architecture.
- **Statistical detection guarantees.**
- **Anything normative.** `Covers` says a coalition's evidence *determines* the hazard.
  Whether such a coalition should exist, and under what governance, is a separate
  question.
- **No AI-system bridge.** No `ai_bridge_status` graduation follows from these results.

## The probabilistic version, and why this one is exact

The most likely reason a consumer bounces off this surface is that their hazard is a
rate, not a predicate — "is this behaviour deceptive" rather than "are both fields
restricted". That generalization is real and is not a refactor. What it would take, and
what breaks:

- `Execution` needs a measure. Nothing in `EvidenceArchitecture` carries one, and the
  six fields are deliberately measure-free; a probabilistic layer adds structure rather
  than replacing any of them.
- `Covers` becomes graded: some `decideHazard` agreeing with the hazard on all but
  `ε` of the mass, rather than everywhere. Exact coverage is the `ε = 0` case.
- **`covers_iff_no_collision` stops being an equivalence.** A single safe/hazardous pair
  sharing an output currently refutes coverage outright. Under a measure, a null pair
  refutes nothing, so the right-hand side must become a bound on collision *mass*. The
  characterization survives only as an inequality, and `CollisionWitness` stops being a
  sufficient refutation.
- The repair boundary survives in spirit — post-processing cannot create information —
  but `postprocess_cannot_repair_collision` would be reproved through a data-processing
  argument rather than by transporting a witness.
- Portfolio selection changes class. Graded coverage turns an exact set-cover target
  into budgeted maximum coverage, so `PortfolioCovers` and `CostOptimalCovering` are
  no longer the right shapes.

Exact was chosen first for two reasons, neither of them convenience. The `ε = 0` case has
to be stated before an approximation to it can be, and the exact negative result is
strictly stronger where it holds: "no permitted computation over this coalition decides
this hazard" is a worst-case impossibility that no probabilistic relaxation strengthens.
More importantly, a collision witness is a **certificate** — a finite object a reader
checks — while probabilistic failure is an estimate. Certificates compose across a
portfolio; estimates need their error budget tracked through every composition, which is
a different engineering problem and should not be smuggled in under the same name.
