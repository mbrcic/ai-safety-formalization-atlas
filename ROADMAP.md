<!-- generated-by: gsd-doc-writer -->
# Roadmap

The AI Safety Formalization Atlas is building a small, dependable layer of
machine-checked mathematics for research on AI safety, utility, and value
alignment. The aim is not to collect the largest number of proofs. It is to make
the most relevant results easy to find, verify, reuse, and extend without hiding
the gap between a mathematical theorem and an informal claim about AI systems.

This is a living strategic document for contributors. Current counts and
short-term tasks live in [the status report](docs/status/formalization-status.md) and
[project state](STATE.md); the full 44-row landscape is browsable in the
generated [atlas index](docs/status/atlas-index.md); detailed research leads live in
[open work](docs/guide/open-work.md) and bounded, ready-to-take units in
[contributor tasks](docs/guide/contributor-tasks.md).

## What we are building

The atlas has three connected layers:

1. A verified registry mapping surveyed impossibility results to primary
   sources and formal-library declarations.
2. A parsimonious Lean API exposing canonical results under stable,
   conventional theorem names.
3. Explicit bridge theorems connecting classical mathematics to precisely
   defined models of agents, utilities, verification, or alignment.

The third layer is where much of the prospective AI-safety research value lies.
A bridge must state its model and assumptions explicitly; renaming a classical
object as an "agent" is not enough.

## Principles

- **Reuse before reproving.** Prefer a maintained declaration or a small
  attributed integration over a new proof of a known result.
- **One canonical public result.** Alternative proofs remain provenance unless
  they add a stronger statement, a needed representation, constructive content,
  a composable reduction, or necessary dependency independence.
- **Familiar names, stable interfaces.** Use established theorem names and
  expose small atlas-facing façades so downstream users need not know the source
  repository layout.
- **Evidence before coverage claims.** Verify the primary source, immutable
  revision, declaration, license, and build where practical.
- **Separate theorem from interpretation.** Machine checking validates the
  encoded statement, not the adequacy of an informal AI-safety interpretation.
- **Expand only when structure is reusable.** New dependencies, domains, and
  abstractions must support a precise theorem or unblock downstream proofs.

## Current foundation

The initial survey inventory and cross-framework discovery pass are complete.
The repository has verified external evidence and compiling Lean interfaces for
computability limits, the halting problem, Arrow's theorem, and a utility
representation of Arrow's theorem. See
[formalization status](docs/status/formalization-status.md) for the maintained figures
and [external formalizations](docs/provenance/external-formalizations.md) for reproduction
evidence.

The squashed v0.1 foundation is published on `main`. Further work is
developed off `main` and proposed as a small reviewed delta rather than by
replaying the private pre-squash history.

## Near-term work

### Harden the public foundation

- Review the statement intent and naming of the computability, social-choice,
  and utility interfaces.
- Keep the public API small while making the documented entry points sufficient
  for downstream proofs.
- Keep evidence classifications and public scope under maintainer review as
  coverage changes.

Success means a contributor can use the canonical results without learning
their upstream repository layouts or encountering multiple competing atlas
versions of the same theorem.

Development checkpoint: implemented on the local `agent-work` branch. A
root-import compile contract exercises every documented entry point without
exposing upstream declaration layouts. No competing theorem aliases were added.

### Build utility and value-alignment foundations

- Re-verify the reported Lean development of von Neumann–Morgenstern expected
  utility before choosing new utility vocabulary.
- Identify the smallest reusable interfaces for preferences, utility
  representation, aggregation, and value comparison.
- Formalize representation bridges only when they enable a concrete downstream
  result.
- Seek precise limitations or trade-offs relevant to preference aggregation and
  value alignment, with interpretation reviewed separately from the proof.

Success means the utility API supports at least one substantive downstream
theorem — a distinct result that imports and reuses the public utility
vocabulary — without duplicating existing decision-theory libraries.

Development checkpoint: partially implemented on the local `agent-work` branch.
What is done is a completed utility-facing social-choice bridge: the utility
Arrow theorem represents finite total preorders by lower-contour cardinalities.
Its representation machinery is private to `Utility.lean` and consumed there to
prove that module's own public Arrow bridge; no separate theorem or module yet
imports the public utility vocabulary for an independent result. The broader
success criterion — a reusable utility foundation with a distinct downstream
consumer, and any value-comparison or value-alignment result — therefore remains
open, not met. The vNM existence and uniqueness development was reproduced at an
immutable revision, but remains provenance rather than a dependency because the
atlas has no current theorem requiring lottery infrastructure. A larger utility
dependency will not be added merely to satisfy the wording.

### State one precise verification or containment limit

- Define the computational object being treated as an agent or system.
- Define a behavioral property and the verifier that is supposed to decide it.
- Derive the limitation from the canonical Rice or halting interface.
- Document exactly which practical verification claims the theorem does and
  does not address.

Success means a reusable bridge theorem, not an AI-themed alias for Rice's
theorem.

Development checkpoint: implemented on the local `agent-work` branch as two
independent bridges over the computability facade.
`AISafetyAtlas.Verification.rice` maps properties of partial input/output
behavior to Mathlib program codes. A downstream consumer,
`AISafetyAtlas.Verification.AgentBehavior.no_behavioral_safety_verifier`, models
encoded agents and total `BehavioralSafetyVerifier`s and reduces through `rice`
(CT-4). Separately,
`AISafetyAtlas.Verification.Robot.action_safety_unverifiable` reduces directly
to `AISafetyAtlas.Computability.halting_problem`; forcing it through the Rice
interface would obscure the paper's switching construction rather than provide
reuse. The robot theorem models total reactive action traces and makes that
construction explicit. It is a machine-checked conditional computability core for
van Leeuwen and Wiedermann's Theorem 1, not a formalization of its complete
robotics language or an ethical interpretation. The scope and external robotics
precedents are recorded in `docs/guide/robot-verification-model.md`. Bridge
review status (v0.2): BY-012 AgentBehavior and BY-033 robot are maintainer
**`REVIEWED`** (robot formalization relationship remains **`RELATED`**; CT-3
evidence at `docs/bridges/ct3-robot-review-package.md`). Finite-state and
otherwise bounded systems, sound incomplete methods, and real-system claims
beyond the scoped interpretation packages remain outside the automatic
conclusion. Live status: [`STATE.md`](STATE.md) and
[`docs/status/formalization-status.md`](docs/status/formalization-status.md).

Post-v0.1 / v0.2 implementation checkpoint: near-term outcomes compile on
`agent-work`. Current-state validation is independent of the immutable v0.1
audit. Publication of **0.2.0** is described in
[`docs/releases/v0.2.md`](docs/releases/v0.2.md) and still requires maintainer
authorization to merge to `main`.

Structural-integrity checkpoint: the post-v0.1 external reviews' immediate
findings are resolved locally. Ordinary CI checks timeless invariants rather
than historical release counts. A single target manifest and import-closure
validator ensure every Lean source is built; strict-trust scanning is
self-tested; generated reporting separates `EXACT`/`EQUIVALENT` coverage from
`RELATED` bridges; and same-repository evidence uses revision-relative
`IN_TREE` provenance. Broader search infrastructure and a website remain
deferred until a reviewed downstream bridge demonstrates demand.

## Research workstreams

These workstreams may proceed when a concrete theorem and a maintainer are
identified:

- **AI-safety-native formalizations:** doubly-efficient debate is reproduced
  into the landscape (`LAND-DEBATE-001`, Path A build at upstream v4.8);
  attribution impossibility is in-atlas (`LAND-ATTR-001`). Remaining: an in-tree
  import surface for debate (Path B port-then-wrap) only when a downstream
  consumer needs it, and debate follow-ups with no existing proof (CT-9).
- **Unformalized high-value results:** investigate No Free Lunch and the
  survey-introduced proof sketches using primary sources; do not treat an
  unsuccessful search as proof that no formalization exists. The sharp
  both-directions NFL characterization (closed-under-permutation priors,
  Schumacher–Vose–Whitley 2001 / Igel–Toussaint 2004) is scoped as optional
  reproduction rung **CT-10** — the general boundary subsuming the uniform-prior
  cores; pull only when a downstream bridge needs "which priors kill learning."
- **Decision theory and reflection:** develop foundations only when they unblock
  a named result, such as a cooperation or decision-theoretic theorem.
- **Multi-agent and value aggregation:** extend the social-choice layer where it
  gives a precise model of aggregation or alignment rather than a parallel
  vocabulary.

Causality, corrigibility, reward tampering, formal decision theories, and broad
solver infrastructure remain later work unless a small addition clearly
unlocks a priority theorem.

## How to contribute

Contributions need not begin with a new Lean proof. Useful entry points include:

- **Source verification:** match one registry result to an exact formal
  declaration, immutable revision, and license.
- **Reproducibility:** independently build an external formalization and record
  the exact environment and theorem checked.
- **API review:** test whether a public atlas theorem is discoverable and usable
  from a downstream Lean file.
- **Bridge design:** propose a formal model, theorem statement, and dependency
  path before implementing an AI-safety bridge.
- **Lean implementation:** fill an approved gap or representation bridge without
  duplicating the canonical result.
- **Domain review:** check whether a formal statement supports the interpretation
  claimed for utility, value alignment, verification, or another AI-safety
  topic.

Before substantial implementation, open an issue or draft pull request that
answers:

1. What exact theorem or evidence gap does this address?
2. What existing formalizations were checked?
3. What unique capability does the proposed addition provide?
4. Which public interface will downstream proofs use?
5. Which interpretation claims require domain review?

Contributions should follow [the methodology](docs/guide/methodology.md), update the
registry when coverage claims change, and leave the repository building without
incomplete proofs.

## How priorities are chosen

Work is prioritized by:

1. relevance to a precise AI-safety, utility, or value-alignment question;
2. reusable mathematical or representational structure;
3. absence of an adequate maintained formalization;
4. clarity of the theorem-to-interpretation boundary;
5. maintenance cost and dependency footprint.

A second proof of a known result is therefore usually lower priority than a
small bridge that makes the canonical proof usable in a new, well-defined
setting.

## What is not a default goal

- Porting every related Coq, Isabelle/HOL, or Lean proof into this repository.
- Counting multiple proofs of one result as additional survey coverage.
- Adding a dependency because it might become useful later.
- Publishing speculative AI interpretations as consequences of a formal proof.
- Building broad infrastructure before a concrete theorem needs it.

The roadmap will change as verified results, contributor capacity, and concrete
research questions change. The parsimony and evidence standards should remain
stable even when priorities move.
