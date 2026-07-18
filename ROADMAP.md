<!-- generated-by: gsd-doc-writer -->
# Roadmap

The AI Safety Formalization Atlas is building a small, dependable layer of
machine-checked mathematics for research on AI safety, utility, and value
alignment. The aim is not to collect the largest number of proofs. It is to make
the most relevant results easy to find, verify, reuse, and extend without hiding
the gap between a mathematical theorem and an informal claim about AI systems.

This is a living strategic document for contributors. Current counts and
short-term tasks live in [the status report](docs/formalization-status.md) and
[project state](STATE.md); detailed research leads live in
[open work](docs/open-work.md).

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
[formalization status](docs/formalization-status.md) for the maintained figures
and [external formalizations](docs/external-formalizations.md) for reproduction
evidence.

This foundation is deliberately narrow. The next work should test whether its
interfaces support useful AI-safety statements before the atlas grows into more
domains.

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
theorem without duplicating existing decision-theory libraries.

### State one precise verification or containment limit

- Define the computational object being treated as an agent or system.
- Define a behavioral property and the verifier that is supposed to decide it.
- Derive the limitation from the canonical Rice or halting interface.
- Document exactly which practical verification claims the theorem does and
  does not address.

Success means a reusable bridge theorem, not an AI-themed alias for Rice's
theorem.

## Research workstreams

These workstreams may proceed when a concrete theorem and a maintainer are
identified:

- **AI-safety-native formalizations:** review debate and attribution
  impossibility developments at statement and build level before registry
  inclusion.
- **Unformalized high-value results:** investigate No Free Lunch and the
  survey-introduced proof sketches using primary sources; do not treat an
  unsuccessful search as proof that no formalization exists.
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

Contributions should follow [the methodology](docs/methodology.md), update the
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
