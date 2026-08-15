module

public import AISafetyAtlas.Computability
public import AISafetyAtlas.Compositional
public import AISafetyAtlas.Explainability
public import AISafetyAtlas.Learning
public import AISafetyAtlas.Knowledge
public import AISafetyAtlas.Inference
public import AISafetyAtlas.Knowledge.Embedded
public import AISafetyAtlas.Knowledge.Embedded.Composition
public import AISafetyAtlas.Knowledge.Embedded.Finite
public import AISafetyAtlas.Knowledge.Temporal
public import AISafetyAtlas.Knowledge.Ambiguity
public import AISafetyAtlas.Knowledge.SelfReference
public import AISafetyAtlas.Knowledge.Accumulation
public import AISafetyAtlas.Knowledge.Devices
public import AISafetyAtlas.Knowledge.Check
public import AISafetyAtlas.Logic
public import AISafetyAtlas.Oversight.JointObservation
public import AISafetyAtlas.Preference
public import AISafetyAtlas.Preference.Complexity
public import AISafetyAtlas.Preference.Reasonable
public import AISafetyAtlas.Preference.SourceComplexity
public import AISafetyAtlas.Preference.Override
public import AISafetyAtlas.Preference.Regret
public import AISafetyAtlas.SelfAwareness
public import AISafetyAtlas.SocialChoice
public import AISafetyAtlas.SocialChoice.Utility
public import AISafetyAtlas.Verification
public import AISafetyAtlas.Verification.AgentBehavior
public import AISafetyAtlas.Verification.Robot
public import AISafetyAtlas.Wireheading

/-!
# AI Safety Formalization Atlas

Root import surface. Modules here compile without `sorry` and distinguish
mathematical results from AI-safety bridge claims.

## Import contracts

One import does not mean the same thing under every parent. Three patterns:

| Pattern | What one import supplies | Parents |
|---|---|---|
| Aggregating facade | the domain's whole public surface | `Compositional`, `Oversight.JointObservation`, `Wireheading` |
| Partial aggregate | the mathematical base, without the bridge modules | `Verification` |
| Kernel and specializations | a closed surface; each specialization is imported on its own | `Knowledge`, `Preference` |

`Knowledge` and `Preference` withhold their specializations deliberately. A
kernel that re-exported its own specializations could no longer state what it
excludes: importing `Knowledge` yields the observation-factorization kernel and
nothing embedded, temporal, or self-referential. The root import list below is
the complete public closure and is expected to name specializations directly.

## Aggregating facades

| Import | Domain |
|---|---|
| `AISafetyAtlas.Compositional` | Hyperproperties, rectangles, networks |
| `AISafetyAtlas.Oversight.JointObservation` | Coalition evidence, coverage, collision, repair boundary |
| `AISafetyAtlas.Wireheading` | Reward channels, self-modification |

## Single-surface domains

One module carries the domain. Vendored or external proofs are re-exported where
the result is not proved here.

| Import | Domain |
|---|---|
| `AISafetyAtlas.Computability` | Rice / halting (Mathlib wrappers) |
| `AISafetyAtlas.Explainability` | Attribution impossibility |
| `AISafetyAtlas.Inference` | Wolpert inference devices: weak/strong inference, control, physical knowledge |
| `AISafetyAtlas.Learning` | Finite NFL cores |
| `AISafetyAtlas.Logic` | Incompleteness / undefinability |
| `AISafetyAtlas.SelfAwareness` | Bounded process-compositional limits on complete self-awareness |
| `AISafetyAtlas.SocialChoice` | Arrow / Gibbard–Satterthwaite |
| `AISafetyAtlas.SocialChoice.Utility` | Arrow over utility profiles |

## Partial aggregate

`Verification` re-exports `Computability` and stops there: neither bridge module
below arrives with it.

| Import | Domain |
|---|---|
| `AISafetyAtlas.Verification` | Behavioral verification core |
| `AISafetyAtlas.Verification.AgentBehavior` | Downstream consumer of `Verification.rice` |
| `AISafetyAtlas.Verification.Robot` | Verification limits for reactive robot programs |

## Kernels and specializations

Import the specialization needed; the parent does not supply it.

| Import | Domain |
|---|---|
| `AISafetyAtlas.Knowledge` | Exact knowability and observation-factorization (kernel) |
| `AISafetyAtlas.Knowledge.Embedded` | Abstract embedded-measurement and meshing limits |
| `AISafetyAtlas.Knowledge.Embedded.Composition` | Product/equivalent complement ⇒ proper inclusion and the bijective positive boundary |
| `AISafetyAtlas.Knowledge.Embedded.Finite` | Finite cardinality gap ⇒ proper inclusion (operational) |
| `AISafetyAtlas.Knowledge.Temporal` | Time-indexed knowability, collisions, delayed knowledge |
| `AISafetyAtlas.Knowledge.Ambiguity` | Finite fibre ambiguity and the counting obstruction |
| `AISafetyAtlas.Knowledge.SelfReference` | The model as a component of the state it models |
| `AISafetyAtlas.Knowledge.Accumulation` | Window ambiguity: never decreases, at most multiplies |
| `AISafetyAtlas.Knowledge.Devices` | Transports between the knowability kernel and Wolpert inference devices |
| `AISafetyAtlas.Knowledge.Check` | Executable checkers for the kernel and the transports, with agreement theorems |
| `AISafetyAtlas.Preference` | Planner/reward unidentifiability, BY-011 (kernel) |
| `AISafetyAtlas.Preference.Complexity` | Simplicity does not break the planner/reward tie |
| `AISafetyAtlas.Preference.Reasonable` | Basic operations and Proposition 7 |
| `AISafetyAtlas.Preference.SourceComplexity` | Propositions 7 and 8 in the source's own parameterization |
| `AISafetyAtlas.Preference.Override` | Overriding human reward functions |
| `AISafetyAtlas.Preference.Regret` | Half-maximal regret is not ruled out by observation |

Each module docstring lists **primary** declarations (laws / instances /
boundaries). Prefer those names over diving into `Upstream/` unless editing a
vendored proof.
-/
