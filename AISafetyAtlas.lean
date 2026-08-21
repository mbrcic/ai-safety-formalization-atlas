module

public import AISafetyAtlas.Computability
public import AISafetyAtlas.Combinatorics.PermInvariance
public import AISafetyAtlas.Compositional
public import AISafetyAtlas.Control
public import AISafetyAtlas.Explainability
public import AISafetyAtlas.Learning
public import AISafetyAtlas.Learning.Sharp
public import AISafetyAtlas.Knowledge
public import AISafetyAtlas.Inference
public import AISafetyAtlas.InformationTheory.ChannelCapacity
public import AISafetyAtlas.InformationTheory.DataProcessing
public import AISafetyAtlas.InformationTheory.Determinism
public import AISafetyAtlas.InformationTheory.Fano
public import AISafetyAtlas.Knowledge.Embedded
public import AISafetyAtlas.Knowledge.Embedded.Composition
public import AISafetyAtlas.Knowledge.Embedded.Finite
public import AISafetyAtlas.Knowledge.Temporal
public import AISafetyAtlas.Knowledge.Ambiguity
public import AISafetyAtlas.Knowledge.SelfReference
public import AISafetyAtlas.Knowledge.Accumulation
public import AISafetyAtlas.Knowledge.Devices
public import AISafetyAtlas.Knowledge.Entropy
public import AISafetyAtlas.Knowledge.Check
public import AISafetyAtlas.Logic
public import AISafetyAtlas.Oversight.JointObservation
public import AISafetyAtlas.Oversight.VarietyBound
public import AISafetyAtlas.Oversight.VarietyCheck
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

One import does not mean the same thing under every parent. Four patterns:

| Pattern | What one import supplies | Parents |
|---|---|---|
| Aggregating facade | the domain's whole public surface | `Compositional`, `Control`, `Oversight.JointObservation`, `Wireheading` |
| Partial aggregate | the mathematical base, without the bridge modules | `Verification` |
| Kernel and specializations | a closed surface; each specialization is imported on its own | `Knowledge`, `Preference` |
| Peer modules | one result each, no aggregating parent | `InformationTheory` |

`Knowledge` and `Preference` withhold their specializations deliberately. A
kernel that re-exported its own specializations could no longer state what it
excludes: importing `Knowledge` yields the observation-factorization kernel and
nothing embedded, temporal, or self-referential. The root import list below is
the public closure and is expected to name specializations directly.

**One published facade is deliberately outside it.**
`AISafetyAtlas.Oversight.Debate` wraps a vendored development that declares
roughly 157 names in the *root* namespace, so it is imported on its own and
audited through `OFF_ROOT_FACADES` in `scripts/check_print_axioms.py` rather
than through this closure; its module docstring gives the reason.

## Aggregating facades

| Import | Domain |
|---|---|
| `AISafetyAtlas.Compositional` | Hyperproperties, rectangles, networks |
| `AISafetyAtlas.Control` | Ashby's variety bounds and Touchette–Lloyd's information limits, in nine modules |
| `AISafetyAtlas.Oversight.JointObservation` | Coalition evidence, coverage, collision, repair boundary |
| `AISafetyAtlas.Wireheading` | Reward channels, self-modification |

`Oversight.JointObservation` aggregates the evidence surface and stops there:
`AISafetyAtlas.Oversight.VarietyBound` is a **bridge** module and does not arrive
with it, the same contract `Verification` keeps with its two bridges below.

### What `Control` aggregates

Nine modules, each one printed development. `AISafetyAtlas.Control` carries all
of them; import one directly when only its result is wanted.

| Import | Domain |
|---|---|
| `AISafetyAtlas.Control.RequisiteVariety` | Ashby's law: counting, logarithmic and entropy forms, and the sensor bound |
| `AISafetyAtlas.Control.ChannelRate` | Ashby §9/12 and §9/15: channel capacity as an entropy rate, and the entropy of a length of Markov chain |
| `AISafetyAtlas.Control.CompleteControl` | Ashby §11/14: perfect regulation makes complete control possible, and what that costs the regulator |
| `AISafetyAtlas.Control.InformationLimits` | Touchette–Lloyd: control loss, and feedback bounded by what the sensor measured |
| `AISafetyAtlas.Control.Observability` | Touchette–Lloyd Theorems 5 and 6 and Corollary 7: sensor loss and perfect observability |
| `AISafetyAtlas.Control.OpenLoop` | Touchette–Lloyd Lemma 8 and Theorem 9: a pure open-loop controller is optimal |
| `AISafetyAtlas.Control.OpenLoopAttainment` | Touchette–Lloyd eq. (48): the maximum over input distributions is attained, by simplex compactness |
| `AISafetyAtlas.Control.PolicyKernel` | Touchette–Lloyd eq. (28) as a minimum over kernels, attained by deterministic state feedback |
| `AISafetyAtlas.Control.Purification` | Touchette–Lloyd eq. (7): every actuation kernel is a deterministic map of an exogenous seed, so Theorems 9 and 10 hold at printed scope |

## Single-surface domains

One module carries the domain. Vendored or external proofs are re-exported where
the result is not proved here.

| Import | Domain |
|---|---|
| `AISafetyAtlas.Combinatorics.PermInvariance` | What invariance under relabelling forces, for functions and for relations: orbits, the multiset-of-values invariant, the counts, and the fact that an invariant relation is constant off the diagonal. Domain-neutral; `Learning.Sharp` is its consumer |
| `AISafetyAtlas.Computability` | Rice / halting (Mathlib wrappers) |
| `AISafetyAtlas.Explainability` | Attribution impossibility |
| `AISafetyAtlas.Inference` | Wolpert inference devices: weak/strong inference, Wolpert's own notion of control over a device, physical knowledge. **Not** Ashby or Touchette–Lloyd control — for those see `AISafetyAtlas.Control` |
| `AISafetyAtlas.Learning` | Finite NFL cores |
| `AISafetyAtlas.Learning.Sharp` | The closed-under-permutation NFL characterization, both directions (`CT-10`) |
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
| `AISafetyAtlas.Oversight.VarietyBound` | Bridge: seeing and doing are independent oversight capacities, proved in both directions. Not re-exported by `Oversight.JointObservation` |
| `AISafetyAtlas.Oversight.VarietyCheck` | The executable side of that bridge, with its agreement theorem. Backs `atlas-check`'s `variety` kind |

## Peer modules

`InformationTheory` has no aggregating parent: each module is one result, and
none is built on the others. Import the one needed. The two entropy modules take
their entropy layer from PFR rather than from `AISafetyAtlas.Inference.entropyOn`,
which is a separate Wolpert-specific development and is not migrated;

| Import | Domain |
|---|---|
| `AISafetyAtlas.InformationTheory.Fano` | Fano's inequality for an arbitrary estimate on any probability space |
| `AISafetyAtlas.InformationTheory.DataProcessing` | Markov chains, the mutual-information chain rule, data processing and its equality case |
| `AISafetyAtlas.InformationTheory.ChannelCapacity` | Capacity of a discrete noiseless channel, with repeated use and parallel composition as lemmas. `Control` is one consumer, not the owner |
| `AISafetyAtlas.InformationTheory.Determinism` | One lemma: a function of a variable adds no uncertainty to it. Three consumers in two domains |

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
| `AISafetyAtlas.Knowledge.Entropy` | The kernel measured: knowability forces zero conditional entropy, positive conditional entropy certifies unknowability, and Fano through data processing bounds every decoder's error rate |
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
