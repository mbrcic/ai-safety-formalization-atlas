module

public import AISafetyAtlas.Wireheading.Corruption
public import AISafetyAtlas.Wireheading.AgentEquations
public import AISafetyAtlas.Wireheading.CRMDP
public import AISafetyAtlas.Wireheading.ObservationLimits
public import AISafetyAtlas.Wireheading.GoalPreservation
public import AISafetyAtlas.Wireheading.GoalPreservationSource
public import AISafetyAtlas.Wireheading.Objective

/-!
# Wireheading and self-modification — public facade

Results on **corruptible reward / evaluation channels**, finite-horizon
objective structure, and **on-policy goal preservation** under self-modification.
Import this module (or `AISafetyAtlas`) for the surface below.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Law** | `Corruption.ComplementedClass.everitt_theorem_eleven` | Half-maximal worst-case regret from complement closure |
| **Specialization** | `CRMDP.Model.everitt_theorem_eleven` | Same bound with states, corruption, observed channel (BY-039 canonical) |
| **Law** | `CRMDP.Env.observed_complement` | Environment and complement look the same on the channel |
| **Law** | `CRMDP.return_add_complement` | True returns sum to the horizon (eq. 3 style) |
| **Boundary** | `ObservationLimits.not_knowable_trueReturn_of_complement_mem` | A complement pair inside a class defeats every history-to-return decoder |
| **Corollary** | `ObservationLimits.not_knowable_trueReturn` | The unrestricted class, at any positive horizon |
| **Law** | `GoalPreservationSource.Model.selected_matches_initial` | Finite-percept Thm 16 induction step without naming surjectivity |
| **Law** | `GoalPreservationSource.Model.safe_modification` | One-step on-policy continuation matches initial value |
| **Specialization** | `AgentEquations.value_eq_of_agree_on_window` | Ring–Orseau finite value depends only on window `(u,w)` |
| **Helper** | `Objective.value_eq_of_agree_on_window` | Finite-horizon locality on trajectories |
| **Helper** | `Objective.value_congr` | Record congruence only — not a paper theorem |

Simpler / secondary: deterministic `GoalPreservation` (uses strong
`names_surjective`); keep as a specialization. `GoalPreservationSource` is the
source-aligned finite-percept induction step, not the full source theorem.

## Explicit non-claims

- **Not** EXACT Everitt et al. Theorem 11: one CRMDP model fixes a deterministic
  transition while the source class may range over stochastic kernels; extrema
  are structure fields; rewards range over the continuous interval `[0,1]`
  rather than a finite uniform grid. Graded **RELATED**.
- **Not** a full Ring–Orseau delusion-box development or AIXI; AgentEquations is
  a finite-horizon packaging of displayed equations under an arbitrary weight
  `ρ`.
- **Not** utility modification; GoalPreservationSource is policy self-mod only,
  and still assumes domination / continuation structure rather than deriving
  full Theorem 20. Its finite percept weights are normalized and full-support.
- **Not** multiprincipal / shared-evaluator infrastructure by itself — that is
  a possible consumer of these cores, not what this facade currently is.
- **Not** an AI-system bridge without separate review.

- **Not** a novelty claim for `ObservationLimits`: the impossibility is the
  source's and `CRMDP` already formalizes both of its steps. That module adds the
  factorization reading through `Knowledge`, a certificate, and the import edge.
  It is class-relative, says nothing about approximate or prior-conditional
  estimation, and quantifies over environments rather than over agents.

Survey / landscape: BY-039 (RELATED), `LAND-WIRE-OBJ-001`, `LAND-GOAL-001`,
`LAND-CRMDP-KNOW-001`.
Residuals: `docs/provenance/a1-a3-b1-b3-b7-reverification.md`.
-/
