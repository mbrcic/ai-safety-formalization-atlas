module

public import AISafetyAtlas.Compositional.Hyperproperties
public import AISafetyAtlas.Compositional.Hyperproperties.PrefixTopology
public import AISafetyAtlas.Compositional.Hyperproperties.Product
public import AISafetyAtlas.Compositional.LocalContractBoundary
public import AISafetyAtlas.Compositional.Networks
public import AISafetyAtlas.Compositional.Rectangularity
public import AISafetyAtlas.Compositional.Symmetry

/-!
# Compositional safety — public facade

Mathematics for **when local structure does or does not compose** into global
guarantees: rectangular local contracts, hyperproperty self-composition, and
anonymous-network symmetry. Import this module (or `AISafetyAtlas`) for the
surface below; nested files hold proofs.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Law** | `rectangle_iff_exchange_closed` | Binary relation is a rectangle iff mix-and-match closed |
| **Law** | `coordinate_product_iff_spliceClosed` | Finite-index product of projections iff local splice closed |
| **Boundary** | `not_isCoordinateProduct_finitelySupported` | Finiteness is necessary for the splice law |
| **Boundary** | `LocalContractBoundary.not_isRectangle_agreement` | Two-agent agreement is not a local product contract |
| **Boundary** | `LocalContractBoundary.atMostOneTrace_bool_boundary` | 2-safety need not be a pure per-trace property |
| **Law** | `Hyperproperties.k_safety_iff_finite_self_composition` | Batch form of Clarkson–Schneider k-safety reduction |
| **Law** | `Hyperproperties.k_safety_iff_product_self_composition` | Synchronized-product form (nonempty systems) |
| **Law** | `Hyperproperties.hyperSafety_of_isKSafety` | k-safety ⇒ operational hypersafety |
| **Law** | `Hyperproperties.hyperSafety_hyperLiveness_decomposition` | Operational safety/liveness split via prefix topology |
| **Law** | `Networks.runFor_eq_of_view_eq` | Equal views ⇒ equal states after n rounds |
| **Law** | `Networks.no_unique_leader_of_fixedPointFree` | No unique leader under free automorphism |
| **Helper** | `Symmetry.Protocol.no_unique_leader_from_symmetric_start` | Core symmetry invariant (observation as field) |

Helpers retained but **not** headline: `coordinate_product_iff_recombination_closed`
(near-definitional), generic `hypersafety_hyperliveness_decomposition` under an
arbitrary topology (use `PrefixTopology` for the operational reading).

## Explicit non-claims

- **Not** a claim that arbitrary multi-agent safety properties factor into
  independent per-agent contracts. See `LocalContractBoundary` for machine-checked
  limits: agreement is not a rectangle; 2-safety need not be a pure trace
  property. Relational multiparty goals need the hyperproperty surface.
- **Not** BY-043 embodiment / self-interest formalization. Networks and
  Symmetry are RELATED dependencies for that survey row at most.
- **Not** full Angluin covering theory, randomized leader election, or
  assume-guarantee completeness (e.g. Dewes–Dimitrova GEDCs).
- **Not** an AI-system bridge. No `ai_bridge_status` graduation from this facade.
- **Not** the same question as `AISafetyAtlas.Oversight.JointObservation`. That surface
  asks whether a hazard label factors through an available observation, under typed
  coalition access restriction. Rectangularity asks whether a relation decomposes into
  local product constraints. Neither subsumes the other — a rectangular relation may be
  unobservable, and a non-rectangular one may be covered — but the indistinguishability
  and bounded-witness patterns recur in both.

Landscape / survey anchors: `LAND-HYPER-002`, `LAND-RECT-001`, `LAND-ANGLUIN-001`,
BY-043 (RELATED). Cores compile; paper-parity residuals live in
`docs/provenance/a1-a3-b1-b3-b7-reverification.md`.
-/
