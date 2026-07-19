module

public import AISafetyAtlas.Upstream.Attribution.Trilemma

/-!
# Explainability / attribution limits

Atlas-facing names for attribution impossibility results. Thin wrappers over
the core trilemma adapted from Caraker et al. (Apache-2.0 software per
`CITATION.cff`). No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Explainability

/-- Feature index type (collinearity groups). -/
public abbrev FeatureIndex := AISafetyAtlas.Upstream.Attribution.FeatureIndex

/-- Group membership. -/
public abbrev inGroup := AISafetyAtlas.Upstream.Attribution.inGroup

/-- Rashomon property for an attribution map. -/
public abbrev RashomonProperty := AISafetyAtlas.Upstream.Attribution.RashomonProperty

/--
Attribution impossibility: under the Rashomon property, no ranking is both
faithful to every model's attributions and stable across models.

Source: `DASHImpossibility.attribution_impossibility`
(DrakeCaraker/dash-impossibility-lean).
-/
public theorem attribution_impossibility
    (fs : FeatureIndex)
    (Model : Type)
    (attribution : Fin fs.P → Model → ℝ)
    (hrash : RashomonProperty fs Model attribution)
    (ℓ : Fin fs.L) (j k : Fin fs.P)
    (hj : inGroup fs ℓ j) (hk : inGroup fs ℓ k) (hjk : j ≠ k)
    (ranking : Fin fs.P → Fin fs.P → Prop)
    (h_faithful : ∀ f : Model,
      ranking j k ↔ attribution j f > attribution k f) :
    False :=
  AISafetyAtlas.Upstream.Attribution.attribution_impossibility
    fs Model attribution hrash ℓ j k hj hk hjk ranking h_faithful

/-- Weak-faithfulness form of the attribution impossibility. -/
public theorem attribution_impossibility_weak
    (fs : FeatureIndex)
    (Model : Type)
    (attribution : Fin fs.P → Model → ℝ)
    (hrash : RashomonProperty fs Model attribution)
    (ℓ : Fin fs.L) (j k : Fin fs.P)
    (hj : inGroup fs ℓ j) (hk : inGroup fs ℓ k) (hjk : j ≠ k)
    (ranking : Fin fs.P → Fin fs.P → Prop)
    (h_faithful_jk : ∀ f : Model,
      attribution j f > attribution k f → ranking j k)
    (h_faithful_kj : ∀ f : Model,
      attribution k f > attribution j f → ranking k j)
    (h_antisym : ¬ (ranking j k ∧ ranking k j)) :
    ¬ (ranking j k ∨ ranking k j) :=
  AISafetyAtlas.Upstream.Attribution.attribution_impossibility_weak
    fs Model attribution hrash ℓ j k hj hk hjk ranking
    h_faithful_jk h_faithful_kj h_antisym

end AISafetyAtlas.Explainability
