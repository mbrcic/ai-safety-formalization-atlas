module

public import AISafetyAtlas.Composition.Rectangularity
public import AISafetyAtlas.Composition.Observability

/-!
# Compositional safety boundaries

Umbrella import for the compositional-expressibility and
observation-boundary layers:

- `AISafetyAtlas.Composition` — when a global safe set decomposes into
  independent per-agent contracts (`independent_iff_rectangular`,
  `not_independent_of_failed_splice`).
- `AISafetyAtlas.Composition.Observability` — when a hazard is monitorable from the
  available observations (`factors_through_iff_fiber_invariant`,
  `no_perfect_monitor_of_collision`).
-/
