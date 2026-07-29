module

public import AISafetyAtlas.Computability
public import AISafetyAtlas.Compositional
public import AISafetyAtlas.Explainability
public import AISafetyAtlas.Learning
public import AISafetyAtlas.Logic
public import AISafetyAtlas.Preference
public import AISafetyAtlas.Preference.Complexity
public import AISafetyAtlas.Preference.Reasonable
public import AISafetyAtlas.Preference.SourceComplexity
public import AISafetyAtlas.Preference.Override
public import AISafetyAtlas.Preference.Regret
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

## Facades (start here)

| Import | Domain |
|---|---|
| `AISafetyAtlas.Logic` | Incompleteness / undefinability |
| `AISafetyAtlas.Computability` | Rice / halting (Mathlib wrappers) |
| `AISafetyAtlas.Verification` | Behavioral verification + bridges |
| `AISafetyAtlas.SocialChoice` | Arrow / Gibbard–Satterthwaite |
| `AISafetyAtlas.Learning` | Finite NFL cores |
| `AISafetyAtlas.Compositional` | Hyperproperties, rectangles, networks |
| `AISafetyAtlas.Wireheading` | Reward channels, self-modification |
| `AISafetyAtlas.Preference` | Planner/reward unidentifiability (BY-011) |
| `AISafetyAtlas.Explainability` | Attribution impossibility |

Each facade's module docstring lists **primary** declarations (laws / instances /
boundaries). Prefer those names over diving into `Upstream/` unless editing a
vendored proof.
-/
