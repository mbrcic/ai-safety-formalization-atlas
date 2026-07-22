module

import AISafetyAtlas.Learning

/-!
# First contribution — a copyable starter

A minimal, self-contained file for your first Lean change (task **CT-13**,
`docs/guide/contributor-tasks.md#open-now`). It compiles as-is, so you can copy
it, add one line, and watch CI stay green.

Everything here is Foundation-free: it imports only `AISafetyAtlas.Learning`, so
it builds under the fast `scripts/setup.sh --quick` path — no full Gödel build
needed. The stable public facade is the single root import:

```lean
import AISafetyAtlas
```

Bring your own theorem in over that root when you graduate to the headline
surface (Rice, Arrow, Gödel, Löb — see the README "Lean API" section). Here we
stay on the learning layer to keep the starter light.
-/

open AISafetyAtlas.Learning

namespace AISafetyAtlas.Examples.FirstContribution

/-- Train on `{0}` only. -/
def trainOn0 : Set (Fin 2) := {0}

/-- Constant-0 learner. -/
def learnerConst0 : SupervisedLearner (Fin 2) (Fin 2) trainOn0 :=
  fun _ _ => 0

/-- Constant-1 learner. -/
def learnerConst1 : SupervisedLearner (Fin 2) (Fin 2) trainOn0 :=
  fun _ _ => 1

/--
Two different learners have equal aggregate off-training-set loss — a concrete
instance of `no_free_lunch_supervised`. This uses the shipped theorem; it does
not reprove it.
-/
example :
    aggregateOffTrainingLoss trainOn0 learnerConst0 =
      aggregateOffTrainingLoss trainOn0 learnerConst1 :=
  no_free_lunch_supervised trainOn0 learnerConst0 learnerConst1

/-
YOUR TURN (CT-13, difficulty S)
-------------------------------
Add ONE new `example` below that exercises an existing shipped theorem — no new
math, just a use-site. Ideas:

  * a third constant learner and another `no_free_lunch_supervised` instance;
  * a `no_free_lunch` instance over cost-sequence schedules
    (see `AISafetyAtlas.Examples.NFLConcrete` for the pattern);
  * anything from the README "Lean API" list, after switching to `import
    AISafetyAtlas`.

Then: `lake build AISafetyAtlas.Examples.FirstContribution` must be green and
`python3 scripts/check_print_axioms.py` must stay clean. Open a pull request.
-/

end AISafetyAtlas.Examples.FirstContribution
