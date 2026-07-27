module

import AISafetyAtlas.Learning

/-!
# First contribution — a copyable starter

A minimal, self-contained file for your first Lean change (task **CT-13**,
`docs/guide/contributor-tasks.md#open-now`). It compiles as-is, so you can copy
it, add one line, and watch CI stay green.

The first example below is the reference pattern; merged CT-13 contributions
accumulate underneath it, so expect the list to grow. Append yours at the
bottom, under the marker after the "YOUR TURN" block.

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

/-- Constant-0 learner with a three-element label space. -/
def learnerThreeConst0 : SupervisedLearner (Fin 2) (Fin 3) trainOn0 :=
  fun _ _ => 0

/-- Constant-2 learner with a three-element label space. -/
def learnerThreeConst2 : SupervisedLearner (Fin 2) (Fin 3) trainOn0 :=
  fun _ _ => 2

/--
The aggregate off-training-set loss remains learner-independent after enlarging
the label space from `Fin 2` to `Fin 3`.
-/
example :
    aggregateOffTrainingLoss trainOn0 learnerThreeConst0 =
      aggregateOffTrainingLoss trainOn0 learnerThreeConst2 :=
  no_free_lunch_supervised trainOn0 learnerThreeConst0 learnerThreeConst2

/-
YOUR TURN (CT-13, difficulty S)
-------------------------------
Add ONE new `example` of your own that exercises an existing shipped theorem —
no new math, just a use-site. Ideas:

  * another constant learner and another `no_free_lunch_supervised` instance;
  * a `no_free_lunch` instance over cost-sequence schedules
    (see `AISafetyAtlas.Examples.NFLConcrete` for the pattern);
  * anything from the README "Lean API" list, after switching to `import
    AISafetyAtlas`.

This is an onboarding exercise, ONE PER CONTRIBUTOR — it proves you can drive
the toolchain, not that the API needed another caller. Coverage here is already
complete: `AISafetyAtlas.Examples.PublicAPI` applies every declaration on the
README "Lean API" list, and `NFLConcrete` covers the learning-layer schedules.
So a second CT-13 will be closed, and widening a type parameter (`Fin 2` →
`Fin 3`) or changing a constant in an already-exercised theorem is not a
distinct use-site. Once yours has merged, take a rung that moves coverage —
`docs/guide/contributor-tasks.md`, "Open now".

APPEND IT AT THE BOTTOM, below this block and above the `end` line — not between
the examples above. Those are earlier contributors' use-sites; leave them alone.
Appending keeps everyone's diffs from colliding.

Then: `lake build AISafetyAtlas.Examples.FirstContribution` must be green and
`./scripts/agent_gate.sh` must stay clean. An anonymous `example` adds no public
declaration, so you do not need to run the kernel axiom check locally — CI runs
it over the headline surface for you. Open a pull request.
-/

-- ↓↓↓ APPEND YOUR CT-13 EXAMPLE HERE ↓↓↓

end AISafetyAtlas.Examples.FirstContribution
