module

import AISafetyAtlas.Learning

/-!
# Concrete finite-domain NFL instance

Tiny `Fin 2 → Fin 2` schedules: two distinct length-1 samples must have
equal aggregate performance for any cost-sequence score. Exercises the
shipped `no_free_lunch` entry point (not a reimplementation).
-/

open AISafetyAtlas.Learning
open Fintype

namespace AISafetyAtlas.Examples.NFLConcrete

/-- Sample the first point of `Fin 2`. -/
def schedule0 : NonadaptiveSchedule (Fin 2) 1 where
  sample := fun _ => 0
  injective := by
    intro a b h
    exact Subsingleton.allEq a b

/-- Sample the second point of `Fin 2`. -/
def schedule1 : NonadaptiveSchedule (Fin 2) 1 where
  sample := fun _ => 1
  injective := by
    intro a b h
    exact Subsingleton.allEq a b

/--
Any cost-sequence score of length 1 has equal uniform aggregate performance
on the two length-1 schedules over `Fin 2`.
-/
example (Φ : CostPerformance 1 (Fin 2)) :
    aggregatePerformance Φ schedule0 = aggregatePerformance Φ schedule1 :=
  no_free_lunch Φ schedule0 schedule1

/-- Closed form: both aggregates equal `|Y|^{|X|-1} · ∑_c Φ(c)`. -/
example (Φ : CostPerformance 1 (Fin 2)) :
    aggregatePerformance Φ schedule0 =
      (card (Fin 2) : ℝ) ^ (card (Fin 2) - 1) * ∑ c : Fin 1 → Fin 2, Φ c :=
  aggregatePerformance_eq_scaled_sum Φ schedule0

/-! ## Supervised OTS form on `Fin 2` -/

/-- Train on `{0}` only. -/
def trainOn0 : Set (Fin 2) := {0}

/-- Constant-0 learner. -/
def learnerConst0 : SupervisedLearner (Fin 2) (Fin 2) trainOn0 :=
  fun _ _ => 0

/-- Constant-1 learner. -/
def learnerConst1 : SupervisedLearner (Fin 2) (Fin 2) trainOn0 :=
  fun _ _ => 1

/-- Both learners have equal aggregate off-training-set loss. -/
example :
    aggregateOffTrainingLoss trainOn0 learnerConst0 =
      aggregateOffTrainingLoss trainOn0 learnerConst1 :=
  no_free_lunch_supervised trainOn0 learnerConst0 learnerConst1

end AISafetyAtlas.Examples.NFLConcrete
