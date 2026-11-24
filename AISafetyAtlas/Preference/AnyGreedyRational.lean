module

public import AISafetyAtlas.Preference.AnyGreedy
public import AISafetyAtlas.Preference.RationalComplexity

/-!
# The fixed-order greedy planners are greedy planners

Armstrong and Mindermann's footnote 9 (PDF p. 6): *"argmax just requires a
for-loop, a reference to R, a comparison with a previously stored value, and
possibly the storage of a new value and the current action"*. That loop, run
along a listing a₀ :: l of the actions and replacing the stored action only on
a strictly higher value, is `AISafetyAtlas.Preference.greedyOn`, and every fixed
priority order of the actions is such a listing. Every covering listing gives a
greedy planner in the sense of `AISafetyAtlas.Preference.IsGreedy`, so the
statements over every greedy planner apply to each fixed tie order. (A loop that
also replaces on equal values is a greedy planner too, but no lemma here
identifies it with a `greedyOn`.)
-/

namespace AISafetyAtlas.Preference

variable {S A : Type*}

/-- **The footnote-9 for-loop planner is a greedy planner**: `greedyOn` along a
listing covering every action satisfies `IsGreedy`, whatever the order of the
listing. -/
public theorem isGreedy_greedyOn {a₀ : A} {l : List A} (hl : ∀ a, a ∈ a₀ :: l) :
    IsGreedy (greedyOn (S := S) a₀ l) :=
  fun R s a => greedyOn_max hl R s a

end AISafetyAtlas.Preference
