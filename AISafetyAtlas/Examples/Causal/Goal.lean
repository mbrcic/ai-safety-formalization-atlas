module

public import AISafetyAtlas.Causal.Goal

/-!
# A worked goal space on two states and two actions

`AISafetyAtlas.Causal.Goal` renders MAIS-A2's goal formalism. This module runs
it on `𝐒 = 𝐀 = Fin 2` and checks the facts that decide whether it is the printed
object rather than a shape with the right name:

* each of the three operators is exercised on a concrete trajectory, and the
  *Eventually* case is checked at the **least** hitting time rather than at some
  hitting time — a weaker reading would shift the recursion past a different
  point;
* a sequential goal of depth two is satisfied, so the shift clause is not
  vacuous, and one is **not** satisfied, so satisfaction is not trivial;
* the immediate-win lemma fires on a composite goal, which is the step every
  counting argument over `𝚿_n` rests on;
* the three counts are evaluated: `|SubGoal| = 48`, `|𝚿_1| = 2^48 - 1`, and
  `R = 8` immediate wins per state–action pair.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Causal.Goal

open AISafetyAtlas.Causal

/-! ## The space -/

/-- Two states, two actions, so `|𝐒 × 𝐀| = 4`. -/
public theorem card_subGoal_two : Fintype.card (SubGoal (Fin 2) (Fin 2)) = 48 := by
  rw [card_subGoal]
  simp

/-- `R = 2^{|𝐒||𝐀| - 1} = 8` immediate wins at every state–action pair. -/
public theorem card_immediateWins_two (s a : Fin 2) :
    (immediateWins s a).card = 8 := by
  rw [card_immediateWins]
  simp

/-- The depth-one sequential goals are exactly the sub-goals. -/
public theorem card_boundedGoals_one :
    (boundedGoals (S := Fin 2) (A := Fin 2) 1).card = 48 := by
  have h : boundedGoals (S := Fin 2) (A := Fin 2) 1 = goalsOfLength 1 := by
    simp [boundedGoals]
  rw [h, card_goalsOfLength, card_subGoal_two, pow_one]

/-- `|𝚿_1| = 2^48 - 1`. The exponent is the set-of-disjuncts convention: a
reading that bounded the *number* of disjuncts would give a polynomial count
here, and every corruption-counting argument would change with it. -/
public theorem card_compositeGoals_one :
    (compositeGoals (S := Fin 2) (A := Fin 2) 1).card = 2 ^ 48 - 1 := by
  rw [card_compositeGoals, card_boundedGoals_one]

/-- The exceptional fraction at this space, from `exceptional_ratio_lt`. -/
public theorem exceptional_ratio_two :
    ((2 ^ (48 - 8) - 1 : ℕ) : ℝ) / ((2 ^ 48 - 1 : ℕ) : ℝ) < 2 / 2 ^ 8 :=
  exceptional_ratio_lt (by norm_num) (by norm_num)

/-! ## The trajectory semantics, exercised

`τ` visits `(0,0)`, then `(1,1)`, then `(0,1)` for ever. -/

/-- The worked trajectory. -/
@[expose] public def τ : ℕ → Fin 2 × Fin 2
  | 0 => (0, 0)
  | 1 => (1, 1)
  | _ => (0, 1)

/-- **Now**, at time `0`. -/
public theorem now_at_zero :
    IsAchievementTime ({ op := .now, target := {((0 : Fin 2), (0 : Fin 2))} }) τ 0 :=
  ⟨rfl, by decide⟩

/-- **Next**, at time `1`. -/
public theorem next_at_one :
    IsAchievementTime ({ op := .next, target := {((1 : Fin 2), (1 : Fin 2))} }) τ 1 :=
  ⟨rfl, by decide⟩

/-- **Eventually**, at the *least* hitting time `2` — the pair `(0,1)` is first
reached there, and the two earlier steps miss it. This is the clause a
"some hitting time" reading would lose. -/
public theorem eventually_at_two :
    IsAchievementTime ({ op := .eventually, target := {((0 : Fin 2), (1 : Fin 2))} }) τ 2 := by
  refine ⟨by decide, ?_⟩
  intro t ht
  have h2 : t = 0 ∨ t = 1 := by omega
  rcases h2 with rfl | rfl <;> decide

/-- The same *Eventually* sub-goal is **not** achieved at time `3`: the
achievement time is the least one, so minimality is a real constraint here. -/
public theorem not_eventually_at_three :
    ¬ IsAchievementTime ({ op := .eventually, target := {((0 : Fin 2), (1 : Fin 2))} }) τ 3 := by
  rintro ⟨-, hmin⟩
  exact hmin 2 (by norm_num) (by decide)

/-- **The shift clause is not vacuous.** A depth-two goal — *Now* `(0,0)`, then
*Eventually* `(0,1)` on the trajectory shifted past time `0` — is satisfied. -/
public theorem satisfies_depth_two :
    Satisfies [{ op := .now, target := {((0 : Fin 2), (0 : Fin 2))} },
               { op := .eventually, target := {((0 : Fin 2), (1 : Fin 2))} }] τ := by
  refine ⟨0, ⟨rfl, by decide⟩, 1, ⟨by decide, ?_⟩, trivial⟩
  intro t ht
  have h0 : t = 0 := by omega
  subst h0
  decide

/-- **Satisfaction is not trivial.** No state–action pair of `τ` is `(1,0)`, so
a goal demanding it eventually is unsatisfied. -/
public theorem not_satisfies_unreachable :
    ¬ Satisfies [{ op := .eventually, target := {((1 : Fin 2), (0 : Fin 2))} }] τ := by
  rintro ⟨T, ⟨hT, -⟩, -⟩
  match T with
  | 0 => exact absurd hT (by decide)
  | 1 => exact absurd hT (by decide)
  | (n + 2) => exact absurd hT (by simp [τ])

/-! ## The immediate win fires -/

/-- The composite goal carrying the *Now* disjunct `{(0,0)}` is achieved by `τ`,
and the proof reads only `τ 0` — no environment, no transition probability. -/
public theorem immediateWin_fires :
    CompositeSatisfies ({nowGoal {((0 : Fin 2), (0 : Fin 2))}} : CompositeGoal (Fin 2) (Fin 2)) τ :=
  compositeSatisfies_of_immediateWin
    (ψ := nowGoal {((0 : Fin 2), (0 : Fin 2))})
    (by
      simp only [immediateWins, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨{((0 : Fin 2), (0 : Fin 2))}, ⟨Finset.subset_univ _, by decide⟩, rfl⟩)
    (Finset.mem_singleton_self _) (τ := τ) rfl

end AISafetyAtlas.Examples.Causal.Goal
