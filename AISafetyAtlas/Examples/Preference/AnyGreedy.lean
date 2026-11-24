module

public import AISafetyAtlas.Preference.AnyGreedyTimed
public import AISafetyAtlas.Preference.AnyGreedyRational
public import AISafetyAtlas.Examples.Preference.TimedComplexity
public import AISafetyAtlas.Examples.Preference.SourceComplexity

/-!
# Witnesses for the results at every greedy planner

Print's instance S = {s}, A = {a₁, a₂} (here `Unit` and `Bool`).

* `tieSwap` applied to a planner g breaks every tie the other way from g. At
  g := `greedyPlanner` it
  is a greedy planner (`isGreedy_swapGreedy`) that differs from `greedyPlanner`
  at the zero reward (`swapGreedy_zero_ne`, `swapGreedy_ne_greedyPlanner`): the
  witness of the adversarial round, in Lean.
* `halfLanguage`, at any planner g, is a language c-reasonable for the F built
  from g, at c = 0, that is not degenerate: the pairs whose reward is the constant
  ±1/2 cost 3, every other pair costs 0. The indifferent pair with the constant
  reward 1/2 is compatible with every policy and is not amongst the lowest, so
  the conditional Theorem 2 and Conjecture 9 have inhabited hypotheses.
* `planLanguage` separates the new statements from the old ones: it is
  0-reasonable for the F built from `swapGreedy` (`planLanguage`) but not for the
  library's F built from `greedyPlanner` (`planK_not_reasonable_greedyPlanner`),
  so Proposition 7 applies to it only through the statement at every greedy
  planner (`plan_proposition_seven`).
-/

namespace AISafetyAtlas.Examples.Preference.AnyGreedy

open AISafetyAtlas.Preference AISafetyAtlas.Preference.Source

/-! ## A greedy planner that is not `greedyPlanner` -/

/-- Break every tie the other way from g: where both actions score the same,
take the action g does not take. -/
@[expose] public noncomputable def tieSwap (g : Planner (RewardFn Unit Bool) (Policy Unit Bool)) :
    Planner (RewardFn Unit Bool) (Policy Unit Bool) :=
  fun R s => if R s true = R s false then !(g R s) else g R s

/-- Swapping the ties of a greedy planner gives a greedy planner. -/
public theorem isGreedy_tieSwap {g : Planner (RewardFn Unit Bool) (Policy Unit Bool)}
    (hg : IsGreedy g) : IsGreedy (tieSwap g) := by
  intro R s a
  have h := hg R s a
  unfold tieSwap
  split_ifs with ht
  · cases hga : g R s <;> cases a <;> simp_all
  · exact h

/-- `greedyPlanner` with every tie broken the other way. -/
@[expose] public noncomputable def swapGreedy : Planner (RewardFn Unit Bool) (Policy Unit Bool) :=
  tieSwap greedyPlanner

/-- `swapGreedy` is a greedy planner. -/
public theorem isGreedy_swapGreedy : IsGreedy swapGreedy :=
  isGreedy_tieSwap AISafetyAtlas.Preference.isGreedy_greedyPlanner

/-- At the zero reward, `swapGreedy` takes the action `greedyPlanner` does not. -/
public theorem swapGreedy_zero_ne :
    swapGreedy 0 () ≠ greedyPlanner (0 : RewardFn Unit Bool) () := by
  unfold swapGreedy tieSwap
  simp only [Pi.zero_apply, if_true]
  cases greedyPlanner (0 : RewardFn Unit Bool) () <;> decide

/-- **`swapGreedy` is not `greedyPlanner`**: print's p_g may be a greedy planner
other than the library's choice. -/
public theorem swapGreedy_ne_greedyPlanner :
    swapGreedy ≠ (greedyPlanner : Planner (RewardFn Unit Bool) (Policy Unit Bool)) :=
  fun h => swapGreedy_zero_ne (by rw [h])

/-! ## Greedy-planner facts at `swapGreedy` -/

example : IsGreedy (greedyPlanner : Planner (RewardFn Unit Bool) (Policy Unit Bool)) :=
  AISafetyAtlas.Preference.isGreedy_greedyPlanner

example (π : Policy Unit Bool) : swapGreedy (rewardOf π) = π :=
  AISafetyAtlas.Preference.IsGreedy.apply_rewardOf isGreedy_swapGreedy π

example (π : Policy Unit Bool) : negPlanner swapGreedy (-rewardOf π) = π :=
  AISafetyAtlas.Preference.IsGreedy.negPlanner_neg_rewardOf isGreedy_swapGreedy π

/-- The anti-greedy planner built from `swapGreedy` takes a minimiser. -/
example (R : RewardFn Unit Bool) (a : Bool) : R () (negPlanner swapGreedy R ()) ≤ R () a :=
  AISafetyAtlas.Preference.IsGreedy.negPlanner_min isGreedy_swapGreedy R () a

/-- A greedy planner on print's bounded rewards (here `swapGreedy` restricted to
them) extends to a greedy planner on all real rewards. -/
example : ∃ g : Planner (RewardFn Unit Bool) (Policy Unit Bool), IsGreedy g ∧
    ∀ R : BoundedRewardFn Unit Bool, g R.1 = swapGreedy R.1 :=
  AISafetyAtlas.Preference.IsGreedy.exists_extend (fun R => swapGreedy R.1)
    (fun R s a => isGreedy_swapGreedy R.1 s a)

/-- **Lemma 6 at `swapGreedy`.** -/
public theorem swap_lemma_six (π : Policy Unit Bool) :
    Explains (indifferentPlanner π) (0 : RewardFn Unit Bool) π ∧
      Explains swapGreedy (rewardOf π) π ∧
      Explains (negPlanner swapGreedy) (-rewardOf π) π :=
  AISafetyAtlas.Preference.lemma_six_of_isGreedy isGreedy_swapGreedy π

/-- `lemma_six` is the instance of `lemma_six_of_isGreedy` at `greedyPlanner`. -/
example (π : Policy Unit Bool) :
    Explains (indifferentPlanner π) (0 : RewardFn Unit Bool) π ∧
      Explains greedyPlanner (rewardOf π) π ∧
      Explains (negPlanner greedyPlanner) (-rewardOf π) π :=
  AISafetyAtlas.Preference.lemma_six_of_isGreedy
    AISafetyAtlas.Preference.isGreedy_greedyPlanner π

/-- The footnote-9 loop along false, true is a greedy planner. -/
example : IsGreedy (greedyOn (S := Unit) false [true]) :=
  AISafetyAtlas.Preference.isGreedy_greedyOn (by decide)

example : op2Of (greedyPlanner (S := Unit) (A := Bool)) = op2 :=
  AISafetyAtlas.Preference.op2Of_greedyPlanner

example (π : Policy Unit Bool) : op3 (op2Of swapGreedy (op6 π)) = π :=
  AISafetyAtlas.Preference.op3_op2Of_op6 isGreedy_swapGreedy π

example (π : Policy Unit Bool) : op3 (op4 (op2Of swapGreedy (op6 π))) = π :=
  AISafetyAtlas.Preference.op3_op4_op2Of_op6 isGreedy_swapGreedy π

/-! ## The composite operations at `swapGreedy` -/

example : F₂Of (greedyPlanner (S := Unit) (A := Bool)) = F₂ :=
  AISafetyAtlas.Preference.Source.F₂Of_greedyPlanner

example : F₃Of (greedyPlanner (S := Unit) (A := Bool)) = F₃ :=
  AISafetyAtlas.Preference.Source.F₃Of_greedyPlanner

example : FmapOf (greedyPlanner (S := Unit) (A := Bool)) = Fmap :=
  AISafetyAtlas.Preference.Source.FmapOf_greedyPlanner

example (π : Policy Unit Bool) : F₁ (op1 (op5 π)) = op1 (op5 π) :=
  AISafetyAtlas.Preference.Source.F₁_of_compatible_any_planner
    (ReasonableForF.compatible_indifferent π)

example (π : Policy Unit Bool) :
    F₂Of swapGreedy (op1 (op5 π)) = op2Of swapGreedy (op6 π) :=
  AISafetyAtlas.Preference.Source.F₂Of_of_compatible swapGreedy
    (ReasonableForF.compatible_indifferent π)

example (π : Policy Unit Bool) :
    F₃Of swapGreedy (op1 (op5 π)) = op4 (op2Of swapGreedy (op6 π)) :=
  AISafetyAtlas.Preference.Source.F₃Of_of_compatible swapGreedy
    (ReasonableForF.compatible_indifferent π)

/-- **The witness of the adversarial round**: at x = (p_π, 0), F₂ built from
`swapGreedy` and F₂ built from `greedyPlanner` give different pairs. -/
public theorem F₂Of_swapGreedy_ne (π : Policy Unit Bool) :
    F₂Of swapGreedy (op1 (op5 π)) ≠ F₂ (op1 (op5 π)) := by
  rw [← AISafetyAtlas.Preference.Source.F₂Of_greedyPlanner,
    AISafetyAtlas.Preference.Source.F₂Of_of_compatible swapGreedy
      (ReasonableForF.compatible_indifferent π),
    AISafetyAtlas.Preference.Source.F₂Of_of_compatible greedyPlanner
      (ReasonableForF.compatible_indifferent π)]
  intro h
  exact swapGreedy_ne_greedyPlanner (congrArg Prod.fst h)

/-! ## A non-degenerate language c-reasonable for F at any planner -/

/-- The constant reward 1/2. -/
@[expose] public noncomputable def halfR : RewardFn Unit Bool := fun _ _ => 1 / 2

open Classical in
/-- Pairs whose reward is the constant ±1/2 cost 3; every other pair costs 0. -/
@[expose] public noncomputable def halfK (x : Pair Unit Bool) : ℕ :=
  if x.2 = halfR ∨ x.2 = -halfR then 3 else 0

private theorem halfK_eq_zero {x : Pair Unit Bool}
    (hv : x.2 () true = 0 ∨ x.2 () true = 1 ∨ x.2 () true = -1) : halfK x = 0 := by
  unfold halfK
  rw [if_neg]
  rintro (h | h) <;> rw [h] at hv <;> simp [halfR] at hv <;> norm_num at hv

private theorem rewardOf_true (π : Policy Unit Bool) :
    rewardOf π () true = 0 ∨ rewardOf π () true = 1 := by
  unfold rewardOf
  split_ifs <;> simp

private theorem halfK_op4 (x : Pair Unit Bool) : halfK (op4 x) = halfK x := by
  unfold halfK op4
  have e1 : -x.2 = halfR ↔ x.2 = -halfR := neg_eq_iff_eq_neg
  have e2 : -x.2 = -halfR ↔ x.2 = halfR := neg_inj
  simp only [e1, e2, or_comm]

/-- **A language c-reasonable for the F built from any planner g**, at c = 0,
with a pair of positive cost. -/
@[expose] public noncomputable def halfLanguage (g : Planner (RewardFn Unit Bool) (Policy Unit Bool)) :
    ReasonableForFOf g where
  KPair := halfK
  c := 0
  F_complexity_le i x := by
    match i with
    | 0 => rw [show halfK (FmapOf g 0 x) = 0 from halfK_eq_zero (Or.inl rfl)]; exact Nat.zero_le _
    | 1 =>
      rw [show halfK (FmapOf g 1 x) = 0 from halfK_eq_zero
        ((rewardOf_true (op3 x)).elim Or.inl fun h => Or.inr (Or.inl h))]
      exact Nat.zero_le _
    | 2 =>
      have h : halfK (FmapOf g 2 x) = 0 := by
        refine halfK_eq_zero ?_
        show -rewardOf (op3 x) () true = 0 ∨ -rewardOf (op3 x) () true = 1 ∨
          -rewardOf (op3 x) () true = -1
        rcases rewardOf_true (op3 x) with h | h <;> rw [h] <;> norm_num
      rw [h]; exact Nat.zero_le _
    | 3 => exact (halfK_op4 x).le

/-- The intended-looking competitor: the indifferent planner with the constant
reward 1/2, compatible with π and of cost 3. -/
@[expose] public noncomputable def halfPair (π : Policy Unit Bool) : Pair Unit Bool :=
  (indifferentPlanner π, halfR)

private theorem halfPair_compatible (π : Policy Unit Bool) :
    ReasonableForF.Compatible (halfPair π) π := rfl

/-- The constant-1/2 pair is not amongst the lowest: the indifferent pair with
the zero reward beats it by 3. -/
public theorem halfPair_not_amongLowest (g : Planner (RewardFn Unit Bool) (Policy Unit Bool))
    (π : Policy Unit Bool) :
    ¬ AmongLowestFor (halfLanguage g).KPair (halfLanguage g).c π (halfPair π) := by
  rintro ⟨-, h⟩
  have h0 := h (op1 (op5 π)) (ReasonableForF.compatible_indifferent π)
  have e3 : (halfLanguage g).KPair (halfPair π) = 3 := by
    show halfK (halfPair π) = 3
    unfold halfK halfPair
    simp
  have e0 : (halfLanguage g).KPair (op1 (op5 π)) = 0 := halfK_eq_zero (Or.inl rfl)
  have ec : (halfLanguage g).c = 0 := rfl
  rw [e3, e0, ec] at h0
  omega

/-! ## A language reasonable for the F of `swapGreedy` but not for the library's F -/

private theorem negate_inj {p q : Planner (RewardFn Unit Bool) (Policy Unit Bool)}
    (h : (fun R => p (-R)) = fun R => q (-R)) : p = q := by
  funext R
  have := congrFun h (-R)
  simpa only [neg_neg] using this

private theorem negate_negPlanner :
    (fun R => negPlanner (greedyPlanner : Planner (RewardFn Unit Bool) (Policy Unit Bool)) (-R)) =
      greedyPlanner := by
  funext R
  simp only [negPlanner, neg_neg]

open Classical in
/-- Pairs whose planner is `greedyPlanner` or its negation cost 5; every other
pair costs 0. -/
@[expose] public noncomputable def planK (x : Pair Unit Bool) : ℕ :=
  if x.1 = greedyPlanner ∨ x.1 = negPlanner greedyPlanner then 5 else 0

private theorem planK_op4 (x : Pair Unit Bool) : planK (op4 x) = planK x := by
  have e1 : ((fun R' => x.1 (-R')) = greedyPlanner) ↔ x.1 = negPlanner greedyPlanner := by
    constructor
    · intro h
      exact negate_inj (h.trans negate_negPlanner.symm)
    · intro h
      rw [h]
      exact negate_negPlanner
  have e2 : ((fun R' => x.1 (-R')) = negPlanner greedyPlanner) ↔ x.1 = greedyPlanner :=
    ⟨fun h => negate_inj h, fun h => by rw [h]; rfl⟩
  have e : ((fun R' => x.1 (-R')) = greedyPlanner ∨
      (fun R' => x.1 (-R')) = negPlanner greedyPlanner) ↔
      (x.1 = greedyPlanner ∨ x.1 = negPlanner greedyPlanner) := by
    rw [e1, e2, or_comm]
  unfold planK op4
  by_cases hx : x.1 = greedyPlanner ∨ x.1 = negPlanner greedyPlanner
  · rw [if_pos (e.2 hx), if_pos hx]
  · rw [if_neg (mt e.1 hx), if_neg hx]

private theorem planK_eq_zero {x : Pair Unit Bool}
    (h1 : x.1 0 () ≠ (greedyPlanner : Planner (RewardFn Unit Bool) (Policy Unit Bool)) 0 ()) :
    planK x = 0 := by
  unfold planK
  rw [if_neg]
  rintro (h | h)
  · exact h1 (by rw [h])
  · refine h1 ?_
    rw [h]
    show (greedyPlanner : Planner (RewardFn Unit Bool) (Policy Unit Bool)) (-0) () = _
    rw [neg_zero]

private theorem planK_indifferent (π : Policy Unit Bool) (R : RewardFn Unit Bool) :
    planK (indifferentPlanner π, R) = 0 := by
  unfold planK
  rw [if_neg]
  rintro (h | h)
  · have := congrFun h (rewardOf fun _ => !(π ()))
    rw [AISafetyAtlas.Preference.IsGreedy.apply_rewardOf
      AISafetyAtlas.Preference.isGreedy_greedyPlanner] at this
    have := congrFun this ()
    simp [indifferentPlanner] at this
  · have := congrFun h (-rewardOf fun _ => !(π ()))
    rw [AISafetyAtlas.Preference.IsGreedy.negPlanner_neg_rewardOf
      AISafetyAtlas.Preference.isGreedy_greedyPlanner] at this
    have := congrFun this ()
    simp [indifferentPlanner] at this

/-- **A language 0-reasonable for the F built from `swapGreedy`.** -/
@[expose] public noncomputable def planLanguage : ReasonableForFOf swapGreedy where
  KPair := planK
  c := 0
  F_complexity_le i x := by
    match i with
    | 0 =>
      rw [show planK (FmapOf swapGreedy 0 x) = 0 from planK_indifferent _ _]
      exact Nat.zero_le _
    | 1 =>
      rw [show planK (FmapOf swapGreedy 1 x) = 0 from planK_eq_zero swapGreedy_zero_ne]
      exact Nat.zero_le _
    | 2 =>
      have h : planK (FmapOf swapGreedy 2 x) = 0 := by
        refine planK_eq_zero ?_
        show swapGreedy (-0) () ≠ _
        rw [neg_zero]
        exact swapGreedy_zero_ne
      rw [h]; exact Nat.zero_le _
    | 3 => exact (planK_op4 x).le

/-- **`planK` is not 0-reasonable for the library's F**: at the indifferent pair
with the zero reward, the library's F₂ produces the pair of `greedyPlanner` and
R_π, which costs 5. So `ReasonableForF.proposition_seven` does not apply to this
complexity at c = 0, while `plan_proposition_seven` does. -/
public theorem planK_not_reasonable_greedyPlanner :
    ¬ ∀ (i : Fin 4) (x : Pair Unit Bool), planK (Fmap i x) ≤ planK x + 0 := by
  intro h
  have h1 := h 1 (op1 (op5 fun _ => true))
  have e5 : planK (Fmap 1 (op1 (op5 fun _ => true))) = 5 := by
    show planK (greedyPlanner, rewardOf fun _ => true) = 5
    unfold planK
    rw [if_pos (Or.inl rfl)]
  have e0 : planK (op1 (op5 fun _ => true)) = 0 := planK_indifferent _ _
  rw [e5, e0] at h1
  omega

/-- **Proposition 7 at `swapGreedy` in `planLanguage`**, a language the
statement over `greedyPlanner` cannot reach at c = 0. -/
public theorem plan_proposition_seven (π : Policy Unit Bool) :
    AmongLowestFor planK 0 π (op1 (op5 π)) ∧ AmongLowestFor planK 0 π (op2Of swapGreedy (op6 π)) ∧
      AmongLowestFor planK 0 π (op4 (op2Of swapGreedy (op6 π))) :=
  AISafetyAtlas.Preference.Source.ReasonableForFOf.proposition_seven_of_isGreedy
    planLanguage isGreedy_swapGreedy π

/-! ## Propositions 7 and 8 and Theorem 2 at `swapGreedy` -/

example : fComplexityOf (greedyPlanner (S := Unit) (A := Bool)) halfK = fComplexity halfK :=
  AISafetyAtlas.Preference.Source.fComplexityOf_greedyPlanner halfK

example : fComplexityOf swapGreedy halfK ≤ ((0 : ℕ) : ℝ) :=
  AISafetyAtlas.Preference.Source.ReasonableForFOf.fComplexityOf_le (halfLanguage swapGreedy)

example : fComplexityOf swapGreedy halfK ≤ ((0 : ℝ) : EReal) ↔
    ∀ (i : Fin 4) (x : Pair Unit Bool), (halfK (FmapOf swapGreedy i x) : ℝ) ≤ halfK x + 0 :=
  AISafetyAtlas.Preference.Source.fComplexityOf_le_iff swapGreedy halfK 0

example : fComplexityOf swapGreedy halfK ≤ (((0 : ℕ) : ℝ) : EReal) :=
  (AISafetyAtlas.Preference.Source.fComplexityOf_le_iff_nat swapGreedy halfK 0).2
    (halfLanguage swapGreedy).F_complexity_le

example : 0 ≤ fComplexityOf swapGreedy halfK :=
  AISafetyAtlas.Preference.Source.fComplexityOf_nonneg swapGreedy halfK

example (π : Policy Unit Bool) :
    AmongLowestFor halfK 0 π (op2Of swapGreedy (op6 π)) :=
  AISafetyAtlas.Preference.Source.greedy_amongLowestFor_of_isGreedy isGreedy_swapGreedy halfK 0
    ((halfLanguage swapGreedy).F_complexity_le 1) π

example (π : Policy Unit Bool) :
    AmongLowestFor halfK 0 π (op4 (op2Of swapGreedy (op6 π))) :=
  AISafetyAtlas.Preference.Source.antirational_amongLowestFor_of_isGreedy isGreedy_swapGreedy
    halfK 0 ((halfLanguage swapGreedy).F_complexity_le 2) π

example (π : Policy Unit Bool) :
    AmongLowestFor halfK 0 π (op1 (op5 π)) ∧ AmongLowestFor halfK 0 π (op2Of swapGreedy (op6 π)) ∧
      AmongLowestFor halfK 0 π (op4 (op2Of swapGreedy (op6 π))) :=
  AISafetyAtlas.Preference.Source.proposition_seven_of_bounds_of_isGreedy isGreedy_swapGreedy
    halfK 0 (halfLanguage swapGreedy).F_complexity_le π

/-- **Proposition 7 at `swapGreedy`**, in a language where the constant-1/2
pair is not amongst the lowest. -/
public theorem swap_proposition_seven (π : Policy Unit Bool) :
    AmongLowestFor (halfLanguage swapGreedy).KPair (halfLanguage swapGreedy).c π (op1 (op5 π)) ∧
      AmongLowestFor (halfLanguage swapGreedy).KPair (halfLanguage swapGreedy).c π
        (op2Of swapGreedy (op6 π)) ∧
      AmongLowestFor (halfLanguage swapGreedy).KPair (halfLanguage swapGreedy).c π
        (op4 (op2Of swapGreedy (op6 π))) :=
  AISafetyAtlas.Preference.Source.ReasonableForFOf.proposition_seven_of_isGreedy
    (halfLanguage swapGreedy) isGreedy_swapGreedy π

/-- `amongLowestFor_iff_amongLowest` at the constant-1/2 pair. -/
example (π : Policy Unit Bool) :
    AmongLowestFor halfK 0 π (halfPair π) ↔
      AmongLowest halfK (0 : ℕ) {y | ReasonableForF.Compatible y π} (halfPair π) :=
  AISafetyAtlas.Preference.amongLowestFor_iff_amongLowest halfK 0 π (halfPair π)

/-- **Proposition 8 at `swapGreedy`**, at the constant-1/2 pair. -/
public theorem swap_proposition_eight (π : Policy Unit Bool) :
    ReasonableForF.Compatible (F₄ (halfPair π)) π ∧
      halfK (F₄ (halfPair π)) ≤ halfK (halfPair π) + 0 ∧
      halfK (halfPair π) ≤ halfK (F₄ (halfPair π)) + 0 :=
  AISafetyAtlas.Preference.Source.ReasonableForFOf.proposition_eight_any_planner
    (halfLanguage swapGreedy) (halfPair_compatible π)

example (π : Policy Unit Bool) :
    ReasonableForF.Compatible (F₄ (halfPair π)) π ∧
      ComparableComplexity halfK ((0 : ℕ) : ℝ) (halfPair π) (F₄ (halfPair π)) :=
  AISafetyAtlas.Preference.Source.ReasonableForFOf.proposition_eight_comparable_any_planner
    (halfLanguage swapGreedy) (halfPair_compatible π)

/-- **The conditional Theorem 2 at `swapGreedy`, with its hypothesis
inhabited**: the three degenerate pairs built from `swapGreedy` are strictly
simpler than the constant-1/2 pair. -/
public theorem swap_theorem_two (π : Policy Unit Bool) :
    halfK (op1 (op5 π)) < halfK (halfPair π) ∧
      halfK (op2Of swapGreedy (op6 π)) < halfK (halfPair π) ∧
      halfK (op4 (op2Of swapGreedy (op6 π))) < halfK (halfPair π) :=
  AISafetyAtlas.Preference.Source.ReasonableForFOf.theorem_two_conditional_of_isGreedy
    (halfLanguage swapGreedy) isGreedy_swapGreedy π (halfPair π) (halfPair_compatible π)
    (halfPair_not_amongLowest swapGreedy π)

/-! ## The bridges to the `greedyPlanner` structure -/

/-- The zero language of `AISafetyAtlas.Examples.Preference.zeroLanguage`,
viewed at `ReasonableForFOf greedyPlanner`, round-trips. -/
example : (AISafetyAtlas.Examples.Preference.zeroLanguage).toReasonableForFOf.toReasonableForF =
    AISafetyAtlas.Examples.Preference.zeroLanguage :=
  AISafetyAtlas.Preference.Source.ReasonableForF.toReasonableForF_toReasonableForFOf _

example (π : Policy Bool Bool) (x : Pair Bool Bool) :
    AISafetyAtlas.Examples.Preference.zeroLanguage.AmongLowestCompatible π x ↔
      AmongLowestFor AISafetyAtlas.Examples.Preference.zeroLanguage.toReasonableForFOf.KPair
        AISafetyAtlas.Examples.Preference.zeroLanguage.toReasonableForFOf.c π x :=
  AISafetyAtlas.Preference.Source.ReasonableForF.amongLowestCompatible_iff_toReasonableForFOf _ π x

/-- `ReasonableForF.proposition_seven` recovered from the statement at every
greedy planner, through the bridges. -/
example (L : ReasonableForF Bool Bool) (π : Policy Bool Bool) :
    L.AmongLowestCompatible π (op2 (op6 π)) :=
  (AISafetyAtlas.Preference.Source.ReasonableForFOf.proposition_seven_of_isGreedy
    L.toReasonableForFOf AISafetyAtlas.Preference.isGreedy_greedyPlanner π).2.1

/-! ## Conjecture 9 at `swapGreedy` -/

example (Human : Policy Unit Bool → Prop) (Reasonable : Pair Unit Bool → Prop) :
    ConjectureNineOf greedyPlanner (fun L => (fun _ => True) L.toReasonableForF) Human Reasonable ↔
      ConjectureNine (fun _ => True) Human Reasonable :=
  AISafetyAtlas.Preference.Source.conjectureNineOf_greedyPlanner_iff (fun _ => True) Human Reasonable

/-- **Conjecture 9 at `swapGreedy` holds for a narrow choice of the informal
predicates** (reasonable language `halfLanguage`, one human policy, the
constant-1/2 pair as the reasonable pair), so its consequences have inhabited
hypotheses. -/
public theorem swap_conjectureNineOf (π : Policy Unit Bool) :
    ConjectureNineOf swapGreedy (fun L => L = halfLanguage swapGreedy) (fun σ => σ = π)
      (fun x => x = halfPair π) := by
  rintro L rfl σ rfl x rfl _
  exact halfPair_not_amongLowest swapGreedy σ

example (π : Policy Unit Bool) :
    halfK (op1 (op5 π)) < halfK (halfPair π) ∧
      halfK (op2Of swapGreedy (op6 π)) < halfK (halfPair π) ∧
      halfK (op4 (op2Of swapGreedy (op6 π))) < halfK (halfPair π) :=
  AISafetyAtlas.Preference.Source.ConjectureNineOf.theorem_two_of_isGreedy isGreedy_swapGreedy
    (swap_conjectureNineOf π) rfl rfl rfl (halfPair_compatible π)

/-- If the reasonable pairs admit an indifferent pair, Conjecture 9 at
`swapGreedy` fails. -/
example (π : Policy Unit Bool) :
    ¬ ConjectureNineOf swapGreedy (fun _ => True) (fun _ => True) (fun _ => True) :=
  AISafetyAtlas.Preference.Source.not_conjectureNineOf_of_indifferent
    (L := halfLanguage swapGreedy) trivial (π := π) trivial trivial

/-! ## Proposition 10 at any greedy planner, in the toy timed language -/

namespace Timed

open AISafetyAtlas.Examples.Preference.TimedComplexity

variable {S A : Type} [Fintype A] [Nonempty A] [DecidableEq A]

/-- A reward-function planner g, as a black-box toy code, read on reward code. -/
@[expose] public noncomputable def onCode (g : Planner (RewardFn S A) (Policy S A))
    (β : ToyCode S A) : Policy S A :=
  match toyRew (toyDen β) with
  | some R => g R
  | none => g 0

private theorem onCode_spec (g : Planner (RewardFn S A) (Policy S A)) (β : ToyCode S A)
    (R : RewardFn S A) (h : (toyLanguage (S := S) (A := A)).GenReward β R) :
    onCode g β = g R := by
  simp only [onCode]
  rw [show toyRew (toyDen β) = some R from h]

private theorem genCodePlanner_plan (g : Planner (RewardFn S A) (Policy S A)) :
    (toyCodePlanning (S := S) (A := A)).GenCodePlanner (.plan g) (onCode g) := by
  intro β R h
  simp [toyDen, toyApply, onCode, h]

/-- **Proposition 10, second sentence, greedy pair, at any greedy planner** in
the toy language, with the planner's code a black box. -/
public theorem toy_proposition_ten_greedy_of_isGreedy
    {g : Planner (RewardFn S A) (Policy S A)} (hg : IsGreedy g) (π : Policy S A) :
    AmongLowestIn (fun y => TimedLanguage.CodeCompatible toyLanguage y π)
        (CodePlanning.codeKt toyCodePlanning)
        ((1 : ℕ) + 3 * (1 : ℕ) + ENNReal.ofReal (Real.log (1 + (1 : ℕ))))
        (onCode g, rewardOf π) ∧
      AmongLowestIn (fun y => TimedLanguage.CodeCompatible toyLanguage y π)
        (CodePlanning.codeKT toyCodePlanning) ((1 : ℕ) + 4 * (1 : ℕ))
        (onCode g, rewardOf π) :=
  AISafetyAtlas.Preference.Source.CodePlanning.proposition_ten_greedy_of_isGreedy
    toyCodePlanning hg (toyWrapping false) (genCodePlanner_plan g) (onCode_spec g) π

/-- **Proposition 10, second sentence, anti-rational pair, at any greedy
planner** in the toy language. -/
public theorem toy_proposition_ten_antigreedy_of_isGreedy
    {g : Planner (RewardFn S A) (Policy S A)} (hg : IsGreedy g) (π : Policy S A) :
    AmongLowestIn (fun y => TimedLanguage.CodeCompatible toyLanguage y π)
        (CodePlanning.codeKt toyCodePlanning)
        ((1 : ℕ) + 3 * (1 : ℕ) + ENNReal.ofReal (Real.log (1 + (1 : ℕ))))
        (onCode (negPlanner g), -rewardOf π) ∧
      AmongLowestIn (fun y => TimedLanguage.CodeCompatible toyLanguage y π)
        (CodePlanning.codeKT toyCodePlanning) ((1 : ℕ) + 4 * (1 : ℕ))
        (onCode (negPlanner g), -rewardOf π) :=
  AISafetyAtlas.Preference.Source.CodePlanning.proposition_ten_antigreedy_of_isGreedy
    toyCodePlanning hg (toyWrapping true) (genCodePlanner_plan (negPlanner g))
    (fun β R h => onCode_spec (negPlanner g) β R h) π

end Timed

/-- Proposition 10's greedy pair at `swapGreedy`, a greedy planner other than
`greedyPlanner`. -/
example (π : Policy Unit Bool) :=
  Timed.toy_proposition_ten_greedy_of_isGreedy isGreedy_swapGreedy π

example (π : Policy Unit Bool) :=
  Timed.toy_proposition_ten_antigreedy_of_isGreedy isGreedy_swapGreedy π

/-- Comparable complexity at a complexity that may be infinite: a complexity that is
⊤ on pairs whose reward is 0 at ((), true) and 0 elsewhere. The pair
(greedyPlanner, 0) is comparable with no pair of finite complexity, here
(greedyPlanner, 1). -/
example : ¬ AISafetyAtlas.Preference.ComparableComplexityIn
    (fun z : Pair Unit Bool => if z.2 () true = 0 then (⊤ : ENat) else 0) ((0 : ℕ) : ENat)
    (greedyPlanner, 0) (greedyPlanner, 1) :=
  AISafetyAtlas.Preference.not_comparableComplexityIn_top _ 0 _ _ (by simp) (by simp)

/-- At natural values the `ENat` relation is `ComparableComplexity`: two pairs of
complexity 0 are comparable at c = 0. -/
example : AISafetyAtlas.Preference.ComparableComplexityIn
    (fun z : Pair Unit Bool => ((fun _ => 0 : Pair Unit Bool → ℕ) z : ENat)) ((0 : ℕ) : ENat)
    (greedyPlanner, 0) (greedyPlanner, 1) :=
  (AISafetyAtlas.Preference.comparableComplexityIn_iff (fun _ => 0) 0 _ _).mpr
    ((AISafetyAtlas.Preference.comparableComplexity_iff _ 0 _ _).mpr ⟨le_refl _, le_refl _⟩)

end AISafetyAtlas.Examples.Preference.AnyGreedy
