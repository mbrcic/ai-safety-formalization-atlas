module

public import AISafetyAtlas.Preference.SourceComplexity
public import Mathlib.Data.ENat.Basic

/-!
# The Armstrong–Mindermann results at every greedy planner

Armstrong and Mindermann (§5.1.1, PDF p. 5) define the greedy planner only by
the maximisation property, *"p_g(R)(s) = argmax_a R(s, a)"*, and print no tie
rule (a recorded silence). The library's `AISafetyAtlas.Preference.greedyPlanner`
is one maximiser selection, made by choice, and the objects built on it
(`AISafetyAtlas.Preference.op2`, `AISafetyAtlas.Preference.Source.Fmap`,
`AISafetyAtlas.Preference.Source.fComplexity`,
`AISafetyAtlas.Preference.Source.ReasonableForF`) fix that one selection.

This module states the same objects and results for **any** greedy planner:
`IsGreedy` applied to g says only that g(R)(s) is a maximiser of R(s, ·), so g may break
ties in any way, including by state or by the whole reward table. Each object
takes g as a parameter and the existing one is its instance at
`AISafetyAtlas.Preference.greedyPlanner` (`op2Of_greedyPlanner`,
`Source.FmapOf_greedyPlanner`, `Source.fComplexityOf_greedyPlanner`,
`Source.ReasonableForF.toReasonableForFOf`).

The one fact the results need about g is that R_π has a unique maximiser at
every state, so every greedy planner returns π on it
(`IsGreedy.apply_rewardOf`). A greedy planner on print's bounded rewards alone
extends to one on all real rewards (`IsGreedy.exists_extend`), so every
completion of print's p_g is covered.

## Explicit non-claims

- **Not** a claim that the greedy planner is unique: at a tied reward, two
  greedy planners may differ, and the witnesses exhibit one that differs from
  `AISafetyAtlas.Preference.greedyPlanner` at the zero reward.
- **Not** a construction of a nontrivial reasonable language; as in
  `AISafetyAtlas.Preference.SourceComplexity`, the language is a hypothesis.
-/

namespace AISafetyAtlas.Preference

variable {S A : Type*}

/-! ## Greedy planners -/

/-- **A greedy planner** (Armstrong and Mindermann, §5.1.1, PDF p. 5: *"The
greedy planner p_g acts by taking the action that maximises the immediate reward
in the current state"*, p_g(R)(s) = argmax_a R(s, a)): at every reward and
state, no action scores above the one the planner takes. No tie rule is
imposed, so this is print's definition at every tie rule. -/
@[expose] public def IsGreedy (g : Planner (RewardFn S A) (Policy S A)) : Prop :=
  ∀ (R : RewardFn S A) (s : S) (a : A), R s a ≤ R s (g R s)

/-- The library's choice-based `greedyPlanner` is a greedy planner. -/
public theorem isGreedy_greedyPlanner [Fintype A] [Nonempty A] :
    IsGreedy (greedyPlanner (S := S) (A := A)) :=
  fun R s a => by rw [greedyPlanner_apply]; exact greedyAction_max R s a

namespace IsGreedy

variable {g : Planner (RewardFn S A) (Policy S A)}

/-- **Every greedy planner recovers π from R_π** (print's p_g(R_π) = π, §5.1.1):
R_π has the unique maximiser π(s) at each state, so the tie rule never matters
there. -/
public theorem apply_rewardOf [DecidableEq A] (hg : IsGreedy g) (π : Policy S A) :
    g (rewardOf π) = π := by
  funext s
  by_contra hne
  have hmax := hg (rewardOf π) s (π s)
  have h1 : rewardOf π s (π s) = 1 := by simp [rewardOf]
  have h0 : rewardOf π s (g (rewardOf π) s) = 0 := by simp [rewardOf, hne]
  rw [h1, h0] at hmax
  exact absurd hmax (not_le.mpr zero_lt_one)

/-- **(−p_g)(−R_π) = π for every greedy planner** (print's Definition 5 and
§5.1.1). -/
public theorem negPlanner_neg_rewardOf [DecidableEq A] (hg : IsGreedy g) (π : Policy S A) :
    negPlanner g (-rewardOf π) = π := by
  rw [negPlanner, neg_neg, hg.apply_rewardOf]

/-- **The anti-greedy planner takes a minimiser** (print, §5.1.1:
*"−p_g(R)(s) = argmin_a R(s, a)"*): for every greedy planner g, the planner −g
of Definition 5 takes, at every reward and state, an action no action scores
below. -/
public theorem negPlanner_min (hg : IsGreedy g) (R : RewardFn S A) (s : S) (a : A) :
    R s (negPlanner g R s) ≤ R s a := by
  have h := hg (-R) s a
  simp only [Pi.neg_apply, neg_le_neg_iff] at h
  exact h

end IsGreedy

/-- **Every greedy planner on print's reward space extends to a greedy planner
on all real rewards.** Print's p_g is a map from ℛ = [-1, 1]^{S×A} to policies
(§3, §5.1.1); any such map taking a maximiser at every bounded reward and state
is the restriction of some g satisfying `IsGreedy`, so statements over every greedy
g cover every completion of print's p_g. -/
public theorem IsGreedy.exists_extend [Fintype A] [Nonempty A]
    (p : BoundedRewardFn S A → Policy S A)
    (hp : ∀ (R : BoundedRewardFn S A) (s : S) (a : A), R.1 s a ≤ R.1 s (p R s)) :
    ∃ g : Planner (RewardFn S A) (Policy S A), IsGreedy g ∧
      ∀ R : BoundedRewardFn S A, g R.1 = p R := by
  classical
  refine ⟨fun R => if h : IsBoundedReward R then p ⟨R, h⟩ else greedyPlanner R,
    fun R s a => ?_, fun R => ?_⟩
  · by_cases h : IsBoundedReward R
    · simp only [h, dite_true]
      exact hp ⟨R, h⟩ s a
    · simp only [h, dite_false]
      exact isGreedy_greedyPlanner R s a
  · simp only [R.2, dite_true]

/-- **Lemma 6 at every greedy planner** (Armstrong and Mindermann, Lemma 6,
PDF p. 6: *"The pairs (p_π, 0), (p_g, R_π), and (−p_g, −R_π) are all compatible
with π"*), for any greedy planner g, whatever its tie rule.
`AISafetyAtlas.Preference.lemma_six` is the instance g := `greedyPlanner`. -/
public theorem lemma_six_of_isGreedy [DecidableEq A] {g : Planner (RewardFn S A) (Policy S A)}
    (hg : IsGreedy g) (π : Policy S A) :
    Explains (indifferentPlanner π) (0 : RewardFn S A) π ∧
      Explains g (rewardOf π) π ∧
      Explains (negPlanner g) (-rewardOf π) π :=
  ⟨degenerate_indifferent π 0, hg.apply_rewardOf π, hg.negPlanner_neg_rewardOf π⟩

/-! ## The basic operation f₂ at any planner -/

/-- **f₂(R) = (p_g, R) at a planner g** (Armstrong and Mindermann, §5.1.2,
PDF p. 6, the second basic operation), for any planner g; print's is g a greedy
planner. `op2` is the instance g := `greedyPlanner` (`op2Of_greedyPlanner`). -/
@[expose] public def op2Of (g : Planner (RewardFn S A) (Policy S A)) (R : RewardFn S A) :
    Pair S A := (g, R)

/-- The library's `op2` is `op2Of` at `greedyPlanner`. -/
public theorem op2Of_greedyPlanner [Fintype A] [Nonempty A] :
    op2Of (greedyPlanner (S := S) (A := A)) = op2 := rfl

/-- (p_g, R_π) = f₂(f₆(π)) is compatible with π, for every greedy planner. -/
public theorem op3_op2Of_op6 [DecidableEq A] {g : Planner (RewardFn S A) (Policy S A)}
    (hg : IsGreedy g) (π : Policy S A) : op3 (op2Of g (op6 π)) = π :=
  hg.apply_rewardOf π

/-- (−p_g, −R_π) = f₄(f₂(f₆(π))) is compatible with π, for every greedy
planner. -/
public theorem op3_op4_op2Of_op6 [DecidableEq A] {g : Planner (RewardFn S A) (Policy S A)}
    (hg : IsGreedy g) (π : Policy S A) : op3 (op4 (op2Of g (op6 π))) = π :=
  hg.negPlanner_neg_rewardOf π

/-! ## Amongst the lowest, at any natural complexity -/

/-- **Amongst the lowest compatible pairs is print's `am-lowest` at the
compatible set**, for any natural-valued complexity and constant: the
structure-free `AISafetyAtlas.Preference.Source.AmongLowestFor` is
`AmongLowest` at the set of pairs compatible with π. No planner enters. -/
public theorem amongLowestFor_iff_amongLowest (K : Pair S A → ℕ) (c : ℕ) (π : Policy S A)
    (x : Pair S A) :
    Source.AmongLowestFor K c π x ↔
      AmongLowest K c {y | Source.ReasonableForF.Compatible y π} x := by
  unfold Source.AmongLowestFor AmongLowest
  simp only [Set.mem_ofPred_eq]
  refine and_congr Iff.rfl (forall_congr' fun y => imp_congr_right fun _ => ?_)
  exact_mod_cast Iff.rfl

/-- **Comparable complexity at a complexity that may be infinite** (Armstrong and
Mindermann, §5.1, am-comparable): the two one-sided bounds, for a complexity
valued in any type with addition and an order. At ℕ∞, a pair with no
description in the language (Kolmogorov complexity ⊤, as for a reward table
with an irrational entry under exact coding) is comparable with no described
pair, as print's ‖K_L(p, R) − K_L(p', R')‖ ≤ c requires.
`comparableComplexityIn_iff` recovers `ComparableComplexity` at natural values. -/
@[expose] public def ComparableComplexityIn {α : Type*} [Add α] [LE α] (K : Pair S A → α)
    (c : α) (x y : Pair S A) : Prop :=
  K x ≤ K y + c ∧ K y ≤ K x + c

/-- At a natural-valued complexity and constant, the ℕ∞ relation is
`ComparableComplexity`. -/
public theorem comparableComplexityIn_iff (K : Pair S A → ℕ) (c : ℕ) (x y : Pair S A) :
    ComparableComplexityIn (fun z => (K z : ENat)) (c : ENat) x y ↔ ComparableComplexity K c x y := by
  rw [comparableComplexity_iff]
  show (K x : ENat) ≤ K y + c ∧ (K y : ENat) ≤ K x + c ↔ _
  norm_cast

/-- A pair of complexity ⊤ is comparable with no pair of finite complexity, at
any finite constant. -/
public theorem not_comparableComplexityIn_top (K : Pair S A → ENat) (c : ℕ) (x y : Pair S A)
    (hx : K x = ⊤) (hy : K y ≠ ⊤) : ¬ ComparableComplexityIn K (c : ENat) x y := by
  rintro ⟨h, -⟩
  rw [hx, top_le_iff, ENat.add_eq_top] at h
  exact h.elim hy (ENat.natCast_ne_top c)

end AISafetyAtlas.Preference

namespace AISafetyAtlas.Preference.Source

open AISafetyAtlas.Preference

variable {S A : Type*} [DecidableEq A]

/-! ## The composite operations at any planner -/

/-- **F₂ = f₂ ∘ f₆ ∘ f₃ at a planner g** (§5.1.2, PDF p. 6). -/
@[expose] public def F₂Of (g : Planner (RewardFn S A) (Policy S A)) (x : Pair S A) :
    Pair S A := op2Of g (op6 (op3 x))

/-- **F₃ = f₄ ∘ f₂ ∘ f₆ ∘ f₃ at a planner g** (§5.1.2, PDF p. 6). -/
@[expose] public def F₃Of (g : Planner (RewardFn S A) (Policy S A)) (x : Pair S A) :
    Pair S A := op4 (op2Of g (op6 (op3 x)))

/-- **The family F = {F₁, F₂, F₃, F₄} at a planner g** (Armstrong and
Mindermann, §5.1.2, PDF p. 6), as one indexed operation. F₁ and F₄ do not
involve the greedy planner; F₂ and F₃ embed g. -/
@[expose] public def FmapOf (g : Planner (RewardFn S A) (Policy S A)) :
    Fin 4 → Pair S A → Pair S A
  | 0 => F₁
  | 1 => F₂Of g
  | 2 => F₃Of g
  | 3 => F₄

/-- The library's `F₂` is `F₂Of` at `greedyPlanner`. -/
public theorem F₂Of_greedyPlanner [Fintype A] [Nonempty A] :
    F₂Of (greedyPlanner (S := S) (A := A)) = F₂ := rfl

/-- The library's `F₃` is `F₃Of` at `greedyPlanner`. -/
public theorem F₃Of_greedyPlanner [Fintype A] [Nonempty A] :
    F₃Of (greedyPlanner (S := S) (A := A)) = F₃ := rfl

/-- The library's `Fmap` is `FmapOf` at `greedyPlanner`. -/
public theorem FmapOf_greedyPlanner [Fintype A] [Nonempty A] :
    FmapOf (greedyPlanner (S := S) (A := A)) = Fmap := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 => rfl

omit [DecidableEq A] in
/-- F₁(p, R) = (p_π, 0) for any π-compatible pair; F₁ involves no planner
choice. Restated beside the others for the planner-parametrised family. -/
public theorem F₁_of_compatible_any_planner {x : Pair S A} {π : Policy S A}
    (h : ReasonableForF.Compatible x π) : F₁ x = op1 (op5 π) :=
  ReasonableForF.F₁_of_compatible h

/-- F₂(p, R) = (g, R_π) for any π-compatible pair, at any planner g. -/
public theorem F₂Of_of_compatible (g : Planner (RewardFn S A) (Policy S A)) {x : Pair S A}
    {π : Policy S A} (h : ReasonableForF.Compatible x π) : F₂Of g x = op2Of g (op6 π) := by
  unfold F₂Of
  rw [show op3 x = π from h]

/-- F₃(p, R) = (−g, −R_π) for any π-compatible pair, at any planner g. -/
public theorem F₃Of_of_compatible (g : Planner (RewardFn S A) (Policy S A)) {x : Pair S A}
    {π : Policy S A} (h : ReasonableForF.Compatible x π) :
    F₃Of g x = op4 (op2Of g (op6 π)) := by
  unfold F₃Of
  rw [show op3 x = π from h]

/-! ## The F-complexity at any planner -/

/-- **The F-complexity of a language at a planner g** (Armstrong and
Mindermann, §5.1.2, `am-f-complexity`, PDF p. 6):
max over pairs and Fᵢ of K(Fᵢ(p, R)) − K(p, R), as an `EReal` supremum, with F
built from g. `fComplexity` is the instance g := `greedyPlanner`
(`fComplexityOf_greedyPlanner`). -/
@[expose] public noncomputable def fComplexityOf (g : Planner (RewardFn S A) (Policy S A))
    (K : Pair S A → ℕ) : EReal :=
  ⨆ (i : Fin 4) (x : Pair S A), ((((K (FmapOf g i x) : ℝ) - K x : ℝ)) : EReal)

/-- The library's `fComplexity` is `fComplexityOf` at `greedyPlanner`. -/
public theorem fComplexityOf_greedyPlanner [Fintype A] [Nonempty A] (K : Pair S A → ℕ) :
    fComplexityOf (greedyPlanner (S := S) (A := A)) K = fComplexity K := by
  rw [fComplexityOf, FmapOf_greedyPlanner, fComplexity]

/-- The F-complexity at g is at most a real c exactly when every Fᵢ raises
every pair's complexity by at most c. -/
public theorem fComplexityOf_le_iff (g : Planner (RewardFn S A) (Policy S A))
    (K : Pair S A → ℕ) (c : ℝ) :
    fComplexityOf g K ≤ (c : EReal) ↔
      ∀ (i : Fin 4) (x : Pair S A), (K (FmapOf g i x) : ℝ) ≤ K x + c := by
  unfold fComplexityOf
  simp only [iSup_le_iff, EReal.coe_le_coe_iff]
  refine forall_congr' fun i => forall_congr' fun x => ?_
  constructor <;> intro h <;> linarith

/-- **c-reasonable for F, at a planner g**: the F-complexity is at most a
natural c exactly when the natural bound holds for every Fᵢ and pair. -/
public theorem fComplexityOf_le_iff_nat (g : Planner (RewardFn S A) (Policy S A))
    (K : Pair S A → ℕ) (c : ℕ) :
    fComplexityOf g K ≤ ((c : ℝ) : EReal) ↔
      ∀ (i : Fin 4) (x : Pair S A), K (FmapOf g i x) ≤ K x + c := by
  rw [fComplexityOf_le_iff]
  refine forall_congr' fun i => forall_congr' fun x => ?_
  exact_mod_cast Iff.rfl

/-- **Footnote 10 at every planner**: the F-complexity is non-negative,
because F₄ is an involution. No greediness is used, and the pair type is
nonempty because it contains (g, 0). -/
public theorem fComplexityOf_nonneg (g : Planner (RewardFn S A) (Policy S A))
    (K : Pair S A → ℕ) : 0 ≤ fComplexityOf g K := by
  let x : Pair S A := (g, 0)
  unfold fComplexityOf
  by_cases h : K x ≤ K (F₄ x)
  · refine le_iSup₂_of_le (3 : Fin 4) x ?_
    rw [show (FmapOf g 3 : Pair S A → Pair S A) = F₄ from rfl, ← EReal.coe_zero,
      EReal.coe_le_coe_iff]
    have : (K x : ℝ) ≤ K (F₄ x) := by exact_mod_cast h
    linarith
  · refine le_iSup₂_of_le (3 : Fin 4) (F₄ x) ?_
    rw [show (FmapOf g 3 : Pair S A → Pair S A) = F₄ from rfl, ReasonableForF.F₄_F₄,
      ← EReal.coe_zero, EReal.coe_le_coe_iff]
    have : (K (F₄ x) : ℝ) ≤ K x := by exact_mod_cast (le_of_not_ge h)
    linarith

/-! ## Proposition 7 at any measure and any greedy planner -/

/-- **Proposition 7, second pair, at every greedy planner, from the F₂ bound
alone**: under any measure where F₂ (built from g) raises complexity by at most
c, the pair (g, R_π) is amongst the lowest compatible pairs. -/
public theorem greedy_amongLowestFor_of_isGreedy {α : Type*} [Add α] [LE α]
    {g : Planner (RewardFn S A) (Policy S A)} (hg : IsGreedy g) (K : Pair S A → α) (c : α)
    (h₂ : ∀ x : Pair S A, K (F₂Of g x) ≤ K x + c) (π : Policy S A) :
    AmongLowestFor K c π (op2Of g (op6 π)) := by
  refine ⟨op3_op2Of_op6 hg π, fun y hy => ?_⟩
  have hb := h₂ y
  rwa [F₂Of_of_compatible g hy] at hb

/-- **Proposition 7, third pair, at every greedy planner, from the F₃ bound
alone.** -/
public theorem antirational_amongLowestFor_of_isGreedy {α : Type*} [Add α] [LE α]
    {g : Planner (RewardFn S A) (Policy S A)} (hg : IsGreedy g) (K : Pair S A → α) (c : α)
    (h₃ : ∀ x : Pair S A, K (F₃Of g x) ≤ K x + c) (π : Policy S A) :
    AmongLowestFor K c π (op4 (op2Of g (op6 π))) := by
  refine ⟨op3_op4_op2Of_op6 hg π, fun y hy => ?_⟩
  have hb := h₃ y
  rwa [F₃Of_of_compatible g hy] at hb

/-- **Proposition 7 at any measure and every greedy planner** (Armstrong and
Mindermann, Proposition 7, PDF p. 7, with the measure widened as appendix A's
Proposition 10 needs): for any greedy planner g, whatever its tie rule, any K
valued in a type with addition and order, and any c such that every composite of
the family F built from g raises K by at most c, the three degenerate pairs
(p_π, 0), (g, R_π) and (−g, −R_π) are amongst the lowest-complexity pairs
compatible with π. `proposition_seven_of_bounds` is the instance
g := `greedyPlanner`. -/
public theorem proposition_seven_of_bounds_of_isGreedy {α : Type*} [Add α] [LE α]
    {g : Planner (RewardFn S A) (Policy S A)} (hg : IsGreedy g) (K : Pair S A → α) (c : α)
    (hF : ∀ (i : Fin 4) (x : Pair S A), K (FmapOf g i x) ≤ K x + c) (π : Policy S A) :
    AmongLowestFor K c π (op1 (op5 π)) ∧ AmongLowestFor K c π (op2Of g (op6 π)) ∧
      AmongLowestFor K c π (op4 (op2Of g (op6 π))) :=
  ⟨indifferent_amongLowestFor K c (hF 0) π, greedy_amongLowestFor_of_isGreedy hg K c (hF 1) π,
    antirational_amongLowestFor_of_isGreedy hg K c (hF 2) π⟩

/-! ## c-reasonable languages for F at a planner -/

/-- **A c-reasonable language for F, with F built from the planner g**
(Armstrong and Mindermann, §5.1.2, PDF p. 6: *"L being a c-reasonable language
for F: that the F-complexity of L is at most c"*): a natural complexity on
pairs whose F-complexity at g is at most c (`ReasonableForFOf.fComplexityOf_le`).
`ReasonableForF` is the case g := `greedyPlanner`
(`ReasonableForF.toReasonableForFOf`, `ReasonableForFOf.toReasonableForF`). -/
public structure ReasonableForFOf (g : Planner (RewardFn S A) (Policy S A)) where
  /-- Complexity of a planner/reward pair. -/
  KPair : Pair S A → ℕ
  /-- The bound on the F-complexity. -/
  c : ℕ
  /-- The F-complexity at g is at most c. -/
  F_complexity_le : ∀ (i : Fin 4) (x : Pair S A), KPair (FmapOf g i x) ≤ KPair x + c

/-- A `ReasonableForF` language is a `ReasonableForFOf` language at
`greedyPlanner`, with the same complexity and constant. -/
@[expose] public def ReasonableForF.toReasonableForFOf [Fintype A] [Nonempty A]
    (L : ReasonableForF S A) : ReasonableForFOf (greedyPlanner (S := S) (A := A)) where
  KPair := L.KPair
  c := L.c
  F_complexity_le := by rw [FmapOf_greedyPlanner]; exact L.F_complexity_le

/-- A `ReasonableForFOf` language at `greedyPlanner` is a `ReasonableForF`
language, with the same complexity and constant. -/
@[expose] public def ReasonableForFOf.toReasonableForF [Fintype A] [Nonempty A]
    (L : ReasonableForFOf (greedyPlanner (S := S) (A := A))) : ReasonableForF S A where
  KPair := L.KPair
  c := L.c
  F_complexity_le := by rw [← FmapOf_greedyPlanner]; exact L.F_complexity_le

namespace ReasonableForFOf

variable {g : Planner (RewardFn S A) (Policy S A)} (L : ReasonableForFOf g)

/-- A c-reasonable language for F at g has F-complexity at g at most c. -/
public theorem fComplexityOf_le : fComplexityOf g L.KPair ≤ ((L.c : ℝ) : EReal) :=
  (fComplexityOf_le_iff_nat g L.KPair L.c).mpr L.F_complexity_le

/-- **Proposition 7 at every greedy planner** (Armstrong and Mindermann,
Proposition 7, PDF p. 7: *"If π̇ is the human policy, c defines a reasonable
measure of comparable complexity, and L is a c-reasonable language for F, then
the degenerate planner-reward pairs (p_π̇, 0), (p_g, R_π̇), and (−p_g, −R_π̇) are
amongst the pairs of lowest complexity among the pairs compatible with π̇"*).
For any greedy planner g, whatever its tie rule, and any language c-reasonable
for the family F built from g, the three degenerate pairs are amongst the
lowest-complexity compatible pairs at distance c, for every policy.
`ReasonableForF.proposition_seven` is the instance g := `greedyPlanner`. -/
public theorem proposition_seven_of_isGreedy (hg : IsGreedy g) (π : Policy S A) :
    AmongLowestFor L.KPair L.c π (op1 (op5 π)) ∧
      AmongLowestFor L.KPair L.c π (op2Of g (op6 π)) ∧
      AmongLowestFor L.KPair L.c π (op4 (op2Of g (op6 π))) :=
  proposition_seven_of_bounds_of_isGreedy hg L.KPair L.c L.F_complexity_le π

/-- **Proposition 8 at every planner** (Armstrong and Mindermann,
Proposition 8, PDF p. 7: *"If π̇ is a human policy, c defines a reasonable
measure of comparable complexity, L is a c-reasonable language for F, and
(ṗ, Ṙ) is compatible with π̇, then (−ṗ, −Ṙ) is of comparable complexity to
(ṗ, Ṙ)"*). For any planner g and any language c-reasonable for the family F
built from g, a compatible pair's negation is compatible and the two are within
c of each other. Only the F₄ bound is used, and F₄ involves no planner, so g
need not even be greedy. `ReasonableForF.proposition_eight` is the instance
g := `greedyPlanner`. -/
public theorem proposition_eight_any_planner {x : Pair S A} {π : Policy S A}
    (h : ReasonableForF.Compatible x π) :
    ReasonableForF.Compatible (F₄ x) π ∧
      L.KPair (F₄ x) ≤ L.KPair x + L.c ∧
      L.KPair x ≤ L.KPair (F₄ x) + L.c := by
  refine ⟨?_, L.F_complexity_le 3 x, ?_⟩
  · show op3 (op4 x) = π
    rw [op3_op4]
    exact h
  · have hb := L.F_complexity_le 3 (F₄ x)
    rw [show (FmapOf g 3 : Pair S A → Pair S A) = F₄ from rfl, ReasonableForF.F₄_F₄] at hb
    exact hb

/-- **Proposition 8 at every planner, in print's vocabulary**: the negation is
compatible and *of comparable complexity* (`ComparableComplexity`, §5.1.3) at
the language's constant. -/
public theorem proposition_eight_comparable_any_planner {x : Pair S A} {π : Policy S A}
    (h : ReasonableForF.Compatible x π) :
    ReasonableForF.Compatible (F₄ x) π ∧ ComparableComplexity L.KPair L.c x (F₄ x) := by
  obtain ⟨hc, h1, h2⟩ := L.proposition_eight_any_planner h
  exact ⟨hc, (comparableComplexity_iff _ _ _ _).mpr ⟨h2, h1⟩⟩

/-- **The informal Theorem 2, conditionally, at every greedy planner**: if a
compatible pair is not amongst the lowest compatible pairs of a language
c-reasonable for the F built from g, the three degenerate pairs built from g
are each strictly simpler than it. -/
public theorem theorem_two_conditional_of_isGreedy (hg : IsGreedy g) (π : Policy S A)
    (intended : Pair S A) (hc : ReasonableForF.Compatible intended π)
    (h9 : ¬ AmongLowestFor L.KPair L.c π intended) :
    L.KPair (op1 (op5 π)) < L.KPair intended ∧
      L.KPair (op2Of g (op6 π)) < L.KPair intended ∧
      L.KPair (op4 (op2Of g (op6 π))) < L.KPair intended := by
  have hy : ∃ y, ReasonableForF.Compatible y π ∧ L.KPair y + L.c < L.KPair intended := by
    by_contra hno
    refine h9 ⟨hc, fun y hy => ?_⟩
    by_contra hgt
    exact hno ⟨y, hy, by omega⟩
  obtain ⟨y, hy, hlt⟩ := hy
  obtain ⟨h1, h2, h3⟩ := L.proposition_seven_of_isGreedy hg π
  exact ⟨by have := h1.2 y hy; omega, by have := h2.2 y hy; omega,
    by have := h3.2 y hy; omega⟩

end ReasonableForFOf

namespace ReasonableForF

variable [Fintype A] [Nonempty A] (L : ReasonableForF S A)

/-- The round trip through `ReasonableForFOf` at `greedyPlanner` is the
identity. -/
public theorem toReasonableForF_toReasonableForFOf :
    L.toReasonableForFOf.toReasonableForF = L := rfl

/-- The language's amongst-the-lowest predicate is the same at the
`ReasonableForFOf` view: same complexity, same constant. -/
public theorem amongLowestCompatible_iff_toReasonableForFOf (π : Policy S A) (x : Pair S A) :
    L.AmongLowestCompatible π x ↔
      AmongLowestFor L.toReasonableForFOf.KPair L.toReasonableForFOf.c π x := Iff.rfl

end ReasonableForF

/-! ## Conjecture 9 at a planner -/

/-- **Conjecture 9 (informal complexity proposition) at a planner g**
(Armstrong and Mindermann, §6, `am-conj9`: *"If π̇ is a human policy, and L is
a 'reasonable' computer language with (ṗ, Ṙ) a 'reasonable' compatible
planner-reward pair, then the complexity of (ṗ, Ṙ) is not close to minimal
amongst the pairs compatible with π̇"*), with "reasonable language" read
through the family F built from g. Print fixes one p_g, so the conjecture is
this proposition at print's g; stated for a parameter g it is print's
conjecture at every completion of p_g's tie rule. A statement, not an
assumption: nothing asserts or proves it. `ConjectureNine` is the case
g := `greedyPlanner` (`conjectureNineOf_greedyPlanner_iff`). -/
@[expose] public def ConjectureNineOf (g : Planner (RewardFn S A) (Policy S A))
    (ReasonableLanguage : ReasonableForFOf g → Prop) (Human : Policy S A → Prop)
    (Reasonable : Pair S A → Prop) : Prop :=
  ∀ L : ReasonableForFOf g, ReasonableLanguage L → ∀ π : Policy S A, Human π →
    ∀ x : Pair S A, Reasonable x → ReasonableForF.Compatible x π →
      ¬ AmongLowestFor L.KPair L.c π x

/-- **`ConjectureNine` is `ConjectureNineOf` at `greedyPlanner`**, with the
reasonable-language predicate transported along
`ReasonableForFOf.toReasonableForF`. -/
public theorem conjectureNineOf_greedyPlanner_iff [Fintype A] [Nonempty A]
    (ReasonableLanguage : ReasonableForF S A → Prop) (Human : Policy S A → Prop)
    (Reasonable : Pair S A → Prop) :
    ConjectureNineOf (greedyPlanner (S := S) (A := A))
        (fun L => ReasonableLanguage L.toReasonableForF) Human Reasonable ↔
      ConjectureNine ReasonableLanguage Human Reasonable := by
  constructor
  · intro h L hL π hπ x hx hc
    exact (L.notAmongLowest_iff π x hc).2
      (h L.toReasonableForFOf hL π hπ x hx hc)
  · intro h L hL π hπ x hx hc
    exact (L.toReasonableForF.notAmongLowest_iff π x hc).1 (h _ hL π hπ x hx hc)

/-- **The informal Theorem 2 from Conjecture 9, at every greedy planner**: where
the conjecture at g holds, each degenerate pair built from g is strictly simpler
than every reasonable compatible pair. -/
public theorem ConjectureNineOf.theorem_two_of_isGreedy {g : Planner (RewardFn S A) (Policy S A)}
    (hg : IsGreedy g) {ReasonableLanguage : ReasonableForFOf g → Prop}
    {Human : Policy S A → Prop} {Reasonable : Pair S A → Prop}
    (h : ConjectureNineOf g ReasonableLanguage Human Reasonable) {L : ReasonableForFOf g}
    (hL : ReasonableLanguage L) {π : Policy S A} (hπ : Human π) {x : Pair S A}
    (hx : Reasonable x) (hc : ReasonableForF.Compatible x π) :
    L.KPair (op1 (op5 π)) < L.KPair x ∧
      L.KPair (op2Of g (op6 π)) < L.KPair x ∧
      L.KPair (op4 (op2Of g (op6 π))) < L.KPair x :=
  L.theorem_two_conditional_of_isGreedy hg π x hc (h L hL π hπ x hx hc)

/-- **The reasonableness premise carries weight, at every planner**: if
`Reasonable` admits the indifferent pair of some human policy at some reasonable
language for the F built from g, Conjecture 9 at g fails. Only the F₁ bound is
used, so g need not be greedy. -/
public theorem not_conjectureNineOf_of_indifferent {g : Planner (RewardFn S A) (Policy S A)}
    {ReasonableLanguage : ReasonableForFOf g → Prop} {Human : Policy S A → Prop}
    {Reasonable : Pair S A → Prop} {L : ReasonableForFOf g} (hL : ReasonableLanguage L)
    {π : Policy S A} (hπ : Human π) (hind : Reasonable (op1 (op5 π))) :
    ¬ ConjectureNineOf g ReasonableLanguage Human Reasonable := fun h =>
  h L hL π hπ _ hind (ReasonableForF.compatible_indifferent π)
    (indifferent_amongLowestFor L.KPair L.c (L.F_complexity_le 0) π)

end AISafetyAtlas.Preference.Source
