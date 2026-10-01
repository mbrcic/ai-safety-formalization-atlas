module

public import AISafetyAtlas.Sovereignty.VotingPower
public import Mathlib.Tactic.FinCases

/-!
# Three voting games the printed statements are about

Witnesses for `Q10` and `B6`, each pinning a clause of print that the general
theorems do not carry by themselves.

* `weighted` is print's own example: quota `3` with weights `(3, 1, 1)`. It
  shows that **a positive nominal vote weight can still be null**, so the
  theorem is not a restatement of "has some weight".
* `cancel` is the countermodel that makes monotonicity load bearing: a simple
  but nonmonotone game where a positive and a negative marginal cancel, so the
  Shapley-Shubik value is zero and the player is **not** null. Without it,
  `Q10`'s class restriction would look decorative.
* `majority` separates the raw Banzhaf score from the normalized index: the raw
  scores sum to `3/2`, not `1`. Print calls the normalized index "a different
  normalization"; this is why it has to be.

Each coalition value is a named definition rather than an inline field, so that
the finite checks below have something to unfold.
-/

namespace AISafetyAtlas.Examples.Sovereignty.VotingPower

open AISafetyAtlas.Sovereignty Finset

/-! ## Print's weighted game: quota 3 with weights (3, 1, 1) -/

/-- The nominal weight of each voter. -/
@[expose] public def wt : Fin 3 → ℤ
  | 0 => 3
  | _ => 1

/-- A coalition wins when its total weight reaches the quota `3`. -/
@[expose] public def weightedVal (C : Finset (Fin 3)) : ℤ :=
  if 3 ≤ ∑ i ∈ C, wt i then 1 else 0

/-- **Quota 3 with weights `(3, 1, 1)`.** -/
@[expose] public def weighted : SimpleGame (Fin 3) where
  val := weightedVal
  simple C := by unfold weightedVal; split <;> simp

public theorem weighted_monotone : weighted.Monotone' := by
  intro C D h
  show weightedVal C ≤ weightedVal D
  unfold weightedVal
  have hsum : ∑ i ∈ C, wt i ≤ ∑ i ∈ D, wt i :=
    Finset.sum_le_sum_of_subset_of_nonneg h
      (fun i _ _ => by fin_cases i <;> simp [wt])
  split
  · rw [if_pos (by omega)]
  · split <;> simp

/-- **Voter 1 is null despite a positive nominal weight.** -/
public theorem weighted_nullPlayer_one : weighted.NullPlayer 1 := by
  unfold SimpleGame.NullPlayer SimpleGame.marginal
  decide

/-- **Voter 0 is not null.** -/
public theorem weighted_not_nullPlayer_zero : ¬ weighted.NullPlayer 0 := by
  unfold SimpleGame.NullPlayer SimpleGame.marginal
  decide

/-- **`Q10` at print's example**: a voter carrying a third of the nominal weight
has Shapley-Shubik value zero. -/
public theorem weighted_shapleyShubik_one : weighted.shapleyShubik 1 = 0 :=
  (weighted.shapleyShubik_eq_zero_iff weighted_monotone 1).mpr weighted_nullPlayer_one

/-- **`B6` at the same example**: and raw Banzhaf score zero. -/
public theorem weighted_banzhafRaw_one : weighted.banzhafRaw 1 = 0 :=
  (weighted.banzhafRaw_eq_zero_iff weighted_monotone 1).mpr weighted_nullPlayer_one

/-- Voter `0`'s score is not zero, so the previous two are not vacuous. -/
public theorem weighted_shapleyShubik_zero_ne : weighted.shapleyShubik 0 ≠ 0 := fun h =>
  weighted_not_nullPlayer_zero
    ((weighted.shapleyShubik_eq_zero_iff weighted_monotone 0).mp h)

/-! ## Monotonicity is load bearing -/

/-- `{0}` and `{1}` win; `∅` and `{0, 1}` lose. -/
@[expose] public def cancelVal (C : Finset (Fin 2)) : ℤ :=
  if C = {0} ∨ C = {1} then 1 else 0

/--
**A simple, nonmonotone game.** Adding voter `1` to the winning coalition `{0}`
loses the game, which is what monotonicity forbids.
-/
@[expose] public def cancel : SimpleGame (Fin 2) where
  val := cancelVal
  simple C := by unfold cancelVal; split <;> simp

public theorem cancel_not_monotone : ¬ cancel.Monotone' := by
  intro h
  have hle : cancel.val {0} ≤ cancel.val {0, 1} := h {0} {0, 1} (by decide)
  revert hle
  show ¬ cancelVal {0} ≤ cancelVal {0, 1}
  decide

/-- Voter `0` is **not** null: joining the empty coalition wins the game. -/
public theorem cancel_not_nullPlayer : ¬ cancel.NullPlayer 0 := by
  unfold SimpleGame.NullPlayer SimpleGame.marginal
  decide

/--
**The cancellation print warns about.** One marginal is `+1` and the other
`-1`, with equal Shapley weights, so the value is zero at a player who is not
null. `Q10` therefore fails outside the monotone class, and the class
restriction is not decoration.
-/
public theorem cancel_shapleyShubik_zero : cancel.shapleyShubik 0 = 0 := by
  have hcard : Fintype.card (Fin 2) = 2 := rfl
  have hset : others (0 : Fin 2) = {∅, {1}} := by decide
  have h0 : cancel.marginal 0 ∅ = 1 := by unfold SimpleGame.marginal; decide
  have h1 : cancel.marginal 0 {1} = -1 := by unfold SimpleGame.marginal; decide
  simp only [SimpleGame.shapleyShubik, hcard, hset]
  rw [Finset.sum_insert (by decide), Finset.sum_singleton, h0, h1]
  norm_num [SimpleGame.shapleyWeight]

/-- And it is a genuine counterexample, not a vacuous one: the same player is
not null. -/
public theorem cancel_shapleyShubik_zero_and_not_null :
    cancel.shapleyShubik 0 = 0 ∧ ¬ cancel.NullPlayer 0 :=
  ⟨cancel_shapleyShubik_zero, cancel_not_nullPlayer⟩

/-! ## Raw Banzhaf is not the normalized index -/

/-- Two of three voters carry the decision. -/
@[expose] public def majorityVal (C : Finset (Fin 3)) : ℤ :=
  if 2 ≤ C.card then 1 else 0

/-- **Simple majority of three.** -/
@[expose] public def majority : SimpleGame (Fin 3) where
  val := majorityVal
  simple C := by unfold majorityVal; split <;> simp

public theorem majority_monotone : majority.Monotone' := by
  intro C D h
  show majorityVal C ≤ majorityVal D
  unfold majorityVal
  have hcard : C.card ≤ D.card := Finset.card_le_card h
  split
  · rw [if_pos (by omega)]
  · split <;> simp

/-- Each voter is pivotal for exactly two of the four coalitions not containing
them. -/
public theorem majority_swings (i : Fin 3) :
    ((others i).filter fun C => majority.Pivotal i C).card = 2 := by
  have : ∀ (j : Fin 3) (C : Finset (Fin 3)),
      majority.Pivotal j C ↔ majorityVal (insert j C) = 1 ∧ majorityVal C = 0 :=
    fun _ _ => Iff.rfl
  simp only [this]
  fin_cases i <;> decide

/-- **Every raw Banzhaf score is `1/2`.** -/
public theorem majority_banzhafRaw (i : Fin 3) : majority.banzhafRaw i = 1 / 2 := by
  have hcard : Fintype.card (Fin 3) = 3 := rfl
  rw [majority.banzhafRaw_eq_swings_div majority_monotone i, majority_swings i, hcard]
  norm_num

/--
**The raw scores do not sum to one.**

`3/2`, not `1`. So the raw score is not an allocation of unit power, which is
exactly why the literature carries a separate normalized index -- Pitz and
Ferraz divide by this sum in their Definition 3.2. Print's remark that the
normalized Banzhaf index "is a different normalization" is this inequality.
-/
public theorem majority_banzhafRaw_sum_ne_one :
    ∑ i : Fin 3, majority.banzhafRaw i ≠ 1 := by
  simp only [majority_banzhafRaw]
  norm_num

/-! ## Where the two indices do agree -/

/-- **The two power indices vanish together on a monotone game.**

They disagree about magnitude everywhere else in this file -- that is what
`weighted_shapleyShubik_zero_ne` and `majority_banzhafRaw_sum_ne_one` are for --
but on the question *"has this player any power at all?"* they never disagree,
because both reduce to the same null-player condition. Monotonicity is what buys
that, and `cancel_not_monotone` is the game where it is unavailable. -/
public theorem weighted_zero_indices_agree (i : Fin 3) :
    weighted.shapleyShubik i = 0 ↔ weighted.banzhafRaw i = 0 :=
  SimpleGame.shapleyShubik_eq_zero_iff_banzhafRaw_eq_zero weighted weighted_monotone i

end AISafetyAtlas.Examples.Sovereignty.VotingPower
