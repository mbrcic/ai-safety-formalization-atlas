module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum

/-!
# Zero power indices and null players, in the class where that is a theorem

The proposal's `Q10` and `B6`, which share one substrate and are therefore one
module. Both quantify over a **finite monotone simple game**: a coalition value
taking only the values `0` and `1`, monotone under inclusion.

`Q10` is the Shapley-Shubik statement. The value is a weighted sum of marginal
contributions with weights `|C|! (n - |C| - 1)! / n!`. Every weight is strictly
positive and, under monotonicity, every marginal is nonnegative, so the sum
vanishes exactly when every marginal does -- which is what it means to be a
null player. Print's warning is the same one the proof makes visible: drop
monotonicity and positive and negative marginals can cancel, so a zero value no
longer identifies a null player. `Examples` carries that countermodel.

`B6` is the Banzhaf statement. The raw score averages the same marginals with
uniform weight `2 ^ -(n - 1)` over the coalitions not containing `i`, and print
reads it as a probability: *the chance that changing `i`'s vote changes the
outcome*. That reading is `banzhafRaw_eq_swings_div`, which identifies the score
with a count of pivotal coalitions over the number of coalitions, since each
marginal in this class is a `0`/`1` pivotality indicator.

The two then coincide: `shapleyShubik_eq_zero_iff_banzhafRaw_eq_zero`. Both are
corollaries of one lemma about a positively weighted sum of nonnegative terms,
and the module is arranged so that lemma is visible rather than duplicated.

## Scope

Only the **raw** Banzhaf score is defined. The normalized index divides by the
sum over all players and is a different object; print says so, and so does the
neighbouring literature -- Pitz and Ferraz, *Cohesion-Sensitive Power Indices*
(arXiv 2026), page 7, define the classical value with the weights used here and
then normalize separately in their Definition 3.2. Nothing here is graded
against that paper.

Nothing here is a Shapley value in general: the weights are written out for
this class and no axiomatic characterization, efficiency or linearity claim is
made. The simple-game condition is carried as a field so that a nonmonotone
simple game is still a legal object, which is what the countermodel needs.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

open Finset

variable {N : Type*} [Fintype N] [DecidableEq N]

/--
**A simple game**: a coalition value taking only the values `0` and `1`.

Monotonicity is deliberately *not* a field. Both printed results hold only in
the monotone class, and keeping the hypothesis separate is what lets the
nonmonotone countermodel be an inhabitant of the same type rather than a
different one.
-/
public structure SimpleGame (N : Type*) [Fintype N] [DecidableEq N] where
  /-- The worth of a coalition. -/
  val : Finset N → ℤ
  /-- Only two values occur. -/
  simple : ∀ C, val C = 0 ∨ val C = 1

/-- The coalitions `i` is not in: the index set both indices sum over. It does
not mention the game, so it is stated once here rather than as a member. -/
@[expose] public def others (i : N) : Finset (Finset N) :=
  (univ.erase i).powerset

namespace SimpleGame

variable (v : SimpleGame N)

/-- **Monotone under inclusion.** Adding members never loses a win. -/
@[expose] public def Monotone' : Prop := ∀ C D : Finset N, C ⊆ D → v.val C ≤ v.val D

/-- The **marginal contribution** of `i` to `C`. -/
@[expose] public def marginal (i : N) (C : Finset N) : ℤ :=
  v.val (insert i C) - v.val C

/-- **A null player** contributes nothing to any coalition. -/
@[expose] public def NullPlayer (i : N) : Prop := ∀ C : Finset N, v.marginal i C = 0

/-- **`i` is pivotal for `C`**: `i` turns a losing coalition into a winning one. -/
@[expose] public def Pivotal (i : N) (C : Finset N) : Prop :=
  v.val (insert i C) = 1 ∧ v.val C = 0

/-- Pivotality is decidable, since the value is an integer. Supplied here so
that finite witnesses can count pivotal coalitions. -/
public instance decidablePivotal (i : N) : DecidablePred (v.Pivotal i) := fun C =>
  decidable_of_iff (v.val (insert i C) = 1 ∧ v.val C = 0) Iff.rfl

/-- The Shapley weight attached to a coalition of size `k` in a game of `n`
players. -/
@[expose] public def shapleyWeight (n k : ℕ) : ℚ :=
  (k.factorial * (n - k - 1).factorial : ℚ) / (n.factorial : ℚ)

/-- **The Shapley-Shubik value of `i`.** -/
@[expose] public noncomputable def shapleyShubik (i : N) : ℚ :=
  ∑ C ∈ others i, shapleyWeight (Fintype.card N) C.card * (v.marginal i C : ℚ)

/-- **The raw Banzhaf score of `i`**: the uniform average of the same marginals
over the coalitions `i` is not in. -/
@[expose] public noncomputable def banzhafRaw (i : N) : ℚ :=
  (∑ C ∈ others i, (v.marginal i C : ℚ)) / (2 : ℚ) ^ (Fintype.card N - 1)

/-! ## The one lemma both results use -/

omit [Fintype N] [DecidableEq N] in
/--
**A positively weighted sum of nonnegative terms vanishes only termwise.**

Stated for an arbitrary index finset so that both indices reach it unchanged.
-/
public theorem sum_weighted_eq_zero_iff {ι : Type*} {s : Finset ι}
    {w f : ι → ℚ} (hw : ∀ a ∈ s, 0 < w a) (hf : ∀ a ∈ s, 0 ≤ f a) :
    ∑ a ∈ s, w a * f a = 0 ↔ ∀ a ∈ s, f a = 0 := by
  constructor
  · intro h a ha
    have hnn : ∀ b ∈ s, 0 ≤ w b * f b := fun b hb =>
      mul_nonneg (hw b hb).le (hf b hb)
    have := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h a ha
    rcases mul_eq_zero.mp this with hwa | hfa
    · exact absurd hwa (hw a ha).ne'
    · exact hfa
  · intro h
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [h a ha, mul_zero]

/-! ## What monotonicity buys -/

/-- Marginals are nonnegative in a monotone game. -/
public theorem marginal_nonneg (hm : v.Monotone') (i : N) (C : Finset N) :
    0 ≤ v.marginal i C :=
  sub_nonneg.mpr (hm C (insert i C) (Finset.subset_insert i C))

/-- In a simple game a marginal is `0` or `1` once it is nonnegative, and it is
`1` exactly when `i` is pivotal. -/
public theorem marginal_eq_one_iff_pivotal (i : N) (C : Finset N) :
    v.marginal i C = 1 ↔ v.Pivotal i C := by
  constructor
  · intro h
    rcases v.simple (insert i C) with h1 | h1 <;> rcases v.simple C with h2 | h2 <;>
      rw [marginal, h1, h2] at h <;> simp_all [Pivotal]
  · rintro ⟨h1, h2⟩
    rw [marginal, h1, h2]; ring

/-- **Every coalition is a witness, including those `i` belongs to.** A null
player is one whose marginals vanish on `others i` alone. -/
public theorem nullPlayer_iff_others (i : N) :
    v.NullPlayer i ↔ ∀ C ∈ others i, v.marginal i C = 0 := by
  constructor
  · intro h C _; exact h C
  · intro h C
    have hC : C.erase i ∈ others i := by
      simp only [others, Finset.mem_powerset]
      intro x hx
      have hxi : x ≠ i := Finset.ne_of_mem_erase hx
      exact Finset.mem_erase.mpr ⟨hxi, Finset.mem_univ x⟩
    by_cases hmem : i ∈ C
    · have := h _ hC
      rw [marginal, Finset.insert_erase hmem] at this
      have hval : v.val C - v.val (C.erase i) = 0 := this
      rw [marginal, Finset.insert_eq_self.mpr hmem]
      ring
    · rw [Finset.erase_eq_of_notMem hmem] at hC
      exact h C hC

/-! ## `Q10`: Shapley-Shubik -/

/-- Every Shapley weight is strictly positive. -/
public theorem shapleyWeight_pos {n k : ℕ} : 0 < shapleyWeight n k := by
  unfold shapleyWeight
  apply div_pos
  · exact_mod_cast Nat.mul_pos k.factorial_pos (n - k - 1).factorial_pos
  · exact_mod_cast n.factorial_pos

/--
**`Q10`: in a finite monotone simple game, zero Shapley-Shubik value is exactly
null-player status.**

The weights are strictly positive and the marginals nonnegative, so the sum
vanishes only termwise. Monotonicity is the whole content: without it the
marginals change sign and the equivalence fails, which
`AISafetyAtlas.Examples.Sovereignty.VotingPower` exhibits.
-/
public theorem shapleyShubik_eq_zero_iff (hm : v.Monotone') (i : N) :
    v.shapleyShubik i = 0 ↔ v.NullPlayer i := by
  rw [nullPlayer_iff_others]
  unfold shapleyShubik
  constructor
  · intro h C hC
    have := (sum_weighted_eq_zero_iff
      (w := fun C => shapleyWeight (Fintype.card N) C.card)
      (f := fun C => (v.marginal i C : ℚ))
      (fun _ _ => shapleyWeight_pos)
      (fun D _ => by exact_mod_cast v.marginal_nonneg hm i D)).mp h C hC
    exact_mod_cast this
  · intro h
    refine Finset.sum_eq_zero fun C hC => ?_
    rw [h C hC]; simp

/-! ## `B6`: Banzhaf -/

/--
**The raw Banzhaf score counts pivotal coalitions.**

This is print's reading: each marginal in a monotone simple game is a `0`/`1`
pivotality indicator, so the average is the number of coalitions for which `i`
is pivotal, over the number of coalitions `i` is not in.
-/
public theorem banzhafRaw_eq_swings_div (hm : v.Monotone') (i : N) :
    v.banzhafRaw i =
      (((others i).filter fun C => v.Pivotal i C).card : ℚ)
        / (2 : ℚ) ^ (Fintype.card N - 1) := by
  unfold banzhafRaw
  congr 1
  rw [Finset.card_filter]
  push_cast
  refine Finset.sum_congr rfl fun C _ => ?_
  by_cases hp : v.Pivotal i C
  · rw [if_pos hp, (v.marginal_eq_one_iff_pivotal i C).mpr hp]; norm_num
  · rw [if_neg hp]
    have hne : v.marginal i C ≠ 1 := fun h => hp ((v.marginal_eq_one_iff_pivotal i C).mp h)
    have hnn : 0 ≤ v.marginal i C := v.marginal_nonneg hm i C
    have : v.marginal i C = 0 := by
      rcases v.simple (insert i C) with h1 | h1 <;> rcases v.simple C with h2 | h2 <;>
        · unfold marginal at hne hnn ⊢
          omega
    rw [this]; norm_num

/--
**`B6`: in a finite monotone simple game, zero raw Banzhaf score is exactly
null-player status.**

Same shape as `Q10` with the constant weight `2 ^ -(n - 1)` in place of the
Shapley weights, which is why both come from `sum_weighted_eq_zero_iff`.
-/
public theorem banzhafRaw_eq_zero_iff (hm : v.Monotone') (i : N) :
    v.banzhafRaw i = 0 ↔ v.NullPlayer i := by
  rw [nullPlayer_iff_others]
  unfold banzhafRaw
  rw [div_eq_zero_iff]
  have hpow : ((2 : ℚ) ^ (Fintype.card N - 1)) ≠ 0 := by positivity
  simp only [hpow, or_false]
  constructor
  · intro h C hC
    have := (sum_weighted_eq_zero_iff (w := fun _ : Finset N => (1 : ℚ))
      (f := fun C => (v.marginal i C : ℚ))
      (fun _ _ => one_pos)
      (fun D _ => by exact_mod_cast v.marginal_nonneg hm i D)).mp (by simpa using h) C hC
    exact_mod_cast this
  · intro h
    refine Finset.sum_eq_zero fun C hC => ?_
    rw [h C hC]; simp

/--
**The two indices vanish together.**

Print states this coincidence as a fact about the monotone simple class, and
that is exactly where it holds: both sides are equivalent to the same
null-player condition.
-/
public theorem shapleyShubik_eq_zero_iff_banzhafRaw_eq_zero (hm : v.Monotone') (i : N) :
    v.shapleyShubik i = 0 ↔ v.banzhafRaw i = 0 :=
  (v.shapleyShubik_eq_zero_iff hm i).trans (v.banzhafRaw_eq_zero_iff hm i).symm

end SimpleGame

end AISafetyAtlas.Sovereignty
