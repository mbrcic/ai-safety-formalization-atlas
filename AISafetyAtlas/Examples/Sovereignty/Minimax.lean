module

public import AISafetyAtlas.Sovereignty.Minimax
public import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The simultaneous-bit game: nothing pure, a half mixed

Print's witness for `Q3`. Two players each name a bit; the row player scores
one when the bits agree, which is the identity payoff matrix.

`pure_security_zero` is the pure security level: whatever bit the row player
commits to, the column player has a reply scoring zero. `half_value` is the
mixed one: the even mixture scores exactly one half against *every* reply, from
either side. So the pure and mixed security levels differ, which is the gap
`Q3` closes and which print records as "pure security and capture values 0 and
0, but mixed values 1/2 and 1/2".

`skewed` is here for a different reason: to pin the orientation. The
simultaneous-bit payoff is symmetric in the way that makes the row player's
guarantee and the column player's guarantee the same number, so it cannot tell
`Q3` apart from the statement with the inequalities reversed. A one-row payoff
`[1, 2]` can: the value is `1`, the row player cannot guarantee `2`, and
`skewed_not_two` says so. Read with the inequalities the wrong way round, `2`
would certify as the value.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Minimax

open AISafetyAtlas.Sovereignty

/-- **The simultaneous-bit game.** The row player scores one when the bits
agree. -/
@[expose] public def agree : Matrix (Fin 2) (Fin 2) ℝ := 1

/-- Its payoff is the overlap of the two mixtures. -/
public theorem payoff_agree (p q : Fin 2 → ℝ) :
    payoff agree p q = ∑ i, p i * q i := by
  simp only [payoff, agree, Matrix.one_apply, mul_ite, mul_one, mul_zero, ite_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- **The value exists at this game.** Von Neumann's theorem, instantiated: the
agreement game has a number both players can guarantee against. Stated because
the existence theorem quantifies over every matrix, and a statement about every
matrix is worth no more than one inhabited instance until one is written. -/
public theorem agree_has_a_value :
    ∃ v : ℝ, ∃ p ∈ mixed 2, ∃ q ∈ mixed 2,
      (∀ q' ∈ mixed 2, v ≤ payoff agree p q') ∧
        (∀ p' ∈ mixed 2, payoff agree p' q ≤ v) :=
  exists_mixed_value (by norm_num) (by norm_num) agree

/-- The pure strategy naming bit `i`. -/
@[expose] public def pureStrat (i : Fin 2) : Fin 2 → ℝ := fun k => if k = i then 1 else 0

/-- It is a mixed strategy. -/
public theorem pureStrat_mem (i : Fin 2) : pureStrat i ∈ mixed 2 := by
  refine ⟨fun k => ?_, ?_⟩
  · by_cases h : k = i <;> simp [pureStrat, h]
  · simp [pureStrat]

/-- The even mixture. -/
@[expose] public noncomputable def half : Fin 2 → ℝ := fun _ => 1 / 2

/-- It is a mixed strategy. -/
public theorem half_mem : half ∈ mixed 2 := by
  refine ⟨fun _ => by norm_num [half], ?_⟩
  simp [half]

/-- **The pure security level is zero**: every pure commitment has a reply that
scores nothing. -/
public theorem pure_security_zero (i : Fin 2) :
    ∃ q ∈ mixed 2, payoff agree (pureStrat i) q = 0 := by
  refine ⟨pureStrat (i + 1), pureStrat_mem _, ?_⟩
  rw [payoff_agree]
  fin_cases i <;>
    · rw [Finset.sum_eq_zero]
      intro k _
      fin_cases k <;> norm_num [pureStrat]

/-- **The even mixture scores one half against every reply**, and so does it
from the other side. That is the mixed value. -/
public theorem half_value :
    (∀ q ∈ mixed 2, payoff agree half q = 1 / 2) ∧
      (∀ p ∈ mixed 2, payoff agree p half = 1 / 2) := by
  constructor
  · intro q hq
    rw [payoff_agree]
    simp only [half]
    rw [← Finset.mul_sum, hq.2]
    norm_num
  · intro p hp
    rw [payoff_agree]
    simp only [half]
    rw [show (∑ i, p i * (1 / 2 : ℝ)) = (∑ i, p i) * (1 / 2) from (Finset.sum_mul ..).symm,
      hp.2]
    norm_num

/-- **So the gap print names is real**: zero pure, one half mixed. -/
public theorem pure_lt_mixed :
    (∀ i : Fin 2, ∃ q ∈ mixed 2, payoff agree (pureStrat i) q = 0) ∧
      ∃ p ∈ mixed 2, ∀ q ∈ mixed 2, payoff agree p q = 1 / 2 :=
  ⟨pure_security_zero, half, half_mem, half_value.1⟩

/-! ## An asymmetric game, to pin which side maximizes -/

/-- One row, two columns, unequal entries. -/
@[expose] public def skewed : Matrix (Fin 1) (Fin 2) ℝ := !![1, 2]

/-- Its payoff at the forced row mixture. -/
public theorem payoff_skewed (p : Fin 1 → ℝ) (q : Fin 2 → ℝ) :
    payoff skewed p q = p 0 * q 0 + p 0 * 2 * q 1 := by
  simp [payoff, skewed, Fin.sum_univ_two]

/-- The row player's only mixture. -/
public theorem mixed_one (p : Fin 1 → ℝ) (hp : p ∈ mixed 1) : p 0 = 1 := by
  simpa [Fin.sum_univ_one] using hp.2

/-- **The value is one**: the row player guarantees it and the column player
holds it there. -/
public theorem skewed_value :
    (∀ q' ∈ mixed 2, (1 : ℝ) ≤ payoff skewed (fun _ => 1) q') ∧
      (∀ p' ∈ mixed 1, payoff skewed p' (pureStrat 0) ≤ 1) := by
  constructor
  · intro q' hq'
    rw [payoff_skewed]
    have hsum : q' 0 + q' 1 = 1 := by simpa [Fin.sum_univ_two] using hq'.2
    have h1 : 0 ≤ q' 1 := hq'.1 1
    nlinarith
  · intro p' hp'
    rw [payoff_skewed, mixed_one p' hp']
    norm_num [pureStrat]

/-- **And the row player cannot guarantee two.** So the orientation of `Q3` is
not a convention here: with the inequalities reversed, `2` would pass as the
value of this game. -/
public theorem skewed_not_two :
    ¬ ∃ p ∈ mixed 1, ∀ q' ∈ mixed 2, (2 : ℝ) ≤ payoff skewed p q' := by
  rintro ⟨p, hp, h⟩
  have := h (pureStrat 0) (pureStrat_mem 0)
  rw [payoff_skewed, mixed_one p hp] at this
  norm_num [pureStrat] at this

end AISafetyAtlas.Examples.Sovereignty.Minimax
