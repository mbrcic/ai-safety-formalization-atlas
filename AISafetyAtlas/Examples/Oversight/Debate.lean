module

public import AISafetyAtlas.Oversight.Debate

/-!
# Worked model — doubly-efficient debate

`AISafetyAtlas.Oversight.Debate` states its three correctness guarantees under
two hypotheses — a parameter bundle `Params w d k t` and a `k`-Lipschitz oracle —
and its three query-complexity bounds under the parameter bundle alone. A theorem
whose hypotheses nothing satisfies is a valid proof of nothing, so this file
exhibits both hypotheses, and then reads the guarantees off at fixed numbers.

| What | Declaration |
|---|---|
| The Lipschitz hypothesis is satisfiable — by **every** oracle, at `t = 0` | `every_oracle_lipschitz_zero` |
| The parameter bundle is inhabited at concrete numbers | `oneRound` |
| Completeness as a number | `honest_alice_reaches_true` |
| Soundness as a number | `honest_bob_reaches_false` |
| Both at once, better than a coin | `one_round_correct`, `success_beats_coin` |
| The verifier's query budget as a number | `verifier_queries_le` |

`t = 0` is the shortest debate the protocol admits (`Debate.protocol` runs
`t + 1` rounds) and the round count at which the Lipschitz hypothesis can be
discharged for every oracle without an induction upstream does not carry.
Nothing below depends on the oracle, so the instantiated guarantees hold for
arbitrary stochastic computations of that length.
-/

namespace AISafetyAtlas.Examples.Oversight.Debate

open AISafetyAtlas.Oversight

noncomputable section

/-! ## The hypotheses are satisfiable -/

/-- Two distributions on `Bool` can differ by at most one in the probability
they assign to `true`. -/
private lemma gap_le_one (p q : Prob Bool) : |p.prob true - q.prob true| ≤ 1 := by
  have hp0 := p.prob_nonneg (x := true)
  have hq0 := q.prob_nonneg (x := true)
  have hp1 := Prob.prob_le_one p true
  have hq1 := Prob.prob_le_one q true
  rw [abs_le]; constructor <;> linarith

/-- Over zero extra rounds the oracle's final answer is exactly its first query:
the fold produces one bit and the protocol reads it back. -/
private lemma final_zero (o : Debate.Oracle) :
    (Debate.finalAnswer o 0).prob true = (o 0 List.Vector.nil).prob true := by
  simp [Debate.finalAnswer, Oracle.final, Oracle.fold]

/--
**Every** stochastic oracle is `1`-Lipschitz over a one-round debate.

The oracle metric is the supremum, over transcript lengths and transcripts, of
the gap in the probability of the next bit. At `t = 0` the final answer *is* one
of the terms of that supremum, so the gap in final answers is bounded by the
distance itself.

This is the witness that `Debate.completeness`, `Debate.soundness` and
`Debate.correctness` are not statements about an empty hypothesis.
-/
public theorem every_oracle_lipschitz_zero (o : Debate.Oracle) : Debate.Lipschitz o 0 1 where
  k0 := zero_le_one
  le o' := by
    have inner : ∀ n : ℕ, BddAbove (Set.range fun y : List.Vector Bool n =>
        |(o n y).prob true - (o' n y).prob true|) :=
      fun n => ⟨1, by rintro _ ⟨y, rfl⟩; exact gap_le_one _ _⟩
    have outer : BddAbove (Set.range fun n : ℕ => ⨆ y : List.Vector Bool n,
        |(o n y).prob true - (o' n y).prob true|) :=
      ⟨1, by rintro _ ⟨n, rfl⟩; exact ciSup_le fun y => gap_le_one _ _⟩
    rw [one_mul, final_zero, final_zero]
    calc |(o 0 List.Vector.nil).prob true - (o' 0 List.Vector.nil).prob true|
        ≤ ⨆ y : List.Vector Bool 0, |(o 0 y).prob true - (o' 0 y).prob true| :=
          le_ciSup (inner 0) List.Vector.nil
      _ ≤ dist o o' := le_ciSup outer 0

/-- The parameter bundle, inhabited at Lipschitz constant `1` and one round.
Success probability `2/3`, output probability `3/5`. -/
public abbrev oneRound : Debate.Params (2 / 3) (3 / 5) 1 0 :=
  Debate.defaultParams 1 0 one_pos

/-! ## The guarantees, as numbers

Each statement below fixes `k = 1` and `t = 0` and quantifies over the oracle,
so it holds for every one-round stochastic computation.
-/

/--
Completeness at fixed numbers: if the oracle says `true` with probability at
least `2/3`, honest Alice wins with probability at least `3/5` — against any
Bob, adversarial ones included.
-/
public theorem honest_alice_reaches_true (o : Debate.Oracle) (eve : Debate.Bob)
    (m : (2 : ℝ) / 3 ≤ (Debate.finalAnswer o 0).prob true) :
    (3 : ℝ) / 5 ≤ ((Debate.protocol (Debate.honestAlice oneRound.c oneRound.q) eve
      (Debate.verifier oneRound.c oneRound.s oneRound.v) 0).prob' o).prob true :=
  Debate.completeness o (every_oracle_lipschitz_zero o) eve oneRound m

/--
Soundness at fixed numbers: if the oracle says `false` with probability at least
`2/3`, honest Bob wins with probability at least `3/5` — against any Alice.
-/
public theorem honest_bob_reaches_false (o : Debate.Oracle) (eve : Debate.Alice)
    (m : (2 : ℝ) / 3 ≤ (Debate.finalAnswer o 0).prob false) :
    (3 : ℝ) / 5 ≤ ((Debate.protocol eve (Debate.honestBob oneRound.s oneRound.b oneRound.q)
      (Debate.verifier oneRound.c oneRound.s oneRound.v) 0).prob' o).prob false :=
  Debate.soundness o (every_oracle_lipschitz_zero o) eve oneRound m

/-- Both directions at once, at the default parameters. -/
public theorem one_round_correct :
    Debate.Correct (3 / 5) 1 0 (Debate.honestAlice oneRound.c oneRound.q)
      (Debate.honestBob oneRound.s oneRound.b oneRound.q)
      (Debate.verifier oneRound.c oneRound.s oneRound.v) :=
  Debate.correctness 1 one_pos 0

/-- The point of the protocol, extracted: the debate succeeds more often than a
coin flip. -/
public theorem success_beats_coin : (1 : ℝ) / 2 < 3 / 5 :=
  one_round_correct.half_lt_w

/-! ## The verifier's budget

`Debate.vera_fast` bounds the trusted party's expected queries by `106000 k² + 1`
with no dependence on the round count. At `k = 1` that is a plain number.
-/

/-- The verifier makes at most `106001` expected queries, whatever Alice and Bob
do. -/
public theorem verifier_queries_le (o : Debate.Oracle) (alice : Debate.Alice)
    (bob : Debate.Bob) :
    (Debate.protocol alice bob (Debate.verifier oneRound.c oneRound.s oneRound.v) 0).cost'
      o VeraId ≤ 106001 := by
  refine le_trans (Debate.vera_fast o 1 one_pos 0 alice bob) ?_
  norm_num

end

end AISafetyAtlas.Examples.Oversight.Debate
