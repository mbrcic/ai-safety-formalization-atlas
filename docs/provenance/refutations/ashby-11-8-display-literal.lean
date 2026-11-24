import AISafetyAtlas.Control.RequisiteVariety

/-!
# Ashby 11/8's last display as printed is false; the repaired line is the one that holds

W. Ross Ashby, *An Introduction to Cybernetics* (1956; second impression 1957), §11/8,
book p. 208 (PDF p. 111; audit row S03-R05):

    But always, by algebraic necessity,
        H(R, E) ≤ H(R) + H(E)
    so
        H(D) + H_D(R) ≤ H(R) + H_R(E)
    i.e.
        H(E) ≥ H(D) + H_D(E) − H(R).

(Transcribed from the page image in
`docs/provenance/printed-statements/ashby-1957-introduction-to-cybernetics.yaml`,
entry `ashby-11-8`; the scan sets `≥`, `≤` as underlined `>`, `<`.) The premise is
§11/8's entropy form of the column condition, entry `ashby-11-8-hyp` (p. 207):
`H_R(E) ≥ H_R(D)`. The setting (p. 207) is *"three variables [...] Without any
regard for how they are related causally"*, so `E` is any variable, not
necessarily the outcome of a table at `(D, R)`. `H_D(E)` is *"the uncertainty in E
when D's state is known"* (entry `ashby-def-entropy-notation-11-8`).

Read literally, the last line is false. Take `D` and `E` two independent fair bits
and `R` constant. Then `H_R(E) = H(E) = log 2 = H(D) = H_R(D)`, so the premise
holds, while the line claims `H(E) ≥ H(D) + H_D(E) − H(R) = 2 log 2`. This file
proves that (`literal_false`) and that the repaired line
`H(E) ≥ H(D) + H_D(R) − H(R)` holds for every three variables meeting the premise
(`repaired_holds`), as an instance of the atlas's
`AISafetyAtlas.Control.entropy_ge_of_condEntropy_ge` at slack `K = 0`. The
intermediate display is `AISafetyAtlas.Control.entropy_add_condEntropy_le_of_condEntropy_ge`
and is included in `repaired_holds` too.

Why the repair is the necessary one and not a different theorem:

* it changes one symbol, `H_D(E)` to `H_D(R)`. The line is introduced by "i.e." as
  a rewriting of the two lines above it, and those give exactly
  `H(D) + H_D(R) ≤ H(R) + H_R(E) ≤ H(R) + H(E)`, so `H_D(R)` is the term the
  derivation produces;
* the next paragraph (entry `ashby-11-8-determinate`) minimises the bound by setting
  *"H_D(R) = 0, i.e. when R is a determinate function of D"*, which names the
  term as `H_D(R)`;
* it keeps the premise, the setting and the direction of the inequality. No
  hypothesis is added.

Restricting `E` instead would not do. If `E` is a function of `(D, R)` (the table
outcome of §11/3--11/5), then `H_D(E) ≤ H_D(R)` and the literal line follows from
the repaired one (not proved here). That narrows §11/8's explicit *"without any
regard for how they are related causally"*, so it is not the repair; the
counterexample above has `E` independent of `(D, R)`, which the setting allows.

Units: PFR's entropies are in nats. Both lines are homogeneous of degree one in
the logarithm, so the counterexample and the repair hold in every base, Ashby's
bits included.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/ashby-11-8-display-literal.lean`.
Grading context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired
slips); final grade: id 183 in
`docs/provenance/regrade-2026-11/final-grades.tsv`.
-/

open MeasureTheory ProbabilityTheory AISafetyAtlas.Control

namespace AshbyElevenEightDisplayLiteral

/-- §11/8's last display exactly as printed, for any three finite-range variables
on a probability space: if `H_R(E) ≥ H_R(D)`, then `H(E) ≥ H(D) + H_D(E) − H(R)`. -/
def LiteralPrint : Prop :=
  ∀ (Ω D R E : Type) [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace R]
    [MeasurableSpace E] [MeasurableSingletonClass D] [MeasurableSingletonClass R]
    [MeasurableSingletonClass E] [Countable D] [Countable R] [Countable E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Dv : Ω → D) (Rv : Ω → R) (Ev : Ω → E),
    Measurable Dv → Measurable Rv → Measurable Ev →
    ∀ [FiniteRange Dv] [FiniteRange Rv] [FiniteRange Ev],
    H[Dv | Rv ; μ] ≤ H[Ev | Rv ; μ] →
    H[Dv ; μ] + H[Ev | Dv ; μ] - H[Rv ; μ] ≤ H[Ev ; μ]

/-- A fair coin. -/
noncomputable def coin : Measure Bool := uniformOn Set.univ

instance : IsProbabilityMeasure coin := by unfold coin; infer_instance

theorem coin_entropy : H[(id : Bool → Bool) ; coin] = Real.log 2 := by
  rw [coin, IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
  simp

/-- The disturbance: the first of two independent fair coins. -/
theorem fst_entropy : H[(Prod.fst : Bool × Bool → Bool) ; coin.prod coin] = Real.log 2 := by
  rw [entropy_def, Measure.map_fst_prod, measure_univ, one_smul, ← coin_entropy, entropy_def,
    Measure.map_id]

/-- The outcome: the second coin. -/
theorem snd_entropy : H[(Prod.snd : Bool × Bool → Bool) ; coin.prod coin] = Real.log 2 := by
  rw [entropy_def, Measure.map_snd_prod, measure_univ, one_smul, ← coin_entropy, entropy_def,
    Measure.map_id]

/-- The response: constant. -/
def blank : Bool × Bool → Unit := fun _ => ()

instance : FiniteRange blank := ⟨Set.toFinite _⟩
instance : FiniteRange (Prod.fst : Bool × Bool → Bool) := ⟨Set.toFinite _⟩
instance : FiniteRange (Prod.snd : Bool × Bool → Bool) := ⟨Set.toFinite _⟩

theorem blank_indep {X : Bool × Bool → Bool} : IndepFun X blank (coin.prod coin) :=
  indepFun_const ()

/-- **The printed line is false.** `D`, `E` independent fair coins, `R` constant:
the premise reads `log 2 ≤ log 2`, and the line reads
`log 2 + log 2 − 0 ≤ log 2`. -/
theorem literal_false : ¬ LiteralPrint := by
  intro h
  have hind : IndepFun (Prod.snd : Bool × Bool → Bool) Prod.fst (coin.prod coin) :=
    indepFun_fst_snd.symm
  have hcond : H[(Prod.snd : Bool × Bool → Bool) | (Prod.fst : Bool × Bool → Bool) ;
      coin.prod coin] = Real.log 2 := by
    rw [hind.condEntropy_eq_entropy measurable_snd measurable_fst, snd_entropy]
  have hR : H[blank ; coin.prod coin] = 0 := entropy_const _
  have hD : H[(Prod.fst : Bool × Bool → Bool) | blank ; coin.prod coin] = Real.log 2 := by
    rw [blank_indep.condEntropy_eq_entropy measurable_fst measurable_const, fst_entropy]
  have hE : H[(Prod.snd : Bool × Bool → Bool) | blank ; coin.prod coin] = Real.log 2 := by
    rw [blank_indep.condEntropy_eq_entropy measurable_snd measurable_const, snd_entropy]
  have := h (Bool × Bool) Bool Unit Bool (coin.prod coin) Prod.fst blank Prod.snd
    measurable_fst measurable_const measurable_snd (by rw [hD, hE])
  rw [fst_entropy, hcond, hR, snd_entropy] at this
  have : 0 < Real.log 2 := Real.log_pos one_lt_two
  linarith

/-- **The repaired line holds in general**, with the intermediate display: for any
three finite-range variables (any measure that is zero or a probability) with
`H_R(E) ≥ H_R(D)`, `H(D) + H_D(R) ≤ H(R) + H_R(E)` and
`H(E) ≥ H(D) + H_D(R) − H(R)`. These are the atlas's
`entropy_add_condEntropy_le_of_condEntropy_ge` and `entropy_ge_of_condEntropy_ge`
at slack `K = 0`. -/
theorem repaired_holds {Ω D R E : Type} [MeasurableSpace Ω] [MeasurableSpace D]
    [MeasurableSpace R] [MeasurableSpace E] [MeasurableSingletonClass D]
    [MeasurableSingletonClass R] [MeasurableSingletonClass E] [Countable D] [Countable R]
    [Countable E] (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {Dv : Ω → D} {Rv : Ω → R} {Ev : Ω → E}
    (hD : Measurable Dv) (hR : Measurable Rv) (hE : Measurable Ev)
    [FiniteRange Dv] [FiniteRange Rv] [FiniteRange Ev]
    (hkey : H[Dv | Rv ; μ] ≤ H[Ev | Rv ; μ]) :
    H[Dv ; μ] + H[Rv | Dv ; μ] ≤ H[Rv ; μ] + H[Ev | Rv ; μ] ∧
      H[Dv ; μ] + H[Rv | Dv ; μ] - H[Rv ; μ] ≤ H[Ev ; μ] := by
  have hkey0 : H[Dv | Rv ; μ] - 0 ≤ H[Ev | Rv ; μ] := by linarith
  refine ⟨?_, ?_⟩
  · simpa using entropy_add_condEntropy_le_of_condEntropy_ge μ hD hR 0 hkey0
  · simpa using entropy_ge_of_condEntropy_ge μ hD hR hE 0 hkey0

end AshbyElevenEightDisplayLiteral
