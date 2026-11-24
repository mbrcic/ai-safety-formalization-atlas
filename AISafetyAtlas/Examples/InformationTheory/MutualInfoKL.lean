module

public import AISafetyAtlas.InformationTheory.MutualInfoKL
public import AISafetyAtlas.Examples.InformationTheory.DataProcessing

/-!
# Mutual information in `[0, ∞]` — witnesses at an infinite alphabet

Every statement of `AISafetyAtlas.InformationTheory.MutualInfoKL`, instantiated where
the `FiniteRange` versions in `AISafetyAtlas.InformationTheory.DataProcessing` cannot
be: the sample space is `ℕ` under `flipLaw`, the geometric law with parameter `1/2`
(Cover & Thomas's Problem 2.1, shifted to start at `0`), the identity takes every
natural number (`not_finiteRange_id_nat`), and `natParity` is its parity. These are
the instances named in the defect records of audit rows S01-R05 to S01-R10: `X` the flip count, `Y = X`, `Z = X mod 2` or `Z = ⌊X / 2⌋`.
-/

namespace AISafetyAtlas.Examples.InformationTheory

open MeasureTheory ProbabilityTheory AISafetyAtlas.InformationTheory

/-- `⌊n / 2⌋`, a function of `n` with two-point fibres. -/
@[expose] public def natHalf : ℕ → ℕ := fun n => n / 2

/-- `mutualInfoKL_comp_le` at `X = Y = id` and `g = natParity`: (Cover & Thomas, first
corollary to Theorem 2.8.1) with an infinite alphabet. -/
public theorem mutualInfoKL_natParity_le :
    mutualInfoKL (id : ℕ → ℕ) (natParity ∘ id) flipLaw ≤ mutualInfoKL id id flipLaw :=
  mutualInfoKL_comp_le measurable_id measurable_id Measurable.of_discrete

/-- `mutualInfoKL_comp_equiv` at the swap of a pair. -/
public theorem mutualInfoKL_swap_pair :
    mutualInfoKL (id : ℕ → ℕ) (MeasurableEquiv.prodComm ∘ fun n => (n, natParity n)) flipLaw
      = mutualInfoKL id (fun n => (n, natParity n)) flipLaw :=
  mutualInfoKL_comp_equiv measurable_id Measurable.of_discrete _

/-- `mutualInfoKL_comm` at the flip count and its parity. -/
public theorem mutualInfoKL_natParity_comm :
    mutualInfoKL (id : ℕ → ℕ) natParity flipLaw = mutualInfoKL natParity id flipLaw :=
  mutualInfoKL_comm measurable_id Measurable.of_discrete

/-- `isMarkovKernel_condLaw`: the law of the flip count given its parity. -/
public theorem isMarkovKernel_condLaw_natParity :
    IsMarkovKernel (condLaw natParity (id : ℕ → ℕ) flipLaw) :=
  isMarkovKernel_condLaw measurable_id

/-- `condLaw_singleton_mul` at parity `0` and count `4`. -/
public theorem condLaw_natParity_singleton_mul :
    condLaw natParity (id : ℕ → ℕ) flipLaw 0 {4} * flipLaw (natParity ⁻¹' {0})
      = flipLaw (natParity ⁻¹' {0} ∩ id ⁻¹' {4}) :=
  condLaw_singleton_mul Measurable.of_discrete measurable_id 0 4

/-- `map_pair_eq_compProd_condLaw`: the joint law of parity and count, disintegrated. -/
public theorem map_natParity_id_eq_compProd :
    flipLaw.map (fun n => (natParity n, id n))
      = flipLaw.map natParity ⊗ₘ condLaw natParity (id : ℕ → ℕ) flipLaw :=
  map_pair_eq_compProd_condLaw Measurable.of_discrete measurable_id

/-- `mutualInfoKL_pair_eq_add`, (2.119), with two infinite-range variables. -/
public theorem mutualInfoKL_pair_natParity :
    mutualInfoKL natParity (fun n => (id n, natHalf n)) flipLaw
      = mutualInfoKL natParity natHalf flipLaw + condMutualInfoKL natParity id natHalf flipLaw :=
  mutualInfoKL_pair_eq_add Measurable.of_discrete measurable_id Measurable.of_discrete

/-- `mutualInfoKL_pair_eq_add'`, (2.120), on the same variables. -/
public theorem mutualInfoKL_pair_natParity' :
    mutualInfoKL natParity (fun n => (id n, natHalf n)) flipLaw
      = mutualInfoKL natParity id flipLaw + condMutualInfoKL natParity natHalf id flipLaw :=
  mutualInfoKL_pair_eq_add' Measurable.of_discrete measurable_id Measurable.of_discrete

/-- `isMarkovChain_iff_condMutualInfoKL_eq_zero`: `I(X; X mod 2 | X) = 0`. -/
public theorem condMutualInfoKL_id_natParity_eq_zero :
    condMutualInfoKL (id : ℕ → ℕ) natParity id flipLaw = 0 :=
  (isMarkovChain_iff_condMutualInfoKL_eq_zero measurable_id measurable_id
    Measurable.of_discrete).mp id_id_natParity_isMarkovChain

/-- **Theorem 2.8.1 at the defect's instance**: `X` the flip count, `Y = X`,
`Z = X mod 2`, `I(X; Y) ≥ I(X; Z)`. -/
public theorem mutualInfoKL_natParity_le_of_isMarkovChain :
    mutualInfoKL (id : ℕ → ℕ) natParity flipLaw ≤ mutualInfoKL id id flipLaw :=
  mutualInfoKL_le_of_isMarkovChain measurable_id measurable_id Measurable.of_discrete
    id_id_natParity_isMarkovChain

/-- **"Similarly, `I(Y; Z) ≥ I(X; Z)`"** at `X` the flip count, `Y = X`, `Z = X mod 2`. -/
public theorem mutualInfoKL_natParity_le_of_isMarkovChain' :
    mutualInfoKL (id : ℕ → ℕ) natParity flipLaw ≤ mutualInfoKL id natParity flipLaw :=
  mutualInfoKL_le_of_isMarkovChain' measurable_id measurable_id Measurable.of_discrete
    id_id_natParity_isMarkovChain

/-- **The second corollary at the defect's instance**: `X` the flip count, `Y = X`,
`Z = ⌊X / 2⌋`, `I(X; Y | Z) ≤ I(X; Y)`. -/
public theorem condMutualInfoKL_natHalf_le :
    condMutualInfoKL (id : ℕ → ℕ) id (natHalf ∘ id) flipLaw ≤ mutualInfoKL id id flipLaw :=
  condMutualInfoKL_le_mutualInfoKL measurable_id measurable_id Measurable.of_discrete
    (isMarkovChain_comp_countable (X := (id : ℕ → ℕ)) measurable_id natHalf)

/-- **Equality in data processing, the "if" half**: `X = Y` the flip count and
`Z = X + 1`, each a function of the other, so both chains hold; no finiteness of
anything. -/
public theorem mutualInfoKL_succ_eq_of_isMarkovChain :
    mutualInfoKL (id : ℕ → ℕ) Nat.succ flipLaw = mutualInfoKL id (id : ℕ → ℕ) flipLaw :=
  mutualInfoKL_eq_of_isMarkovChain measurable_id measurable_id Measurable.of_discrete
    (isMarkovChain_comp_countable (X := (id : ℕ → ℕ)) measurable_id Nat.succ)
    (isMarkovChain_comp_countable (X := (id : ℕ → ℕ)) (Y := Nat.succ) Measurable.of_discrete
      Nat.pred)

/-- `I(X mod 2; X mod 2)` is finite: it is PFR's real `I` there. -/
public theorem mutualInfoKL_natParity_ne_top :
    mutualInfoKL natParity natParity flipLaw ≠ ⊤ := by
  rw [mutualInfoKL_eq_ofReal_mutualInfo Measurable.of_discrete Measurable.of_discrete]
  exact ENNReal.ofReal_ne_top

/-- `X → Y → Z` with `X = Y = X mod 2` and `Z` the flip count itself. -/
public theorem natParity_natParity_id_isMarkovChain :
    IsMarkovChain natParity natParity (id : ℕ → ℕ) flipLaw :=
  isMarkovChain_comm.mp (isMarkovChain_comp_countable (X := (id : ℕ → ℕ))
    (Y := natParity) Measurable.of_discrete id)

/-- **Equality in data processing, repaired, with an infinite-range `Z`**
(`mutualInfoKL_eq_iff_condMutualInfoKL_eq_zero`): `X = Y = X mod 2`, `Z` the flip count,
which `FiniteRange` excludes; `I(X; Y) < ∞` holds. -/
public theorem mutualInfoKL_natParity_id_eq_iff_cond :
    mutualInfoKL natParity (id : ℕ → ℕ) flipLaw = mutualInfoKL natParity natParity flipLaw ↔
      condMutualInfoKL natParity natParity id flipLaw = 0 :=
  mutualInfoKL_eq_iff_condMutualInfoKL_eq_zero Measurable.of_discrete Measurable.of_discrete
    measurable_id natParity_natParity_id_isMarkovChain mutualInfoKL_natParity_ne_top

/-- **Equality in data processing, repaired, Markov form** (`mutualInfoKL_eq_iff_isMarkovChain`),
on the same instance. -/
public theorem mutualInfoKL_natParity_id_eq_iff :
    mutualInfoKL natParity (id : ℕ → ℕ) flipLaw = mutualInfoKL natParity natParity flipLaw ↔
      IsMarkovChain natParity (id : ℕ → ℕ) natParity flipLaw :=
  mutualInfoKL_eq_iff_isMarkovChain Measurable.of_discrete Measurable.of_discrete
    measurable_id natParity_natParity_id_isMarkovChain mutualInfoKL_natParity_ne_top

/-- `mutualInfoKL_const`. -/
public theorem mutualInfoKL_id_const :
    mutualInfoKL (id : ℕ → ℕ) (fun _ => (0 : ℕ)) flipLaw = 0 :=
  mutualInfoKL_const measurable_id 0

/-- **Theorem 2.5.2 at `n = 2`** with the infinite-range family `X₁ = id`,
`X₂ = natParity` and `Y = natHalf`. -/
public theorem mutualInfoKL_chain_rule_natParity :
    mutualInfoKL natHalf (observationVector ![(id : ℕ → ℕ), natParity]) flipLaw
      = ∑ i : Fin 2, condMutualInfoKL natHalf (![(id : ℕ → ℕ), natParity] i)
          (observationPrefix ![(id : ℕ → ℕ), natParity] i) flipLaw :=
  mutualInfoKL_chain_rule_fin natHalf _ Measurable.of_discrete fun _ => Measurable.of_discrete

/-- `condMutualInfoKL_comm` at the flip count, its parity, and `⌊X / 2⌋`. -/
public theorem condMutualInfoKL_natParity_comm :
    condMutualInfoKL (id : ℕ → ℕ) natParity natHalf flipLaw
      = condMutualInfoKL natParity id natHalf flipLaw :=
  condMutualInfoKL_comm measurable_id Measurable.of_discrete Measurable.of_discrete

/-- **Theorem 2.5.2 at `n = 2`, in print's argument order**, on the same family. -/
public theorem mutualInfoKL_chain_rule_natParity' :
    mutualInfoKL (observationVector ![(id : ℕ → ℕ), natParity]) natHalf flipLaw
      = ∑ i : Fin 2, condMutualInfoKL (![(id : ℕ → ℕ), natParity] i) natHalf
          (observationPrefix ![(id : ℕ → ℕ), natParity] i) flipLaw :=
  mutualInfoKL_chain_rule_fin' natHalf _ Measurable.of_discrete fun _ => Measurable.of_discrete

/-- `mutualInfoKL_eq_ofReal_mutualInfo` where both variables have finite range: the parity
of the flip count with itself. -/
public theorem mutualInfoKL_natParity_eq_ofReal :
    mutualInfoKL natParity natParity flipLaw
      = ENNReal.ofReal I[natParity : natParity ; flipLaw] :=
  mutualInfoKL_eq_ofReal_mutualInfo Measurable.of_discrete Measurable.of_discrete

/-- `rnDeriv_singleton` at a point mass, against itself. -/
public theorem rnDeriv_dirac_singleton :
    (Measure.dirac (0 : ℕ)).rnDeriv (Measure.dirac 0) 0
      = Measure.dirac (0 : ℕ) {0} / Measure.dirac (0 : ℕ) {0} :=
  rnDeriv_singleton _ _ (Measure.AbsolutelyContinuous.refl _) 0 (by simp) (by simp)

/-- The alphabets of a two-variable family with different types: `ℕ`, then `Bool`. -/
@[expose] public def natBoolAlph : Fin 2 → Type
  | 0 => ℕ
  | 1 => Bool

/-- Every set of either alphabet is measurable. -/
public instance (i : Fin 2) : MeasurableSpace (natBoolAlph i) := ⊤

public instance (i : Fin 2) : MeasurableSingletonClass (natBoolAlph i) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

public instance : (i : Fin 2) → Countable (natBoolAlph i)
  | 0 => inferInstanceAs (Countable ℕ)
  | 1 => inferInstanceAs (Countable Bool)

/-- The flip count and whether it is even, with their own alphabets. -/
@[expose] public def natBoolFamily : (i : Fin 2) → ℕ → natBoolAlph i
  | 0 => fun n => (n : ℕ)
  | 1 => fun n => (decide (n % 2 = 0) : Bool)

/-- **Theorem 2.5.2 with one alphabet per index** (`mutualInfoKL_chain_rule_pi`), at the
flip count in `ℕ` and its evenness in `Bool`, with `Y = ⌊X / 2⌋`. -/
public theorem mutualInfoKL_chain_rule_natBool :
    mutualInfoKL (observationVectorPi natBoolFamily) natHalf flipLaw
      = ∑ i : Fin 2, condMutualInfoKL (natBoolFamily i) natHalf
          (observationPrefixPi natBoolFamily i) flipLaw :=
  mutualInfoKL_chain_rule_pi natHalf _ Measurable.of_discrete fun _ => Measurable.of_discrete

end AISafetyAtlas.Examples.InformationTheory
