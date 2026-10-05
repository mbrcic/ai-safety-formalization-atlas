module

public import AISafetyAtlas.Causal.Model

/-!
# A genuinely categorical causal model

This mirror example witnesses the non-binary surface of `AISafetyAtlas.Causal.Model`.
The root has three states, its binary child depends on that root, and the intervention
profile combines a ternary translation with a non-injective binary state map.
-/

namespace AISafetyAtlas.Examples.Causal.Model

open AISafetyAtlas.Causal

/-- A ternary root and a binary child. -/
@[expose] public def categoricalDim : Bool → ℕ
  | false => 3
  | true => 2

/-- The sole edge is from the ternary root to the binary child. -/
@[expose] public def categoricalParents : Bool → Finset Bool
  | false => ∅
  | true => {false}

/-- The child's probability of state one at each ternary parent state. -/
@[expose] public def childOne (x : Fin 3) : ℚ :=
  if x = 0 then 1 / 4 else if x = 1 then 1 / 2 else 3 / 4

/-- Full-simplex CPTs for the ternary-root, binary-child model. -/
@[expose] public def categoricalCpt :
    (c : Bool) → Fin (categoricalDim c) → Assignment Bool categoricalDim → ℚ
  | false, _, _ => 1 / 3
  | true, a, v => if a.val = 1 then childOne (v false) else 1 - childOne (v false)

private theorem childOne_bounds (x : Fin 3) : 0 ≤ childOne x ∧ childOne x ≤ 1 := by
  fin_cases x <;> norm_num [childOne]

/-- A non-binary model with a nontrivial parent-dependent CPT. -/
@[expose] public def categoricalModel :
    AISafetyAtlas.Causal.Model Bool categoricalDim ℚ where
  dim_pos := by intro c; cases c <;> decide
  parents := categoricalParents
  acyclic := ⟨fun c ↦ if c then 1 else 0, by decide⟩
  cpt := categoricalCpt
  cpt_parents := by
    intro c a v w h
    cases c
    · rfl
    · have hvw : v false = w false := h false (by simp [categoricalParents])
      simp only [categoricalCpt, hvw]
  cpt_nonneg := by
    intro c a v
    cases c
    · norm_num [categoricalCpt]
    · by_cases ha : a.val = 1
      · simp only [categoricalCpt, if_pos ha]
        exact (childOne_bounds (v false)).1
      · simp only [categoricalCpt, if_neg ha]
        linarith [(childOne_bounds (v false)).2]
  cpt_sum := by
    intro c v
    cases c
    · change (∑ _a : Fin 3, (1 / 3 : ℚ)) = 1
      norm_num [Fin.sum_univ_succ]
    · change (∑ a : Fin 2,
        if a.val = 1 then childOne (v false) else 1 - childOne (v false)) = 1
      rw [Fin.sum_univ_two]
      simp

/-- Translation by one modulo three. -/
@[expose] public def ternaryShift (a : Fin 3) : Fin 3 :=
  ⟨(a.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

/-- Translate the ternary root and collapse both child states to zero. -/
@[expose] public def shiftCollapse : InterventionProfile Bool categoricalDim
  | false => ternaryShift
  | true => fun _ ↦ ⟨0, by simp [categoricalDim]⟩

/-- A state used to expose both intervention factors numerically. -/
@[expose] public def witness : Assignment Bool categoricalDim
  | false => ⟨2, by simp [categoricalDim]⟩
  | true => ⟨0, by simp [categoricalDim]⟩

/-- The ternary translation has one preimage, retaining the root mass `1/3`. -/
public theorem factor_root :
    categoricalModel.factor shiftCollapse witness false = 1 / 3 := by
  unfold AISafetyAtlas.Causal.Model.factor
  change (∑ a : Fin 3, if ternaryShift a = (2 : Fin 3) then (1 / 3 : ℚ) else 0) =
    1 / 3
  rw [Fintype.sum_eq_single (1 : Fin 3)]
  · have hshift : ternaryShift (1 : Fin 3) = (2 : Fin 3) := by decide
    simp [hshift]
  · intro b hb
    fin_cases b <;> simp_all [ternaryShift, Fin.ext_iff]

/-- Collapsing the child to zero sums both original child cells to one. -/
public theorem factor_child :
    categoricalModel.factor shiftCollapse witness true = 1 := by
  unfold AISafetyAtlas.Causal.Model.factor
  simpa [shiftCollapse, witness] using categoricalModel.cpt_sum true witness

/-- The general normalization theorem applies to the non-binary translated model. -/
public theorem jointProb_sum_shiftCollapse :
    ∑ v : Assignment Bool categoricalDim, categoricalModel.jointProb shiftCollapse v = 1 :=
  categoricalModel.jointProb_sum shiftCollapse

/-! ## Every model lemma, applied

`AISafetyAtlas.Causal.Model` proves eighteen results that nothing instantiated.
Each is applied below on `categoricalModel`, the ternary-root/binary-child model
this file already builds, or on the binary helpers it shares with the rest of the
cluster. Most are arithmetic facts about one model rather than discoveries; what
they establish is that the hypotheses are inhabited.

Names are written `Causal.Model.…` throughout: this file's own namespace ends in
`Model`, so the short form resolves here and not to the library.
-/

/-- The binary state encoding and its inverse, at both values, and the count of
local interventions on a binary pair. -/
public theorem model_binary_facts :
    binaryState false = 0 ∧ binaryState true = 1 ∧
      finTwoEquiv.symm false = (0 : Fin 2) ∧ finTwoEquiv.symm true = (1 : Fin 2) ∧
      Fintype.card (Fin 2 → Fin 2) = 4 :=
  ⟨Causal.binaryState_false, Causal.binaryState_true, Causal.finTwoEquiv_symm_false,
    Causal.finTwoEquiv_symm_true, Causal.card_binaryLocalIntervention⟩

/-- Every assignment on a binary pair is one of the four `asg` values. -/
public theorem model_assignment_two :
    asg false false
      = asg (finTwoEquiv (asg false false 0)) (finTwoEquiv (asg false false 1)) :=
  Causal.assignment_two_eq _

/-- The factorization, read the RE24 way and summed over the child's states. -/
public theorem model_factor_readings :
    categoricalModel.factor shiftCollapse witness true
        = ∑ a, (if shiftCollapse true a = witness true then
            categoricalModel.cpt true a witness else 0) :=
  Causal.Model.factor_eq_re24 categoricalModel shiftCollapse witness true

public theorem model_factor_sum :
    (∑ b : Fin (categoricalDim true),
      categoricalModel.factor shiftCollapse (Function.update witness true b) true) = 1 :=
  Causal.Model.factor_sum categoricalModel shiftCollapse witness true

/-- The joint law is a probability distribution, and collapses to a point mass
under a profile that fixes every variable. -/
public theorem model_jointProb_readings :
    0 ≤ categoricalModel.jointProb shiftCollapse witness ∧
      (∑ v : Assignment Bool categoricalDim,
        categoricalModel.jointProb shiftCollapse v) = 1 ∧
      categoricalModel.jointProb (Causal.fixProfile witness) witness = 1 :=
  ⟨Causal.Model.jointProb_nonneg categoricalModel shiftCollapse witness,
    Causal.Model.jointProb_sum categoricalModel shiftCollapse,
    by rw [Causal.Model.jointProb_fixProfile categoricalModel witness witness]; simp⟩

/-- Marginals: over no variables the mass is one, over a forced variable it is a
point mass, and adding a variable to its own parents factorizes. -/
public theorem model_marginal_empty :
    categoricalModel.marginal shiftCollapse ∅ witness = 1 :=
  Causal.Model.marginal_empty categoricalModel shiftCollapse witness

public theorem model_marginal_forced :
    categoricalModel.marginal
      (Causal.hardInterventionProfile {true} witness) {true} witness = 1 := by
  rw [Causal.Model.marginal_forced categoricalModel {true} witness
    (Finset.mem_singleton_self true) witness]
  simp

public theorem model_marginal_insert_parents :
    categoricalModel.marginal (Causal.Model.observationalProfile Bool categoricalDim)
        (insert true (categoricalModel.parents true)) witness
      = categoricalModel.marginal (Causal.Model.observationalProfile Bool categoricalDim)
          (categoricalModel.parents true) witness *
        categoricalModel.marginal
          (Causal.hardInterventionProfile (categoricalModel.parents true) witness)
          {true} witness :=
  Causal.Model.marginal_insert_parents categoricalModel true witness

/-- An empty hard intervention is the observational profile, and the difference
operator is linear in a scalar. -/
public theorem model_profile_and_delta :
    Causal.hardInterventionProfile (∅ : Finset Bool) witness
        = Causal.Model.observationalProfile Bool categoricalDim ∧
      categoricalModel.Δ (fun _ => (2 : ℚ) * 1) shiftCollapse
        = 2 * categoricalModel.Δ (fun _ => (1 : ℚ)) shiftCollapse :=
  ⟨Causal.Model.hardInterventionProfile_empty witness,
    Causal.Model.Δ_smul categoricalModel 2 (fun _ => 1) shiftCollapse⟩

/-- `agreeSet` over everything is the single assignment, and filtering it on one
more coordinate is the same as agreeing on that coordinate too. -/
public theorem model_agreeSet_readings :
    Causal.Model.agreeSet (Finset.univ : Finset Bool) witness = {witness} ∧
      (Causal.Model.agreeSet (∅ : Finset Bool) witness).filter
          (fun v => v true = witness true)
        = Causal.Model.agreeSet (insert true (∅ : Finset Bool))
            (Function.update witness true (witness true)) :=
  ⟨Causal.Model.agreeSet_univ witness,
    Causal.Model.agreeSet_filter ∅ witness (by simp) (witness true)⟩

/-- **Forcing every variable collapses the expectation to a point value.**
`Δ` averages a function against the model's law; under `fixProfile` the law is a
point mass, so the average *is* the value there. This is the degenerate case
every intervention argument checks itself against, and nothing had run it. -/
public theorem categorical_Δ_fixProfile (g : Causal.Assignment Bool categoricalDim → ℚ)
    (target : Causal.Assignment Bool categoricalDim) :
    categoricalModel.Δ g (Causal.fixProfile target) = g target :=
  Causal.Model.Δ_fixProfile categoricalModel g target

end AISafetyAtlas.Examples.Causal.Model
