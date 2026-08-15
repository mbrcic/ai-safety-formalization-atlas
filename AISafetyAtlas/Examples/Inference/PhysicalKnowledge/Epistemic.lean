module

public import AISafetyAtlas.Inference.PhysicalKnowledge.Epistemic
public import AISafetyAtlas.Examples.Inference.Device
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Tactic.FinCases

/-!
# Executable epistemic boundaries for Wolpert 2018

Finite certificates exercise both the positive hypotheses and the boundaries
that distinguish physical knowledge from ordinary logical omniscience.

* `corollary3_nonvacuous` and `corollary24_nonvacuous` reuse the 2008 row/column
  devices and add a physical-knowledge certificate, showing that the
  three-function impossibility is attained by the shipped model.
* `distribution_failure` is the paper's Example 9 phenomenon: one device knows
  `Γ₁`, knows the valid implication `Γ₁ ⇒ Γ₂`, and `Γ₂` is true throughout the
  context, but the device does not physically know `Γ₂` because it cannot weakly
  infer it on counterfactual setup fibres.
* `corollary21_ii_counterexample` refutes the second disjunct of Corollary 21(ii)
  as printed. All refinement and physical-knowledge premises are inhabited, but
  the printed consequent is false.
-/

namespace AISafetyAtlas.Examples.Inference.PhysicalKnowledge.Epistemic

open AISafetyAtlas.Inference

/-! ## Corollary 3 is non-vacuous -/

open AISafetyAtlas.Examples.Inference.Device in
/-- The row/column devices already used for the 2008 Theorem 1 example have
different conclusion partitions. -/
public theorem row_col_conclusions_inequivalent :
    ¬ FunctionallyEquivalent colDevice.concl rowDevice.concl := by
  intro h
  have heq := (h (false, false) (true, false)).mp rfl
  contradiction

open AISafetyAtlas.Examples.Inference.Device in
/-- The hypotheses of the three-function gap occur in the shipped device model,
so Corollary 3 is not merely a conditional theorem over an empty class. -/
public theorem corollary3_nonvacuous :
    ∃ Γ₀ Γ₁ Γ₂ : Bool × Bool → Bool,
      Function.Surjective Γ₀ ∧ Function.Surjective Γ₁ ∧
      Function.Surjective Γ₂ ∧
      ¬ FunctionallyEquivalent Γ₀ Γ₁ ∧
      ¬ FunctionallyEquivalent Γ₀ Γ₂ ∧
      ¬ FunctionallyEquivalent Γ₁ Γ₂ ∧
      ¬ WeaklyInfers colDevice Γ₀ ∧
      ¬ WeaklyInfers colDevice Γ₁ ∧
      ¬ WeaklyInfers colDevice Γ₂ :=
  exists_three_inequivalent_not_weaklyInfers
    row_col_distinguishable.symm row_col_conclusions_inequivalent row_infers_col

open AISafetyAtlas.Examples.Inference.Device in
/-- Context in which the column conclusion is constantly true while both row
setup blocks remain available. -/
public abbrev rowKnowsColWorlds : Set (Bool × Bool) := {u | u.2 = true}

open AISafetyAtlas.Examples.Inference.Device in
private def rowKnowsColBlock
    (g : ImageValue colDevice.concl) : SetupBlock rowDevice :=
  ⟨!g.1, ⟨(!g.1, g.1), rfl⟩⟩

open AISafetyAtlas.Examples.Inference.Device in
/-- The row device physically knows the column conclusion is true on the
refining context. This strengthens the existing one-way weak-inference example
enough to inhabit Corollary 24. -/
public def rowKnowsColWitness :
    PhysicalKnowledgeWitness rowDevice colDevice.concl true rowKnowsColWorlds := by
  refine {
    target_realized := ⟨(false, true), rfl⟩
    selector := rowKnowsColBlock
    correct := ?_
    yes_nonempty := ?_
    yes_on := ?_
    no_nonempty := ?_
    no_on := ?_ }
  · intro g u hu
    rcases u with ⟨a, b⟩
    change a = !g.1 at hu
    subst a
    cases hg : g.1 <;> cases b <;> simp
  · exact ⟨(false, true), rfl, rfl⟩
  · rintro ⟨a, b⟩ hb ha
    change b = true at hb
    change a = false at ha
    subst a
    subst b
    rfl
  · intro g hg
    have hfalse : g.1 = false := by cases h : g.1 <;> simp_all
    exact ⟨(true, true), rfl, by simp [rowKnowsColBlock, hfalse]⟩
  · intro g hg u huW huX
    have hfalse : g.1 = false := by cases h : g.1 <;> simp_all
    rcases u with ⟨a, b⟩
    change b = true at huW
    change a = !g.1 at huX
    subst a
    subst b
    simp [hfalse]

open AISafetyAtlas.Examples.Inference.Device in
public theorem row_physicallyKnows_col :
    PhysicallyKnows rowDevice colDevice.concl true rowKnowsColWorlds :=
  ⟨rowKnowsColWitness⟩

open AISafetyAtlas.Examples.Inference.Device in
public theorem rowKnowsColWorlds_refines :
    RefinesOn rowKnowsColWorlds colDevice.concl := by
  intro u v hu hv
  exact hu.trans hv.symm

open AISafetyAtlas.Examples.Inference.Device in
/-- Corollary 24's full physical-knowledge premise is inhabited, not merely its
underlying Corollary 3 device relation. -/
public theorem corollary24_nonvacuous :
    ∃ Γ₀ Γ₁ Γ₂ : Bool × Bool → Bool,
      Function.Surjective Γ₀ ∧ Function.Surjective Γ₁ ∧
      Function.Surjective Γ₂ ∧
      ¬ FunctionallyEquivalent Γ₀ Γ₁ ∧
      ¬ FunctionallyEquivalent Γ₀ Γ₂ ∧
      ¬ FunctionallyEquivalent Γ₁ Γ₂ ∧
      (∀ (W : Set (Bool × Bool)) (g : Bool), RefinesOn W Γ₀ →
        ¬ PhysicallyKnows colDevice Γ₀ g W) ∧
      (∀ (W : Set (Bool × Bool)) (g : Bool), RefinesOn W Γ₁ →
        ¬ PhysicallyKnows colDevice Γ₁ g W) ∧
      (∀ (W : Set (Bool × Bool)) (g : Bool), RefinesOn W Γ₂ →
        ¬ PhysicallyKnows colDevice Γ₂ g W) :=
  corollary24 row_col_distinguishable.symm
    row_col_conclusions_inequivalent rowKnowsColWorlds_refines
    row_physicallyKnows_col

/-! ## Example 9: distribution fails -/

/-- Rows of a finite thermometer-style model. -/
public structure DistributionRow where
  setup : Fin 3
  concl : Bool
  gamma1 : Bool
  gamma2 : Bool

/-- Eight named worlds keep the certificate executable without arithmetic on
state indices obscuring the setup fibres. -/
public inductive DistributionWorld
  | w0 | w1 | w2 | w3 | w4 | w5 | w6 | w7
  deriving DecidableEq

/-- Three setup blocks. The first two infer `Γ₁`; the third answers the always
true implication. Every block deliberately fails at least one `Γ₂` probe. -/
public def distributionTable : DistributionWorld → DistributionRow
  | .w0 => ⟨0, true,  true,  true⟩
  | .w1 => ⟨0, false, false, false⟩
  | .w2 => ⟨0, false, false, true⟩
  | .w3 => ⟨1, false, true,  true⟩
  | .w4 => ⟨1, true,  false, false⟩
  | .w5 => ⟨1, true,  false, true⟩
  | .w6 => ⟨2, true,  true,  true⟩
  | .w7 => ⟨2, true,  false, false⟩

public abbrev distributionDevice : InferenceDevice DistributionWorld where
  Setup := Fin 3
  setup := fun u => (distributionTable u).setup
  concl := fun u => (distributionTable u).concl
  concl_surjective := fun
    | false => ⟨.w1, by simp [distributionTable]⟩
    | true => ⟨.w0, by simp [distributionTable]⟩

public abbrev gamma1 : DistributionWorld → Bool := fun u => (distributionTable u).gamma1
public abbrev gamma2 : DistributionWorld → Bool := fun u => (distributionTable u).gamma2
public abbrev distributionWorlds : Set DistributionWorld := {u | gamma1 u = true}

private def setup0 : distributionDevice.Setup := by change Fin 3; exact 0
private def setup1 : distributionDevice.Setup := by change Fin 3; exact 1
private def setup2 : distributionDevice.Setup := by change Fin 3; exact 2

private def gamma1Block (g : ImageValue gamma1) : SetupBlock distributionDevice :=
  if h : g.1 = true then
    ⟨setup0, ⟨.w0, by change (0 : Fin 3) = 0; rfl⟩⟩
  else
    ⟨setup1, ⟨.w3, by change (1 : Fin 3) = 1; rfl⟩⟩

public def knowsGamma1Witness :
    PhysicalKnowledgeWitness distributionDevice gamma1 true distributionWorlds := by
  refine {
    target_realized := ⟨.w0, rfl⟩
    selector := gamma1Block
    correct := ?_
    yes_nonempty := ?_
    yes_on := ?_
    no_nonempty := ?_
    no_on := ?_ }
  · intro g u hu
    cases u <;> cases hg : g.1 <;>
      simp [distributionDevice, distributionTable, gamma1, gamma1Block,
        setup0, setup1, hg] at hu ⊢
  · exact ⟨.w0, rfl, by rfl⟩
  · intro u huW huX
    cases u <;>
      simp [distributionWorlds, distributionDevice, distributionTable, gamma1,
        gamma1Block, setup0] at huW huX ⊢
  · intro g hg
    exact ⟨.w3, rfl, by simp [gamma1Block, hg]; rfl⟩
  · intro g hg u huW huX
    cases u <;>
      simp [distributionWorlds, distributionDevice, distributionTable, gamma1,
        gamma1Block, hg, setup1] at huW huX ⊢

private def implicationBlock
    (_g : ImageValue (Implies gamma1 gamma2)) : SetupBlock distributionDevice :=
  ⟨setup2, ⟨.w6, by change (2 : Fin 3) = 2; rfl⟩⟩

private theorem implication_always_true :
    ∀ u : DistributionWorld, Implies gamma1 gamma2 u = true := by
  intro u
  cases u <;> decide

public def knowsImplicationWitness :
    PhysicalKnowledgeWitness distributionDevice (Implies gamma1 gamma2) true
      distributionWorlds := by
  refine {
    target_realized := ⟨.w0, by decide⟩
    selector := implicationBlock
    correct := ?_
    yes_nonempty := ?_
    yes_on := ?_
    no_nonempty := ?_
    no_on := ?_ }
  · intro g u hu
    have hg : g.1 = true := by
      obtain ⟨w, hw⟩ := g.2
      rw [implication_always_true w] at hw
      exact hw.symm
    cases u <;>
      simp [distributionDevice, distributionTable, implicationBlock, setup2, hg,
        implication_always_true] at hu ⊢
  · exact ⟨.w6, rfl, by rfl⟩
  · intro u _huW huX
    cases u <;>
      simp [distributionDevice, distributionTable, implicationBlock, setup2] at huX ⊢
  · intro g hg
    exact (hg (by
      obtain ⟨w, hw⟩ := g.2
      rw [implication_always_true w] at hw
      exact hw.symm)).elim
  · intro g hg
    exact (hg (by
      obtain ⟨w, hw⟩ := g.2
      rw [implication_always_true w] at hw
      exact hw.symm)).elim

public theorem knows_gamma1 :
    PhysicallyKnows distributionDevice gamma1 true distributionWorlds :=
  ⟨knowsGamma1Witness⟩

public theorem knows_implication :
    PhysicallyKnows distributionDevice (Implies gamma1 gamma2) true
      distributionWorlds :=
  ⟨knowsImplicationWitness⟩

public theorem distributionWorlds_refines_gamma1 :
    RefinesOn distributionWorlds gamma1 := by
  intro u v hu hv
  exact hu.trans hv.symm

public theorem distributionWorlds_refines_implication :
    RefinesOn distributionWorlds (Implies gamma1 gamma2) := by
  intro u v _ _
  rw [implication_always_true u, implication_always_true v]

public theorem gamma2_true_on_distributionWorlds :
    TrueOn distributionWorlds gamma2 :=
  corollary20_ii distributionWorlds_refines_gamma1
    distributionWorlds_refines_implication knows_gamma1 knows_implication

/-- No setup block answers even the identity probe of `Γ₂` correctly. -/
public theorem not_weaklyInfers_gamma2 :
    ¬ WeaklyInfers distributionDevice gamma2 := by
  intro h
  obtain ⟨x, _hx, hrun⟩ := h true id isProbe_id ⟨.w0, rfl⟩
  change Fin 3 at x
  fin_cases x
  · have := hrun .w2 rfl
    contradiction
  · have := hrun .w3 rfl
    contradiction
  · have := hrun .w7 rfl
    contradiction

/-- **Example 9 / failure of distribution.** The device knows the antecedent
and knows the implication; the consequent is true, but it is not physically
known at any value over any context because it is not weakly inferred. -/
public theorem distribution_failure :
    PhysicallyKnows distributionDevice gamma1 true distributionWorlds ∧
    PhysicallyKnows distributionDevice (Implies gamma1 gamma2) true
      distributionWorlds ∧
    TrueOn distributionWorlds gamma2 ∧
    (∀ (W : Set DistributionWorld) (γ : Bool),
      ¬ PhysicallyKnows distributionDevice gamma2 γ W) := by
  refine ⟨knows_gamma1, knows_implication, gamma2_true_on_distributionWorlds, ?_⟩
  intro W γ h
  exact not_weaklyInfers_gamma2 h.weaklyInfers

/-! ## Corollary 21(ii) as printed is false -/

public structure Cor21World where
  candidate : Bool
  context : Bool
  third : Bool

public abbrev cor21Gamma1 : Cor21World → Bool := Cor21World.context
public abbrev cor21Gamma2 : Cor21World → Bool := fun u => !u.context
public abbrev cor21Gamma3 : Cor21World → Bool := Cor21World.third
public abbrev cor21Composite : Cor21World → Bool :=
  Implies cor21Gamma1 cor21Gamma3

public abbrev cor21Device : InferenceDevice Cor21World where
  Setup := Bool
  setup := Cor21World.candidate
  concl := fun u => decide (cor21Composite u = u.candidate)
  concl_surjective := fun
    | false => ⟨⟨false, false, false⟩, rfl⟩
    | true => ⟨⟨true, false, false⟩, rfl⟩

public abbrev cor21Worlds : Set Cor21World :=
  {u | u.context = false ∧ u.third = false}

private def cor21Block (g : ImageValue cor21Composite) : SetupBlock cor21Device :=
  ⟨g.1, ⟨⟨g.1, false, false⟩, by simp [cor21Device]⟩⟩

public def cor21KnowsCompositeWitness :
    PhysicalKnowledgeWitness cor21Device cor21Composite true cor21Worlds := by
  refine {
    target_realized := ⟨⟨false, false, false⟩, rfl⟩
    selector := cor21Block
    correct := ?_
    yes_nonempty := ?_
    yes_on := ?_
    no_nonempty := ?_
    no_on := ?_ }
  · intro g u hu
    rcases u with ⟨candidate, context, third⟩
    simp only [cor21Device, cor21Block] at hu
    subst candidate
    simp
  · exact ⟨⟨true, false, false⟩, ⟨rfl, rfl⟩, rfl⟩
  · rintro ⟨candidate, context, third⟩ ⟨hc, ht⟩ huX
    change context = false at hc
    change third = false at ht
    simp only [cor21Device, cor21Block] at huX
    subst context
    subst third
    subst candidate
    rfl
  · intro g hg
    have hfalse : g.1 = false := by cases h : g.1 <;> simp_all
    exact ⟨⟨false, false, false⟩, ⟨rfl, rfl⟩, by simp [cor21Block, hfalse]⟩
  · intro g hg u huW huX
    have hfalse : g.1 = false := by cases h : g.1 <;> simp_all
    rcases u with ⟨candidate, context, third⟩
    rcases huW with ⟨hc, ht⟩
    change context = false at hc
    change third = false at ht
    simp only [cor21Device, cor21Block] at huX
    subst context
    subst third
    rw [hfalse] at huX
    subst candidate
    rfl

public theorem cor21_knows_composite :
    PhysicallyKnows cor21Device cor21Composite true cor21Worlds :=
  ⟨cor21KnowsCompositeWitness⟩

public theorem cor21_refines_first_implication :
    RefinesOn cor21Worlds (Implies cor21Gamma1 cor21Gamma2) := by
  rintro ⟨c₁, x₁, z₁⟩ ⟨c₂, x₂, z₂⟩ ⟨hx₁, _⟩ ⟨hx₂, _⟩
  change x₁ = false at hx₁
  change x₂ = false at hx₂
  subst x₁
  subst x₂
  rfl

public theorem cor21_refines_second_implication :
    RefinesOn cor21Worlds (Implies cor21Gamma2 cor21Gamma3) := by
  rintro ⟨c₁, x₁, z₁⟩ ⟨c₂, x₂, z₂⟩ ⟨hx₁, hz₁⟩ ⟨hx₂, hz₂⟩
  change x₁ = false at hx₁
  change z₁ = false at hz₁
  change x₂ = false at hx₂
  change z₂ = false at hz₂
  subst x₁
  subst z₁
  subst x₂
  subst z₂
  rfl

public theorem cor21_first_implication_true :
    TrueOn cor21Worlds (Implies cor21Gamma1 cor21Gamma2) := by
  rintro ⟨candidate, context, third⟩ ⟨hc, _⟩
  change context = false at hc
  subst context
  rfl

public theorem cor21_second_implication_not_true :
    ¬ TrueOn cor21Worlds (Implies cor21Gamma2 cor21Gamma3) := by
  intro h
  have := h ⟨false, false, false⟩ ⟨rfl, rfl⟩
  contradiction

/-- **Counterexample to Corollary 21(ii) as printed.** Its refinement
hypotheses hold; `Γ₁ ⇒ Γ₂` is true; the device knows `Γ₁ ⇒ Γ₃`; nevertheless
the printed conclusion `Γ₂ ⇒ Γ₃` is false. -/
public theorem corollary21_ii_counterexample :
    RefinesOn cor21Worlds (Implies cor21Gamma1 cor21Gamma2) ∧
    RefinesOn cor21Worlds (Implies cor21Gamma2 cor21Gamma3) ∧
    TrueOn cor21Worlds (Implies cor21Gamma1 cor21Gamma2) ∧
    PhysicallyKnows cor21Device (Implies cor21Gamma1 cor21Gamma3) true cor21Worlds ∧
    ¬ TrueOn cor21Worlds (Implies cor21Gamma2 cor21Gamma3) :=
  ⟨cor21_refines_first_implication, cor21_refines_second_implication,
    cor21_first_implication_true, cor21_knows_composite,
    cor21_second_implication_not_true⟩

end AISafetyAtlas.Examples.Inference.PhysicalKnowledge.Epistemic
