module

public import AISafetyAtlas.Sovereignty.AlphaVersusActual

/-!
# Example 1 of Chen, Ju and Ågotnes, applied

Witnesses for the module AISafetyAtlas.Sovereignty.AlphaVersusActual.

* In the second warehouse-gate scenario the whole state set is an alpha power of
  robot a, obtained from the actual power of closing the gate through
  `AISafetyAtlas.Sovereignty.alphaEff_eq_supersets_actualEff`, although it is not
  an actual power there: the information alpha powers lose.
* `AISafetyAtlas.Sovereignty.alphaEff_eq_of_actualEff_eq` applied across the two
  states of the first scenario.
* `AISafetyAtlas.Sovereignty.exists_alphaEff_eq_actualEff_ne` read in every one
  of print's eight classes: no class lets alpha powers determine actual powers.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-- In the second scenario robot a has the whole state set as an alpha power,
because it contains the actual power of closing the gate, and yet the whole
state set is not an actual power of a there. -/
public theorem warehouseGate_univ_alpha_not_actual (s : WarehouseGate.GateState) :
    Set.univ ∈ alphaEff WarehouseGate.secondScenario {WarehouseGate.Robot.a} s ∧
      Set.univ ∉ actualEff WarehouseGate.secondScenario {WarehouseGate.Robot.a} s := by
  refine ⟨?_, (WarehouseGate.univ_mem_actualEff_first_not_second s).2⟩
  rw [AISafetyAtlas.Sovereignty.alphaEff_eq_supersets_actualEff]
  refine ⟨{WarehouseGate.GateState.w₁}, ?_, Set.subset_univ _⟩
  rw [AISafetyAtlas.Sovereignty.WarehouseGate.actualEff_secondScenario_a]
  exact Or.inl rfl

/-- Equal actual powers of robot a at the two states of the first scenario give
equal alpha powers there. -/
public theorem warehouseGate_alphaEff_states_eq :
    alphaEff WarehouseGate.firstScenario {WarehouseGate.Robot.a} WarehouseGate.GateState.w₁ =
      alphaEff WarehouseGate.firstScenario {WarehouseGate.Robot.a}
        WarehouseGate.GateState.w₂ :=
  AISafetyAtlas.Sovereignty.alphaEff_eq_of_actualEff_eq
    ((WarehouseGate.actualEff_firstScenario_a _).trans
      (WarehouseGate.actualEff_firstScenario_a _).symm)

/-- Print's alpha table at the four coalitions, in the first scenario. -/
example (s : WarehouseGate.GateState) :
    alphaEff WarehouseGate.firstScenario {WarehouseGate.Robot.a, WarehouseGate.Robot.b} s =
        {X | X.Nonempty} ∧
      alphaEff WarehouseGate.firstScenario {WarehouseGate.Robot.b} s = {Set.univ} ∧
      alphaEff WarehouseGate.firstScenario ∅ s = {Set.univ} :=
  ⟨AISafetyAtlas.Sovereignty.WarehouseGate.alphaEff_scenario_of_mem true (Or.inl rfl) s,
    AISafetyAtlas.Sovereignty.WarehouseGate.alphaEff_scenario_of_not_mem true
      (C := {WarehouseGate.Robot.b}) (by simp) s,
    AISafetyAtlas.Sovereignty.WarehouseGate.alphaEff_scenario_of_not_mem true
      (Set.notMem_empty _) s⟩

/-- The two scenarios agree on alpha powers of robot a and differ on its actual
powers. -/
example :
    alphaEff WarehouseGate.firstScenario {WarehouseGate.Robot.a} WarehouseGate.GateState.w₁ =
        alphaEff WarehouseGate.secondScenario {WarehouseGate.Robot.a}
          WarehouseGate.GateState.w₁ ∧
      actualEff WarehouseGate.firstScenario {WarehouseGate.Robot.a}
          WarehouseGate.GateState.w₁ ≠
        actualEff WarehouseGate.secondScenario {WarehouseGate.Robot.a}
          WarehouseGate.GateState.w₁ := by
  refine ⟨AISafetyAtlas.Sovereignty.WarehouseGate.alphaEff_firstScenario_eq_secondScenario _ _,
    fun h => ?_⟩
  have h1 := AISafetyAtlas.Sovereignty.WarehouseGate.actualEff_firstScenario_a
    WarehouseGate.GateState.w₁
  exact (AISafetyAtlas.Sovereignty.WarehouseGate.univ_mem_actualEff_first_not_second
    WarehouseGate.GateState.w₁).2 (h ▸ (h1 ▸ Or.inr (Or.inr rfl)))

/-- Both scenarios are frames of every one of print's eight classes. -/
example (X : FrameClass) :
    IsFrame X WarehouseGate.firstScenario ∧ IsFrame X WarehouseGate.secondScenario :=
  ⟨isFrame_of_sid X (AISafetyAtlas.Sovereignty.WarehouseGate.scenario_isFrame_sid true),
    isFrame_of_sid X (AISafetyAtlas.Sovereignty.WarehouseGate.scenario_isFrame_sid false)⟩

/-- **In no class do alpha powers determine actual powers.** For each of print's
eight labels, it is false that any two frames of that class with the same alpha
powers everywhere have the same actual powers everywhere. -/
public theorem not_alphaEff_determines_actualEff (X : FrameClass) :
    ¬ ∀ (AG ST AC : Type) (F₁ F₂ : ActionFrame AG ST AC), IsFrame X F₁ → IsFrame X F₂ →
      (∀ C s, alphaEff F₁ C s = alphaEff F₂ C s) → ∀ C s, actualEff F₁ C s = actualEff F₂ C s := by
  intro h
  obtain ⟨AG, ST, AC, _, F₁, F₂, h₁, h₂, halpha, C, s, hne⟩ :=
    AISafetyAtlas.Sovereignty.exists_alphaEff_eq_actualEff_ne
  exact hne (h AG ST AC F₁ F₂ (isFrame_of_sid X h₁) (isFrame_of_sid X h₂) halpha C s)

end AISafetyAtlas.Examples.Sovereignty
