module

public import AISafetyAtlas.Causal.ParameterChart
public import AISafetyAtlas.Examples.Causal.OneNodeClass

/-!
# Two leaves of the chart, at models `OneNodeClass` already built

Both facts hold for any model or any richness witness, so the one-node class's
own `model` and `containsChartBox` are enough to ground them -- no new
construction.
-/

namespace AISafetyAtlas.Examples.Causal.ParameterChart

open AISafetyAtlas.Causal AISafetyAtlas.Analysis
open AISafetyAtlas.Examples.Causal.OneNodeClass

/-- **Reading a model's point and rebuilding it is the identity, at the
witness.** `model p h0 h1` has no parents, so its own parent map is the
graph the round trip is checked against. -/
public theorem model_ofChart_chartOn (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    Model.ofChart (fun _ : Fin 1 ↦ (∅ : Finset (Fin 1))) (model p h0 h1).acyclic
        ((model p h0 h1).chartOn (fun _ ↦ ∅))
        ((model p h0 h1).chartOn_mem_unitInterval (fun _ ↦ ∅))
      = model p h0 h1 :=
  Model.ofChart_chartOn (model p h0 h1) rfl

/-- **A richness witness is itself semialgebraic, at the class `OneNodeClass`
already certifies richness for.** -/
public theorem exists_semialgebraic_of_containsChartBox :
    ∃ (G : Fin 1 → Finset (Fin 1)) (corner : ChartIndex G → ℝ),
      IsSemialgebraic (ClosedBox corner (1 - 2 * lam)) ∧
        ClosedBox corner (1 - 2 * lam) ⊆
          Model.chartSlice {M | sk.MarginClass M lam} G :=
  isSemialgebraic_of_containsChartBox containsChartBox

end AISafetyAtlas.Examples.Causal.ParameterChart
