module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import AISafetyAtlas.Examples.Causal.OneNodeClass
public import AISafetyAtlas.Examples.Causal.Query
public import AISafetyAtlas.Examples.Conjectures.MAIS.Common

/-!
# MAIS-O23 resolved, negatively

The registered proposition, discharged by the real-chart collision.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ## The two already-checked negatives, named as their registered propositions

`margin_class_not_identifiable` and its two-graph companion carry the witnesses;
these state that they *inhabit* the registered `Prop`s, so every resolved row in
`conjectures.yaml` has a theorem whose statement is the ledger's own
declaration. -/

public theorem maisO23_marginsDoNotSuffice_holds :
    maisO23_marginsDoNotSuffice := by
  unfold maisO23_marginsDoNotSuffice
  obtain ⟨hlam, M, M', hM, hM', _, hne, hbeh⟩ := margin_class_not_identifiable_real
  exact ⟨1, skel.mapRat ℝ, ((lam : ℚ) : ℝ), hlam, M, M', hM, hM', hne, hbeh⟩


end AISafetyAtlas.Examples.Conjectures.MAIS
