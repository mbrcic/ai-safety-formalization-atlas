module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import AISafetyAtlas.Examples.Causal.OneNodeClass
public import AISafetyAtlas.Examples.Causal.Query
public import AISafetyAtlas.Examples.Conjectures.MAIS.Common

/-!
# MAIS-O34(a) margin sufficiency, resolved negatively

The other clause of `prob:starter-set`(a) — the explicit singleton criterion —
is proved in `Examples/Conjectures/O34Fiber.lean`.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

public theorem maisO34_marginAloneDoesNotIdentify_holds :
    maisO34_marginAloneDoesNotIdentify := by
  unfold maisO34_marginAloneDoesNotIdentify
  obtain ⟨hlam, M, M', hM, hM', hpar, _, hor, hor', hbeh⟩ :=
    margin_class_not_identifiable_two_graphs_real
  refine ⟨skel.mapRat ℝ, ((lam : ℚ) : ℝ), rfl, rfl, hlam, M, M', hM, hM', ?_, ?_,
    Model.ne_of_parents_ne hpar, hbeh⟩
  · rcases hor with h | h
    · exact ⟨Y, X, by rw [h]; simp [arrowXY]⟩
    · exact ⟨X, Y, by rw [h]; simp [arrowYX]⟩
  · rcases hor' with h | h
    · exact ⟨Y, X, by rw [h]; simp [arrowXY]⟩
    · exact ⟨X, Y, by rw [h]; simp [arrowYX]⟩


end AISafetyAtlas.Examples.Conjectures.MAIS
