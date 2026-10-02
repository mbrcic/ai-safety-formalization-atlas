module

public import AISafetyAtlas.Compositional.Hyperproperties.PrefixTopology
public import AISafetyAtlas.Compositional.Hyperproperties.Product

/-!
# Subset closure is strictly weaker than hypersafety

`AISafetyAtlas.Compositional.Hyperproperties.subsetClosed_of_isHyperSafetyOp` is
the inclusion half of Clarkson & Schneider's Theorem 1, `SHP ⊂ SSC`. This module
supplies the **strictness**: a hyperproperty that is subset closed and is not
hypersafety, so the inclusion is proper and the theorem is not an equality in
disguise.

The witness is a lifted trace property over a *liveness* trace property, which is
their own reason the inclusion is strict. Traces are natural numbers, a prefix is
a number below the trace, and the trace property is "not zero" — every prefix
extends into it, so no finite observation can ever be bad, and a system that
contains `0` violates the hyperproperty without any finite witness.

The degenerate route — an empty `Prefix` type, where the only observation is the
empty one — is deliberately **not** taken: it would make the strictness an
artifact of there being nothing to observe rather than of the property's shape.
-/

namespace AISafetyAtlas.Examples.Compositional.Hyperproperties

open AISafetyAtlas.Compositional.Hyperproperties

/-- A prefix is a number at most the trace it is a prefix of. -/
@[expose] public def le : ℕ → ℕ → Prop := fun p t => p ≤ t

/-- **A liveness trace property**: every finite prefix extends into it. -/
@[expose] public def nonzero : TraceSystem ℕ := {t | t ≠ 0}

/-- The lifted trace property: the systems contained in `nonzero`. -/
@[expose] public def liveLift : Hyperproperty ℕ := {S | S ⊆ nonzero}

/-- **It is subset closed.** Immediate: a subset of a subset of `nonzero` is one. -/
public theorem liveLift_subsetClosed : SubsetClosed liveLift :=
  fun _ hT _ hsub => hsub.trans hT

/-- The system `{0}` violates it. -/
public theorem zero_violates : ({0} : TraceSystem ℕ) ∉ liveLift := by
  intro h
  exact absurd (h (Set.mem_singleton 0)) (by simp [nonzero])

/--
**And it is not hypersafety.** No finite observation witnesses the violation:
every prefix of `0` is `0`, `0` is also a prefix of `1`, and `{1}` satisfies the
hyperproperty — so any observation the violating system realizes is realized by a
satisfying one, and no bad observation exists.
-/
public theorem liveLift_not_hyperSafety : ¬ IsHyperSafetyOp le liveLift := by
  intro h
  obtain ⟨M, hreal, hbad⟩ := h {0} zero_violates
  refine hbad {1} (fun p hp => ⟨1, Set.mem_singleton 1, ?_⟩) ?_
  · obtain ⟨t, ht, hpt⟩ := hreal p hp
    have ht0 : t = 0 := ht
    subst ht0
    have hp0 : p ≤ 0 := hpt
    exact Nat.le_trans hp0 (Nat.zero_le 1)
  · intro t ht
    have : t = 1 := ht
    simp [nonzero, this]

/--
**Theorem 1's inclusion is strict**, at this witness: subset closed, and not
hypersafety.
-/
public theorem subsetClosed_not_hyperSafety :
    SubsetClosed liveLift ∧ ¬ IsHyperSafetyOp le liveLift :=
  ⟨liveLift_subsetClosed, liveLift_not_hyperSafety⟩

/-! ## The rest of the reduction, applied -/

/-- Every system realizes the empty observation, at this file's prefix
relation. -/
theorem le_cone_empty :
    Cone le (∅ : Observation ℕ) = Set.univ :=
  cone_empty le

/-- `Set.univ` is a hyperproperty everything satisfies, so it is trivially
hypersafety: the violation clause is never triggered. -/
theorem univ_isHyperSafetyOp : IsHyperSafetyOp le (Set.univ : Hyperproperty ℕ) :=
  fun S hS => absurd (Set.mem_univ S) hS

/-- **The inclusion half of Theorem 1**, at the trivial hypersafety witness. -/
theorem univ_subsetClosed : SubsetClosed (Set.univ : Hyperproperty ℕ) :=
  subsetClosed_of_isHyperSafetyOp le univ_isHyperSafetyOp

/-- Reordering a two-trace tuple does not change the traces it mentions. -/
theorem toBatch_perm_example :
    toBatch (Fin.val ∘ Equiv.swap (0 : Fin 2) 1) = toBatch (Fin.val : Fin 2 → ℕ) :=
  toBatch_perm Fin.val (Equiv.swap 0 1)

/-- **The `k`-safety reduction's predicate is honestly a safety predicate.** -/
theorem selfCompositionSafe_liveLift_isSafety :
    IsSafetyPredicate le (SelfCompositionSafe le 1 liveLift) :=
  self_composition_is_safety le 1 liveLift

/-- **Every hyperproperty decomposes**, at `liveLift` under this file's own
observation topology. -/
theorem liveLift_decomposition :
    letI : TopologicalSpace (TraceSystem ℕ) := prefixTopology le
    ∃ safetyPart livenessPart : Hyperproperty ℕ,
      IsHyperSafety safetyPart ∧ IsHyperLiveness livenessPart ∧
        liveLift = safetyPart ∩ livenessPart :=
  letI : TopologicalSpace (TraceSystem ℕ) := prefixTopology le
  hypersafety_hyperliveness_decomposition liveLift

end AISafetyAtlas.Examples.Compositional.Hyperproperties
