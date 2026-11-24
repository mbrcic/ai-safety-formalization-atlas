import AISafetyAtlas.Sovereignty.Representation

/-!
Peleg (1998), §3, effectivity-function condition (i), p. 72. The empty
coalition's effectivity family is the single set of all social states,
`E(∅) = A` under print's singleton convention. The cited definition clause is
`IsEffectivityFunction.empty`. The auxiliary game-form routes
(`effectivity_empty_eq_singleton_univ`, `range_outcome_mem_effectivity_empty`,
`vetoGame_effectivity_empty`) are not transferred: print states no game-form
claim about the empty coalition (Definition 3.3 defines alpha-effectivity for
nonempty coalitions only), so there is no printed conclusion to transfer
through.

For the defining clause the map uses one member and keeps the outcome type.
Every printed coalition gets the Lean family of the empty coalition, so the
printed clause at the empty coalition is the Lean clause verbatim.

Checked: `lake env lean docs/provenance/transfers/093-empty-coalition-clause.lean`
-/

namespace Transfer093

def PrintStatement {n : ℕ} {X : Type*} (E : Set (Fin n) → Set (Set X)) : Prop :=
  E ∅ = {Set.univ}

def LeanStatement {N X : Type*} (E : Set N → Set (Set X)) : Prop :=
  E ∅ = {Set.univ}

def phi {N X : Type*} (E : Set N → Set (Set X)) : Set (Fin 1) → Set (Set X) :=
  fun _ => E ∅

theorem defining_condition {N X : Type*} (E : Set N → Set (Set X)) :
    LeanStatement E ↔ PrintStatement (phi E) :=
  Iff.rfl

theorem lean_of_print {N X : Type*} (E : Set N → Set (Set X)) :
    PrintStatement (phi E) → LeanStatement E :=
  (defining_condition E).mpr

theorem print_of_lean {n : ℕ} {X : Type*} (E : Set (Fin n) → Set (Set X)) :
    LeanStatement E → PrintStatement E :=
  fun h => h

end Transfer093
