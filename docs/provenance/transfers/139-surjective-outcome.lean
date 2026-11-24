import AISafetyAtlas.Sovereignty.Separations

/-!
Peleg (1998), Definition 3.3, p. 73: "Now assume that `g` is surjective (onto
`A`)", for a game form `Γ = ⟨N; Σ¹, …, Σⁿ; g; A⟩` (Definition 3.2) with
`N = {1, …, n}`, non-empty strategy sets `Σⁱ` and outcome function
`g : Σ¹ × ⋯ × Σⁿ → A`. The cited declarations read the assumption as
`Function.Surjective G.outcome` for a `GameForm N X` over any player type `N`
and any (possibly empty) strategy types: the hypothesis of
`effectivity_empty_eq_singleton_univ` and `effectivity_univ_eq_nonempty`, the
conclusion of `Represents.surjective_outcome` and
`surjective_shirtGame_outcome`.

This is a definition row (G12). The map sends a Lean game form `G` to a printed
game form with one player, whose strategy set is `Option (∀ i, G.strategy i)`
(non-empty through `none`), social states `Option X`, and outcome
`Option.map G.outcome`. `none` goes to `none`, and the preimage of `some x` is
exactly the set of profiles of `G` producing `x`, so the printed surjectivity
at the image is the Lean surjectivity of `G`. Print's legality (Definition 3.2,
relative to a society's assignment of rights) does not enter the defining
condition; the image is legal for the society with one right that restricts no
strategy.

Checked: `lake env lean docs/provenance/transfers/139-surjective-outcome.lean`
-/

namespace Transfer139

open AISafetyAtlas.Sovereignty

universe u v w

/-- Print's game form (Definition 3.2): members `Fin n`, non-empty strategy
sets, an outcome function into the social states `A`. -/
structure PrintGameForm (n : ℕ) (A : Type v) where
  Sigma : Fin n → Type w
  nonempty : ∀ i, Nonempty (Sigma i)
  g : (∀ i, Sigma i) → A

/-- Print's assumption: `g` is surjective (onto `A`). -/
def PrintStatement {n : ℕ} {A : Type v} (Γ : PrintGameForm.{v, w} n A) : Prop :=
  Function.Surjective Γ.g

/-- The Lean assumption on a `GameForm`. -/
def LeanStatement {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X) : Prop :=
  Function.Surjective G.outcome

/-- One player choosing a profile of `G` or `none`; outcome `Option.map G.outcome`. -/
def phi {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X) :
    PrintGameForm.{v, max u w} 1 (Option X) where
  Sigma := fun _ => Option (∀ i, G.strategy i)
  nonempty := fun _ => ⟨none⟩
  g := fun s => Option.map G.outcome (s 0)

theorem defining_condition {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X) :
    LeanStatement G ↔ PrintStatement (phi G) := by
  constructor
  · intro h y
    cases y with
    | none => exact ⟨fun _ => none, rfl⟩
    | some x =>
      obtain ⟨s, hs⟩ := h x
      exact ⟨fun _ => some s, by simp [phi, hs]⟩
  · intro h x
    obtain ⟨s, hs⟩ := h (some x)
    change Option.map G.outcome (s 0) = some x at hs
    obtain ⟨p, -, hp⟩ := Option.map_eq_some_iff.mp hs
    exact ⟨p, hp⟩

theorem lean_of_print {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X) :
    PrintStatement (phi G) → LeanStatement G :=
  (defining_condition G).mpr

/-- Every printed game form is a `GameForm` on `Fin n`, with the same assumption. -/
def incl {n : ℕ} {A : Type v} (Γ : PrintGameForm.{v, w} n A) : GameForm.{0, v, w} (Fin n) A :=
  ⟨Γ.Sigma, Γ.g⟩

theorem print_of_lean {n : ℕ} {A : Type v} (Γ : PrintGameForm.{v, w} n A) :
    LeanStatement (incl Γ) ↔ PrintStatement Γ :=
  Iff.rfl

end Transfer139
