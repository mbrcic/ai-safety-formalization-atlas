import AISafetyAtlas.Sovereignty.AATS
import Mathlib.Data.Finite.Prod

/-!
Wooldridge and van der Hoek (2005), J. Applied Logic 3, §3, p. 402. A
normative system forbids anything that is forbidden by nature:
`∀ α ∈ Ac_Ag : (Q \ ρ(α)) ⊆ η(α)`, for an AATS with finite nonempty state,
agent, action and proposition sets and the two coherence constraints (p. 399).
The cited definition is `AISafetyAtlas.Sovereignty.Norm.RespectsNature`.

The map builds a printed AATS with one agent, one proposition and two
actions, a test action (`true`) and an always-available dummy (`false`). Its
states are pairs of bits: every pair whose first bit is `true`, and each pair
`(false, b)` for which some original incidence `(i, α, q)` has `q ∉ ρ_i(α)`
and `b` records whether `η_i(α)` forbids `α` at `q`. The first bit says
whether the test action is available and the second whether the printed
norm forbids it; the dummy is never forbidden. A joint action steps to the
same state exactly when it is available, so both coherence constraints hold.
The printed requirement at this AATS is then the Lean requirement.

The forward direction is the identity: a printed AATS is an `AATS` value, and
print's disjoint union `Ac_Ag` is the sigma type of the action family.

Checked: `lake env lean docs/provenance/transfers/069-respects-nature.lean`
-/

namespace Transfer069

open AISafetyAtlas.Sovereignty

/-- Print's requirement at a printed AATS (finite nonempty `Q` through `init`, finite nonempty
`Ag`, finite nonempty action sets, finite nonempty `Φ`). -/
def PrintStatement {Q Ag : Type*} {Ac : Ag → Type*} {Φ : Type*} [Finite Q] [Finite Ag]
    [Nonempty Ag] [∀ i, Finite (Ac i)] [∀ i, Nonempty (Ac i)] [Finite Φ] [Nonempty Φ]
    (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) : Prop :=
  ∀ α : Σ i, Ac i, (Set.univ \ S.precond α.1 α.2) ⊆ η α.1 α.2

def LeanStatement {Q Ag : Type*} {Ac : Ag → Type*} {Φ : Type*}
    (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) : Prop :=
  Norm.RespectsNature S η

section

variable {Q Ag : Type*} {Ac : Ag → Type*} {Φ : Type*}

/-- The states of the map: realized (availability, prohibition) bit pairs of the test action. -/
def St (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) : Type :=
  {p : Bool × Bool // p.1 = true ∨
    ∃ i α q, q ∉ S.precond i α ∧ (p.2 = true ↔ q ∈ η i α)}

instance (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) : Finite (St S η) :=
  Subtype.finite

def phiPrecond (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) :
    ∀ _ : Unit, Bool → Set (St S η) :=
  fun _ a ↦ if a then {q | q.1.1 = true} else Set.univ

open Classical in
noncomputable def phi (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) :
    AATS (St S η) Unit (fun _ ↦ Bool) Unit where
  init := ⟨(true, true), Or.inl rfl⟩
  precond := phiPrecond S η
  step := fun q j ↦ if q ∈ phiPrecond S η () (j ()) then some q else none
  interp := fun _ ↦ Set.univ
  nontrivial := fun _ _ ↦ ⟨false, by simp [phiPrecond]⟩
  consistent := by
    intro q j
    by_cases h : q ∈ phiPrecond S η () (j ())
    · rw [if_pos h]
      exact ⟨fun _ _ ↦ h, fun _ ↦ rfl⟩
    · rw [if_neg h]
      exact ⟨fun h' ↦ by simp at h', fun h' ↦ (h (h' ())).elim⟩

def phiNorm (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) : Norm (St S η) Unit (fun _ ↦ Bool) :=
  fun _ a ↦ if a then {q | q.1.2 = true} else ∅

theorem defining_condition (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) :
    LeanStatement S η ↔ PrintStatement (phi S η) (phiNorm S η) := by
  constructor
  · rintro hη ⟨_, a⟩ ⟨⟨b₁, b₂⟩, hq⟩ ⟨-, hpre⟩
    cases a with
    | false => exact (hpre trivial).elim
    | true =>
      change ¬ b₁ = true at hpre
      change b₂ = true
      rcases hq with h | ⟨i, α, q, hq, hb⟩
      · exact (hpre h).elim
      · exact hb.mpr (hη i α hq)
  · intro hp i α q hq
    classical
    let s : St S η := ⟨(false, decide (q ∈ η i α)), Or.inr ⟨i, α, q, hq, by simp⟩⟩
    have h := hp ⟨(), true⟩ (show s ∈ Set.univ \ (phi S η).precond () true from
      ⟨trivial, Bool.false_ne_true⟩)
    exact of_decide_eq_true (show decide (q ∈ η i α) = true from h)

theorem lean_of_print (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) :
    PrintStatement (phi S η) (phiNorm S η) → LeanStatement S η :=
  (defining_condition S η).mpr

theorem print_of_lean [Finite Q] [Finite Ag] [Nonempty Ag] [∀ i, Finite (Ac i)]
    [∀ i, Nonempty (Ac i)] [Finite Φ] [Nonempty Φ] (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) :
    LeanStatement S η → PrintStatement S η :=
  fun h α _ hq ↦ h α.1 α.2 hq.2

end

end Transfer069
