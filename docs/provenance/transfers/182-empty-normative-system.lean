import AISafetyAtlas.Sovereignty.AATS
import Mathlib.Data.Finite.Prod

/-!
Wooldridge and van der Hoek (2005), J. Applied Logic 3, §3.1, p. 403. The
empty normative system: "any action that is physically/naturally feasible is
legal according to `η_⊥`", `∀ α ∈ Ac_Ag : η_⊥(α) = Q \ ρ(α)`, for an AATS with
finite nonempty state, agent, action and proposition sets and the two
coherence constraints (p. 399). `q ∈ η(α)` means that `η` forbids `α` at `q`
(p. 402). The cited definition is `AISafetyAtlas.Sovereignty.Norm.bot`;
`Norm.top` is cited beside it but defines `η_⊤`, the next printed sentence
(p. 404), and is not transferred here.

The definition is compared through its defining clause: a normative system
`η` is `η_⊥` exactly when `η(α) = Q \ ρ(α)` for every action `α`.

The map, as in transfer 069, builds a printed AATS with one agent, one
proposition and two actions, a test action (`true`) and an always-available
dummy (`false`). Its states are bit pairs: the pair `(true, false)` (the
initial state), and each pair `(b₁, b₂)` realized by some original incidence
`(i, α, q)`, where `b₁` records whether `q ∈ ρ_i(α)` and `b₂` whether
`q ∈ η_i(α)`. The first bit says whether the test action is available and the
second whether the printed norm forbids it; the dummy is never forbidden. A
joint action steps to the same state exactly when it is available, so both
coherence constraints hold. Print's defining clause at this AATS is the Lean
one: at the test action it says `b₂ ↔ ¬ b₁` on every realized pair, and at the
dummy it says `∅ = Q \ Q`. The map records the two atoms of each incidence
separately; the clause relating them is checked by print.

The forward direction is the identity: a printed AATS is an `AATS` value, and
print's disjoint union `Ac_Ag` is the sigma type of the action family.

Checked: `lake env lean docs/provenance/transfers/182-empty-normative-system.lean`
-/

namespace Transfer182

open AISafetyAtlas.Sovereignty

/-- Print's defining clause of `η_⊥` at a printed AATS. -/
def PrintStatement {Q Ag : Type*} {Ac : Ag → Type*} {Φ : Type*} [Finite Q] [Finite Ag]
    [Nonempty Ag] [∀ i, Finite (Ac i)] [∀ i, Nonempty (Ac i)] [Finite Φ] [Nonempty Φ]
    (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) : Prop :=
  ∀ α : Σ i, Ac i, η α.1 α.2 = Set.univ \ S.precond α.1 α.2

def LeanStatement {Q Ag : Type*} {Ac : Ag → Type*} {Φ : Type*}
    (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) : Prop :=
  ∀ i α, η i α = Norm.bot S i α

section

variable {Q Ag : Type*} {Ac : Ag → Type*} {Φ : Type*}

open Classical in
/-- The states of the map: the initial pair and the realized (availability, prohibition) bit
pairs of the test action. -/
def St (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) : Type :=
  {p : Bool × Bool // p = (true, false) ∨
    ∃ i α q, p = (decide (q ∈ S.precond i α), decide (q ∈ η i α))}

instance (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) : Finite (St S η) :=
  Subtype.finite

def phiPrecond (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) :
    ∀ _ : Unit, Bool → Set (St S η) :=
  fun _ a ↦ if a then {q | q.1.1 = true} else Set.univ

open Classical in
noncomputable def phi (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) :
    AATS (St S η) Unit (fun _ ↦ Bool) Unit where
  init := ⟨(true, false), Or.inl rfl⟩
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
  classical
  constructor
  · rintro hη ⟨_, a⟩
    cases a with
    | false => simp [phiNorm, phi, phiPrecond]
    | true =>
      ext ⟨⟨b₁, b₂⟩, hq⟩
      change b₂ = true ↔ (True ∧ ¬ b₁ = true)
      rw [true_and]
      rcases hq with h | ⟨i, α, q, h⟩
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h; simp
      · simp only [Prod.mk.injEq] at h; obtain ⟨rfl, rfl⟩ := h
        rw [hη i α]
        exact ⟨fun h h' ↦ of_decide_eq_true h (of_decide_eq_true h'),
          fun h ↦ decide_eq_true fun h' ↦ h (decide_eq_true h')⟩
  · intro hp i α
    ext q
    let s : St S η := ⟨(decide (q ∈ S.precond i α), decide (q ∈ η i α)), Or.inr ⟨i, α, q, rfl⟩⟩
    have h := congrArg (s ∈ ·) (hp ⟨(), true⟩)
    change (decide (q ∈ η i α) = true) = (s ∈ Set.univ ∧ ¬ decide (q ∈ S.precond i α) = true) at h
    simp only [decide_eq_true_eq, Set.mem_univ, true_and, eq_iff_iff] at h
    simpa [Norm.bot] using h

theorem lean_of_print (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) :
    PrintStatement (phi S η) (phiNorm S η) → LeanStatement S η :=
  (defining_condition S η).mpr

theorem print_of_lean [Finite Q] [Finite Ag] [Nonempty Ag] [∀ i, Finite (Ac i)]
    [∀ i, Nonempty (Ac i)] [Finite Φ] [Nonempty Φ] (S : AATS Q Ag Ac Φ) (η : Norm Q Ag Ac) :
    LeanStatement S η → PrintStatement S η := by
  intro h α
  rw [h α.1 α.2]
  ext q; simp [Norm.bot]

end

end Transfer182
