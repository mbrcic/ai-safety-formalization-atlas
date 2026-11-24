import AISafetyAtlas.Control.VarietyCounting

/-!
W. Ross Ashby, *An Introduction to Cybernetics*, §11/5 (p. 206).
In a table with `r` rows and `c` columns, if each column has distinct entries,
selecting one entry per row yields at least `r / c` distinct outcomes.

The cited declaration is `AISafetyAtlas.Control.card_le_mul_card_admittedOutcomes`.
The map restricts the table to the indicated rows and columns, tags selected outcomes,
and replaces every unselected entry with a fresh tag carrying its row and column.

Checked: `lake env lean docs/provenance/transfers/086-selected-outcome-variety.lean`
-/

namespace Transfer086

open AISafetyAtlas.Control

universe uD uR uE

def PrintStatement : Prop :=
  ∀ (D : Type uD) (R : Type uR) (E : Type uE) [Fintype D] [Fintype R] [DecidableEq E]
    (T : D → R → E) (ρ : D → R), 0 < Fintype.card R →
    (∀ r, Function.Injective (fun d ↦ T d r)) →
    (Fintype.card D : ℚ) / Fintype.card R ≤ (admittedOutcomes T ρ Finset.univ).card

def LeanStatement : Prop :=
  ∀ {D : Type uD} {R : Type uR} {E : Type uE} [DecidableEq R] [DecidableEq E]
    (T : D → R → E) (ρ : D → R) (s : Finset D) (rs : Finset R),
    (∀ d ∈ s, ρ d ∈ rs) →
    (∀ r, Set.InjOn (fun d ↦ T d r) {d | d ∈ s ∧ ρ d = r}) →
    s.card ≤ (admittedOutcomes T ρ s).card * rs.card

variable {D : Type uD} {R : Type uR} {E : Type uE} [DecidableEq R]
  {T : D → R → E} {ρ : D → R} {s : Finset D} {rs : Finset R}

def phi (T : D → R → E) (ρ : D → R) (s : Finset D) (rs : Finset R) :
    s → rs → E ⊕ (s × rs) :=
  fun d r ↦ if ρ d = r then Sum.inl (T d r) else Sum.inr (d, r)

def selection (hρ : ∀ d ∈ s, ρ d ∈ rs) (d : s) : rs :=
  ⟨ρ d, hρ d d.property⟩

theorem print_hyp
    (hcol : ∀ r, Set.InjOn (fun d ↦ T d r) {d | d ∈ s ∧ ρ d = r}) (r : rs) :
    Function.Injective (fun d ↦ phi T ρ s rs d r) := by
  intro a b hab
  apply Subtype.ext
  by_cases ha : ρ a = r <;> by_cases hb : ρ b = r
  · exact hcol r ⟨a.property, ha⟩ ⟨b.property, hb⟩ (by simpa [phi, ha, hb] using hab)
  · simp [phi, ha, hb] at hab
  · simp [phi, ha, hb] at hab
  · exact congrArg (fun p : s × rs ↦ (p.1 : D))
      (Sum.inr.inj (by simpa only [phi, ha, hb, if_false] using hab))

theorem lean_concl [DecidableEq E] [DecidableEq (E ⊕ (s × rs))]
    (hρ : ∀ d ∈ s, ρ d ∈ rs) (hpos : 0 < rs.card)
    (h : (Fintype.card s : ℚ) / Fintype.card rs ≤
      (admittedOutcomes (phi T ρ s rs) (selection hρ) Finset.univ).card) :
    s.card ≤ (admittedOutcomes T ρ s).card * rs.card := by
  have heq : admittedOutcomes (phi T ρ s rs) (selection hρ) Finset.univ =
      (admittedOutcomes T ρ s).image Sum.inl := by
    ext x
    simp [admittedOutcomes, selection, phi]
  rw [heq, Finset.card_image_of_injective _ Sum.inl_injective, Fintype.card_coe,
    Fintype.card_coe, div_le_iff₀ (by exact_mod_cast hpos)] at h
  exact_mod_cast h

theorem lean_of_print : PrintStatement.{uD,uR,max uD uR uE} →
    LeanStatement.{uD,uR,uE} := by
  intro h D R E _ _ T ρ s rs hρ hcol
  classical
  rcases Nat.eq_zero_or_pos rs.card with hc | hc
  · have hs : s = ∅ := Finset.eq_empty_iff_forall_notMem.mpr fun d hd ↦
      Finset.notMem_empty (ρ d) (Finset.card_eq_zero.mp hc ▸ hρ d hd)
    simp [hs]
  · exact lean_concl hρ hc (h s rs _ (phi T ρ s rs) (selection hρ)
      (by simpa using hc) (print_hyp hcol))

theorem print_of_lean : LeanStatement.{uD,uR,uE} → PrintStatement.{uD,uR,uE} := by
  intro h D R E _ _ _ T ρ hpos hcol
  classical
  have hmul := h T ρ Finset.univ Finset.univ (fun d _ ↦ Finset.mem_univ (ρ d))
    (fun r ↦ (hcol r).injOn)
  rw [Finset.card_univ, Finset.card_univ] at hmul
  rw [div_le_iff₀ (by exact_mod_cast hpos)]
  exact_mod_cast hmul

end Transfer086
