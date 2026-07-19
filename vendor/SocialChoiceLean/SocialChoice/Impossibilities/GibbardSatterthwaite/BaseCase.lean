import SocialChoice.Axioms.Core
import SocialChoice.Axioms.Unanimity
import SocialChoice.Axioms.Strategyproofness
import SocialChoice.Axioms.Dictatorship

namespace SocialChoice

/-!
# Gibbard-Satterthwaite Base Case

The base case of the induction proof: for a single voter, any resolute,
unanimous, strategy-proof voting rule is dictatorial.

This is trivially true because with one voter, unanimity forces the rule
to select that voter's top choice.
-/

open Finset

/-- Base case: For a single voter (Unit type), any resolute, unanimous voting rule
    selects the unique voter's top choice. -/
theorem gs_base_case_unit {A : Type} [Fintype A] [Nonempty A]
    (f : VotingRule) (_hf : Resolute f)
    (hf_unan : Unanimity f) :
    ∀ P : Profile Unit A, f P = {topChoice P ()} := by
  intro P
  -- The single voter unanimously ranks topChoice P () first
  have htop : ∀ v : Unit, TopRank P v (topChoice P ()) := by
    intro v
    cases v
    exact topChoice_topRank P ()
  exact hf_unan P (topChoice P ()) htop

/-- Base case with explicit cardinality condition. -/
theorem gs_base_case {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (hcard_V : Fintype.card V = 1)
    (f : VotingRule) (_hf : Resolute f)
    (hf_unan : Unanimity f) :
    ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d} := by
  -- There's exactly one voter, so pick it
  classical
  have hnonempty : Nonempty V := by
    refine Fintype.card_pos_iff.mp ?_
    simp [hcard_V]
  let _ : Nonempty V := hnonempty
  have hunique := Fintype.card_eq_one_iff.mp hcard_V
  obtain ⟨d, hd⟩ := hunique
  use d
  intro P
  -- All voters equal d, so TopRank P v (topChoice P d) for all v
  have htop : ∀ v : V, TopRank P v (topChoice P d) := by
    intro v
    have hveq := hd v
    rw [hveq]
    exact topChoice_topRank P d
  exact hf_unan P (topChoice P d) htop

end SocialChoice
