import SocialChoice.Profile
import Mathlib.Data.Finset.Card

namespace SocialChoice

/-!
# Resolute Voting Rules

A voting rule is **resolute** if it always returns exactly one winner.
This file provides the definition and helper lemmas for working with resolute rules.
-/

open Finset

/-- A voting rule is resolute if it always returns exactly one winner. -/
def Resolute (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty A] (P : Profile V A), (f P).card = 1

/-! ## Extracting the Unique Winner -/

/-- Extract the unique winner from a resolute voting rule's output. -/
noncomputable def theWinner {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (f : VotingRule) (P : Profile V A) (hf : Resolute f) : A := by
  have h : ∃! x, x ∈ f P := by
    have hcard := hf P
    rw [Finset.card_eq_one] at hcard
    obtain ⟨x, hx⟩ := hcard
    exact ⟨x, by simp [hx], fun y hy => by simp [hx] at hy; exact hy⟩
  exact Classical.choose h

/-- The winner is a member of f P. -/
lemma theWinner_mem {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (f : VotingRule) (P : Profile V A) (hf : Resolute f) :
    theWinner f P hf ∈ f P := by
  unfold theWinner
  have h : ∃! x, x ∈ f P := by
    have hcard := hf P
    rw [Finset.card_eq_one] at hcard
    obtain ⟨x, hx⟩ := hcard
    exact ⟨x, by simp [hx], fun y hy => by simp [hx] at hy; exact hy⟩
  exact (Classical.choose_spec h).1

/-- If f P = {c}, then the winner is c. -/
lemma theWinner_eq_of_eq_singleton {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (f : VotingRule) (P : Profile V A) (hf : Resolute f) (c : A)
    (hc : f P = {c}) : theWinner f P hf = c := by
  have hmem : theWinner f P hf ∈ f P := theWinner_mem f P hf
  simp only [hc, Finset.mem_singleton] at hmem
  exact hmem

/-- f P = {c} iff theWinner is c. -/
lemma eq_singleton_iff_theWinner_eq {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (f : VotingRule) (P : Profile V A) (hf : Resolute f) (c : A) :
    f P = {c} ↔ theWinner f P hf = c := by
  constructor
  · exact theWinner_eq_of_eq_singleton f P hf c
  · intro hw
    have hcard := hf P
    rw [Finset.card_eq_one] at hcard
    obtain ⟨x, hx⟩ := hcard
    have hmem : theWinner f P hf ∈ f P := theWinner_mem f P hf
    simp only [hx, Finset.mem_singleton] at hmem
    -- hmem : theWinner f P hf = x
    -- hw : theWinner f P hf = c
    -- hx : f P = {x}
    -- Goal: f P = {c}
    rw [hmem] at hw
    simp only [hx, hw]

end SocialChoice
