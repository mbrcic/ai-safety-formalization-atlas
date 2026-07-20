import SocialChoice.Rank
import SocialChoice.Axioms.Resolute

namespace SocialChoice

/-!
# Dictatorship Axiom

A voting rule is **dictatorial** if some voter's top choice always uniquely wins.
-/

/-- A voting rule is dictatorial if some voter's top choice always uniquely wins.
    This is the fully quantified version over all voter/candidate types. -/
def Dictatorial (f : VotingRule) (_hf : Resolute f) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty A],
    ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d}

/-- A voting rule is dictatorial for a fixed voter type if some voter's
    top choice always uniquely wins, for all candidate sets. -/
def DictatorialV {V : Type} [Fintype V] (f : VotingRule) : Prop :=
  ∃ d : V, ∀ {A : Type} [Fintype A] [Nonempty A] (P : Profile V A),
    f P = {topChoice P d}

/-- A voting rule is dictatorial for fixed voter and candidate types. -/
def DictatorialVA {V A : Type} [Fintype V] [Fintype A] [Nonempty A]
    (f : Profile V A → Finset A) : Prop :=
  ∃ d : V, ∀ P : Profile V A, f P = {topChoice P d}

end SocialChoice
