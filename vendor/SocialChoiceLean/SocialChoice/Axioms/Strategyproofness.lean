import SocialChoice.Profile
import SocialChoice.Axioms.Core

namespace SocialChoice

/-- Replace one voter's ballot with a new linear order. -/
noncomputable def updateProfile {V A : Type} [Fintype V] [Fintype A]
    (P : Profile V A) (v : V) (ballot : LinearOrder A) : Profile V A := by
  classical
  exact { pref := fun w => if w = v then ballot else P.pref w }

/-- Strategyproofness for resolute rules: no voter can gain by misreporting. -/
def ResoluteStrategyproofness (f : VotingRule) (_hf : Resolute f) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A]
      (P : Profile V A) (v : V) (ballot : LinearOrder A) (x y : A),
    f P = {x} →
    f (updateProfile P v ballot) = {y} →
    ¬ Prefers P v y x

end SocialChoice
