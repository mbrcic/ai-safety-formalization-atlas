import SocialChoice.Profile

namespace SocialChoice

/-- If every voter ranks `c` uniquely first, then `c` is the unique winner. -/
def Unanimity (f : VotingRule) : Prop :=
  ∀ {V A : Type} [Fintype V] [Fintype A] [Nonempty V] (P : Profile V A) (c : A),
    (∀ v : V, TopRank P v c) → f P = {c}

end SocialChoice
