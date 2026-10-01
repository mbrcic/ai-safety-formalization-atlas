module

public import AISafetyAtlas.Compositional.Rectangularity
public import AISafetyAtlas.Compositional.LocalContractBoundary

/-!
# Exchange closure and the agreement boundary, applied

`ExchangeClosed.exchange_fst` and `agreement_ssubset_product_of_projections`
had no worked instance anywhere in the tree. The first is exercised at the
cheapest possible rectangle, `Set.univ`; the second is already a closed
statement about the fixed `Agreement` relation and is cited by name.
-/

namespace AISafetyAtlas.Examples.Compositional.Rectangularity

open AISafetyAtlas.Compositional
open AISafetyAtlas.Compositional.LocalContractBoundary

/-- The full square is trivially exchange closed: every pair is in it. -/
theorem univ_exchangeClosed : ExchangeClosed (Set.univ : Set (Bool × Bool)) :=
  fun _p _ _q _ => Set.mem_univ _

/-- **Exchange closure splices the first coordinate too**, at the trivial
witness. -/
theorem univ_exchange_fst :
    ∀ p ∈ (Set.univ : Set (Bool × Bool)), ∀ q ∈ (Set.univ : Set (Bool × Bool)),
      (q.1, p.2) ∈ (Set.univ : Set (Bool × Bool)) :=
  ExchangeClosed.exchange_fst univ_exchangeClosed

/-- **The agreement relation's projections outgrow it** — a closed statement
about the fixed diagonal-on-`Bool` relation, cited by name. -/
theorem agreement_ssubset_product :
    Agreement ⊂ (Prod.fst '' Agreement) ×ˢ (Prod.snd '' Agreement) :=
  agreement_ssubset_product_of_projections

end AISafetyAtlas.Examples.Compositional.Rectangularity
