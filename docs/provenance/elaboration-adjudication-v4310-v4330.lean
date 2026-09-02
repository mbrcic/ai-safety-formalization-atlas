import Mathlib
import Foundation.FirstOrder.Incompleteness.Second

/-!
# Adjudication of the elaboration drift, v4.31.0 -> v4.33.0

`scripts/check_elaboration_drift.py` compares declarations by their *elaborated
type*. Run across the migration over all 5994 declarations our modules compile
-- ours and the vendored code alike -- it reported 171 whose printed type is
identical at both versions and whose elaborated type is not, the case no text
diff, no axiom audit and no build can see. No declaration we wrote appeared or
vanished.

All 171 are substitutions of upstream constants, and none of them changed the
shape of a statement: of the 171, zero had the same constants in a different
arrangement, so no binder kind, argument order or universe moved. The eleven
substitution classes are recorded in `docs/status/migration-baseline.json`; the
per-class counts below sum to more than 171 because a statement can be touched
by two of them.

This file is the verdict on them. Every `example` pins one class to a fact
phrased in terms that exist at **both** toolchains, so the same file is a proof
obligation on each tree, and it was checked on each:

    lake env lean docs/provenance/elaboration-adjudication-v4310-v4330.lean

at v4.31.0 (worktree at the baseline commit) and at v4.33.0. Both exit 0.

The anchors determine meaning rather than compare instance terms -- a set is its
membership predicate, a power is fixed by its recursion -- because most of the
pre-migration constants no longer exist at v4.33.0, so there is nothing to
compare them against. Two declarations, `AISafetyAtlas.Logic.loeb` and
`AISafetyAtlas.Logic.tarski_undefinability`, are settled differently: both are
thin wrappers whose proof is the upstream Foundation theorem applied with no
adaptation, so the kernel already checks our statement against Foundation's at
whichever version it is elaborated on.

CI elaborates this file at the pinned toolchain, so the claim above is checked
rather than asserted. The v4.31.0 side cannot be re-checked from this tree --
it was run once, by hand, on a worktree at the baseline commit. What CI does
check is that the anchors still hold at whatever toolchain is pinned now: each
class below is a standing claim that an upstream substitution preserved
meaning, and such a claim goes bad when a later toolchain breaks one of these
definitional equalities. Expect that to fail one day; re-adjudicate the class
rather than deleting its anchor.

`-- class:` lines bind each anchor to its key in
`docs/status/elaboration-classes.json`. Tests assert the two sets agree, so a
class cannot be recorded with no anchor, nor an anchor left behind for a class
that has been dropped.
-/

section SetOfIsOfPred
-- class: setOf
-- `setOf` ==> `Set.ofPred`   (52 declarations)
example {α : Type} (p : α → Prop) (a : α) : (a ∈ {x | p x}) = p a := rfl
end SetOfIsOfPred

section MonoidPow
-- class: Monoid.toPow
-- `Monoid.toPow` ==> `Monoid.toNPow` `NPow.toPow`   (75 declarations)
-- `Monoid.npow` does not exist at 4.33 and `NPow.npow` does not exist at 4.31, so
-- the anchor is the recursion, which determines the operation uniquely.
example {M : Type} [Monoid M] (f : M → ℕ → M)
    (h0 : ∀ a, f a 0 = 1) (hs : ∀ a n, f a (n + 1) = f a n * a) (a : M) (n : ℕ) :
    a ^ n = f a n := by
  induction n with
  | zero => rw [pow_zero, h0]
  | succ k ih => rw [pow_succ, ih, hs]
end MonoidPow

section RealNonUnitalCommRing
-- class: Real.normedCommRing
-- the normed route ==> `CommRing.toNonUnitalCommRing Real.commRing`   (18 declarations)
example :
    (@NonUnitalNormedCommRing.toNonUnitalCommRing ℝ
      (@NormedCommRing.toNonUnitalNormedCommRing ℝ Real.normedCommRing))
      = @CommRing.toNonUnitalCommRing ℝ Real.commRing := rfl
end RealNonUnitalCommRing

section SubsetIsLe
-- class: Set.instHasSubset
-- class: Finset.instHasSubset
-- class: Set.instHasSSubset
-- `HasSubset.Subset` ==> `LE.le` (17 on `Set`, 11 on `Finset`),
-- `HasSSubset.SSubset` ==> `LT.lt` (1)
example {α : Type} (s t : Set α) : (s ⊆ t) = (s ≤ t) := rfl
example {α : Type} (s t : Set α) : (s ⊂ t) = (s < t) := rfl
example {α : Type} [DecidableEq α] (s t : Finset α) : (s ⊆ t) = (s ≤ t) := rfl
end SubsetIsLe

section SubsetTransIsLeTrans
-- class: HasSubset.Subset.trans
-- `HasSubset.Subset.trans` `Set.instIsTransSubset` ==> `LE.le.trans` and the
-- `Set` complete-lattice route   (1 declaration: `Comp.allow_allow`)
-- `Comp.allow` takes the inclusion proof as an argument, so the substituted
-- constant occurs inside a statement. It is a proof of a `Prop`, and any two
-- proofs of one `Prop` are definitionally equal, so which one is written there
-- cannot change what the statement says; that the two `Prop`s are the same one
-- is the anchor above.
example {α : Type} {s u : Set α} (h₁ h₂ : s ⊆ u) : h₁ = h₂ := rfl
end SubsetTransIsLeTrans

section FinsetOrder
-- class: Finset.partialOrder
-- `Finset.partialOrder` ==> `Finset.instPartialOrder`   (6 declarations)
example {α : Type} (s t : Finset α) : (s ≤ t) = (∀ ⦃a : α⦄, a ∈ s → a ∈ t) := rfl
end FinsetOrder

section AddMonoidAlgebraGroup
-- class: AddMonoidAlgebra.addAddCommGroup
-- `AddMonoidAlgebra.addAddCommGroup` ==> `AddMonoidAlgebra.addCommGroup`   (1)
-- Reached through `MvPolynomial`, so the anchor is on coefficients, which
-- determine a polynomial; `AddMonoidAlgebra` itself is not the same shape of
-- definition at the two versions and cannot be named uniformly.
example {σ : Type} (p q : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    (p - q).coeff m = p.coeff m - q.coeff m := by simp [MvPolynomial.coeff_sub]
example {σ : Type} (p : MvPolynomial σ ℝ) (m : σ →₀ ℕ) :
    (-p).coeff m = -p.coeff m := by simp [MvPolynomial.coeff_neg]
end AddMonoidAlgebraGroup

section FoundationArrow
-- class: LO.Arrow.arrow
-- class: LO.FirstOrder.instLCWQOfQuantifierOfLogicalConnective
-- `LO.Arrow.arrow` ==> `LO.Arrow.instHArrow` `LO.HArrow.hArrow`   (1: `Logic.loeb`)
-- The Foundation LCWQ instance gaining `LogicalNeutral` (1: `Logic.tarski_undefinability`)
-- is settled by the wrapper argument in the header, not by an anchor here.
example {α : Type} [LO.Arrow α] (a b : α) : (a 🡒 b) = LO.Arrow.arrow a b := rfl
end FoundationArrow
