module

public import Mathlib.Data.Set.Prod
public import Mathlib.Data.Finset.Piecewise
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Set.Finite.Basic

/-!
# Rectangularity and independent local contracts

The binary result is the standard communication-complexity characterization:
a relation is a Cartesian rectangle exactly when it is closed under exchanging
coordinates.  The indexed results characterize the corresponding full-product
property.

The binary theorem is the folklore result used throughout communication
complexity (for example, Kushilevitz and Nisan, *Communication Complexity*,
1997).  It is also the empty-determinant special case of Fagin's lossless-join
characterization of multivalued dependencies (ACM TODS, 1977).

## Two indexed characterizations, and why both are here

`coordinate_product_iff_recombination_closed` is close to definitional: one
inclusion of the product equality always holds, so the statement reduces to
unfolding `Set.pi` against the recombination hypothesis.  It is kept as a
helper, not as a headline result.

`coordinate_product_iff_spliceClosed` is the substantive statement.  Splice
closure is a *local* condition: update one accepted point at a single
coordinate using another accepted point's value there.  Over a finite index and
a nonempty predicate it is equivalent to being the full product, by splicing
coordinates one at a time along a `Finset.piecewise` induction.

Finiteness is necessary, not an artifact of the proof.
`spliceClosed_finitelySupported` and `not_isCoordinateProduct_finitelySupported`
exhibit the counterexample: over `ℕ`, the Boolean functions with finite support
are splice closed and have full unary projections, yet the constantly-true
function is missing, so they are not the full product.

No claim is made here about hyperproperties.  These predicates describe one
state or trace at a time; relational properties of several executions require
the lifting in `Hyperproperties`.
-/

namespace AISafetyAtlas.Compositional

/-- A binary relation is a Cartesian product of its two projections. -/
@[expose] public def IsRectangle {X Y : Type*} (R : Set (X × Y)) : Prop :=
  R = (Prod.fst '' R) ×ˢ (Prod.snd '' R)

/-- Coordinate exchange: two accepted pairs may exchange their second
coordinates.  The other mixed pair follows by exchanging the arguments. -/
@[expose] public def ExchangeClosed {X Y : Type*} (R : Set (X × Y)) : Prop :=
  ∀ p ∈ R, ∀ q ∈ R, (p.1, q.2) ∈ R

/--
**Rectangle/exchange equivalence.**

A binary relation is exactly the product of its projections iff it is closed
under mix-and-match coordinate exchange.
-/
public theorem rectangle_iff_exchange_closed {X Y : Type*} (R : Set (X × Y)) :
    IsRectangle R ↔ ExchangeClosed R := by
  constructor
  · intro hR p hp q hq
    rw [IsRectangle] at hR
    rw [hR] at hp hq ⊢
    exact ⟨hp.1, hq.2⟩
  · intro h
    apply Set.Subset.antisymm
    · intro p hp
      exact ⟨⟨p, hp, rfl⟩, ⟨p, hp, rfl⟩⟩
    · rintro ⟨x, y⟩ ⟨⟨p, hp, hpx⟩, ⟨q, hq, hqy⟩⟩
      simpa [hpx, hqy] using h p hp q hq

/-- The values occurring in coordinate `i` among the accepted global states. -/
@[expose] public def coordinateProjection {ι : Type*} {X : ι → Type*}
    (P : Set (∀ i, X i)) (i : ι) : Set (X i) :=
  Function.eval i '' P

/-- An indexed predicate is the full product of its unary projections. -/
@[expose] public def IsCoordinateProduct {ι : Type*} {X : ι → Type*}
    (P : Set (∀ i, X i)) : Prop :=
  P = Set.pi Set.univ (coordinateProjection P)

/-- Every point assembled from coordinate values that occur locally is
accepted globally.  This is arbitrary (possibly infinite) recombination, not
merely closure under finitely many single-coordinate updates. -/
@[expose] public def RecombinationClosed {ι : Type*} {X : ι → Type*}
    (P : Set (∀ i, X i)) : Prop :=
  ∀ x, (∀ i, x i ∈ coordinateProjection P i) → x ∈ P

/--
**Helper: indexed product versus arbitrary recombination.**

`P` is a conjunction of its unary coordinate contracts exactly when arbitrary
choices satisfying every projected contract recombine to an element of `P`.

This is close to definitional.  The inclusion `P ⊆ Set.pi univ (coordinateProjection P)`
holds for every `P`, since each point's coordinates lie in its own projections,
so the equality reduces to the reverse inclusion, which is `RecombinationClosed`
after unfolding `Set.pi`.  It is retained as a helper for
`coordinate_product_iff_spliceClosed`, and is not the module's headline result.
-/
public theorem coordinate_product_iff_recombination_closed
    {ι : Type*} {X : ι → Type*} (P : Set (∀ i, X i)) :
    IsCoordinateProduct P ↔ RecombinationClosed P := by
  constructor
  · intro hP x hx
    rw [IsCoordinateProduct] at hP
    rw [hP]
    exact fun i _ => hx i
  · intro hP
    apply Set.Subset.antisymm
    · intro x hx i _
      exact ⟨x, hx, rfl⟩
    · intro x hx
      exact hP x (fun i => hx i (Set.mem_univ i))

/-!
## Local splicing

Splice closure updates one accepted point at a *single* coordinate, using the
value another accepted point takes there.  Unlike `RecombinationClosed` it never
rebuilds a point from scratch, so it is a genuinely local condition.
-/

/-- Closure under updating one accepted point at a single coordinate with the
value another accepted point takes at that coordinate. -/
@[expose] public def SpliceClosed {ι : Type*} [DecidableEq ι] {X : ι → Type*}
    (P : Set (∀ i, X i)) : Prop :=
  ∀ x ∈ P, ∀ y ∈ P, ∀ i, Function.update x i (y i) ∈ P

/-- Every full product is splice closed: an update keeps each coordinate inside
its own projection. -/
public theorem spliceClosed_of_isCoordinateProduct
    {ι : Type*} [DecidableEq ι] {X : ι → Type*} {P : Set (∀ i, X i)}
    (hP : IsCoordinateProduct P) : SpliceClosed P := by
  intro x hx y hy i
  rw [hP] at hx hy ⊢
  intro j _
  by_cases hij : j = i
  · subst hij
    simpa using hy j (Set.mem_univ j)
  · simpa [Function.update_of_ne hij] using hx j (Set.mem_univ j)

/--
Splice one coordinate at a time along a `Finset`.

If every coordinate of `z` in `s` is realized by some accepted point, then the
point agreeing with `z` on `s` and with the base point `x` off `s` is accepted.
-/
public theorem spliceClosed_piecewise_mem
    {ι : Type*} [DecidableEq ι] {X : ι → Type*} {P : Set (∀ i, X i)}
    (hsplice : SpliceClosed P) {x : ∀ i, X i} (hx : x ∈ P)
    (z : ∀ i, X i) (s : Finset ι)
    (hz : ∀ i ∈ s, ∃ y ∈ P, y i = z i) :
    s.piecewise z x ∈ P := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hx
  | insert a t ha ih =>
      have hz' : ∀ i ∈ t, ∃ y ∈ P, y i = z i := fun i hi =>
        hz i (Finset.mem_insert_of_mem hi)
      have hbase : t.piecewise z x ∈ P := ih hz'
      obtain ⟨y, hy, hya⟩ := hz a (Finset.mem_insert_self a t)
      have hupd := hsplice _ hbase y hy a
      rw [hya] at hupd
      rwa [Finset.piecewise_insert]

/--
**Indexed rectangularity via local splicing.**

Over a finite index type, a nonempty predicate is the full product of its unary
coordinate contracts exactly when it is closed under single-coordinate splicing.

Finiteness is essential; see `spliceClosed_finitelySupported` and
`not_isCoordinateProduct_finitelySupported` for the infinite-index
counterexample.
-/
public theorem coordinate_product_iff_spliceClosed
    {ι : Type*} [Fintype ι] [DecidableEq ι] {X : ι → Type*}
    (P : Set (∀ i, X i)) (hne : P.Nonempty) :
    IsCoordinateProduct P ↔ SpliceClosed P := by
  classical
  refine ⟨spliceClosed_of_isCoordinateProduct, fun hsplice => ?_⟩
  rw [coordinate_product_iff_recombination_closed]
  intro z hz
  obtain ⟨x, hx⟩ := hne
  have hall : ∀ i ∈ (Finset.univ : Finset ι), ∃ y ∈ P, y i = z i := by
    intro i _
    obtain ⟨y, hy, hyi⟩ := hz i
    exact ⟨y, hy, hyi⟩
  have := spliceClosed_piecewise_mem hsplice hx z Finset.univ hall
  rwa [Finset.piecewise_univ] at this

/-!
### The binary theorem is the two-coordinate case

`ExchangeClosed` replaces the second coordinate of an accepted pair by the
second coordinate of another accepted pair, which is exactly a splice at that
coordinate.  Applying it with the arguments swapped splices the first
coordinate, so both single-coordinate updates are available.
-/

/-- Exchange closure also splices the *first* coordinate. -/
public theorem ExchangeClosed.exchange_fst {X Y : Type*} {R : Set (X × Y)}
    (h : ExchangeClosed R) : ∀ p ∈ R, ∀ q ∈ R, (q.1, p.2) ∈ R :=
  fun p hp q hq => h q hq p hp

/-!
## Necessity of finiteness

Over an infinite index the finite-support Boolean functions are splice closed
and have full unary projections, but omit the constantly-true function.
-/

/-- Boolean sequences with finitely many `true` values. -/
@[expose] public def FinitelySupported : Set (ℕ → Bool) :=
  {x | {n | x n = true}.Finite}

/-- The finite-support predicate is closed under single-coordinate splicing. -/
public theorem spliceClosed_finitelySupported : SpliceClosed FinitelySupported := by
  intro x hx y _ i
  have hsub :
      {n | Function.update x i (y i) n = true} ⊆ {n | x n = true} ∪ {i} := by
    intro n hn
    by_cases hni : n = i
    · exact Or.inr (by simpa using hni)
    · left
      simpa [Function.update_of_ne hni] using hn
  exact Set.Finite.subset (hx.union (Set.finite_singleton i)) hsub

/-- Every coordinate contract of the finite-support predicate is the full
Boolean set, since flipping a single coordinate of the constantly-false
sequence stays finitely supported. -/
public theorem coordinateProjection_finitelySupported (i : ℕ) :
    coordinateProjection FinitelySupported i = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro b
  refine ⟨Function.update (fun _ => false) i b, ?_, by simp⟩
  refine Set.Finite.subset (Set.finite_singleton i) ?_
  intro n hn
  by_cases hni : n = i
  · simpa using hni
  · simp [Function.update_of_ne hni] at hn

/-- The finite-support predicate is *not* the full product of its coordinate
contracts: the constantly-true sequence satisfies every unary contract but is
not finitely supported. -/
public theorem not_isCoordinateProduct_finitelySupported :
    ¬ IsCoordinateProduct FinitelySupported := by
  intro hP
  have hmem : (fun _ => true) ∈ Set.pi Set.univ
      (coordinateProjection FinitelySupported) := by
    intro i _
    rw [coordinateProjection_finitelySupported i]
    exact Set.mem_univ _
  rw [← hP] at hmem
  have : {n : ℕ | true = true} = Set.univ := by simp
  exact Set.infinite_univ (α := ℕ) (this ▸ hmem)

end AISafetyAtlas.Compositional
