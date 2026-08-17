module

public import Mathlib.Logic.Equiv.Fintype
public import Mathlib.Data.Sym.Card
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Rat.Cast.Order
public import Mathlib.Tactic.NormNum.Pow

/-!
# Invariance under relabelling the index type

The symmetric group `Equiv.Perm X` acts on everything built over `X`. This
module collects what that action forces, for two kinds of object, with no
commitment to what `X` is for.

## Functions `X → Y`

`permOrbit f` is the set of relabellings of `f`, and `ClosedUnderPermutation F`
says `F` is a union of orbits — the condition variously called *anonymity*,
*exchangeability*, or *order-blindness* depending on the field.

`spectrum f : Sym Y |X|` is the multiset of values `f` takes, and it is the
**complete invariant** of the orbit: `spectrum_eq_iff_mem_permOrbit`. So a
property of functions that cannot see which point is which factors through
`spectrum`, and `closedUnderPermutationEquivSet` turns that into a bijection —
**relabelling-invariant families of functions are exactly families of
multisets**, with nothing lost either way. The counts follow from Mathlib's
tally of `Sym`.

## Relations on `X`

`forall_rel_of_permInvariant`: a relation invariant under every permutation is
constant off the diagonal, and `rel_diag_iff_of_permInvariant` says it is
constant on the diagonal too — independently. Neither symmetry nor
irreflexivity is used, so `exists_perm_rel_not_iff` reaches relations no graph
can be instantiated at. The `SimpleGraph` corollaries are the form a reader
looking for graph automorphisms would search for: such a graph is complete or
empty.

## Consumers

`AISafetyAtlas.Learning.Sharp` uses all of it — closure under permutation is
exactly the condition under which No Free Lunch holds, the counts say almost no
prior meets it, and the relation results say no structured search space does.
That is one application. Nothing here mentions search, learning, or objectives.

Two more places do this kind of reasoning and do not yet route through here, so
the relationship is worth stating rather than assuming.
`AISafetyAtlas.Compositional.Hyperproperties.toBatch_perm` proves that
reordering a tuple does not change the traces it mentions; that is the image of
`spectrum` under `Multiset.toFinset`, so it follows from `spectrum` being
orbit-invariant, but **only in one direction** — `toBatch` is a `Finset` and
forgets multiplicity, so it cannot be strengthened to the `iff` that
`spectrum_eq_iff_mem_permOrbit` gives. And `AISafetyAtlas.Upstream` relabels
voters and alternatives by hand, which is anonymity and neutrality; that module
is vendored and is deliberately left alone.
-/

namespace AISafetyAtlas.Combinatorics

open Function

variable {X : Type*} {Y : Type*}

/-! ## Orbits of functions under relabelling of the domain -/

/--
**Schumacher–Vose–Whitley's set form.** A set of objectives closed under
permutation of the domain has a permutation-invariant indicator weight, so NFL
holds over it. `ClosedUnderPermutation` is their condition verbatim.
-/
@[expose] public def ClosedUnderPermutation (F : Set (X → Y)) : Prop :=
  ∀ (π : Equiv.Perm X) (f : X → Y), f ∈ F → f ∘ π ∈ F

/--
**The permutation orbit of an objective**: everything obtainable from `f` by
relabelling the search domain. That this coincides with Igel–Toussaint's *basis
class* is their Lemma 1(2), proved as `basisClass_histogram_eq_permOrbit` — not
assumed here.
-/
@[expose] public def permOrbit (f : X → Y) : Set (X → Y) :=
  {g | ∃ π : Equiv.Perm X, g = f ∘ (π : X → X)}

/-- An objective lies in its own orbit, via the identity relabelling. -/
public theorem mem_permOrbit_self (f : X → Y) : f ∈ permOrbit f :=
  ⟨1, rfl⟩

/--
**Closed under permutation is closure under taking orbits.** The membership
form; `eq_iUnion_permOrbit` below is the union form, which with
`basisClass_histogram_eq_permOrbit` gives Igel–Toussaint's Lemma 1(1) —
disjointness and uniqueness of the decomposition are theirs and are not proved
here.
-/
public theorem closedUnderPermutation_iff_permOrbit_subset {F : Set (X → Y)} :
    ClosedUnderPermutation F ↔ ∀ f ∈ F, permOrbit f ⊆ F := by
  constructor
  · rintro hF f hf g ⟨π, rfl⟩
    exact hF π f hf
  · intro h π f hf
    exact h f hf ⟨π, rfl⟩

/-- Every orbit is itself permutation-closed, so each is a prior for which NFL
holds — the smallest such priors there are. -/
public theorem closedUnderPermutation_permOrbit (f : X → Y) :
    ClosedUnderPermutation (permOrbit f) := by
  rintro π g ⟨ρ, rfl⟩
  exact ⟨ρ * π, rfl⟩

/--
**Igel–Toussaint's histogram.** How many points of the domain each cost value
receives. Their `h_f(y) = |f⁻¹(y)|`.
-/
@[expose] public noncomputable def histogram [Fintype X] [DecidableEq Y]
    (f : X → Y) : Y → ℕ :=
  fun y => (Finset.univ.filter fun x : X => f x = y).card

/-- Their **basis class** `B_h`: all objectives with a given histogram. -/
@[expose] public noncomputable def basisClass [Fintype X] [DecidableEq Y]
    (h : Y → ℕ) : Set (X → Y) :=
  {f | histogram f = h}

/--
**Igel–Toussaint's Lemma 1(2)**: the basis class of `f`'s histogram *is* `f`'s
permutation orbit.

This is the half of their Lemma 1 with content — histograms and orbits are
defined independently, and the lemma says they cut the objectives the same way.
The atlas states `PermInvariant` in terms of orbits and the source states
Theorem 5's hypothesis in terms of histograms, so without this the two are not
known to be the same condition.

Both inclusions are counting. A relabelling permutes the fibres of `f` without
resizing them, so an orbit member has `f`'s histogram; conversely two objectives
with the same histogram have equinumerous fibres, and any family of bijections
between corresponding fibres assembles into a permutation carrying one to the
other.
-/
public theorem basisClass_histogram_eq_permOrbit [Fintype X] [DecidableEq X] [DecidableEq Y]
    (f : X → Y) : basisClass (histogram f) = permOrbit f := by
  classical
  apply Set.eq_of_subset_of_subset
  · rintro g (hg : histogram g = histogram f)
    -- equal histograms give a bijection of each fibre, hence a permutation
    have hcard : ∀ y : Y, (Finset.univ.filter fun x : X => g x = y).card
        = (Finset.univ.filter fun x : X => f x = y).card := fun y => congrFun hg y
    have hbij : ∀ y : Y, Nonempty ({x : X // g x = y} ≃ {x : X // f x = y}) := by
      intro y
      refine ⟨Fintype.equivOfCardEq ?_⟩
      simpa [Fintype.card_subtype] using hcard y
    have e : ∀ y : Y, ({x : X // g x = y} ≃ {x : X // f x = y}) :=
      fun y => Classical.choice (hbij y)
    -- `Equiv.ofFiberEquiv` assembles the fibrewise bijections into a permutation
    refine ⟨Equiv.ofFiberEquiv e, funext fun x => ?_⟩
    exact (Equiv.ofFiberEquiv_map e x).symm

  · rintro g ⟨π, rfl⟩
    show histogram (f ∘ (π : X → X)) = histogram f
    funext y
    refine Finset.card_bij (fun x _ => π x) (fun x hx => ?_) (fun a _ b _ h => π.injective h)
      (fun b hb => ⟨π.symm b, ?_, by simp⟩)
    · simpa [histogram] using hx
    · simpa [histogram] using hb

/--
**The multiset of values a function takes on a finite domain** — its image with
multiplicity, as an element of `Sym Y |X|`.

This is the complete invariant of a function under relabelling its domain:
`spectrum_eq_iff_mem_permOrbit` says two functions have the same spectrum
exactly when one is the other precomposed with a permutation. So anything
definable on `X → Y` that cannot see which point is which — an anonymous or
exchangeable property — factors through `spectrum`, and questions about such
properties become questions about subsets of `Sym Y |X|`, where Mathlib's count
of symmetric powers applies.

Here it is Igel and Toussaint's histogram of cost values, but nothing in the
definition is about search.
-/
@[expose] public noncomputable def spectrum [Fintype X] (f : X → Y) :
    Sym Y (Fintype.card X) :=
  ⟨Multiset.map f Finset.univ.val, by simp [Finset.card_univ]⟩

/-- `spectrum` and `histogram` carry the same information: the multiset's
multiplicity at `y` is the number of domain points `f` sends to `y`. -/
public theorem spectrum_eq_iff_histogram_eq [Fintype X] [DecidableEq Y]
    (f g : X → Y) : spectrum f = spectrum g ↔ histogram f = histogram g := by
  simp only [← Sym.coe_inj, spectrum, Sym.coe_mk, Multiset.ext, funext_iff,
    Multiset.count_map, histogram, Finset.card, Finset.filter, eq_comm]

/-- **Lemma 1, in the form the count needs.** Two objectives have the same
spectrum exactly when one is a relabelling of the other. -/
public theorem spectrum_eq_iff_mem_permOrbit [Fintype X] [DecidableEq X]
    [DecidableEq Y] (f g : X → Y) :
    spectrum f = spectrum g ↔ g ∈ permOrbit f := by
  rw [spectrum_eq_iff_histogram_eq, ← basisClass_histogram_eq_permOrbit f]
  simp [basisClass, eq_comm]

/-- Every multiset of `|X|` cost values is the spectrum of some objective, so
the orbits are exactly the elements of `Sym Y |X|` and none is missed. -/
public theorem surjective_spectrum [Fintype X] :
    Function.Surjective (spectrum (X := X) (Y := Y)) := by
  classical
  intro s
  have hlen : s.val.toList.length = Fintype.card X := by
    rw [Multiset.length_toList, s.2]
  let e : X ≃ Fin s.val.toList.length :=
    (Fintype.equivFin X).trans (finCongr hlen.symm)
  refine ⟨fun x => s.val.toList.get (e x), Subtype.ext ?_⟩
  show Multiset.map (fun x => s.val.toList.get (e x)) Finset.univ.val = s.val
  rw [show (fun x => s.val.toList.get (e x)) = s.val.toList.get ∘ e from rfl,
    ← Multiset.map_map, Multiset.map_univ_val_equiv e, Fin.univ_val_map,
    List.ofFn_get]
  exact Multiset.coe_toList s.val

/-- A permutation-closed set is recovered from its set of spectra: membership
depends on nothing but the multiset of cost values. -/
public theorem preimage_image_spectrum [Fintype X] [DecidableEq X] [DecidableEq Y]
    {F : Set (X → Y)} (hF : ClosedUnderPermutation F) :
    spectrum ⁻¹' (spectrum '' F) = F := by
  apply Set.Subset.antisymm
  · rintro g ⟨f, hf, hfg⟩
    obtain ⟨π, rfl⟩ := (spectrum_eq_iff_mem_permOrbit f g).1 hfg
    exact hF π f hf
  · exact fun f hf => ⟨f, hf, rfl⟩

/--
**Relabelling-invariant families of functions are exactly families of
multisets.** The subsets of `X → Y` closed under precomposition by permutations
of a finite `X` biject with the subsets of `Sym Y |X|`, by taking each family to
its set of spectra.

The orbit space itself is `Sym Y |X|` — `surjective_spectrum` and
`spectrum_eq_iff_mem_permOrbit` are what identify it. This equiv is the
statement one level up, about invariant *subsets*, and it is the general form of
what "depends on the values but
not on which point carries them" means: an anonymous, exchangeable, or
order-blind family of functions *is* a family of multisets, with no information
lost either way.

Here it turns Igel–Toussaint's count into Mathlib's tally of `Sym`, but the
bijection is not about search or about counting.
-/
@[expose] public noncomputable def closedUnderPermutationEquivSet [Fintype X]
    [DecidableEq X] [DecidableEq Y] :
    {F : Set (X → Y) // ClosedUnderPermutation F} ≃ Set (Sym Y (Fintype.card X)) where
  toFun F := spectrum '' F.1
  invFun S := ⟨spectrum ⁻¹' S, by
    rintro π f hf
    have : spectrum (f ∘ (π : X → X)) = spectrum f :=
      ((spectrum_eq_iff_mem_permOrbit f (f ∘ (π : X → X))).2 ⟨π, rfl⟩).symm
    simpa [Set.mem_preimage, this] using hf⟩
  left_inv := by
    rintro ⟨F, hF⟩
    exact Subtype.ext (preimage_image_spectrum hF)
  right_inv S := Set.image_preimage_eq S surjective_spectrum

/--
**Igel–Toussaint's Theorem 3, first equation.** The permutation-closed subsets of
`Y ^ X` number `2 ^ C(|X| + |Y| − 1, |X|)`; print states the count of the
**non-empty** ones, which is this less the empty set.

Their statement is attributed to their own earlier paper, where the proof is
given; this is a transcription of the printed count, not a strengthening of it.
-/
public theorem card_closedUnderPermutation [Fintype X] [Fintype Y] [DecidableEq X]
    [DecidableEq Y] :
    Nat.card {F : Set (X → Y) // ClosedUnderPermutation F}
      = 2 ^ ((Fintype.card Y + Fintype.card X - 1).choose (Fintype.card X)) := by
  classical
  rw [Nat.card_congr closedUnderPermutationEquivSet, Nat.card_eq_fintype_card,
    Fintype.card_set, Sym.card_sym_eq_choose]

/-- All but one subset of a finite type is non-empty. Stated with the `+ 1` on
the left so that no truncated subtraction appears. -/
public theorem card_nonempty_set_add_one (σ : Type*) [Fintype σ] :
    Nat.card {S : Set σ // S.Nonempty} + 1 = 2 ^ Fintype.card σ := by
  classical
  have hcompl : Fintype.card {S : Set σ // ¬ (S = ∅)}
      = Fintype.card (Set σ) - Fintype.card {S : Set σ // S = ∅} :=
    Fintype.card_subtype_compl _
  rw [Fintype.card_subtype_eq (∅ : Set σ), Fintype.card_set] at hcompl
  have hne : Nat.card {S : Set σ // S.Nonempty}
      = Fintype.card {S : Set σ // ¬ (S = ∅)} := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_congr
      (Equiv.subtypeEquivRight fun S => Set.nonempty_iff_ne_empty)
  have hpos : 1 ≤ 2 ^ Fintype.card σ := Nat.one_le_two_pow
  rw [hne, hcompl]
  omega

/--
The bijection above, restricted to the non-empty sets on both sides.
-/
@[expose] public noncomputable def closedUnderPermutationNonemptyEquivSet [Fintype X]
    [DecidableEq X] [DecidableEq Y] :
    {F : Set (X → Y) // ClosedUnderPermutation F ∧ F.Nonempty}
      ≃ {S : Set (Sym Y (Fintype.card X)) // S.Nonempty} where
  toFun F := ⟨spectrum '' F.1, F.2.2.image _⟩
  invFun S :=
    ⟨spectrum ⁻¹' S.1,
      (closedUnderPermutationEquivSet.symm S.1).2,
      by
        obtain ⟨t, ht⟩ := S.2
        obtain ⟨f, hf⟩ := surjective_spectrum (X := X) (Y := Y) t
        exact ⟨f, by simpa [Set.mem_preimage, hf] using ht⟩⟩
  left_inv := by
    rintro ⟨F, hF, -⟩
    exact Subtype.ext (preimage_image_spectrum hF)
  right_inv S := Subtype.ext (Set.image_preimage_eq S.1 surjective_spectrum)

/--
The printed form: the **non-empty** permutation-closed subsets number
`2 ^ C(|X| + |Y| − 1, |X|) − 1`. Stated with the `+ 1` on the left so that no
truncated subtraction appears in a hypothesis-free claim.
-/
public theorem card_closedUnderPermutation_nonempty [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] :
    Nat.card {F : Set (X → Y) // ClosedUnderPermutation F ∧ F.Nonempty} + 1
      = 2 ^ ((Fintype.card Y + Fintype.card X - 1).choose (Fintype.card X)) := by
  classical
  rw [Nat.card_congr closedUnderPermutationNonemptyEquivSet,
    card_nonempty_set_add_one, Sym.card_sym_eq_choose]

/-- The denominator of Igel–Toussaint's fraction: `2 ^ (|Y| ^ |X|) − 1`
non-empty subsets of `Y ^ X` in all. -/
public theorem card_nonempty_set_objective [Fintype X] [Fintype Y] [DecidableEq X] :
    Nat.card {F : Set (X → Y) // F.Nonempty} + 1
      = 2 ^ (Fintype.card Y ^ Fintype.card X) := by
  classical
  rw [card_nonempty_set_add_one, Fintype.card_fun]

/--
**Igel–Toussaint's Theorem 3, second equation.** The fraction of non-empty
subsets that are permutation-closed.

The point of the printed statement is what this fraction does as the alphabets
grow: they observe it *"converges to zero double exponentially fast"*, so the
condition characterizing No Free Lunch is met by almost nothing. That asymptotic
claim is a separate statement and is **not** proved here.
-/
public theorem fraction_closedUnderPermutation [Fintype X] [Fintype Y]
    [DecidableEq X] [DecidableEq Y] :
    (Nat.card {F : Set (X → Y) // ClosedUnderPermutation F ∧ F.Nonempty} : ℚ)
        / (Nat.card {F : Set (X → Y) // F.Nonempty} : ℚ)
      = ((2 : ℚ) ^ ((Fintype.card Y + Fintype.card X - 1).choose (Fintype.card X)) - 1)
        / ((2 : ℚ) ^ (Fintype.card Y ^ Fintype.card X) - 1) := by
  have hnum := card_closedUnderPermutation_nonempty (X := X) (Y := Y)
  have hden := card_nonempty_set_objective (X := X) (Y := Y)
  have hnum' : (Nat.card {F : Set (X → Y) // ClosedUnderPermutation F ∧ F.Nonempty} : ℚ)
      = (2 : ℚ) ^ ((Fintype.card Y + Fintype.card X - 1).choose (Fintype.card X)) - 1 :=
    eq_sub_of_add_eq (by exact_mod_cast hnum)
  have hden' : (Nat.card {F : Set (X → Y) // F.Nonempty} : ℚ)
      = (2 : ℚ) ^ (Fintype.card Y ^ Fintype.card X) - 1 :=
    eq_sub_of_add_eq (by exact_mod_cast hden)
  rw [hnum', hden']

/-! ## Relations invariant under relabelling -/

/--
**The symmetric group is two-transitive.** Any ordered pair of distinct points
can be carried to any other by a single permutation, assembled from two
transpositions.

This is the whole geometric content of the results below, and it is worth having
separately: everything here that says "a relabelling exists" is this lemma with
a predicate attached. Mathlib has `Equiv.swap` and its lemmas but does not name
the two-transitive statement.
-/
public theorem exists_perm_apply_eq_of_ne {x y a b : X} (hne : x ≠ y) (hab : a ≠ b) :
    ∃ π : Equiv.Perm X, π x = a ∧ π y = b := by
  classical
  have h1 : (Equiv.swap x a) x = a := Equiv.swap_apply_left x a
  have he_ne : (Equiv.swap x a) y ≠ a := fun hc =>
    hne ((Equiv.swap x a).injective (hc.trans h1.symm)).symm
  refine ⟨(Equiv.swap x a).trans (Equiv.swap ((Equiv.swap x a) y) b), ?_, ?_⟩
  · show Equiv.swap ((Equiv.swap x a) y) b ((Equiv.swap x a) x) = a
    rw [h1]
    exact Equiv.swap_apply_of_ne_of_ne (Ne.symm he_ne) hab
  · exact Equiv.swap_apply_left _ _

/--
**A non-trivial relation can be moved onto any pair of distinct points.** If some
pair of distinct points is related, then for *every* pair of distinct points
there is a relabelling putting them in the relation.

This is the form an application needs when it wants to build a bad instance
rather than derive a contradiction: given any two points one cares about — say a
global maximum and a global minimum of some function — a relabelling makes them
neighbours.
-/
public theorem exists_perm_rel_of_ne {r : X → X → Prop}
    (hedge : ∃ a b : X, a ≠ b ∧ r a b) {x y : X} (hne : x ≠ y) :
    ∃ π : Equiv.Perm X, r (π x) (π y) := by
  obtain ⟨a, b, hab, hr⟩ := hedge
  obtain ⟨π, hpx, hpy⟩ := exists_perm_apply_eq_of_ne hne hab
  exact ⟨π, by rw [hpx, hpy]; exact hr⟩

/--
**A relation invariant under every permutation is constant off the diagonal.**
One instance of `r` at a pair of distinct points forces `r` at *every* pair of
distinct points.

The proof is two-transitivity: a permutation assembled from two transpositions
carries the witnessing pair to any other, and invariance transports `r` along
it.

Neither symmetry nor irreflexivity of `r` is used. With
`rel_diag_iff_of_permInvariant` this pins a permutation-invariant relation down
to its behaviour on two independent parts: it is all-or-nothing off the
diagonal, and all-or-nothing on it.
-/
public theorem forall_rel_of_permInvariant {r : X → X → Prop}
    (h : ∀ (π : Equiv.Perm X) (a b : X), r (π a) (π b) ↔ r a b)
    {x y : X} (hne : x ≠ y) (hxy : r x y) :
    ∀ a b : X, a ≠ b → r a b := by
  intro a b hab
  obtain ⟨π, hpx, hpy⟩ := exists_perm_apply_eq_of_ne hne hab
  have hmove := h π x y
  rw [hpx, hpy] at hmove
  exact hmove.2 hxy

/-- **And constant on the diagonal**: a single transposition already forces it.
The other half of the classification. -/
public theorem rel_diag_iff_of_permInvariant {r : X → X → Prop}
    (h : ∀ (π : Equiv.Perm X) (a b : X), r (π a) (π b) ↔ r a b) (x y : X) :
    r x x ↔ r y y := by
  classical
  have h' := h (Equiv.swap x y) x x
  rw [Equiv.swap_apply_left] at h'
  exact h'.symm

/--
**Igel–Toussaint's Theorem 4**, over print's own object: a non-trivial
neighbourhood relation on the search space is not invariant under permutations
of it.

Non-triviality is their condition verbatim — some pair of **distinct** points
neighbours, some pair of distinct points does not — and the conclusion is their
equation (6): a pair and a relabelling on which the relation disagrees with
itself.

Print requires `n` symmetric. This does not: symmetry never enters the argument,
so the hypothesis is dropped rather than assumed, and the diagonal is left
entirely free.
-/
public theorem exists_perm_rel_not_iff {r : X → X → Prop}
    (hedge : ∃ a b : X, a ≠ b ∧ r a b)
    (hnon : ∃ a b : X, a ≠ b ∧ ¬ r a b) :
    ∃ (a b : X) (π : Equiv.Perm X), ¬ (r (π a) (π b) ↔ r a b) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨x, y, hne, hxy⟩ := hedge
  obtain ⟨a, b, hab, hnab⟩ := hnon
  exact hnab (forall_rel_of_permInvariant (fun π a b => hcon a b π) hne hxy a b hab)

/--
**A simple graph fixed by every permutation of its vertices is complete or
empty.**

The graph reading of `forall_rel_of_permInvariant`, and the statement someone
looking for graph automorphisms would search for: if `Equiv.Perm X` is the whole
automorphism group of `G` then `G` is complete or empty. The converse holds too
and is easy, but is not proved here for general `X` — only at `Fin 3`, by
`Examples…top_permInvariant` and `Examples…bot_permInvariant`.

Looplessness is what removes the diagonal degree of freedom here, leaving the
plain dichotomy.
-/
public theorem forall_adj_or_forall_not_adj_of_permInvariant (G : SimpleGraph X)
    (h : ∀ (π : Equiv.Perm X) (a b : X), G.Adj (π a) (π b) ↔ G.Adj a b) :
    (∀ a b : X, a ≠ b → G.Adj a b) ∨ ∀ a b : X, ¬ G.Adj a b := by
  classical
  by_cases hall : ∀ a b : X, ¬ G.Adj a b
  · exact Or.inr hall
  push Not at hall
  obtain ⟨x, y, hxy⟩ := hall
  exact Or.inl (forall_rel_of_permInvariant h (G.ne_of_adj hxy) hxy)

/-- Theorem 4 for a graph, where an edge is distinct-by-construction so print's
first non-triviality clause needs no `≠`. -/
public theorem exists_perm_adj_not_iff (G : SimpleGraph X)
    (hedge : ∃ a b : X, G.Adj a b)
    (hnon : ∃ a b : X, a ≠ b ∧ ¬ G.Adj a b) :
    ∃ (a b : X) (π : Equiv.Perm X), ¬ (G.Adj (π a) (π b) ↔ G.Adj a b) := by
  obtain ⟨a, b, hab⟩ := hedge
  exact exists_perm_rel_not_iff ⟨a, b, G.ne_of_adj hab, hab⟩ hnon

end AISafetyAtlas.Combinatorics
