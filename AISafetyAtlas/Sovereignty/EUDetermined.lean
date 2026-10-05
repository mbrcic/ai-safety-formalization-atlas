module

public import AISafetyAtlas.Sovereignty.Retargetable
public import Mathlib.Algebra.Group.Action.Pointwise.Set.Basic
public import Mathlib.Algebra.Group.Action.Pointwise.Finset

/-!
# Expected-utility-determined decision-makers have orbit-level tendencies

Turner and Tadepalli, *Parametrically Retargetable Decision-Makers Tend To Seek
Power*, arXiv:2206.13477v2, appendix B.2 and theorem A.13.

`AISafetyAtlas.Sovereignty.Retargetable` carries section 3, whose header says
plainly that section 3 is **not** about power and itemizes the five appendix
results standing between it and the paper's actual claim. This module discharges
that chain: lemma B.7, definition B.8, lemma B.9, lemma B.10, definition A.12,
lemma B.11 and theorem A.13.

## The chain, and what it does *not* need

A.13 says: if `B` contains `n` copies of `A` via permutations that also fix the
choice set `C`, and the decision-maker is determined by expected utilities, then
`B` is selected at `n` times as many parameters in every orbit.

Everything in it is finite subsets of a vector space, a group permuting
coordinates, and inner products. **No Markov decision process appears anywhere in
the chain**, and none is needed. The paper's MDP layer is appendix D, which
*instantiates* `A`, `B`, `C` as sets of recurrent state distributions; that is a
separate obligation and is not taken here. See the closing section.

## Fidelity notes, in the order they will matter to a reader

* **Item 1 of lemma B.7 is stated here without print's guard, because print's own
  proof of B.7 requires the unguarded form.** Print writes item 1 as *"there
  exist `B⋆ᵢ` such that **if** `f(B ∣ θ*) < f(A ∣ θ*)`, then `∀i : f(A ∣ θ*) ≤
  f(B⋆ᵢ ∣ φᵢ · θ*)"*. Its equation (25) applies item 1 at the parameter
  `φᵢ⁻¹ · θ*`, where the guard reads `f(B ∣ φᵢ · θ*) < f(A ∣ φᵢ · θ*)` -- the
  negation of the very inequality equation (29) concludes. So the guard cannot be
  available there. Lemma B.9, which is print's only consumer of B.7, discharges
  item 1 unguarded (*"Holds since `f(A ∣ θ*) ≤ f(φᵢ · A ∣ φᵢ · θ*) ≤ f(B⋆ᵢ ∣ φᵢ ·
  θ*)`"*, with no antecedent), so nothing downstream is weakened. Items 2 and 4
  keep their guards, which their uses do respect.
* **The involutions are load-bearing** and are hypotheses here. `ContainsCopies`
  in `Retargetable` deliberately drops print's involution clause, and that is
  sound for its own consumers; B.7 is not one of them, since equations (24), (31)
  and (36) all rewrite `φᵢ⁻¹` to `φᵢ`. `InvolutiveCopies` below is definition A.7
  verbatim, and `InvolutiveCopies.containsCopies` records that it is the stronger
  of the two.
* **The group is arbitrary**, as in `Retargetable`; print's is `S_d`.
* **B.11 is proved against an arbitrary invariant pairing** rather than against
  permutation matrices. Print's proof uses exactly one property of `P_φ` -- that
  it is orthogonal, so `xᵀu = (P_φ x)ᵀ(P_φ u)` -- and that property is the
  hypothesis here. Print's setting is the instance where the pairing is the dot
  product on `Fin d → ℝ` and the group acts by permuting coordinates.
* **Option sets are `Finset`s from definition A.12 onward, and `Set`s before it.**
  Corrected 2026-09-10: this bullet used to read *"option sets are `Set`s"* and
  said `EUDetermined` asked for something weaker than print's equation (4)
  *instead* of the multiset. Both halves were wrong about this file. Equation (4)
  is rendered closely -- `euProfile` **is** the multiset of pairings, and
  `EUDetermined` factors through it -- and the carrier at that point is
  `Finset V`, not `Set`. Only `InvolutiveCopies` and `ContainsCopies`, which
  never read a profile, are stated over `Set`.
  The one genuine narrowing is that carrier: print's type at A.12 is the power
  set `𝒫 (ℝᵈ)`. It is costed in section 16 of
  `docs/provenance/source-coverage-audit.md` and the cost buys nothing, since no
  step of the chain reads a cardinality and an infinite profile would need a
  multiplicity function `ℝ → Cardinal` that Mathlib does not carry. Print's
  equation (4) presupposes finiteness anyway by writing a multiset and its size;
  print's definition A.2 states it outright, while A.12 and A.13 do not restate
  it.
* **Print's cardinality index is dropped, and that is not a narrowing.** Print
  writes a *family* `{g^{ω₁,…,ω_m}}` indexed by the `|Xᵢ|`. `Multiset.card`
  recovers each `|Xᵢ|` from the profile itself, so the single `g` here carries
  the same data.
-/

namespace AISafetyAtlas.Sovereignty

open scoped Pointwise

universe u v w

variable {G : Type u} [Group G] {Ω : Type v} [MulAction G Ω]

/-! ## Moving inside an orbit -/

/-- Acting on a point of `orbitIn` keeps it in the orbit; membership in `Θ` is
the only thing that has to be supplied. -/
public theorem smul_mem_orbitIn {Θ : Set Ω} {θ θ' : Ω} (g : G)
    (h : θ' ∈ orbitIn G Θ θ) (hmem : g • θ' ∈ Θ) :
    g • θ' ∈ orbitIn G Θ θ := by
  obtain ⟨⟨x, hx⟩, _⟩ := h
  refine ⟨⟨g * x, ?_⟩, hmem⟩
  show (g * x) • θ = g • θ'
  rw [mul_smul]
  exact congrArg (g • ·) hx

/-! ## Lemma B.7, the quantitative general orbit lemma -/

section OrbitLemma

variable {E : Type w}

/--
**Lemma B.7 (quantitative general orbit lemma).**

For each parameter `θ` in `Θ`, print chooses involutions `φ₁, …, φₙ` and
alternative option sets `B⋆₁, …, B⋆ₙ`, and asks four conditions of every `θ'` in
`θ`'s orbit inside `Θ`. The conclusion is that `f B` beats `f A` at `n` times as
many orbit parameters.

The four hypotheses, in print's order:

1. *retargetable under parameter permutation* -- `f A θ' ≤ f (B⋆ i) (φ i • θ')`;
2. *`Θ` closed under certain symmetries* -- where `A` beats `B`, each `φ i • θ'`
   stays in `Θ`;
3. *`f` increasing on certain inputs* -- `f (B⋆ i) θ' ≤ f B θ'`;
4. *increasing under alternate symmetries* -- where `B` beats `A`, `B⋆ j` does no
   worse after acting by a *different* `φ i`.

Item 1 carries no guard here; the module header says why, and print's table 3
shows item 4's guard cannot be dropped.
-/
public theorem mostOrbit_of_orbitConditions [Finite G] {n : ℕ} {Θ : Set Ω}
    {f : E → Ω → ℝ} {A B : E}
    (h : ∀ θ ∈ Θ, ∃ φ : Fin n → G, ∃ Bstar : Fin n → E,
      (∀ i, φ i * φ i = 1) ∧
      (∀ θ' ∈ orbitIn G Θ θ, ∀ i, f A θ' ≤ f (Bstar i) (φ i • θ')) ∧
      (∀ θ' ∈ orbitIn G Θ θ, f B θ' < f A θ' → ∀ i, φ i • θ' ∈ Θ) ∧
      (∀ θ' ∈ orbitIn G Θ θ, ∀ i, f (Bstar i) θ' ≤ f B θ') ∧
      (∀ θ' ∈ orbitIn G Θ θ, f A θ' < f B θ' →
        ∀ i j, i ≠ j → f (Bstar j) θ' ≤ f (Bstar j) (φ i • θ'))) :
    MostOrbit G n Θ (f A) (f B) := by
  refine MultiplyRetargetable.mostOrbit ?_
  intro θ hθ
  obtain ⟨φ, Bstar, hinv, h1, h2, h3, h4⟩ := h θ hθ
  -- acting by `φ i` is its own inverse
  have hsmul : ∀ (i : Fin n) (x : Ω), φ i • φ i • x = x := by
    intro i x
    rw [← mul_smul, hinv i, one_smul]
  -- print's equations (24)-(29): the retargeted parameter favours `B`
  have hflip : ∀ i, ∀ θ' ∈ orbitAgainst G Θ (f A) (f B) θ,
      f A (φ i • θ') < f B (φ i • θ') := by
    intro i θ' hθ'
    have horb : θ' ∈ orbitIn G Θ θ := hθ'.1
    have hlt : f B θ' < f A θ' := hθ'.2
    have hmem : φ i • θ' ∈ orbitIn G Θ θ :=
      smul_mem_orbitIn _ horb (h2 θ' horb hlt i)
    calc f A (φ i • θ')
        ≤ f (Bstar i) (φ i • φ i • θ') := h1 _ hmem i
      _ = f (Bstar i) θ' := by rw [hsmul]
      _ ≤ f B θ' := h3 θ' horb i
      _ < f A θ' := hlt
      _ ≤ f (Bstar i) (φ i • θ') := h1 θ' horb i
      _ ≤ f B (φ i • θ') := h3 _ hmem i
  refine ⟨φ, hflip, fun i θ' hθ' => h2 θ' hθ'.1 hθ'.2 i, ?_⟩
  -- print's equations (30)-(39): the `n` retargeted copies are disjoint
  intro i j hij θ' hθ' θ'' hθ'' hEq
  have horb' : θ' ∈ orbitIn G Θ θ := hθ'.1
  have horb'' : θ'' ∈ orbitIn G Θ θ := hθ''.1
  have hmem' : φ i • θ' ∈ orbitIn G Θ θ :=
    smul_mem_orbitIn _ horb' (h2 θ' horb' hθ'.2 i)
  have hmem'' : φ j • θ'' ∈ orbitIn G Θ θ :=
    smul_mem_orbitIn _ horb'' (h2 θ'' horb'' hθ''.2 j)
  have hself : f A θ'' < f A θ'' := by
    calc f A θ''
        ≤ f (Bstar j) (φ j • θ'') := h1 θ'' horb'' j
      _ = f (Bstar j) (φ i • θ') := by rw [hEq]
      _ ≤ f (Bstar j) (φ i • φ i • θ') :=
          h4 _ hmem' (hflip i θ' hθ') i j hij
      _ = f (Bstar j) θ' := by rw [hsmul]
      _ ≤ f B θ' := h3 θ' horb' j
      _ < f A θ' := hθ'.2
      _ ≤ f (Bstar i) (φ i • θ') := h1 θ' horb' i
      _ = f (Bstar i) (φ j • θ'') := by rw [hEq]
      _ ≤ f (Bstar i) (φ j • φ j • θ'') :=
          h4 _ hmem'' (hflip j θ'' hθ'') j i (Ne.symm hij)
      _ = f (Bstar i) θ'' := by rw [hsmul]
      _ ≤ f B θ'' := h3 θ'' horb'' i
      _ < f A θ'' := hθ''.2
  exact absurd hself (lt_irrefl _)

end OrbitLemma

/-! ## Option sets, abstractly

Lemma B.9 and definition B.8 are stated by print over a family `E` of subsets of
`ℝᵈ`, ordered by inclusion and permuted pointwise. The two properties the proof
uses are exactly that: an order, and an action. So they are stated here over an
arbitrary ordered `G`-set, and `Set X` -- print's case -- is one instance of it.
`Finset V` is the other, and is what theorem A.13 needs, because print's
equation (4) reads a *multiset* of inner products and a multiset needs a finite
option set.
-/

section Abstract

variable {𝔈 : Type w} [Preorder 𝔈] [MulAction G 𝔈]

/--
**Definition B.4, at the shape lemma B.9 uses.** `f` does not decrease when its
option set and its parameter are permuted *together* by any `φ i`.
-/
@[expose] public def IncreasingUnderJointPerm {n : ℕ} (E : Set 𝔈) (Θ : Set Ω)
    (φ : Fin n → G) (f : 𝔈 → Ω → ℝ) : Prop :=
  ∀ i, ∀ S ∈ E, ∀ θ ∈ Θ, f S θ ≤ f (φ i • S) (φ i • θ)

/--
**Definition B.8 (superset-of-copy containment).** `B` contains `n`
*superset-copies* `B⋆ i` of `A` when involutions carry `A` *inside* each `B⋆ i`,
each `B⋆ i` sits inside `B`, and each `φ i` fixes every other `B⋆ j`.

This is the form lemma B.9 consumes: definition A.7 asks for `φ i • A` on the
nose, B.8 lets a larger set sit in between.
-/
@[expose] public def SupersetCopies (G : Type u) [Group G] [MulAction G 𝔈]
    (n : ℕ) (B A : 𝔈) (Bstar : Fin n → 𝔈) (φ : Fin n → G) : Prop :=
  (∀ i, φ i * φ i = 1) ∧
  (∀ i, φ i • A ≤ Bstar i) ∧
  (∀ i, Bstar i ≤ B) ∧
  (∀ i j, i ≠ j → φ i • Bstar j = Bstar j)

/--
**Lemma B.9 (looser sufficient conditions for orbit-level incentives).**

If `Θ` is closed under the group, `B` contains `n` superset-copies of `A` inside
the family `E`, `f` is increasing under joint permutation on `E`, and `f` is
monotone in its option set, then `f B` beats `f A` at `n` times as many orbit
parameters.

The proof is print's: check the four conditions of lemma B.7. Item 1 is joint
permutation followed by monotonicity, item 2 is closure of `Θ`, item 3 is
monotonicity, and item 4 is joint permutation combined with `φ i` fixing `B⋆ j`.
-/
public theorem mostOrbit_of_supersetCopies [Finite G] {n : ℕ} {Θ : Set Ω}
    {E : Set 𝔈} {f : 𝔈 → Ω → ℝ} {A B : 𝔈} {Bstar : Fin n → 𝔈} {φ : Fin n → G}
    (hclosed : ∀ (g : G), ∀ θ ∈ Θ, g • θ ∈ Θ)
    (hA : A ∈ E) (hB : B ∈ E) (hstar : ∀ i, Bstar i ∈ E) (hsmulA : ∀ i, φ i • A ∈ E)
    (hcopies : SupersetCopies G n B A Bstar φ)
    (hjoint : IncreasingUnderJointPerm E Θ φ f)
    (hmono : ∀ S ∈ E, ∀ T ∈ E, S ≤ T → ∀ θ, f S θ ≤ f T θ) :
    MostOrbit G n Θ (f A) (f B) := by
  obtain ⟨hinv, hsubStar, hstarB, hfix⟩ := hcopies
  refine mostOrbit_of_orbitConditions (f := f) (A := A) (B := B) ?_
  intro θ hθ
  refine ⟨φ, Bstar, hinv, ?_, ?_, ?_, ?_⟩
  · intro θ' hθ' i
    exact le_trans (hjoint i A hA θ' hθ'.2)
      (hmono _ (hsmulA i) _ (hstar i) (hsubStar i) _)
  · intro θ' hθ' _ i
    exact hclosed (φ i) θ' hθ'.2
  · intro θ' hθ' i
    exact hmono _ (hstar i) _ hB (hstarB i) _
  · intro θ' hθ' _ i j hij
    have := hjoint i (Bstar j) (hstar j) θ' hθ'.2
    rwa [hfix i j hij] at this

end Abstract

/-! ## Definition A.7 with print's involutions -/

section Copies

variable {X : Type w} [MulAction G X]

/--
**Definition A.7, verbatim.** `B` contains `n` copies of `A` when there are `n`
**involutions** carrying `A` into `B` whose images are fixed by each other.

`ContainsCopies` in `AISafetyAtlas.Sovereignty.Retargetable` is this definition
with the involution clause dropped, which is wider and is sound for its own
consumers. Lemma B.7 is not one of them, so this is the version the chain uses.

Print's footnote 8 records a degeneracy of its own definition: taking every `φ i`
to be the identity shows that `A` contains `n` copies of `A` for every `n`. Print
declines to rule it out, because enforcing pairwise disjointness of the images
"would narrow our results to not apply e.g. when the `Bᵢ` share a constant
vector". That looseness is print's and is reproduced here.
-/
@[expose] public def InvolutiveCopies (G : Type u) [Group G] [MulAction G X]
    (n : ℕ) (B A : Set X) : Prop :=
  ∃ φ : Fin n → G,
    (∀ i, φ i * φ i = 1) ∧
    (∀ i, (fun ω => φ i • ω) '' A ⊆ B) ∧
    (∀ i j, i ≠ j → (fun ω => φ i • ω) '' ((fun ω => φ j • ω) '' A)
      = (fun ω => φ j • ω) '' A)

/-- Print's involution clause is extra information, so definition A.7 as printed
is the stronger of the two renderings. -/
public theorem InvolutiveCopies.containsCopies {n : ℕ} {A B : Set X}
    (h : InvolutiveCopies G n B A) : ContainsCopies G n B A := by
  obtain ⟨φ, _, hsub, hfix⟩ := h
  exact ⟨φ, hsub, hfix⟩

/-- **Definition A.7 gives definition B.8**, taking `B⋆ i` to be the copy `φ i • A`
itself. So the chain's looser hypothesis is genuinely looser. -/
public theorem InvolutiveCopies.supersetCopies {n : ℕ} {A B : Set X}
    (h : InvolutiveCopies G n B A) :
    ∃ (Bstar : Fin n → Set X) (φ : Fin n → G), SupersetCopies G n B A Bstar φ := by
  obtain ⟨φ, hinv, hsub, hfix⟩ := h
  refine ⟨fun i => φ i • A, φ, hinv, fun i => le_rfl, fun i => ?_, fun i j hij => ?_⟩
  · simpa only [Set.image_smul] using hsub i
  · simpa only [Set.image_smul] using hfix i j hij

end Copies

/-! ## Lemma B.10 -/

section Hiding

variable {𝔈 : Type w} [MulAction G 𝔈] {𝔉 : Type*} [MulAction G 𝔉]

/--
**Lemma B.10 (hiding an argument which is invariant under certain permutations).**

If every `φ i` fixes the choice set `C`, then fixing `C` in a two-set scoring
function leaves a one-set function that is still increasing under joint
permutation. This is what lets theorem A.13 speak of `p (X ∣ u)` while the
underlying `h` takes the choice set as a second argument.
-/
public theorem increasingUnderJointPerm_of_hide {n : ℕ} {E : Set 𝔈} {Θ : Set Ω}
    {φ : Fin n → G} {C : 𝔉} (h : 𝔈 → 𝔉 → Ω → ℝ)
    (hC : ∀ i, φ i • C = C)
    (hincr : ∀ i, ∀ S ∈ E, ∀ θ ∈ Θ, h S C θ ≤ h (φ i • S) (φ i • C) (φ i • θ)) :
    IncreasingUnderJointPerm E Θ φ (fun S θ => h S C θ) := by
  intro i S hS θ hθ
  have hle := hincr i S hS θ hθ
  rwa [hC i] at hle

/-- Print's *"furthermore"*: an `h` that is **invariant** under joint permutation
hides an invariant argument, so the residue is invariant too, hence increasing. -/
public theorem increasingUnderJointPerm_of_hide_invariant {n : ℕ} {E : Set 𝔈}
    {Θ : Set Ω} {φ : Fin n → G} {C : 𝔉} (h : 𝔈 → 𝔉 → Ω → ℝ)
    (hC : ∀ i, φ i • C = C)
    (hinv : ∀ (g : G) (S : 𝔈) (θ : Ω), h (g • S) (g • C) (g • θ) = h S C θ) :
    IncreasingUnderJointPerm E Θ φ (fun S θ => h S C θ) :=
  increasingUnderJointPerm_of_hide h hC
    fun i S _ θ _ => le_of_eq (hinv (φ i) S θ).symm

end Hiding

/-! ## Definition A.12, lemma B.11 and theorem A.13 -/

section EUDetermined

variable {V : Type w} [DecidableEq V] [MulAction G V]

/--
The multiset of expected utilities of the options in `X` at parameter `u`: print's
`[xᵀu]_{x ∈ X}`.

A multiset, not a set, because multiplicities are load-bearing -- two distinct
options may have the same expected utility, and a Boltzmann-rational agent sums
over both. That is why the option sets here are `Finset`s.
-/
@[expose] public def euProfile (pair : V → V → ℝ) (u : V) (X : Finset V) : Multiset ℝ :=
  X.val.map fun x => pair x u

/--
**Definition A.12 (EU-determined functions)**, at the two-argument case theorem
A.13 uses.

`h` is EU-determined when it reads its option sets only through the multisets of
expected utilities they induce.

Print writes a *family* `{g^{ω₁,…,ω_m}}` indexed by the cardinalities `|Xᵢ|`. The
index is redundant: `Multiset.card` recovers `|Xᵢ|` from the profile itself, so a
single `g` carries the same data. Print's `m` is arbitrary; A.13 uses `m = 2` and
that is the case rendered here.
-/
@[expose] public def EUDetermined (pair : V → V → ℝ)
    (h : Finset V → Finset V → V → ℝ) : Prop :=
  ∃ g : Multiset ℝ → Multiset ℝ → ℝ,
    ∀ X Y u, h X Y u = g (euProfile pair u X) (euProfile pair u Y)

/-- The expected-utility profile is unchanged when the options and the parameter
are permuted together, provided the pairing is invariant. This is the whole
content of lemma B.11. -/
public theorem euProfile_smul {pair : V → V → ℝ}
    (hpair : ∀ (g : G) (x u : V), pair (g • x) (g • u) = pair x u)
    (g₀ : G) (u : V) (X : Finset V) :
    euProfile pair (g₀ • u) (g₀ • X) = euProfile pair u X := by
  rw [euProfile, euProfile, Finset.smul_finset_def,
    Finset.image_val_of_injOn ((MulAction.injective g₀).injOn), Multiset.map_map]
  exact Multiset.map_congr rfl fun x _ => hpair g₀ x u

/--
**Lemma B.11 (EU-determined functions are invariant under joint permutation).**

Print's proof uses exactly one property of the permutation matrix `P_φ`: that it
is orthogonal, so `xᵀu = (P_φ x)ᵀ(P_φ u)`. That property is the hypothesis
`hpair` here, which is why the lemma is stated for an arbitrary invariant pairing
rather than for permutation matrices. Print's setting is the instance where the
pairing is the dot product and the group permutes coordinates.
-/
public theorem EUDetermined.jointPermInvariant {pair : V → V → ℝ}
    {h : Finset V → Finset V → V → ℝ} (hEU : EUDetermined pair h)
    (hpair : ∀ (g : G) (x u : V), pair (g • x) (g • u) = pair x u)
    (g₀ : G) (X Y : Finset V) (u : V) :
    h (g₀ • X) (g₀ • Y) (g₀ • u) = h X Y u := by
  obtain ⟨g, hg⟩ := hEU
  rw [hg, hg, euProfile_smul hpair, euProfile_smul hpair]

/--
**Theorem A.13 (orbit tendencies occur for EU-determined decision-making
functions).**

If `B` contains `n` superset-copies of `A` via involutions that also fix the
choice set `C`, and the selection probability is determined by expected
utilities, then `B` is selected at `n` times as many parameters in every orbit.

`hmono` is print's sentence *"suppose that `p` returns a probability of selecting
an element of `X` from `C`"*, which its proof immediately reads as *"`p` obeys the
monotonicity probability axiom: if `X' ⊆ X` then `f(X' ∣ u) ≤ f(X ∣ u)`"*. It is
stated here as the monotonicity, since that is the only use print makes of it.
Note that print does not require `A, B ⊆ C`, although its proposition A.11 does.

Print's `Θ` is all of `ℝᵈ`, which is `Set.univ` here.
-/
public theorem eu_determined_mostOrbit [Finite G] {n : ℕ} {pair : V → V → ℝ}
    {h : Finset V → Finset V → V → ℝ} {A B C : Finset V} {Bstar : Fin n → Finset V}
    {φ : Fin n → G}
    (hEU : EUDetermined pair h)
    (hpair : ∀ (g : G) (x u : V), pair (g • x) (g • u) = pair x u)
    (hC : ∀ i, φ i • C = C)
    (hcopies : SupersetCopies G n B A Bstar φ)
    (hmono : ∀ X Y : Finset V, X ⊆ Y → ∀ u, h X C u ≤ h Y C u) :
    MostOrbit G n (Set.univ : Set V) (fun u => h A C u) (fun u => h B C u) :=
  mostOrbit_of_supersetCopies
    (fun _ _ _ => Set.mem_univ _)
    (Set.mem_univ A) (Set.mem_univ B) (fun _ => Set.mem_univ _) (fun _ => Set.mem_univ _)
    hcopies
    (increasingUnderJointPerm_of_hide_invariant (fun X Y u => h X Y u) hC
      fun g X u => hEU.jointPermInvariant hpair g X C u)
    (fun X _ Y _ hXY u => hmono X Y hXY u)

end EUDetermined

end AISafetyAtlas.Sovereignty
