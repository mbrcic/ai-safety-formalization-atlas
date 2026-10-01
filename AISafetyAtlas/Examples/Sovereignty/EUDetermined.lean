module

public import AISafetyAtlas.Sovereignty.EUDetermined
public import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# Theorem A.13 has a model, and its antecedent is not empty

`eu_determined_mostOrbit` carries five hypotheses. Two failures would be invisible
without a witness: they could be jointly unsatisfiable, or satisfiable only where
`orbitAgainst` is empty, in which case the counting conclusion `n * 0 ≤ _` would
hold for nothing.

This file rules out both, at print's own smallest interesting case: two
coordinates, the symmetric group on them, and a Boltzmann-shaped selection
weight.

## The witness

Options and parameters both live in `Fin 2 → ℚ`, permuted by `Equiv.Perm (Fin 2)`
reindexing coordinates. The pairing is the dot product, which is invariant because
reindexing both factors by the same permutation is a reindexing of one sum.

`selectWeight` sends an option set to the sum of `Real.exp` of its expected
utilities -- the numerator of the Boltzmann rationality print gives as its worked
example of an EU-determined function. It is EU-determined because it reads the
options only through that multiset, and monotone because its summands are
positive.

`optA` is the first basis vector and `optB` the second, so the transposition
carries `optA` onto `optB`: `optB` contains one copy of `optA`, and the
transposition fixes the choice set `{optA, optB}`.

The two are *incomparable*, which is what makes the example say something. Had
`optA ⊆ optB` been chosen, `selectWeight` would favour `optB` everywhere and
`orbitAgainst` would be empty by accident.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

open scoped Pointwise

/-- Permutations act on coordinate-indexed families by reindexing. Scoped to this
file: it is a witness, not an instance the atlas offers. -/
public scoped instance permArrow {α β : Type} :
    MulAction (Equiv.Perm α) (α → β) where
  smul φ x := x ∘ φ.symm
  one_smul _ := rfl
  mul_smul _ _ _ := rfl

/-- The dot product of two rational coordinate families, valued in `ℝ`. -/
@[expose] public def dotPair (x u : Fin 2 → ℚ) : ℝ :=
  ∑ i, (x i : ℝ) * (u i : ℝ)

/-- **The pairing is invariant under joint reindexing.** Print gets this from
orthogonality of permutation matrices; here it is one reindexing of a sum. -/
public theorem dotPair_smul (φ : Equiv.Perm (Fin 2)) (x u : Fin 2 → ℚ) :
    dotPair (φ • x) (φ • u) = dotPair x u := by
  show ∑ i, ((x (φ.symm i) : ℝ)) * ((u (φ.symm i) : ℝ)) = ∑ i, (x i : ℝ) * (u i : ℝ)
  exact Equiv.sum_comp φ.symm fun i => (x i : ℝ) * (u i : ℝ)

/-- The Boltzmann numerator: the total exponentiated expected utility of the
options in `X`. The second argument is the choice set, which this weight ignores;
`eu_determined_mostOrbit` supplies it because print's `h` takes one. -/
@[expose] public noncomputable def selectWeight
    (X : Finset (Fin 2 → ℚ)) (_C : Finset (Fin 2 → ℚ)) (u : Fin 2 → ℚ) : ℝ :=
  ∑ x ∈ X, Real.exp (dotPair x u)

/-- **It is EU-determined**: it reads the options only through the multiset of
their expected utilities. -/
public theorem selectWeight_euDetermined :
    EUDetermined dotPair selectWeight :=
  ⟨fun P _ => (P.map Real.exp).sum, fun X Y u => by
    show ∑ x ∈ X, Real.exp (dotPair x u)
      = (Multiset.map Real.exp (euProfile dotPair u X)).sum
    rw [euProfile, Multiset.map_map]
    rfl⟩

/-- **And monotone in its option set**, because every summand is positive. -/
public theorem selectWeight_mono (X Y C : Finset (Fin 2 → ℚ)) (hXY : X ⊆ Y)
    (u : Fin 2 → ℚ) : selectWeight X C u ≤ selectWeight Y C u :=
  Finset.sum_le_sum_of_subset_of_nonneg hXY fun _ _ _ => (Real.exp_pos _).le

/-- The first coordinate direction. -/
@[expose] public def e₀ : Fin 2 → ℚ := fun i => if i = 0 then 1 else 0

/-- The second coordinate direction. -/
@[expose] public def e₁ : Fin 2 → ℚ := fun i => if i = 1 then 1 else 0

/-- The transposition of the two coordinates. -/
@[expose] public def swap2 : Equiv.Perm (Fin 2) := Equiv.swap 0 1

/-- The option set that will lose, and the one that will win: single directions,
so neither contains the other. -/
@[expose] public def optA : Finset (Fin 2 → ℚ) := {e₀}

/-- The winning option set. -/
@[expose] public def optB : Finset (Fin 2 → ℚ) := {e₁}

/-- The choice set, which the transposition fixes. -/
@[expose] public def choices : Finset (Fin 2 → ℚ) := {e₀, e₁}

/-- The transposition is an involution. -/
public theorem swap2_involutive : swap2 * swap2 = 1 := Equiv.swap_mul_self 0 1

/-- The transposition carries the first direction onto the second. -/
public theorem swap2_smul_e₀ : swap2 • e₀ = e₁ := by
  funext i
  show e₀ (swap2.symm i) = e₁ i
  fin_cases i <;> simp [swap2, e₀, e₁]

/-- And the second onto the first. -/
public theorem swap2_smul_e₁ : swap2 • e₁ = e₀ := by
  funext i
  show e₁ (swap2.symm i) = e₀ i
  fin_cases i <;> simp [swap2, e₀, e₁]

/-- **`optB` contains one superset-copy of `optA`.** -/
public theorem optB_supersetCopies :
    SupersetCopies (Equiv.Perm (Fin 2)) 1 optB optA (fun _ => optB) (fun _ => swap2) := by
  refine ⟨fun _ => swap2_involutive, fun _ => ?_, fun _ => le_rfl,
    fun i j hij => absurd (Subsingleton.elim i j) hij⟩
  show swap2 • optA ≤ optB
  rw [optA, Finset.smul_finset_singleton, swap2_smul_e₀, optB]

/-- **And it fixes the choice set.** -/
public theorem swap2_smul_choices : swap2 • choices = choices := by
  rw [choices, Finset.smul_finset_insert, Finset.smul_finset_singleton,
    swap2_smul_e₀, swap2_smul_e₁]
  exact Finset.pair_comm e₁ e₀

/-- **Theorem A.13 applies here.** Every hypothesis is discharged, so the theorem
is not an implication from an empty antecedent. -/
public theorem witness_mostOrbit :
    MostOrbit (Equiv.Perm (Fin 2)) 1 (Set.univ : Set (Fin 2 → ℚ))
      (fun u => selectWeight optA choices u) (fun u => selectWeight optB choices u) :=
  eu_determined_mostOrbit selectWeight_euDetermined
    (fun g x u => dotPair_smul g x u)
    (fun _ => swap2_smul_choices)
    optB_supersetCopies
    (fun X Y hXY u => selectWeight_mono X Y choices hXY u)

/-- **The conclusion is not about an empty set.** At the parameter `e₀` the losing
option set is strictly preferred, so `orbitAgainst` is inhabited and the counting
inequality `1 * |against| ≤ |favouring|` is a claim about a nonempty left-hand
side rather than `0 ≤ _`. -/
public theorem selectWeight_optB_lt_optA_at_e₀ :
    selectWeight optB choices e₀ < selectWeight optA choices e₀ := by
  have hA : dotPair e₀ e₀ = 1 := by
    show ∑ i, ((e₀ i : ℝ)) * ((e₀ i : ℝ)) = 1
    rw [Fin.sum_univ_two]; norm_num [e₀]
  have hB : dotPair e₁ e₀ = 0 := by
    show ∑ i, ((e₁ i : ℝ)) * ((e₀ i : ℝ)) = 0
    rw [Fin.sum_univ_two]; norm_num [e₀, e₁]
  rw [selectWeight, selectWeight, optA, optB, Finset.sum_singleton,
    Finset.sum_singleton, hA, hB, Real.exp_zero]
  have h1 := Real.add_one_le_exp (1 : ℝ)
  linarith

/-! ## Definition A.7 as printed, and the two renderings it implies -/

/-- **The involutive form of the copy relation, at the same transposition.**

This is print's definition A.7 with its involution clause intact: the
transposition squares to the identity, carries the one direction onto the other,
and the pairwise condition is vacuous at a single copy. -/
public theorem singleton_involutiveCopies :
    InvolutiveCopies (Equiv.Perm (Fin 2)) 1 ({e₁} : Set (Fin 2 → ℚ))
      ({e₀} : Set (Fin 2 → ℚ)) :=
  ⟨fun _ => swap2, fun _ => swap2_involutive,
    fun _ => by rw [Set.image_singleton, swap2_smul_e₀],
    fun i j hij => absurd (Subsingleton.elim i j) hij⟩

/-- **A.7 gives the containment rendering.** The involution clause is extra
information, so nothing is lost in dropping it. -/
public theorem singleton_containsCopies :
    ContainsCopies (Equiv.Perm (Fin 2)) 1 ({e₁} : Set (Fin 2 → ℚ))
      ({e₀} : Set (Fin 2 → ℚ)) :=
  singleton_involutiveCopies.containsCopies

/-- **And it gives the superset rendering**, taking each copy to be its own
superset. Both weakenings are inhabited here, so the chain's looser hypothesis
is genuinely looser rather than vacuously so. -/
public theorem singleton_supersetCopies :
    ∃ (Bstar : Fin 1 → Set (Fin 2 → ℚ)) (φ : Fin 1 → Equiv.Perm (Fin 2)),
      SupersetCopies (Equiv.Perm (Fin 2)) 1 ({e₁} : Set (Fin 2 → ℚ))
        ({e₀} : Set (Fin 2 → ℚ)) Bstar φ :=
  singleton_involutiveCopies.supersetCopies

/-- **And containing one copy weakens to containing none**, which is the count's
downward monotonicity at the witness already built above. -/
public theorem singleton_containsCopies_zero :
    ContainsCopies (Equiv.Perm (Fin 2)) 0 ({e₁} : Set (Fin 2 → ℚ))
      ({e₀} : Set (Fin 2 → ℚ)) :=
  ContainsCopies.mono (Nat.zero_le 1) singleton_containsCopies

end AISafetyAtlas.Examples.Sovereignty
