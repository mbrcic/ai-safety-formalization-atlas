module

public import AISafetyAtlas.Sovereignty.Representation
public import AISafetyAtlas.Sovereignty.TrulyPlayable
public import AISafetyAtlas.Sovereignty.Transfer

/-!
# Pauly's Theorem 3.2 at a finite outcome set, and the truly playable characterization

Marc Pauly, *A Modal Logic for Coalitional Power in Games*, J. Logic Computat.
12(1), 2002, Theorem 3.2 and the construction in its proof, pp. 152--154:

> An effectivity function E is playable iff it is the effectivity function of
> some strategic game. [...] let E be an effectivity function satisfying the
> five properties. We shall construct a game G such that E = E_G.

As printed the converse is false: `not_exists_gameForm_cofiniteEff` is Goranko,
Jamroga and Turrini's counterexample on an infinite outcome set. At a **finite**
outcome set the claim holds (their Proposition 6 makes playable and truly playable
coincide there), and their corrected theorem (Section 4.2) reads it at
any outcome set with true playability in place of playability. Both are here, at every coalition,
including the empty and the grand coalition, which `Playable.effectivity_paulyGame_eq`
leaves out.

* `TrulyPlayable.exists_gameForm` -- a truly playable E is the effectivity
  function of a game form with non-empty strategy sets, at any outcome type.
* `exists_gameForm_iff_trulyPlayable` -- Goranko, Jamroga and Turrini's corrected
  Theorem 3.2 as a biconditional.
* `Playable.exists_gameForm_of_finite` and `exists_gameForm_iff_playable_of_finite`
  -- Pauly's Theorem 3.2 at a finite outcome set, one direction and both.

## The route

Pauly's own game cannot be the carrier, even at a finite outcome set: on one
player over `Bool` with every coalition effective exactly for the sets containing
true, `paulyGame` reaches false (`Playable.surjective_paulyGame_outcome`), so
it puts {false} in the grand coalition's family. The example file runs that.

The construction here restricts the outcome set instead of revising the strategies.
Let Z be the least member of E(∅), which true playability provides
(`Playable.trulyPlayable_iff_principal`). Superadditivity with the empty coalition
gives A ∈ E C iff A ∩ Z ∈ E C, and N-maximality gives that the grand
coalition is effective for exactly the sets meeting Z. So the family read on the
subtype Z is one of Peleg's effectivity functions: the empty coalition is
effective only for the whole of Z and the grand coalition for every non-empty
subset. Peleg's sufficiency, `IsEffectivityFunction.effectivity_paulyGame`, builds
a game form on Z, and reading its outcome in X (`GameForm.map`,
`mem_effectivity_map_iff`) gives back E at every coalition. This is the place
N-maximality is consumed; `PlayableConverse` notes that its own construction
never reads it.

Goranko, Jamroga and Turrini, Section 4.2, instead restrict Pauly's selectors to
Z; the reduction here uses Peleg's Theorem 3.5 (Social Choice and Welfare 15,
1998) on the subtype. The two games
differ and represent the same function.
-/

namespace AISafetyAtlas.Sovereignty

universe u v

variable {N : Type u} {X : Type v} {E : Set N → Set (Set X)}

namespace Playable

/-! ## The least member of E(∅) decides every family -/

/-- Membership in any family is decided on Z, when Z ∈ E(∅). -/
private theorem mem_iff_inter_mem (hE : Playable E) {Z : Set X}
    (hZ : Z ∈ E (∅ : Set N)) {C : Set N} {A : Set X} :
    A ∈ E C ↔ A ∩ Z ∈ E C := by
  constructor
  · intro hA
    have := hE.superadd C ∅ A Z (Set.disjoint_empty C) hA hZ
    rwa [Set.union_empty] at this
  · exact hE.mono C _ _ Set.inter_subset_left

/-- The grand coalition is effective for exactly the sets meeting the least
member of E(∅). -/
private theorem mem_univ_iff (hE : Playable E) {Z : Set X}
    (hZ : Z ∈ E (∅ : Set N)) (hleast : ∀ B ∈ E (∅ : Set N), Z ⊆ B) {A : Set X} :
    A ∈ E (Set.univ : Set N) ↔ (A ∩ Z).Nonempty := by
  constructor
  · intro hA
    rw [hE.mem_iff_inter_mem hZ] at hA
    exact Set.nonempty_iff_ne_empty.mpr fun h => hE.live _ (h ▸ hA)
  · rintro ⟨x, hxA, hxZ⟩
    have hx : ({x} : Set X) ∈ E (Set.univ : Set N) := by
      refine hE.maximal _ fun hc => ?_
      exact (hleast _ hc hxZ) rfl
    exact hE.mono _ _ _ (Set.singleton_subset_iff.mpr hxA) hx

/-- The family E read on the subtype Z. -/
private def restrict (E : Set N → Set (Set X)) (Z : Set X) : Set N → Set (Set Z) :=
  fun C => {B | Subtype.val '' B ∈ E C}

private theorem isEffectivityFunction_restrict (hE : Playable E) {Z : Set X}
    (hZ : Z ∈ E (∅ : Set N)) (hleast : ∀ B ∈ E (∅ : Set N), Z ⊆ B) :
    IsEffectivityFunction (restrict E Z) where
  empty := by
    ext B
    simp only [restrict, Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · intro hB
      refine Set.eq_univ_of_forall fun z => ?_
      obtain ⟨y, hy, hyz⟩ := hleast _ hB z.2
      exact Subtype.val_injective hyz ▸ hy
    · rintro rfl
      rw [Set.image_univ, Subtype.range_coe]
      exact hZ
  univ := by
    ext B
    simp only [restrict, Set.mem_ofPred_eq]
    rw [hE.mem_univ_iff hZ hleast,
      Set.inter_eq_left.mpr (Subtype.coe_image_subset Z B), Set.image_nonempty]
  live := fun C h => hE.live C (by simpa [restrict] using h)
  safe := fun C => by
    simp only [restrict, Set.mem_ofPred_eq, Set.image_univ, Subtype.range_coe]
    have := (hE.mem_iff_inter_mem hZ (C := C) (A := Set.univ)).mp (hE.safe C)
    rwa [Set.univ_inter] at this

private theorem superadditive_restrict (hE : Playable E) (Z : Set X) :
    Superadditive (restrict E Z) := by
  intro C D B₁ B₂ hCD h₁ h₂
  simp only [restrict, Set.mem_ofPred_eq] at h₁ h₂ ⊢
  rw [Set.image_inter Subtype.val_injective]
  exact hE.superadd C D _ _ hCD h₁ h₂

private theorem upwardClosed_restrict (hE : Playable E) (Z : Set X) :
    UpwardClosed (restrict E Z) :=
  fun C _ _ hB hBB' => hE.mono C _ _ (Set.image_mono hBB') hB

end Playable

/-! ## The representation -/

/--
**Goranko, Jamroga and Turrini's corrected Theorem 3.2, construction direction.**
A truly playable effectivity function on a non-empty finite player set is the
effectivity function of a game form whose strategy sets are all non-empty, at
every coalition, the empty and the grand coalition included.

No finiteness is assumed on X. Pauly's Theorem 3.2 (p. 152) asks the same of a
merely playable E, which `not_exists_gameForm_cofiniteEff` refutes;
`Playable.exists_gameForm_of_finite` is the finite reading.
-/
public theorem TrulyPlayable.exists_gameForm [Finite N] [Nonempty N]
    (h : TrulyPlayable E) :
    ∃ G : GameForm.{u, v, max u v} N X,
      (∀ i, Nonempty (G.strategy i)) ∧ effectivity G = E := by
  classical
  have := Fintype.ofFinite N
  have hE : Playable E := h.1
  obtain ⟨Z, hZ, hleast⟩ := hE.trulyPlayable_iff_principal.mp h
  have hEF := hE.isEffectivityFunction_restrict hZ hleast
  have hs := hE.superadditive_restrict Z
  have hu := hE.upwardClosed_restrict Z
  refine ⟨(paulyGame (hEF.playable hs hu)).map Subtype.val, fun i => ?_, ?_⟩
  · exact ⟨((hEF.playable hs hu).nonempty_choiceFn i).some, Classical.arbitrary N,
      Classical.arbitrary _⟩
  · funext C
    ext A
    rw [mem_effectivity_map_iff, hEF.effectivity_paulyGame hs hu]
    show Subtype.val '' (Subtype.val ⁻¹' A : Set Z) ∈ E C ↔ A ∈ E C
    rw [Subtype.image_preimage_coe, Set.inter_comm, ← hE.mem_iff_inter_mem hZ]

/--
**Goranko, Jamroga and Turrini's corrected Theorem 3.2.** On a non-empty finite
player set, an effectivity function is the effectivity function of a game form
with non-empty strategy sets iff it is truly playable.
-/
public theorem exists_gameForm_iff_trulyPlayable [Finite N] [Nonempty N] :
    (∃ G : GameForm.{u, v, max u v} N X,
      (∀ i, Nonempty (G.strategy i)) ∧ effectivity G = E) ↔ TrulyPlayable E := by
  constructor
  · rintro ⟨G, hne, rfl⟩
    exact trulyPlayable_effectivity
  · exact TrulyPlayable.exists_gameForm

/--
**Pauly's Theorem 3.2, construction direction, at a finite outcome set.** Every
playable effectivity function on a finite outcome set, over a non-empty finite
player set, is E_G for a game form G with non-empty strategy sets, at every
coalition: print's *"We shall construct a game G such that E = E_G"* (p. 152),
under the finite-outcome repair.
-/
public theorem Playable.exists_gameForm_of_finite [Finite N] [Nonempty N] [Finite X]
    (hE : Playable E) :
    ∃ G : GameForm.{u, v, max u v} N X,
      (∀ i, Nonempty (G.strategy i)) ∧ effectivity G = E :=
  hE.trulyPlayable_of_finite.exists_gameForm

/--
**Pauly's Theorem 3.2 at a finite outcome set**, both directions: *"an
effectivity function E is playable iff it is the effectivity function of some
strategic game"* (p. 152), read at a finite outcome set and a non-empty finite
player set.
-/
public theorem exists_gameForm_iff_playable_of_finite [Finite N] [Nonempty N] [Finite X] :
    (∃ G : GameForm.{u, v, max u v} N X,
      (∀ i, Nonempty (G.strategy i)) ∧ effectivity G = E) ↔ Playable E := by
  constructor
  · rintro ⟨G, hne, rfl⟩
    exact playable_effectivity
  · exact Playable.exists_gameForm_of_finite

end AISafetyAtlas.Sovereignty
