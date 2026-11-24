import AISafetyAtlas.Sovereignty.TrulyPlayable

/-!
Goranko, Jamroga & Turrini (2013), Proposition 6, p. 14. Every playable
effectivity function `E : 2^N → 2^{2^S}` on a finite domain `S` is truly
playable. The player set is any set (author ruling of 2026-11-22 for the
Pauly §3 / Definition 2 rows). The cited declarations are
`Playable.trulyPlayable_of_finite` (print itself),
`Playable.trulyPlayable_of_finite_empty` (any outcome type, `E(∅)` a finite
family) and `Playable.trulyPlayable_of_exists_minimal` (any outcome type, a
minimal member of `E(∅)`). The last two are transferred here.

One map serves both routes, fixed by a finite family `F ⊆ E(∅)` below which
every member of `E(∅)` has a member of `F`: the whole of `E(∅)` in the
finite-family route, the supplied minimal member alone in the other. It sends
an outcome to its membership pattern in `F`, a function `F → Bool`, and pulls
`E` back along this pattern map, keeping the players. The printed core at the
whole pattern set supplies a minimal, hence least, member of the image's
`E(∅)`. Its preimage lies in `E(∅)` and below every member of `F`, hence below
every member of `E(∅)`, so it is a least member and the core is complete.

`print_of_lean` is given for the finite-family route only (a finite outcome
type has a finite `E(∅)`). For the minimal-member route the forward direction
needs a minimal member of a finite nonempty family; it is omitted.

Checked: `lake env lean docs/provenance/transfers/110-finite-cofinal-truly-playable.lean`
-/

namespace Transfer110

open AISafetyAtlas.Sovereignty

universe u v

def PrintStatement : Prop :=
  ∀ (N : Type u) (S : Type v) [Finite S] (E : Set N → Set (Set S)),
    Playable E → TrulyPlayable E

def LeanStatementFiniteEmpty : Prop :=
  ∀ (N : Type u) (X : Type v) (E : Set N → Set (Set X)),
    Playable E → (E (∅ : Set N)).Finite → TrulyPlayable E

def LeanStatementMinimal : Prop :=
  ∀ (N : Type u) (X : Type v) (E : Set N → Set (Set X)), Playable E →
    (∃ A ∈ E (∅ : Set N), ∀ B ∈ E (∅ : Set N), ¬ B ⊂ A) → TrulyPlayable E

variable {N : Type u} {X : Type v}

open Classical in
/-- An outcome's membership pattern in the family `F`. -/
noncomputable def pattern (F : Set (Set X)) (x : X) : ↥F → Bool :=
  fun B => decide (x ∈ B.1)

noncomputable def phi (E : Set N → Set (Set X)) (F : Set (Set X)) :
    Set N → Set (Set (↥F → Bool)) :=
  fun C => {K | pattern F ⁻¹' K ∈ E C}

theorem H {E : Set N → Set (Set X)} (hE : Playable E) (F : Set (Set X)) :
    Playable (phi E F) := by
  let f := pattern F
  change Playable (fun C => {K | f ⁻¹' K ∈ E C})
  refine ⟨fun C => hE.live C, fun C => hE.safe C, fun K hK => ?_,
    fun C K L hKL hK => hE.mono C _ _ (Set.preimage_mono hKL) hK, ?_⟩
  · exact hE.maximal (f ⁻¹' K) fun hc =>
      hK (by change f ⁻¹' Kᶜ ∈ E ∅; rwa [Set.preimage_compl])
  · intro C D K L hCD hK hL
    exact hE.superadd C D _ _ hCD hK hL

theorem C {E : Set N → Set (Set X)} (hE : Playable E) {F : Set (Set X)}
    (hF : F ⊆ E ∅) (hcof : ∀ A ∈ E (∅ : Set N), ∃ B ∈ F, B ⊆ A)
    (hPrint : TrulyPlayable (phi E F)) : TrulyPlayable E := by
  obtain ⟨hP', hcore⟩ := hPrint
  obtain ⟨K, hK, -⟩ := hcore Set.univ (hP'.safe ∅)
  have hB0 : pattern F ⁻¹' K ∈ E ∅ := hK.1
  have least : ∀ A ∈ E (∅ : Set N), pattern F ⁻¹' K ⊆ A := by
    intro A hA
    obtain ⟨B, hB, hBA⟩ := hcof A hA
    let KB : Set (↥F → Bool) := {y | y ⟨B, hB⟩ = true}
    have hpre : pattern F ⁻¹' KB = B := by ext x; simp [KB, pattern]
    have hKB : KB ∈ phi E F ∅ := by change pattern F ⁻¹' KB ∈ E ∅; rw [hpre]; exact hF hB
    have hsub := Set.preimage_mono (f := pattern F)
      (hP'.subset_of_mem_nonmonotonicCore_empty hK hKB)
    rw [hpre] at hsub
    exact hsub.trans hBA
  refine ⟨hE, fun A hA => ⟨pattern F ⁻¹' K, ⟨hB0, ?_⟩, least A hA⟩⟩
  rintro ⟨B, hB, hlt⟩
  exact hlt.2 (least B hB)

theorem lean_of_print_finiteEmpty : PrintStatement.{u, v} → LeanStatementFiniteEmpty.{u, v} := by
  intro hPrint N X E hE hfin
  have : Finite ↥(E (∅ : Set N)) := hfin.to_subtype
  exact C hE subset_rfl (fun A hA => ⟨A, hA, subset_rfl⟩)
    (hPrint N _ (phi E (E ∅)) (H hE _))

theorem lean_of_print_minimal : PrintStatement.{u, v} → LeanStatementMinimal.{u, v} := by
  intro hPrint N X E hE ⟨A, hA, hmin⟩
  have hcore : A ∈ nonmonotonicCore E ∅ := ⟨hA, fun ⟨B, hB, hlt⟩ => hmin B hB hlt⟩
  exact C hE (Set.singleton_subset_iff.2 hA)
    (fun A' hA' => ⟨A, rfl, hE.subset_of_mem_nonmonotonicCore_empty hcore hA'⟩)
    (hPrint N _ (phi E {A}) (H hE _))

theorem print_of_lean_finiteEmpty :
    LeanStatementFiniteEmpty.{u, v} → PrintStatement.{u, v} :=
  fun hLean N S _ E hE => hLean N S E hE (Set.toFinite _)

end Transfer110
