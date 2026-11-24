import AISafetyAtlas.Sovereignty.Representation

/-!
Peleg (1998), p. 72, remark after Definition 3.1. A superadditive effectivity
function satisfying conditions (i)–(iv) is monotone in its coalition argument.
The cited declarations are `Superadditive.coalitionMonotone` and
`Playable.mono_coalition`. The former supplies the statement on the broader
class of Lean hypotheses.

For a tested inclusion `S ⊆ T`, the map uses the three blocks `S`, `T \ S`
and the complement of `T` as players. The empty coalition gets the singleton
family containing the whole outcome space, and the grand coalition gets all
nonempty sets. At other coalitions, a set must contain `none` and its preimage
under `some` must be effective for the corresponding union of blocks.

Checked: `lake env lean docs/provenance/transfers/103-superadditive-coalition-monotone.lean`
-/

namespace Transfer103

open AISafetyAtlas.Sovereignty

universe u v

def PrintStatement : Prop :=
  ∀ (P : Type u) [Finite P] [Nonempty P] (X : Type v) (E : Set P → Set (Set X)),
    IsEffectivityFunction E → Superadditive E → CoalitionMonotone E

def LeanStatement : Prop :=
  ∀ (N : Type u) (X : Type v) (E : Set N → Set (Set X)),
    Superadditive E → (∀ S : Set N, Set.univ ∈ E S) → CoalitionMonotone E

noncomputable def player {N : Type u} (S T : Set N) : N → ULift.{u} (Fin 3) := by
  classical
  exact fun i => ⟨if i ∈ S then 0 else if i ∈ T then 1 else 2⟩

noncomputable def phi {N : Type u} {X : Type v}
    (E : Set N → Set (Set X)) (S T : Set N) :
    Set (ULift.{u} (Fin 3)) → Set (Set (Option X)) := by
  classical
  exact fun K =>
    if K = ∅ then {Set.univ}
    else if K = Set.univ then {B | B.Nonempty}
    else {B | none ∈ B ∧ Option.some ⁻¹' B ∈ E (player S T ⁻¹' K)}

theorem H {N : Type u} {X : Type v} {E : Set N → Set (Set X)} (S T : Set N)
    (hE : Superadditive E) (hSafe : ∀ K : Set N, Set.univ ∈ E K) :
    IsEffectivityFunction (phi E S T) ∧ Superadditive (phi E S T) := by
  classical
  constructor
  · refine ⟨by simp [phi], by simp [phi], ?_, ?_⟩
    · intro K
      by_cases hK : K = ∅
      · simpa [phi, hK, eq_comm] using
          (Set.univ_nonempty.ne_empty : (Set.univ : Set (Option X)) ≠ ∅)
      · by_cases hFull : K = Set.univ <;> simp [phi, hK, hFull]
    · intro K
      by_cases hK : K = ∅
      · simp [phi, hK]
      · by_cases hFull : K = Set.univ <;> simp [phi, hK, hFull, hSafe]
  · intro K L A B hKL hA hB
    by_cases hK : K = ∅
    · subst K
      have hA' : A = Set.univ := by simpa [phi] using hA
      simpa only [hA', Set.univ_inter, Set.empty_union] using hB
    by_cases hL : L = ∅
    · subst L
      have hB' : B = Set.univ := by simpa [phi] using hB
      simpa only [hB', Set.inter_univ, Set.union_empty] using hA
    have hKProper : K ≠ Set.univ := fun h => hL (by simpa [h] using hKL)
    have hLProper : L ≠ Set.univ := fun h => hK (by simpa [h] using hKL)
    have hA' : none ∈ A ∧ Option.some ⁻¹' A ∈ E (player S T ⁻¹' K) := by
      simpa [phi, hK, hKProper] using hA
    have hB' : none ∈ B ∧ Option.some ⁻¹' B ∈ E (player S T ⁻¹' L) := by
      simpa [phi, hL, hLProper] using hB
    have hNone : none ∈ A ∩ B := ⟨hA'.1, hB'.1⟩
    have hUnion : K ∪ L ≠ ∅ := fun h =>
      hK (Set.eq_empty_iff_forall_notMem.mpr fun i hi =>
        Set.eq_empty_iff_forall_notMem.mp h i (Set.mem_union_left L hi))
    by_cases hFull : K ∪ L = Set.univ
    · simpa [phi, hUnion, hFull] using (show (A ∩ B).Nonempty from ⟨none, hNone⟩)
    · have hInter : Option.some ⁻¹' (A ∩ B) ∈ E (player S T ⁻¹' (K ∪ L)) := by
        rw [Set.preimage_inter, Set.preimage_union]
        exact hE _ _ _ _ (hKL.preimage _) hA'.2 hB'.2
      simpa [phi, hUnion, hFull] using And.intro hNone hInter

theorem C {N : Type u} {X : Type v} (E : Set N → Set (Set X)) {S T : Set N}
    (hST : S ⊆ T) (hPrint : CoalitionMonotone (phi E S T)) : E S ⊆ E T := by
  classical
  let first : ULift.{u} (Fin 3) := ⟨0⟩
  let second : ULift.{u} (Fin 3) := ⟨1⟩
  let third : ULift.{u} (Fin 3) := ⟨2⟩
  let K : Set (ULift.{u} (Fin 3)) := {first}
  let L : Set (ULift.{u} (Fin 3)) := {first, second}
  have hKL : K ⊆ L := by simp [K, L]
  have hK : K ≠ ∅ := (show K.Nonempty from ⟨first, by simp [K]⟩).ne_empty
  have hL : L ≠ ∅ := (show L.Nonempty from ⟨first, by simp [L]⟩).ne_empty
  have hThirdFirst : third ≠ first := by decide
  have hThirdSecond : third ≠ second := by decide
  have hLProper : L ≠ Set.univ := by
    intro h
    have : third ∈ L := h ▸ Set.mem_univ third
    simp [L, hThirdFirst, hThirdSecond] at this
  have hKProper : K ≠ Set.univ := by
    intro h
    exact hLProper (Set.eq_univ_of_univ_subset (h ▸ hKL))
  have hPreK : player S T ⁻¹' K = S := by
    ext i
    by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
      simp [K, first, player, hS, hT]
  have hPreL : player S T ⁻¹' L = T := by
    ext i
    by_cases hS : i ∈ S
    · simp [L, first, second, player, hS, hST hS]
    · by_cases hT : i ∈ T <;> simp [L, first, second, player, hS, hT]
  intro B hB
  let lifted := Option.some '' B ∪ {none}
  have hSome : Option.some ⁻¹' lifted = B := by
    dsimp only [lifted]
    rw [Set.preimage_union, Set.preimage_image_eq _ (Option.some_injective X)]
    ext x
    simp
  have hLifted : lifted ∈ phi E S T K := by
    simp only [phi, if_neg hK, if_neg hKProper, Set.mem_ofPred_eq, hPreK, hSome]
    exact ⟨Set.mem_union_right _ (by simp), hB⟩
  have hResult := hPrint K L hKL hLifted
  have hPreResult : Option.some ⁻¹' lifted ∈ E T := by
    have : none ∈ lifted ∧ Option.some ⁻¹' lifted ∈ E T := by
      simpa only [phi, if_neg hL, if_neg hLProper, Set.mem_ofPred_eq, hPreL] using hResult
    exact this.2
  rwa [hSome] at hPreResult

theorem lean_of_print : PrintStatement.{u, v} → LeanStatement.{u, v} := by
  intro hPrint N X E hSuper hSafe S T hST
  obtain ⟨hEF, hPhiSuper⟩ := H S T hSuper hSafe
  exact C E hST (hPrint (ULift.{u} (Fin 3)) (Option X) (phi E S T) hEF hPhiSuper)

theorem print_of_lean : LeanStatement.{u, v} → PrintStatement.{u, v} := by
  intro hLean P _ _ X E hEF hSuper
  exact hLean P X E hSuper hEF.safe

end Transfer103
