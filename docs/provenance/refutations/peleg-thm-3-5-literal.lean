import AISafetyAtlas.Examples.Sovereignty.Rights
import AISafetyAtlas.Sovereignty.Representation

/-!
# Peleg Theorem 3.5's necessity of (i) as printed is false; the repaired (i) holds

Bezalel Peleg, *Effectivity functions, game forms, games, and rights*, Soc Choice
Welfare 15 (1998) 67--80, Theorem 3.5, p. 73 (audit row S21-R23):

    Theorem 3.5. Let E : 2^N →→ 2^A be the EF which is derived by (3.1). Then
    there exists a GF Γ = ⟨N; Σ¹, …, Σⁿ; g; A⟩ such that E_α(S; Γ) = E(S) for all
    S ∈ 2^N iff the following two conditions hold:
    (i) γ is monotonic w.r.t. the alternatives;
    (ii) E is superadditive.

(Transcribed from the page image in
`docs/provenance/printed-statements/peleg-1998-effectivity-functions.yaml`, entry
`peleg-thm-3.5`.) Condition (i) is (3.3), stated on `γ` at **every** set of rights
`θ`, while (3.1) reads `γ` only on the diagonal, `E(S) = γ(S, α(S))`; print says
so itself on p. 70: "the values γ(S, θ) where θ ≠ α(S) do not enter the analysis
of a society at a given date". So the direction "a representing GF exists ⇒ (i)"
is false. This file proves it on a society meeting every hypothesis print has in
force there: the standing assumptions of p. 69 (`α(∅) = ∅`,
`γ(∅, θ) = γ(S, ∅) = {A}`), condition (3.5), which print says (p. 72) "we shall
usually assume", and `E` an EF. The society is Example 2.3's two-shirt society with
a second right, so that `θ = {ρ₁}` is neither empty nor all of `ρ`, and with
`γ(S, {ρ₁}) = {A, {(w, w)}}` for `S ≠ ∅`. The family `{A, {(w, w)}}` is not closed
upwards, so (3.3) fails: `{(w, w)} ⊆ {(w, w), (w, b)}`, and the second set is not
in it. On the diagonal the society is the two-shirt society, so print's own
Example 3.6 game form represents it.

The library's witness `represented_not_monotoneAlternatives` puts `{∅}` off the
diagonal instead, and that breaks (3.5): from `∅ ⊆ {1}` at `θ = {ρ₁}`,
`{A} ⊄ {∅}` (`not_offDiagonal_monotoneCoalitions`). The family here contains `A`, so
the off-diagonal values grow with the coalition and (3.5) holds
(`variant_monotoneCoalitions`). Condition (3.4), monotonicity in the rights, fails
here (at `S = {1}`, `{ρ₁} ⊆ ρ`, since `{(w, w)}` is not in `γ(1, ρ)`; not proved
here); print does not assume it and says on p. 72 that it "generally does not
hold".

Why the repair is the necessary one and not a different theorem: it moves (i) to
the diagonal, "`E` is monotonic w.r.t. the alternatives", which is print's own
Theorem 3.5* in the appendix (p. 79, (3.8)), from which print says "Clearly,
Theorem 3.5* implies Theorem 3.5". It is what representation can see
(`Represents.upwardClosed`), and with it the library proves both directions
(`Constitution.exists_represents_iff_superadditive`, and
`exists_gameForm_of_isEffectivityFunction` on a bare EF).

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/peleg-thm-3-5-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips).
-/

open AISafetyAtlas.Sovereignty AISafetyAtlas.Examples.Sovereignty

namespace PelegTheoremThreeFiveLiteral

/-- **The direction "representable ⇒ (i)" of Theorem 3.5 exactly as printed**, under
every hypothesis print has in force: finite non-empty `N`, the standing
assumptions, (3.5), and `E = γ(·, α(·))` an EF. Condition (i) is (3.3) on `γ`. -/
def LiteralPrint : Prop :=
  ∀ (N X R : Type) [Fintype N] [Nonempty N] (κ : Constitution N X R),
    κ.Standing → κ.MonotoneCoalitions → IsEffectivityFunction κ.induced →
    (∃ G : GameForm.{0, 0, 0} N X, Represents G κ) → κ.MonotoneAlternatives

open Classical in
/-- The two-shirt society with rights `Bool`: every non-empty coalition holds both
rights; with both it attains what it pins down, with none only `A`, and with
exactly one right (off the diagonal) the family `{A, {(w, w)}}`. -/
noncomputable def variant : Constitution Bool Outfit Bool where
  assign := fun C => {_r | C.Nonempty}
  access := fun C θ =>
    if C = ∅ ∨ θ = ∅ then {Set.univ}
    else if θ = Set.univ then shirtAccess C
    else {Set.univ, {(false, false)}}

theorem univ_mem_variant_access (C : Set Bool) (θ : Set Bool) :
    Set.univ ∈ variant.access C θ := by
  simp only [variant]
  split_ifs
  · rfl
  · exact univ_mem_shirtAccess C
  · exact Or.inl rfl

/-- Off the empty coalition and the empty set of rights, the value is read from
`θ` alone. -/
theorem variant_access_of_ne {C θ : Set Bool} (hC : C ≠ ∅) (hθ : θ ≠ ∅) :
    variant.access C θ =
      if θ = Set.univ then shirtAccess C else {Set.univ, {(false, false)}} :=
  if_neg (not_or.mpr ⟨hC, hθ⟩)

/-- On the diagonal it is the two-shirt society. -/
theorem variant_induced (C : Set Bool) : variant.induced C = shirtAccess C := by
  by_cases hC : C = ∅
  · subst hC
    simp [Constitution.induced, variant, shirtAccess_empty]
  · have ha : variant.assign C = Set.univ := by
      ext r; simp [variant, Set.nonempty_iff_ne_empty, hC]
    rw [Constitution.induced, ha, variant_access_of_ne hC Set.univ_nonempty.ne_empty,
      if_pos rfl]

theorem variant_standing : variant.Standing where
  assign_empty := by ext r; simp [variant]
  access_empty_coalition θ := by simp [variant]
  access_empty_rights C := by simp [variant]

/-- **(3.5) holds**, unlike for the library's `offDiagonal`. -/
theorem variant_monotoneCoalitions : variant.MonotoneCoalitions := by
  intro S S' θ hSS' B hB
  by_cases hS : S = ∅
  · subst hS
    have hB' : B = Set.univ := by simpa [variant] using hB
    exact hB' ▸ univ_mem_variant_access S' θ
  have hS' : S' ≠ ∅ := fun h => hS (Set.subset_empty_iff.mp (h ▸ hSS'))
  by_cases hθ : θ = ∅
  · simpa [variant, hθ] using hB
  rw [variant_access_of_ne hS hθ] at hB
  rw [variant_access_of_ne hS' hθ]
  by_cases hθu : θ = Set.univ
  · rw [if_pos hθu] at hB ⊢
    exact shirtAccess_mono hSS' hB
  · rw [if_neg hθu] at hB ⊢
    exact hB

theorem variant_represented : Represents shirtGame variant := fun C => by
  rw [shirtGame, effectivity_shirtGameOf (fun _ => Function.surjective_id) C, variant_induced]

/-- Its induced `E` is an EF in print's sense, conditions (i)--(iv). -/
theorem variant_isEF : IsEffectivityFunction variant.induced where
  empty := (variant_induced _).trans shirtAccess_empty
  univ := (variant_represented _).symm.trans effectivity_shirtGame_univ
  live C := by
    rw [variant_induced]
    rintro ⟨f, hf⟩
    exact hf (a := (f false, f true)) (fun i _ => by cases i <;> rfl)
  safe C := (variant_induced C) ▸ univ_mem_shirtAccess C

/-- **(3.3) fails off the diagonal**, at `S = {1}`, `θ = {ρ₁}`. -/
theorem not_variant_monotoneAlternatives : ¬ variant.MonotoneAlternatives := by
  intro h
  have hne : ({false} : Set Bool) ≠ Set.univ := fun hu => by
    simpa using Set.eq_univ_iff_forall.mp hu true
  have hval := variant_access_of_ne (Set.singleton_ne_empty false) (Set.singleton_ne_empty false)
  rw [if_neg hne] at hval
  have hmem := h {false} {false} {(false, false)} {x | x.1 = false}
    (hval ▸ Or.inr rfl) (by simp)
  rw [hval, Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
  rcases hmem with hmem | hmem
  · simpa using Set.ext_iff.mp hmem (true, false)
  · simpa using Set.ext_iff.mp hmem (false, true)

/-- The library's `offDiagonal` witness breaks (3.5), which is why it does not
settle the printed direction under print's usual assumption. -/
theorem not_offDiagonal_monotoneCoalitions : ¬ offDiagonal.MonotoneCoalitions := by
  intro h
  have hne : ({false} : Set Bool) ≠ Set.univ := fun hu => by
    simpa using Set.eq_univ_iff_forall.mp hu true
  have hval : offDiagonal.access {false} {false} = {(∅ : Set Outfit)} := by
    show (if ({false} : Set Bool) = ∅ ∨ ({false} : Set Bool) = ∅ then _
      else if ({false} : Set Bool) = Set.univ then _ else _) = _
    rw [if_neg (by simp), if_neg hne]
  have hmem : (Set.univ : Set Outfit) ∈ offDiagonal.access ∅ {false} := by
    show Set.univ ∈ (if (∅ : Set Bool) = ∅ ∨ ({false} : Set Bool) = ∅ then _ else _)
    rw [if_pos (Or.inl rfl)]
    rfl
  have := h ∅ {false} {false} (Set.empty_subset _) hmem
  rw [hval, Set.mem_singleton_iff] at this
  exact Set.univ_nonempty.ne_empty this

/-- **The printed direction is false.** -/
theorem not_literalPrint : ¬ LiteralPrint := fun h =>
  not_variant_monotoneAlternatives
    (h Bool Outfit Bool variant variant_standing variant_monotoneCoalitions variant_isEF
      ⟨shirtGame, variant_represented⟩)

/-- **The repaired (i) holds on the same society**: it is represented, and its `E`
is monotonic w.r.t. the alternatives and superadditive, print's Theorem 3.5* (3.8). -/
theorem repaired_holds :
    (∃ G : GameForm.{0, 0, 0} Bool Outfit, Represents G variant) ∧
      UpwardClosed variant.induced ∧ Superadditive variant.induced :=
  ⟨⟨shirtGame, variant_represented⟩, variant_represented.upwardClosed,
    variant_represented.superadditive⟩

end PelegTheoremThreeFiveLiteral
