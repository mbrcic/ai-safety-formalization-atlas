import AISafetyAtlas.Examples.Sovereignty.Rights

/-!
# Peleg Example 3.6 on Example 2.3's printed γ is false; on its upward closure it holds

Bezalel Peleg, *Effectivity functions, game forms, games, and rights*, Soc Choice
Welfare 15 (1998) 67--80. Example 2.3, p. 69 (audit row S21-R05), defines the
two-shirt society, with `w` white, `b` blue and `(x, y)` the shirts of members 1
and 2, by

    γ(S, ∅) = A for all S ⊂ N, γ(∅, ρ₁) = A,
    γ(1, ρ₁) = {{(w, w), (w, b)}, {(b, w), (b, b)}},
    γ(2, ρ₁) = {{(w, w), (b, w)}, {(w, b), (b, b)}}, and γ(N, ρ₁, ) = 2^A \ {∅},

and Example 3.6, pp. 73--74 (audit row S21-R24), claims:

    (3.1) yields the following EF E: E(∅) = A and E(S) = γ(S, ρ₁) for S ≠ ∅.
    [...] Then the GF Γ = ⟨N; {ŵ, b̂}, {ŵ, b̂}; g; A⟩, where g is given by
    g(x̂¹, x̂²) = (x¹, x²) for all x¹, x² ∈ {w, b}, is a representation of E.

(Transcribed from the page images in
`docs/provenance/printed-statements/peleg-1998-effectivity-functions.yaml`, entries
`peleg-examples-2` and `peleg-examples-3`; `A` for `{A}` is print's singleton
convention, stated in Example 2.3 itself.)

Read literally, with `γ(1, ρ₁)` exactly the two listed sets, Example 3.6 is false.
The failure is at coalition `{1}`: member 1 forces the whole outcome space `A` in
`Γ` (by either strategy), but `A` is not one of the two listed sets, so
`E_α(1; Γ) ≠ E(1)`. The same omission makes the literal `E` fail print's own EF
condition (iv), `A ∈ E(S)`, although Example 3.6 calls it an EF
(`univ_not_mem_literal`). This file
proves the failure for print's game form `Γ` (`shirtGame`) from the library's
`not_represents_of_induced_eq_listed`, which in fact rules out every game form.

The repair closes the listed families upwards at members 1 and 2 (the library's
`shirtConstitution`, built on `shirtAccess`); print's values at `∅` and `N` are
already closed and are unchanged. Why this is the necessary repair:

* it is the only value of `γ(1, ρ₁)` making Example 3.6 true: any constitution
  that `Γ` represents has `E(1) = E_α(1; Γ)`, which is the upward closure
  (`closure_forced`); member 2 is symmetric (not proved here);
* the smallest patch, adding only `A` to the two listed sets (which would mend
  condition (iv)), still fails: the closure also contains
  `{(w, w), (w, b), (b, b)}`, which that patch omits (`closure_ne_listed_add_univ`);
* print supplies the reading itself: Remark 2.2 (p. 69) says each listed `B_k` is
  attainable "separately", and Example 2.10 (p. 71) writes its families as upward
  closures `B⁺`.

Supplementary, not library: nothing imports this file. CI checks it with
`lake env lean docs/provenance/refutations/peleg-ex-2-3-literal.lean`. Grading
context: `docs/provenance/regrade-2026-11/RULINGS-PENDING.md` (ruling on repaired slips).
-/

open AISafetyAtlas.Sovereignty AISafetyAtlas.Examples.Sovereignty

namespace PelegExampleTwoThreeLiteral

/-- Print's `γ(1, ρ₁)`, the two listed sets, with `w = false` and `b = true`. -/
def printedGammaOne : Set (Set Outfit) :=
  {{(false, false), (false, true)}, {(true, false), (true, true)}}

/-- Print's `γ(2, ρ₁)`. -/
def printedGammaTwo : Set (Set Outfit) :=
  {{(false, false), (true, false)}, {(false, true), (true, true)}}

open Classical in
/-- Print's `γ(S, ρ₁)` at the four coalitions: `A` (the family `{A}`) at `∅`, the
two listed families at members 1 (`false`) and 2 (`true`), `2^A \ {∅}` at `N`. -/
noncomputable def printedGamma (C : Set Bool) : Set (Set Outfit) :=
  if C = ∅ then {Set.univ}
  else if C = {false} then printedGammaOne
  else if C = {true} then printedGammaTwo
  else {B | B.Nonempty}

/-- **Example 2.3 exactly as printed**: `α(∅) = ∅`, `α(1) = α(2) = α(N) = ρ₁`,
`γ(S, ∅) = A`, and `γ(S, ρ₁)` as listed. -/
noncomputable def printedShirt : Constitution Bool Outfit Unit where
  assign := fun C => {_r | C.Nonempty}
  access := fun C θ => {B | () ∈ θ ∧ B ∈ printedGamma C ∨ () ∉ θ ∧ B = Set.univ}

/-- **Example 3.6 exactly as printed**: the simultaneous game form `Γ` represents
the EF that (3.1) derives from Example 2.3's printed `γ`. -/
def LiteralPrint : Prop :=
  Represents shirtGame printedShirt

/-- The two listed sets are the library's `listedAccess {false}`: the outfits
member 1 pins down by fixing a shirt, with no supersets. -/
theorem printedGammaOne_eq : printedGammaOne = listedAccess {false} := by
  ext B
  simp only [printedGammaOne, listedAccess, Set.mem_insert_iff, Set.mem_singleton_iff,
    Set.mem_ofPred_eq]
  constructor
  · rintro (rfl | rfl)
    · refine ⟨fun _ => false, ?_⟩
      ext ⟨a, b⟩; cases a <;> cases b <;> simp [worn]
    · refine ⟨fun _ => true, ?_⟩
      ext ⟨a, b⟩; cases a <;> cases b <;> simp [worn]
  · rintro ⟨f, rfl⟩
    cases h : f false
    · left; ext ⟨a, b⟩; cases a <;> cases b <;> simp [worn, h]
    · right; ext ⟨a, b⟩; cases a <;> cases b <;> simp [worn, h]

/-- The literal EF at member 1 is the listing. -/
theorem printedShirt_induced_one : printedShirt.induced {false} = listedAccess {false} := by
  rw [← printedGammaOne_eq]
  ext B
  simp [Constitution.induced, printedShirt, printedGamma]

/-- The literal `E` is not an EF: it fails condition (iv) at member 1. -/
theorem univ_not_mem_literal : Set.univ ∉ printedShirt.induced {false} := by
  rw [printedShirt_induced_one]
  rintro ⟨f, hf⟩
  have hmem : ((!f false, f true) : Outfit) ∈ (Set.univ : Set Outfit) := Set.mem_univ _
  rw [hf] at hmem
  exact Bool.not_ne_self _ (hmem false rfl)

/-- **The printed example is false.** At coalition `{1}`, `Γ`'s effectivity family
is closed upwards and the listing is not. -/
theorem not_literalPrint : ¬ LiteralPrint :=
  not_represents_of_induced_eq_listed shirtGame printedShirt printedShirt_induced_one

/-- **The repaired example holds**: with `γ(1, ρ₁)` and `γ(2, ρ₁)` closed upwards,
`Γ` represents the society, which at `N` is print's `2^A \ {∅}` and at `∅` is
print's `{A}`. -/
theorem repaired_holds :
    Represents shirtGame shirtConstitution ∧
      shirtConstitution.induced Set.univ = {B : Set Outfit | B.Nonempty} ∧
      shirtConstitution.induced ∅ = {Set.univ} :=
  ⟨represents_shirtGame, (represents_shirtGame _).symm.trans effectivity_shirtGame_univ,
    shirtConstitution_induced_empty⟩

/-- **The closure is forced**: any constitution `Γ` represents has the upward
closure at member 1. -/
theorem closure_forced {R : Type} (κ : Constitution Bool Outfit R)
    (h : Represents shirtGame κ) : κ.induced {false} = shirtAccess {false} :=
  (h {false}).symm.trans (effectivity_shirtGameOf (fun _ => Function.surjective_id) {false})

/-- **Adding only `A` to the listing is not enough**: the closure contains
`{(w, w), (w, b), (b, b)}`, which neither listed set nor `A` is. -/
theorem closure_ne_listed_add_univ :
    shirtAccess {false} ≠ insert Set.univ printedGammaOne := by
  intro h
  have hW : ({(false, false), (false, true), (true, true)} : Set Outfit) ∈ shirtAccess {false} :=
    ⟨fun _ => false, by
      rintro ⟨a, b⟩ hx
      have ha : a = false := hx false rfl
      subst ha; cases b <;> simp⟩
  rw [h] at hW
  simp only [printedGammaOne, Set.mem_insert_iff, Set.mem_singleton_iff, Set.ext_iff] at hW
  rcases hW with hW | hW | hW
  · simpa using hW (true, false)
  · simpa using hW (true, true)
  · simpa using hW (false, false)

end PelegExampleTwoThreeLiteral
