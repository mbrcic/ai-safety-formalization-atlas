module

public import Mathlib.Combinatorics.SetFamily.KruskalKatona
public import Mathlib.Data.Fintype.EquivFin

/-!
# Kruskal-Katona over an arbitrary ground type

Mathlib proves the Kruskal-Katona theorem for families of subsets of `Fin n`, and
records as an open task that the statement should not need that. This module does
the transport for the Lovasz form, which is the form a consumer usually wants: a
family of `r`-sets large enough to contain a full `k`-set's worth of `r`-subsets
has a shadow at least as large as that `k`-set's own.

The ground type here is arbitrary. What replaces `Fin n` is a finite `s` that
contains every member of the family, and `n` becomes `s.card`. The proof carries
the family back along an embedding `Fin s.card` into `s`, applies the Mathlib
statement there, and pushes the iterated shadow forward again; pushing forward is
a subset rather than an equality, which is all a lower bound on the shadow needs.

Read contrapositively the bound is a ceiling: a family whose low-order shadow is
small cannot itself be large at a higher order. That is the direction a counting
argument over a downward-closed family wants, and it needs no randomisation null
to justify it. No module in this repository consumes it yet; it is here as the
domain-neutral form of a statement the library would otherwise restate locally.

Source and scope: the mathematical content is Mathlib's
`Finset.kruskal_katona_lovasz_form`. This module contributes only the change of
ground type, which that file lists under its own `TODO`.
-/

namespace AISafetyAtlas.Combinatorics

open Finset
open scoped FinsetFamily

variable {α : Type*} [DecidableEq α]

omit [DecidableEq α] in
/--
A finite set is the range of an embedding out of `Fin` of its cardinality. This
is `Finset.equivFin` packaged so that the ground type of a set family can be
changed without mentioning the subtype.
-/
public theorem exists_embedding_range_eq (s : Finset α) :
    ∃ f : Fin s.card ↪ α, ∀ a, a ∈ s ↔ ∃ i, f i = a := by
  refine ⟨(s.equivFin.symm.toEmbedding).trans (Function.Embedding.subtype _), fun a => ?_⟩
  constructor
  · exact fun ha => ⟨s.equivFin ⟨a, ha⟩, by simp⟩
  · rintro ⟨i, rfl⟩
    exact (s.equivFin.symm i).2

/--
**The Lovasz form of Kruskal-Katona, over an arbitrary ground type.**

If every member of `𝒜` is an `r`-subset of a finite `s`, and `𝒜` is at least as
large as the family of all `r`-subsets of a `k`-element set, then the `i`-th
iterated shadow of `𝒜` is at least as large as the family of all `(r - i)`-subsets
of that `k`-element set.

Read contrapositively this is a ceiling: a family whose `(r - i)`-shadow is small
cannot itself be large. That is the direction a coverage argument uses, because
it turns a measured low-order count into a bound on the high-order count that no
randomisation null is needed to justify.
-/
public theorem choose_le_card_shadow_iterate
    {𝒜 : Finset (Finset α)} {s : Finset α} {r i k : ℕ}
    (hsub : ∀ A ∈ 𝒜, A ⊆ s) (hsized : (𝒜 : Set (Finset α)).Sized r)
    (hir : i ≤ r) (hrk : r ≤ k) (hks : k ≤ s.card) (hcard : k.choose r ≤ 𝒜.card) :
    k.choose (r - i) ≤ (∂^[i] 𝒜).card := by
  classical
  obtain ⟨f, hf⟩ := exists_embedding_range_eq s
  set B : Finset α → Finset (Fin s.card) := fun A => Finset.univ.filter (fun j => f j ∈ A) with hBdef
  have hBmap : ∀ A ∈ 𝒜, (B A).map f = A := by
    intro A hA
    ext a
    simp only [hBdef, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨j, hj, rfl⟩
      exact hj
    · intro ha
      obtain ⟨j, rfl⟩ := (hf a).mp (hsub A hA ha)
      exact ⟨j, ha, rfl⟩
  have hinj : Set.InjOn B 𝒜 := by
    intro A hA A' hA' h
    rw [← hBmap A hA, ← hBmap A' hA', h]
  have hcardB : (𝒜.image B).card = 𝒜.card := Finset.card_image_of_injOn hinj
  have hsizedB : ((𝒜.image B : Finset (Finset (Fin s.card))) : Set (Finset (Fin s.card))).Sized r := by
    intro C hC
    simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hC
    obtain ⟨A, hA, rfl⟩ := hC
    have hmapA : ((B A).map f).card = A.card := by rw [hBmap A hA]
    rw [← Finset.card_map f, hmapA]
    exact hsized hA
  have hshadow :
      ((∂^[i] (𝒜.image B)).map ⟨Finset.map f, Finset.map_injective f⟩) ⊆ ∂^[i] 𝒜 := by
    intro T hT
    rw [Finset.mem_map] at hT
    obtain ⟨T₀, hT₀, rfl⟩ := hT
    rw [Finset.mem_shadow_iterate_iff_exists_sdiff] at hT₀ ⊢
    obtain ⟨S, hS, hTS, hcard'⟩ := hT₀
    obtain ⟨A, hA, rfl⟩ := Finset.mem_image.mp hS
    refine ⟨A, hA, ?_, ?_⟩
    · rw [← hBmap A hA]
      exact Finset.map_subset_map.mpr hTS
    · rw [← hBmap A hA]
      show (Finset.map f (B A) \ Finset.map f T₀).card = i
      rw [← Finset.map_sdiff, Finset.card_map]
      exact hcard'
  have hle : (∂^[i] (𝒜.image B)).card ≤ (∂^[i] 𝒜).card := by
    have h := Finset.card_le_card hshadow
    rwa [Finset.card_map] at h
  refine le_trans ?_ hle
  exact Finset.kruskal_katona_lovasz_form hir hrk hks hsizedB (by rw [hcardB]; exact hcard)

end AISafetyAtlas.Combinatorics
