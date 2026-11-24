import AISafetyAtlas.Knowledge.Embedded

/-!
Breuer (1995), §3.5, unnumbered Lemma, p. 208. Under meshing, the states
inferred from a singleton reading are exactly those inferred from the
full apparatus space that restrict to that reading. The cited theorem is
`infer_singleton_eq_of_meshing`.

The map adds a Boolean rest to each global state, then pulls restriction and
inference back along the first projection. This gives distinct global states
with the same reading, as required under the proper-inclusion reading of §3.3.

Checked: `lake env lean docs/provenance/transfers/292-breuer-meshing.lean`
-/

namespace Transfer292

open AISafetyAtlas.Knowledge.Embedded

universe u v

def PrintHyp {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) : Prop :=
  Function.Surjective restrict ∧ ProperInclusion restrict ∧ Meshing restrict M

def PrintConcl {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) : Prop :=
  ∀ a : A, M.infer (ReadingSet.singleton a) =
    {s | s ∈ M.infer (@ReadingSet.univ A ⟨a⟩) ∧ restrict s = a}

def PrintStatement : Prop :=
  ∀ (Ω : Type u) (A : Type v) (restrict : Restriction Ω A) (M : InferenceMap Ω A),
    PrintHyp restrict M → PrintConcl restrict M

def LeanStatement : Prop :=
  ∀ {Ω : Type u} {A : Type v} [Nonempty A] (restrict : Restriction Ω A)
      (M : InferenceMap Ω A),
    Meshing restrict M →
      ∀ a : A, M.infer (ReadingSet.singleton a) =
        {s | s ∈ M.infer ReadingSet.univ ∧ restrict s = a}

def phi {Ω : Type u} {A : Type v} (restrict : Restriction Ω A) (M : InferenceMap Ω A) :
    Restriction (Ω × Bool) A × InferenceMap (Ω × Bool) A :=
  ⟨restrict ∘ Prod.fst,
    { infer := fun U ↦ Prod.fst ⁻¹' M.infer U
      infer_eq_union_singletons := by
        intro U
        ext s
        change (s.1 ∈ M.infer U) ↔ ∃ a ∈ U.1, s.1 ∈ M.infer (ReadingSet.singleton a)
        rw [M.infer_eq_union_singletons U]
        rfl }⟩

theorem print_hyp {Ω : Type u} {A : Type v} [Nonempty A] (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hm : Meshing restrict M) :
    PrintHyp (phi restrict M).1 (phi restrict M).2 := by
  have hsurj := hm.restrict_surjective restrict M
  refine ⟨?_, ?_, ?_⟩
  · intro a
    obtain ⟨s, hs⟩ := hsurj a
    exact ⟨(s, false), hs⟩
  · obtain ⟨a⟩ := ‹Nonempty A›
    obtain ⟨s, _⟩ := hsurj a
    exact ⟨(s, false), (s, true), rfl, fun h ↦ Bool.noConfusion (congrArg Prod.snd h)⟩
  · intro a
    ext b
    change (∃ s : Ω × Bool, s.1 ∈ M.infer (ReadingSet.singleton a) ∧ restrict s.1 = b) ↔
      b ∈ ({a} : Set A)
    rw [← hm a]
    exact ⟨fun ⟨s, hs, hr⟩ ↦ ⟨s.1, hs, hr⟩,
      fun ⟨s, hs, hr⟩ ↦ ⟨(s, false), hs, hr⟩⟩

theorem lean_concl {Ω : Type u} {A : Type v} [Nonempty A] (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (h : PrintConcl (phi restrict M).1 (phi restrict M).2)
    (a : A) :
    M.infer (ReadingSet.singleton a) =
      {s | s ∈ M.infer ReadingSet.univ ∧ restrict s = a} := by
  ext s
  exact Set.ext_iff.mp (h a) (s, false)

theorem lean_of_print : PrintStatement.{u, v} → LeanStatement.{u, v} := by
  intro hp Ω A _ restrict M hm
  exact lean_concl restrict M
    (hp (Ω × Bool) A (phi restrict M).1 (phi restrict M).2 (print_hyp restrict M hm))

theorem print_of_lean : LeanStatement.{u, v} → PrintStatement.{u, v} := by
  intro h Ω A restrict M hPrint a
  exact @h Ω A ⟨a⟩ restrict M hPrint.2.2 a

end Transfer292
