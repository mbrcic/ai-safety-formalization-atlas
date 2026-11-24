import AISafetyAtlas.Sovereignty.ConcurrentGameFrame

/-!
Chen, Ju and Ågotnes (2026), arXiv:2607.10567v1, Definition 8, pp. 9-10. An
action frame is a general concurrent game frame if (GCI) for every coalition
`C`, state `s` and `σ_C ∈ JA_C`, `out_C(s, σ_C)` is the union of
`out_AG(s, σ_AG)` over the `σ_AG` with `σ_AG|_C = σ_C`, and (ODA) for every
`C` and `s`, `av_C(s) = {σ_C | out_C(s, σ_C) ≠ ∅}`. Agents form a finite
nonempty set (§2.1), states and actions nonempty sets (Definition 1). The
cited definition is `AISafetyAtlas.Sovereignty.IsGCGF`; the cited lemmas
`mem_out_iff`, `mem_av_iff`, `gameFrame_isGCGF`, `ofGrand_out_univ` and
`ofGrand_isGCGF` are consequences and are not transferred.

The map has one agent. Its states are an optional copy of the original
states together with a tag `(C, s, σ)` for every original coalition, state
and joint action of that coalition. Its actions are optional codes of
original grand joint actions (`none` keeps the action set nonempty). At the
tag `(C, s, σ)` the grand action with code `σ'` has the copied outcome
`out_AG(s, σ')` when `σ'|_C = σ`, and no outcome otherwise; the empty
coalition there has the copied outcome `out_C(s, σ)`, and its empty joint
action is available exactly when `σ ∈ av_C(s)`. The grand coalition's
availability is defined by ODA. Every other state has no outcome and nothing
available. Print's GCI for the empty coalition at the tag `(C, s, σ)` is the
original GCI at `(C, s, σ)`, and print's ODA there is the original ODA at
`σ`; the conditions at the grand coalition hold by construction.

The forward direction is the identity: print's restriction `σ_AG|_C` is
`restrictJA` definitionally.

Checked: `lake env lean docs/provenance/transfers/157-general-concurrent-game-frame.lean`
-/

namespace Transfer157

open AISafetyAtlas.Sovereignty Classical

/-- Print's GCI and ODA conditions at a printed action frame. -/
def PrintStatement {AG ST AC : Type*} [Finite AG] [Nonempty AG] [Nonempty ST] [Nonempty AC]
    (F : ActionFrame AG ST AC) : Prop :=
  (∀ (C : Set AG) (s : ST) (σ : C → AC), F.out C s σ =
    ⋃ σ' ∈ {σ' : ↥(Set.univ : Set AG) → AC | (fun i : C ↦ σ' ⟨i.1, Set.mem_univ _⟩) = σ},
      F.out Set.univ s σ') ∧
  ∀ (C : Set AG) (s : ST), F.av C s = {σ | (F.out C s σ).Nonempty}

def LeanStatement {AG ST AC : Type*} (F : ActionFrame AG ST AC) : Prop := IsGCGF F

section

variable {AG ST AC : Type*}

abbrev Tag (AG ST AC : Type*) : Type _ := Σ C : Set AG, ST × (C → AC)
abbrev St (AG ST AC : Type*) : Type _ := Option (ST ⊕ Tag AG ST AC)
abbrev Act (AG AC : Type*) : Type _ := Option (↥(Set.univ : Set AG) → AC)

def emb (x : ST) : St AG ST AC := some (Sum.inl x)

theorem emb_injective : Function.Injective (emb (AG := AG) (ST := ST) (AC := AC)) := by
  intro x y h; simpa [emb] using h

def tag (C : Set AG) (s : ST) (σ : C → AC) : St AG ST AC := some (Sum.inr ⟨C, s, σ⟩)

noncomputable def grandOut (F : ActionFrame AG ST AC) : St AG ST AC → Act AG AC → Set (St AG ST AC)
  | some (Sum.inr ⟨C, s, σ⟩), some σ' =>
      if restrictJA (Set.subset_univ C) σ' = σ then emb '' F.out Set.univ s σ' else ∅
  | _, _ => ∅

def emptyOut (F : ActionFrame AG ST AC) : St AG ST AC → Set (St AG ST AC)
  | some (Sum.inr ⟨C, s, σ⟩) => emb '' F.out C s σ
  | _ => ∅

def emptyAv (F : ActionFrame AG ST AC) : St AG ST AC → Prop
  | some (Sum.inr ⟨C, s, σ⟩) => σ ∈ F.av C s
  | _ => False

/-- The map. -/
noncomputable def phi (F : ActionFrame AG ST AC) : ActionFrame Unit (St AG ST AC) (Act AG AC) where
  av C' t := if h : () ∈ C' then {a | (grandOut F t (a ⟨(), h⟩)).Nonempty} else {_a | emptyAv F t}
  out C' t a := if h : () ∈ C' then grandOut F t (a ⟨(), h⟩) else emptyOut F t

theorem restrict_univ {C' : Set Unit} (h : () ∈ C') (σ' : ↥(Set.univ : Set Unit) → Act AG AC)
    (a : C' → Act AG AC) :
    (fun i : C' ↦ σ' ⟨i.1, Set.mem_univ _⟩) = a ↔ σ' ⟨(), trivial⟩ = a ⟨(), h⟩ :=
  ⟨fun e ↦ congrFun e ⟨(), h⟩, fun e ↦ funext fun i ↦ by cases i; exact e⟩

theorem restrict_empty {C' : Set Unit} (h : () ∉ C') (σ' : ↥(Set.univ : Set Unit) → Act AG AC)
    (a : C' → Act AG AC) : (fun i : C' ↦ σ' ⟨i.1, Set.mem_univ _⟩) = a :=
  funext fun i ↦ by obtain ⟨⟨⟩, hi⟩ := i; exact (h hi).elim

/-- Print's GCI for the empty coalition at a state of the map, unfolded. -/
theorem gci_tag (F : ActionFrame AG ST AC) (t : St AG ST AC) :
    emptyOut F t = ⋃ b, grandOut F t b ↔
      ∀ C s σ, t = tag C s σ → F.out C s σ =
        ⋃ σ' ∈ {σ' | restrictJA (Set.subset_univ C) σ' = σ}, F.out Set.univ s σ' := by
  rcases t with _ | x | ⟨C, s, σ⟩
  · simp [emptyOut, grandOut, tag]
  · simp [emptyOut, grandOut, tag]
  · have hR : (⋃ b, grandOut F (some (Sum.inr ⟨C, s, σ⟩)) b) =
        emb '' ⋃ σ' ∈ {σ' | restrictJA (Set.subset_univ C) σ' = σ}, F.out Set.univ s σ' := by
      ext y
      simp only [Set.mem_iUnion, Set.mem_image, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨_ | σ', hy⟩
        · simp [grandOut] at hy
        · simp only [grandOut] at hy
          split_ifs at hy with he
          · obtain ⟨z, hz, rfl⟩ := hy; exact ⟨z, ⟨σ', he, hz⟩, rfl⟩
          · exact hy.elim
      · rintro ⟨z, ⟨σ', he, hz⟩, rfl⟩
        exact ⟨some σ', by simp only [grandOut, if_pos he]; exact ⟨z, hz, rfl⟩⟩
    change emb '' F.out C s σ = _ ↔ _
    rw [hR, (emb_injective.image_injective).eq_iff]
    constructor
    · rintro h C' s' σ' ht; simp only [tag, Option.some.injEq, Sum.inr.injEq] at ht
      obtain ⟨rfl, ht⟩ := Sigma.mk.inj_iff.mp ht
      simp only [heq_eq_eq, Prod.mk.injEq] at ht; obtain ⟨rfl, rfl⟩ := ht; exact h
    · intro h; exact h C s σ rfl

theorem defining_condition (F : ActionFrame AG ST AC) :
    LeanStatement F ↔ PrintStatement (phi F) := by
  have hU : ∀ (C' : Set Unit) (h : () ∉ C') t (a : C' → Act AG AC),
      (⋃ σ' ∈ {σ' : ↥(Set.univ : Set Unit) → Act AG AC |
        (fun i : C' ↦ σ' ⟨i.1, Set.mem_univ _⟩) = a}, (phi F).out Set.univ t σ') =
        ⋃ b, grandOut F t b := by
    intro C' h t a; ext y
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq, phi, dif_pos (Set.mem_univ ()), exists_prop]
    exact ⟨fun ⟨σ', _, hy⟩ ↦ ⟨_, hy⟩, fun ⟨b, hy⟩ ↦ ⟨fun _ ↦ b, restrict_empty h (fun _ ↦ b) a, hy⟩⟩
  constructor
  · rintro ⟨gci, oda⟩
    refine ⟨fun C' t a ↦ ?_, fun C' t ↦ ?_⟩
    · by_cases h : () ∈ C'
      · ext y; simp only [Set.mem_iUnion, Set.mem_ofPred_eq, restrict_univ h, phi, dif_pos h,
          dif_pos (Set.mem_univ ()), exists_prop]
        exact ⟨fun hy ↦ ⟨fun _ ↦ a ⟨(), h⟩, rfl, hy⟩, fun ⟨σ', he, hy⟩ ↦ he ▸ hy⟩
      · rw [hU C' h t a]; simp only [phi, dif_neg h]
        exact (gci_tag F t).mpr fun C s σ _ ↦ gci C s σ
    · by_cases h : () ∈ C'
      · ext a; simp [phi, dif_pos h]
      · ext a; simp only [phi, dif_neg h, Set.mem_ofPred_eq]
        rcases t with _ | x | ⟨C, s, σ⟩
        · simp [emptyAv, emptyOut]
        · simp [emptyAv, emptyOut]
        · simp only [emptyAv, emptyOut, Set.image_nonempty]
          rw [oda C s]; rfl
  · rintro ⟨gci, oda⟩
    have e : () ∉ (∅ : Set Unit) := id
    let a0 : (∅ : Set Unit) → Act AG AC := fun i ↦ (e i.2).elim
    refine ⟨fun C s σ ↦ ?_, fun C s ↦ ?_⟩
    · have h := gci ∅ (tag C s σ) a0
      rw [hU ∅ e _ a0] at h; simp only [phi, dif_neg e] at h
      exact (gci_tag F _).mp h C s σ rfl
    · ext σ
      have h := congrArg (a0 ∈ ·) (oda ∅ (tag C s σ))
      simpa [phi, emptyAv, emptyOut, tag] using h

theorem lean_of_print (F : ActionFrame AG ST AC) : PrintStatement (phi F) → LeanStatement F :=
  (defining_condition F).mpr

theorem print_of_lean [Finite AG] [Nonempty AG] [Nonempty ST] [Nonempty AC]
    (F : ActionFrame AG ST AC) : LeanStatement F → PrintStatement F :=
  fun h ↦ ⟨h.gci, h.oda⟩

end

end Transfer157
