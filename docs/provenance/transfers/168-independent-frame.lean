import AISafetyAtlas.Sovereignty.ConcurrentGameFrame

/-!
Chen, Ju and Ågotnes (2026), arXiv:2607.10567v1, Definition 9, second
bullet, p. 10. A general concurrent game frame is independent if, for all
states `s` and all disjoint coalitions `C`, `D`, whenever
`σ_C ∈ av_C(s)` and `σ_D ∈ av_D(s)`, `σ_C ∪ σ_D ∈ av_{C ∪ D}(s)`. Print's
frames are general concurrent game frames (Definition 8) over a finite
nonempty agent set, with nonempty state and action sets. The cited definition
is `AISafetyAtlas.Sovereignty.Independent`; the cited lemmas
`gameFrame_independent`, `clashFrame_not_independent` and
`exists_gcgf_not_superadditive` are consequences and are not transferred.

The map has two agents, `false` and `true`. Its states are optional tags
`(C, D, s)` for every disjoint pair of original coalitions and original
state. Its actions are optional tagged original joint actions
`⟨E, σ_E⟩`. At the tag `(C, D, s)` a grand action, a pair `(a, b)`, is
enabled when `a` is `none` or `⟨C, σ_C⟩` with `σ_C ∈ av_C(s)`, `b` is `none`
or `⟨D, σ_D⟩` with `σ_D ∈ av_D(s)`, and, when both are tagged, the union
`σ_C ∪ σ_D` is in `av_{C ∪ D}(s)`. An enabled pair loops back to its state;
every other pair, and every action at `none`, has no outcome. The frame is
`ActionFrame.ofGrand` of this grand outcome table, a general concurrent game
frame by `ofGrand_isGCGF`. Print's independence at the tag `(C, D, s)`, for
the coalitions `{false}` and `{true}`, is the original independence at
`(s, C, D)`. Conversely, under the original independence the union clause
follows from the two availability clauses, so availability at the map is
closed under any joint union.

Print's GCGF condition is stated with `IsGCGF` at print's finite instances
(row 157 transfers it). The forward direction is the identity.

Checked: `lake env lean docs/provenance/transfers/168-independent-frame.lean`
-/

namespace Transfer168

open AISafetyAtlas.Sovereignty

/-- Print's independence at a printed general concurrent game frame. -/
def PrintStatement {AG ST AC : Type*} [Finite AG] [Nonempty AG] [Nonempty ST] [Nonempty AC]
    (F : ActionFrame AG ST AC) (_gcgf : IsGCGF F) : Prop :=
  ∀ (s : ST) (C D : Set AG), Disjoint C D →
    ∀ σC ∈ F.av C s, ∀ σD ∈ F.av D s, jointUnion σC σD ∈ F.av (C ∪ D) s

def LeanStatement {AG ST AC : Type*} (F : ActionFrame AG ST AC) : Prop := Independent F

section

variable {AG ST AC : Type*}

abbrev Tag (AG ST : Type*) : Type _ := {p : Set AG × Set AG × ST // Disjoint p.1 p.2.1}
abbrev St (AG ST : Type*) : Type _ := Option (Tag AG ST)
abbrev Act (AG AC : Type*) : Type _ := Option (Σ E : Set AG, E → AC)

def ok (F : ActionFrame AG ST AC) (C : Set AG) (s : ST) (a : Act AG AC) : Prop :=
  a = none ∨ ∃ σ ∈ F.av C s, a = some ⟨C, σ⟩

def En (F : ActionFrame AG ST AC) (C D : Set AG) (s : ST) (a b : Act AG AC) : Prop :=
  ok F C s a ∧ ok F D s b ∧
    ∀ σC σD, a = some ⟨C, σC⟩ → b = some ⟨D, σD⟩ → jointUnion σC σD ∈ F.av (C ∪ D) s

def agt (b : Bool) : ↥(Set.univ : Set Bool) := ⟨b, Set.mem_univ _⟩

/-- The grand outcome table of the map. -/
def grand (F : ActionFrame AG ST AC) :
    St AG ST → (↥(Set.univ : Set Bool) → Act AG AC) → Set (St AG ST)
  | some p, τ => {x | x = some p ∧ En F p.1.1 p.1.2.1 p.1.2.2 (τ (agt false)) (τ (agt true))}
  | none, _ => ∅

/-- The map. -/
def phi (F : ActionFrame AG ST AC) : ActionFrame Bool (St AG ST) (Act AG AC) :=
  ActionFrame.ofGrand (grand F)

theorem phi_isGCGF (F : ActionFrame AG ST AC) : IsGCGF (phi F) := ofGrand_isGCGF (grand F)

theorem some_inj {C : Set AG} {σ σ' : C → AC}
    (h : (some ⟨C, σ⟩ : Act AG AC) = some ⟨C, σ'⟩) : σ = σ' := by
  simpa using h

theorem av_tag (F : ActionFrame AG ST AC) (p : Tag AG ST) (C' : Set Bool) (σ : C' → Act AG AC) :
    σ ∈ (phi F).av C' (some p) ↔ ∃ τ, restrictJA (Set.subset_univ C') τ = σ ∧
      En F p.1.1 p.1.2.1 p.1.2.2 (τ (agt false)) (τ (agt true)) := by
  change (∃ x τ, _ ∧ x ∈ grand F (some p) τ) ↔ _
  simp only [grand, Set.mem_ofPred_eq]
  exact ⟨fun ⟨_, τ, r, _, e⟩ ↦ ⟨τ, r, e⟩, fun ⟨τ, r, e⟩ ↦ ⟨_, τ, r, rfl, e⟩⟩

theorem lean_of_print (F : ActionFrame AG ST AC) :
    PrintStatement (phi F) (phi_isGCGF F) → LeanStatement F := by
  classical
  intro hp s C D hCD σC hC σD hD
  let p : Tag AG ST := ⟨(C, D, s), hCD⟩
  let τ : Act AG AC → Act AG AC → ↥(Set.univ : Set Bool) → Act AG AC :=
    fun a b i ↦ if i.1 then b else a
  have h1 : (fun _ ↦ some ⟨C, σC⟩ : ({false} : Set Bool) → Act AG AC) ∈ (phi F).av {false} (some p) :=
    (av_tag F p _ _).mpr ⟨τ (some ⟨C, σC⟩) none, funext fun ⟨i, hi⟩ ↦ by
      obtain rfl := Set.mem_singleton_iff.mp hi; rfl,
      Or.inr ⟨σC, hC, rfl⟩, Or.inl rfl, fun _ _ _ h ↦ by simp [τ, agt] at h⟩
  have h2 : (fun _ ↦ some ⟨D, σD⟩ : ({true} : Set Bool) → Act AG AC) ∈ (phi F).av {true} (some p) :=
    (av_tag F p _ _).mpr ⟨τ none (some ⟨D, σD⟩), funext fun ⟨i, hi⟩ ↦ by
      obtain rfl := Set.mem_singleton_iff.mp hi; rfl,
      Or.inl rfl, Or.inr ⟨σD, hD, rfl⟩, fun _ _ h _ ↦ by simp [τ, agt] at h⟩
  obtain ⟨τ', hτ, -, -, hj⟩ := (av_tag F p _ _).mp
    (hp (some p) {false} {true} (by simp) _ h1 _ h2)
  have e1 := congrFun hτ ⟨false, Or.inl rfl⟩
  have e2 := congrFun hτ ⟨true, Or.inr rfl⟩
  simp only [restrictJA, jointUnion, Set.mem_singleton_iff] at e1 e2
  simp only [Bool.true_eq_false, dite_false, dite_true] at e1 e2
  exact hj σC σD e1 e2

theorem print_of_lean_at_phi (F : ActionFrame AG ST AC) :
    LeanStatement F → PrintStatement (phi F) (phi_isGCGF F) := by
  classical
  intro hl t C' D' hCD σ1 h1 σ2 h2
  rcases t with _ | p
  · obtain ⟨_, _, _, hx⟩ := h1; exact hx.elim
  obtain ⟨τ1, r1, o1, o1', -⟩ := (av_tag F p _ _).mp h1
  obtain ⟨τ2, r2, o2, o2', -⟩ := (av_tag F p _ _).mp h2
  let τ : ↥(Set.univ : Set Bool) → Act AG AC :=
    fun i ↦ if i.1 ∈ C' then τ1 i else if i.1 ∈ D' then τ2 i else none
  have hok : ∀ (E : Set AG) (a b : Act AG AC), ok F E p.1.2.2 a → ok F E p.1.2.2 b →
      ∀ v, (v = a ∨ v = b ∨ v = none) → ok F E p.1.2.2 v := by
    rintro E a b ha hb v (rfl | rfl | rfl)
    exacts [ha, hb, Or.inl rfl]
  have hv : ∀ i, τ i = τ1 i ∨ τ i = τ2 i ∨ τ i = none := by
    intro i; simp only [τ]; split_ifs <;> simp
  have okC := hok _ _ _ o1 o2 _ (hv (agt false))
  have okD := hok _ _ _ o1' o2' _ (hv (agt true))
  refine (av_tag F p _ _).mpr ⟨τ, funext fun i ↦ ?_, okC, okD, fun σC σD ha hb ↦ ?_⟩
  · rcases i with ⟨i, hi⟩
    simp only [restrictJA, jointUnion, τ]
    by_cases hc : i ∈ C'
    · rw [dif_pos hc, if_pos hc, ← r1]; rfl
    · rw [dif_neg hc, if_neg hc, if_pos (hi.resolve_left hc), ← r2]; rfl
  · rcases okC with h | ⟨σ, hσ, e⟩
    · rw [h] at ha; cases ha
    rcases okD with h | ⟨σ', hσ', e'⟩
    · rw [h] at hb; cases hb
    rw [ha] at e; rw [hb] at e'
    rw [some_inj e, some_inj e']
    exact hl _ _ _ p.2 σ hσ σ' hσ'

theorem defining_condition (F : ActionFrame AG ST AC) :
    LeanStatement F ↔ PrintStatement (phi F) (phi_isGCGF F) :=
  ⟨print_of_lean_at_phi F, lean_of_print F⟩

theorem print_of_lean [Finite AG] [Nonempty AG] [Nonempty ST] [Nonempty AC]
    (F : ActionFrame AG ST AC) (hF : IsGCGF F) : LeanStatement F → PrintStatement F hF :=
  fun h ↦ h

end

end Transfer168
