import AISafetyAtlas.Sovereignty.ConcurrentGameFrame

/-!
Chen, Ju & Ågotnes (2026), Fact 1, item 1, p. 10. In a general concurrent game
frame, for every state, all coalitions `C ⊆ D ⊆ AG` and every joint action of
`D`, the outcome set of the joint action is contained in the outcome set of its
restriction to `C`. Print's agents are finite and nonempty, its states and
actions nonempty (§2.1, Definition 1). The cited declaration is
`AISafetyAtlas.Sovereignty.IsGCGF.out_anti_coalition`, at any agent type and
possibly empty state and action types.

The map builds one printed frame with three agents, standing for `C`, `D \ C`
and `AG \ D`, and keeps the state type (nonempty, since a state is given). An
action is a partial joint action of the Lean frame. A printed grand action
reads each Lean agent's action from the printed agent of its block; when every
lookup is defined, its outcome set is the Lean grand outcome set of the joint
action read off, and otherwise empty. The other coalitions' outcome and
availability functions are determined by `ActionFrame.ofGrand`. The queried
printed coalitions are `{0} ⊆ {0, 1}`, both agents playing the given joint
action of `D`. The Lean GCI-condition identifies the two printed outcome sets
with the Lean ones, so the printed inclusion gives the Lean inclusion.

Checked: `lake env lean docs/provenance/transfers/104-outcome-monotonicity.lean`
-/

namespace Transfer104

open AISafetyAtlas.Sovereignty Classical

universe u v w

def PrintStatement : Prop :=
  ∀ (AG : Type u) [Finite AG] [Nonempty AG] (ST : Type v) [Nonempty ST] (AC : Type w)
    [Nonempty AC] (F : ActionFrame AG ST AC), IsGCGF F →
    ∀ (s : ST) (C D : Set AG) (h : C ⊆ D) (σD : D → AC),
      F.out D s σD ⊆ F.out C s (restrictJA h σD)

def LeanStatement : Prop :=
  ∀ (AG : Type u) (ST : Type v) (AC : Type w) (F : ActionFrame AG ST AC), IsGCGF F →
    ∀ (C D : Set AG) (h : C ⊆ D) (s : ST) (σD : D → AC),
      F.out D s σD ⊆ F.out C s (restrictJA h σD)

variable {AG : Type u} {ST : Type v} {AC : Type w}

/-- The printed agent whose action a Lean agent reads. -/
noncomputable def block (C D : Set AG) (i : AG) : ↥(Set.univ : Set (Fin 3)) :=
  ⟨if i ∈ C then 0 else if i ∈ D then 1 else 2, trivial⟩

noncomputable def phi (F : ActionFrame AG ST AC) (C D : Set AG) :
    ActionFrame (Fin 3) ST (AG → Option AC) :=
  ActionFrame.ofGrand fun s τ => {x | ∃ σ : AG → AC,
    (∀ i, τ (block C D i) i = some (σ i)) ∧ x ∈ F.out Set.univ s (fun i => σ i.1)}

/-- The partial joint action that plays `σD` on `D`. -/
noncomputable def enc {D : Set AG} (σD : D → AC) : AG → Option AC :=
  fun i => if hi : i ∈ D then some (σD ⟨i, hi⟩) else none

def C' : Set (Fin 3) := {0}
def D' : Set (Fin 3) := {0, 1}
theorem hCD' : C' ⊆ D' := by intro k hk; simp_all [C', D']

theorem H (F : ActionFrame AG ST AC) (C D : Set AG) : IsGCGF (phi F C D) :=
  ofGrand_isGCGF _

theorem C (F : ActionFrame AG ST AC) (hF : IsGCGF F) {C D : Set AG} (h : C ⊆ D)
    (s : ST) (σD : D → AC)
    (hPrint : (phi F C D).out D' s (fun _ => enc σD) ⊆
      (phi F C D).out C' s (restrictJA hCD' (fun _ => enc σD))) :
    F.out D s σD ⊆ F.out C s (restrictJA h σD) := by
  intro x hx
  obtain ⟨σ', hσ', hx'⟩ := hF.mem_out_iff.1 hx
  -- the printed grand action: `enc σD` for the first two agents, `σ'` for the third
  let τ : ↥(Set.univ : Set (Fin 3)) → AG → Option AC :=
    fun k => if k.1 = 2 then fun i => some (σ' ⟨i, trivial⟩) else enc σD
  have hτ : x ∈ (phi F C D).out D' s (fun _ => enc σD) := by
    refine ⟨τ, ?_, fun i => σ' ⟨i, trivial⟩, fun i => ?_, hx'⟩
    · funext k
      have hk : k.1 ≠ 2 := by
        obtain ⟨k, hk⟩ := k
        simp only [D', Set.mem_insert_iff, Set.mem_singleton_iff] at hk
        rcases hk with rfl | rfl <;> simp
      simp [restrictJA, τ, hk]
    · have hσi : ∀ hi : i ∈ D, σD ⟨i, hi⟩ = σ' ⟨i, trivial⟩ := fun hi => by
        rw [← hσ']; rfl
      by_cases hC : i ∈ C
      · simp [τ, block, hC, enc, h hC, hσi (h hC)]
      · by_cases hD : i ∈ D
        · simp [τ, block, hC, hD, enc, hσi hD]
        · simp [τ, block, hC, hD]
  obtain ⟨τ₂, hτ₂, σ, hσ, hxσ⟩ := hPrint hτ
  refine hF.mem_out_iff.2 ⟨fun i => σ i.1, ?_, hxσ⟩
  funext ⟨i, hi⟩
  have h0 : τ₂ ⟨0, trivial⟩ = enc σD := congrFun hτ₂ ⟨0, rfl⟩
  have := hσ i
  simp only [block, hi, if_true, h0, enc, h hi, dif_pos, Option.some.injEq] at this
  exact this.symm

theorem lean_of_print : PrintStatement.{0, v, max u w} → LeanStatement.{u, v, w} := by
  intro hPrint AG ST AC F hF S T h s σD
  have : Nonempty ST := ⟨s⟩
  have : Nonempty (AG → Option AC) := ⟨fun _ => none⟩
  exact C F hF h s σD (hPrint (Fin 3) ST (AG → Option AC) (phi F S T) (H F S T) s C' D' hCD'
    (fun _ => enc σD))

theorem print_of_lean : LeanStatement.{u, v, w} → PrintStatement.{u, v, w} :=
  fun hLean AG _ _ ST _ AC _ F hF s C D h σD => hLean AG ST AC F hF C D h s σD

end Transfer104
