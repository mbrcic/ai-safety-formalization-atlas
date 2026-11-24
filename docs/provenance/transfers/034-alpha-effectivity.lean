import AISafetyAtlas.Sovereignty.Rights

/-!
Peleg (1998), Definition 3.3, p. 73. A nonempty proper coalition in a legal
game form is alpha-effective for a set if it has a joint strategy whose
outcome belongs to that set against every complement strategy. The cited
definition is `AISafetyAtlas.Sovereignty.Forces`.

The map gives a two-player game with no assigned rights. Each player can
choose an original joint strategy or a dummy. A dummy first choice loses.
A genuine first choice against a dummy opponent wins. Against a genuine
opponent the original outcome decides membership in the translated target.

Checked: `lake env lean docs/provenance/transfers/034-alpha-effectivity.lean`
-/

namespace Transfer034

open AISafetyAtlas.Sovereignty Classical
open scoped Set

universe u v r w

noncomputable def merge {N : Type u} {strat : N → Type w} {C : Set N}
    (a : ∀ i : C, strat i) (b : ∀ i : ↥(Cᶜ), strat i) (i : N) : strat i :=
  if hi : i ∈ C then a ⟨i, hi⟩ else b ⟨i, hi⟩

structure PrintGame (N : Type u) (X : Type v) (R : Type r) where
  game : GameForm.{u, v, w} N X
  nonemptyStrategy : ∀ i, Nonempty (game.strategy i)
  constitution : Constitution N X R
  standing : constitution.Standing
  permits : (C : Set N) → R → (∀ i : C, game.strategy i) → Prop
  legal : ∀ C a r, r ∈ constitution.assign C → permits C r a

def PrintStatement {N : Type u} {X : Type v} {R : Type r} [Finite N] [Finite R]
    (P : PrintGame.{u, v, r, w} N X R) {C : Set N} (_nonempty : C.Nonempty)
    (_proper : C ⊂ Set.univ) (B : Set X) : Prop :=
  ∃ a : ∀ i : C, P.game.strategy i, ∀ b : ∀ i : ↥(Cᶜ), P.game.strategy i,
    P.game.outcome (merge a b) ∈ B

def LeanStatement {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X)
    (C : Set N) (B : Set X) : Prop :=
  Forces G C B

def first : Set Bool := {i | i = false}

theorem first_nonempty : first.Nonempty := ⟨false, rfl⟩

theorem first_proper : first ⊂ Set.univ := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨Set.subset_univ _, ?_⟩
  intro heq
  have h : true ∈ (Set.univ : Set Bool) := Set.mem_univ _
  rw [← heq] at h
  simp [first] at h

private abbrev strategy {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X) (C : Set N) :
    Bool → Type (max u w)
  | false => Option (∀ i : C, G.strategy i)
  | true => Option (∀ i : ↥(Cᶜ), G.strategy i)

private noncomputable def outcome {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X)
    {C : Set N} (a : strategy G C false) (b : strategy G C true) : Option (Option X) :=
  match a, b with
  | none, _ => none
  | some _, none => some none
  | some a, some b => some (some (G.outcome (merge a b)))

noncomputable def phi {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X) (C : Set N) :
    PrintGame Bool (Option (Option X)) Unit where
  game := ⟨strategy G C, fun q ↦ outcome G (q false) (q true)⟩
  nonemptyStrategy := by intro i; cases i <;> exact ⟨none⟩
  constitution := ⟨fun _ ↦ ∅, fun _ _ ↦ {Set.univ}⟩
  standing := ⟨rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  permits := fun _ _ _ ↦ True
  legal := fun _ _ _ _ ↦ trivial

def target {X : Type v} (B : Set X) : Set (Option (Option X))
  | none => False
  | some none => True
  | some (some x) => x ∈ B

private theorem played {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X)
    {C : Set N} (a : ∀ i : first, strategy G C i) (b : ∀ i : ↥(firstᶜ), strategy G C i) :
    (phi G C).game.outcome (merge a b) =
      outcome G (a ⟨false, rfl⟩) (b ⟨true, by simp [first]⟩) := by
  change outcome G (merge a b false) (merge a b true) = _
  simp [merge, first]

private def firstChoice {N : Type u} {X : Type v} {G : GameForm.{u, v, w} N X}
    {C : Set N} (a : strategy G C false) (i : first) : strategy G C i := by
  have hi : i.1 = false := i.2
  simpa only [hi] using a

private def secondChoice {N : Type u} {X : Type v} {G : GameForm.{u, v, w} N X}
    {C : Set N} (b : strategy G C true) (i : ↥(firstᶜ)) : strategy G C i := by
  have hi : i.1 = true := by
    have hn : i.1 ∉ first := i.2
    cases hv : i.1
    · exact (hn hv).elim
    · rfl
  simpa only [hi] using b

theorem defining_condition {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X)
    (C : Set N) (B : Set X) :
    LeanStatement G C B ↔ PrintStatement (phi G C) first_nonempty first_proper (target B) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨firstChoice (some a), fun b ↦ ?_⟩
    rw [played G (firstChoice (some a)) b]
    change outcome G (some a) (b ⟨true, _⟩) ∈ target B
    cases b ⟨true, by simp [first]⟩ with
    | none => trivial
    | some b' =>
      exact ha (merge a b') (fun i ↦ by simp [merge, i.2])
  · rintro ⟨a, ha⟩
    cases h : a ⟨false, rfl⟩ with
    | none =>
      have hbad := ha (secondChoice none)
      rw [played G a (secondChoice none), h] at hbad
      exact False.elim hbad
    | some a' =>
      refine ⟨a', fun s hs ↦ ?_⟩
      have hout := ha (secondChoice (some (fun i ↦ s i)))
      rw [played G a (secondChoice (some (fun i ↦ s i))), h] at hout
      change G.outcome (merge a' (fun i ↦ s i)) ∈ B at hout
      have hm : merge a' (fun i ↦ s i) = s := by
        funext i
        by_cases hi : i ∈ C
        · simpa only [merge, dif_pos hi] using (hs ⟨i, hi⟩).symm
        · simp [merge, hi]
      rwa [hm] at hout

theorem lean_of_print {N : Type u} {X : Type v} (G : GameForm.{u, v, w} N X)
    (C : Set N) (B : Set X) :
    PrintStatement (phi G C) first_nonempty first_proper (target B) → LeanStatement G C B :=
  (defining_condition G C B).mpr

theorem print_of_lean {N : Type u} {X : Type v} {R : Type r} [Finite N] [Finite R]
    (P : PrintGame.{u, v, r, w} N X R) {C : Set N} (hC : C.Nonempty) (hProper : C ⊂ Set.univ)
    (B : Set X) : LeanStatement P.game C B → PrintStatement P hC hProper B := by
  rintro ⟨a, ha⟩
  exact ⟨a, fun b ↦ ha (merge a b) (fun i ↦ by simp [merge, i.2])⟩

end Transfer034
