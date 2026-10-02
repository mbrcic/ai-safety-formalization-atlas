module

public import AISafetyAtlas.Sovereignty.SafetyGame
public import AISafetyAtlas.Sovereignty.Domination

/-!
# Why being outnumbered is not the same as being outmatched

A guard outnumbered by prisoners, a vendor outnumbered by the institutions
depending on it, one system outnumbered by the people nominally holding
override authority over it. In each case the many *can* win and do not. This
module isolates where that fact lives, because it lives in two different places
and neither of them is the effectivity layer.

## It is not in the game form

At a game form, `Forces G C Φ` quantifies over a **joint** commitment by `C`.
Coordination is free, so the many simply win, and `forces_superadditive` says
merging coalitions never costs anything. That is not a defect of the model: in
a genuinely simultaneous move the outnumbered guard does lose. What a game form
*can* say about the situation is that the win needs everyone —
`not_forces_of_veto_outside` is that, and it is why a coalition one member short
has nothing.

## It is in who moves when

`AdversaryLe Γ₁ Γ₂` says every move of `Γ₁`'s adversary is matched by a move of
`Γ₂`'s, at every state and action. Then `safetyKernel_subset_of_adversaryLe`:
a stronger adversary has a smaller safety kernel. The guard's position is the
statement that this inclusion is **strict** between the adversary that may
change one coordinate per round and the adversary that may change all of them
at once. The many's power is intact in both; only the schedule differs.

That inclusion being strict is not provable in general — it is a property of a
particular system — so the witness is in
`AISafetyAtlas.Examples.Sovereignty.Outnumbered`, where a guard who can put
down one revolt per round holds a threshold forever against defectors arriving
singly and cannot hold it for one round against defectors arriving together.

## It is also in the incentives, and that part is not here

The third mechanism is that the profile which overthrows the guard is not an
equilibrium: whoever moves first is punished, so nobody moves, so a coalition's
effectivity is never exercised. That needs preferences over outcomes and a
deviation-stability notion, and this repository has neither. Nothing below
should be read as addressing it.

Source and scope: `docs/provenance/formal-power-proposal-triage.md` for the
layers used. The one-to-many reading is this repository's, is not in the
proposal, and is not coverage of anything.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

/-! ## What a game form can say: the win needs everyone -/

variable {N : Type u} {X : Type v}

/--
**A coalition that leaves out a vetoing member forces nothing.**

If some `Y` disjoint from `C` can force the complement of `Φ`, then `C` cannot
force `Φ`, whatever its size. Applied at a single missing member this is why
unanimity is fragile: one abstention is a veto.
-/
public theorem not_forces_of_veto_outside {G : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G.strategy i)] {C Y : Set N} {Φ : Set X}
    (hdisj : Disjoint C Y) (hveto : Veto G Y Φ) : ¬ Forces G C Φ := by
  classical
  rintro ⟨sC, hsC⟩
  obtain ⟨sY, hsY⟩ := hveto
  refine absurd (hsY (fun i => if hi : i ∈ C then sC ⟨i, hi⟩ else
      if hj : i ∈ Y then sY ⟨i, hj⟩ else Classical.arbitrary _) ?_)
    (not_not_intro (hsC (fun i => if hi : i ∈ C then sC ⟨i, hi⟩ else
      if hj : i ∈ Y then sY ⟨i, hj⟩ else Classical.arbitrary _) ?_))
  · rintro ⟨i, hi⟩
    have hiC : i ∉ C := Set.disjoint_right.mp hdisj hi
    simp only [dif_neg hiC, dif_pos hi]
  · rintro ⟨i, hi⟩
    simp only [dif_pos hi]

/-! ## What the schedule says: a stronger adversary keeps less -/

variable {S : Type u} {A : Type v} {B₁ B₂ : Type w}

/--
**One adversary dominates another.** Every move the first can make at a state
and an action, the second can make too. Nothing is said about the reverse, so
the second may have moves the first has not -- which is the case of interest.
-/
@[expose] public def AdversaryLe (Γ₁ : SafetyGame S A B₁) (Γ₂ : SafetyGame S A B₂) :
    Prop :=
  ∀ s a b₁, ∃ b₂, Γ₂.step s a b₂ = Γ₁.step s a b₁

/-- **The controllable predecessor shrinks under a stronger adversary.** -/
public theorem cpre_subset_of_adversaryLe {Γ₁ : SafetyGame S A B₁}
    {Γ₂ : SafetyGame S A B₂} (h : AdversaryLe Γ₁ Γ₂) (W : Set S) :
    Γ₂.cpre W ⊆ Γ₁.cpre W := by
  rintro s ⟨a, ha⟩
  refine ⟨a, fun b₁ => ?_⟩
  obtain ⟨b₂, hb⟩ := h s a b₁
  exact hb ▸ ha b₂

/--
**And so does the safety kernel.**

Facing more answers cannot help. The content of the outnumbered guard is that
this inclusion is strict when the only difference between the two adversaries
is whether the many move singly or together.
-/
public theorem safetyKernel_subset_of_adversaryLe {Γ₁ : SafetyGame S A B₁}
    {Γ₂ : SafetyGame S A B₂} (h : AdversaryLe Γ₁ Γ₂) (V : Set S) :
    Γ₂.safetyKernel V ⊆ Γ₁.safetyKernel V :=
  Γ₁.subset_safetyKernel (Γ₂.safetyKernel_subset V)
    ((Γ₂.safetyKernel_subset_cpre V).trans (cpre_subset_of_adversaryLe h _))

end AISafetyAtlas.Sovereignty
