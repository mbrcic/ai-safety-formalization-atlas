module

public import AISafetyAtlas.Sovereignty.Transfer

/-!
# One policy or one policy per demand

`Demandwise` asks, for each demand separately, whether the coalition can force
it. Nothing in that asks for a single way of doing so, and the difference is
not a technicality: it is the whole space between a system that can pass each
item of a checklist and a system that can be run.

## What is here

`DemandwiseUniform` is the stronger reading: **one** commitment whose footprint
sits inside every demand at once. `demandwise_of_demandwiseUniform` is the
implication, and it is strict.

`demandwise_iff_exists_selector` is the proposal's `S2`: the weak reading is
exactly the existence of a *selector*, one policy per demand, chosen with
knowledge of which demand is being served. Print states it for a finite
catalogue; the same proof works at any catalogue under choice, and print says
so. What neither gives is a policy that does not need to be told the demand in
advance.

`not_forces_of_disjoint_of_shared` is the proposal's `S7`: no single commitment
serves two demands with nothing in common. Together with
`forces_inter_of_shared_footprint` -- the shared-witness rule -- this says
exactly when the uniform reading is unavailable, and it is why print insists
that conflicting requests need allocation or arbitration rather than being
required all at once.

`retainsFamily_refl` completes the proposal's `S4`: retention at a fixed
protected family is a preorder, with transitivity already stated as
`RetainsFamily.trans`.

## The separation

`AISafetyAtlas.Examples.Sovereignty.Catalogue` puts the two readings apart at
one game: a principal who names the outcome meets the catalogue
`{{true}, {false}}` demandwise and meets no part of it uniformly, because the
two demands are disjoint. So an evaluation that scores demands one at a time
certifies something the system cannot do.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

variable {N : Type u} {X : Type v} {G : GameForm.{u, v, w} N X}

/-! ## A commitment always leaves something possible -/

/-- **Every commitment has at least one possible outcome**, as long as everyone
has a strategy to play. This is what makes a conflicting pair of demands a
genuine obstruction rather than a vacuous one. -/
public theorem outcomesOf_nonempty [∀ i, Nonempty (G.strategy i)] {C : Set N}
    (sC : ∀ i : C, G.strategy i) : (outcomesOf G C sC).Nonempty := by
  classical
  refine ⟨G.outcome (fun i => if hi : i ∈ C then sC ⟨i, hi⟩
    else Classical.arbitrary _), _, ?_, rfl⟩
  rintro ⟨i, hi⟩
  simp [hi]

/-! ## One policy for the whole catalogue -/

/--
**Uniform demandwise sovereignty.** A single commitment whose footprint lies
inside every demand of the catalogue.

`Demandwise` allows a different commitment for each demand. This does not, and
that is the difference between passing a checklist and being operable.
-/
@[expose] public def DemandwiseUniform (G : GameForm.{u, v, w} N X) (C : Set N)
    (𝒬 : Set (Set X)) : Prop :=
  ∃ sC : ∀ i : C, G.strategy i, ∀ Φ ∈ 𝒬, outcomesOf G C sC ⊆ Φ

/-- One policy for all the demands is a policy for each of them. -/
public theorem demandwise_of_demandwiseUniform {C : Set N} {𝒬 : Set (Set X)}
    (h : DemandwiseUniform G C 𝒬) : Demandwise G C 𝒬 := by
  obtain ⟨sC, hsC⟩ := h
  exact fun Φ hΦ => forces_iff_outcomesOf_subset.mpr ⟨sC, hsC Φ hΦ⟩

/-- The uniform reading forces the whole intersection at once, which is the
shared-witness rule read at a catalogue. -/
public theorem forces_sInter_of_demandwiseUniform {C : Set N}
    {𝒬 : Set (Set X)} (h : DemandwiseUniform G C 𝒬) : Forces G C (⋂₀ 𝒬) := by
  obtain ⟨sC, hsC⟩ := h
  exact forces_iff_outcomesOf_subset.mpr
    ⟨sC, fun _ hx => Set.mem_sInter.mpr fun Φ hΦ => hsC Φ hΦ hx⟩

/-- And it is antitone in the catalogue. -/
public theorem DemandwiseUniform.mono {C : Set N} {𝒬 ℛ : Set (Set X)}
    (h : DemandwiseUniform G C ℛ) (h𝒬 : 𝒬 ⊆ ℛ) : DemandwiseUniform G C 𝒬 := by
  obtain ⟨sC, hsC⟩ := h
  exact ⟨sC, fun Φ hΦ => hsC Φ (h𝒬 hΦ)⟩

/-! ## `S2`: the weak reading is a selector -/

/--
**`S2`: demandwise sovereignty is exactly a selector.** A policy for each
demand, chosen knowing which demand it must serve.

Print states this for a finite catalogue and notes that the same argument works
in general under choice; that is the form here. Print also notes what the
equivalence does not give, and the statement makes it visible: the witness is a
function *of the demand*, so nothing here produces a policy that works before
the demand is known. That policy is `DemandwiseUniform`, and it is strictly
stronger.
-/
public theorem demandwise_iff_exists_selector {C : Set N} {𝒬 : Set (Set X)} :
    Demandwise G C 𝒬 ↔
      ∃ f : 𝒬 → ∀ i : C, G.strategy i,
        ∀ Φ : 𝒬, outcomesOf G C (f Φ) ⊆ (Φ : Set X) := by
  classical
  constructor
  · intro h
    choose f hf using fun Φ : 𝒬 => forces_iff_outcomesOf_subset.mp (h Φ Φ.2)
    exact ⟨f, hf⟩
  · rintro ⟨f, hf⟩ Φ hΦ
    exact forces_iff_outcomesOf_subset.mpr ⟨f ⟨Φ, hΦ⟩, hf ⟨Φ, hΦ⟩⟩

/-! ## `S7`: conflicting demands need arbitration, not a policy -/

/--
**`S7`: no single commitment serves two demands with nothing in common.**

The obstruction is not that the demands are hard. It is that a commitment
leaves at least one outcome possible, and that outcome would have to lie in
both.

This is the exact boundary of the shared-witness rule: where
`forces_inter_of_shared_footprint` would conclude `Forces G C (Φ ∩ Ψ)`, the
intersection is empty and nothing forces the empty set. Print's conclusion is
that conflicting requests must be allocated, time-indexed, or arbitrated --
never required simultaneously.
-/
public theorem not_forces_of_disjoint_of_shared [∀ i, Nonempty (G.strategy i)]
    {C : Set N} {Φ Ψ : Set X} {sC : ∀ i : C, G.strategy i}
    (hΦ : outcomesOf G C sC ⊆ Φ) (hΨ : outcomesOf G C sC ⊆ Ψ)
    (hd : Disjoint Φ Ψ) : False := by
  obtain ⟨x, hx⟩ := outcomesOf_nonempty (G := G) sC
  exact Set.disjoint_left.mp hd (hΦ hx) (hΨ hx)

/-- **The same at a catalogue.** A catalogue with two disjoint demands admits no
uniform policy, however each demand looks on its own. -/
public theorem not_demandwiseUniform_of_disjoint [∀ i, Nonempty (G.strategy i)]
    {C : Set N} {𝒬 : Set (Set X)} {Φ Ψ : Set X} (hΦ : Φ ∈ 𝒬) (hΨ : Ψ ∈ 𝒬)
    (hd : Disjoint Φ Ψ) : ¬ DemandwiseUniform G C 𝒬 := by
  rintro ⟨sC, hsC⟩
  exact not_forces_of_disjoint_of_shared (hsC Φ hΦ) (hsC Ψ hΨ) hd

/-- A separating catalogue of two demands is a conflicting one, so `S7` refutes
the uniform reading wherever the proposal's §5.2 nonvacuity condition holds on
a pair. -/
public theorem not_demandwiseUniform_of_separating_pair
    [∀ i, Nonempty (G.strategy i)] {C : Set N} {Φ Ψ : Set X}
    (h : Separating ({Φ, Ψ} : Set (Set X))) :
    ¬ DemandwiseUniform G C ({Φ, Ψ} : Set (Set X)) := by
  refine not_demandwiseUniform_of_disjoint (Φ := Φ) (Ψ := Ψ) (by simp) (by simp) ?_
  rw [Set.disjoint_iff_inter_eq_empty, ← Set.sInter_pair]
  exact h

/-! ## `S4`: retention is a preorder -/

/-- **Retention is reflexive**, which with `RetainsFamily.trans` is the
proposal's `S4`: at a fixed protected family, retention is a preorder. It is
not a partial order, and print does not claim one -- two game forms can retain
each other without being equal. -/
public theorem retainsFamily_refl (G : GameForm.{u, v, w} N X) (C : Set N)
    (𝒜 : Set (Set X)) : RetainsFamily G G C C 𝒜 :=
  fun _ _ h => h

end AISafetyAtlas.Sovereignty
