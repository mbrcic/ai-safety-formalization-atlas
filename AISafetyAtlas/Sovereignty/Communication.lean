module

public import AISafetyAtlas.Sovereignty.Auditability

/-!
# Sending a message through an adversary

How much can a coalition say through a channel it does not control, if the
message has to arrive whatever everyone else does?

`TransmitsZeroError` is the proposal's `B3`: a family of decoding regions in
the observable projection, pairwise disjoint, each of which the coalition can
force. `transmitsZeroError_iff_exists_code` is the result -- that condition is
exactly the existence of an encoder and **one fixed decoder** that works
against every opposition.

The fixed decoder is the content. Disjointness of the regions is what lets a
single decoder be defined at all; without it two messages could produce the
same reading and no decoder could be right about both. The quantity print
derives from this, the largest such `k`, is a communication capacity computed
from strategic power rather than from a probability law, and it is not Shannon
capacity: no distribution appears anywhere here.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

variable {N : Type u} {X : Type v} {G : GameForm.{u, v, w} N X}

/--
**Zero-error communicative power.** For each message there is a region of the
observable projection the coalition can force the outcome into, and the regions
for different messages are disjoint.
-/
@[expose] public def TransmitsZeroError (G : GameForm.{u, v, w} N X) (C : Set N)
    {Z : Type*} (f : X → Z) (Msg : Type*) : Prop :=
  ∃ D : Msg → Set Z, (∀ m m' : Msg, m ≠ m' → Disjoint (D m) (D m')) ∧
    ∀ m, Forces G C (f ⁻¹' D m)

/--
**`B3`: disjoint forceable regions are exactly a zero-error code.**

The right-hand side is what an engineer would build: one encoder per message,
one decoder for all of them, correct against every opposition. The left-hand
side is what can be checked from the effectivity function alone.

The proof of the forward direction is where disjointness is spent: a reading
could in principle lie in several regions, and the decoder picks one; that
choice is right because a commitment always leaves an outcome possible and two
distinct regions share none.
-/
public theorem transmitsZeroError_iff_exists_code
    [∀ i, Nonempty (G.strategy i)] {C : Set N} {Z Msg : Type*} [Nonempty Msg]
    (f : X → Z) :
    TransmitsZeroError G C f Msg ↔
      ∃ (enc : Msg → ∀ i : C, G.strategy i) (dec : Z → Msg),
        ∀ m : Msg, outcomesOf G C (enc m) ⊆ {x | dec (f x) = m} := by
  classical
  constructor
  · rintro ⟨D, hdisj, hforce⟩
    choose enc henc using fun m => forces_iff_outcomesOf_subset.mp (hforce m)
    refine ⟨enc, fun z => if h : ∃ m, z ∈ D m then Classical.choose h
      else Classical.arbitrary Msg, fun m x hx => ?_⟩
    have hfx : f x ∈ D m := henc m hx
    have hex : ∃ m', f x ∈ D m' := ⟨m, hfx⟩
    show (if h : ∃ m', f x ∈ D m' then Classical.choose h
      else Classical.arbitrary Msg) = m
    rw [dif_pos hex]
    by_contra hne
    exact Set.disjoint_left.mp (hdisj _ _ hne) (Classical.choose_spec hex) hfx
  · rintro ⟨enc, dec, hcode⟩
    refine ⟨fun m => {z | dec z = m}, fun m m' hmm => ?_, fun m => ?_⟩
    · refine Set.disjoint_left.mpr fun z hz hz' => hmm ?_
      exact hz.symm.trans hz'
    · exact forces_iff_outcomesOf_subset.mpr ⟨enc m, hcode m⟩

/-- Fewer messages are easier to send, along any injection of message sets. -/
public theorem TransmitsZeroError.comp_injective {C : Set N} {Z Msg Msg' : Type*}
    {f : X → Z} (h : TransmitsZeroError G C f Msg) (e : Msg' → Msg)
    (he : Function.Injective e) : TransmitsZeroError G C f Msg' := by
  obtain ⟨D, hdisj, hforce⟩ := h
  exact ⟨D ∘ e, fun m m' hmm => hdisj _ _ fun heq => hmm (he heq), fun m => hforce (e m)⟩

/-- **Coarsening the channel cannot help.** If the coalition can send a message
set through a coarser reading, it can send it through the finer one, because
every coarse region pulls back to a fine one. This is the qualitative shadow of
the proposal's `Q8`. -/
public theorem TransmitsZeroError.of_comp {C : Set N} {Z Z' Msg : Type*}
    {f : X → Z} {g : Z → Z'} (h : TransmitsZeroError G C (g ∘ f) Msg) :
    TransmitsZeroError G C f Msg := by
  obtain ⟨D, hdisj, hforce⟩ := h
  exact ⟨fun m => g ⁻¹' D m, fun m m' hmm => Disjoint.preimage g (hdisj m m' hmm),
    hforce⟩

end AISafetyAtlas.Sovereignty
