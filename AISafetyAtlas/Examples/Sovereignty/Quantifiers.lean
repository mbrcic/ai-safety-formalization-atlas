module

public import AISafetyAtlas.Sovereignty.Quantifiers
public import AISafetyAtlas.Sovereignty.Playability

/-!
# Matching a bit you cannot see, and two guarantees that will not conjoin

Two countermodels, one for each quantifier failure.

`bitMatch` is the simultaneous-bit game: the principal (`false`) and the
opponent (`true`) each name a bit, and the outcome records whether they agree.
`bitMatch_not_forces` says the principal cannot guarantee agreement --
whatever bit it commits to, the opponent names the other. `bitMatch_forcesResp`
says it can answer **each** opponent commitment, by naming that same bit. So
the response-dependent quantifier is strictly weaker, which is the proposal's
`P8`, and `S3` is that failure read at a catalogue.

`decider` is `principalDecides`: the principal names the outcome outright.
`decider_forces_both` and `decider_not_forces_inter` are the proposal's `P7` --
it guarantees `{true}` and it guarantees `{false}`, and it cannot guarantee
both, because the intersection is empty and nothing forces the empty set.
`decider_inter_of_shared` shows where the repair lives: at a *single*
commitment the conjunction goes through, which is the proposal's `A6`.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Quantifiers

open AISafetyAtlas.Sovereignty

/-- The simultaneous-bit game: each party names a bit, the outcome records
whether the bits agree. -/
@[expose] public def bitMatch : GameForm.{0, 0, 0} Bool Bool where
  strategy _ := Bool
  outcome s := s false == s true

/-- Everyone has a strategy. -/
public instance bitMatch_nonempty (i : Bool) : Nonempty (bitMatch.strategy i) :=
  ⟨false⟩

/-- **The principal cannot guarantee agreement.** Whatever bit it commits to,
the opponent names the other one. -/
public theorem bitMatch_not_forces :
    ¬ Forces bitMatch {false} ({true} : Set Bool) := by
  unfold bitMatch
  decide

/-- **And it can answer each opponent commitment separately**, by naming the
bit that commitment names. The two facts together are the proposal's `P8`. -/
public theorem bitMatch_forcesResp :
    ForcesResp bitMatch {false} ({true} : Set Bool) := by
  intro sD
  have hmem : (true : Bool) ∈ ({false}ᶜ : Set Bool) := by simp
  refine ⟨fun _ => sD ⟨true, hmem⟩, fun s hD hC => ?_⟩
  have h0 : s false = sD ⟨true, hmem⟩ := hC ⟨false, rfl⟩
  have h1 : s true = sD ⟨true, hmem⟩ := hD ⟨true, hmem⟩
  have hy : ∀ y : Bool, (y == y) = true := fun y => by cases y <;> rfl
  simp only [bitMatch, h0, h1, Set.mem_singleton_iff]
  exact hy _

/-- So response-dependent capacity is strictly weaker than a guarantee. -/
public theorem forcesResp_not_forces :
    ForcesResp bitMatch {false} ({true} : Set Bool) ∧
      ¬ Forces bitMatch {false} ({true} : Set Bool) :=
  ⟨bitMatch_forcesResp, bitMatch_not_forces⟩

/-- **`S3` at a one-demand catalogue.** The responsive reading passes the
catalogue and the enforceable reading does not, so the inclusion
`demandwiseResp_of_demandwise` is strict. -/
public theorem demandwiseResp_not_demandwise :
    DemandwiseResp bitMatch {false} {({true} : Set Bool)} ∧
      ¬ Demandwise bitMatch {false} {({true} : Set Bool)} := by
  refine ⟨fun Φ hΦ => ?_, fun h => bitMatch_not_forces (h _ rfl)⟩
  rw [Set.mem_singleton_iff] at hΦ
  exact hΦ ▸ bitMatch_forcesResp

/-! ## Two guarantees that will not conjoin -/

/-- The principal names the outcome outright. -/
@[expose] public def decider : GameForm.{0, 0, 0} Bool Bool :=
  principalDecides Bool

/-- Everyone has a strategy. -/
public instance decider_nonempty (i : Bool) : Nonempty (decider.strategy i) :=
  ⟨false⟩

/-- It guarantees each singleton. -/
public theorem decider_forces_both :
    Forces decider {false} ({true} : Set Bool) ∧
      Forces decider {false} ({false} : Set Bool) :=
  ⟨principalDecides_forces_singleton true, principalDecides_forces_singleton false⟩

/-- **And not their intersection**, which is empty. This is the proposal's
`P7`: same agent, two guarantees, no conjunction. -/
public theorem decider_not_forces_inter :
    ¬ Forces decider {false}
      (({true} : Set Bool) ∩ ({false} : Set Bool)) := by
  have hempty : (({true} : Set Bool) ∩ ({false} : Set Bool)) = ∅ := by
    ext b; simp
  rw [hempty]
  exact not_forces_empty {false}

/-- **Where the repair lives.** One commitment whose footprint sits inside both
targets does give the conjunction -- here the commitment naming `true`, whose
footprint is `{true}`, against the targets `{true}` and `Set.univ`. This is the
proposal's `A6`, and it is why `P7` is a statement about witnesses rather than
about conjunction. -/
public theorem decider_inter_of_shared :
    Forces decider {false} (({true} : Set Bool) ∩ Set.univ) := by
  refine forces_inter_of_shared_footprint (sC := fun _ => true) ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    exact hs ⟨false, rfl⟩
  · exact fun _ _ => trivial

/-! ## The monotonicity and conjunction lemmas, at these two games

`bitMatch` carries the responsive reading and `decider` the enforceable one, so
each of the remaining statements has a game form where its hypothesis holds.
-/

/-- Response-dependent capacity is upward closed in the target. -/
public theorem bitMatch_forcesResp_univ :
    ForcesResp bitMatch {false} (Set.univ : Set Bool) :=
  ForcesResp.mono bitMatch_forcesResp (Set.subset_univ _)

/-- The responsive reading at a two-demand catalogue ... -/
public theorem bitMatch_demandwiseResp_pair :
    DemandwiseResp bitMatch {false}
      ({({true} : Set Bool), (Set.univ : Set Bool)} : Set (Set Bool)) := by
  rintro Φ (rfl | rfl)
  · exact bitMatch_forcesResp
  · exact bitMatch_forcesResp_univ

/-- ... is antitone, so it still passes the one-demand sub-catalogue. -/
public theorem bitMatch_demandwiseResp_singleton :
    DemandwiseResp bitMatch {false} ({({true} : Set Bool)} : Set (Set Bool)) :=
  DemandwiseResp.mono bitMatch_demandwiseResp_pair (by
    rintro Φ rfl
    simp)

/-- The principal that names the outcome meets a one-demand catalogue
enforceably. -/
public theorem decider_demandwise_singleton :
    Demandwise decider {false} ({({true} : Set Bool)} : Set (Set Bool)) := by
  rintro Φ hΦ
  rw [Set.mem_singleton_iff] at hΦ
  exact hΦ ▸ principalDecides_forces_singleton true

/-- **An enforceable catalogue is a responsive one.** `demandwiseResp_not_demandwise`
is the witness that the converse fails, so this inclusion is strict. -/
public theorem decider_demandwiseResp_singleton :
    DemandwiseResp decider {false} ({({true} : Set Bool)} : Set (Set Bool)) :=
  demandwiseResp_of_demandwise decider_demandwise_singleton

/-- **Two guarantees carried by one commitment do conjoin**, which is the
positive half of what `decider_not_forces_inter` denies for two commitments. -/
public theorem decider_forces_iInter :
    Forces decider {false} (⋂ _ : Bool, ({true} : Set Bool)) :=
  forces_iInter_of_shared_footprint (sC := fun _ ↦ true) (by
    rintro _ x ⟨s, hs, rfl⟩
    show decider.outcome s ∈ ({true} : Set Bool)
    rw [Set.mem_singleton_iff]
    exact hs ⟨false, rfl⟩)

end AISafetyAtlas.Examples.Sovereignty.Quantifiers
