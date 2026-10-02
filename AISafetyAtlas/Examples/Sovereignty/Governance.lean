module

public import AISafetyAtlas.Sovereignty.Enforcement
public import AISafetyAtlas.Sovereignty.ShutdownChannel
public import AISafetyAtlas.Sovereignty.Conformity
public import AISafetyAtlas.Sovereignty.Attestation
public import AISafetyAtlas.Sovereignty.DelegationChain
public import AISafetyAtlas.Examples.Sovereignty.Catalogue
public import AISafetyAtlas.Examples.Sovereignty.Authority

/-!
# The five governance bridges, run

Each bridge under `AISafetyAtlas.Sovereignty` states an obstruction conditionally
— *if the observation channel collides*, *if the relay may decline*, *if two
requirements are disjoint*. A conditional obstruction with nothing satisfying its
antecedent is decoration, so every one of them is instantiated here, and where
the obstruction can be escaped the escape is exhibited too.

* **Enforcement.** `blindRegime` is a rule against an act whose log entry is the
  same either way; `openRegime` is the same rule with the act in the log.
  The first admits no sanction at all, the second admits one — so the module's
  hypothesis is doing work rather than holding vacuously.
* **Shutdown channel.** `haltThrough` halts on delivery and keeps running
  otherwise: obedience is total, authority is absent, and
  `haltThrough_not_inert` shows the channel is not the degenerate one the repair
  would force.
* **Conformity.** `bitAssessment` passes each item of a two-item checklist and is
  not operable, at the game form `AISafetyAtlas.Examples.Sovereignty.Catalogue`
  already uses.
* **Attestation.** The two existentials are consumed rather than restated: a
  record and the claim it makes are different predicates, and a pair of recorded
  properties implies nothing in either direction.
* **Delegation chain.** The general obstruction recovers
  `split_opponent_not_forces_snd` at the `split` game, so the abstract statement
  and the concrete refutation are the same fact.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Governance

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Examples.Sovereignty.Quantifiers
open AISafetyAtlas.Examples.Sovereignty.Authority

/-! ## Enforcement: a rule against something the log does not record

An act is a pair: whether the forbidden thing was done, and what the log shows.
The norms forbid doing it and permit not doing it. What changes between the two
regimes is only what the overseer sees.
-/

/-- The rule: doing the thing is forbidden, not doing it is permitted. -/
@[expose] public def actNorms : NormSystem (Bool × Bool) where
  permitted e := e.1 = false
  forbidden e := e.1 = true

/-- The rule classifies every act... -/
public theorem actNorms_complete : actNorms.Complete := by
  rintro ⟨a, l⟩
  cases a
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- ...and never both ways. -/
public theorem actNorms_consistent : actNorms.Consistent := by
  rintro ⟨a, l⟩ ⟨hp, hf⟩
  exact Bool.noConfusion (hp.symm.trans hf)

/-- **A monitor that records only the second component.** The act itself never
reaches the log. -/
@[expose] public def blindRegime : Enforcement.Regime (Bool × Bool) Bool where
  norms := actNorms
  observe e := e.2

/-- **A monitor that records the act.** -/
@[expose] public def openRegime : Enforcement.Regime (Bool × Bool) Bool where
  norms := actNorms
  observe e := e.1

/-- Doing the forbidden thing and not doing it produce the same log entry. -/
public theorem blindRegime_collides :
    blindRegime.observe (true, false) = blindRegime.observe (false, false) := rfl

/--
**The rule cannot be enforced, by anything.** No response type, no response
function and no choice of benign response separates the violation from the
compliant act — and no detector sees it either.
-/
public theorem blindRegime_unenforceable :
    ¬ Enforcement.Detectable blindRegime ∧
      ∀ (S : Type) (respond : Bool → S) (benign : S),
        ¬ Enforcement.Enforces blindRegime respond benign :=
  Enforcement.undetectable_norm_is_unenforceable blindRegime
    blindRegime_collides rfl rfl actNorms_consistent

/--
**And the same rule under a monitor that sees the act is enforceable**, by the
response "flag it". So the obstruction is a property of the channel and not of
the rule, which is the whole reason the module carries the observation as a
field.
-/
public theorem openRegime_enforced :
    Enforcement.Enforces openRegime (fun a => a) false := by
  constructor
  · rintro ⟨a, l⟩ hf
    exact fun h => Bool.noConfusion (hf.symm.trans h)
  · rintro ⟨a, l⟩ hp
    exact hp

/-- Which makes it detectable, through the converse. -/
public theorem openRegime_detectable : Enforcement.Detectable openRegime :=
  Enforcement.detectable_of_enforcement openRegime openRegime_enforced actNorms_complete

/-! ## Shutdown: an instruction that is obeyed and cannot be given -/

/-- **Halt on delivery, keep running otherwise.** The outcome `true` is "still
running". -/
@[expose] public def haltThrough : ShutdownChannel.RelayedCommand Unit Bool where
  idle := true
  effect _ := false

/-- Halting is not the same as continuing, so the command is a live one. -/
public theorem haltThrough_live : haltThrough.effect () ≠ haltThrough.idle := by decide

/--
**Total obedience, and no authority.** Every delivered halt halts, and no
instruction the principal can give guarantees a halt.
-/
public theorem haltThrough_obeys_without_authority :
    (∀ c, ShutdownChannel.run haltThrough true c = haltThrough.effect c) ∧
      ¬ ∀ deliver : Bool,
        ShutdownChannel.run haltThrough deliver () = haltThrough.effect () :=
  ShutdownChannel.obedience_does_not_give_authority haltThrough haltThrough_live

/-- The relay, on its own, keeps the system running. -/
public theorem haltThrough_relay_keeps_running :
    ∀ c : Unit, ShutdownChannel.run haltThrough false c = haltThrough.idle :=
  ShutdownChannel.relay_forces_idle haltThrough

/--
**And this channel is not the degenerate one.** `undeclinable_iff_inert` says the
only relayed channel whose instruction always takes effect is one where every
command does nothing; this channel does something, so no assumption inside the
model rescues it.
-/
public theorem haltThrough_not_inert :
    ¬ ∀ (c : Unit) (deliver : Bool),
        ShutdownChannel.run haltThrough deliver c = haltThrough.effect c := by
  rw [ShutdownChannel.undeclinable_iff_inert]
  intro h
  exact haltThrough_live (h ())

/-! ## Conformity: every item passed, nothing operable -/

/-- The assessment: the one-party decider game, assessed against two
requirements that contradict each other. -/
@[expose] public def bitAssessment : Conformity.Assessment.{0, 0, 0} Bool Bool where
  system := decider
  operator := {false}
  requirements := Catalogue.rivalBits

/-- **Every item of the checklist passes.** -/
public theorem bitAssessment_passesEach : Conformity.PassesEach bitAssessment :=
  Catalogue.decider_demandwise

/-- **And no single operating policy meets the catalogue.** -/
public theorem bitAssessment_not_operable : ¬ Conformity.Operable bitAssessment :=
  Catalogue.decider_not_demandwiseUniform

/--
**Both together: a passing certificate over a system that cannot be run.** The
defect is visible in the requirement set alone — the two requirements are
disjoint — without examining the system at all.
-/
public theorem bitAssessment_passes_and_not_operable :
    Conformity.PassesEach bitAssessment ∧ ¬ Conformity.Operable bitAssessment := by
  have : ∀ i, Nonempty (bitAssessment.system.strategy i) := fun _ => ⟨false⟩
  refine Conformity.passes_every_check_and_not_operable bitAssessment
    (Φ := ({true} : Set Bool)) (Ψ := ({false} : Set Bool))
    bitAssessment_passesEach (by simp [bitAssessment, Catalogue.rivalBits])
    (by simp [bitAssessment, Catalogue.rivalBits]) ?_
  rw [Set.disjoint_iff_inter_eq_empty]
  ext b
  simp

/-- **The fibre reading of detectability**, at the regime that has it: the
prohibition is recoverable from the log exactly because two acts with the same
log entry are prohibited alike. -/
public theorem openRegime_constant_on_fibres :
    ∀ e e' : Bool × Bool, openRegime.observe e = openRegime.observe e' →
      openRegime.norms.forbidden e = openRegime.norms.forbidden e' :=
  (Enforcement.detectable_iff_constant_on_fibres openRegime).mp openRegime_detectable

/-! ## Conformity: a catalogue one policy does serve -/

/-- The same system assessed against two requirements a single policy meets. -/
@[expose] public def agreeAssessment : Conformity.Assessment.{0, 0, 0} Bool Bool where
  system := decider
  operator := {false}
  requirements := Catalogue.agreeBits

/-- **This one is operable**, so the negative results above are not the only
thing the layer can say. -/
public theorem agreeAssessment_operable : Conformity.Operable agreeAssessment :=
  Catalogue.decider_demandwiseUniform

/-- Operability is the stronger reading, and here it delivers the weaker one. -/
public theorem agreeAssessment_passesEach : Conformity.PassesEach agreeAssessment :=
  Conformity.passesEach_of_operable agreeAssessment agreeAssessment_operable

/-- And it delivers what a deployment actually needs: every requirement met at
once by one commitment. -/
public theorem agreeAssessment_meets_all_at_once :
    Forces agreeAssessment.system agreeAssessment.operator (⋂₀ agreeAssessment.requirements) :=
  Conformity.operable_meets_all_at_once agreeAssessment agreeAssessment_operable

/-- **A catalogue containing a conflicting pair is inoperable however much else
it contains.** Adding requirements cannot repair the conflict, so the diagnosis
survives enlarging the standard. -/
public theorem widened_not_operable :
    ¬ Conformity.Operable
      { system := decider, operator := {false},
        requirements := Catalogue.rivalBits ∪ Catalogue.agreeBits } :=
  Conformity.not_operable_of_subset_not_operable _ Set.subset_union_left
    Catalogue.decider_not_demandwiseUniform

/-! ## Attestation: a record and its claim are different predicates -/

/-- **`A4` consumed at the bridge.** What a record asserts and what is the case
are not the same predicate, so no proof that a claim was attested is a proof of
the claim. -/
public theorem attested_ne_holds :
    ∃ (C : Type) (A : Attestation.Record C), A.attested ≠ A.holds := by
  obtain ⟨C, A, c, hv, ht⟩ := Attestation.attestation_is_not_the_claim
  exact ⟨C, A, fun h => ht (h ▸ hv)⟩

/-- **`B8` consumed at the bridge.** Two recorded properties of one system
license no inference in either direction, so any link between them is an
assumption about the system. -/
public theorem recorded_properties_link_nothing :
    ∃ (Sys : Type) (p q : Sys → Prop), (¬ ∀ s, p s → q s) ∧ ¬ ∀ s, q s → p s :=
  Attestation.no_property_implies_another

/-- **Neither direction of attestation transfers**, consumed: a record can assert
what is false, and something can hold without being recorded. -/
public theorem attestation_transfers_nowhere :
    ∃ (C : Type) (A : Attestation.Record C),
      (¬ ∀ c, A.attested c → A.holds c) ∧ ¬ ∀ c, A.holds c → A.attested c :=
  Attestation.attested_does_not_transfer

/-- **The independence is not degenerate**, consumed from the four quadrants:
neither recorded property is constant, so the failure to imply one another is not
the trivial failure of a property that never holds or always does. -/
public theorem recorded_properties_are_nontrivial :
    ∃ (Sys : Type) (p q : Sys → Prop),
      (∃ s, p s) ∧ (∃ s, ¬ p s) ∧ (∃ s, q s) ∧ (∃ s, ¬ q s) := by
  obtain ⟨Sys, p, q, neither, onlyQ, onlyP, both, hn, hq, hp, -⟩ :=
    Attestation.properties_are_independent
  exact ⟨Sys, p, q, ⟨onlyP, hp.1⟩, ⟨neither, hn.1⟩, ⟨onlyQ, hq.2⟩, ⟨neither, hn.2⟩⟩

/-! ## Delegation: the general obstruction at a concrete chain -/

/-- The opponent's commitment never reaches the second matter: whatever it
commits to, the principal can still move the second coordinate off any target. -/
public theorem split_snd_is_free (w : Bool) :
    ∀ sC : ∀ i : ({true} : Set Bool), split.strategy i,
      ∃ s : ∀ i, split.strategy i,
        (∀ i : ({true} : Set Bool), s i = sC i) ∧ (split.outcome s).2 ≠ w := by
  intro sC
  refine ⟨fun i => match i with | true => sC ⟨true, rfl⟩ | false => !w, ?_, ?_⟩
  · rintro ⟨i, hi⟩
    obtain rfl : i = true := hi
    rfl
  · show (!w) ≠ w
    cases w <;> decide

/--
**The general theorem recovers the concrete refutation.** So
`not_forces_of_free_coordinate` is not a weaker restatement of
`split_opponent_not_forces_snd`; it is the same fact with the game left open,
and the concrete game is the witness that its hypothesis is inhabited.
-/
public theorem split_opponent_not_forces_snd_via_general (w : Bool) :
    ¬ Forces split {true} (Prod.snd ⁻¹' {w}) :=
  DelegationChain.not_forces_of_free_coordinate split {true} w (split_snd_is_free w)

/--
**The chain, all three arrows at once.** The opponent settles the first matter,
the principal settles the second, and the opponent settles nothing about the
second — so the two documented powers do not compose into the third.
-/
public theorem split_chain_does_not_compose (v w : Bool) :
    Forces split {true} (Prod.fst ⁻¹' {v}) ∧
      Forces split {false} (Prod.snd ⁻¹' {w}) ∧
        ¬ Forces split {true} (Prod.snd ⁻¹' {w}) :=
  DelegationChain.power_over_a_matter_does_not_compose split {true} {false} v w
    (split_opponent_forces_fst v) (split_principal_forces_snd w) (split_snd_is_free w)

/--
**And what a single commitment does buy.** With both parties inside the
coalition, one commitment settles both matters at once — which is the repair the
bridge names, and it needs the *same* commitment rather than two separate powers.
-/
public theorem split_both_matters_of_one_commitment (v w : Bool) :
    Forces split (Set.univ : Set Bool)
      ((Prod.fst ⁻¹' {v}) ∩ (Prod.snd ⁻¹' {w})) := by
  refine DelegationChain.forces_both_of_shared_commitment split Set.univ v w
    (sC := fun i => if (i : Bool) then v else w) ?_ ?_
  · rintro x ⟨s, hs, rfl⟩
    have h : s true = v := by simpa [split] using hs ⟨true, Set.mem_univ _⟩
    show (split.outcome s).1 ∈ ({v} : Set Bool)
    simp [split, h]
  · rintro x ⟨s, hs, rfl⟩
    have h : s false = w := by simpa [split] using hs ⟨false, Set.mem_univ _⟩
    show (split.outcome s).2 ∈ ({w} : Set Bool)
    simp [split, h]

end AISafetyAtlas.Examples.Sovereignty.Governance
