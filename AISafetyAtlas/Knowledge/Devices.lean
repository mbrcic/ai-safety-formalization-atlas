module

public import AISafetyAtlas.Knowledge
public import AISafetyAtlas.Inference.PhysicalKnowledge

/-!
# The spine–device joint: transports, not an identification

`Knowledge.Knowable` and `Inference.WeaklyInfers` answer the same informal
question — *what can be recovered from evidence* — and are **not** the same
relation. That is a theorem of this development, witnessed both ways on finite
models, and `Inference/Device.lean` says so at length. Nothing here retracts it.

What was missing is the other half: the conditions under which the two
mechanisms **do** talk to each other, as named lemmas a downstream file can
apply. Without them a theorem proved about devices cannot be used by an
oversight file except by restating it.

## The joint object

A device carries two functions on `U`, and the spine takes one observation. The
transport is to read the device's **own pair** as that observation:

`deviceObservation C w = (C.setup w, C.concl w)`

An `IndistinguishabilityWitness` for this observation is a pair of universes the
device is configured identically in and concludes identically in, on which the
target nevertheless differs. That object is what crosses the joint. Neither
component alone crosses it: a setup collision by itself refutes nothing, because
weak inference may answer the probe from a *different* block, which is exactly
the quantifier alternation the non-identification turns on.

## Direction of travel

* **Spine ⟶ device.** One witness kills one block
  (`not_blockAnswers_of_witness`). A witness in *every* realized block, straddling
  the target value, kills weak inference and physical knowledge outright
  (`BlockwiseCollision`). The physical-knowledge refutation is independent of the
  context `W`, because Definition 11's clause (i) is a condition on the whole
  selected block and not on its trace in `W`.
* **Device ⟶ spine.** A device that answers a probe in every realized block has
  its conclusion function *equal* to the probed target, so the probed target is
  knowable from the joint observation by second projection
  (`knowable_probe_of_forall_blockAnswers`).

## What is deliberately absent

There is **no** `Knowable → WeaklyInfers` lemma and there is no iff between
"no collision in a block" and that block answering. Both fail:

* knowability of the target from the setup gives no answering block, since the
  device's conclusion is fixed data and need not agree with any probe;
* a block on which the conclusion is the *negation* of the probed target is
  collision-free and answers nothing.

The countermodels for the first are `Examples.Inference.Device`, which is where
the non-identification is witnessed in both directions.

## Non-claims

This module is **atlas modelling**, not a claim of either Wolpert paper. Nothing
here is graded against a printed statement and nothing here enters the 2008 or
2018 fidelity tallies. Wolpert states no relation between his devices and a
factorization criterion; the transports below are the atlas's own.

No probability, no dynamics, no AI-system reading.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `deviceObservation` | The device's own setup-and-conclusion pair, as a spine observation |
| **Model** | `BlockAnswers` | Definition 3's inner condition, named |
| **Model** | `BlockwiseCollision` | Every realized block hides the target value from the device |
| **Transport** | `not_blockAnswers_of_witness` | A spine witness inside a block stops that block answering |
| **Transport** | `BlockwiseCollision.not_weaklyInfers` | Blockwise collisions refute Definition 3 |
| **Transport** | `BlockwiseCollision.not_physicallyKnows` | …and Definition 11, for every context |
| **Transport** | `knowable_probe_of_forall_blockAnswers` | A device answering everywhere makes the probed target knowable |
| **Boundary** | `blockAnswers_no_collision` | Answering blocks carry no witness — the converse direction, and all of it that holds |

## Axiom profile

Measured with `#print axioms`, not assumed — the same discipline
`Inference/Device.lean` reports for its own split, and for the same reason.

Every refutation and the positive transport depend on **no axioms at all**:
`not_blockAnswers_of_collision`, `not_blockAnswers_of_witness`,
`BlockwiseCollision.not_weaklyInfers`, `BlockwiseCollision.not_physicallyKnows`,
`knowable_probe_of_forall_blockAnswers`, `blockAnswers_no_collision` and
`weaklyInfers_iff_blockAnswers`.

Two exceptions, both expected. `BlockwiseCollision.witnessAt` reports `propext`,
from assembling the product equality. `BlockwiseCollision.not_weaklyInfers_classical`
reports the full classical three, because it constructs a probe — exactly where
`exists_isProbe` puts the choice. Supplying the probe yourself keeps the
refutation constructive.
-/

namespace AISafetyAtlas.Knowledge.Devices

open AISafetyAtlas.Inference

universe u v v'

variable {U : Type u}

/-! ## The joint observation -/

/--
The device's own pair, read as a spine observation: how it is configured together
with what it concludes.

This is the observation the transports below quantify over. It is *not* proposed
as the canonical observation of a device — `C.setup` alone is the paper's
`X`, and the pair is what the joint needs.
-/
@[expose] public def deviceObservation (C : InferenceDevice.{u, v} U) :
    U → C.Setup × Bool :=
  fun w => (C.setup w, C.concl w)

/-! ## The block condition, named -/

/--
The inner condition of Definition 3: the block `x` **answers** the probe `f` of
the target, in the sense that the device's conclusion agrees with the probe
throughout the block.

Naming it is the point — Definition 3 is `∀ probe, ∃ realized block, BlockAnswers`,
and every transport below is about one block.
-/
@[expose] public def BlockAnswers (C : InferenceDevice.{u, v} U) {G : Type v'}
    (Γ : U → G) (f : G → Bool) (x : C.Setup) : Prop :=
  ∀ w : U, C.setup w = x → C.concl w = f (Γ w)

/-- Definition 3, restated over `BlockAnswers`. Definitional. -/
public theorem weaklyInfers_iff_blockAnswers (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) :
    WeaklyInfers C Γ ↔
      ∀ (γ : G) (f : G → Bool), IsProbe f γ → (∃ w : U, Γ w = γ) →
        ∃ x : C.Setup, C.Realized x ∧ BlockAnswers C Γ f x :=
  Iff.rfl

/-! ## Spine ⟶ device -/

/--
**One witness kills one block.** If the device is configured the same way and
concludes the same thing at two universes on which the probed target differs,
then that block does not answer that probe.

Constructive, and the whole content of the joint: both components of
`deviceObservation` are used, and neither alone suffices.
-/
public theorem not_blockAnswers_of_collision
    {C : InferenceDevice.{u, v} U} {G : Type v'} {Γ : U → G} {f : G → Bool}
    {x : C.Setup} {u u' : U}
    (hu : C.setup u = x) (hu' : C.setup u' = x)
    (hconcl : C.concl u = C.concl u')
    (hdiff : f (Γ u) ≠ f (Γ u')) :
    ¬ BlockAnswers C Γ f x :=
  fun h => hdiff (by rw [← h u hu, ← h u' hu', hconcl])

/--
The same, consuming the spine's own negative certificate. The witness must lie
inside the block; a witness elsewhere in `U` says nothing about it.
-/
public theorem not_blockAnswers_of_witness
    {C : InferenceDevice.{u, v} U} {G : Type v'} {Γ : U → G} {f : G → Bool}
    {x : C.Setup}
    (w : IndistinguishabilityWitness (deviceObservation C) (fun t => f (Γ t)))
    (hleft : C.setup w.left = x) (hright : C.setup w.right = x) :
    ¬ BlockAnswers C Γ f x :=
  not_blockAnswers_of_collision hleft hright
    (congrArg Prod.snd w.sameObservation) w.propertyDiffers

/--
**Blockwise collision at `γ`.** Every realized block of the device contains a
pair it cannot tell apart, one of which sits at the target value `γ` and one of
which does not.

This is the hypothesis both refutations below need. Requiring the pair to
*straddle* `γ` is not slack: a pair on which the target merely differs leaves
both probes of `γ` satisfied, and refutes nothing.
-/
@[expose] public def BlockwiseCollision (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (γ : G) : Prop :=
  ∀ x : C.Setup, C.Realized x → ∃ u u' : U,
    C.setup u = x ∧ C.setup u' = x ∧ C.concl u = C.concl u' ∧ Γ u = γ ∧ Γ u' ≠ γ

/-- Each block's collision pair is a spine witness for the probed target. -/
public theorem BlockwiseCollision.witnessAt
    {C : InferenceDevice.{u, v} U} {G : Type v'} {Γ : U → G} {γ : G}
    (h : BlockwiseCollision C Γ γ) {f : G → Bool} (hf : IsProbe f γ)
    {x : C.Setup} (hx : C.Realized x) :
    Nonempty (IndistinguishabilityWitness (deviceObservation C) (fun t => f (Γ t))) := by
  obtain ⟨u, u', hu, hu', hconcl, hγ, hγ'⟩ := h x hx
  refine ⟨{ left := u, right := u', sameObservation := ?_, propertyDiffers := ?_ }⟩
  · simp only [deviceObservation, Prod.mk.injEq]
    exact ⟨hu.trans hu'.symm, hconcl⟩
  · rw [(hf (Γ u)).mpr hγ]
    intro hcontra
    exact hγ' ((hf (Γ u')).mp hcontra.symm)

/--
**Blockwise collisions refute weak inference.** Constructive: the probe is
supplied, not chosen.
-/
public theorem BlockwiseCollision.not_weaklyInfers
    {C : InferenceDevice.{u, v} U} {G : Type v'} {Γ : U → G} {γ : G}
    (h : BlockwiseCollision C Γ γ) {f : G → Bool} (hf : IsProbe f γ)
    (hγ : ∃ w : U, Γ w = γ) :
    ¬ WeaklyInfers C Γ := by
  intro hw
  obtain ⟨x, hx, hans⟩ := hw γ f hf hγ
  obtain ⟨u, u', hu, hu', hconcl, hu_eq, hu'_ne⟩ := h x hx
  refine not_blockAnswers_of_collision hu hu' hconcl ?_ hans
  rw [(hf (Γ u)).mpr hu_eq]
  intro hcontra
  exact hu'_ne ((hf (Γ u')).mp hcontra.symm)

/--
The same without supplying a probe. Classical, because constructing a probe at an
arbitrary point is where the choice sits — the same split `Inference/Device.lean`
reports for `exists_isProbe`.
-/
public theorem BlockwiseCollision.not_weaklyInfers_classical
    {C : InferenceDevice.{u, v} U} {G : Type v'} {Γ : U → G} {γ : G}
    (h : BlockwiseCollision C Γ γ) (hγ : ∃ w : U, Γ w = γ) :
    ¬ WeaklyInfers C Γ := by
  classical
  obtain ⟨f, hf⟩ := exists_isProbe (A := G) γ
  exact h.not_weaklyInfers hf hγ

/--
**Blockwise collisions refute physical knowledge, in every context.**

Definition 11's clause (i) constrains the whole selected block, not its trace in
the context `W`, so the refutation never inspects `W`. That is why the statement
quantifies over every `W` rather than fixing one — strictly stronger than
refuting one context.
-/
public theorem BlockwiseCollision.not_physicallyKnows
    {C : InferenceDevice.{u, v} U} {G : Type v'} {Γ : U → G} {γ : G}
    (h : BlockwiseCollision C Γ γ) (W : Set U) :
    ¬ PhysicallyKnows C Γ γ W := by
  rintro ⟨K⟩
  obtain ⟨u, u', hu, hu', hconcl, hu_eq, hu'_ne⟩ :=
    h K.knownBlock.1 K.knownBlock.2
  have hcu : C.concl u = true := (K.correct _ u hu).mpr hu_eq
  have hcu' : C.concl u' ≠ true := fun hc => hu'_ne ((K.correct _ u' hu').mp hc)
  exact hcu' (hconcl ▸ hcu)

/--
**The condition an engineer can actually check.** If the device's report is a
function of its own configuration, and no realized configuration separates the
value `γ` from the rest, then the blockwise collision is automatic.

Both hypotheses are inspectable without reasoning about probes: the first is
`Knowable C.setup C.concl` — the spine's own predicate, applied to the device's
two functions — and the second says every block the device can reach contains a
universe at `γ` and a universe away from it.

The first hypothesis is a genuine restriction. Definition 1 assumes **nothing**
about how setup and conclusion relate, and a device whose conclusion reads the
universe directly escapes this lemma entirely; `Examples.Oversight.Overseer`
exhibits one that answers every probe.
-/
public theorem blockwiseCollision_of_knowable_concl
    {C : InferenceDevice.{u, v} U} {G : Type v'} {Γ : U → G} {γ : G}
    (hro : Knowable C.setup C.concl)
    (hsplit : ∀ x : C.Setup, C.Realized x →
      (∃ u : U, C.setup u = x ∧ Γ u = γ) ∧ (∃ u' : U, C.setup u' = x ∧ Γ u' ≠ γ)) :
    BlockwiseCollision C Γ γ := by
  obtain ⟨decoder, hdec⟩ := hro
  intro x hx
  obtain ⟨⟨u, hu, hγ⟩, ⟨u', hu', hγ'⟩⟩ := hsplit x hx
  exact ⟨u, u', hu, hu', by rw [hdec u, hdec u', hu, hu'], hγ, hγ'⟩

/-! ## Device ⟶ spine -/

/--
**A device that answers everywhere makes the probed target knowable.**

If every realized block answers the probe, the device's conclusion function *is*
the probed target, so second projection of the joint observation decodes it.
Constructive.
-/
public theorem knowable_probe_of_forall_blockAnswers
    {C : InferenceDevice.{u, v} U} {G : Type v'} {Γ : U → G} {f : G → Bool}
    (h : ∀ x : C.Setup, C.Realized x → BlockAnswers C Γ f x) :
    Knowable (deviceObservation C) (fun t => f (Γ t)) :=
  ⟨Prod.snd, fun w => (h (C.setup w) ⟨w, rfl⟩ w rfl).symm⟩

/-- The converse direction, and all of it that holds: an answering block carries
no witness. Not an iff — see the module docstring. -/
public theorem blockAnswers_no_collision
    {C : InferenceDevice.{u, v} U} {G : Type v'} {Γ : U → G} {f : G → Bool}
    {x : C.Setup} (h : BlockAnswers C Γ f x) {u u' : U}
    (hu : C.setup u = x) (hu' : C.setup u' = x) (hconcl : C.concl u = C.concl u') :
    f (Γ u) = f (Γ u') := by
  rw [← h u hu, ← h u' hu', hconcl]

end AISafetyAtlas.Knowledge.Devices
