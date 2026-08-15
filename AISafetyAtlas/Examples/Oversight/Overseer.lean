module

public import AISafetyAtlas.Examples.Knowledge.Devices

/-!
# An overseer that may reconfigure, and a monitor that may not

Every other model in `Examples/` exists to show that some definition is not
vacuous. This one is a job: **does letting the overseer reconfigure recover a
hazard bit the monitor cannot read?**

The question is worth asking because the two capabilities are graded by different
predicates, and the atlas has both. A monitor reads a fixed channel and must
decode the hazard from it with one rule that works everywhere — that is
`Knowledge.Knowable`. An overseer may pose each question in a configuration of
its choosing — that is Wolpert's Definition 3, `WeaklyInfers`. Neither implies
the other, so the answer is not available by inspection.

## The system

Four states. Two are configurations the overseer can be in, and within each
configuration the hazard is either present or absent:

| State | Configuration | Hazard |
|---|---|---|
| `0` | `0` | absent |
| `1` | `0` | present |
| `2` | `1` | absent |
| `3` | `1` | present |

The configuration on its own therefore says nothing about the hazard, by
construction. The two overseers below differ only in what they report.

## The answer, both ways

**Reconfiguration can help — and the report stream still does not.** The first
overseer answers every probe of the hazard: asked whether the hazard is present
it configures to `0` and is right at both states there, asked whether it is
absent it configures to `1` and is right at both states there. It satisfies
Definition 3 exactly.

Yet **its output alone does not determine the hazard**: two states on which it
reports the same thing differ in hazard, so no decoder over its report stream is
correct everywhere. An overseer that *knows*, in Wolpert's sense, can emit a
stream from which the fact cannot be recovered. That is the quantifier
alternation made concrete, and it is the reason the atlas refuses to package one
predicate as the other.

Read as a design law: **logging what an overseer concluded is not the same as
being able to reconstruct what it concluded about.**

**Reconfiguration cannot help when the report is a function of the
configuration.** The second overseer reports one bit per configuration — the
shape of a monitor that summarizes its own setting rather than reading the world.
Then no configuration resolves the hazard, no reconfiguration schedule does
either, and no context `W` turns the output into physical knowledge. One
certificate settles all three, via
`Knowledge.Devices.blockwiseCollision_of_knowable_concl`, whose two hypotheses
are inspectable without mentioning probes at all.

## Non-claims

Four states, two configurations, one bit. No AI system is described, no bridge is
claimed, and nothing here is a statement about any deployed monitor. The reading
above is a reading of this model.
-/

namespace AISafetyAtlas.Examples.Oversight.Overseer

open AISafetyAtlas.Inference
open AISafetyAtlas.Knowledge
open AISafetyAtlas.Knowledge.Devices
open AISafetyAtlas.Examples.Inference.Enumerable

/-! ## The system -/

/-- The configuration the overseer is in: states `{0,1}` and `{2,3}`. -/
public def config : Fin 4 → Fin 2 := fun i => ⟨i.val / 2, by omega⟩

/-- Whether the hazard is present. Independent of the configuration. -/
public def hazard : Fin 4 → Bool := fun i => i.val % 2 = 1

/-- The configuration alone never determines the hazard: each configuration
occurs with the hazard present and with it absent. -/
public theorem config_says_nothing :
    ¬ Knowable config hazard :=
  not_knowable_of_collision (observation := config) (property := hazard)
    (ω₁ := 0) (ω₂ := 1) (by decide) (by decide)

/-! ## Overseer A — reads the world, answers every probe -/

/-- Reports the hazard in configuration `0` and its negation in configuration
`1`. Its report is **not** a function of the configuration. -/
public def reportA : Fin 4 → Bool := fun i => if i.val < 2 then hazard i else !hazard i

/-- Overseer A as enumerable data. -/
public def overseerA : FinDevice 4 2 where
  setup := config
  concl := reportA
  concl_surj := by decide

/--
**Reconfiguration recovers the hazard.** Overseer A satisfies Definition 3: it
answers the probe of *present* from configuration `0` and the probe of *absent*
from configuration `1`.
-/
public theorem overseerA_weaklyInfers :
    WeaklyInfers overseerA.toDevice hazard := by
  decide

/--
**And its report stream does not.** States `1` and `2` produce the same report
and differ in hazard, so no decoder over the report is correct at both.

This is the non-obvious half. Definition 3 is satisfied and the output is still
undecodable, because Definition 3 lets the overseer pick *which* configuration
answers each question, while a decoder must work in all of them at once.
-/
public theorem overseerA_report_not_knowable :
    ¬ Knowable reportA hazard :=
  not_knowable_of_collision (observation := reportA) (property := hazard)
    (ω₁ := 1) (ω₂ := 2) (by decide) (by decide)

/-- The two capabilities therefore come apart on one system, in the direction
that matters: the overseer answers, the log does not. -/
public theorem overseerA_answers_but_log_does_not :
    WeaklyInfers overseerA.toDevice hazard ∧ ¬ Knowable reportA hazard :=
  ⟨overseerA_weaklyInfers, overseerA_report_not_knowable⟩

/-! ## Overseer B — reports its configuration, and is blind -/

/-- Reports one bit per configuration. This is the restriction: the report
factors through the setup. -/
public def reportB : Fin 4 → Bool := fun i => 2 ≤ i.val

/-- Overseer B as enumerable data. -/
public def overseerB : FinDevice 4 2 where
  setup := config
  concl := reportB
  concl_surj := by decide

/-- B's report is a function of its configuration — the first hypothesis of the
transport, exhibited by naming the decoder. -/
public theorem reportB_knowable_from_config :
    Knowable overseerB.toDevice.setup overseerB.toDevice.concl :=
  ⟨fun x => x = 1, by decide⟩

/-- No configuration resolves the hazard — the second hypothesis. -/
public theorem overseerB_no_configuration_resolves :
    ∀ x : Fin 2, overseerB.toDevice.Realized x →
      (∃ u : Fin 4, overseerB.toDevice.setup u = x ∧ hazard u = true) ∧
        (∃ u' : Fin 4, overseerB.toDevice.setup u' = x ∧ hazard u' ≠ true) := by
  decide

/-- The certificate the transport consumes. -/
public theorem overseerB_blockwiseCollision :
    BlockwiseCollision overseerB.toDevice hazard true :=
  blockwiseCollision_of_knowable_concl reportB_knowable_from_config
    overseerB_no_configuration_resolves

/-- **No reconfiguration recovers the bit.** -/
public theorem overseerB_not_weaklyInfers :
    ¬ WeaklyInfers overseerB.toDevice hazard :=
  overseerB_blockwiseCollision.not_weaklyInfers isProbe_id ⟨1, by decide⟩

/-- **And no context turns the output into physical knowledge**, for any `W`
whatsoever — the refutation never inspects the context. -/
public theorem overseerB_not_physicallyKnows (W : Set (Fin 4)) :
    ¬ PhysicallyKnows overseerB.toDevice hazard true W :=
  overseerB_blockwiseCollision.not_physicallyKnows W

/--
The whole job, in one statement: the same hazard, on the same four states, with
the same two configurations. Whether reconfiguration helps turns entirely on
whether the overseer's report is allowed to depend on more than its own setting.
-/
public theorem reconfiguration_helps_iff_report_reads_the_world :
    WeaklyInfers overseerA.toDevice hazard ∧
      ¬ WeaklyInfers overseerB.toDevice hazard :=
  ⟨overseerA_weaklyInfers, overseerB_not_weaklyInfers⟩

end AISafetyAtlas.Examples.Oversight.Overseer
