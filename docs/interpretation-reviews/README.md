# Bridge reviews

A bridge is a Lean declaration graded `type: BRIDGE` — layer 3 of
[`ledger-coverage.md`](../agent/policy/ledger-coverage.md), the layer that states
an AI-safety reading over an AI-system model. **Layer 3 needs human review**, so
every one of these declarations needs a signature before its reading may be
cited.

**37 bridges. 3 signed. 34 open.**

## One bridge, one label

The label lives on the **declaration**, in `registry.yaml`, as `review_status`
plus a `review` record:

```json
{ "atlas_declaration": "AISafetyAtlas.Sovereignty.Refusal.safety_suite_admits_a_refusal",
  "type": "BRIDGE",
  "review_status": "REVIEWED",
  "review": { "reviewer": "...", "date": "...", "statement_reviewed": true,
              "interpretation_reviewed": true, "evidence": "docs/interpretation-reviews/..." } }
```

Not on the row. A registry row is too wide a unit: `LAND-SOV-AUTH-001` owns four
bridges — about shutdown channels, attestations and delegation chains — and one
status on the row cannot say which of the four a human signed. A row's own
`ai_interpretation_status` still means what it always meant: whether that row's
`informal_claim` has a signed AI reading. Different question, different field.

`scripts/validate_registry.py` enforces it: every `BRIDGE` carries a
`review_status`; a graduated one needs a complete record; the evidence must be a
file that exists under this directory; and a non-`BRIDGE` declaration may not
carry either field.

## How to sign one

1. Open the bridge's file below. Each has the same five parts: the Lean
   statement, **what to check** (the two to four things specific to that
   declaration), the **allowed claim**, the **forbidden claims**, and **misuse
   tests** that must be blocked.
2. Fill in the decision block at the top.
3. I transcribe it onto the declaration.

Two verdicts, and the weaker one is a real answer:

- **`STATEMENT_REVIEWED`** — the Lean says what the file says it says; you are
  not signing the AI reading. Policy prefers this over overclaiming.
- **`REVIEWED`** — statement and interpretation both.

**Rejecting costs nothing.** The declaration stays correct; what is withdrawn is
the `BRIDGE` grade and the allowed claim.

## Five worth opening first

Not the biggest — the ones where the answer is least obvious.

| Bridge | Why |
|---|---|
| [`gameFormAcyclic_iff`](review-gameformacyclic-iff.md) | `Iff.rfl`. Keiding's two theorems are not carried — but the blocker is the **core**, not the profiles, so *hold it open and build the core* is a third verdict beside accept and reject |
| [`count_is_not_a_measurement`](review-count-is-not-a-measurement.md) | the newest row; the proof is `congrArg` and what the declaration adds is the reframing from decoders to published numbers |
| [`access_is_not_what_separates_them`](review-access-is-not-what-separates-them.md) | the one whose false reading — *"verification is impossible even with full access"* — travels furthest |
| [`no_procedure_on_output_recovers_fallback`](review-no-procedure-on-output-recovers-fallback.md) | the only one where an over-reading becomes a claim about people, against a cited empirical finding |
| [`not_uniformlyActionable_iff_exists_unservable`](review-not-uniformlyactionable-iff-exists-unservable.md) | newly graded; check that the pairwise certificate really is insufficient, because a reviewer who accepts `ActionConflict` as the test will pass a system with no uniform policy |

**Two re-grades were applied on 2026-09-16** rather than left as review
questions, both moving a grade off a declaration that proves nothing:
`Knowledge.knowable_iff_uniformlyActionable` (`Iff.rfl`) → `WRAPPER`, with the
grade moved to the certificate above; and `SocialChoice.Utility.arrow` →
`WRAPPER`, since it moves between two mathematical presentations rather than
stating a reading over an AI-system model. `BY-007` now carries no bridge.

## All 37

| Bridge | Row | Status | |
|---|---|---|---|
| `Control.OversightBudget.oversight_reduction_le_budget` | `BY-005` | unsigned | [review](review-oversight-reduction-le-budget.md) |
| `Verification.Containment.harming_undecidable` | `BY-025` | unsigned | [review](review-harming-undecidable.md) |
| `Compositional.AgentNetwork.symmetry_is_the_shared_cause` | `BY-043` | unsigned | [review](review-symmetry-is-the-shared-cause.md) |
| `Knowledge.Access.whiteBox_determines_blackBox` | `LAND-ACCESS-ORDER-001` | unsigned | [review](review-whitebox-determines-blackbox.md) |
| `Knowledge.Access.no_blackBox_methodology` | `LAND-ACCESS-ORDER-001` | unsigned | [review](review-no-blackbox-methodology.md) |
| `Knowledge.Access.exists_indistinguishable_behaviour` | `LAND-ACCESS-ORDER-001` | unsigned | [review](review-exists-indistinguishable-behaviour.md) |
| `Knowledge.Audit.audit_certifies_audited_not_deployed` | `LAND-AUDIT-LAG-001` | unsigned | [review](review-audit-certifies-audited-not-deployed.md) |
| `Knowledge.Audit.later_audit_does_not_close_the_gap` | `LAND-AUDIT-LAG-001` | unsigned | [review](review-later-audit-does-not-close-the-gap.md) |
| `Oversight.JointObservation.consortium_covers_of_registry_covers` | `LAND-AUDIT-REGISTRY-001` | unsigned | [review](review-consortium-covers-of-registry-covers.md) |
| `Oversight.JointObservation.not_registry_covers_of_emit_collision` | `LAND-AUDIT-REGISTRY-001` | unsigned | [review](review-not-registry-covers-of-emit-collision.md) |
| `Compositional.Hyperproperties.Evaluation.traceProperty_knowable_of_score_decides` | `LAND-EVAL-BLINDSPOT-001` | unsigned | [review](review-traceproperty-knowable-of-score-decides.md) |
| `Compositional.Hyperproperties.Evaluation.sampling_misses_subsingleton` | `LAND-EVAL-BLINDSPOT-001` | unsigned | [review](review-sampling-misses-subsingleton.md) |
| `Goodhart.RegulatoryTarget.certified_systems_were_never_examined` | `LAND-GOODHART-REGTARGET-001` | unsigned | [review](review-certified-systems-were-never-examined.md) |
| `Goodhart.RegulatoryTarget.risk_unconstrained_on_certified` | `LAND-GOODHART-REGTARGET-001` | unsigned | [review](review-risk-unconstrained-on-certified.md) |
| `Goodhart.RegulatoryTarget.raising_the_bar_does_not_help` | `LAND-GOODHART-REGTARGET-001` | unsigned | [review](review-raising-the-bar-does-not-help.md) |
| `Knowledge.IncidentCount.count_is_not_a_measurement` | `LAND-INCIDENT-COUNT-001` | unsigned | [review](review-count-is-not-a-measurement.md) |
| `Knowledge.not_uniformlyActionable_iff_exists_unservable` | `LAND-KNOW-UNIFORM-001` | unsigned | [review](review-not-uniformlyactionable-iff-exists-unservable.md) |
| `Oversight.forces_of_constant_effect` | `LAND-OVERSIGHT-VARIETY-001` | unsigned | [review](review-forces-of-constant-effect.md) |
| `Oversight.forces_of_constant_effect_of_not_knowable` | `LAND-OVERSIGHT-VARIETY-001` | unsigned | [review](review-forces-of-constant-effect-of-not-knowable.md) |
| `Sovereignty.CapabilityAssessment.no_procedure_on_output_recovers_fallback` | `LAND-SOV-ASSESSMENT-001` | unsigned | [review](review-no-procedure-on-output-recovers-fallback.md) |
| `Sovereignty.CapabilityAssessment.protocols_are_incomparable` | `LAND-SOV-ASSESSMENT-001` | unsigned | [review](review-protocols-are-incomparable.md) |
| `Sovereignty.CapabilityAssessment.withdrawal_settles_and_no_output_procedure_does` | `LAND-SOV-ASSESSMENT-001` | unsigned | [review](review-withdrawal-settles-and-no-output-procedure-does.md) |
| `Sovereignty.ShutdownChannel.obedience_does_not_give_authority` | `LAND-SOV-AUTH-001` | unsigned | [review](review-obedience-does-not-give-authority.md) |
| `Sovereignty.Attestation.attestation_is_not_the_claim` | `LAND-SOV-AUTH-001` | unsigned | [review](review-attestation-is-not-the-claim.md) |
| `Sovereignty.Attestation.properties_are_independent` | `LAND-SOV-AUTH-001` | unsigned | [review](review-properties-are-independent.md) |
| `Sovereignty.DelegationChain.power_over_a_matter_does_not_compose` | `LAND-SOV-AUTH-001` | unsigned | [review](review-power-over-a-matter-does-not-compose.md) |
| `Sovereignty.Conformity.passes_every_check_and_not_operable` | `LAND-SOV-CATALOGUE-001` | unsigned | [review](review-passes-every-check-and-not-operable.md) |
| `Sovereignty.AmendmentLog.unbroken_chain_is_not_a_constraint` | `LAND-SOV-CONST-001` | unsigned | [review](review-unbroken-chain-is-not-a-constraint.md) |
| `Sovereignty.Enforcement.undetectable_norm_is_unenforceable` | `LAND-SOV-DEONTIC-001` | unsigned | [review](review-undetectable-norm-is-unenforceable.md) |
| `Sovereignty.Refusal.safety_suite_admits_a_refusal` | `LAND-SOV-SERVICE-001` | unsigned | [review](review-safety-suite-admits-a-refusal.md) |
| `Sovereignty.gameFormAcyclic_iff` | `LAND-SOV-STABILITY-001` | unsigned | [review](review-gameformacyclic-iff.md) |
| `Verification.FullAccess.no_fullAccessVerifier_of_extensional` | `LAND-VERIF-FULLACCESS-001` | unsigned | [review](review-no-fullaccessverifier-of-extensional.md) |
| `Verification.FullAccess.fullAccessVerifier_exactArtifact` | `LAND-VERIF-FULLACCESS-001` | unsigned | [review](review-fullaccessverifier-exactartifact.md) |
| `Verification.FullAccess.access_is_not_what_separates_them` | `LAND-VERIF-FULLACCESS-001` | unsigned | [review](review-access-is-not-what-separates-them.md) |
| `Oversight.not_forces_of_card_lt` | `BY-004` | **`REVIEWED` 2026-08-17** | [package](review-oversight-varietybound.md) |
| `Verification.rice` | `BY-012` | **`REVIEWED` 2026-07-19** | [package](review-by-012-agentbehavior.md) |
| `Verification.Robot.action_safety_unverifiable` | `BY-033` | **`REVIEWED` 2026-07-19** | [package](ct3-robot-review-package.md) |

## Not a bridge review

- [`review-by-044-selfawareness.md`](review-by-044-selfawareness.md) — `BY-044`'s
  claim row is `STATEMENT_REVIEWED`; the encoded statement is accepted and the
  AI-system interpretation is withheld because none has been proposed. That is a
  row-level record about an `informal_claim`, not a bridge.

## Every bridge has a row

`AISafetyAtlas.Knowledge.IncidentCount` used to be the exception — bridge-hood
declared in its module docstring, no registry entry, so invisible to the count
and unlabelled. `LAND-INCIDENT-COUNT-001` was written on 2026-09-16 and it is in
the table above. A module whose docstring opens with the bridge paragraph and
which carries no `BRIDGE` declaration is a defect; that is the check to repeat
when a new bridge module lands.
