# Bridge review — `Sovereignty.ShutdownChannel.obedience_does_not_give_authority`

**Row `LAND-SOV-AUTH-001` · module `AISafetyAtlas/Sovereignty/ShutdownChannel.lean` · `HUMAN_REVIEW`**

Siblings on this row, signed separately:
[`attestation_is_not_the_claim`](review-attestation-is-not-the-claim.md),
[`properties_are_independent`](review-properties-are-independent.md),
[`power_over_a_matter_does_not_compose`](review-power-over-a-matter-does-not-compose.md).

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem obedience_does_not_give_authority {c : Cmd}
    (hlive : R.effect c ≠ R.idle) :
    (∀ c', run R true c' = R.effect c') ∧
      ¬ ∀ deliver : Bool, run R deliver c = R.effect c
```

`RelayedCommand` is the weakest model of an instruction reaching its target
through something else: commands, their effects, and an `idle` outcome for a
command that never arrives.

## What to check

1. **The first conjunct must be *true*, not a modelling slip.** Whenever the
   instruction is delivered, the outcome is exactly the instruction. That is
   everything an observer of compliant episodes sees, and the result is that this
   truth carries no authority. **The gap between the conjuncts is the entire
   content.**
2. **`hlive` rules out the degenerate command** whose effect is idling anyway.
   Check it is not doing hidden work beyond that.
3. **The model is single-shot**: no time, no retries, no penalty for withholding,
   no observation of whether delivery occurred. A real design defeats this by
   adding exactly those, and none is modelled. `relay_forces_idle` (not graded)
   says where the power went — this is a **transfer**, not a diffusion.

## Allowed claim

> An arrangement can obey every delivered command indefinitely while the
> principal has no guarantee for any command whose effect differs from idling:
> behavioural compliance is compatible with no authority whatsoever, and the
> power sits with whatever can decline delivery.

## Forbidden

- **Not** "shutdown switches do not work." A channel the principal controls
  end-to-end is not an instance — which is the useful form: it names the property
  an arrangement must establish, that no party between the principal and the
  effect can decline delivery.
- **Not** a claim that any real oversight arrangement has this shape.
- **Not** about retries, escalation, or detection of withholding.
- **Not** an assignment of `idle` to "the system keeps running".

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "We tested the kill switch and it stopped, so we have control." | this is the first conjunct, and the theorem is precisely the refusal of the inference |
| "Human-oversight requirements are unsatisfiable." | no retries, no receipts, no penalties are modelled; a controlled channel is not an instance |
| "So the relay is adversarial." | nothing about intent; declining delivery needs no motive here |

## Witness

`AISafetyAtlas/Examples/Sovereignty/Governance.lean`; also
`Examples/DeployedAssistant.lean`.
