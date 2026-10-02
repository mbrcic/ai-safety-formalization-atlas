# Bridge review — `Sovereignty.CapabilityAssessment.no_procedure_on_output_recovers_fallback`

**Row `LAND-SOV-ASSESSMENT-001` · module `AISafetyAtlas/Sovereignty/CapabilityAssessment.lean` · `HUMAN_REVIEW`**

Siblings: [`protocols_are_incomparable`](review-protocols-are-incomparable.md),
[`withdrawal_settles_and_no_output_procedure_does`](review-withdrawal-settles-and-no-output-procedure-does.md).

**This row is the one where an over-reading becomes a claim about people.**
Context source: *International AI Safety Report 2026* (chair: Yoshua Bengio),
§2.3.2.

## Decision

| | |
|---|---|
| Verdict | ☐ `REVIEWED` ☐ `STATEMENT_REVIEWED` ☐ rejected — drop the `BRIDGE` grade |
| Reviewer | |
| Date | |
| Note | |

## The statement

```lean
public theorem no_procedure_on_output_recovers_fallback {R : Type u} [Ring R]
    {K : Sort*} {x y : R} (hxy : x ≠ y) (report : R → K) :
    ¬ Knowable (fun state : R × R => report (outputProtocol R state))
      (fallbackCapability (R := R))
```

The state is a pair: unaided capability and what is borrowed.
`outputProtocol` reads the assisted output — the sum.

## What to check

1. **`report` is arbitrary.** Any statistic, rubric, satisfaction score,
   productivity metric or summary computed from assisted output. This is
   `not_knowable_comp`, and it makes the obstruction structural rather than an
   instrument-quality complaint.
2. **The decomposition `output = fallback + borrowed` is itself a model.** A
   setting where assistance and capability do not compose additively is not this
   one.
3. **Self-report is not covered.** The theorem applies to a report **if** it is a
   function of assisted output. Whether someone's self-assessment is such a
   function is a layer-4 premise — plausible, **not established here**. The
   empirical literature describes a *bias* mechanism; this describes
   *non-invertibility*. Compatible, different, neither implies the other.

## Allowed claim

> Where assisted performance is the sum of unaided capability and what is
> borrowed, no instrument computed from assisted output recovers unaided
> capability, at any level of sophistication, because the evidence does not
> contain the answer.

## Forbidden

- **Not** that any deployed system causes cognitive offloading. Nothing here is
  evidence of decline, and the report's own caveat travels with every use of the
  6% figure: *"research into the relationship between use of AI and cognitive
  offloading and critical thinking is nascent, and further studies supporting
  these findings are warranted."*
- **Not** that decline is affine. `AffineCapability` is in the layer-2 module and
  is deliberately **not used**; its own docstring calls it *"a selected model, not
  a law"*.
- **Not** a practice policy. No quantity, schedule or intervention follows.
- **Not** a claim about any individual or profession.

## Misuse tests

| Attempted use | Blocked because |
|---|---|
| "Formal proof that AI assistance degrades clinicians." | the theorems are about measurement, not about change |
| "Productivity metrics show staff capability is intact." | this is exactly the refused inference |
| "Ask people to self-assess instead." | conditional on self-report being a function of assisted output — unestablished, and named as such |

## Witness

`AISafetyAtlas/Examples/Sovereignty/CapabilityAssessment.lean`, with `x ≠ y`
inhabited.
