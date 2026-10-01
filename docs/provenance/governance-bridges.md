# Six governance bridges over the sovereignty cluster (2026-09-16)

Rows: `LAND-SOV-DEONTIC-001`, `LAND-SOV-AUTH-001`, `LAND-SOV-CATALOGUE-001`.
Witness: `AISafetyAtlas/Examples/Sovereignty/Governance.lean`.

## Why these, and why now

The sovereignty cluster carries **462 public theorems across 36 modules and 30
registry rows**, and before this change **four** declarations in it were typed
`BRIDGE`. The mathematics was done — `docs/provenance/formal-power-proposal-triage.md`
counts 63 of the proposal's 64 results closed, with no row left `SUBSTRATE` — and
the AI-safety reading of almost all of it lived in registry *prose*, inside the
`application` field of a `NEW_PROOF` declaration.

Prose in an `application` field is not layer 3. `ledger-coverage.md` is explicit:
a bridge is Lean, and `type: BRIDGE` means *that declaration* states the reading
over an AI-system model. So this change writes six of those readings as
declarations, each over a named model, each witnessed.

## What was built

| Bridge | Module | Layer-2 parent |
|---|---|---|
| An undetectable norm is unenforceable | `Sovereignty.Enforcement` | `Deontic` × `Auditability` |
| Obedience does not give shutdown authority | `Sovereignty.ShutdownChannel` | `A5`, the gate game |
| Passing every check is not operability | `Sovereignty.Conformity` | `Catalogue` |
| An attestation is not its claim | `Sovereignty.Attestation` | `A4` |
| Recorded properties imply nothing | `Sovereignty.Attestation` | `B8` |
| Power over a party is not power over a matter | `Sovereignty.DelegationChain` | `B7` |

**`Enforcement` is the one with new mathematics in it.** `Deontic` and
`Auditability` both existed and **neither imported the other**: one is about
permission and prohibition with no observations, the other about labels and
observations with no norms. The module is that edge. It also carries the
converse — an enforcement that works *is* a detector, recovered from it — so
detectability is not an accidental prerequisite but the same requirement, and a
proposal that concedes a violation is undetectable while asserting it will be
enforced is incoherent rather than optimistic.

The other five restate results the tree already had, over models it did not: a
relayed command, an assessment, an attestation record, a free coordinate.

## Two design rules applied throughout

**Both halves, always.** Every bridge that says a check fails also says what the
check does establish. `obedience_does_not_give_authority` asserts total obedience
*and* absence of authority; `passes_every_check_and_not_operable` keeps the
passing result as a hypothesis. A bridge that reported only the negative half
would read as a claim that the practice is worthless, which is not what is
proved.

**The escape is exhibited, not described.** Each obstruction is conditional, and
`Examples/Sovereignty/Governance.lean` inhabits every antecedent *and* shows a
case that escapes it where one exists:

* `blindRegime` admits no sanction of any kind; `openRegime` — the same rule
  under a monitor that sees the act — is enforced, and detectable through the
  converse. So the obstruction is a property of the channel, not of the rule.
* `haltThrough` obeys every delivered halt and gives the principal nothing, and
  `haltThrough_not_inert` shows it is not the degenerate channel that
  `undeclinable_iff_inert` says is the only escape available inside the model.
* `bitAssessment` passes both items of a two-item checklist and has no operating
  policy.
* `split_opponent_not_forces_snd_via_general` recovers the pre-existing concrete
  refutation from the general obstruction, so the two are one fact rather than a
  general statement and an unrelated example.

## What none of these do

They are layer 3. Not one of them is connected to a deployed system, a named
framework, a real monitoring stack or an actual certificate, and every module
says so in its own header. The contestable content of a governance argument is
whether a real arrangement instantiates the hypothesis — whether the log really
does merge those two acts, whether the relay really may decline — and **that
argument is not in this repository.**

Read them as refusal instruments with a stated precondition: each one names a
remedy that does not work *given its antecedent*, and names the instrument that
would. They cannot be cited to say a particular scheme is broken.

## The review record, which is a known gap

`ledger-coverage.md` requires human review at layers 3 and 4.
`ai_interpretation_status` is the field that records it, it is **mandatory on
claim rows and forbidden on artifact rows**, and all three rows here are `LAND-`
artifact rows. So these six bridges carry no review record, and there is no field
in which one could be written.

This is not an oversight in the rows. It is the schema, and it now affects the
majority of the tree's bridges. Recorded here so that the gap is disclosed rather
than discovered.
