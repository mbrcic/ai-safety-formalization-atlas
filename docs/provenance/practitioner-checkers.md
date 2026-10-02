# Nine new `atlas-check` kinds (2026-09-16)

`atlas-check` reads a finite model from JSON and prints a verdict together with
the declaration that certifies it. It had five kinds — `knowability`,
`coalition`, `device`, `variety`, `regulation`. It now has fourteen.

The additions exist because the atlas states its obstructions as theorems and a
consumer arrives with a model instead. A theorem is the right form for a result
and the wrong form for *"here are my acts, here is what my log records, can this
rule bind?"*

## What was added

| Kind | Question | Source |
|---|---|---|
| `unlearning` | Did removal actually remove it? | Reuel et al. **OP 84** |
| `membership` | Can it be verified what a model was trained on? | Reuel et al. **OP 45** |
| `access` | Does this redaction preserve the audit question? | Reuel et al. **OP 30/31** |
| `enforcement` | Can this rule bind, given what the log records? | Reuel et al. **OP 90/91** |
| `shield` | Synthesise a runtime safety envelope | Reuel et al. **OP 64**; Bloem et al. 2015, Humphrey et al. 2019 |

Reuel, Bucknall et al. is a **directory**: it states 99 questions and no theorem,
so nothing here is graded against it and it is not in the coverage audit. The
atlas answered 8 of the 99 before this change.

## The first three are one search under three readings

`unlearning`, `membership` and `access` all run
`Knowledge.Check.findCollision`, which already backed three kinds. They are
separate kinds anyway, and the reason is the content:

**The same collision is success for one party and failure for another.** For
unlearning, a collision between a world where the fact was retained and a world
where it never existed is the *success condition* — the released evidence cannot
tell them apart. For membership, the identical collision is the verifier's
failure. A checker that printed one verdict for both would leave the reader to
work out which, and that is the half worth saying out loud.

`access` runs the search twice, at the level being narrowed and at what would
actually be released, because the practitioner's decision has three outcomes and
not two. A question that already fails at full access was not broken by the
redaction, and reporting it as a redaction failure would send the reader to fix
the wrong thing.

## Two new library modules, and why their positive branches matter

Every checker in this repository before today answered a negative question: it
returned a witness, or nothing. Both new ones return an **artifact** when the
search is clean.

**`Sovereignty.EnforcementCheck`.** `sanctionOf` is the monitoring rule anyone
would write down — flag an observation exactly when some forbidden act produces
it. `enforces_sanctionOf_of_findUnenforceable_eq_none` proves *that rule*
enforces the norm whenever the search finds no collision. So an enforceable
regime gets the monitor back, already checked, rather than a verdict about
monitors. It is constructive for a specific reason: the obstruction is a
collision, and the absence of one is exactly what makes the obvious rule correct.

**`Sovereignty.ShieldCheck`.** The interesting design decision is that the
fixpoint iteration is **untrusted**. A shield synthesiser normally owes a proof
that its downward iteration converges to the greatest controlled-invariant set.
This one owes nothing: it computes a candidate, then checks two decidable
conditions on the result, and `subset_safetyKernel` — the Knaster–Tarski
direction, already in `SafetyGame` — turns that check into membership of the
kernel. Checking a certificate is sound whatever produced it.

`exists_maintaining_of_isShield` then carries membership to a positional
controller that holds for all time, through
`mem_safetyKernel_iff_exists_maintaining`. The output is a state-to-action table:
something to install.

## What is not claimed

**Shield completeness.** Nothing says the returned envelope is the largest. A
smaller envelope refuses more often than it must, which is safe and not wrong,
and an empty result is a limit of the search rather than a finding that the
system cannot be shielded.

**Enumeration scope.** Both checkers take their enumeration as an argument and
`hcomplete` as a hypothesis. A caller who passes a partial list gets an answer
about the acts or states on that list.

**Adversarial answers.** `cpre` quantifies over every answer, so a model that
gives the environment fewer answers than reality does will certify a shield that
does not hold. That is a modelling error the checker cannot see.

**Layer 4.** Whether a real log schema is `observe`, a real rule is `forbidden`,
or real dynamics are `step`, is an assignment this repository does not make —
here or anywhere.

## Witnesses

`AISafetyAtlas/Examples/Sovereignty/Checkers.lean` runs **both branches of
both** new checkers: a rule the log defeats and the same rule under a log that
records the act; an envelope that certifies and a system with none. A checker
whose positive branch nobody has seen succeed is a checker nobody has seen.

## Added later the same day

| Kind | Question |
|---|---|
| `conformity` | Does passing the checklist mean the system can be run? |
| `fairness` | Which of calibration and the two balances must fail here? |
| `goodhart` | Is this threshold already outside its own evidence base? |
| `refusal` | Does your safety suite admit a do-nothing pass? |

`refusal` is the only kind in the family whose **both** verdicts carry an
agreement theorem. The others are one-sided by design, because their negative
answer quantifies over systems or over rules and the search cannot settle it.
This one is a finite search over outcomes with no such quantifier inside, so
`exists_refusal_hole_of_admitsRefusal` and
`not_exists_refusal_hole_of_admitsRefusal_eq_false` cover both branches — and the
question needs no system at all, since the defect is a property of the suite.

Six more bridges landed with them: `Sovereignty.Refusal`,
`Sovereignty.AmendmentLog`, `Fairness.Tradeoff`, `Control.OversightBudget`,
`Compositional.AgentNetwork` and `Knowledge.IncidentCount`. The
`certify-versus-act` reading that was on the same shortlist was **dropped as
duplication**: `LAND-KNOW-UNIFORM-001` already bridges "acting acceptably without
identifying the state", and a second module saying it from the monitoring side
would have been a rename.
