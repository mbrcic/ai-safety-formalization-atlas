# CT-3 — Robot bridge review package

**Status:** **fully reviewed (2026-07-19)** — maintainer reviewed packaging and
**scoped interpretation**; accepts transparent **`RELATED`** formalization (not
paper EXACT; reduction core under assumed `SwitchingConstruction`).  
**Registry:** relationship **`RELATED`**; `ai_bridge_status` **`REVIEWED`**.

## Maintainer decision

| Field | Value |
|---|---|
| Decision | Reviewed; accept RELATED packaging and scoped interpretation |
| Reviewer | Mario Brčić (mbrcic) |
| Date | 2026-07-19 |
| Formalization relationship | Keep **`RELATED`** (not EXACT / EQUIVALENT) |
| Bridge status | **`REVIEWED`** — statement and interpretation accepted |
| Statement | `statement_reviewed: true` |
| Interpretation | `interpretation_reviewed: true` — scoped claim only; no claim about real robots, ethics, or law beyond the model |
| Rationale | Lean is the computability core under an explicit certificate; paper builds τ in SPA from Def. 3. That cut is intentional, transparent, and accepted after review. |

## What was reviewed

| Item | Location |
|---|---|
| Machine-checked theorem | `AISafetyAtlas.Verification.Robot.action_safety_unverifiable` |
| Model document | [`robot-verification-model.md`](../guide/robot-verification-model.md) |
| Paper | van Leeuwen & Wiedermann, UU-PCS-2021-02 (2021), Theorem 1 / Corollary 1 |
| Registry row | BY-033 (`RELATED`, `REVIEWED`) |
| Literature map | [`related-literature.md`](../guide/related-literature.md) (`related-formal`) |

## Checklist outcome

1. **Statement fidelity.** Total-trace model preserves the computability core —
   accepted as **RELATED**, not full paper statement. **Yes.**
2. **Switching certificate.** Lean assumes `SwitchingConstruction`; paper
   builds τ — **accepted as the right cut**; `RELATED` remains correct.
3. **Proof length.** Paper longer because of SPA construction — accepted.
4. **Scope exclusions.** Bounded systems, incomplete verifiers, ethics instances
   outside automatic conclusion — accepted.
5. **Interpretation.** Scoped allowed claim accepted; forbidden slogans and
   real-product overclaims remain blocked. Full informal “robot ethics
   impossible” is **not** licensed.

## Statement review (accepted)

See maintainer decision and model document. Encoded Lean packaging accepted
2026-07-19.

## Interpretation review (accepted)

| Field | Value |
|---|---|
| Decision | `ACCEPT` |
| Decision date | 2026-07-19 |
| Decision notes | Scoped interpretation; relationship stays RELATED |

### Intended systems (mapping)

The bridge is a **computability packaging** of van Leeuwen & Wiedermann’s online
observer problem for total reactive action traces—not a theorem about a named
robot product or a complete formalization of their SPA language.

**In-scope modeling class:** systems *deliberately modeled* as:

- an abstract **program** class with a predicate of “structured” programs;
- a total **behavior** assigning an action to every complete scenario and
  operational cycle (`Scenario → ℕ → Action`);
- a property **always-*P***: every action on every scenario/cycle satisfies a
  fixed `acceptable` predicate (ethics/legality are **instances** of *P*, not
  hard-coded);
- a **total computable verifier** that is sound and complete for always-*P* on
  every structured program;
- an **effective switching construction**: a computable map from source codes
  into structured programs such that always-*P* holds iff a fixed-input
  computation does not halt (the paper’s τ-style embedding, assumed not derived
  from Def. 3 inside SPA).

**Out of scope unless separately argued:** physical robots without that model;
finite-state / bounded-memory / bounded-horizon classes that cannot host the
switching construction; incomplete verifiers, monitors, testing; proof that a
particular ethical or legal code is the right `acceptable` predicate; full
Sense–Plan–Act syntax, hyper-commands, or probability in Def. 3.

### Allowed claim (accepted)

> If robot programs are modeled so that an effective switching construction
> exists (the program class can computably embed an arbitrary source computation
> while continuing to act, and switch from always-acceptable to not-always-
> acceptable behavior if that computation halts), then there is no total
> computable procedure that is sound and complete for whether every structured
> program’s total reactive action trace always satisfies a fixed action
> property *P*. This is the machine-checked core of van Leeuwen & Wiedermann
> (UU-PCS-2021-02) Theorem 1 / Corollary 1 under an explicit certificate
> (`SwitchingConstruction`); the atlas formalization is **RELATED** to the
> paper: it does not derive the construction from the paper’s Def. 3
> non-triviality inside a full SPA language. Ethics and legality appear only as
> possible choices of *P*, not as separately proved predicates.
> (`AISafetyAtlas.Verification.Robot.action_safety_unverifiable`; model note
> [`robot-verification-model.md`](../guide/robot-verification-model.md).)

### Forbidden claims (not licensed by `REVIEWED`)

1. “Robot ethics is impossible” or “legal compliance of robots is undecidable”
   as informal slogans without the model and certificate above.
2. That a named deployed robot, controller, or product is unverifiable or
   unethical.
3. That finite-state, bounded-memory, or otherwise restricted program classes
   inherit the same no-go automatically.
4. That testing, simulation, runtime monitoring, incomplete proof systems, or
   conservative certification are pointless.
5. That the paper’s full SPA / hyper-command / probability model is formalized
   in Lean, or that relationship is EXACT/EQUIVALENT.
6. That any particular ethical or legal standard is correctly captured by
   `acceptable`.
7. That after the paper drops unbounded memory, the same Lean theorem still
   applies unchanged to bounded robots (the paper itself changes setting there).

### Misuse tests (blocked)

| Misread | Why blocked |
|---|---|
| “We proved robot ethics is undecidable.” | Ethics is only a possible *P*; theorem is about total observers for always-*P* under a switching certificate. |
| “No robot can be verified safe.” | Restricted classes and incomplete methods are outside scope; certificate may fail. |
| “The atlas formalized van Leeuwen & Wiedermann exactly.” | Relationship is **RELATED**; SPA/Def. 3 construction not mechanized. |
| “Red-teaming robots is pointless.” | Empirical and incomplete methods are not total sound-and-complete verifiers. |

### Survey / coverage

- BY-033 Lean contribution is RELATED-only and does **not** raise headline
  EXACT/EQUIVALENT coverage.
- Distinct from BY-012 AgentBehavior (Rice packaging); see
  [`related-literature.md`](../guide/related-literature.md).

## Registry recording

```json
"ai_bridge_status": "REVIEWED",
"bridge_review": {
  "reviewer": "Mario Brčić (mbrcic)",
  "date": "2026-07-19",
  "statement_reviewed": true,
  "interpretation_reviewed": true,
  "evidence": "docs/bridges/ct3-robot-review-package.md"
}
```

Formalization **`relationship` stays `RELATED`.**

## Non-goals for agents

- Do not flip relationship to EXACT/EQUIVALENT without a new fidelity argument.
- Do not weaken the machine-checked statement or hide the RELATED cut.
- Do not expand interpretation beyond the allowed claim without a new review.
