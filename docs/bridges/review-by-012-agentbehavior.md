# Bridge review — BY-012 AgentBehavior / Verification.rice

**Registry status:** `REVIEWED` (2026-07-19).  
**Statement:** accepted. **Interpretation:** accepted (scoped; see allowed claim).  
**Scope of row status:** `REVIEWED` documents the **AI-facing bridges**
`Verification.rice` and `AgentBehavior.no_behavioral_safety_verifier`, not a
re-audit of Mathlib’s classical Rice proofs as novel AI-safety content.

## Reviewer

- **Name:** Mario Brčić (mbrcic)
- **Date:** 2026-07-19
- **Scope:**
  `AISafetyAtlas.Verification.AgentBehavior.no_behavioral_safety_verifier` and
  `AISafetyAtlas.Verification.rice`.

## Statement review (accepted)

| Item | Location | Outcome |
|---|---|---|
| Agent model | `Agent` = Mathlib `Code` / partial I/O | Accepted |
| Safety specification | `SafetySpec` = extensional set of behaviors | Accepted |
| Nontriviality | `SpecNontrivial` = `Verification.Nontrivial` | Accepted |
| Verifier | Total computable Bool, sound and complete on all codes | Accepted |
| Theorem | No such verifier for nontrivial specs | Accepted |
| Proof | Through `Verification.rice` → Mathlib `rice₂` | Accepted |
| Public API shape | `Examples/PublicAPI.lean` | Accepted |

Exclusions at statement layer: particular deployed systems; non-extensional or
non-I/O properties; incomplete verifiers; claim that every practical safety
property is a `BehavioralProperty`.

## Interpretation review (accepted)

| Field | Value |
|---|---|
| Decision | `ACCEPT` |
| Decision date | 2026-07-19 |
| Decision notes | Scoped implementation |

### Intended systems (mapping)

AI-safety packaging of classical Rice, not a theorem about a named product.

**In-scope modeling class:** systems *deliberately modeled* as:

- an **encoded agent** = program code with partial map `ℕ →. ℕ`;
- a **safety specification** = extensional set of acceptable partial I/O
  behaviors;
- a **safety question** of the form: does this agent’s behavior lie in the
  specification?

**Out of scope unless separately argued:** neural nets, LLMs, robots, or
deployed products without an explicit encoding into that program model;
multi-agent norms; intent; deception; non-extensional or non-behavioral
properties.

### Allowed claim (accepted)

> If agents are modeled as partial recursive programs and a safety property is a
> nontrivial extensional set of partial input/output behaviors, then there is no
> total computable procedure that correctly decides, for every program code,
> whether that agent satisfies the property. Equivalently: a sound-and-complete
> total behavioral safety verifier for all encoded agents cannot exist for any
> nontrivial such specification. This is Rice’s theorem under an agent /
> safety-spec vocabulary (`AgentBehavior.no_behavioral_safety_verifier` via
> `Verification.rice`). Melo et al. (arXiv:2408.08995; `atlas-ref-melo-2024`,
> `LAND-MELO-001`) use a comparable agent/program and non-trivial I/O-judge
> setup; see
> [`related-literature.md`](../guide/related-literature.md).
> The atlas formalizes the Rice packaging, not that paper’s full narrative or
> architecture recommendations.

### Forbidden claims (not licensed by `REVIEWED`)

1. Undecidability of alignment, safety, or value loading as informal goals,
   without the encoded agent/program model and property class above.
2. That a named deployed system is unverifiable or unsafe.
3. That testing, red-teaming, monitoring, runtime enforcement, type systems, or
   restricted program classes are pointless or impossible.
4. That incomplete but sound methods, or complete methods on a decidable
   fragment, are ruled out.
5. That every property of interest to AI safety is an extensional I/O
   `BehavioralProperty`.
6. That humans or organizations cannot make justified safety judgments outside
   a total algorithmic verifier.

### Misuse tests (blocked)

| Misread | Why blocked |
|---|---|
| Blanket claim that “alignment” (unspecified) is undecidable | Only total decision of nontrivial extensional I/O properties on all codes is formalized. |
| “Company X’s model cannot be verified.” | No encoding into `Code` / `eval` is assumed or proved. |
| “Red-teaming is pointless.” | Incomplete, empirical, and restricted methods are outside the verifier class. |
| “No safety property can be decided.” | Only **nontrivial** specs; trivial specs are decidable in the Rice sense. |

### Survey row

- BY-012 informal claim remains **Rice’s theorem** (mathematics).
- AgentBehavior is a vocabulary bridge, not a new Table-1 theorem or coverage
  upgrade.
- Robot (BY-033) is a separate `RELATED` bridge.

## Registry recording

```json
"ai_bridge_status": "REVIEWED",
"bridge_review": {
  "reviewer": "Mario Brčić (mbrcic)",
  "date": "2026-07-19",
  "statement_reviewed": true,
  "interpretation_reviewed": true,
  "evidence": "docs/bridges/review-by-012-agentbehavior.md"
}
```
