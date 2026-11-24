# Fidelity grading of a printed statement against its Lean rendering: specification (v5, 2026-11-15)

You compare one **printed statement** ("print", from a published source) with the **Lean rendering** that a formal library gives for it. You record three axes: **C objects**, **A applicability** and **B conclusion**. Scope and coverage are computed from A and B (§6); you never judge them directly.

Changes from v4: print and its setting come only from the packet (§0); abstract parameters (C0a); structure fields as hypotheses (A7); derived content (§0 *Visible*); informal premises (A8); assumption targets (§7.5); several declarations combine by union (§7.3); four misread clarifications (A9, B4, C0, E4).

Follow the steps of §1 in order. Every label has a test. Apply the test literally; do not choose a label by overall impression.

## 0. Vocabulary

- **Print.** The statement as the source states it: objects, hypotheses, conclusion, quantifiers. The packet gives it transcribed from the page, with the printed context it needs, the source's definitions of the terms it uses, any proof excerpts recorded for it, and the source's standing assumptions (the *Setting* block). If the packet marks it NONE PRINTED, grade against the Atlas transcription and set `missing_context: true`. The Atlas's transcription is orientation only; where it differs from print, print wins.
- **Print's hypotheses** include (i) what the statement says, (ii) the **standing assumptions** of its source section or paper (for example "throughout, all sets are finite", "agents act on a finite MDP"), and (iii) what print's **terms mean** in the source (for example "complete control" means every outcome is reachable; dividing by log|X| presupposes |X| ≥ 2). A silent statement does not make print unrestricted: if the Setting block says the source works in a finite setting, print is finite. **(ii) and (iii) come only from the packet** (its statement, context, definitions, excerpts and Setting block), never from your memory of the source or of related literature. If a decision needs something the packet does not show, say what, and set `missing_context: true`.
- **Lean rendering.** All declarations the row cites, **taken together**.
- **Object.** A mathematical thing the statement is about or uses: a set, function, measure, agent, value, policy, game, quantity (for example "the infinite-horizon value", "the Shannon entropy", "the argmax over policies").
- **Instance.** One concrete assignment of objects that satisfies a statement's hypotheses.
- **Component.** One separately checkable part of a conclusion (each inequality, each equality, an existence clause, a uniqueness clause, a rate).
- **Visible.** Shown in the packet, or found in the provided Lean tree, or standard mathematics that a referee would accept without proof (for example: a finite set is countable; x ≤ y and y ≤ x give x = y).
- **Proved.** Established by a visible Lean declaration without `sorry`, **or derived from such declarations by steps that are each visible**: a lemma in the Lean tree or a standard identity, every one named in the reason (for example: "the chain rule H(X,Z|C) = H(X|C) + H(Z|X,C) and (30) give (31)"). A step you cannot name does not count. The same standard applies to axis A (an implication between hypotheses) and axis B (a conclusion component). A Lean hypothesis is not proved.

## 1. Procedure (do the steps in this order)

1. **Refutation check.** Does the Lean rendering prove print false (its negation, or a countermodel meeting print's hypotheses and violating its conclusion)? If yes: record `refutes: true`, skip steps 2–5, explain in `reason_B`.
2. **Axis C, objects** (§2).
3. **Axis A, applicability** (§3), hypothesis by hypothesis.
4. **Axis B, conclusion** (§4), component by component.
5. **Consistency check** (§5). If a constraint fails, revise.

## 2. Axis C: objects

For each object that print's hypotheses or conclusion mention, find the Lean object that plays its role.

| Label | Test (apply to every object; the row's label is the worst one: own < equivalent < proxy) |
|---|---|
| `own` | The Lean object is print's object: same definition up to representation (§7.1). |
| `equivalent` | The Lean object is defined differently, **and** a visible proved statement (or standard mathematics) shows it equals or corresponds one-to-one to print's object on print's instances. Name that statement in `reason_C`. |
| `proxy` | The Lean object is different and **no visible proof** shows the correspondence. This includes truncations (depth-n value for the limit value), approximations, a different but "similar" quantity, and a specific instance standing in for print's general object. |

Border rules:
- C0. **Subclass is not proxy.** If the Lean object is a special case of print's object (a subclass: only effectivity functions induced by a game form; only deterministic transitions; only finite instances), the object is `own`, and the restriction is an **applicability** difference (axis A, narrows). Judge axis B on the covered instances. Use `proxy` only when the Lean object is a *different* object, not a special case of print's.
- C0a. **Abstract parameters and interfaces.** If the Lean quantifies over an abstract parameter or interface (a structure, class or function argument) where print fixes one object, the object is `own` provided print's object is a value the parameter can take. Whether print's object meets the interface (its fields and axioms) is an axis-A question (A7), not a reason for `proxy`. Say which assignment specializes the parameter to print's object. A structure whose fields merely have suggestive names is not a specialization: the field assignments must be stated, and their properties checked under A7. Use `proxy` only when the Lean asserts that some *other* object is print's object (for example an arbitrary score claimed to be description complexity) with no visible correspondence.
- C0b. **Truncation check (E4).** Before calling a value, return or quantity `own`, check its definition for a depth, horizon or step index. A depth-n quantity standing for print's limit or infinite-horizon quantity is `proxy` unless a visible proved statement connects them (then `equivalent`).
- C1. "Probably equal" or "equal by a known theorem not in the Lean tree" is `proxy`, unless it is standard mathematics (§0 *Visible*).
- C2. A correspondence proved only under an extra hypothesis makes the object `equivalent` only if that hypothesis is among print's hypotheses; otherwise `proxy`.

## 3. Axis A: applicability (hypotheses only)

Make a two-column list: print's hypotheses and Lean's hypotheses (after translating objects via axis C). Classify each difference:

| Difference | Effect |
|---|---|
| Lean drops or weakens a hypothesis of print that print's other hypotheses do **not** imply (the theorem holds without it) | broadens |
| Lean drops a hypothesis of print that print's other hypotheses **do** imply (redundant in print) | no effect; set `leaner: true` |
| Lean generalizes a carrier (any type/field/space with the needed structure in place of print's specific one; infinite in place of finite) | broadens |
| Lean adds a hypothesis print lacks (including an unproved conjecture, an assumed bound, an assumed property, a finiteness or regularity condition) | narrows |
| Print is about a specific named object and the Lean theorem is general, but its hypotheses are never proved for that object | narrows |
| A Lean hypothesis **renders a condition that print states**, in words or symbols (quote the print phrase in reason_A) | no effect |
| A Lean hypothesis is **implied by print's hypotheses** in the sense of §0 (including standing assumptions and term meanings); state the implication in reason_A | no effect |
| A Lean hypothesis is **weaker** than the print hypothesis it replaces (every print instance satisfies it, and some non-print instance does too) | broadens |
| A hypothesis is replaced by one that is provably equivalent given the others (visible) | no effect |
| A Lean hypothesis is implied by the other hypotheses (redundant, visibly) | no effect |
| Representation change (§7.1) | no effect |

Record **every** difference in **both directions** before choosing the label. A carrier generalization (A6) still counts as broadening when another difference narrows; the result is then `incomparable`.

| Degenerate instances | Effect |
|---|---|
| The Lean also admits degenerate instances on which print's conclusion holds trivially or vacuously (the zero measure, an empty type, a zero-length run) | no effect |

Then the label:

| Label | Test |
|---|---|
| `same` | no difference has an effect |
| `broader` | at least one difference broadens, none narrows |
| `narrower` | at least one difference narrows, none broadens |
| `incomparable` | at least one broadens and at least one narrows |

Border rules:
- A1. An assumed hypothesis narrows **even if it is believed true or is a famous conjecture**, until it is proved (§0).
- A2. If you cannot see whether a Lean hypothesis is implied by the others, treat it as narrowing and set `missing_context: true`.
- A3. Never let the conclusion influence axis A.
- A5. **Quote before you narrow.** Before marking a Lean hypothesis as narrowing, check that no print phrase, standing assumption or term meaning implies it. Mark it narrowing only if you can say which print instance violates it.
- A6. **Carrier generalization is always `broader`, also in definitions.** If a definition or theorem accepts any type (any player set, any field, any countable distribution) where print fixes a specific or finite one, that difference broadens. Do not call it `same` because the defining condition is unchanged.
- A2 and A5 together. A5 governs whenever the packet shows print's hypotheses and setting: narrow only with a violating print instance in hand. A2 applies only when the packet lacks the material needed to decide; it never licenses narrowing because you did not look.
- A7. **Structure fields and class axioms are hypotheses** (with C0a). For each field or axiom the Lean requires of print's object, apply the **extension test**: if every print instance can be extended to satisfy it (say how, for example "set the unused utilities to 0"), it has no effect; if some print instance cannot, it narrows; if it is never instantiated for print's setting and you cannot say how print's instances would satisfy it, it narrows. Fields that only carry data absent from print's objects and claim may be filled in any way.
- A8. **Informal premises.** If print states a premise in words without a precise form ("many", "reasonable", "not fully rational"), give the quantified reading you use and the packet text that warrants it. Do not infer a stronger premise from the conclusion print argues for. If readings consistent with the packet give different instance sets, choose the best-warranted one for the label, state the others and the label each would give in `reason_A`, set `interpretation_sensitive: true`, and keep confidence ≤ 3. Do not narrow merely because the premise is informal.
- A9. **Graded once.** A restriction on which inputs or instances are accepted is graded on axis A only; never count it again as a missing or weaker component on axis B. A subclass (C0) narrows only if some print instance lies outside it; say which.
- A4. **Unnecessary vs redundant.** Dropping a hypothesis broadens only if the instance set really grows: some instance satisfies the Lean hypotheses but not print's. If print's other hypotheses already imply the dropped one, the instance set is unchanged: applicability is `same`, and the row is `leaner`.

## 4. Axis B: conclusion (on the instances both statements cover)

List print's conclusion components. For each, find what the Lean proves about it:

| Per component | Test |
|---|---|
| `stronger` | Lean's version implies print's and not conversely (tighter bound or constant, extra uniqueness, ∃∀ in place of ∀∃, an explicit rate where print has none) |
| `same` | equivalent (identical, definitional unfolding, algebraic rearrangement, an explicit witness for print's ∃ with no extra property) |
| `weaker` | print's version implies Lean's and not conversely (looser bound, ∀∃ in place of ∃∀, only a special case of the component) |
| `missing` | Lean proves nothing that print's component implies or is implied by |
| `incomparable` | neither implies the other (for example the claim is about a proxy object, C = proxy) |

Combine the components into the row label:

| Label | Test |
|---|---|
| `same` | every component `same` |
| `stronger` | every component `same` or `stronger`, at least one `stronger`, and Lean adds nothing that print's components contradict |
| `weaker` | every component `same`, `weaker` or `missing`, at least one `weaker` or `missing`, and at least one component is not `missing` |
| `incomparable` | at least one `stronger` and at least one `weaker`/`missing`; or any component `incomparable` |
| `none` | every component `missing` |

Border rules:
- B1. **Object rule.** If a component is about an object rated `proxy` in axis C, that component is `incomparable` (if Lean says something about the proxy) or `missing`. It is never `same` or `weaker`.
- B2. **Extras.** An extra fact about **print's own component or objects** strengthens it and counts as `stronger` (for example: when equality holds in print's inequality, an explicit rate, uniqueness of print's object). An extra fact about **objects print does not mention** does not count.
- B3. Constructive versus classical proof does not matter.
- B4. **A witness in a subclass is a witness.** For an existential or "can" component, a specific witness (even one from a narrow subclass) establishes it; specificity of the witness does not narrow axis A.

## 5. Consistency constraints

- K1. A component about a `proxy` object is `incomparable` or `missing` (B1). So if C = `proxy` for an object in print's conclusion, B cannot be `same` or `stronger`.
- K2. B = `none` ⇒ coverage `No` (§6), whatever A says.
- K3. `refutes: true` ⇒ A, B, C all null.
- K4. If you set `missing_context`, `interpretation_sensitive` or `aggregation_sensitive`, confidence ≤ 3.

## 6. Computed scope and coverage (not judged by you)

| A \ B | stronger | same | weaker | incomparable | none |
|---|---|---|---|---|---|
| **broader** | Wider | Wider | Mixed | Mixed | — |
| **same** | Wider | Same | Narrower | Mixed | — |
| **narrower** | Mixed | Narrower | Narrower | Mixed | — |
| **incomparable** | Mixed | Mixed | Mixed | Mixed | — |

Coverage: `Yes` if scope is Same or Wider; `No` if B = `none`; otherwise `Partial`.
Wider applicability never excuses a weaker conclusion: broader + weaker is Mixed.

## 7. Special cases

7.1 **Representation.** Notation, names, `Fin n` for {1,…,n}, curried vs uncurried, bundled vs unbundled structures, an exposed implicit parameter: no effect on any axis, **provided** the encoding matches instances one-to-one and preserves the claim.

7.2 **Definitions.** If print defines an object: axis C compares the defined object; axis A compares the domains (inputs accepted); axis B is `same` if the defining conditions agree on print's domain, otherwise `incomparable`.

7.3 **Several declarations.** Grade the set together. A cited declaration irrelevant to print changes nothing. **Combine alternative routes by union, not by intersecting hypotheses:** for each print conclusion component, list the cited declarations that establish it; each covers the instances that satisfy its own hypotheses, and the component is covered on the union of those instance sets. A restriction on one route does not narrow what another route already covers. An abstract route contributes only once its specialization to print (C0a, A7) is checked; a concrete instance does not discharge an abstract theorem's hypotheses for every print instance. If the union cannot be stated as one A/B pair, give a per-route account in the reasons and set `aggregation_sensitive: true`.

7.4 **Missing context.** If a decision depends on something the packet does not show, follow the conservative default named in the rule (narrowing, proxy, missing), set `missing_context: true`, and say what you would need. Do not supply it from memory (§0).

7.5 **Statement role.** Record what kind of text print is: `theorem` (an assertion: theorem, lemma, proposition, corollary, a claim in a remark), `definition` (§7.2), `assumption` (print asks the reader to assume a condition), or `explanatory` (motivation with no precise claim; grade it only after stating the mathematical claim you read in it, and set `interpretation_sensitive: true`). For an **assumption**: C compares its objects; A compares the domain on which the condition is stated; B is `same` when a Lean hypothesis states the condition where the source uses it (a faithful rendering, not a proof of the condition); ignore the other hypotheses of the enclosing declaration unless they are needed to state the condition. A **notational convention** is representation (§7.1). A clause that restricts a **parameter's domain** is graded on A only (A9). For a theorem, a matching Lean hypothesis is never a proof (§0 *Proved*).

## 8. Calibration examples (synthetic; not from the graded set)

| # | Print | Lean | C | A | B | Scope |
|---|---|---|---|---|---|---|
| E1 | For finite sets X, \|P(X)\| = 2^\|X\| | For any Fintype α, card (Set α) = 2^card α | own | same (Fintype is finite; representation) | same | Same |
| E2 | For f:[0,1]→ℝ continuous, f attains a max | For f:K→ℝ continuous, K compact nonempty | own | broader (carrier generalized) | same | Wider |
| E3 | For n ≥ 1, a_n ≤ 2/n | For n ≥ 1, a_n ≤ 1/n | own | same | stronger | Wider |
| E4 | V* = sup over policies of the infinite-horizon value; V* satisfies Bellman's equation | The depth-n value V_n satisfies the depth-n Bellman recursion, for every n; no lemma relating V_n to V* | proxy (V_n for V*; C0b) | same | incomparable (B1) | Mixed |
| E5 | Same print as E4 | Same as E4 plus a proved lemma V_n → V* and V* satisfies Bellman's equation | equivalent (lemma named) | same | same | Same |
| E6 | If X ⊥ Y given Z then I(X;Y\|Z)=0 and I(X;Y) ≤ H(Z) | Proves only I(X;Y\|Z)=0 | own | same | weaker (one component missing) | Narrower |
| E7 | For every agent π, property P(π) | For every agent π with bounded rewards, P(π) | own | narrower (added hypothesis) | same | Narrower |
| E8 | For every agent π, P(π) | For any agent with bounded rewards, P'(π) where P' implies P | own | narrower | stronger | Mixed |
| E9 | Agent A* (a specific construction) satisfies bound β | For any agent satisfying conditions H1–H4, bound β; H1–H4 never proved for A* | own | narrower (A-row 4: specific object, hypotheses not proved for it) | same | Narrower |
| E10 | Under Conjecture K, statement S | S, assuming K as a hypothesis | own | same (print also assumes K) | same | Same |
| E11 | Statement S (no conjecture) | S, assuming Conjecture K as a hypothesis | own | narrower (A1) | same | Narrower |
| E12 | ∀x ∃y R(x,y) | ∃y ∀x R(x,y) | own | same | stronger | Wider |
| E13 | For a finite set X with \|X\| = n ≥ 1, P(X) | For X with \|X\| = n ≥ 1, P(X) ("finite" dropped; it follows from \|X\| = n) | own | same, leaner | same | Same |
| E15 | Effectivity function on a finite player set N (print's setting is finite) | Same definition with N any type | own | broader (A6) | same | Wider |
| E16 | "If the agent does not help the human, the human's policy stays suboptimal" | hypothesis `value noop < optValue` | own | same (renders print's stated condition; quote it) | same | Same |
| E17 | Paraphrase silent on finiteness; source states "throughout, variables take finitely many values" | Lean assumes `Fintype` for variables | own | same (standing assumption, §0) | same | Same |
| E18 | Condition (ii) holds for every effectivity function | Proved only for effectivity functions induced by a surjective game form | own (C0: subclass) | narrower | same | Narrower |
| E19 | For finite X, bound β on a probability measure μ | For any type X and any finite measure μ (zero measure allowed) | own | broader (carrier); zero measure: no effect | same | Wider |
| E20 | H(X\|Y) ≤ H(X) | H(X\|Y) ≤ H(X), with equality iff X ⊥ Y | own | same | stronger (B2: extra about print's own inequality) | Wider |
| E21 | For finite X, property P | For any type X with `Fintype` on Y added (Y unrestricted in print) | own | incomparable (broadens on X, narrows on Y) | same | Mixed |
| E14 | For a finite group G of odd order, P(G) | For any finite group G, P(G) (odd order not needed) | own | broader | same | Wider |
| E22 | For the description complexity K, property P(K) | For every `c : Complexity` (a structure with a cost function and two axioms), P(c); K satisfies both axioms by a named lemma | own (C0a: c := K) | same (A7: K meets the axioms) | same | Same |
| E23 | Same print as E22 | Same Lean, but K violates the second axiom on some print instance | own (C0a) | narrower (A7: that instance is excluded) | same | Narrower |
| E24 | "Assume the reward is bounded by M" (an assumption) | A theorem with hypothesis `hbound : ∀ s, r s ≤ M` among others | own | same | same (§7.5: renders the assumption; role assumption) | Same |
| E25 | There exists an MDP on which policy iteration takes exponential time | A two-state-per-level chain family with deterministic transitions, proved exponential | own | same (B4: specificity of a witness does not narrow) | same | Same |
| E26 | X holds for every finite game (one component) | Theorem 1 proves X for finite games with ≤ 2 players; Theorem 2 proves X for finite games with ≥ 2 players | own | same (§7.3: union of the two routes covers every finite game) | same | Same |

## 9. Output per row

One JSON object per line, nothing else:

```
{"id": "NNN", "role": "theorem|definition|assumption|explanatory", "refutes": false, "objects": "own|equivalent|proxy", "applicability": "broader|same|narrower|incomparable", "conclusion": "stronger|same|weaker|incomparable|none", "reason_C": "one sentence", "reason_A": "one sentence naming each difference and its effect", "reason_B": "one sentence naming each component and its label", "leaner": false, "missing_context": false, "interpretation_sensitive": false, "aggregation_sensitive": false, "confidence": 1-5}
```

`leaner` is true when the Lean drops hypotheses that print's other hypotheses already imply, or states print's claim more concisely, with no change to instances or conclusion. It is a note, not part of scope.

If `refutes` is true, set objects, applicability and conclusion to null and explain in reason_B.
