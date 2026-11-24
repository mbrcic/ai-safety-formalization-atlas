# Review of SPEC-v5 as canonical scope taxonomy

Verdict: **not yet fit to be canonical.** The matrix is sound for universally quantified theorems about fixed objects, but three rules break implication, v5 leaves undecided four row kinds the regrade decided by ruling, and it conflicts with the old scheme on two row classes and on Stability. Refs by line: SPEC = `spec/SPEC-v5.md`, AUD = `source-coverage-audit.md`, BR = `BRIEF-ruling-adjudication.md`. Findings are from reading only; no Lean was run.

## A. Soundness

- **[note]** For print of the form "every instance meeting H satisfies C", with C = own/equivalent, each Wider/Same cell (SPEC:127-134) gives "Lean implies print on every print instance"; same x weaker, narrower x same and narrower x weaker give the converse. K1-K4 agree with the matrix.
- **[blocker] A6 ignores polarity.** "Carrier generalization is always `broader`" (SPEC:83, :53) holds only for a class quantified universally in positive position. For an existential print with the Lean witness in a wider class, the Lean is weaker; a class enlarged inside a hypothesis or under a printed `max` narrows. A6 then outputs Wider for a statement that does not imply print.
- **[blocker] A6 against C0a.** E22 (SPEC:174) quantifies over every `c : Complexity` where print fixes K and grades A = same; A6 and table row 3 call this broader (Same vs Wider). By the same clash E9/E23 (SPEC:161, :175) are `narrower`, while "every difference in both directions" (SPEC:63) gives `incomparable`, Mixed.
- **[blocker] Narrower is unsound for an uninstantiated general theorem.** In E9 print does not imply the Lean, and no print instance is shown covered, yet the row is Narrower/Partial with B = same judged on an empty shared set.
- **[fix] Proxy in hypotheses.** K1/B1 constrain conclusion objects only; a proxy that appears only in print's hypotheses can still grade Same.
- **[fix] Two routes to one label.** "Only a special case of the component" is B `weaker` (SPEC:98) while C0/A9 send the same restriction to A; a proxy component is `incomparable` or `missing` at the grader's choice (SPEC:113), so Mixed or Narrower. E9 cites "A-row 4"; the rule is row 5 (SPEC:55).
- **[fix] Mixed is overloaded.** B = incomparable from a proxy gives Mixed with nothing wider (AUD:287).
- **[fix]** A step-1 countermodel (SPEC:22) must also meet standing assumptions, term meanings and rulings (BR:114-117).

## B. Completeness

- **[blocker] Refuted print, repairs.** K3 nulls the axes, so §6 yields no scope. The regrade graded at least seven rows against repaired print (BR:22-30, :40-42, :224-232) on conditions v5 does not contain. Partial refutation is undecided.
- **[blocker] B = none.** v5 prints "—"; the regrade writes `NoScope` and counts it below print (row 005, `final.jsonl`); AUD:478, :502 say "—" is not debt; `check_coverage_audit.py:161` has no `NoScope`.
- **[blocker] Conjectures.** No role (SPEC:147). As `theorem`, an unproved Prop is B = none; R15 (BR:63) reverses that.
- **[blocker] Several readings.** A8 covers informal premises only and says "choose the best-warranted one" (SPEC:86); the regrade used the conservative default (BR:122-123). Ambiguous definitions, quantifier order (R10) and conclusions (060, 286, 018) are undecided.
- **[fix] Beyond.** v5 cannot produce it; AUD:461-465 counts it, and AUD:451-454 routes a conditional restatement there where v5 says Narrower.
- **[fix] Standard mathematics not in Lean.** *Proved* (SPEC:18) lets a named standard identity complete a conclusion; its example is a chain rule. AUD:229-233 allows only specialization, unfolding, rearrangement, representation.
- **[fix] Rendering.** v5 grades "all declarations the row cites" (SPEC:13); the regrade graded HEAD with citation gaps (BR:43-46).
- **[fix]** §7.3: a union that "cannot be stated as one A/B pair" has no matrix input.

## C. Relation to the old scheme

Not a projection. Classes that disagree:

1. **[blocker] Presentation against carrier.** AUD:409 "The sample space is not a scope axis" (Same); A6 says broader. `STATS.md` shows 123 rows moving Same to Wider; I did not check per row how many are this class.
2. **[blocker] Coverage independent of scope.** The audit table holds 10 Partial/Same, 7 Partial/Wider, 3 Yes/Narrower, 3 Yes/Mixed rows (my count); §6 forbids all four. `methodology.md:56` states the old convention.
3. **[fix]** A definition with a stronger defining predicate: old Same plus a note (AUD:369-395); §7.2 gives Mixed.
4. **[fix]** Attainment: the old object rule owes the proof (AUD:269); R3 makes it a free hypothesis.

**[blocker] Stability** (AUD:272-273) is incompatible as written: adopting v5, and each ruling, is a re-reading of text already read. 134 final rows are decided by blind majority alone.

## D. Diagnosability

| Label | Remedy | Ambiguity |
|---|---|---|
| C proxy | build print's object, or prove the correspondence | none |
| A narrower | prove the hypothesis from print's; drop it; instantiate the interface for print's object; or refute the wider statement (row 135) | four remedies |
| A incomparable | as narrower, on the narrowing differences | which ones is lost |
| B weaker | prove the missing component; tighten the bound; swap quantifiers | three |
| B incomparable | proxy (go to C), or fix the weaker part | two |
| B none | build, or accept as boundary | no policy |

**[blocker]** Not one-to-one: nine cells collapse into Mixed, and the standing rule's three states (AUD:291-332) have no v5 field. Record per row: role; C, A, B; computed scope and coverage; flags; rulings or repair applied; open questions; decided-by; and per below-print axis the `defects` record `final.jsonl` already uses (kind, print quote and page, Lean declaration file:line and binder, violating print instance, state: closed / unclosable with witness / costed, closure statement).

## E. Rulings with general force

General:
- "These rulings are now part of print's meaning... They are not evidence about the Lean" (BR:6-8).
- "grade against the repaired print; the literal print is refuted" (BR:22-23), on "literal print proved wrong, repair necessary and minimal" (BR:225).
- "Read binders as elaborated" (BR:34).
- "Grade against the Lean at HEAD... record the citation gap" (BR:43-46); "An upgrade stands only if a declaration at HEAD, cited or citable, carries it" (BR:120).
- "A downgrade stands only if its witness meets every hypothesis of print, the standing assumptions..." (BR:114-117).
- "A claimed print clause... counts only if it is part of this row's printed statement" (BR:118-119).
- "Where the decision rests on a reading no ruling settles, grade under the conservative default" (BR:122-123).
- R15 (BR:63).
- R3 and its extension (BR:53-55, :129-131), R9's "presupposes E_π exists", R6, the 2.10.1 ruling: one principle, a hypothesis needed for print's expression to be defined is print's.
- The sweep after each ruling (BR:197-200, :233-235).
- 018's core: an existential "can" is carried by "one inhabited instance" (BR:252-254).

One source only: R1, R2, R4, R5, R8, R10, R12, R16, R17, window completion, Prop. 10, 060, 064, 206, 286, the p_g tie rule, 287. R8 reverses the audit's own closure (AUD:297-305).

## F. Weak points

- **Visible / standard mathematics [blocker].** Limit non-Lean steps to a closed list (unfolding, specialization, rewriting, propositional logic, order antisymmetry); otherwise name a Lean declaration, or set `derived: true` and keep the row out of the headline.
- **A8 [fix].** Label = worst over packet-consistent readings unless a ruling id is recorded.
- **§7.3 [fix].** Row coverage = intersection over components of the union over routes; state the exhaustive split; beyond two routes cite a combining theorem.
- **B4 [fix].** Show the witness meets print's hypotheses and standing assumptions; quote or rule the existential reading.
- **A7 [fix].** `same` needs a named instance or lemma, as in E22.
- **Flags [fix].** K4 caps confidence only; a flagged row still counts Same/Wider. Require a grounded verdict first.

## Spec edits

1. A6: restrict to universal positive positions; add a polarity rule and examples.
2. Decide whether C0a abstraction broadens; make E9, E22, E23 agree with SPEC:63.
3. Add an A label for "no print instance shown covered".
4. Extend K1 to proxies in hypotheses.
5. Separate proxy from Mixed, or require C, A, B columns in the table.
6. Add a section on refuted print and repairs (conditions, refutation file, `repair` field, partial refutation).
7. Fix B = none: one spelling, owed or not; update `check_coverage_audit.py`.
8. Add role `conjecture` (R15), coverage shown as stated.
9. Add a general ambiguity rule; align A8 with it.
10. Add a rulings register to §0 (id, date, sweep).
11. Add the definedness-presupposition rule, bounded: it never turns a claim print makes into a hypothesis.
12. Apply the tightenings in F.
13. Define the rendering as cited declarations, read as elaborated; HEAD-only support is a citation gap.
14. State Beyond as outside v5; keep its counting rule.
15. Replace Stability: a row moves on new Lean, source evidence, a recorded ruling with sweep, or a spec version change with a published mapping.
16. Reconcile AUD:409 and Partial-with-Same with §7.1/§6; amend `methodology.md:56`.
17. Make the `defects` record and the three owed states table fields.
18. Fix the "A-row 4" reference and the `incomparable`/`missing` overlap in B1.
