# Review of SPEC v6

Verdict: **not yet canonical.** Blockers: N1-N4 and §4. Read only; no Lean run; the checker claim rests on a grep of the script. R = resolved, P = partly, N = not.

## 1. v5 findings

Fable review:
- A6 polarity [blocker]: R (A10); nested positions unstated (N9).
- A6 against C0a [blocker]: R (C0a; E9, E22, E23).
- Uninstantiated general theorem [blocker]: P. E9 is Mixed, still Partial (N3).
- Proxy in hypotheses: R (C3, K1, E33).
- Two routes to one label: R (A9, §4).
- Mixed overloaded: P (§11 records axes).
- Countermodel meets all hypotheses: R (§1.1, §7.7, G5).
- Refuted print, repairs [blocker]: P (refuted component without repair undecided).
- B = none [blocker]: P. `check_coverage_audit.py:161` has no `None`/`Refuted` and reads no axes, against §6.
- Conjectures [blocker]: R (§7.5, G4, E32); see N6.
- Several readings [blocker]: P (§7.6); "lower scope" is not an order (N5).
- Beyond: R (`no-print`).
- Standard mathematics: P (§0 closed list, undone by §7.9).
- Rendering: R (§0, §7.8).
- §7.3 no matrix input: N. `aggregation_sensitive` still yields no A/B pair.
- Presentation against carrier [blocker]: P (A6b, E27; N1).
- Coverage independent of scope [blocker]: N. §6 still forbids the 23 combinations that review counted; no mapping.
- Definition with stronger predicate: N (§7.2 still Mixed, undeclared).
- Attainment: R (G3).
- Stability [blocker]: R (§10); (d)'s mapping does not exist.
- Diagnosability [blocker]: P (§9, §11; §13 lacks `defects`, `repaired`, `open_questions`, `decided_by`).
- Visible mathematics [blocker]: P (v6 counts argued rows in the headline).
- A8, B4, A7: R (§7.6, B4 i-iii, A7).
- §7.3 tightening: P (no combining theorem beyond two routes).
- Flags: N (K4 still only caps confidence).

Codex review:
- Whole-row entailment evidence [blocker]: P. C is still per object; no non-vacuity requirement (N3).
- Strictness [blocker]: P. `∀ n>0, P n ∧ P 0` is now Wider (B2), sound but not strict.
- Rule overlaps [blocker]: P. A3 now conflicts with A12 and A6(b), which read the conclusion.
- Refutation records [blocker]: R (§7.7).
- NoScope/Beyond: P (checker).
- Conjecture role, definitions on overlap [blocker]: R (§7.2, §7.5).
- Scales disagree, migrate [blocker]: P (no migration).
- Stability, owed states: R, except `None` is made owed.
- Remedies: R. Record fields: P (§13 row-level only).
- R15, R3 [blocker]; standing rulings: R (G1-G8).
- Proof provenance: P (§7.9).
- Provisional status; Partial needs print content [blocker]: P. Partial remains "otherwise".
- Calibration: P (no shared-witness example).

## 2. New defects

- **N1 [blocker] A6(b)/§7.1 is degenerate.** For a proved Lean theorem and a true print, every map from Lean instances to print instances preserves the truth of hypotheses and conclusion (all true). Every generalization is then "representation"; E2, E15, E19, E22 contradict the rule.
- **N2 [blocker] A11/A5 against A1, A2, A-table rows 4-5.** An assumed, unproved hypothesis (E9, E11) has no excluded print instance "in hand", so A11 forbids `narrower`; A1 demands it.
- **N3 [blocker] E9 against §7.3.** §7.3 counts a route "only once its specialization to print is checked"; E9's is not, so B is `missing`, scope None, coverage No. E9 says Mixed/Partial. An interface no print instance satisfies likewise grades Narrower/Partial.
- **N4 [blocker] §7.1 unsound for Same.** A map from Lean to print instances need not reach every print instance, so "no effect" can hide a narrowing; Same would not imply print everywhere.
- **N5 [fix] §7.6.** Scope is not ordered (Narrower against Mixed; None). Undecided when one reading refutes print.
- **N6 [fix] Conjecture refuted in Lean:** §7.5 says Yes with `proof: refuted`; §7.7/K3 say Refuted/No.
- **N7 [fix] Off-list steps by axis:** C1 gives `proxy`, §7.9 gives proved-with-flag for B, A is unstated.
- **N8 [fix] §9** attaches defect records to below-print axes; an `argued` Same row cannot carry its owed proof.
- **N9 [note]** A10 covers three positions; nested antecedents and shrunk classes need the parity rule.
- [note] Every E-row's scope matches §6 on its stated axes; the defects are in axis cells.

## 3. A6 + §7.1

**[blocker]** Not well-defined (N1), and "not reducible" quantifies over all maps, which a grader cannot establish. Disagreement case, after repairing N1: print bounds a probability measure on finite X; Lean takes any finite measure (E19). One grader normalizes μ/μ(X) (zero measure degenerate): Same. Another follows E19: Wider.

Sharper wording: "A generalization is representation iff the Lean statement follows from the printed statement, taken as a hypothesis and not unfolded, by closed-list steps and named Lean transfer lemmas (ideally one declaration `lean_of_print`), **and** every print instance is a Lean instance. Otherwise it broadens, with A4's witness. Undecided: no effect, flagged."

## 4. §7.6 + §7.9

**[blocker] Not coherent.** Doubt about print's meaning takes the lowest grade; doubt about whether the mathematics holds takes the highest. Inflation routes:
1. `argued` is unbounded: any step, up to the whole theorem, grades Same/Yes.
2. Role has no test; `conjecture`, `assumption`, `definition` give B = same without proof, in the same count.
3. Vacuous or uninstantiated Lean gets Partial instead of No (N3).
4. `no-print` removes a row from the count; no test stops a failing row moving there.

## 5. Author decisions

1. Is B = none owed (§6) or a boundary (§9), and who decides per row?
2. Do `argued` rows count as Yes, Partial, or a separate column? What may an argued step cite?
3. Do conjecture Yes rows share the headline with proved theorems?
4. Is an uninstantiated general theorem (E9) Mixed/Partial or None/No?
5. Definition with a stronger defining predicate: Mixed or Same with a note?
6. Rows whose coverage and scope disagree under §6: regraded how?
7. Order of scopes for "conservative"; is a refutation under one unruled reading `needs-ruling`?
8. Is G3 the general definedness presupposition (R6, R9, 2.10.1) or attainment only?
9. A refuted component with no accepted repair: whole row Refuted?
10. Who assigns role when print asserts without proof, and who reads G3's "used as a maximiser"?

## Edits

1. Replace A6(b) and §7.1's reduction by the §3 wording; re-derive E2, E15, E19, E22, E27 from it.
2. A11: `narrower` needs an excluded instance **or** a Lean hypothesis not shown implied; record `strict: yes|unknown`.
3. Add K5: no print instance shown covered gives B = `none`. Regrade E9 to None; add a vacuous-interface example.
4. §7.9: apply to all three axes; bound argued steps to a cited published theorem; record per component; report argued rows in a separate headline column; give them a defect record.
5. §7.6: define the order (Refuted, None < Mixed < Narrower < Same < Wider); a reading that refutes is `needs-ruling`.
6. §7.5: a role test; conjecture counted separately; `proof: refuted` routes to §7.7.
7. A3: list A12 and the reduction as exceptions. A10: state the parity rule.
8. §7.3: say which A/B pair an `aggregation_sensitive` row records (the intersection's).
9. §6: say the checker "will" compute scope; add `None`, `Refuted`. §13: add `defects`, `repaired`, `open_questions`, `decided_by`.
10. Publish the mapping §10(d) requires; amend `methodology.md:56`.
11. §7.7: decide partial refutation without repair. Add a shared-witness calibration row.
