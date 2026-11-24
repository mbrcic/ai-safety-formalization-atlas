# Review of a scope-grading taxonomy before it becomes canonical

A formal library (Lean 4) renders printed statements from published sources and grades each rendering against print. The maintainer intends to make the v5 specification the library's canonical grading taxonomy, replacing the older single-scale scheme. Your job: decide whether v5 is correct and fit to be canonical, and say exactly what must change first.

ROOT = the repository root

Read:
1. The v5 specification: ROOT/docs/provenance/regrade-2026-11/spec/SPEC-v5.md
2. The old scheme it replaces: ROOT/docs/provenance/source-coverage-audit.md, the preamble before section 1 (the "Scope" verdict table, the standing rule "scope >= print", the owed-cell states, "Stability", "Counting", the rule for "—" cells). Also ROOT/docs/guide/methodology.md on EXACT/RELATED and scope_delta.
3. The author rulings and accepted repairs applied during the regrade: ROOT/docs/provenance/regrade-2026-11/ADJUDICATION-LOG.md (then at adjudication-full-v5/BRIEF-ruling-adjudication.md) (all sections). Many are row-specific readings; some may have general force.
4. Optional evidence: the regrade's final grades (then adjudication-full-v5/final.jsonl, not published; see final-grades.tsv) (final grades and sources), and the scope-computing checker ROOT/scripts/check_coverage_audit.py.

Answer, with references (section/rule numbers, file:line):
A. Soundness. Is the A x B matrix (§6) sound with respect to implication? Under C = own/equivalent, does every Wider/Same cell guarantee "the Lean statement implies print on every print instance"? Does Narrower/Mixed follow? Are K1-K4 consistent with the matrix? Find any rule pair that contradicts another, or a case that two rules decide differently.
B. Completeness. Which situations does v5 not decide? At least check: refuted literal print and graded-against-repair rows; rows with no Lean conclusion (B = none) and what scope/coverage they get (v5 says "—"; the regrade used "NoScope"); "Beyond" rows; conjecture rows; definitions with several inequivalent readings; rows resting on a step that is "standard mathematics" but not in Lean.
C. Relation to the old scheme. Is the old five-value scale a coarse projection of v5 (so both can never conflict), or do they disagree on some class of rows? Name the class. Is the old "Stability" rule ("a row does not move on a re-reading of a text already read") compatible with v5 as canonical?
D. Diagnosability and use. For each axis label below print, what remedy does it prescribe (e.g. A narrower -> drop/prove a hypothesis)? Is the mapping one-to-one enough to drive work? What should the audit table record per row so a defect is diagnosable from the table alone?
E. Rulings with general force. Which rulings in item 3 state a general rule that belongs in the canonical spec (quote them), and which are readings of one source?
F. Weak points. Where does v5 rely on grader judgement that could silently inflate grades (e.g. "Visible", "standard mathematics", A8 informal premises, §7.3 union, B4)? Propose a tightening for each that keeps the spec usable.

Constraints: do not run lean or lake; do not edit any repository file; no web access; never use 2>/dev/null; write only in your scratch folder.

Output: a markdown report (<= 1500 words) with sections A-F, each finding tagged [blocker] (must fix before canonical), [fix] (should fix in the same change) or [note]; end with a numbered list of concrete spec edits. Write it to <scratch>/review.md and also return it as your final message.
