# Review of SPEC v6 before it becomes the canonical scope taxonomy

ROOT = the repository root

SPEC v6 (ROOT/docs/provenance/regrade-2026-11/spec/SPEC-v6.md) revises SPEC v5 (same folder) to answer two reviews (ROOT/docs/provenance/regrade-2026-11/spec/reviews/2026-11-22-spec-v5-review-fable.md and -codex.md). The rulings it draws on are in ROOT/docs/provenance/regrade-2026-11/adjudication-full-v5/BRIEF-ruling-adjudication.md.

Answer, with section/rule references:
1. For each [blocker] and [fix] in the two v5 reviews: resolved, partly resolved, or not resolved by v6? One line each.
2. New defects v6 introduces: contradictions between rules, calibration examples that disagree with the rules (check every E-row against the rules it cites), unsound cells (a Wider/Same that does not guarantee "the Lean statement implies print on every print instance"; a Narrower that does not give the converse), undecided cases.
3. A6 + §7.1 (carrier generalization broadens only if some Lean instance is not reducible to a print instance by a claim-preserving map): is the test well-defined and checkable by a grader? Give one case where graders would plausibly disagree, and a sharper wording.
4. §7.6 (conservative default) + §7.9 (argued components counted with a flag): coherent together? Can a row be inflated under v6, and how?
5. Is anything in v6 still a matter of grader judgement that should be an author decision? List them as questions the author must answer.

Constraints: do not run lean or lake; do not edit repository files; no web access; never use 2>/dev/null; write only in your scratch folder.

Output: a markdown report (<= 1200 words), each finding tagged [blocker], [fix] or [note], ending with a numbered list of concrete edits. Write it to <scratch>/review.md and return it as your final message.
