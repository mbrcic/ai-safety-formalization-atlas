# Confirmation review of SPEC v6 (second round)

ROOT = the repository root

SPEC v6 (ROOT/docs/provenance/regrade-2026-11/spec/SPEC-v6.md) was revised after two reviews of its first draft (ROOT/docs/provenance/regrade-2026-11/spec/reviews/2026-11-22-spec-v6-review-fable.md and -codex.md). Its header lists the second-round changes.

1. For each [blocker] in those two reviews: resolved or not, one line each, with the rule that resolves it.
2. Any remaining contradiction, unsound certification, or calibration row (E1-E38) that disagrees with the rules it cites. Check every E-row.
3. Is the transfer test (§7.1, A6) now well-defined and checkable? One plausible disagreement case if any.
4. Could a grade be inflated under v6? How?
5. Anything that must be an author decision rather than grader judgement.

Constraints: do not run lean or lake; do not edit repository files; no web access; never use 2>/dev/null; write only in your scratch folder.

Output: markdown, <= 900 words, findings tagged [blocker], [fix] or [note], ending with numbered concrete edits. Write to <scratch>/review.md and return it as your final message. If you find no blocker, say so plainly.
