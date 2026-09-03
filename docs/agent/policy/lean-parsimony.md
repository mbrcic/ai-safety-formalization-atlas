## Parsimony (formalizations)

Reuse a maintained Lean result + thin atlas alias before porting another proof.
Keep a second formalization only for a documented substantial gain (stronger
theorem, different representation, reduction certificate, constructive content,
or necessary independence). Non-Lean proofs may be provenance without duplicate
public Lean declarations. Prefer packaging Rice as `Verification.rice` /
`AgentBehavior.no_behavioral_safety_verifier` rather than a second undecidability
proof. Detail: [`docs/guide/methodology.md`](../../guide/methodology.md).

**Parsimony governs duplication, not foundations.** A second way to establish
something the tree can already state is duplication, and the rule above is
strict about it. A definitional layer that catalogued rows cannot be *stated*
without is a foundation, and asking it to show consumers first is a rule no
foundation can pass: the consumers are blocked on the thing being judged. A
foundation may land ahead of its consumers when all four hold:

1. **Two blocked rows, by id.** At least two existing `BY-`/`CLM-`/`LAND-` rows
   or `tasks.yaml` entries that cannot be stated without it — blocked, not
   merely inconvenienced.
2. **The gap is upstream and recorded.** A `novelty_checks` entry showing the
   pinned corpora lack it, so the blocker is availability rather than effort.
3. **Definitions may precede consumers; theorems may not.** The definitional
   layer may land with none. Theorems built on it need a consumer landing in the
   same change or the next.
4. **An expiry.** The row names a release by which a consumer must land, or the
   layer is deleted or demoted to provenance. Removal is an ordinary outcome —
   the `doc-gen4` pipeline was built and removed on cost grounds.

A foundation is a `LAND-` artifact row, never headline coverage, and carries no
statement-match grade against a source it does not state.
