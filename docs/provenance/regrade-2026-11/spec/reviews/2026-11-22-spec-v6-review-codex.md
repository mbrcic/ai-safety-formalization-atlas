# SPEC v6 canonical adoption review

[blocker] Hold adoption. §6 still awards entailment labels without requiring the corresponding whole-row implication.

## Disposition of v5 findings

Tags and line numbers identify the original findings. [Fable review](../../../../../docs/provenance/regrade-2026-11/spec/reviews/2026-11-22-spec-v5-review-fable.md), [Codex review](../../../../../docs/provenance/regrade-2026-11/spec/reviews/2026-11-22-spec-v5-review-codex.md).

### Fable

- [blocker] L8 partly resolved — A6/A10 handle several polarities, with conflicting exceptions.
- [blocker] L9 resolved — C0a/A6 align E9/E22/E23 in principle.
- [blocker] L10 partly resolved — E9 becomes Mixed. Empty overlap remains possible.
- [fix] L11 resolved — C3/K1 catch premise proxies.
- [fix] L12 partly resolved — A9 removes double grading and E9 drops the miscitation. §4 leaves object matching ambiguous.
- [fix] L13 resolved — §11 exposes axes behind Mixed.
- [fix] L14 resolved — §0/§7.7 require all standing conditions.
- [blocker] L18 partly resolved — §7.7 handles repairs, leaves unrepaired partial refutation unclear.
- [blocker] L19 partly resolved — §6 chooses owed None, which the checker still rejects.
- [blocker] L20 resolved — §7.5 implements R15.
- [blocker] L21 partly resolved — §7.6 covers readings without defining their ordering.
- [fix] L22 partly resolved — §7.5 restores Beyond. Conditional restatements still change categories.
- [fix] L23 partly resolved — §0 restricts Proved. §7.9 counts off-list derivations.
- [fix] L24 resolved — §0/§7.8 specify elaboration, citation gaps and both grades.
- [fix] L25 not resolved — §7.3 still lacks a fallback grade.
- [blocker] L31 resolved — A6/§7.1/E27 recognize finite-law pushforwards as presentation.
- [blocker] L32 not resolved — §6 still couples coverage and scope. Methodology migration is absent.
- [fix] L33 not resolved — §7.2 still changes stronger definitions’ grades.
- [fix] L34 partly resolved — G3 distinguishes presupposed from asserted attainment. Old audit rule remains.
- [blocker] L36 resolved — §10 versions changes and sweeps.
- [blocker] L49 resolved — §§9/11 require axes, provenance and defect dispositions.
- [blocker] L70 partly resolved — §0 adopts a closed list. Argued work enters headlines.
- [fix] L71 partly resolved — §7.6 leaves “lower” undefined.
- [fix] L72 partly resolved — §7.3 states intersection/union without requiring a combining proof.
- [fix] L73 resolved — B4 requires admissibility and textual warrant.
- [fix] L74 resolved — A7 requires a joint construction or lemma.
- [fix] L75 not resolved — K4 still only caps confidence.

### Codex

- [blocker] L3 not resolved — §6 lacks whole-row certification.
- [blocker] L7 partly resolved — C3/A7/§7.3 address proxies and jointness locally.
- [blocker] L8 partly resolved — A12 repairs the example. A11/B5 test local strictness.
- [blocker] L9 partly resolved — §4/B2/A7 improve. A2/A5/A11 priority remains unclear.
- [blocker] L13 partly resolved — §7.7 counts repaired grades once. Its evidence rules differ from §1.
- [fix] L14 partly resolved — §§6/7.5 define None/Beyond. Checker and precedence need migration.
- [blocker] L15 partly resolved — §§7.2/7.5/7.6 cover fidelity. §7.9 blurs certification.
- [blocker] L19 partly resolved — §§7.1/10/11 address representation and migration. Evidence policies diverge.
- [fix] L20 partly resolved — §§9/10 record dispositions. §6 makes No rows owed.
- [fix] L24 resolved — §9 requires per-defect remedy and disposition.
- [fix] L25 partly resolved — §§7.8/9/11/13 omit mandatory joint evidence and schema fields.
- [blocker] L29 resolved — §7.5/G3 implement R15/R3.
- [fix] L30 partly resolved — §0/§7/G1–G9 capture procedure. §7.8 delays the audit upgrade until citation.
- [fix] L35 resolved — §0/§7.9 distinguish proved from argued.
- [blocker] L36 partly resolved — B4/§7.3 improve joint coverage. Provisional and substantive Partial gates are absent.

## New defects and calibration

- [blocker] §7.1 calls the inclusion of positive naturals into naturals representation. It preserves `P(n)` on its domain. §6 then permits Same for Lean’s positive-only theorem versus print’s all-natural theorem, although `P(0)` need not follow. A5/A9 demand narrowing when recovery fails.
- [blocker] Extend E34’s first route to assert an independent R on games outside the small-game class. §4 sees identical conclusions on joint overlap, so §7.3/§6 can still give Narrower. Print supplies no R there, so it cannot imply the Lean routes.
- [blocker] A10 reverses variance for a hypothesis `(∀x ∈ S, R(x)) → Q`. Enlarging S weakens that hypothesis and can produce broader applicability. A10 says it narrows, contrary to A5.
- [blocker] B5’s fallback can label an undecided implication Same. A3 omits A12’s recovery exception. §1 requires a Lean declaration while §7.7 can admit a bare countermodel. §7.6’s ruling-only freeze conflicts with §10’s evidence and version triggers.
- [fix] §6’s checker claim is premature. The checker tallies recorded cells, rejects None/Refuted and computes no axis-derived grades. §§9/13 omit a defect schema for null-axis refutations.
- [note] Consistent on stated readings. E1/E13 (§7.1/A4), E3/E12 (§4/B5), E4/E33 (C0b/B1/C3), E14 (A4, even-order witness), E26 (§7.3), E27 (joint-law reduction), E31/E36 (§7.7/K3, admissible evidence), E32 (§7.5), E35 (§7.9).
- [fix] E2/E19/E22/E23 lack A6 non-reduction evidence. E19 also leaves the zero case unstated. E5 needs a distinct bridged object for equivalent. E6’s unproved clause shares objects with the proved clause, leaving missing versus incomparable open (§4). E7/E8/E11/E18 need A5 exclusions. E15 needs a role and an A6 witness. E21 needs both A4/A5 witnesses. E8/E20/E28 need B5 strictness. E28’s possibly infinite witness alone leaves the converse undecided.
- [fix] E9 conflates unproved application with exclusion (A5/A7). E10/E16/E17 clash with literal A1 when premises render print. E16 must warrant treating suboptimality as a premise (A8). E17 must distinguish finite range from a finite ambient type. E24 leaves enclosing hypotheses ambiguous (§7.5). E25 must specify the family/size quantifiers (B4). E29 needs explicit incompatible shared extension data. E30 works by A12 despite A3. E34 violates §7.3’s single-route shared-binder requirement as written.

## Carrier test and counting

- [blocker] A6/§7.1 leave admissible maps unspecified. In E2 one grader can map every compact-domain function to a constant on the interval and prove both conclusions true. Another requires preservation of the function’s range and rejects disconnected ranges. Truth preservation alone permits circular proofs.
- [blocker] §§7.6/7.9 can coexist, but conservative reading selection supplies no proof gate. Accepting a necessary Fubini step without checking integrability can turn Partial into flagged headline Yes. Even a valid off-list argument increases that count. K4 only lowers confidence.

## Decisions for the author

- [fix] Which observations and maps qualify? How are Mixed, Narrower, None and Refuted ordered across readings? Which flagged, proxy-only and empty-overlap rows count? What certifies refutation or Partial? Do unproved comparisons get a provisional grade? Does G7’s generalization of the row 018 ruling yield to contextual readings? Which definedness conditions besides G3’s attainment are presupposed? Does Wider/Narrower require whole-statement strictness?

## Concrete edits

1. [blocker] Require a simultaneous print-to-Lean lift and joint conclusion transfer for Yes, and reverse entailment for Narrower.
2. [blocker] Fix the claim-relevant observations and admissible maps before grading. Require a total Lean-to-print map that jointly preserves the named observations and definedness, proved independently of the target theorem. Require an unmatched observation profile for widening or record undecided.
3. [blocker] Define provisional grades and count only certified theorem coverage in the headline.
4. [fix] Specify rule precedence, composed routes and aggregation fallback. Repair the calibration rows and migrate the schema, checker and methodology together.
