# Adversarial Review — v0.1 Release Candidate

Date: 2026-07-18
Scope: full repository at `agent-work` (95d1592), reviewed against the stated
purpose (README, ROADMAP) and plan (STATE.md, docs/guide/methodology.md,
docs/releases/v0.1.md).
Method: every checkable claim was re-executed or re-derived locally, not taken
from the documents.

## Verification performed

| Check | Result |
|---|---|
| `lake build` | Passed, 8,662 jobs, exit 0 |
| `grep sorry` over released Lean files | None (only a docstring mention) |
| `scripts/validate_registry.py` | Passed (44 results, 9 formalizations, 7 Lean artifacts) |
| `scripts/audit_release.py` | Passed |
| Upstream `Arrow/Arrow.lean` SHA-256 at pinned commit | Re-fetched from GitHub; matches claimed `ed006bc3…ab7ab0` byte-for-byte |
| Vendored Arrow diff vs upstream | Proof bodies unchanged; modifications reviewed line-by-line (see F2) |
| Facade statements vs Mathlib declarations | `rice`, `rice_code_iff`, `halting_re`, `halting_problem`, `nonhalting_not_re` are faithful thin wrappers |
| Utility bridge proof architecture | Sound (see "What held up") |
| STATE.md counts | All verified accurate against registry and source |

## Findings

Ordered by severity. "Blocking" means it should be resolved before the
approval gate is exercised, because the gate itself depends on it.

### F1 (blocking): The release-candidate evidence table is stale — the approval gate would sign off on numbers that no longer describe the repository

`docs/releases/v0.1.md` is the document Mario is asked to approve. Its
"Objective evidence" table records:

- line 11: `lake build`: **8,659 jobs** — actual current build: **8,662 jobs**
- line 16: **8** verified formalization records — registry now has **9**
- line 17: **5** compiled Lean declarations — the atlas now exposes **7**

The table was written at commit `cb3f4e7` ("prepare private v0.1 release
candidate") and never regenerated after the two most substantial feature
commits landed *after* it (`94da85a` canonical Arrow + utility bridge,
`9f18b2f` computability facade refactor). The largest single piece of Lean
work in the repository is therefore absent from the evidence table backing its
own release.

`scripts/audit_release.py` audits the repository state (and reports the
correct 9/7 numbers) but does not cross-check `release-v0.1.md`, so CI cannot
catch this class of drift. Recommendation: either generate the evidence table
from the audit script's output, or add an assertion that the release document's
figures match the audit.

Related: `main` (local and `origin/main`) is 13 commits behind `agent-work` —
the entire project exists only on the working branch. Not an error, but the
release document should state which ref the approval covers.

### F2 (blocking): The vendored Arrow file contains undisclosed additions, contradicting its own provenance header

`AISafetyAtlas/Upstream/Arrow.lean` states: *"The proof body is unchanged. The
atlas adds the modern `module` marker, public declaration visibility,
reducible abbreviations for interface definitions, and this namespace."*

The diff against the verified upstream file shows the header's list is
incomplete. The vendored file also adds **four new public theorems** that do
not exist upstream:

- `Preorder'.lt_iff`
- `unanimity_iff`
- `iia_iff`
- `nonDictatorship_iff`

and silently changes `Profile` and `SWF` from `def` to `abbrev` (this is what
"reducible abbreviations" refers to, but the reader cannot tell which
definitions were affected).

The additions are harmless elimination lemmas (`Iff.rfl` proofs) needed by the
utility bridge, and the proof bodies are genuinely unchanged — I confirmed
both. But this is a repository whose entire value proposition is provenance
precision, and its one vendored file misdescribes its own delta. Fix: list the
added declarations and the `def`→`abbrev` conversions explicitly in the
header, or move the four `_iff` lemmas out of the vendored file into the
facade module where they belong.

### F3 (major): The "44/44 six-corpus discovery pass" materially overstates what the search achieved — including one demonstrable miss of a formalization sitting in its own evidence file

The discovery pass is a headline claim (STATE.md "Formal-library discovery
searches: 44/44"; release table "Cross-framework discovery — Passed"). Three
defects, all verified directly against `docs/provenance/formalization-search.json`:

**F3a — BY-001 (Unobservability) was searched with the wrong queries.** The
row's informal claim is control-theoretic ("a system's internal state cannot
in general be reconstructed from its observable outputs"). Its query terms are
`gödel incompleteness`, `goedel incompleteness`, `incompleteness theorem` —
Gödel phrases with no relation to observability, almost certainly copied from
the unprovability row (BY-013 uses the same terms). Its 22 recorded
"candidates" are all incompleteness files. The 44/44 claim counts this row as
searched; for its actual topic, it was not.

**F3b — BY-027 (Löb's theorem) reports "no candidates" while a Löb
formalization is present in the project's own evidence file.** The AFP corpus
snapshot contains `thys/Incompleteness/Loebs_Theorem.thy` — it appears in
`formalization-search.json` under **BY-001's** hit list (matched by
"incompleteness theorem"). BY-027's queries (`löb theorem`, `loeb theorem`,
`lob theorem`) miss it because the phrase forms don't match "Loeb's Theorem" /
`Loebs_Theorem`. Additionally, HOL-Light's `GL/` provability-logic development
(where Löb's axiom is central) surfaces under BY-014's hits but not BY-027's.
A registry row that is an explicit near-term target (`open-work.md` lists Löb
leads) records negative search evidence that the same JSON file refutes.

**F3c — Candidate counts are dominated by noise.** BY-021 (No Free Lunch —
optimization) reports 143 candidate files; every one matched only the bare
word "optimization" (`meson.ml`, `Redblackset.sml`, red-black tree
implementations…), and zero matched "no free lunch". Meanwhile BY-020 (No Free
Lunch — supervised learning, the same theorem family) reports 0 candidates.
BY-014 similarly lists `Data/Fintype/Order.lean` and `Control/LawfulFix.lean`
as "candidates" for undecidability. The per-row candidate-file counts in
`docs/provenance/formalization-search.md` are presented in a summary table where they
read as signal; for generic single-word queries they are ~100% noise.

The methodology honestly caveats that zero hits are only "scoped negative
search evidence" — that caveat is doing a lot of work, and F3b shows a case
where the corpus *did* contain the target and the method still missed it.
Recommendation before public release: (1) fix BY-001's queries and re-run;
(2) re-run BY-027 with declaration-name and stem queries (`loeb`, `löb`,
`provability`) and record the AFP + HOL-Light leads; (3) either drop bare
generic terms or report per-query hit counts so noise is visible.

### F4 (moderate): `SocialChoice.lean` docstring states the Arrow proof "is pinned as a dependency" — it is not a dependency

`lakefile.toml` requires only `mathlib`. The Arrow proof is a vendored
snapshot (as `Arrow.lean`'s header and `open-work.md` §1 correctly state).
The facade docstring contradicts both. One-line fix, but it is exactly the
kind of provenance statement this repository promises to get right.

### F5 (moderate): `Foundations/Basic.lean` publicly imports all of Mathlib into the atlas's public surface

The module does `public import Mathlib` and is publicly imported by the root
`AISafetyAtlas` module. Every downstream user of the atlas therefore pulls the
entire Mathlib import closure to obtain a `2 + 2 = 4` build witness. This
contradicts two stated principles: "maintenance cost and dependency footprint"
(ROADMAP prioritization criterion 5) and the parsimony policy generally. The
witness needs at most `Mathlib.Tactic.NormNum`; alternatively drop the module
from the root import list — `lake build` of the real modules already witnesses
the Mathlib pin.

### F6 (moderate): Registry status vocabulary is partially undefined and partially unused

`vocabulary.progress_status` declares `MAPPED`, `EXTERNAL_VERIFIED`,
`LEAN_AVAILABLE`, `LEAN_COMPLETE`, `HUMAN_REVIEW`, but:

- `EXTERNAL_VERIFIED` and `HUMAN_REVIEW` are used by zero rows (actual
  distribution: 41 MAPPED, 2 LEAN_AVAILABLE, 1 LEAN_COMPLETE).
- No document defines the `LEAN_AVAILABLE` vs `LEAN_COMPLETE` boundary.
  BY-012 and BY-014 have compiled atlas declarations yet sit at
  `LEAN_AVAILABLE`, while BY-007 is `LEAN_COMPLETE`; a reader cannot tell
  whether the difference is "has a new proof/bridge" or something else.

Since the public API review is the current phase, the status semantics should
be written down before contributors start setting them.

### F7 (minor): The "worked example" is an anonymous `example` in a publicly imported module

`Survey/BrcicYampolskiy/HaltingExample.lean` compiles its restatement as
`example`, so the module contributes nothing to the API yet sits in the public
import surface, and its namespace (`Survey.BrcicYampolskiy`) deviates from the
documented `<Domain>.<OptionalRepresentation>.<Theorem>` scheme. As a
pedagogical artifact this is fine, but the release evidence table lists it as
a release criterion, and a criterion satisfiable by an unnamed example is a
weak gate. Consider naming the theorem or reclassifying the criterion as
documentation.

### F8 (observation, not a defect): Against its stated purpose, the atlas currently contains zero AI-safety content at layer 3

The three-layer plan puts "much of the prospective AI-safety research value"
in bridge theorems connecting mathematics to defined models of agents or
verification. Current state, verified:

- 3 of 44 survey rows have any formalization record (7%);
- the 7 atlas declarations are thin wrappers over one Mathlib module and one
  vendored proof, plus one math-to-math representation bridge;
- every `ai_bridge_status` is `HUMAN_REVIEW`; no AI-safety bridge theorem
  exists.

The documentation is honest about this — open-work.md and the epistemic-scope
section say it plainly, which is to the project's credit. The review point is
about release framing: README's coverage narrative leads with what exists;
for a repository whose title promises an AI-safety atlas, the 3/44 + 0-bridge
state should be equally prominent at the point of first contact, or the v0.1
public framing will invite exactly the overclaim the methodology forbids.
STATE.md's "Next three tasks" item 2 (select one precise bridge) is the right
mitigation; consider making one completed bridge a v0.2 entry criterion.

### F9 (observation): "Canonical maintained source" overstates the Arrow upstream

ROADMAP's first principle is "Reuse before reproving. Prefer a **maintained**
declaration." CC Liang's `arrow` is a personal single-purpose repository; by
vendoring it the atlas has de facto assumed its maintenance (Lean-version
migrations included — the vendoring was already necessitated by Lean 4.32
module boundaries). The choice is defensible (no Arrow in Mathlib; the pin and
license are verified), but documents should say "canonical *pinned* source"
and acknowledge the assumed maintenance burden, rather than implying an
upstream that will track Lean for you.

## What held up under attack

Reported truthfully, since an adversarial review that only lists faults would
misrepresent the repository:

- **The build and no-`sorry` claims are true.** Full `lake build` passes;
  released Lean files contain no incomplete proofs.
- **The provenance pins are real.** The upstream Arrow file's SHA-256 was
  re-fetched and matches; proof bodies are unchanged; the Mathlib and AFP pins
  are recorded with immutable revisions and archive hashes; the Isabelle
  reproduction script verifies archive hashes before building in a
  digest-pinned image.
- **The facades are faithful.** Each computability wrapper restates its
  Mathlib source exactly; no statement drift was found.
- **The utility bridge is architecturally honest and mathematically sound.**
  It represents finite total preorders by lower-contour cardinality, transfers
  Unanimity/IIA/NonDictatorship correctly (the NonDictatorship transfer's use
  of IIA is legitimate and necessary), and explicitly disclaims being a second
  proof of Arrow's core — exactly the parsimony policy applied.
- **The layer separation is consistently enforced.** No registry row, doc, or
  docstring asserts an AI-safety implication from a formal proof; all bridge
  fields are gated `HUMAN_REVIEW`; the validator enforces this for v0.1.
- **STATE.md's numbers are accurate** (7 declarations across 3 rows; 3
  external records across 2 results; 2 extra reproduced variants — all
  re-verified against the registry and sources).

## Recommended pre-approval actions, in order

1. Regenerate `docs/releases/v0.1.md` evidence from the current tree, and make
   `audit_release.py` fail on drift between the release doc and the audit (F1).
2. Correct the `Arrow.lean` vendoring header and the `SocialChoice.lean`
   "dependency" docstring (F2, F4).
3. Re-run discovery for BY-001 and BY-027 with corrected queries; record the
   AFP `Loebs_Theorem.thy` and HOL-Light `GL/` leads in the registry (F3).
4. Narrow the `Foundations/Basic.lean` import or remove it from the public
   root (F5).
5. Define `LEAN_AVAILABLE`/`LEAN_COMPLETE` semantics in the registry or
   methodology (F6).
6. Decide the public-framing question in F8 consciously before flipping the
   repository public.
