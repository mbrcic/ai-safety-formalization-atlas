# A governance-kernel sketch — the one section built from it

**Date.** 2026-09-12.

**Status.** Not a published source, not graded in
[`source-coverage-audit.md`](source-coverage-audit.md), and no registry row
cites it as print. It is an externally supplied sketch, held privately, produced by a model that could see only the public branch of
this atlas. This note exists so that the one result taken from it has a pinned
origin rather than a remembered one.

## The document

Held privately; the files and their hashes:

| File | sha256 |
|---|---|
| `FORMAL_SPECIFICATION.md` | `419a02dd7a24a0d28e49434310cf610673b448b21e56aaaf90d142efe905d695` |
| `COVERAGE.md` | `9042d2cdbfac5e4ad1bc772e0ea02043e3586b6b59c453c08851382fad18c08b` |
| `INTEGRATION.md` | `71a1df218f2e42d731562b57c0cc6868fa5942db2dbea8ce44c815026d57d2f6` |

Titled, on its own first line, *Governance, agency, and cognitive sovereignty:
an Atlas integration specification*. Seventeen sections, numbered 0 to 16: status
and interpretation; the common interface; norms; institutions; constitutions and
amendment; delegation and revocation; epistemics and implementable coordination;
incentives, equilibrium and cores; enforcement and detection; contestability;
hyperproperties and cognitive authorship; preference change and capture;
preservation and mandate drift; collective procedures, voting power and
complexity; required transports; one worked arrangement; verification and open
semantics.

**What the directory does not hold.** `COVERAGE.md` and `INTEGRATION.md`
reference fourteen Lean files, forty-two proof scripts, one hundred nineteen
declarations, 6,091 executed checks, `evidence/declarations.json`,
`scripts/Audit.lean` and `tests/governed_review.py`. The directory contains the
three Markdown files above and nothing else. Every claim in this note is
therefore graded against the prose of `FORMAL_SPECIFICATION.md` alone, and the
evidence class those two files describe is treated as **absent**, not as
unverified. The full reading is
in a private note.

## What was taken

**§6.3, the uniform decision boundary (`GE5`, `GE6`).** Print states, for a
nonempty action type and classically:

> ∃ d : O → A, ∀ w. Good(w, d(o(w)))
> iff
> ∀ v ∈ o(W). ⋂_{w : o(w) = v} { a : Good(w, a) } ≠ ∅

with `GE5` the proof ("a uniform controller supplies a common action per fibre;
conversely choose one common action per realized fibre and an arbitrary
unused-observation value"), and `GE6` the obstruction ("two observationally
identical contexts with disjoint acceptable-action sets defeat every
observation-based controller; full state observability is unnecessary when a
shared acceptable action exists").

Built as `AISafetyAtlas.Knowledge.UniformAction`, registry row
`LAND-KNOW-UNIFORM-001`.

| Print | Atlas | Relationship |
|---|---|---|
| the existential controller | `UniformlyActionable` | Same |
| the fibre-intersection criterion | `uniformlyActionable_iff_iInter_nonempty` | Same, at `Type`, with print's own `[Nonempty A]` |
| `GE5` | `uniformlyActionable_iff_fibrewiseAgreeable` | Wider: at `Sort`, and with the fibre indexed by a state rather than by a realized observation value, which removes the realizability side condition |
| `GE6` | `ActionConflict`, `not_uniformlyActionable_of_conflict` | Same, and explicitly **sufficient only** |
| "add discriminating information" | `UniformlyActionable.mono` | Same |
| "make a common safe action available" | `uniformlyActionable_of_universal`, `UniformlyActionable.mono_good` | Wider: print names the universal action, the atlas also carries the monotonicity in acceptability that contains it |
| — | `knowable_iff_uniformlyActionable` | Atlas-side: print does not know this repository's `Knowable`, and the bridge makes the generalization a theorem |
| — | `not_uniformlyActionable_iff_exists_unservable` | Atlas-side: the certificate that is necessary as well as sufficient |

## The published anchor, found

**Fetched and read 2026-09-13**: F. Lin and W. M. Wonham, *On Observability of
Discrete-Event Systems*, Information Sciences 44:173–198, 1988,
`10.1016/0020-0255(88)90001-1`; held, sha256 `73030c40…`, manifested in
the private manifest of 2026-09-13.
Read at folios 177–181 from rendered page images.

The question put to it was whether its observability condition is pairwise and,
if so, why it is nonetheless complete. Both halves answered:

* **p. 177.** Observability is `ker P ≤ act_K`, where `(s,s') ∈ act_K` iff
  `A_K(s) ∩ IA_K(s') = ∅ = A_K(s') ∩ IA_K(s)` and the two strings agree on
  membership in `K`. A relation on **pairs**.
* **p. 178.** `act_K` *"is a tolerance relation on Σ*, i.e. is reflexive and
  symmetric"* — and so not transitive, which is exactly the shape that makes a
  pairwise condition look too weak.
* **p. 181, Theorem 2.1.** A proper supervisor achieving `K` exists **iff** `K`
  is controllable and observable. So it is not too weak.
* **p. 179 is the reason.** The "If" direction builds the supervisor as *any*
  `ψ : Σ × X → {0,1}` with `ψ = 1` on `Σ¹_x = ⋃{A_K(s)}` and `ψ = 0` on
  `Σ⁰_x = ⋃{IA_K(s)}`, observability being used only to prove those two unions
  disjoint. **One binary decision per event.**

That is now a theorem here rather than a remark:
`uniformlyActionable_of_pairwiseAgreeable_of_card_le_two`. At most two actions
and pairwise agreement forces a uniform rule; the module's three-action
counterexample is the sharpness witness, so the incompleteness result **delimits
print rather than contradicting it**.

Graded `RELATED`, not `EXACT`. Lin & Wonham work in languages, supervisors and
controllability jointly over a discrete-event generator; this module has one
observation map, an arbitrary action type and no controllability. What transfers
is the mechanism, not the theorem.

**A wrong generalization was refuted on the way**, recorded so it is not
retried: "per-coordinate binary actions make pairwise sufficient" is **false**
for an arbitrary predicate on a product — `{TT,TF}`, `{TF,FF}`, `{TT,FF}` over
`Bool × Bool` are pairwise intersecting and jointly empty. The two-element
codomain is doing the work, not the product structure.

Cieslak, Desclaux, Fawaz & Varaiya (IEEE TAC 33(3), 1988) also arrived and is
pinned with its face read. Its subject is the **decentralized** case — several
controllers each observing partially — which is a different question and was not
what this row needed.

## One correction to print

`GE6` is stated as *the* obstruction. It is not complete. Acceptable-action
sets can be pairwise intersecting and jointly empty: three states on one fibre
with sets `{1,2}`, `{0,2}`, `{0,1}` admit no `ActionConflict` and no uniform
rule either. `AISafetyAtlas.Examples.Knowledge.UniformAction.conflict_is_not_complete`
is that witness, proved in both halves.

This is where the module differs structurally from the `Knowable` kernel, and
the difference is not cosmetic. `exists_witness_of_not_knowable` produces a
*pair* whenever knowability fails, because equality is transitive. Compatibility
of acceptable-action sets is not, so the necessary certificate here has to be an
empty fibre.

Print does not claim the converse of `GE6` in words. It does present the pair as
the diagnosis, and a reader carrying that into a Lean development would state
the iff. The witness blocks it.

## What was checked and not taken

`demandwise_iff_exists_selector` in `AISafetyAtlas.Sovereignty.Catalogue` has
the same logical shape — a uniform witness against a family — and is **not** an
instance of this, nor is this an instance of it. Its index is the demand a
coalition must serve; this one's index is what an observer can see, and the
obstruction lives on observation fibres, which the catalogue layer has no notion
of. Both are named in the module docstring so a later reader does not merge
them.

## What remains open in the document

Recorded so the omission is a decision rather than an oversight:

* §2.1's four-valued norm annotation and §3.1's guarded-Horn `Derives` both sit
  downstream of the deontic question — whether this repository takes on *may
  not* at all — which is unanswered.
* §7's coalition-proofness recursion is delivered as prose plus a Python model
  that is not in the directory.
* §11.3's complement relation (line 581) is already
  `lowerValue_add_opponentLowerValue_le_one`; nothing to build.
* Its §5 and §12 are not open questions but **corrections to this side**. The
  sketch's §5, under *Installed revocation versus effective withdrawal* (line 267),
  says the `recoveryRank ≤ H` theorem is
  applicable only once its recovery target is shown to mean withdrawn effective
  authority, intermediate states are shown viable, and the scheduler assumptions
  are shown to match — "not an unrestricted iff between revocability and mandate
  preservation". Its §12 says a product of per-step retentions does not give
  eventual failure, and that mandate drift needs an explicitly fixed protected
  family. Both land on a private working note of the maintainer's,
  whose §4 and §1.1 asserted the contrary; the dated strikes are there, not here,
  and neither claim ever entered this repository.
