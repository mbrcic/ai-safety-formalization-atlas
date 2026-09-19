# Where a result lives, and where it is also offered

[`lean-reuse-sources.md`](lean-reuse-sources.md) says where to look before you
build. [`lean-parsimony.md`](lean-parsimony.md) says when a second formalization
of the same thing is allowed. Neither says where a result you *do* build
belongs. This file is that rule.

## Routing

| | Generic mathematics | AI-safety-specific |
|---|---|---|
| **Small / bounded** | build it here, offer it upstream | direct atlas change |
| **Large / project-scale** | build it here, offer it upstream; consider a roadmap with the library whose job it is | workspace, then graduate a facade |

**Generic mathematics** is a statement whose truth does not mention an agent, a
policy, an observer, a safety property, or any other object this repository
exists to talk about. Laplace-method asymptotics, a Tauberian theorem, maximal
minors of a rectangular matrix, a null bound for a hyperplane family, and the
measurability of a projection are generic. Ashby's law over an overseer's
variety is not, even though its proof is counting.

## Keep **and** contribute — never "send it away"

The rule is not that generic mathematics is unwelcome here. It is that generic
mathematics has **two** homes and this repository is one of them.

- **Keep it.** A proof this tree needs stays in this tree, ledgered as a `LAND-`
  artifact row under [`ledger-coverage.md`](ledger-coverage.md), on the root
  import if a consumer names it. Removing a working proof because it is generic
  makes the atlas attempt less and helps nobody.
- **Offer it.** The same result is proposed upstream — Mathlib for the general
  body, or the downstream library whose subject it is (see the ecosystem table
  in [`lean-reuse-sources.md`](lean-reuse-sources.md#where-the-mathematics-is)).
  Contributing costs a PR and buys reach, review, and maintenance by someone
  else.

Consuming from the ecosystem without ever contributing to it is extraction, and
it is also a maintenance bet against yourself: every generic proof kept only
here is one this repository alone will carry through every future toolchain
migration.

**Neither half substitutes for the other.** Vendoring a library's code and
writing that library a roadmap are the same decision seen twice; doing only the
first takes, and doing only the second gives away work the tree needs.

## Record the decision either way

The point of the rule is that the decision gets **made and written down**, not
that it always comes out the same way. Both outcomes are legitimate and both are
recorded:

| Outcome | Where it is recorded |
|---|---|
| Offered upstream | the row's `notes`, naming the PR or issue; and the entry in [`external-formalizations.md`](../../provenance/external-formalizations.md) if it lands |
| Drafted, awaiting authorization | [`upstream-contribution-drafts.md`](../../provenance/upstream-contribution-drafts.md) — where an offer waits for the maintainer to send it |
| Deliberately kept only here | the row's `notes`, with the reason — an unstable API, a pin the upstream cannot take, a statement shaped for this tree's consumers, or a judgement that the upstream would not want it |
| Not yet decided | nothing to record, but the result is not finished |

A generic result with no routing note is not a defect in the mathematics. It is
a decision nobody has taken, and "we decided not to" and "we never got to it"
must not be indistinguishable — that is the same anti-overclaiming discipline
[`ledger-coverage.md`](ledger-coverage.md) applies to grades, applied to
provenance.

## What this rule does not do

- It does not require a PR before a result may land here. Upstreaming is slow,
  upstreams reject things, and blocking the tree on someone else's queue would
  trade the constraint this repository actually has (speed of discovery) for one
  it does not.
- It does not authorize opening a PR or an issue anywhere. Publication outside
  this repository is maintainer-authorized —
  [`workflow-branch-publication.md`](workflow-branch-publication.md). Draft the
  contribution, record the intent, and stop there.
- It does not make "is this generic?" a gate. No script decides it; a reviewer
  does. The boundary case — a domain-neutral lemma proved because one safety row
  needed it — is generic, and the note saying so takes one sentence.
