# Upstream contribution drafts

Contributions this repository owes the ecosystem, drafted and **not filed**.

[`lean-routing.md`](../agent/policy/lean-routing.md) says generic mathematics
built here stays here *and* is offered upstream, and that the decision is
recorded either way. This file is where the offer is drafted.
[`workflow-branch-publication.md`](../agent/policy/workflow-branch-publication.md)
says publication outside this repository is maintainer-authorized, so nothing
here has been sent. Each entry is ready to paste and needs a decision, not more
writing.

**Why this file exists at all.** The traffic has run one way. This tree consumes
`vendor/SocialChoiceLean`, `vendor/debate`, `vendor/TauCeti`, Foundation and
PFR, and has contributed nothing back to any of them.
`AISafetyAtlas/Upstream/KolmogorovMathlib/` has carried the exemption reason
*"staged for upstreaming to Mathlib"* since 2026-07-19. Recording the drafts
does not discharge the debt, but it does stop the debt from being invisible.

---

## D1 — Tau Ceti: an intention for the parameterized splitting lemma

**Target.** [`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti),
`[Intention]` issue template.

**Why this one first.** Their `CONTRIBUTING` says roadmaps are *"where human
judgement is worth the most, so that is what this repository asks of you"*, and
that *"substantive review, especially from a subject-area expert, is the thing
we are shortest of"*. An intention is the cheapest honest form of that: it names
a gap where the people who could close it will see it, and commits nobody.

**Status.** Drafted. Not filed. The consumption half of this relationship is
already done — the Morse cone is vendored under `vendor/TauCeti/` with its
provenance recorded — so filing this is what makes the exchange two-way rather
than extraction.

> **Title:** Parameterized splitting / Morse–Bott lemma at a degenerate critical point
>
> **What is missing.** Your `Analysis/Calculus/Morse/` carries the Morse lemma
> in a Banach space for a *nondegenerate* critical point, in the Palais form.
> What has no counterpart **there, nor in Mathlib at the revision this
> repository pins** — searched 2026-09-07 for `MorseBott`, `Morse-Bott`,
> `GromollMeyer` and `splittingLemma`, all zero hits, and Mathlib has no
> `Analysis/Calculus/Morse/` at all — is the degenerate case: a splitting
> (Gromoll–Meyer / Morse–Bott) normal form at a critical point whose Hessian
> has nontrivial kernel, and its parameterized version, where the critical
> point and the splitting vary with a parameter. That is two trees searched by
> name, not a claim about the literature.
>
> **Why it is wanted.** Loss landscapes of over-parameterized models are
> degenerate everywhere that matters: the critical set is positive-dimensional
> and the Hessian is singular along it, so the nondegenerate Morse lemma applies
> at no point of interest. The parameterized splitting lemma is the standard
> route from a local normal form to an asymptotic statement about such a family.
>
> **What exists in your tree already** that a roadmap could build on: the
> operator square root, the bilinear-form machinery, and the congruence normal
> form in `Analysis/Normed/Algebra/SquareRoot.lean` and
> `Analysis/Calculus/Morse/NormalForm.lean` — paths relative to `TauCeti/`,
> both of which this repository vendors under `vendor/TauCeti/`. The degenerate case needs the
> kernel/range splitting and an implicit-function step on the range factor,
> rather than new analysis at the bottom.
>
> **What I am offering.** A roadmap, if the area owner wants one, and review of
> the statement from the consumer side. I am not offering the proof.

**What would change this entry.** If a roadmap is written, this becomes a
roadmap entry rather than an intention. If Mathlib acquires the splitting lemma
first, the entry is closed with a pointer and the vendored cone is reconsidered
against it.

---

## D2 — Mathlib: the Kolmogorov-complexity staging area

**Target.** Mathlib, as a sequence of small PRs rather than one.

**Status.** Drafted only as a scope note; no PR text yet, and the split below is
a proposal rather than an agreed shape.

`AISafetyAtlas/Upstream/KolmogorovMathlib/` is exempted from example coverage on
the grounds that it is *staged for upstreaming to Mathlib, which carries its own
test discipline*. That exemption has been true for fifty days and load-bearing
for none of them, which makes it a claim about intent that nothing tests.

The tree is `Core/Basic`, `Foundation/{NatEncoding, RecursivelyEnumerable,
UnboundedSearch}`, and `Complexity/{NatComplexity, Properties, Incompressibility,
Uncomputability, Chaitin}`. Only the last is atlas-specific in motivation; the
foundation layer is ordinary computability theory.

**The decision this entry is really asking for** is not the PR split. It is
whether the exemption should keep saying *staged for upstreaming*. If the answer
is that the material stays here indefinitely, that is a legitimate outcome under
`lean-routing.md` — but then the exemption reason should say *kept here, and
why*, because an intent that is never acted on and never withdrawn is the shape
of a claim nobody has to defend.

---

## D3 — Domain-neutral results with no upstream home yet

Recorded so they are not lost, and so the routing decision on each is visible as
outstanding rather than absent. None is drafted as a submission.

| Result | Where it lives | Generic? |
|---|---|---|
| Maximal minors of a rectangular matrix | `Analysis/MaximalMinor.lean` | yes — the module's own note says the rectangular statement is absent upstream |
| Null bound for a hyperplane family | `Analysis/NullImage.lean` | yes — stands in for semialgebraic dimension theory the pinned Mathlib lacks |
| Polynomial genericity | `Analysis/PolynomialGenericity.lean` | yes |
| The Laplace / Tauberian / layer-cake layer | `SingularLearning/` | yes, and the largest block of it — 36 modules, most of them domain-neutral analysis |

The `SingularLearning` row is the one that matters. It is the biggest single
body of generic mathematics in the tree, it has one ledger consumer, and no
routing decision is recorded for any of it. Under `lean-routing.md` that is not
a defect in the mathematics; it is a decision nobody has taken.
