# MAIS-O70: the two source-fidelity adjudications

Two interpretive decisions determine whether the atlas's MAIS-O70 statements say
what the printed problem says. Both were made against `agendas/A6/MAIS-A6.tex`
read verbatim — not against the candidate solution — and both are load-bearing:
reverse either one and the Lean statements it governs would have to be rewritten
before any grade attached to them could stand.

This file is the tracked record of those two decisions. It lives here rather than
in the review tree because that tree is `.gitignore`d: reasoning a reader cannot
clone is reasoning that, on release, does not exist. Everything needed to check
the decisions is restated below; nothing here points at a file a cloner cannot
open.

---

## ⚠ STATUS: BOTH ADJUDICATIONS ARE DRAFTS AWAITING A HUMAN COUNTERSIGN

**Neither verdict below is approved.** The project's rule is that no agent
finally adjudicates its own statement: **agents draft, a human adjudicates
against print.** What follows is an agent's application of a criterion the
maintainer set, with print quoted verbatim so the reasoning is checkable in one
pass. It is not the adjudication itself.

The criterion, as set by the maintainer and recorded verbatim:

> "i need faithfulness to MAIS problem statement, otherwise i need closeness to
> submitted proof in issue #3 unless there is some smarter or more efficient way"

Do not read anything below as settled. Until the block below is filled in, both
verdicts are **proposed readings of print**, and any downstream grade that
depends on them inherits that provisional status.

### Countersign

| adjudication | verdict as drafted | countersigned by | date |
|---|---|---|---|
| 1 — radius quantifier | generic-radius exact (`HasExactLocalPair` as written) | *(unsigned)* | *(undated)* |
| 2 — P3 reading | the fiber minimum | *(unsigned)* | *(undated)* |

```
Countersigned by: ______________________________    Date: ______________
```

A countersign is a statement that the reader has re-read the quoted print and
agrees the verdict follows from it. Filling in a name records that; nothing else
does, and no gate script checks this file.

---

## The printed problem, and what is pinned

`MAIS-A6.tex` `\label{prob:calibration}` (`\Oid{70}`, "Local coefficients on the
template"), verbatim:

> For reduced-rank regression with parameters $(N,M,H,r)$, prove that the local
> pair $(\lambda(w^*),m(w^*))$ at a factorization $w^*=(A,B)\in W_0$ depends only
> on $(\rank A,\rank B)$, and compute the resulting table. Hence characterize the
> strata on which $\lambda(w^*)$ equals the minimum in Theorem~\ref{thm:aw}. For
> example, when $N=M=H=2$ and $r=0$, a neighborhood of $(I_2,0)$ has local
> coefficient $2$, whereas the table gives $3/2$.

Three obligations — **(P1)** rank-dependence, **(P2)** the table, **(P3)** the
minimizing strata — plus an anchor.

The exact bytes graded against are pinned in
[`mais-source-pin.md`](mais-source-pin.md): repository `lionellevine/MAIS` at
commit `9dd29f8bf5ccd1e7701e300039b09ed4096b6516`, with
`agendas/A6/MAIS-A6.tex` at
`sha256:3da2eda1b1fa9633d09e48c4ce3bab34bc22aeea4bfc72eeb04b6b919b1c1d3e`. The
statement source is the `.tex`; `open-problems/MAIS-O70.md` is a one-page
restatement, pinned at
`sha256:69a47687da280365ac2023ef4b69d571b472ccae5543251f00058d3683c7a47e`.

The candidate solution is MAIS issue #3 — a paper, not a Lean artifact: Robert
Sneiderman, *Local learning coefficients of reduced-rank regression*, August
2026, attachment `mais_o70_local_rlct_svd.pdf`,
`sha256:405c8cb324884607f3e827cdd915d8ac10ce01b969a7739616474b3fb8401cbe`.

---

## Adjudication 1 — the radius quantifier

### What print says

`MAIS-A6.tex` `\label{def:local}`, verbatim:

> "The **local learning coefficient** λ(w\*) and **local multiplicity** m(w\*)
> are the threshold and pole order, in the sense of Theorem \ref{thm:zeta}, of
> ζ_{w\*}(z) = ∫_{B_ε(w\*)} K(w)^z dw for sufficiently small ε > 0. **They do not
> depend on ε**, nor on inserting any smooth positive density into the integral.
> Equivalently, λ(w\*) is **the exponent** in \eqref{eq:volume} with the volume
> computed over B_ε(w\*)."

`eq:volume` is `vol(ε) = c ε^λ (log(1/ε))^{m-1} (1 + o(1))` as `ε ↓ 0`.

### Verdict as drafted

**Adopt the generic-radius exact form**: exact `c(1 + o(1))` asymptotics at all
but countably many sufficiently small radii. That is `HasExactLocalPair`, as
written in
[`AISafetyAtlas/SingularLearning/LocalPair.lean`](../../AISafetyAtlas/SingularLearning/LocalPair.lean).
It also matches the candidate's Definition 2.1, "for some, equivalently all but
countably many", so the secondary half of the criterion is satisfied too.

### Reasoning

Print's asserted invariant is **the pair**: "they do not depend on ε". Print says
nothing whatever about the constant `c` in `eq:volume`. Demanding exactness at
*every* small radius is a claim about `c`'s existence at each radius — a claim
print never makes, and one the candidate expressly declines. Under
faithfulness-first that is not a stronger reading of print; it is a claim on an
axis print does not have, so it cannot be more faithful, only more expensive.

The co-countable form carries print's actual content: a single `(λ, m)` valid for
all sufficiently small ε.

The rejected alternative at the other extreme — a bare `∃ δ > 0` — was rejected
on a concrete ground, not on taste. It does not determine the pair: for
`K(x) = x²(x-1)⁴` at `w = 0`, the ball of radius `1/2` sees only the zero at `0`
and gives `(1/2, 1)`, while the ball of radius `2` also sees the zero at `1` and
gives `(1/4, 1)`. Both are witnesses for a bare `∃ δ`, so uniqueness — the
property every "the table is `f`" claim leans on — would be unprovable. With the
co-countable quantifier, uniqueness is a theorem (`exactLocalPair_unique`).

A weaker operational relation, `HasLocalVolumeOrder` (two-sided order bounds at
*every* sufficiently small radius), is kept as a separate named relation and is
deliberately **not** identified with the source relation. Both carry a neutral
`(0, 1)` branch for a germ vanishing on a whole neighbourhood.

### The rider attached to this verdict

Print's *primary* definition is the **zeta** pair; the volume form arrives as
"Equivalently". Print therefore licenses the substitution by its own assertion —
which is what makes working in the volume normalization defensible. But an
assertion the atlas relies on and does not prove must be **machine-visible**, not
prose. The rider was: state the substitution in Lean as a named proposition, with
a frozen surface and a named consumer. Proving it stays optional; stating it is
what makes the one deviation from print's primary definition auditable.

**The rider is met, and only by a narrow bridge.** Why it must be narrow is
part of the record, not a footnote to it.

*Why the general bridge will not serve.* The rider is not met by a
**general** bridge: one quantified over every
nonnegative nondegenerate germ with no analyticity hypothesis, together with its
frozen surface and a general conditional theorem
hasZetaPoleOrder_of_exactLocalPair. Those three names are written here without
code formatting on purpose — **no such declarations exist in the tree**. That
proposition is **false**, and no mechanical gate here can see that it is. The
counterexample:
`HasExactLocalPair` pins only the *leading*
behaviour of the sublevel volume, so a germ whose sublevel volume is
`c · ε^λ · (1 + 1 / log(1/ε))` has exact local pair `(λ, 1)` while its zeta
function has a logarithmic branch point at `-λ` rather than a pole. The dropped
hypothesis is the one print itself carries: `def:local` speaks of a nonnegative
**real-analytic** `K`.

*What stands now.*
[`AISafetyAtlas/SingularLearning/ZetaPair.lean`](../../AISafetyAtlas/SingularLearning/ZetaPair.lean)
states print's primary definition and records the counterexample in a section
written precisely where the next person would otherwise restate the general form:

| declaration | what it is |
|---|---|
| `zetaIntegral` | print's `ζ_{w*}(z) = ∫_{B_ε(w*)} K(w)^z dw`, real axis only — the continuation is the thing in question, so it is not built into the definition |
| `HasZetaPoleOrder` | **print's primary definition**: threshold and pole order, via `MeromorphicAt` and `meromorphicOrderAt` |
| `HasZetaRealAxisOrder` | the weaker two-sided real-axis bound, which is all the candidate's Lemma 6.1(ii) gives for a **sharp ball**; recorded so the shape of the gap is visible, and proved nowhere |

The hypothesis itself lives with the O70 frontier, in
[`AISafetyAtlas/Conjectures/MAIS/O70.lean`](../../AISafetyAtlas/Conjectures/MAIS/O70.lean):

| declaration | what it is |
|---|---|
| `O70ZetaPoleBridge` | the bridge at the **O70 germs only**, under the same `∀ M N H, 0 < M → … → ∀ C A B, B * A = C → …` shape the other O70 frontier hypotheses use. Those germs are polynomial, hence real-analytic, which is print's own hypothesis |
| `o70ZetaPoleBridge_iff` | its frozen surface, `Iff.rfl`, with both sides expanded, registered in [`scripts/check_statement_freeze.py`](../../scripts/check_statement_freeze.py) |
| `hasZetaPoleOrder_o70Pair` | **the conditional theorem the rider asked for** — the candidate's table as the *zeta* pair. It is the bridge's sole consumer |

`O70ZetaPoleBridge` is **stated and not proved**. Nothing in the atlas inhabits
it, and nothing here is evidence that it holds. The degenerate branch — on which
any such bridge is *false*, not merely unproved — is not excluded by a side
condition but is unreachable inside the statement's own quantifiers: positivity
of `M`, `N`, `H` plus the unconditional
`not_eventually_rrrLossCoords_eq_zero_of_pos`. Nonnegativity likewise comes from
`rrrLoss_nonneg` rather than from a binder.

*Does the narrow form still meet the rider?* Yes. The rider asked that the one
deviation from print's primary definition be a Lean constant with a frozen
surface and a named consumer rather than a sentence in a design note. It is, and
the consumer is the theorem the rider named. The rider said nothing about
generality, and the standing stop rule — formalize only the specialized results
actually consumed — is what the narrow shape follows.

Meeting this rider does **not** countersign this adjudication. The verdict above
still awaits a human countersign; the status block at the top stands unchanged.

The full frontier accounting for `O70ZetaPoleBridge` — statement, provenance,
risk, and every declaration that consumes it — is in
[`o70-frontier-manifest.md`](o70-frontier-manifest.md).

---

## Adjudication 2 — the P3 reading

### What print says

`MAIS-A6.tex` `\label{thm:aw}`, verbatim:

> "The global learning coefficient λ and multiplicity m are as follows … .
> **Equivalently, λ is the minimum of λ(w) over w ∈ W₀, and m is the largest m(w)
> among the minimizers**:"

### Verdict as drafted

**The fiber minimum.** P3's "the minimum in Theorem `thm:aw`" means
`min_{w ∈ W₀} λ(w)`. The global-RLCT theorem of Aoyagi–Watanabe is **not** a
dependency of P3.

### Reasoning — this is print's own identification, not an interpretive preference

Three readings were on the table: (1) numeric equality with the published
Aoyagi–Watanabe value; (2) the fiber minimum; (3) importing the Aoyagi–Watanabe
global-RLCT theorem as a hypothesis and reading P3 against it.

Print *itself* identifies the minimum in `thm:aw` with `min_{w ∈ W₀} λ(w)`, in
the same sentence that defines the target. Reading 3 would therefore be assuming
an identification print states outright. The three-reading ambiguity raised
during planning is resolved **by print**, against the drafting agent's own
framing of it as open. That is why this verdict is drafted as a reading forced by
the text rather than as a choice among defensible options — though, like
adjudication 1, it still awaits countersign.

### Consequences

- A global-RLCT hypothesis (`O70-AW-GLOBAL` in the planning notes) leaves the P3
  path **entirely**. It is not one of the atlas's frontier hypotheses; the three
  that exist are listed in [`o70-frontier-manifest.md`](o70-frontier-manifest.md)
  and none of them is a global-RLCT import. Numeric agreement with the published
  Aoyagi–Watanabe value survives only as an optional cross-check.
- `IsO70FiberMinimumTable`'s lower-bound-plus-attainment shape is exactly print's
  "λ is the minimum of λ(w) over W₀". It is kept as written: `awLambda M N H r`
  is a lower bound for the table on every admissible rank stratum, and some
  admissible stratum attains it.
- `IsO70MinimizerCharacterization` needs no global-RLCT conjunct.

### What P3 does and does not ask

`prob:calibration` asks to characterize the strata on which **λ(w\*)** equals the
minimum. It does not ask about multiplicity at those strata. So the `m`-clause of
`thm:aw` is not part of P3's target, and `IsO70FiberMinimumTable` is right to
range over λ alone. The multiplicity clause matters only as the mechanism of a
separate finding about the agenda's own conventions (below).

### A consequence for `rem:conventions`, recorded because print sharpens it

`thm:aw` says `m` is "the largest m(w) among the minimizers", while
`rem:conventions` guarantees only that "W contains a neighborhood of **a**
factorization attaining the Aoyagi–Watanabe minimum". A neighborhood of *a*
minimizer does not deliver the *largest* multiplicity among minimizers. The
smallest witness is the scalar model `M = N = H = 1`, `r = 0`: all three feasible
strata attain λ = 1/2, and only the origin has `m = 2`, so a `W` that is a
neighborhood of ranks `(a,b) = (0,1)` alone yields the global pair `(1/2, 1)`
rather than `thm:aw`'s `(1/2, 2)`.
[`scripts/reproduce_o70_table.py`](../../scripts/reproduce_o70_table.py)
recomputes this from the printed formulas alone and finds 640 such witnesses
among tuples with `M, N, H ≤ 6`. Reading 2 does not create this gap — it makes it
visible, because "largest among the minimizers" is what makes the support
condition insufficient.

---

## The three fidelity checks that were run rather than assumed

These are checks on whether the candidate answers *print's* question at *print's*
quantifiers. They grade the statement, not the proof.

**(i) The loss is print's loss.** Print defines
`K(w) = E_{x~q}[KL(q(·|x) ‖ p(·|x,w))]` for the model
`p(y|x,w) = (2π)^{-M/2} exp(-½‖y - BAx‖²)` with `x ~ N(0, I_N)`. For unit-variance
Gaussian outputs, `KL(N(Cx,I) ‖ N(BAx,I)) = ½‖(BA - C)x‖²`, and `E_{x~N(0,I_N)}`
of that is `½ tr((BA-C)(BA-C)ᵀ) = ½‖BA - C‖²_F`. The candidate states exactly this
identity and works with it. **No narrowing.** The atlas does not take the
identity on trust either: `rrrLoss` in
[`AISafetyAtlas/SingularLearning/Loss.lean`](../../AISafetyAtlas/SingularLearning/Loss.lean)
is the *Gaussian expectation* print prints, and the Frobenius form is
`rrrLoss_eq_frobenius`, a **theorem** — so the substitution is performed once, in
public, with a proof.

**(ii) The dependence claim sits at print's quantifier.** Print says the pair
depends only on `(rank A, rank B)`. The candidate's formula also involves `r`,
through `h = H - a - b + r`. That is not a narrowing: `r` is fixed by the truth,
which print fixes *before* quantifying over `w* ∈ W₀`. Within one fiber the
dependence is exactly on `(a, b)`. **Same as print.**

**(iii) The multiplicity is required by print, not a bonus.** Print asks for the
*pair* `(λ(w*), m(w*))`, so the multiplicity `m₀` is an obligation, not an extra.
(What *is* extra is the candidate's pointwise identity `λ = ½ codim`, which is
outside MAIS-O70 entirely.)

### Scope verdict

**The candidate answers MAIS-O70 at print's quantifiers, and is wider than print
on P2 and P3; no axis is narrower.**

| | printed obligation | candidate | grade |
|---|---|---|---|
| P1 | local pair depends only on `(rank A, rank B)` | Theorem 1.1, last sentence | Same as print |
| P2 | compute the resulting table | Theorem 1.2 (five branches) + Corollary 1.3 (unified min form) | Wider than print |
| P3 | characterize the strata attaining the minimum in `thm:aw` | Corollary 11.2, with an excess formula print does not ask for | Wider than print |
| anchor | `(I₂,0)` gives `2`, table gives `3/2` | reproduced | Reproduced |

By the standing scope rule (scope ≥ print), there is **no scope defect to
close**. Note carefully what this verdict is about: it grades the *candidate's
statement* against print. It is not a claim that the candidate's proof is
correct, and it is not a claim about what the atlas has verified.

---

## What the countersign blocks, and what it does not

**Blocked.** The specification gate for MAIS-O70 carries an explicit checklist
item: *a human fidelity verdict against print, written down, separately deciding
the radius normalization and whether P3 means numeric equality, fiber-minimum
equality, or the stronger global-RLCT theorem.* That item is satisfied when a
human countersigns these two verdicts — not when this file is written. Until
then the specification gate has an open box.

**Not blocked.** The arithmetic P3 gate is adjudication-independent: its
obligations are kernel checks about the candidate table over the admissible rank
strata (`o70_fiber_minimum_correct` for `IsO70FiberMinimumTable o70Pair`,
and `o70_aw_value_strata_correct` for
`IsO70AWValueStratumTable o70Pair o70Minimizers`), symbolic over all natural dimensions rather than extrapolated
from a finite search. Those proofs are what they are regardless of how the two
adjudications are countersigned. Likewise unaffected are the loss identity, the
orbit reduction, the elimination chart and the chamber calculus, none of which
turns on either verdict.

**Exposed rather than blocked.** Adjudication 1 fixes the *shape* of
`HasExactLocalPair`, and every statement that mentions it — the exact-pair-level
tables, `IsO70MinimizerCharacterization`, `O70ZetaPoleBridge`,
`O70ExactLocalPairsExist` — is written against that shape. A reversed
countersign on adjudication 1 would not falsify any proved theorem, but it would
mean those statements are no longer the ones print asks for, and each would have
to be restated and re-graded. That is the concrete cost of the open box, and it
is why the box is worth keeping open rather than quietly closing.

## Standing caution

**Nothing in this file resolves MAIS-O70, and nothing here verifies the
candidate's proof.** MAIS lists O70 as open with a full solution pending review;
the atlas's own conjecture row for it is `OPEN`. The atlas holds no unconditional
inhabitant of the P1/P2 targets: those stand behind named frontier hypotheses
that are stated and not proved, enumerated in
[`o70-frontier-manifest.md`](o70-frontier-manifest.md). What is established
unconditionally is narrower than the problem, and is described there and in the
conjecture row rather than here. This file records only *how the printed question
was read*, and both readings are still awaiting a human countersign.
