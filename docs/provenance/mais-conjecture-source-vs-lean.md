# Conjectures side by side: source text, Lean statement, Lean read back

Every live MAIS-linked ledger conjecture — the eight of the nine whose source
is a MAIS agenda or one of its issues; CONJ-002 grades against an
information-theory survey and is out of scope here — in three columns of prose:
**what the source prints**, **what the Lean says**, and **what the Lean says
translated back into English from its binders rather than from its intent**. The last column is the
one that earns the document — it is written from the quantifier structure, not
smoothed toward the source's phrasing, so that a mismatch is visible rather than
argued away.

A fourth block per row, **The delta**, states what differs and why the row is
still graded as it is.

## Provenance

Everything below was read from these bytes. **What was re-verified for this move,
and what was not**, because the two are not the same and a table of ticks hides
the difference: the repository artifacts were recomputed from a local clone
checked out at the pinned commit with a clean tree — `MAIS-A2.tex`,
`MAIS-A2.pdf` and all six `open-problems/*.md` pages match
[`mais-source-pin.md`](mais-source-pin.md) exactly.

**Amended 2026-08-27**, when CONJ-025 was added from agenda **A3**. That pass
fetched `agendas/A3/MAIS-A3.tex` and `open-problems/MAIS-O38.md` at the pinned
commit and diffed them against `main`: identical, so the pin and the branch are
not on different problems. It also re-fetched the three 2026-08-20 issue bodies,
which still match, and read MAIS issue #30 for the first time. Everything else
below was left as read on 2026-08-23 and was **not** re-derived; issue bodies are
served by the GitHub API rather than carried in the tree, so a silent edit
between readings would not have been caught.

| artifact | value |
|---|---|
| MAIS repository | `github.com/lionellevine/MAIS` |
| MAIS commit | `9dd29f8bf5ccd1e7701e300039b09ed4096b6516` |
| `agendas/A2/MAIS-A2.tex` | sha256 `d61be3eed51f618dd3b9389693b14e066e89a9cef5e89985b4226fff658c3c4f` — recomputed 2026-08-23, matches pin |
| MAIS issue #4 body | sha256 `f425da83395b457feb5615c9beed703675a977967890ebe1b97dd61efdd0b328` — recorded 2026-08-20, re-fetched 2026-08-27, matches |
| MAIS issue #4 author comment | sha256 `e290bb83bd980cc9a9b8a3610e21ec6e26a0aa5c3d2e036db10b2610d909bca8` — as recorded 2026-08-20, not recomputed; a rendering note only, not part of the mathematical candidate |
| MAIS issue #8 body | sha256 `8e2e688eaac1a72f915aa787ad1e74676e6b72eff4f2796394e95b0a83fb8a96` — recorded 2026-08-20, re-fetched 2026-08-27, matches |
| `agendas/A3/MAIS-A3.tex` | sha256 `146f0cc95a0a5eb0cf3b2660c32d591169b0e346571b80ee63723a9906371387` — fetched 2026-08-27, the statement source for CONJ-025 |
| MAIS issue #30 body | sha256 `6e2db10eb10242c075ca331fcf87a604511b9b31df3d55a5c4b0d2d2d95d05ab` — read 2026-08-27; context for CONJ-025, not its graded artifact |
| atlas commit the Lean was read from | the tip of the branch this file is part of; the reproducible pin is the toolchain and build evidence below, not a hash this file could state about itself |
| toolchain | `leanprover/lean4:v4.31.0`, Mathlib `fabf563a7c95a166b8d7b6efca11c8b4dc9d911f` |
| build evidence, measured at that commit | root `lake build` 3331 jobs, `scripts/lean_build_targets.txt` 4004 jobs; `check_print_axioms` 2495 declarations ⊆ `{propext, Classical.choice, Quot.sound}` |

Two structural points about the reading below. The MAIS-O25 adaptivity
constant `c` is bound in `maisO25_exactQueryRate`'s outer existential, before the
class, as print chooses it. Every MAIS-O27 target carries a characterization
lemma, which is what lets an instance be proved from another module rather than
argued: `HasRealFirstOrderRadius` and `RealEdgeStrengthAtLeast` are non-exposed
`public def`s, and without `hasRealFirstOrderRadius_iff` and
`realEdgeStrengthAtLeast_iff` a clause could be named downstream and reasoned
about nowhere.

**Two things surround the rows without changing them.** MAIS-O27 was lifted to `prob:floor`'s own real quantifier in all three clauses —
`O27RealRadiusVanishes`, `O27RealHasFirstOrderConstant`,
`O27RealEdgeSurvivalRegion`, bundled as `o27RealProblemTargets` — so the rational
predicates are now the transported instance rather than the statement of record,
and two of the clauses have negative instances there. O27 has no *conjecture*
row either way, being a determine-problem; since 2026-08-24 each of its three
clauses has a target row naming the specification a proposed answer must
satisfy.
MAIS-O31's chart was proved onto the printed class by
`exists_O31ChainModel_toModel_eq`, and `o31IdentifiesCoordinate_iff_class` and
`o31IdentifiesNodeMass_iff_class` carry the two identification predicates to that
class, so the row's chart-quantified predicates are now *equivalent* to their
statements over every model of `𝕄(sk, λ)` carrying the chain graph — which is the
comparison class `q:chain` names in its own parentheses. That removes the
one-directional bridge CONJ-010's delta used to disclose. Nothing else in the
transcriptions changed.

## Where each row's Lean lives

Since 2026-08-23 the statement and proof layers are **one module per printed
problem** rather than two long files, so checking one row means opening one file
on each side. Every declaration kept its namespace, so no name below moved.

| Row | Target | Statement | Proof |
|---|---|---|---|
| CONJ-004 | O23 | `AISafetyAtlas/Conjectures/MAIS/O23.lean` | `AISafetyAtlas/Examples/Conjectures/MAIS/O23.lean` |
| CONJ-006 | O25 | `…/MAIS/O25.lean`, rate predicates in `…/MAIS/Rates.lean` | `…/Examples/…/MAIS/O25.lean`, `…/Rates.lean` |
| CONJ-003 | O26 | `…/MAIS/O26.lean`, rate predicates in `…/MAIS/Rates.lean` | `…/Examples/…/MAIS/O26.lean`, `…/Rates.lean` |
| CONJ-008 | O29 | `…/MAIS/O29.lean` | `…/Examples/…/MAIS/O29.lean` |
| CONJ-010 | O31 | `…/MAIS/O31.lean`, chart and transport in `…/MAIS/O31Chart.lean` | `…/Examples/…/MAIS/O31.lean`, positive-measure counterexample in `…/O31Measure.lean` |
| CONJ-005 | O34 | `…/MAIS/O34.lean` | `…/Examples/…/MAIS/O34.lean` |
| CONJ-009 | O34 | `…/MAIS/O34.lean` | `…/Examples/…/MAIS/O34.lean`, fibre criterion in `…/Examples/Conjectures/O34Fiber.lean` |
| CONJ-025 | O38 | `…/MAIS/O38.lean` | `…/Examples/…/MAIS/O38.lean` |

`AISafetyAtlas/Conjectures/MAIS.lean` and its `Examples` counterpart are now
aggregate shims that import these and declare nothing, so a permalink into
either points at an import list rather than at a statement. MAIS-O27 has modules
on both sides and no *conjecture* row; it has one target row per clause since
2026-08-24, and the reason for the distinction is below.

**Issue bodies are editable in place** and carry no revision history a permalink
can address. The hashes above are the bytes as read on the dates each row states;
an edit by their authors changes the hash and invalidates whatever rests on it,
which is the point of recording them. Only #4 and #8 carry a *grade*: #30 is
context for CONJ-025 and an edit to it invalidates a provenance note rather than
a verdict.

## What the two grades promise, for a reader who does not read Lean

Two columns below carry the whole claim, and neither is about proof. They are
about **what question was written down**, which is the step no proof assistant
checks and the only step in this repository done by hand.

**Scope `Same`** says the Lean proposition sits at the printed statement's own
quantifiers — the same objects, the same "for every", the same "there exists",
the same order between them. It does **not** say the proposition is true, that
its hypotheses can be satisfied, or that the printed problem is settled. Those
are three further questions and this document keeps them apart. The schema's
other values name the ways a transcription can drift: `Narrower` asks about
fewer instances than print, `Mixed` drifts both ways at once, `Beyond` is a
question the atlas asks that print does not. **Every live MAIS row here is
`Same`, and that is enforced rather than asserted** — `scripts/validate_conjectures.py`
rejects a MAIS-sourced row graded anything else, because a defect in a printed
statement is a finding about the source and not permission to repair it.

**Fidelity** says how the sentence was rendered. `Literal` is a transcription:
print states a claim, the Lean states that claim. `Selected` is print asking the
reader to decide a branch — *"decide whether …"* — with the Lean stating one
branch, which is truth-valued where the surrounding *determine* or *characterize*
problem is not. Nothing here is graded `Bridged`, and a MAIS row may not be: a
bridge substitutes an atlas-supplied object for something print leaves implicit,
and on these rows that is forbidden.

**What no grade covers.** Two of the agenda's problems, MAIS-O24 and MAIS-O27,
read *"exhibit …"* and *"determine …"* with no truth-valued clause anywhere in
them. No proposition is the same statement as an instruction to construct
something, so neither has a row at all, and the closing notes say what stands in
their place.

## The eight MAIS-linked rows at a glance

| Row | Source artifact | Target | Status | Scope | Fidelity |
|---|---|---|---|---|---|
| CONJ-004 | agenda `q:ident` | MAIS-O23 | RESOLVED | `Same` | `Selected` |
| CONJ-006 | agenda `prob:exact` | MAIS-O25 | OPEN | `Same` | `Selected` |
| CONJ-003 | agenda `conj:exact` | MAIS-O26 | OPEN | `Same` | `Literal` |
| CONJ-008 | agenda `prob:boltzmann` | MAIS-O29 | RESOLVED | `Same` | `Selected` |
| CONJ-010 | **issue #8** | MAIS-O31 | OPEN | `Same` | `Literal` |
| CONJ-005 | agenda `prob:starter-set` | MAIS-O34 | RESOLVED | `Same` | `Selected` |
| CONJ-009 | **issue #4** | MAIS-O34 | RESOLVED | `Same` | `Literal` |
| CONJ-025 | agenda `prob:samples` (**A3**) | MAIS-O38 | RESOLVED | `Same` | `Selected` |

---

# CONJ-004 — MAIS-O23

Graded against the agenda's `q:ident`. Status **RESOLVED**, scope `Same`,
fidelity `Selected`.

### Source, verbatim

```latex
\begin{question}[\Oid{23}: Do margins suffice?]\label{q:ident}
Fix a skeleton $\sk$ and $\lambda\in(0,\tfrac12)$. If $M,M'\in\MM(\sk,\lambda)$
satisfy $\boldsymbol\Delta_M=\boldsymbol\Delta_{M'}$, must $M=M'$? Equivalently
(by Proposition~\ref{prop:equiv}): can two distinct models in the margin class
share a common family of optimal policies for every observation mask?
\end{question}
```

### Lean, top level

```lean
@[expose] public noncomputable def maisO23_marginsDoNotSuffice : Prop :=
  ∃ (m : ℕ) (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ) (lam : ℝ),
    Skeleton.ValidMargin lam ∧
      ∃ M M' : Model (Fin (m + 1)) (binaryDim (Fin (m + 1))) ℝ,
        sk.MarginClass M lam ∧ sk.MarginClass M' lam ∧
          M ≠ M' ∧ sk.BehaviorEq M M'
```

### Lean read back

There exist a number of chance variables `m+1`, a skeleton over that many binary
chance variables with real-valued tables, and a real margin `λ` that is a valid
margin, such that there exist two models `M` and `M'` over that skeleton, both
of which lie in the six-condition margin class at `λ`, which are **not equal**
and whose complete masked behavioural transforms are equal.

### The delta

Print asks a yes/no question — *"must `M = M'`?"* — and the Lean asserts the
**negative branch**. That is what `Selected` records: a decide-question is not
itself a proposition, and stating one of its two branches is a truth-valued
statement print asked for. The negative branch of a universal is an existential,
which is why the Lean opens with `∃` where print opens with *"if … must"*.

The quantifier over the skeleton and `λ` is existential in the Lean because a
counterexample at one skeleton answers print's question, which is posed after
*"Fix a skeleton and λ"*. Print fixes them and asks about all pairs; the Lean's
negation moves both to the outside as existentials. This is the ordinary
De Morgan reading, not a change of scope.

Print's second sentence — *"can two distinct models share a common family of
optimal policies for every observation mask"* — is the same question via
`prop:equiv`, and `sk.BehaviorEq` is the transform equality of the first
sentence, so the row transcribes the first form.

**Coverage.** The `resolution` field opens *"COVERAGE: THIS ROW IS ALL OF
q:ident."* MAIS-O23 has no clauses, so RESOLVED here is the status of both the
Lean `Prop` and the printed question. It is the only row of which that is true.
Proved by `Examples.Causal.margin_class_not_identifiable_real`.

---

# CONJ-006 — MAIS-O25

Graded against the agenda's `prob:exact`. Status **OPEN**, scope `Same`,
fidelity `Selected`.

### Source, verbatim

```latex
\begin{problem}[\Oid{25}: Query complexity with exact policy probabilities]\label{prob:exact}
Let $\mathcal{N}\subseteq\MM(\sk,\lambda)$ be a compact semialgebraic class
satisfying conclusions (a)--(b) of Problem~\ref{prob:effective} with modulus
$\omega(\delta)=L\delta$. Assume also a richness condition: for some graph $G$
and $\rho>0$, its table-parameter projection contains a $K(G)$-dimensional box
of side $\rho$. Determine, up to constants depending on $(m,K,\lambda,L,\rho)$,
the minimal budget $N(\varepsilon)$ such that the minimax risk over
$\mathcal{N}$ at budget $N(\varepsilon)$, with $\delta=0$ and the
policy-probability oracle, is at most $\varepsilon$. In particular: decide
whether $N(\varepsilon)\le \mathrm{poly}(K,1/\lambda,L,1/\rho)\log(1/\varepsilon)$,
and whether adaptive queries outperform non-adaptive ones by more than a
constant factor.
\end{problem}
```

### Lean, top level

```lean
public noncomputable def maisO25_exactQueryRate : Prop :=
  ∃ A c : ℝ, ∃ d : ℕ, 0 ≤ A ∧ 0 < c ∧
    ∀ (C : Type) [Fintype C] [DecidableEq C] [Nonempty C]
      (sk : Skeleton C (binaryDim C) Bool ℝ)
      (modelClass : Set (Model C (binaryDim C) ℝ)) (lam : ℝ) (K : ℕ)
      (L δmax rho : ℝ),
      maisO25_exactQueryRate_for sk modelClass lam K L δmax rho A c d
```

One level down, because the top level says nothing without it:

```lean
public noncomputable def maisO25_exactQueryRate_for
    (sk : Skeleton C (binaryDim C) Bool ℝ)
    (modelClass : Set (Model C (binaryDim C) ℝ))
    (lam : ℝ) (K : ℕ) (L δmax : ℝ) (rho : ℝ) (A c : ℝ) (d : ℕ) : Prop :=
  ExactClassAssumptions sk modelClass lam K L rho δmax →
    IsPolyLogBudget
      (fun ε ↦ exactMinimalBudget sk modelClass ε)
      K lam L rho A d ∧
    NonadaptiveWithinConstant c
      (fun ε ↦ exactMinimalBudget sk modelClass ε)
      (fun ε ↦ nonadaptiveExactMinimalBudget sk modelClass ε)

@[expose] public noncomputable def ExactClassAssumptions (sk : Skeleton C (binaryDim C) Bool ℝ)
    (modelClass : Set (Model C (binaryDim C) ℝ)) (lam : ℝ) (K : ℕ) (L : ℝ)
    (rho : ℝ) (δmax : ℝ) : Prop :=
  Skeleton.ValidMargin lam ∧ 0 < L ∧
    IsClassChartDim sk lam K ∧
    (∀ M ∈ modelClass, sk.MarginClass M lam) ∧
    IsCompactSemialgebraicClass modelClass ∧
    (∀ M ∈ modelClass, ∀ M' ∈ modelClass, sk.BehaviorEq M M' → M = M') ∧
    HasLinearRecoveryModulus sk modelClass lam L δmax ∧
    ContainsChartBox modelClass rho
```

### Lean read back

There exist a nonnegative real coefficient `A` and a natural degree `d`, **chosen
before anything else**, such that for every finite nonempty type of chance
variables, every skeleton over it with real binary tables, every set of models,
every margin `λ`, every chart dimension `K`, every modulus constant `L`, every
`δmax` and every richness side `ρ`: *if* the class satisfies all eight
conditions — valid margin, positive `L`, `K` is `def:margin`'s chart maximum over
the class, every member is in the margin class at `λ`, the class is compact and
semialgebraic on every graph's chart slice, behavioural equality on the class
implies model equality, the class has a linear recovery modulus `Lδ` up to
`δmax`, and its chart projection contains a `K(G)`-dimensional box of side `ρ` —
*then* two things hold at once: the minimal budget is bounded by
`A·(1 + K + 1/|λ| + |L| + 1/|ρ|)^d · log(1/ε)`, and the non-adaptive minimal budget exceeds
the adaptive one by at most the factor `c`.

`c` is chosen in the same existential as `A` and `d`, **before** the skeleton and
the class, and that placement is the content of the clause rather than a detail
of it: a `c` chosen after the class would permit a different constant for each
class, which is what *"by more than a constant factor"* denies.

`exactMinimalBudget` is the infimum, over **randomized** analyst strategies, of
the supremum over the class of the *expected* error, valued in `ℕ∞` so that `⊤`
refutes a finite bound rather than satisfying one.

### The delta

Print's *"Determine … the minimal budget"* is a determine-problem and no
truth-valued `Prop` is the same statement as it. Print then writes *"In
particular: decide whether …"* twice, and **the Lean states exactly those two
decide-clauses and no more** — a one-sided `poly·log` bound, not a `Θ`, and the
constant-factor adaptivity claim. That is what `Selected` records here.

`A` and `d` are bound **before** the skeleton and the class. Print says the
constants depend on `(m,K,λ,L,ρ)` and writes `poly(K,1/λ,L,1/ρ)` inside the
decide-clause, with no `m` in the polynomial, so the coefficient and degree
cannot be chosen after seeing the instance. The Lean's quantifier order is that
reading.

All eight conditions of `ExactClassAssumptions` map one-to-one onto print's
preamble: `𝒩 ⊆ 𝕄(sk,λ)`, *compact semialgebraic*, conclusions (a)–(b) with
modulus `ω(δ)=Lδ` (the injectivity conjunct together with the linear modulus),
and the richness condition. `Nonempty C` is not an added hypothesis: (M5) asks
`𝐎 ⊊ 𝐂`, which no empty `𝐂` satisfies.

**Non-vacuity.** `ExactClassAssumptions` is inhabited — `oneNode_exactClassAssumptions`
meets all eight clauses over the one-node class with `K = 1`, `L = 10`,
`ρ = 1 − 2λ`, `δmax = 1` — so this `Prop` is not vacuously true.

---

# CONJ-003 — MAIS-O26

Graded against the agenda's `conj:exact`. Status **OPEN**, scope `Same`,
fidelity `Literal`.

### Source, verbatim

```latex
\begin{conjecture}[\Oid{26}]\label{conj:exact}
For $\mathcal{N}=\MM(\sk,\lambda,\mu)$ with $\mu$ fixed,
$N(\varepsilon)=\Theta\bigl(K\log(1/\varepsilon)\bigr)$ as $\varepsilon\to0$,
with the implied constants polynomial in $1/\lambda$, $1/\mu$, and $L$ and
independent of $m$ otherwise: bisection along the segments of
Proposition~\ref{prop:equiv} achieves the information-theoretic floor of
Remark~\ref{rem:packing} up to constants.
\end{conjecture}
```

### Lean, top level

```lean
public noncomputable def maisO26_exactRate : Prop :=
  ∀ sol : O24Solution, ∃ A : ℝ, ∃ d : ℕ, 0 ≤ A ∧
    ∀ (m : ℕ)
      (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ) (K : ℕ)
      (lam mu L δmax : ℝ),
      maisO26_exactRate_for sol sk K lam mu L δmax A d
```

One level down:

```lean
@[expose] public noncomputable def maisO26_exactRate_for {m : ℕ} (sol : O24Solution)
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (K : ℕ) (lam mu L δmax A : ℝ) (d : ℕ) : Prop :=
  O26ClassAssumptions sol sk lam mu K L δmax →
    IsThetaWithMarginBound
      (fun ε ↦ exactMinimalBudget sk (sol.marginClass sk lam mu) ε)
      (fun ε ↦ (K : ℝ) * Real.log (1 / ε))
      lam mu L A d

public noncomputable def O26ClassAssumptions {m : ℕ} (sol : O24Solution)
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (lam mu : ℝ) (K : ℕ) (L δmax : ℝ) : Prop :=
  Skeleton.ValidMargin lam ∧ Skeleton.ValidMargin mu ∧ 0 < L ∧
    IsClassChartDim sk lam K ∧
    HasLinearRecoveryModulus sk (sol.marginClass sk lam mu) lam L δmax
```

### Lean read back

For every solution to MAIS-O24 there exist a nonnegative coefficient `A` and a
degree `d`, chosen after the solution but **before the diagram**, such that for
every `m`, every skeleton over `m+1` binary chance variables with real tables,
every `K`, and every `λ`, `μ`, `L`, `δmax`: *if* `λ` and `μ` are valid margins,
`L` is positive, `K` is `def:margin`'s chart maximum over the margin class, and
the class cut by that solution's polynomial list has a linear recovery modulus
`Lδ` up to `δmax`, *then* the randomized exact-policy-probability minimal budget
is `Θ(K·log(1/ε))` as `ε → 0`, with **both** implied constants bounded by
`A·(1 + 1/λ + 1/μ + L)^d`.

The two-sided constraint is not decoration: `IsThetaWithMarginBound` asks
`c₁⁻¹ ≤ A(1 + 1/λ + 1/μ + L)^d` as well as `c₂ ≤ A(…)^d`, and since `0 < c₁` the
first is a **lower** bound on `c₁`. A degenerate constant cannot satisfy it.

### The delta

**Where print's `𝕄(sk,λ,μ)` went.** Print writes `𝒩 = 𝕄(sk,λ,μ)` and does not
quantify over anything. The Lean's `∀ sol : O24Solution` is not an added
quantifier — it is that class. `𝕄(sk,λ,μ)` is *defined* by `prob:effective`'s
polynomial list, and no such list is exhibited, so the only faithful rendering of
"the class print names" is "the class any solution to O24 cuts". A reader who
takes the `∀ sol` for an atlas-supplied generalization has it backwards.

**Compact semialgebraicity is absent, deliberately.** `prob:exact` prints it;
`conj:exact` does not. Carrying it here would make the row a specialization of
print's sentence, so it was removed on 2026-08-23. It remains on CONJ-006, where
print does state it — deleting it there would widen O25 past its own hypothesis.

**The richness condition and its `ρ` are also absent**, for a stated reason:
`conj:exact`'s constants are polynomial in `1/λ`, `1/μ` and `L` and mention no
`ρ`. The inheritance from `prob:exact` is selective and the printed text is what
selects.

`A` and `d` do not mention `m` or `K`. That is print's *"independent of `m`
otherwise"*: `K(G) = Σᵢ 2^{|Pa(Cᵢ)|}` is itself bounded by a function of `m`, so
letting the constants depend on `K` would smuggle the `m`-dependence back in.

**The printed sentence continues after a colon and the Lean transcribes the half
before it.** *"… independent of `m` otherwise: bisection along the segments of
Proposition `prop:equiv` achieves the information-theoretic floor of Remark
`rem:packing` up to constants."* That clause names a mechanism — `rem:packing`
gives `N = Ω(K(G) log(1/ε))` from a packing-and-Fano argument, and bisection is
asserted to match it from above. Read as a gloss it explains how print expects
the `Θ` to be proved and nothing is lost; read as a conjunct it asserts a
specific algorithm is optimal up to constants, and then the `Prop` is narrower
than print's sentence, since a proof of the rate need not go through bisection.
The atlas takes the gloss reading. **The choice was made silently until
2026-08-23**, when this paragraph and the declaration's own docstring were
written; before that, the verbatim source above quoted a clause that no delta
addressed. Closing it the other way needs bisection as a query strategy and
`rem:packing` as a theorem, neither of which exists in the tree.

**Two live caveats, both disclosed rather than repaired.**

1. *This statement may be vacuously true.* Its antecedent needs an
   `O24Solution` — an answer to `prob:effective` — and none is exhibited
   anywhere in the tree.
2. *Print's literal sentence admits a refutation route.* On an empty cut class
   the risk is a supremum over the empty set, hence `0`, so the minimal budget
   is `0` and the lower half of the `Θ` fails at any `K ≥ 1`. This is now a
   machine-checked conditional theorem,
   `not_maisO26_exactRate_for_of_empty`, not a prose argument. It is a *route*
   and not a refutation: it needs a solution with an empty cut, and no such
   solution is exhibited in this tree.
   The atlas does **not** add a nonemptiness premise to rescue the conjecture;
   the atlas-original variant that did carry one left the ledger on 2026-08-23
   and is recorded in `docs/provenance/retired-conjecture-rows.md`.

---

# CONJ-008 — MAIS-O29 part (a)

Graded against the agenda's `prob:boltzmann`. Status **RESOLVED**, scope `Same`,
fidelity `Selected`.

### Source, verbatim

```latex
\begin{problem}[\Oid{29}: Boltzmann agents: rates and design]\label{prob:boltzmann}
Under the Boltzmann channel with known $\beta$: (a) decide whether the map from
models to Boltzmann behavior is injective on $\MM(\sk,\lambda)$; (b) for each
fixed finite $\beta$, determine the minimax risk at budget $N$ up to constants,
including the deterioration as $\beta\to0$; then characterize the joint
$(N,\beta)$ crossover from the smooth local rate (typically proportional to
$1/(\beta\sqrt N)$) to the noiseless adaptive-search regime as $\beta\to\infty$;
(c) solve the design problem: which distribution over queries
$(\sigma,\bO',w)$ maximizes the minimax rate?
\end{problem}
```

### Lean, top level

```lean
@[expose] public noncomputable def maisO29_boltzmannNotInjective : Prop :=
  ∀ β : ℝ, 0 < β →
    ∃ (m : ℕ) (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ) (lam : ℝ),
      Skeleton.ValidMargin lam ∧
        ∃ M M' : Model (Fin (m + 1)) (binaryDim (Fin (m + 1))) ℝ,
          sk.MarginClass M lam ∧ sk.MarginClass M' lam ∧ M ≠ M' ∧
            BoltzmannBehaviorEq sk β M M'
```

### Lean read back

For every positive real inverse-temperature `β` there exist a chance-variable
count, a skeleton over that many binary variables with real tables, and a valid
margin `λ`, together with two models in the margin class at `λ` that are **not
equal** and whose Boltzmann response distributions agree.

### The delta

Print asks *"(a) decide whether the map … is injective"*; the Lean asserts the
**negative branch**, so `Selected` again, and the negation of injectivity is the
existential pair.

**`β` outside, skeleton inside.** Print says *"Under the Boltzmann channel with
known `β`"* — the analyst knows `β`, so the failure has to hold at each `β`, and
the witness may depend on it. `∀ β, 0 < β → ∃ sk …` is that reading. This is a
deliberate choice recorded in the coverage audit, not an accident of transcription.

**This row is part (a) only.** The `resolution` field opens *"Coverage: this row
is `prob:boltzmann`(a) only"* and says explicitly that neither (b) nor (c)
follows: a negative (a) *constrains* (b), since non-identifiability is what
would floor the risk, but does not determine it, and it bears on (c) not at all.

**Part (b) is not this row, and since 2026-08-23 it is not unproved either.**
`boltzmann_minimax_floor` bounds a *deterministic* estimator, and
`subsec:queries` takes the infimum over *randomized* strategies of the expected
error; deterministic strategies are a subset, so bounding their infimum from
below says nothing about print's. That retraction stands. What changed is that
the bound at print's own quantifier now exists:
`AISafetyAtlas.Conjectures.MAIS.O29Experiment` builds the sampled experiment,
`runBoltzmannTranscript_congr` proves two Boltzmann-indistinguishable models
induce the same transcript law at every budget, and
`half_le_boltzmannMinimaxRisk_collision` floors the **randomized** minimax risk
at `1/2` on the full margin class, uniformly in the budget and in `β`, for two
such models **with different graphs**.

`boltzmannMinimaxRisk_le_one` supplies the other side, so
`boltzmannMinimaxRisk_collision_bounds` determines (b)'s quantity up to a factor
of two **at that skeleton** — no rate, hence no `β → 0` deterioration and no
`(N, β)` crossover. That is (b) at one print-legal instance and not at every one;
on a class where the risk decays none of (b) is touched. This row's status is
unaffected either way and stays part (a): (b) is a determine-clause, and no
truth-valued `Prop` is `Same` as one. Part (c) is definition-blocked.

Proved by `maisO29_boltzmannNotInjective_holds` at every positive `β`, on the
source's real chart.

---

# CONJ-010 — MAIS-O31

**Graded against MAIS issue #8**, not the agenda. Status **OPEN**, scope `Same`,
fidelity `Literal`.

### The setting — agenda `q:chain` (context, *not* the graded artifact)

```latex
\begin{question}[\Oid{31}: The chain]\label{q:chain}
Let $\bC=\{C_1,\dots,C_m\}$ with graph the directed path
$C_m\to C_{m-1}\to\dots\to C_1$, observation set $\bO=\emptyset$, utility parents
$\bZ=\{C_1\}$, and $u$ with margin (M2)--(M3). For $W=\{C_j\}$, a single
intervenable variable: which of the $2(m-1)+1$ table parameters are
$\Sigma_W$-identifiable for almost every $\theta$ (comparison class: the models
of $\MM(\sk,\lambda)$ carrying this chain graph, so that all the parameters are
defined)? (Heuristic, labeled as such: mixtures at $C_j$ should reveal the
composite transfer map from $C_j$ to $C_1$---a product of $2\times2$ stochastic
matrices---and the observational marginal of $C_1$, but not the individual
factors nor anything upstream of $C_j$; I have not proved either the positive or
the negative half, and the negative half needs a genuine indistinguishability
construction.)
\end{question}
```

`q:chain` asks *"which of the `2(m-1)+1` table parameters are identifiable"* — a
characterize-question, which no truth-valued `Prop` is the same statement as.
That is why it sits in `context_source_ref` and the graded artifact is the
issue.

### Source, verbatim — MAIS issue #8, "Claim" section

> Write the downstream transfer from $P(C_j=1)=x$ to $P(C_1=1)$ as $T(x)=A+Bx$,
> let $r=P(C_j=1)$, and let $t\in(0,1)$ be the utility decision threshold.
>
> - If $(A-t)(A+B-t)<0$, behavior identifies $r$. Among the literal CPT
>   coordinates listed in the problem, exactly one is identified when $j=m$: the
>   root probability $P(C_m=1)$. When $j<m$, no literal table coordinate is
>   identified.
> - If $A$ and $A+B$ lie strictly on the same side of $t$, no table coordinate
>   is identified.

And its Scope section:

> This is an almost-everywhere classification: endpoint ties, CPT boundaries, and
> exact margin boundaries are excluded. A named chamber may be empty for some
> fixed margin constraints; the theorem is conditional on its feasibility.

### Lean, top level

```lean
@[expose] public noncomputable def maisO31_chainClassificationCandidate : Prop :=
  ∀ (n : ℕ) (lam t : ℝ) (j : Fin (n + 1)) (M : O31ChainModel n),
    0 < t → t < 1 → M.Valid lam → M.Generic lam →
      (O31StraddlingChamber t j M ∨ O31SameSideChamber t j M) →
      (O31StraddlingChamber t j M → O31IdentifiesNodeMass lam t j M) ∧
        ∀ coordinate : O31Coordinate n,
          O31IdentifiesCoordinate lam t j M coordinate ↔
            O31StraddlingChamber t j M ∧ O31CoordinateCandidate j coordinate
```

The two identification predicates, one level down:

```lean
@[expose] public noncomputable def O31IdentifiesNodeMass {n : ℕ} (lam t : ℝ)
    (j : Fin (n + 1)) (M : O31ChainModel n) : Prop :=
  ∀ M' : O31ChainModel n, M'.Valid lam → O31BehaviorEqAt t j M M' →
    M'.nodeMass j = M.nodeMass j

@[expose] public noncomputable def O31IdentifiesCoordinate {n : ℕ} (lam t : ℝ)
    (j : Fin (n + 1)) (M : O31ChainModel n) (coordinate : O31Coordinate n) : Prop :=
  ∀ M' : O31ChainModel n, M'.Valid lam → O31BehaviorEqAt t j M M' →
    M'.coordinate coordinate = M.coordinate coordinate
```

### Lean read back

For every chain length `n+1`, every margin `λ`, every threshold `t`, every
intervened node `j`, and every chain model `M`: *if* `t` lies strictly in
`(0,1)`, `M` is margin-valid at `λ` (which itself forces `0 < λ < 1/2`), `M` is
generic at `λ`, and `M` lies in either the straddling chamber or the same-side
chamber at `t` and `j`, *then* two things hold:

1. if `M` is in the straddling chamber, then every margin-valid model sharing an
   optimal-policy family with `M` under every real mixture of the local
   interventions at `j` has the **same node mass at `j`**; and
2. for every one of the listed table coordinates, that coordinate is identified
   in the same sense **if and only if** `M` is in the straddling chamber *and*
   the coordinate is the one the issue names — the root probability when `j` is
   the last node, and nothing otherwise.

Identification is behavioural throughout: `O31BehaviorEqAt` is *"shares an
optimal-policy family"*, never *"has the same observed distribution"*. That is
read from the paragraph opening the interventions subsection of the pinned
`.tex`, which defines `Σ_W`-identifiability of `T(M)` by requiring `T` to be
constant on the models sharing an optimal-policy family with `M`. Had the
observer been handed distributions instead, this statement would be about a
strictly narrower observation model than print assumes.

### The delta

**The threshold is free, as the issue writes it.** The issue says only *"let
`t ∈ (0,1)`"*. Deriving `t` from a margin-admissible utility gap instead would
restrict the statement to the sub-interval `[λ/(1+λ), 1/(1+λ)]` that admissible
utilities induce — at `λ = 1/10`, `[1/11, 10/11]`, not `(0,1)` — so the Lean
quantifies over `t` directly. The bounds themselves survive as
`o31Threshold_mem_marginInterval`, now recording which thresholds the surrounding
`q:chain` problem produces rather than restricting this row.

**The exclusions are the issue's own words**, rendered rather than replaced: the
chamber disjunct excludes endpoint ties, and `O31ChainModel.Generic` excludes CPT
boundaries and exact margin boundaries. The issue's *"almost-everywhere"* is not
swapped for a chamber of the atlas's choosing.

**Both bullets are stated, and the first as an implication.** The issue asserts
that straddling implies `r` is identified; it does not assert the converse, and
the Lean does not either. The coordinate clause *is* an `↔`, because the issue
states both directions there.

**Any chain length.** The statement admits `n = 0`. `q:chain` counts
`2(m−1)+1` parameters and rules out no `m`; at `m = 1` that is the single root
probability, and (M4)'s edge condition is vacuous rather than violated.

**Non-vacuity, both branches.** `o31_antecedent_inhabited` meets every hypothesis
at once on a two-node chain at margin `1/10` and lands on the *straddling*
branch, which is the branch the issue's `r` bullet is about;
`o31_sameSide_antecedent_inhabited` lands on the same-side branch.
`o31_not_sameSideChamber_oneNode` records why two nodes are needed: at one node
the intervened node is the guessed endpoint, so the hard interventions pin the
transfer at `0` and `1` and straddle every admissible threshold.

**A separate finding sits beside this row and is not part of it.** The agenda's
*heuristic* parenthetical says mixtures should reveal the observational marginal
of `C₁`. `o31BoxSet_volume` computes an explicit open box's Lebesgue measure as
`1/500`, and `o31_endpointMarginal_not_identified_positiveMeasure` proves failure
at every point of that box in the three-parameter two-node chart: a model and its
mate are both margin-valid,
share the transfer map, share an optimal policy under every real mixture, and
disagree on the marginal of `C₁`. That is consistent with issue #8's same-side
branch rather than in tension with it — the issue classifies literal *table
coordinates*, and the marginal of `C₁` is not one of the `2(m−1)+1` of them.

---

# CONJ-005 — MAIS-O34 part (a), margin subquestion

Graded against the agenda's `prob:starter-set`. Status **RESOLVED**, scope
`Same`, fidelity `Selected`.

### Source, verbatim

```latex
\begin{problem}[\Oid{34}: Starter: the identified set, exactly]\label{prob:starter-set}
For the family $\MM_2(\lambda)$, write
$r_M(\delta):=\sup_{M'\in I_\delta(M)}e(M;G',\theta')$ for the local radius of
the identified set. (a) Determine, as an explicit semialgebraic condition on
$(u,\theta)$, when the global fiber $\{M':\Delta_{M'}=\Delta_M\}$ is the
singleton $\{M\}$; in particular decide whether margin $\lambda>0$ alone
suffices. (b) On the locus where the inverse is locally Lipschitz and the graph
is locally fixed, compute the first-order constant in
$r_M(\delta)=c(u,\theta)\delta+o(\delta)$. On the complementary locus, classify
the alternatives: a positive limiting radius, graph ambiguity, or a
fractional-power modulus. Use this classification to determine the largest
regret below which the edge direction is certain throughout the class.
\end{problem}
```

### Lean, top level

```lean
@[expose] public noncomputable def maisO34_marginAloneDoesNotIdentify : Prop :=
  ∃ (sk : Skeleton (Fin 2) (binaryDim (Fin 2)) Bool ℝ) (lam : ℝ),
    sk.observed = ∅ ∧ sk.utilityParents = Finset.univ ∧
      Skeleton.ValidMargin lam ∧
      ∃ M M' : Model (Fin 2) (binaryDim (Fin 2)) ℝ,
        sk.MarginClass M lam ∧ sk.MarginClass M' lam ∧
          HasGraphEdge M ∧ HasGraphEdge M' ∧
          M ≠ M' ∧ sk.BehaviorEq M M'
```

### Lean read back

There exist a two-variable skeleton with empty observation set and both variables
as utility parents — which is `def:twovar`'s family `𝕄₂(λ)` — and a valid margin
`λ`, together with two models over it, both in the margin class at `λ`, both
carrying a graph edge, which are **not equal** and whose complete masked
behavioural transforms are equal.

### The delta

Part (a) has two halves. *"Determine, as an explicit semialgebraic condition …"*
is a determine-problem; **this row is the second half only**, *"in particular
decide whether margin `λ > 0` alone suffices"*, answered negatively. The
`resolution` field says so verbatim: *"COVERAGE: THIS ROW IS THE
MARGIN-SUFFICIENCY SUBQUESTION OF prob:starter-set(a) ONLY."* The first half is
CONJ-009's, graded against issue #4. Part (b) is covered by neither.

**`HasGraphEdge` on both models is not a narrowing.** It is what makes the
witness answer the question print asks: two edgeless models colliding would not
show that margin fails to pin the *structure*. A same-orientation collision would
answer (a) equally well, which is why the row asks only `M ≠ M'` — an earlier
version asked for differing parent sets and thereby excluded half the legal
witnesses; that narrowing was removed on 2026-08-21.

Proved by `Examples.Causal.margin_class_not_identifiable_two_graphs_real`, with
two models of *opposite* one-edge orientation, on the source's real chart.

---

# CONJ-009 — MAIS-O34 part (a), the singleton criterion

**Graded against MAIS issue #4**, not the agenda. Status **RESOLVED**, scope
`Same`, fidelity `Literal`.

### Source, verbatim — MAIS issue #4, "Result" section

> Let $g=(g_{xy})$ be the known utility-gap table, let
> $d_x=g_{x1}-g_{x0}$, $e_y=g_{1y}-g_{0y}$, and let
> $\Delta_M\in\mathbb{R}^{16}$ be the behavioral transform of a two-variable
> model $M$.
>
> For a forward model $M=(a,b_0,b_1)$, the same-direction fiber is a singleton
> exactly when either $d_0d_1\neq 0$, or exactly one row is flat, say $d_z=0$,
> and the feasible companion set
> $K_\lambda(t)=\{s\in[\lambda,1-\lambda]: |s-t|\ge \lambda\}$
> satisfies $K_\lambda(b_{1-z})=\{b_z\}$.
>
> An opposite-direction model has the same transform exactly when there is one
> flat row, one flat column, and $K_\lambda(a)\neq\varnothing$.
>
> These statements give the complete global-singleton criterion for part (a).

### Lean, top level

```lean
@[expose] public noncomputable def maisO34_exactFiberCandidate : Prop :=
  ∀ (g : Fin 2 → Fin 2 → ℝ) (lam : ℝ) (M : PairModel),
    ValidGap lam g → M.Valid lam →
      (HasSingletonFibre g lam M ↔ O34GlobalSingletonCandidate g lam M)
```

### Lean read back

For every real utility-gap table `g` indexed by the two binary configurations,
every margin `λ`, and every two-variable pair model `M`: *if* `g` is a valid gap
table at `λ` and `M` is margin-valid at `λ`, *then* the global sixteen-coordinate
behavioural fibre of `M` is a singleton **if and only if** the criterion issue #4
states holds of `(g, λ, M)`.

### The delta

This is a **biconditional**, and the issue asserts a biconditional — *"is a
singleton exactly when"*. Both directions are proved, which is what makes the
row `RESOLVED` affirmatively rather than one-directionally. Necessity splits into
a same-direction and an opposite-direction half and both halves are discharged;
the same-direction half rests on `behaviorEq_of_childDifference_eq_zero`,
which shows a vanishing direction difference hides its child coordinate from all
sixteen profiles rather than only from the two that read coordinates.

**The graded artifact is the issue, not the agenda.** `prob:starter-set`(a)'s
first half reads *"Determine … an explicit semialgebraic condition"*, which no
truth-valued `Prop` is the same statement as. Issue #4 supplies a candidate
condition, and grading the row `Same` against *that* is what makes the verdict
falsifiable. The agenda sits in `context_source_ref` as the setting.

**Part (b) is untouched** and the issue is not accepted as a whole — the row
adjudicates the part-(a) criterion and says nothing about the rest of the
submission.

Proved by `Examples.Conjectures.O34.maisO34_exactFiberCandidate_holds`, on the
source's real two-variable chart.

---

# CONJ-025 — MAIS-O38

Graded against **agenda A3**'s `prob:samples`. Status **RESOLVED**,
affirmatively, scope `Same`, fidelity `Selected`. The only row here whose source
is not MAIS-A2, and the only one with no causal content. The construction and
proof are MAIS issue #30's, not the atlas's; the atlas transcribed and
machine-checked them.

### Source, verbatim

```latex
\begin{problem}[\Oid{38}: Polynomially many samples for growing sparsity]\label{prob:samples}
Call a dataset $Y=\{A x_1,\dots,A x_N\}\subset\R^n$, generated by a matrix
$A\in\R^{n\times m}$ and $k$-sparse codes $x_i\in\R^m$, \emph{uniquely coded} if
for every $B\in\R^{n\times m}$ and $k$-sparse $\bar x_1,\dots,\bar x_N$ with
$B\bar x_i=Ax_i$ for all $i$, there are a permutation matrix $P$ and invertible
diagonal matrix $D$ with $B=APD$ and $\bar x_i=D^{-1}P^{-1}x_i$. Let
$k=k(m)\to\infty$ (say $k=\lceil m^{\alpha}\rceil$ for some $\alpha\in(0,1)$, or
even $k=\lceil\log m\rceil$) and $n\ge 2k$. Do there exist $N$ bounded by a
polynomial in $m$ and $k$-sparse $x_1,\dots,x_N$ such that for almost every $A$
satisfying the spark condition of order $k$, the dataset $Y$ is uniquely coded?
(The spark condition---every set of at most $2k$ columns linearly
independent---applies verbatim to matrices with non-unit columns, and
``almost every'' refers to Lebesgue measure on $\R^{n\times m}$.)
\end{problem}
```

### Lean, top level

```lean
@[expose] public noncomputable def maisO38_polynomialSamplesSuffice : Prop :=
  ∀ k n : ℕ → ℕ, Filter.Tendsto k Filter.atTop Filter.atTop →
    (∀ m, 2 * k m ≤ n m) → (∀ᶠ m in Filter.atTop, k m < m) →
      O38PolynomialSampleAnswer k n

@[expose] public noncomputable def O38PolynomialSampleAnswer (k n : ℕ → ℕ) : Prop :=
  ∃ (N : ℕ → ℕ) (p : Polynomial ℕ),
    (∀ m, N m ≤ p.eval m) ∧
      ∀ᶠ m in Filter.atTop,
        ∃ x : Fin (N m) → (Fin m → ℝ), GenericallyUniquelyCoding (k m) (n m) m (N m) x

@[expose] public noncomputable def GenericallyUniquelyCoding (k n m N : ℕ)
    (x : Fin N → (Fin m → ℝ)) : Prop :=
  (∀ i, IsKSparse k (x i)) ∧
    ∀ᵐ A : Fin n → Fin m → ℝ,
      SparkCondition k (Matrix.of A) → UniquelyCoded k (Matrix.of A) x

@[expose] public noncomputable def UniquelyCoded (k : ℕ) {n m N : ℕ}
    (A : Matrix (Fin n) (Fin m) ℝ) (x : Fin N → (Fin m → ℝ)) : Prop :=
  ∀ (B : Matrix (Fin n) (Fin m) ℝ) (x' : Fin N → (Fin m → ℝ)),
    (∀ i, IsKSparse k (x' i)) → (∀ i, B *ᵥ x' i = A *ᵥ x i) →
      ∃ P D : Matrix (Fin m) (Fin m) ℝ,
        IsPermutationMatrix P ∧ IsInvertibleDiagonal D ∧
          B = A * P * D ∧ ∀ i, x' i = (D⁻¹ * P⁻¹) *ᵥ x i
```

### Lean read back

For every pair of functions `k` and `n` from naturals to naturals such that `k`
tends to infinity and `2 * k m ≤ n m` at every `m`, there exist a function `N`
from naturals to naturals and a polynomial `p` with natural coefficients such
that `N m ≤ p.eval m` at every `m`, and such that for all sufficiently large `m`
there exists a family of `N m` vectors in `Fin m → ℝ`, each of whose supports has
at most `k m` elements, with the property that for Lebesgue-almost every function
`A : Fin (n m) → Fin m → ℝ` — Lebesgue meaning the `n m · m`-fold product of the
Lebesgue measure on `ℝ` — if every finite set of at most `2 * k m` column indices
gives a linearly independent family of columns of `A`, then: for every matrix `B`
of the same shape and every family `x'` of `N m` vectors each of whose supports
has at most `k m` elements, if `B` applied to `x' i` equals `A` applied to `x i`
at every `i`, then there exist a matrix `P` that is the permutation matrix of some
permutation of `Fin m` and a matrix `D` that is the diagonal matrix of some
nowhere-vanishing vector, with `B = A * P * D` and `x' i = (D⁻¹ * P⁻¹) *ᵥ x i` at
every `i`.

### The delta

Print asks a yes/no question — *"Do there exist `N` … such that …?"* — and the
Lean asserts the **affirmative branch**. That is what `Selected` records, on the
same genre already graded that way at CONJ-004, CONJ-005 and CONJ-008.

**One quantifier is print's and unwritten, and it is the whole of the delta.**
Print never quantifies `m`: it writes *"Let `k = k(m) → ∞` … and `n ≥ 2k`"* and
*"`N` bounded by a polynomial in `m`"*, both asymptotic, and then poses the
question. The Lean reads the missing quantifier at `Filter.atTop`. Under the
strictest alternative — a design at *every* `m` — the printed sentence is false,
and that is a theorem rather than a worry:
`Examples.Conjectures.MAIS.not_maisO38_everyDimensionReading` refutes
`maisO38_everyDimensionReading` at `m = 1`, where `k 1 = 0` makes every code the
zero vector and the dataset `{0}`, so every `B` reproduces it. Print's own named
family `k = ⌈log m⌉` has `k 1 = 0` as well. On the eventual reading print's own
`k(m) → ∞` excludes the case and no atlas condition on `k` appears anywhere,
which `eventually_one_le_sparsity` is the proof of.

**A second unwritten quantifier, read the same way.** Print says what `k` tends
to and never says what it ranges over. Two of print's own phrases presuppose
`k(m) < m`: *"`k`-sparse codes `xᵢ ∈ ℝᵐ`"* is no condition at all once `m ≤ k`,
and *"the spark condition of order `k`"* is Definition 4.1's condition on a
dictionary in `U_{n,m}`, which §2 places at `m > n`, giving `2k ≤ n < m`
already. The Lean carries the domain as eventually `k m < m`.

What turns on the choice is a theorem, not an argument. The wider reading is
`maisO38_unboundedSparsityReading`, and it is **false**:
`Examples.Conjectures.MAIS.not_maisO38_unboundedSparsityReading` refutes it at
`k(m) = m`, `n(m) = 2m`, where `not_uniquelyCoded_of_full_sparsity_spark` kills
every design at every spark-condition matrix and `ae_sparkCondition` closes the
vacuous escape. That refutation has no sparse-coding content — a transvection is
the whole argument — and by `rows_gt_cols_of_full_sparsity_spark` print's own
`n ≥ 2k` forces the witness into `m < n`, an undercomplete dictionary on the
wrong side of the agenda's own regime. **It is a warning about the printed
sentence, not an answer**, and `exists_admissibleGrowthLaw` checks the narrowed
universal is not empty. (This sentence read *"the row stays `OPEN`"* until
2026-08-30. The refutation still answers nothing; what changed is that the row was
resolved the same day by a different argument — the candidate in MAIS
[issue #30](https://github.com/lionellevine/MAIS/issues/30), transcribed and
proved — so the clause was true about the refutation and false
about the row.) MAIS
[issue #30](https://github.com/lionellevine/MAIS/issues/30) reads the domain as
`1 ≤ k < m` independently.

**The set braces are print's and the pairing is print's too.** `Y` is written
`{A x₁, …, A x_N}`, and *uniquely coded* is then stated index by index —
`B x̄ᵢ = A xᵢ` for all `i`, `x̄ᵢ = D⁻¹P⁻¹xᵢ` at the matching index. `UniquelyCoded`
takes an indexed family, because a `Set` drops that pairing.

**Non-vacuity is discharged**, which for an existential row is the obligation that
matters: `Examples.Conjectures.MAIS.genericallyUniquelyCoding_two` exhibits two
one-sparse coordinate probes meeting print's demand at `m = 2`, `k = 1`, for every
ambient `n`, and pointwise rather than almost everywhere.

**No candidate is graded here.** Unlike CONJ-009 and CONJ-010, whose graded
artifact is a submitted issue, this row grades against the agenda. MAIS issue #30
submits a candidate solution; it is `context_source_ref`, its construction is not
transcribed, and its only influence is recorded in
[`mais-o38-transcription.md`](mais-o38-transcription.md).

---

# Notes on reading this document

**Where a `Same` grade can still be wrong.** Every verdict above rests on one
step no proof assistant checks: someone read the PDF or the issue and wrote the
Lean. That transcription is irreducibly human. Everything downstream of it is
mechanical, and in one place the atlas closes even the transcription gap by
proof — `Skeleton.marginClass_iff_printed` proves the categorical margin class
equals the printed binary one, with `PrintedM1`, `PrintedM4` and `PrintedM5`
transcribed separately. That pattern is not yet extended to the O25/O26
assumption bundles, so those two rows' agreement with print is an argument where
the margin class's is a theorem.

**What `Same` does and does not assert.** It says the Lean `Prop` is at the
printed statement's own quantifier. It does not say the `Prop` is true, that its
antecedent can be satisfied, or that the printed problem is settled. Those are
three separate columns and CONJ-003 currently fails the second.

**Two MAIS-related rows left the live ledger** and are recorded verbatim with
their reason in [`retired-conjecture-rows.md`](retired-conjecture-rows.md):
CONJ-007 (the defective MAIS-O27 encoding — O27 is a determine-problem, so no
`Prop` can ever be `Same` as it and a row needs a candidate submitted to MAIS
first), and CONJ-011 (the atlas-original well-posed MAIS-O26 variant). CONJ-007's
declaration still compiles with its recorded type.
CONJ-011's names still compile, but removing compact semialgebraicity from the
shared O26 assumptions changed the surviving atlas-original proposition after
the row was archived; the archive now says so explicitly.

**MAIS-O24 has no *conjecture* row for the same reason** — it has a target row,
CONJ-012, since 2026-08-24, and this was the first place the distinction was
written down.** `prob:effective` reads *"exhibit a finite explicit list … Find
constants `a, b > 0` …"* end to end and contains no *decide whether* clause —
unlike `prob:exact`, `prob:boltzmann`(a), `prob:starter-set`(a) and
`prob:floor`(a), each of which carries one and each of which has a row. A
`Prop` asserting that a solution *exists* is not the same statement as a demand
to exhibit one, so grading it `Same` against `mais-a2-2026` would be false, and
`scripts/validate_conjectures.py` requires every MAIS row to be `Same`. The
target is nonetheless fully encoded: `Causal.O24Solution` bundles all three
conclusions with the size and construction-time clauses, and
`docs/provenance/mais-o24-statability.md` records it clause by clause. The route
that could produce a row is the one CONJ-009 and CONJ-010 already take — grade
against a submitted candidate rather than against the agenda — and MAIS issue #7
is such a candidate, claiming conclusions (a) and (c) cannot both hold. Opening
that route needs a `registry.yaml` source entry, and the candidate's own
argument is unverified here past its collision step, so it is a proposal and not
a pending edit.

This file is tracked rather than local because a side-by-side a MAIS reviewer
cannot open settles nothing. Tracking makes its claims permalinkable and its
staleness visible: the provenance block above names the tree its Lean was read
from, and a later change to a transcribed statement falsifies this file rather
than quietly diverging from it.
