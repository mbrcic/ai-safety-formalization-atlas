# Limited self-awareness: source map and formal interpretation

This note pins the source statement before mechanization and separates the
published argument from the additional structure needed to make its informal
process language precise.

## Source

| Field | Value |
|---|---|
| Work | M. Brcic and R. V. Yampolskiy, “Impossibility Results in AI: A Survey” |
| Published version | *ACM Computing Surveys* 56(1), 2023 |
| DOI | <https://doi.org/10.1145/3603371> |
| Relevant section | §4.3, *Limited Self-awareness* |
| Source declarations | Definition 4.6, Proposition 4.7, Theorem 4.8 |
| Registry source key | `brcic-yampolskiy-2023-own-results` |
| Audit date | 2026-08-12 |

The published definition calls an agent aware of a phenomenon when it observes
and predictively models it. Awareness of an internal process is self-awareness.
The accompanying prose distinguishes merely producing a process's outputs from
attending to and modelling that process "in an ontology that is richer than just
the final results and where the model is simpler than the process itself."

The model-simplicity half of that sentence is **not formalized**. `Model.aware`
is an abstract relation, and no field compares the size, cost, or description
length of a model against its target. Nothing in either proof needs the
comparison, so its absence does not weaken them; recording it here keeps the
residual visible. Two consequences follow for anything built on this module.
Awareness in the source is a *lossy* model of a process, so a reading that
decorates an awareness edge with a lossless or exhaustive representation of the
target has left Definition 4.6 rather than interpreted it. And exactness on a
selected abstraction or question family is compatible with the clause, while
exactness about the whole process is not.

The six listed assumptions are:

1. bounded computational resources;
2. positive cost for every process;
3. a positive lower bound on process cost;
4. positive information-propagation duration;
5. bounded lag between a process and awareness of it;
6. faithful representation of process-awareness relations by a directed graph.

Proposition 4.7 rules out process self-awareness by an awareness-of-awareness
regress. Theorem 4.8 chooses a finite weakly connected awareness component,
treats its joint activity as a new composite process, and applies Proposition
4.7. The paper then asks whether ordinary awareness graphs may contain cycles;
acyclicity is therefore not an assumption of the result.

The two source statements are short and exact:

> **Proposition 4.7.** “The process cannot be aware of itself.”

> **Theorem 4.8.** “In every agent A, under the assumptions above, there are
> internal processes A is unaware of.”

## Formal vocabulary

The Lean model is fixed to one bounded awareness horizon. Persistent software
components may recur, but its `Process` values represent the process/composite
instances relevant to that horizon.

| Source phrase | Lean interpretation |
|---|---|
| process | an element of `Process` |
| one process is part of another | the semilattice order `q ≤ p` |
| joint/composite process | `p ⊔ q` |
| processes available during the horizon | `Model.available` |
| awareness edge from `q` to `p` | `Model.aware q p` |
| finite-resource consequence | `Model.available_finite` |
| nonzero lower-bounded awareness work | `minAwarenessCost > 0` and `awareness_cost` |
| agent awareness of `p` | some available `q` satisfies `Aware q p` |
| perfect self-awareness | every available process has such an observer |

The central formal commitment is **strict awareness extension**:

```text
aware q p  ⇒  cost p + minAwarenessCost ≤ cost (p ⊔ q).
```

It formalizes the source's distinction between executing a process and
performing the additional observation and predictive modelling of that process.
In particular, if `q ≤ p`, then `p ⊔ q = p`; the displayed inequality and
the positive lower bound are inconsistent. Thus no constituent process can
provide complete horizon-relative awareness of the composite containing that
very awareness activity. Proposition 4.7 is the special case `q = p`.

This commitment is not an additional physical assumption. It makes explicit the
non-cancellation/additivity already used by the published regress: awareness is
active observation and predictive modelling, is distinguished from merely
executing the target process, and is itself positive-cost computation within the
bounded lag. Consequently adding that awareness activity cannot be identified
with the unchanged process it observes. During statement-level review on
2026-08-12, the paper's first author confirmed that this is intended semantic
content of Definition 4.6 together with assumptions 2--5. The Lean field exposes
what the source leaves loaded into those words, so fixed-point or cached static
self-description readings are visibly outside the theorem.

Positive propagation duration and bounded lag are represented semantically by
the fixed-horizon `aware` relation: an edge records observation and predictive
modelling completed within the allowed lag. They are not given a separate clock
type in the first artifact. Consequently the artifact does not derive the
strict-extension law from a physical timing theory.

Likewise, `available_finite` records the fixed-horizon consequence the source
draws from assumptions 1--3. A scalar budget and a pointwise positive process
cost do not by themselves prove finiteness in Lean without an additional
accounting rule saying how the costs of jointly active process instances consume
that budget. The first artifact keeps that physical/resource accounting outside
the theorem instead of silently inventing it. It also needs a positive lower
bound only for awareness work; positive costs for unrelated processes would not
strengthen either proof.

## Proposition 4.7

Formal target:

```text
¬ M.aware p p
```

More generally, if `q ≤ p`, then `¬ M.aware q p`. The proof rewrites the
composite `p ⊔ q` to `p`; strict awareness extension would then require
`cost p + minAwarenessCost ≤ cost p`, contradicting positivity. This is the
finite resource form of the source's vertical awareness-of-awareness regress.

## Theorem 4.8

Formal target:

```text
∃ p ∈ M.available, ∀ q ∈ M.available, ¬ M.aware q p
```

Choose a maximal available composite `p`. If an available `q` were aware of
`p`, `awareness_closed` makes `p ⊔ q` another available composite. Maximality
forces `p ⊔ q ≤ p`, hence `q ≤ p`; the generalized Proposition 4.7
then gives a contradiction.

The Lean surface exposes the stronger reusable intermediate result: **every**
maximal available composite lacks an available complete observer. Theorem 4.8
is its existential corollary, obtained from finiteness and nonemptiness. This
does not assert that there are multiple maximal composites; an agent may have a
unique maximum.

This is the published component argument with its two implicit bridges exposed:

1. an awareness relation makes observer and target a legitimate composite;
2. awareness performed by a constituent of a composite would be composite
   self-awareness.

No acyclicity hypothesis appears. Reciprocal awareness among incomparable
processes is consistent with the model; their composite is the larger target
to which the theorem applies.

## Fidelity decision

Relationship: **`EQUIVALENT`**, after first-author statement-level review on
2026-08-12. The Lean statement preserves the intended assumptions, obstruction,
and conclusion while changing their representation:

- strict additive awareness cost explicitly unpacks the active, distinct,
  positive-cost observation-and-modelling semantics implicit in Definition 4.6
  and assumptions 2--5;
- positive propagation and bounded lag are absorbed into the horizon-relative
  awareness relation rather than modelled numerically;
- the source's weakly connected component and hierarchical supernode step are
  represented by semilattice composition plus closure under witnessed
  awareness.

`EQUIVALENT` rather than `EXACT` records those representational changes. The
proof is not a DAG repair and does not prohibit cycles.

## Deliberate omissions

- The subsequent consciousness hypothesis is not part of either result and is
  not formalized.
- Definition 4.6's model-simplicity clause is unformalized; see *Source* above
  for what that leaves open and for the readings it rules out.
- The paper's suggestions concerning Lawvere-style propagation along awareness
  chains are an open direction, not a premise. The published question asks
  whether *weak* point surjectivity propagates along awareness chains; the
  relational machinery it points at (Abramsky–Zvesper, Lemmas 5–6) turns on the
  weaker *very weak* variant, so an answer must fix which one it establishes.
- No claim is made about approximate, selected-property, cached, or delayed
  self-models. The result concerns the recursively complete horizon-relative
  notion encoded by `aware` and strict awareness extension.
- No Landauer, thermodynamic, or quantum lower bound is formalized. The positive
  minimum cost is an operational hypothesis.
