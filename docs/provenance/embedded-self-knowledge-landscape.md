# Embedded self-knowledge — landscape sweep

What already exists, machine-checked or not, around the question *which
properties of an embedded system can be known from inside it*. The purpose is to
fix the **novelty boundary** before more atlas mathematics is written against it,
and to record negative searches so a later contributor does not repeat them
blind.

Swept on 2026-08-11. Kernel this bounds:
[`LAND-KNOW-001`](../../registry.yaml),
[`LAND-SELFMEAS-001`](../../registry.yaml), and the source-faithful abstract
core [`LAND-SELFMEAS-002`](../../registry.yaml).

## Outcomes

| Candidate | Machine proof found | Atlas outcome |
|---|---|---|
| Lawvere fixed point (types) | **Yes — Mathlib**, already a dependency | `CLM-LAWVERE-001`, `WRAPPER` |
| Lawvere fixed point (categorical) | **Yes — Isabelle/AFP `Category_Set`** (ETCS, not arbitrary CCC); no usable Lean one | `CLM-LAWVERE-CCC-001`, source claim + candidate lead |
| Chandy–Lamport snapshot | **Yes — Isabelle/AFP**, BSD | `LAND-CL-001`, **reproduced** |
| Breuer 1995 self-measurement | **Yes — Lean abstract core** | `LAND-SELFMEAS-002`, **EQUIVALENT** to §3.5; see [note](self-measurement-kernel.md) |
| Wolpert 2008 physical limits of inference | No | `BY-024` stays unformalized |
| Brandenburger–Keisler 2006 | No | catalogued |
| Abramsky–Zvesper 2010 | No | catalogued |

**Search policy.** Lean first — and against the *local* `.lake/packages` tree,
not against a citation. Then other proof assistants. Only then the literature.
Throughout: an unsuccessful search is not proof that no formalization exists.

**And every absence claim carries a machine-readable record**, as
`novelty_check_obligation` requires. The absence claims here are `NC-002` …
`NC-005` in [`formalization-search.json`](formalization-search.json), each naming
the corpora actually grepped at their pinned revisions, and each stating plainly
which corpora were **not** searched. Prose alone does not discharge the
obligation; see
[why in the methodology](../guide/methodology.md#formal-library-discovery-evidence).

## Lawvere — already in the dependency tree

The decisive finding of the sweep. `Mathlib.Logic.Function.Basic` carries

```lean
theorem exists_fixed_point_of_surjective {α β : Type*} (f : α → α → β)
    (hf : Surjective f) (g : β → β) : ∃ x, g x = x
```

whose own docstring names it as Lawvere's fixed-point theorem for types and
functions, alongside `cantor_surjective` and `cantor_injective`. Mathlib is
pinned at `db584cd6d46c` and is already a dependency, so no external repository,
vendoring, or reproduction is involved. This is `CLM-LAWVERE-001`.

The third-party Lean 4 repository `mdnestor/LawvereFixedPoint` was inspected and
**rejected**. It does contain the genuinely more general statement — over any
`[Category C] [HasFiniteProducts C] [CartesianClosed C]`, with
`weak_point_surjective` and the contrapositive `lawvere_diagonal` — but it
carries **no license file**, which the registry already treats as disqualifying
regardless of proof quality (see the `BY-021` notes for the same rejection).
Last push 2024-09-21.

That generality is not cosmetic, and this is worth recording because it bounds a
tempting claim. In `Type`, points are elements, so the Mathlib instance yields
Cantor and Russell but **not** Gödel, Turing, Rice or Brandenburger–Keisler:
there is no surjection `ℕ → (ℕ → Bool)` in `Type`. Deriving those as instances of
one diagonal kernel needs a category whose points are computable or whose objects
model belief structures — realizability categories, or the regular categories
Abramsky–Zvesper use. Nothing in Lean supplies that today.

### A categorical version exists, in the AFP (NC-005)

Not in Lean, and not in the full generality — but it exists, and any claim that
no categorical Lawvere formalization is available is false.

AFP entry **`Category_Set`** — *The Elementary Theory of the Category of Sets* —
carries `Fixed_Points.thy` with

```isabelle
lemma Lawveres_fixed_point_theorem:
  assumes p_type: "p : X → A\<^bsup>X\<^esup>"
  assumes p_surj: "surjective p"
  shows "fixed_point_property A"
```

over ETCS `cfunc`/`cset` with exponential objects, following Halvorson Theorem
2.6.13, and derives Cantor from it. Maintained, licensed, pinned at the same AFP
release the atlas already uses.

Two qualifications keep the row a source claim rather than coverage. ETCS is
**one axiomatized category of sets**, not an arbitrary cartesian closed category,
so the fully general statement is still unformalized. And it is Isabelle/HOL, so
the sentence above — Lean supplies no categorical version — stands. The
obstruction is generality and language, not availability.

Reproduction is feasible today via
`scripts/reproduce_isabelle.sh` against the same pinned release. It has not been
attempted, so this is a **candidate lead, not coverage**.

**Consequence.** The atlas keeps its existing Gödel (`Foundation`), Tarski, Löb
and Rice (`Mathlib.Computability.Halting`) proofs. Their relation to
`CLM-LAWVERE-001` is mechanism-level only and is recorded as such. Any claim that
the atlas "derives the diagonal family from one kernel" would be false.

Two further Lean 4 claims surfaced in web search — a "Reflexive Reality" master
fixed-point theorem and a ResearchGate "Generative Stack" — and were **not**
catalogued: unreproduced, non-institutional preprints. Recorded here as leads not
taken, with the date, rather than silently dropped.

## Wolpert — BY-024 stays unformalized

`BY-024` (*Physical limits on inference*, Wolpert 2008, `survey-ref-005`) is
`PROVEN` in the survey and carries no formalization. It is the most general
statement in this cluster — inference devices covering observation, prediction
and recollection, with impossibility results independent of the physical laws,
including for devices exceeding Turing machines.

**The row already carries a complete corpus-level negative search**, dated
2026-07-28, over mathlib, isabelle-afp, rocq-undecidability, hol4, hol-light and
agda-stdlib, with the query terms *physical limits of inference*, *inference
device*, *inference devices*, *computational capabilities of physical systems*
and *wolpert*, and an empty `candidate_corpora`. Nothing about it needed
changing, and this sweep changed nothing.

What this sweep adds is only a web-level re-confirmation on 2026-08-11: no
proof-assistant formalization of the inference-device results surfaced. That is
weaker evidence than the corpus-level record and does not supersede it, so it is
recorded here rather than by editing the row's `searched_on` date. Re-running the
corpus-level search would require
[`update_formalization_search.py`](../../scripts/update_formalization_search.py)
against pinned local corpus checkouts, which were not available in this session.

## Brandenburger–Keisler and Abramsky–Zvesper

`brandenburger-keisler-2006` and `abramsky-zvesper-2010-lawvere-bk` are
catalogued as `work` sources. Neither has a proof-assistant formalization as of
2026-08-11; what exists for the second is a mathematical reduction, not a
machine-checked artifact.

They are catalogued rather than pursued because both sit on the categorical side
of the Lawvere boundary described above: formalizing either would require the
regular-category machinery the atlas does not have and has no consumer for.

## Chandy–Lamport — the escape boundary

Catalogued as `chandy-lamport-1985`. It is a **possibility** result and it is in
the sweep for a specific reason: it constrains how any self-knowledge
impossibility may be worded. A process can determine a consistent global state
while the computation continues. So the honest obstruction concerns *exact
knowledge of the present state*, never "a system cannot know its own global
state" — a claim distributed snapshots simply falsify at useful engineering
resolutions. Snapshots escape by relaxing contemporaneity.

Machine-checked in Isabelle/HOL: AFP entry `Chandy_Lamport`, Ben Fiedler and
Dmitriy Traytel, July 2020, **BSD License**, latest release 2026-02-06 for
Isabelle2025-2 — the same AFP release the atlas already pins for
`Recursion-Theory-I` and `ArrowImpossibilityGS`.

The single-entry archive does **not** close: the `Chandy_Lamport` session's
parent is `Ordered_Resolution_Prover`, which itself requires `Coinductive` and
`Nested_Multisets_Ordinals`. Reproduction therefore goes through the full
immutable AFP release, the pattern already used for `Deep_Learning`, via
[`scripts/reproduce_isabelle.sh chandy-lamport`](../../scripts/reproduce_isabelle.sh).
The full-release sha256 `b059edd4…` was computed independently in this session
and matches the pin already recorded in-tree for `Deep_Learning`.

### Reproduction (2026-08-11)

| Field | Value |
|-------|-------|
| Entry | `Chandy_Lamport` — Ben Fiedler, Dmitriy Traytel, AFP, July 2020 |
| Release | AFP 2026-02-06, full archive, SHA256 `b059edd46073479ee8dde45004c2346a7365e5d94cded49d27257cfea66c8879` |
| Toolchain | Isabelle2025-2, `makarius/isabelle@sha256:9bd33b18…` |
| Result | `Finished Chandy_Lamport`, exit 0, 7 theories, no errors, 1:54 elapsed |
| Theorems | `snapshot_algorithm_must_terminate`, `snapshot_algorithm_is_correct`, `Stable_Property_Detection` (`Snapshot.thy`) |
| Record | [`LAND-CL-001`](../../registry.yaml) |

Path A — built at the upstream Isabelle, **not** vendored. There is no atlas Lean
import surface for it and no atlas declaration depends on it. It never counts
toward headline `EXACT`/`EQUIVALENT` coverage.

## Where the novelty actually is

Both mechanism trunks are already provisioned:

- **Diagonal.** Lawvere in Mathlib; Gödel I/II, Tarski, Löb in `Foundation`;
  Rice in Mathlib. Zero new dependencies.
- **Indistinguishability.** The factorization kernel is in-tree as
  `LAND-KNOW-001`, and coalition-indexed as `LAND-JOINTOBS-001`.

So the ground the sweep leaves open is neither trunk. It is the two axes the
factorization kernel does not supply on its own: **self-reference** — an
observation map that is a projection of a state containing the observer — and
**time**: indexed observations, and the contemporaneity qualifier Chandy–Lamport
forces. Breuer and Wolpert demonstrably occupy the static and the
inference-level cases; neither occupies the dynamic, property-specific one.

## What the atlas holds on that ground

- `LAND-SELFMEAS-001` — the whole-state target, with non-injectivity assumed
  rather than derived. The smallest step onto the self-reference axis, and
  ungraded: it states no source claim.
- `LAND-SELFMEAS-002` — the source-faithful abstract inference-map and meshing
  layer, `RELATED` to Breuer. It proves the paper's abstract Propositions 1–2 by
  two independent routes, the derived one and Breuer's own, and deliberately
  stops before physical, quantum, dynamical and EPR formalization.
- `LAND-SELFMEAS-003` — product-complement and finite-cardinality bridges that
  *derive* proper inclusion instead of assuming it, together with the bijective
  positive boundary. Atlas physical modelling, graded separately from the paper
  core.
- `LAND-SELFREF-001` — the self-reference axis proper: the observer's model is a
  component of the state it models, and complete self-knowledge holds **iff**
  nothing else is in the state.
- `LAND-TEMPORAL-001` — the time axis, as indexing only. Knowing the target as of
  `s` from evidence at `t`, kept apart from knowing it at `t`. Prior art is
  Mathlib's filtration theory, recorded as `NC-007`; no novelty is claimed for
  time indexing as such, and the reasons to have the layer are that it needs no
  measurable structure and that its evidence types differ across time.
- `LAND-AMBIG-001` / `LAND-ACCUM-001` — the counting form, and its extension to a
  window of targets: ambiguity never decreases as the window widens and never
  exceeds the product of the steps.

## What stays unoccupied

**Dynamics.** Every layer above indexes or projects; none carries a transition
relation. So nothing here says *why* a collision arises, or how a target moves
between observations. A genuine causal-innovation condition — the target changed
between the last evidence-generating event and now — is stateable only once
dynamics exist, and it is what would have to **imply** the collisions these
modules take as given; it is not what any of them says.

The achievability half of the frontier therefore stays with `LAND-CL-001`, a
reproduced external Isabelle record with its model delta stated, until a shared
transition-system-with-observations interface exists for an impossibility and a
construction to instantiate together.
