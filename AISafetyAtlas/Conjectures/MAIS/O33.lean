module

public import AISafetyAtlas.Causal.Corruption
public import Mathlib.Order.CompleteLattice.Basic

/-!
# MAIS-O33 — persistent corruption

`prob:corruption`, stated at the MAIS revision pinned in
`docs/provenance/mais-source-pin.md`. Defining a proposition asserts nothing
about its truth; the resolution lives in
`AISafetyAtlas/Examples/Conjectures/MAIS/O33.lean`.

Print asks two things and this module states both: *"Determine
`η* := sup{η : η uniformly tolerable}`. Is `η* > 0`?"*

`AISafetyAtlas.Causal.Corruption` carries the vocabulary: print's first-action
data, `η`-corruption counted against `𝐒 × 𝚿_n`, and the adaptive randomized
query protocol under a budget. This module adds the two quantifiers that make
tolerability *uniform* — one algorithm and one polynomial, across every
instance — and the supremum print asks to determine.

Two readings are recorded rather than assumed, both in
`AISafetyAtlas.Causal.Corruption`'s module note: the corruption is carried as a
total map (invisible to the protocol, which queries only `𝐒 × 𝚿_n`), and print's
`max_{π'}` is read as `⨆`, which selects a sub-collection of `A(E,n,δ)` and so
makes a refutation over it the stronger result.

## What *"a single randomized algorithm"* means here

`UniformAnalyst` carries the quantifier order print's word fixes: the strategy,
the estimator and the polynomial are chosen **before** the instance, so nothing
is selected per instance. It withholds nothing from them either — print's
instance is `(𝐒, 𝐀, n, δ)` and all four reach the strategy and the estimator;
only the query bound is `δ`-free, matching print's `p(|𝐒|,|𝐀|,n)`. It does not carry computability — its fields are Lean
functions — so `UniformlyTolerable` quantifies over a class at least as wide as
print's, and a widening is a scope defect unless it is closed. It is closed here
by `UniformlyTolerableWithin`, which restricts the analyst by an arbitrary
predicate and is refuted for every such predicate in
`AISafetyAtlas/Examples/Conjectures/MAIS/O33.lean`.

## Why the instance quantifier is over types

Print's instance is `(𝐒, 𝐀, n, δ)` with `𝐒` and `𝐀` finite. `UniformlyTolerable`
quantifies over `Type` with `Fintype`, `DecidableEq`, `MeasurableSpace` and
`MeasurableSingletonClass` instances. The last two are the probability layer's
plumbing and not print's, and they do not narrow the quantifier: on a finite
type, `MeasurableSingletonClass` forces the σ-algebra to be the full power set,
so each finite `𝐒` contributes exactly one instance here as it does in print,
and `Fintype` and `DecidableEq` instances are subsingletons for the same reason.
The quantifier is over `Type` rather than every universe, which restricts it to
a family every finite set is equivalent to and can only make the negative answer
stronger.

## The `0 ≤ η` clause in `etaStar`

`prob:corruption` writes `sup{η : η uniformly tolerable}` for a *corruption
fraction*. Without a sign clause every negative `η` joins the set vacuously — no
map differs from another on a negative number of arguments — and the supremum
would be `0` for a reason having nothing to do with corruption. The clause is
print's intent, not print's letter, and it is the one place this module supplies
a word the source does not.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal

/-- The data print calls *"a single randomized algorithm and a polynomial `p`"*:
one query strategy and one estimator, chosen **before** the instance and applied
at every one of them, and a polynomial carried as a pair `(coeff, deg)` giving
the bound `coeff·(|𝐒| + |𝐀| + n + 1)^deg`. Every polynomial in the three
parameters is dominated by one of that shape, and print asks only for an upper
bound on the number of queries.

**The instance is `(𝐒, 𝐀, n, δ)`, and the analyst reads all four.** Print names
`δ` as part of the instance, so a single algorithm may use it; only the *query
bound* is `δ`-free, which is print's `p(|𝐒|,|𝐀|,n)` and is why `coeff` and `deg`
do not see `δ`. Withholding `δ` from the strategy would narrow the analyst class
and the refutation would not transfer. -/
public structure UniformAnalyst where
  /-- The query strategy, one at every instance `(𝐒, 𝐀, n, δ)`. -/
  strategy : ∀ (S A : Type) [Fintype S] [DecidableEq S] [MeasurableSpace S]
      [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] (n : ℕ) (_δ : ℝ),
      FirstActionStrategy S A n
  /-- The estimator, one at every instance `(𝐒, 𝐀, n, δ)`. -/
  estimator : ∀ (S A : Type) [Fintype S] [DecidableEq S] [MeasurableSpace S]
      [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] (n : ℕ) (_δ : ℝ),
      FirstActionEstimator S A n
  /-- The polynomial's coefficient. Print's `p` takes `|𝐒|`, `|𝐀|` and `n`, not
  `δ`. -/
  coeff : ℕ
  /-- The polynomial's degree. -/
  deg : ℕ

/-- **What print asks the analyst to do**: *"use at most `p(|𝐒|,|𝐀|,n)` queries
and achieve … for every such instance, every communicating environment `E`,
every `π ∈ A(E,n,δ)`, and every `η`-corruption"*. -/
@[expose] public def UniformAnalyst.Meets (a : UniformAnalyst) (η : ℝ) : Prop :=
  ∀ (S A : Type) [Fintype S] [DecidableEq S] [MeasurableSpace S]
      [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] (n : ℕ) (δ : ℝ),
    2 ≤ Fintype.card A → 1 < n → 0 ≤ δ → δ < 1 → 4 < ((n : ℝ) - 1) * (1 - δ) →
    ∀ E : ControlledMarkovProcess S A, E.Communicating →
      ∀ π : FullAgent S A, IsDeltaBoundedFull E π n δ →
        ∀ ρ : FirstActionData S A, IsCorruption n η (firstActionMapFull π) ρ →
          Succeeds E δ (a.strategy S A n δ) (a.estimator S A n δ)
            (a.coeff * (Fintype.card S + Fintype.card A + n + 1) ^ a.deg) ρ

/-- **Print's uniform tolerability.** -/
@[expose] public def UniformlyTolerable (η : ℝ) : Prop :=
  ∃ a : UniformAnalyst, a.Meets η

/-- **Tolerability under any further restriction on the algorithm.**

Print says *"a single randomized algorithm"*. `UniformAnalyst` carries the
quantifier order that word fixes — the strategy, the estimator and the
polynomial are chosen before the instance, so no adversary picks them per
instance — but it is a Lean function, and a Lean function is not a computable
one. `UniformlyTolerable` therefore quantifies over a class **at least as wide**
as print's, and a widening is a scope defect unless it is closed.

It is closed here rather than confessed: `C` is an arbitrary predicate on
analysts, so it may be *"the strategy is computable"*, *"the analyst has a
finite description"*, or any other reading of the word, and
`not_uniformlyTolerableWithin` in
`AISafetyAtlas/Examples/Conjectures/MAIS/O33.lean` refutes every one of them at
once. The reason is structural: the witness defeats **every** strategy at a
single instance, so restricting the class cannot rescue it. -/
@[expose] public def UniformlyTolerableWithin (C : UniformAnalyst → Prop) (η : ℝ) : Prop :=
  ∃ a : UniformAnalyst, C a ∧ a.Meets η

/-- A restricted analyst is an analyst, so the wide statement dominates every
reading of *"algorithm"*. -/
public theorem uniformlyTolerable_of_within {C : UniformAnalyst → Prop} {η : ℝ}
    (h : UniformlyTolerableWithin C η) : UniformlyTolerable η :=
  ⟨h.choose, h.choose_spec.2⟩

/-- Print's single algorithm supplies one at every admissible instance, which is
the form a refutation consumes: one instance where nothing works is enough. -/
public theorem tolerantAt_of_uniformlyTolerable {η : ℝ} (h : UniformlyTolerable η)
    (S A : Type) [Fintype S] [DecidableEq S] [MeasurableSpace S]
    [MeasurableSingletonClass S] [Fintype A] [DecidableEq A] (n : ℕ) (δ : ℝ)
    (hA : 2 ≤ Fintype.card A) (hn : 1 < n) (hδ0 : 0 ≤ δ) (hδ1 : δ < 1)
    (hadm : 4 < ((n : ℝ) - 1) * (1 - δ)) :
    TolerantAt S A n δ η := by
  obtain ⟨a, hsucc⟩ := h
  exact ⟨a.strategy S A n δ, a.estimator S A n δ,
    a.coeff * (Fintype.card S + Fintype.card A + n + 1) ^ a.deg,
    fun E hE π hπ ρ hρ ↦ hsucc S A n δ hA hn hδ0 hδ1 hadm E hE π hπ ρ hρ⟩

/-- **`η*`**, print's supremum of the uniformly tolerable corruption fractions.

The `0 ≤ η` clause is print's intent rather than print's letter: `prob:corruption`
writes `sup{η : η uniformly tolerable}` for a *corruption fraction*, and without
the clause every negative `η` joins the set vacuously — no map differs from
another on a negative number of arguments — which would fix the supremum at `0`
for a reason that has nothing to do with corruption. -/
@[expose] public noncomputable def etaStar : ℝ :=
  sSup {η : ℝ | 0 ≤ η ∧ UniformlyTolerable η}

/-- **MAIS-O33's yes/no clause**: *"Is `η* > 0`?"* -/
@[expose] public def maisO33_etaStarPos : Prop := 0 < etaStar

/-- The value MAIS issue [#9](https://github.com/lionellevine/MAIS/issues/9)
proposes for `η*`. -/
@[expose] public def maisO33_etaStarCandidate : ℝ := 0

/-- **MAIS-O33's determine-clause, at the proposed answer.** Print says
*"Determine `η*`"*; this grades the submitted value.

Read it with `maisO33_etaStarIsZeroGivenBaseline`, which is the same equation
without a dependence on Lean's `Real.sSup ∅ = 0`. -/
@[expose] public def maisO33_etaStarIsZero : Prop := etaStar = maisO33_etaStarCandidate

/-- **Print's cited baseline**: that the *uncorrupted* problem is already solved,
which is `η = 0` being uniformly tolerable. Print does not prove this in
`prob:corruption`; it inherits it from `thm:rabe`
(Richens–Abel–Bellot–Everitt), which this repository does not formalize.

The proposition is named so that the dependence is visible to the build rather
than buried in a provenance note: it is the *only* thing between the proved
content — no positive `η` is tolerable — and print's `η* = 0` as a value. -/
@[expose] public def maisO33_baselineTolerable : Prop := UniformlyTolerable 0

/-- **The determine-clause with its one dependence made explicit.** `η* = 0`
*given* that print's own baseline holds. Unlike `maisO33_etaStarIsZero`, the
`0 ≤ η*` half of this comes from an inhabitant of the tolerable set rather than
from the empty-supremum convention, so it says what print's sentence says even
if one refuses that convention. -/
@[expose] public def maisO33_etaStarIsZeroGivenBaseline : Prop :=
  maisO33_baselineTolerable → maisO33_etaStarIsZero

end AISafetyAtlas.Conjectures.MAIS
