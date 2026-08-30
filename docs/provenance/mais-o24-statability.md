# Is MAIS-O24 statable? Clause by clause

MAIS-O24 (`prob:effective` in the pinned MAIS-A2, see
[`mais-source-pin.md`](mais-source-pin.md)) is the foundation several other A2
targets rest on: `conj:exact` (O26) is stated over the class `𝕄(sk, λ, μ)` that
only exists once O24 is solved, and O24's parameter chart is what O28, O30 and
the source-exact forms of O25–O29 and O34 are phrased in.

Before building a predicate for it, each printed clause has to be checked for
whether the atlas can state it *at all*. A clause the atlas silently drops
would make `IsO24Solution` admit a **superset** of genuine solutions, and then a
downstream statement of the form "for every O24 solution, …" would be **stronger
than print** rather than `Same`. That is the failure mode this note exists to
rule out.

## The verdict

**Every clause is statable, every clause is stated, and the bundle is `Same` on
every clause.** The one that looked like it would not be — construction time — is
available in Mathlib. `AISafetyAtlas.Causal.O24Solution` bundles all of them; the table below
records what each rests on.

Stating a clause is not the same as stating it tightly, and two clauses show the
difference.

The construction clause admits no supplied encoding of any kind. Leaving the
variable numbering existential would be an advice channel and would widen the
solution class; see the bullet on naming below.

**Conclusion (b)'s threshold is at print's own quantifier.** Read the quantifier
order:
`prob:effective` says *"Find constants `a, b > 0` depending only on `(m, S)`
such that **for all** `λ, μ ∈ (0, ½)` … (b) … for all `δ` below an explicit
threshold"*. Only `a` and `b` are scoped to `(m, S)`. The threshold is named
inside (b), which is inside the `∀ λ, μ`, itself inside the per-shape *"for each
diagram shape and each compatible graph"* — so print lets it vary with the shape
and with both margins.

`O24Threshold` carries it, indexed by the skeleton and applied at `λ` and `μ`,
and `O24Solution.thresholds` supplies one family per chance-variable count
exactly as `lists` does. It stays a **supplied** field rather than an `∃` inside
conclusion (b): the existential would match print's quantifier position and lose
what *explicit* asks for, since the threshold belongs to the exhibited answer
and not to a proof that consumes it. Giving a supplied field print's own
arguments is the only rendering that satisfies both halves of the sentence.

Two earlier gradings of this clause were wrong, and the error was in the grading
rather than the wording, so both are recorded. It was first a **widening**, on
the ground that an existentially quantified structure field is only *"there
exists a threshold"* while print says *explicit*. That does not survive
comparison with `a` and `b`: identical shape, no formula, no computability,
graded `Same`. The same note said a solution might supply an *"uncomputably
small"* threshold — computability and magnitude are independent, and neither was
what bit. It was then a **narrowing**, which was correct: read at `(m, S)` the
threshold varied with `λ` only through the integer `S` and with `μ` not at all,
so one threshold had to serve every margin pair, including as `μ` tends to `0`
and the cut subclass shrinks around it. That demanded more of a solution than
print does, so the predicate admitted fewer constructions.

`O24Solution` is now **`Same`** on every clause.

| printed clause | statable | with what |
|---|---|---|
| a finite explicit list of rational polynomials `Q^G_1, …, Q^G_r` in `(θ, u)` | yes | `MvPolynomial (ChartIndex G ⊕ UtilityIndex) ℚ`; the `θ` coordinates are `AISafetyAtlas.Causal.ChartIndex` |
| `S = K(G) + 2^{\|𝐙\|}` | yes | `chartDim` is `K(G)`, proved equal to the printed `Σᵢ 2^{\|Pa_G(Cᵢ)\|}` by `card_chartIndex` |
| **list length** polynomial in `S` | yes | `List.length` |
| **degrees** polynomial in `S` | yes | `MvPolynomial.totalDegree` |
| **coefficient bit lengths** polynomial in `S` | yes | `Nat.log 2` of numerator and denominator over `MvPolynomial.support` |
| sparse monomial encoding | yes | `MvPolynomial` is already finitely supported; `support.card` is the sparse length |
| **construction time** polynomial in `S` | **yes** | `Turing.TM2OutputsInTime` at the bound `p.eval S` — see below |
| (a) `𝚫_M = 𝚫_M'` implies `M = M'` on the subclass | yes | `Skeleton.BehaviorEq` and `Model.chartOn` |
| (b) `M' ∈ I_δ(M)` implies `e(M; M') ≤ (K/λμ)^a δ` below a threshold | yes | `InIdentifiedSet`, `modelError` |
| (c) `Leb{θ : \|Q^G_j(θ,u)\| < μ for some j} ≤ S^a μ^b`, for a.e. `u` | yes | `MeasureTheory.volume` on `ChartIndex G → ℝ` (the finite-dimensional pi measure) and `∀ᵐ` for the `u` quantifier |

## Construction time, which is the one that decides it

`prob:effective` requires "the list length, degrees, coefficient bit lengths,
and **construction time** to be polynomial in `S`". A runtime bound is a claim
about a computation model, and the atlas has none of its own.

Mathlib does. `Mathlib/Computability/TuringMachine/Computable.lean` defines

```
structure Turing.TM2ComputableInPolyTime
    {α β αΓ βΓ : Type} (ea : α → List αΓ) (eb : β → List βΓ) (f : α → β)
    extends TM2ComputableAux αΓ βΓ where
  time : Polynomial ℕ
  outputsFun : ∀ a, TM2OutputsInTime tm … (time.eval (ea a).length)
```

— a Turing machine, a **polynomial** time bound, and a proof the machine
computes `f` within `time(input length)` steps.

**That is not the printed clause.** The bundled structure measures time in the *encoded input length*, while `prob:effective`
measures it in `S = K(G) + 2^{|𝐙|}`. Those differ, and not harmlessly: `S` can
be exponentially larger than the ~`m²` bits needed to write the diagram shape
and graph down, so poly(input length) is the **stricter** requirement. It would
admit fewer solutions, and a downstream "for every O24 solution, …" would then
be *narrower* than print — the mirror image of the failure this note exists to
rule out, but a failure all the same.

The repair needs no padding and no new theory. `TM2ComputableInPolyTime` is a
bundling of the underlying relation

```
Turing.TM2OutputsInTime tm (init input) (some (output)) (p.eval S)
```

which takes the step bound as a plain `ℕ` and so states "polynomial in `S`"
directly. Use the relation, not the wrapper.

**What it costs.** Two `Computability.Encoding`s:

1. **Input** — the diagram shape `(𝐂, 𝐎, 𝐙)` together with the graph `G`. Finite
   combinatorial data.
2. **Output** — a list of sparse rational multivariate polynomials, which needs
   an encoding of `ℚ`; `Denumerable ℚ` supplies the bijection.

The combinators are half there, and the difference is what decides how much
`IsO24Solution` costs:

- `finEncodingPair {α β} (ea : FinEncoding α) (eb : FinEncoding β) :
  FinEncoding (α × β)` **is** the combinator it looks like, and is usable as-is.
- `finEncodingList (α) [Fintype α] : FinEncoding (List α)` is **not**. Its
  `encode` is `id`: it encodes a list over a finite alphabet *as itself*. It does
  not carry an encoding of `α` to an encoding of `List α`, which is what a list
  of polynomials needs. That lift is not in
  `Mathlib/Computability/Encoding.lean` at the pinned revision.

So: ordinary but real work, not assembly from parts already on the shelf.

**Built on 2026-08-21, and the estimate held.**
[`AISafetyAtlas/InformationTheory/PrefixCode.lean`](../../AISafetyAtlas/InformationTheory/PrefixCode.lean)
supplies both codes from scratch over a three-symbol alphabet, with
`IsPrefixCode` as the composable property and `IsPrefixCode.pair` /
`IsPrefixCode.list` as the combinators the library did not have. Two decisions
there are load-bearing rather than stylistic:

- **The codes are definitions, not existentials.** A clause reading *"there exist
  a machine **and encodings** such that …"* is met by advice: choose an encoding
  that already carries the answer and let the machine copy its input.
- **Including the variable naming.** Writing the polynomials over `Fin S` with a
  *supplied* bijection `O24Var Z G ≃ Fin S` as a field of `O24Solution` would be
  advice of exactly this kind, on the reasoning that print fixes no numbering so
  demanding one would be an extra obligation. That is the argument rejected one
  bullet above, and it fails for the same reason: a bijection is an encoding. An unrestricted one
  carries `log₂(S!)` bits of per-instance choice about *which* coordinate each
  monomial is about, is not required to be computable, and is chosen by the
  solution — so a machine emitting fixed syntax could let the bijection decide
  what it meant. Repaired on 2026-08-21: `SparseMonomial` carries the variables
  themselves, `ofSparsePoly` decodes with no bijection interposed, and
  `encodeO24Var` names a table coordinate by its chance variable and parent
  configuration and a utility coordinate by its configuration of `𝐙`.
  `card_le_o24Size` (`m ≤ S`) is what keeps those names short enough for the
  clause to stay meetable.
- **The code is binary, not unary.** The size clause bounds coefficient bit
  lengths by a polynomial in `S`, so a unary transcript would be exponentially
  long in `S` and no machine could write it in `poly(S)` steps. A unary code
  would make `prob:effective` unsatisfiable for reasons unrelated to the
  mathematics.

One thing the note did not anticipate: **the output must be required to *decode*
correctly, not to match one serialization.** A polynomial's sparse form is a set
of monomials, so fixing a serialization also fixes an arbitrary order over that
set and demands the machine reproduce it — an obligation print does not make.
`O24Constructor.output_decodes` asks that the machine's syntax decode to the
supplied list. The order of `Q₁, …, Q_r` *is* pinned, since print numbers those.

## What is built so far

[`AISafetyAtlas/Causal/ParameterChart.lean`](../../AISafetyAtlas/Causal/ParameterChart.lean)
— the coordinate layer only. `ChartIndex G` is the index set of the free table
entries; `card_chartIndex` proves there are `K(G)` of them against the printed
formula; `Model.chartOn` reads a model's coordinates and `Model.ofChart` rebuilds
a model from a point, with `Model.chartOn_ofChart` and `Model.ofChart_chartOn`
making the pair a bijection onto the models carrying `G`.

Both directions are load-bearing rather than decorative: (c) integrates over `θ`
with no model present, while (a) and (b) cut a subclass of *models* by a
condition on their `θ`. Those are the same condition only because every point of
the box is realized by a model.

[`AISafetyAtlas/Causal/EffectiveGenericity.lean`](../../AISafetyAtlas/Causal/EffectiveGenericity.lean)
— the certificate layer, complete as of 2026-08-21. All three conclusions, the
structural size bounds, the construction-time clause, and the bundled
`O24Solution` that carries them together.

Three repairs landed with the bundle, each of which a looser rendering gets
wrong:

- **The list is quantified before the utility.** Print asks for a list *"for each
  diagram shape `(𝐂, 𝐎, 𝐙)` and each compatible graph `G`"*, with `u` a
  *variable* of the polynomials. Indexing the list by a whole `Skeleton`, which carries
  a numeric utility, would let a solution supply a different certificate for each
  utility it is supposed to treat symbolically. `O24Assignment` reads `(𝐎, 𝐙, G)` and nothing else, and
  `o24List_indifferent_to_utility` checks that on two skeletons that share a
  shape and differ in their gap.
- **Conclusion (c)'s utility domain is bounded.** `u : {0,1} × dom(𝐙) → [0,1]`
  is print's own range, and taking *"Lebesgue-almost-every `u`"* over all of
  `ℝ^{2^{|𝐙|}}` is **stronger** than print. The printed box has positive measure,
  so a null subset of the ambient space meets it in a set null for the box:
  almost-everywhere on `ℝ^{2^{|𝐙|}}` *implies* almost-everywhere on the box.
  The unbounded form therefore demands the estimate at utilities no skeleton
  realizes, admits fewer solutions than print's problem, and would make every
  downstream *"for every O24 solution, …"* weaker than print. `utilityBox` is
  that printed domain and `utility_mem_utilityBox` shows nothing realizable is
  discarded.

  A derived `[-1,1]` *gap* box would be the atlas's own, not print's:
  `def:cid` prints `[0,1]` utility cells, so `utilityBox` is read off the source
  and `O24Var` is in print's `(θ, u)`. The second stale bullet in this list, after the recovery threshold
  one above.
  (Note the contrast with the `θ` bound in the same conclusion, which fails the
  *other* way: measured in all of `ℝ^{K(G)}` an excluded set of infinite measure
  would pass, since `(⊤ : ℝ≥0∞).toReal = 0`.)
- **The threshold in (b) is supplied, not merely existential.** Print calls it
  *explicit*; a bound that only exists is the one thing an explicit threshold is
  not. It is not a field of `O24Constants` alongside `a` and `b`, because print does
  not scope it there.
  `O24Constants` scopes its fields to `(m, S)`, which is print's scope for `a`
  and `b` and **not** for the threshold: conclusion (b) sits inside *"for all
  `λ, μ ∈ (0, 1/2)"*, so a threshold reading only the integer `S` varies with
  `λ` only through that integer and with `μ` not at all — a stronger demand than
  print's, hence fewer admitted solutions, hence a weaker statement wherever a
  solution is universally quantified. It is now `O24Threshold`, carried by
  `O24Solution.thresholds` as one family per chance-variable count, applied at
  `λ` and `μ`. `O24Solution.thresholds`' own docstring records why it is not a
  field of `constants`.

## What this does not buy

**CONJ-006 (O25) does not need O24 at all.** `prob:exact` asks for a
class *satisfying* conclusions (a)–(b) of `prob:effective` — properties of a
class, statable directly — not for one arising from a solution's polynomial
list. Since 2026-08-21 every axis O24 could have closed there *is* closed:
`ExactClassAssumptions` carries `IsCompactSemialgebraicClass` and
`ContainsChartBox`, and the statement sits in `AISafetyAtlas.Causal.Query` over
real tables. CONJ-006 is `Same`. The `ε` range that had made it `Narrower` — `prob:exact` restricts `ε` nowhere and `IsPolyLogBudget` had supplied an `ε₀` — closed the same day by deleting the restriction; that axis was unrelated to O24. It had been `Mixed` for a reason
unrelated to O24 — its estimator returns a `PMF`, where `subsec:queries`
constrains the output law not at all, which is a widening — and
`Causal.measureMinimalBudget_eq_exactMinimalBudget_binary` closed that by proving
the two budgets are the same number. Non-vacuity was a proof debt there rather
than a scope delta, and it closed on 2026-08-21:
`Examples.Conjectures.MAIS.oneNode_exactClassAssumptions` inhabits
`ExactClassAssumptions` on a one-node margin class.

**CONJ-003 (O26) did need it, and that is what the bundle bought.** `conj:exact`
opens *"For `𝒩 = 𝕄(sk, λ, μ)`"*, which is O24's cut, so until the bundle existed
the conjecture could not state print's class and instead quantified over any
class meeting a supplied genericity witness — admitting classes print never
reaches. Since 2026-08-21 it cuts by `O24Solution.marginClass`, which closed the
rational-table axis as a byproduct (`θ` is real) and let O26 move into
`AISafetyAtlas.Causal.Query`, where the analyst is randomized as
`subsec:queries` requires.

Two antecedents *stronger* than print's went with the stand-in. Properness and
tightness of the cut existed because an arbitrary witness could cut nothing or
could decouple `μ` from the class; a solution's list can do neither, since it
must satisfy conclusion (c). That is the same fact `effectiveMarginClass_nil` and
`not_o24Identifies_nil` check from the two sides.

The trade is visible in the non-vacuity column: the old package had a checked
inhabitant, and `O26ClassAssumptions` has none, because inhabiting it now needs a
solution to this open construction problem. Better fidelity, larger debt. CONJ-006
made the same trade and has since paid it off — its `ExactClassAssumptions` is
inhabited, because its clauses are conditions on a class that can be exhibited,
where O26's package additionally quantifies over a supplied `O24Solution`.

O24 is itself a **construction problem** — "exhibit a finite explicit list …
Find constants `a, b > 0`" — so the atlas holds `IsO24Solution` as a *predicate*
and quantifies over solutions rather than exhibiting one. That is
`o27ProblemTargets`'s pattern generalised, and it is why `DetermineProblem` is a
permanent grade in `conjectures.yaml` rather than a debt: the source genre is
permanent.

## A submitted candidate says clause (a) and clause (c) cannot both hold

**The pinned source itself flags this and the atlas had not engaged it.** At the
pinned revision, `open-problems/MAIS-O24.md` carries the status line *"open;
full solution pending review (issue #7)"*. The bytes this note grades against
therefore name a candidate resolution, and nothing in the atlas cited it until
2026-08-22. Four of the five A2 problems the atlas tracks carry such a pointer
at the pin — O23 to issue #6, O31 to issue #8, O34 to issue #4, all three
already engaged — so O24 was the outlier rather than a new genre.

**What the candidate claims.** No finite polynomial lists satisfy conclusions
(a) and (c) at once, independently of every complexity bound in (b). The
mechanism is a collision family that stays a collision on an open set of tables.
At the two-variable utility whose gap is `1/2` off `(1,1)` and `-1/2` there, an
`X → Y` model and an edgeless model have equal behavioural transforms across an
open box of parameters, because the gap reads only the `(1,1)` cell and the two
models agree there. Clause (a) then forces some discriminator to vanish
identically at that utility; polynomial continuity makes it uniformly small on a
fixed positive-volume table box at nearby utilities; and clause (c)'s bound
`S^a μ^b` tends to zero while the excluded volume does not.

**Where it would bite the atlas.** `O24ExcludedSetSmall` reads its exponents from
`O24Constants`, whose fields `O24Constants.a` and `O24Constants.b` are
`ℕ → ℕ → ℝ` — functions of the variable count and of `o24Size` only. They do not
depend on the utility, which is exactly the uniformity the argument attacks.
Conclusion (a) is `O24Identifies`, whose quantifier ranges over
`effectiveMarginClass` and so compares models across different graphs, which is
what the collision needs. If the argument is sound, `O24Solution` is an
uninhabited type.

**What has been checked here, and what has not.** The collision step is
verified: `Examples.Causal.margin_class_not_identifiable` already machine-checks
that utility on rational literals, and a parametrised re-derivation confirms the
discarded transition column is invisible to the transform for *every* value of
that column and *every* intervention profile, which is stronger than the open
box the candidate needs. The limit step — a real polynomial vanishing on a
nonempty open set is the zero polynomial, then uniform smallness on a compact
box — is standard and is **not** formalised in the atlas. So this note records a
citation, not a verdict.

**What it does not change.** CONJ-003 stays `OPEN`, and its entry says no
`O24Solution` is exhibited in the tree, so nothing recorded here is
contradicted. The former nonempty-class O26 variant is no longer a ledger row;
it remains explicitly atlas-only in Lean. What changes is the reading of the
live row's debt: if the candidate holds, the antecedent is not merely
un-inhabited but uninhabitable, and CONJ-003 would be vacuously true — provable
for a reason that makes it worthless. Establishing that in Lean needs the
multivariate identity theorem and the compact-box continuity step, and is
costed open work rather than a claim this note makes.

**Pin.** The candidate's note is a GitHub attachment rather than a path in the
pinned tree, so it carries its own hash:
`MAIS-O24-candidate-solution.pdf`, sha256
`fd096dea004135fbbed054619857b307881d6432925d1ff1cae5ae3f45d16477`, four pages,
dated 2026-08-03, authored by OpenAI Codex after one prompt by Svyatoslav
Novikov (kumino), offered under CC BY 4.0, and explicitly claiming no human
referee or journal review. It grades MAIS-O24 at commit
`43016a3e5c94edfca55ba49bd3e16770f7ac5dae`, which is **not** the atlas pin. The
two revisions were compared: `open-problems/MAIS-O24.md` is byte-identical
between them apart from the status line quoted above, so the candidate and the
atlas are reading the same printed problem.
