# MAIS-A2 statement coverage

Every MAIS-linked ledger row is also printed source-beside-Lean, with a read-back from its binders and a statement of what differs, in [`mais-conjecture-source-vs-lean.md`](mais-conjecture-source-vs-lean.md).

This note audits the fourteen A2 targets at the pinned MAIS revision used by
the causal concordance: MAIS-O2 and MAIS-O23--O35. It distinguishes a compiling
Lean proposition from the additional foundations needed to state the source's
literal continuous or stochastic scope.

The conjecture mechanism uses `def name : Prop := ...`; it never uses `sorry`
or an axiom. A row marked **proof only** means that every object in the stated
Lean specialization now exists and a contributor can settle that proposition
without changing its signature. It does not erase an explicitly listed source
scope delta.

**Every one of the fourteen targets has a ledger row**, and the `Ledger` column
says which kind. A *determine* problem has no truth-valued claim that is the same
statement as it — a fact about transcription rather than about solvability — so
its row carries a specification and its answer fields rather than a `Prop`. A row
of kind `target` names the specification a proposed answer must satisfy, and a
row of kind `blocked` names the declarations that are missing. Counting only the
rows that hold a `Prop` therefore undercounts what is covered.

## Matrix

| ID | Ledger | Scope | Lean statement status | What remains | Source-scope boundary |
|---|---|---|---|---|---|
| O2 | `CONJ-018` *blocked* | `NotFormalized` | **Definition-blocked** | Sampled-action transcript laws and independent response corruption at a known level | Two of the four things this row used to list arrived with `AISafetyAtlas.Causal.Query`: the analyst is randomized with perfect recall, and the risk is the expected error under a supremum over models and adversaries. What is missing is the *oracle*. `prob:noisy` replaces the policy-probability oracle by sampled actions, so a transcript's answers become draws rather than numbers, and the query layer observes exact real policy probabilities. **A sampled-answer transcript now exists for one channel**: `AISafetyAtlas.Conjectures.MAIS.O29Experiment` runs the same protocol with the answer drawn from the model's Boltzmann response. That is a precedent for the shape, not this row's oracle — `prob:noisy`'s answer is a sampled *action* under a supplied policy, not a binary Boltzmann response, and the O29 layer is written at `Bool` rather than at an arbitrary action type. Corruption is a second, independent gap |
| O23 | `CONJ-004` *claim* | `Same` | **Resolved statement, on both of print's phrasings** — `maisO23_marginsDoNotSuffice` for the transform reading, and `Examples.Causal.margin_class_not_identifiable_shared_optimal` for the *Equivalently (by `prop:equiv`)* reading, which exhibits two distinct margin-class models with different graphs sharing a policy family admissible at level `0` — a common family of optimal policies | Nothing; the proof is `margin_class_not_identifiable`, transported to the reals | **`Same` as `q:ident`.** The `Prop` quantifies over an arbitrary skeleton on a finite binary chance-variable set with real tables, which is the printed quantifier. The witness is narrower than the statement and that is free for an existential: it is checked on rational literals and carried over by `Skeleton.marginClass_mapRat` / `Skeleton.behaviorEq_mapRat`, covering real CPTs and every real mixture |
| O24 | `CONJ-012` *target* | `Same` | **Solution predicate complete, graded `Same`** — `O24Solution` | **Answered 2026-08-30: no solution exists** (`Examples.Causal.O24Refutation.isEmpty_o24Solution`), from the candidate in MAIS [issue #7](https://github.com/lionellevine/MAIS/issues/7). | Regraded on 2026-08-21, when the last clause landed. All three conclusions, the structural size bounds and the construction-time bound are fields of one bundle, so a downstream *"for every O24 solution …"* is print's quantifier rather than a superset. Four fidelity points are worth naming. Print writes the polynomials in `(θ, u)`, and the row is stated in those coordinates, with no bridge. `(θ, u)` carries `2·2^{|𝐙|}` utility coordinates while the same sentence sets `S = K(G) + 2^{|𝐙|}`, and `S` is not a class: print introduces it only as a complexity budget — *"require the list length, degrees, coefficient bit lengths, and construction time to be polynomial in `S`"* — and never claims to count variables, and `poly(S)` is insensitive to a factor of two. So there is one printed variable set, `(θ, u)`, and the gap list is a strict restriction of it. `O24Var` is now `ChartIndex G ⊕ (Bool × UtilityConfig Z)` — print's `(θ,u)`, with the two utility cells per configuration — so the solution predicate admits exactly print's lists and CONJ-003 is `Same` on the coordinate axis rather than below print. `card_o24Var` no longer claims `S` counts the variables; `card_o24Var_le` records that the count is within a factor of two of `S`, which is all `poly(S)` can see. What remains true is that `Skeleton.gap_determines_marginClass` and `Skeleton.gap_determines_behaviorEq` prove the discarded coordinate is invisible to everything conclusions (a) and (b) are stated over. Then: the list reads the diagram shape `(𝐎, 𝐙, G)` and **not** the numeric utility, which print makes a variable of the polynomials rather than an input to their construction; conclusion (c)'s `u` ranges over `Causal.utilityBox`, which is print's own codomain rather than a restriction the atlas chose — `def:cid` declares `u : {0,1} × dom(𝐙) → [0,1]`, and `utilityBox` is the `[0,1]` box on `Bool × UtilityConfig Z`, which is that same index set. and (b)'s threshold is supplied as data, which is what *explicit* asks for, and is read at `(sk, λ, μ)`, which is where print's quantifier order puts it — `prob:effective` scopes only `a` and `b` *"depending only on `(m, S)`"*, and names the threshold inside conclusion (b), inside *"for all λ, μ ∈ (0, ½)"*. Reading the threshold at `(m, S)` instead would vary it with `λ` only through the integer `S` and with `μ` not at all, so one threshold would have to serve every margin pair; `O24Threshold` and `O24Solution.thresholds` bind it where print does, and this row is `Same`. The construction clause fixes every code as a definition — an existential encoding is satisfiable by advice — and asks the machine's syntax to **decode** to the supplied list rather than to match one serialization, since a polynomial's sparse form is a set and fixing a byte order would be an obligation print does not impose. That last point took two passes: the first version wrote its syntax over `Fin S` and carried a solution-supplied bijection `O24Var Z G ≃ Fin S`, which is an encoding and therefore advice — `log₂(S!)` bits of uncomputed per-instance choice about which coordinate each monomial names, so a machine emitting fixed syntax could "construct" a certificate it never computed, and the bundle admitted more solutions than print's problem. Since 2026-08-21 the syntax names its variables and `encodeO24Var` is a definition, with `card_le_o24Size` keeping names short enough for the clause to stay meetable |
| O25 | `CONJ-006` *claim* | `Same` | **Statement only, graded `Same`** — `maisO25_exactQueryRate` | Prove or refute the polynomial-log budget bound and the constant-factor adaptivity claim. **`ExactClassAssumptions` is inhabited as of 2026-08-21** by `Examples.Conjectures.MAIS.oneNode_exactClassAssumptions`, over the one-node class of `Examples.Causal.OneNodeClass` — all eight clauses, with `K = 1`, `L = 10`, `rho = 1 - 2*lambda` and `delta_max = 1` — so the `Prop` is not vacuously true. That shows the antecedent is nonempty, not that it is selective: at one vertex only the edgeless graph exists, so several clauses hold for reasons about the vertex set. **The last scope axis closed**: `measureMinimalBudget_eq_exactMinimalBudget` proves `N(ε)` is the same number whether the analyst's output is a `PMF` or an arbitrary probability measure | All four axes that had made this `Mixed` are closed. The last of them was in the widening direction: `Causal.RandomizedEstimator` returns a `PMF`, hence a countably supported output law, where `subsec:queries` says only that the analyst *"outputs `(Ĝ, θ̂)`"* and the model space is uncountable. Restricting the output laws shrinks the set the infimum ranges over, so `exactMinimalBudget` can only rise and a finite bound on it is **stronger** than print's. The schema has no `Wider`, so `Mixed` here means widening-only. It does not rise. `measureMinimaxRisk` is the same definition over arbitrary output measures and the two agree, by an `O(ε)` rounding cost onto a countable set of rounded models (`AISafetyAtlas.Causal.ModelSpace`); `measureMinimalBudget_eq_exactMinimalBudget` carries that to `N(ε)`, and `Examples…o25_minimalBudget_eq_measure` instantiates it at this row's quantifier. On the closed axes: The `Prop` is the printed *decide*-clause: a **one-sided** bound `N(eps) <= poly(K,1/lambda,L,1/rho) log(1/eps)`, not a `Theta`, with no `m` in the polynomial and with the coefficient and degree chosen **before** the skeleton and class. It is now stated over real tables in `AISafetyAtlas.Causal.Query` — `N(eps)` is `exactMinimalBudget`, the infimum over **randomized** analysts of the supremum of the *expected* error, valued in `ℕ∞` so that `⊤` refutes a finite bound instead of satisfying one — and over `prob:exact`'s own class: `IsCompactSemialgebraicClass` plus `ContainsChartBox`, an affine box over all `K(G)` chart coordinates. The recovery modulus takes `M'` in print's `I_delta(M)` rather than in the class, a defect that had been repaired in `O24RecoveryModulus` and left standing in the O25 stand-in |
| O26 | `CONJ-003` *claim* | `Same` | **Statement only, graded `Same`** — `maisO26_exactRate` | Prove or refute the `Theta(K log(1/epsilon))` rate under its constant bound; **and exhibit an O24 solution** | The class is `O24Solution.marginClass`, print's own `𝕄(sk,λ,μ)`, and `N(ε)` is the randomized exact-policy-probability minimax budget. Properness, tightness, nonemptiness, compact semialgebraicity and O25's richness condition are absent because O26 does not state them. `IsClassChartDim` binds print's `K`. `O24Solution.exists_o26ClassAssumptions` now proves that any hypothetical O24 solution supplies the named linear recovery modulus and hence an `O26ClassAssumptions` instance; the remaining non-vacuity debt was exactly the absence of an exhibited `O24Solution`, and since 2026-08-30 that absence is known to be permanent. No compact-semialgebraic premise is inherited, because `conj:exact` does not state one. **The rate predicate is proved to be a genuine `Theta`**: `IsThetaWithMarginBound` is not Mathlib's `Asymptotics.IsTheta`, because the library predicate cannot express `conj:exact`'s demand that the implied constants be bounded by `A*(1 + 1/lambda + 1/mu + L)^d` -- it quantifies its constants existentially with nothing said about their size. `Examples.Conjectures.MAIS.isTheta_of_isThetaWithMarginBound` proves the atlas predicate **implies** the library one on the punctured right neighbourhood of `0`, so print's *`N(eps) = Theta(K log(1/eps))` as `eps -> 0`* is being asserted in the library's own sense rather than in a lookalike of it. Nonnegativity of the comparison function is not assumed: `0 <= n <= c2 * g eps` with `0 < c2` supplies it. **The bridge is one-directional and the converse is false by expressiveness rather than by missing proof** -- a budget can be `Theta(g)` with constants that blow up as the margins shrink, which is exactly what `conj:exact` denies -- so reading it as an equivalence would silently delete the printed clause the predicate exists to carry. If the literal source statement is false or vacuous, that is a result about MAIS-O26 |
| O27 | `CONJ-013` *target* | `Same` | **All three clauses formalized at print's real quantifier; defective conjecture withdrawn** — `o27RealProblemTargets`, `O27RealRadiusVanishes`, `O27RealHasFirstOrderConstant`, `O27RealEdgeSurvivalRegion`, with `o27ProblemTargets` and its rational predicates kept as the decidable-witness instance | Determine clause (b)'s first-order constant, and the rest of clause (c)'s region, or propose a truth-valued candidate for a clause. **Clause (a) already has a settled negative instance, and this row used not to say so.** Print writes that (a) *refines* `q:ident`, and the atlas refutes `q:ident` (`maisO23_marginsDoNotSuffice_holds`, the O23 row above). The refutation carries: equal transforms give the two models one shared zero-regret policy family, so each lies in the other's identified set at `delta = 0` and hence at every `delta > 0`, and their graphs differ, so `modelError` is `1` throughout. The radius is pinned at `1` on that skeleton, so O27(a) fails there — `Examples.Conjectures.MAIS.regretRadius_collision_eq_one` and `not_o27RadiusVanishes_collision` at the rational layer, and since 2026-08-23 `realRegretRadius_collision_eq_one` and `not_o27RealRadiusVanishes_collision` at print's own real quantifier, all resting on `Causal.inIdentifiedSet_mono`. The same collision settles clause (c) negatively at `s = lambda`; see the notes column. That settles (a) at one print-legal `(sk, lambda)` and not at every one — print contemplates the answer varying, since clause (b) opens *assuming it is zero*. What remains for (a) is the general question. (b) has no instance either way. (c) is **not** untouched: one point is certified outside the printed region, at `s = lambda` and every positive `delta`, and the exhibition half is proved there. What is undetermined is the rest of the `(s,delta)` region, which is what the problem asks for | The source asks for the full set of `(s,delta)` pairs, not a closed threshold cut. **All three clauses reached print's real quantifier on 2026-08-23, and the debt this cell recorded is paid.** `realRegretRadius`, `RealRadiusTendsToZero` and `O27RealRadiusVanishes` state the radius, its vanishing and clause (a) over real tables and a real regret range, taking the supremum directly in `R` rather than through an embedding of rational errors; `HasRealFirstOrderRadius` and `O27RealHasFirstOrderConstant` state (b) with print's *matching statement* -- the pair at distance `c*delta` -- as a separate conjunct, since a limit of a supremum does not by itself produce a pair attaining it; `RealEdgeStrengthAtLeast`, `RealEdgesSurviveAt` and `O27RealEdgeSurvivalRegion` state (c) as the full real two-dimensional region rather than a closed threshold cut. `o27RealProblemTargets` is the answer object a solver fills. The rational layer above is now the transported instance rather than the statement of record, and it stays because that is where a decidable witness is computed; the transport is `Skeleton.marginClass_mapRat` and `Skeleton.behaviorEq_mapRat`, the same pair the O23 row uses, and it is not a cast of the hypothesis, since real mixtures are not images of rational ones. **Two clauses now have negative instances at that quantifier**: `not_o27RealRadiusVanishes_collision` for (a), and `not_realEdgesSurviveAt_collision` for (c) at `s = lambda`, with `lam_pair_not_mem_o27RealEdgeSurvivalRegion` reading the consequence off the printed region -- the collision's two models carry opposite one-edge graphs and share a zero-regret family, so an edge as strong as (M4) guarantees is still absent from a model of `I_delta(M)` at every positive `delta`. `realEdgeStrengthAtLeast_lam_of_printedM4` is what makes that non-vacuous, by connecting print's (c) strength to print's (M4) bound. **Clause (c) has two halves and both are now theorems at the collision's own `s = lambda`, which is one point of the region and not the region.** The second -- *exhibit, for the complementary pairs, an `M` and an `M' in I_delta(M)` omitting the edge* -- is `exists_strong_edge_omitted_collision`, stated as print writes it: a model of the class, a second sharing a possible behavior with it, an edge whose strength (M4) puts at least at `lambda`, and its absence from the second. `not_realEdgesSurviveAt_collision` is a corollary of it. Clause (b) has no instance either way. `HasRealFirstOrderRadius` is a non-exposed `public def`, so a downstream instance needs a characterization lemma to reach it; `hasRealFirstOrderRadius_iff` and `realEdgeStrengthAtLeast_iff` supply that for (b) and for the edge-strength predicate (c) reads. Direction still matters when reading a rational result: `phi` is a supremum over the class, so replacing `R` by `Q` can only lower it, and a rational *negative* answer transports up to print while a rational *positive* one does not. No replacement conjecture is invented for a determine-problem |
| O28 | `CONJ-019` *blocked* | `NotFormalized` | **Definition-blocked** | The declared continuous distribution on pairs of profiles, a uniform real mixing weight, masks, and average-case admissibility | A finite or rational surrogate would change the exception-mass question |
| O29 | `CONJ-008` (a) *claim*, `CONJ-016` (b) *target*, `CONJ-020` (c) *blocked* | `Same`, `Same`, `NotFormalized` | **Part (a) resolved** — `maisO29_boltzmannNotInjective`, proved by `maisO29_boltzmannNotInjective_holds`. **Part (b) answered at one instance as of 2026-08-23** — `boltzmannMinimaxRisk_collision_bounds` pins the *randomized* minimax risk over the sampled experiment between `1/2` and `1` at this skeleton, at every budget and every `beta`. Part (c) blocked | Answer (b) on a class where the risk decays -- that is where its rate, its `beta -> 0` deterioration and its `(N,beta)` crossover live, and none of it is touched here | **Part (a) is `Same` as `prob:boltzmann`(a).** Since 2026-08-20 the response probability is a real softmax over *real* causal models, `beta` is quantified on the outside and the skeleton inside, exactly as print asks; the witness is carried to the reals by the value-field transport. **Part (b) has a proved lower bound at print's own quantifier.** `boltzmann_minimax_floor` quantifies over a deterministic estimator; `subsec:queries` takes the infimum over *randomized* strategies of the *expected* error, and deterministic strategies are a subset, so bounding their infimum from below says nothing about print's, which is why the randomized floor is proved separately. `AISafetyAtlas.Conjectures.MAIS.O29Experiment` builds the sampled experiment — the exact-oracle protocol with the policy-probability oracle replaced by one Bernoulli response, and the adversarial policy family dropped because the Boltzmann law is pinned by the model and `beta` rather than left to a tie-break. `runBoltzmannTranscript_congr` proves two Boltzmann-indistinguishable models induce the **same transcript law at every budget**, so the analyst's output law is identical under both; print's error is `1` against whichever graph that output misses, so the two expected errors sum to at least `1` and the class supremum is at least `1/2`. `half_le_boltzmannMinimaxRisk_of_collision` is that bound and `half_le_boltzmannMinimaxRisk_collision` instantiates it on this row's own witness over the full margin class, uniformly in `N` and in `beta`. The risk itself is `boltzmannMinimaxRisk`, the infimum over randomized analysts of the class supremum, and the experiment it is taken over is `runBoltzmannTranscript` with the answer drawn by `boltzmannAnswer`. **A degenerate oracle would have produced the same floor and `boltzmannTrueProbability_of_answer_eq` is what rules that out**: a channel ignoring the model -- a fixed coin -- satisfies the equal-answers lemma vacuously and would floor the risk for a reason having nothing to do with a collision. That theorem is the converse, so the answer law determines the response probability it was built from and the transcript-law collision is exactly the behavioural one. `boltzmannMinimaxRisk_le_one` supplies the other side — print's error is bounded by `1`, so every minimax risk here is — and the pair **determines** (b)'s quantity up to a factor of two at this skeleton: `boltzmannMinimaxRisk_collision_bounds`. There is no rate to deteriorate as `beta -> 0` and no `(N,beta)` crossover to characterize, because the risk never decays. **That is (b) at one print-legal instance, not at every one**, the same standing as the MAIS-O27(a) negative instance; on a class where the risk *does* decay, none of (b) is touched, and that is where its rate and crossover live. The floor's graph condition is load-bearing: without it `modelError` is the table supremum rather than `1` and the floor is not `1/2`, so a same-graph Boltzmann collision does not floor the risk, and any rate answer to (b) must restrict the class away from graph-differing pairs specifically. `modelError` *is* print's `e`, so the value is not an atlas convention |
| O30 | `CONJ-021` *blocked* | `NotFormalized` | **Definition-blocked** | `Σ_W`-identifiability of a named functional, labels for edge and table functionals, and a combinatorial classifier in `(G, W, 𝐎, 𝐙)` | Two of this row's four entries arrived with MAIS-O24's layer and are no longer missing: `ParameterChart` is the real graph-wise chart, and `O24ExcludedSetSmall` shows the Lebesgue-almost-every quantification over it is statable. `BehaviorEq` and restricted profiles are available too. What blocks the row is the shape of the answer: the source asks for an almost-every *classification* of which functionals are identifiable, not for one identifiability predicate |
| O31 | `CONJ-010` *answer*, `CONJ-017` *target* | `Same`, `Same` | **Candidate statement** — `maisO31_chainClassificationCandidate` | Prove or refute the strict-chamber literal-coordinate classification submitted in MAIS issue [#8](https://github.com/lionellevine/MAIS/issues/8) | **`Same` and `Literal` as issue [#8](https://github.com/lionellevine/MAIS/issues/8)'s claim.** The declaration now quantifies directly over every `t ∈ (0,1)` rather than deriving a restricted threshold from an atlas-supplied utility gap. It transcribes the issue's Scope exclusions as the chamber disjunct and `O31ChainModel.Generic`, and states both bullets. `O31ChainModel.toModel_marginClass` proves every valid chart model with a legal endpoint utility belongs to the printed kernel class; `o31BehaviorEqAt_iff_kernel` proves the chart marginals are computed by the embedded kernel; `O31ChainModel.Δ_toModel_endpointGap` proves the actual utility transform is the threshold-centered marginal up to its nonzero scale; `o31BehaviorEqAt_threshold_iff_utilityKernel` transports shared-optimum behavior to that actual utility; and `shareBinaryOptimum_iff_exists_common_action` proves the sign predicate means existence of a shared optimal binary action. The positive-measure example instantiates these bridges. Both chamber antecedents are inhabited. **The chart bridge runs both ways as of 2026-08-23**, and until that day it did not. `O31ChainModel.toModel_marginClass` carries chart objects into the printed class; `exists_O31ChainModel_toModel_eq` carries every model of `𝕄(sk, λ)` whose graph is the printed chain back to a valid chart point, through `O31ChainModel.ofModel` reading a model's own tables as coordinates and `O31ChainModel.toModel_ofModel` showing that reading loses nothing; `O31ChainModel.toModel_injective` names none twice. That direction is the one that needed proving, and the reason is the direction asymmetry rather than symmetry of taste: an existence claim — *there is a model whose behaviour collides* — only gets harder in a larger class, so a chart witness always settled the counterexamples outright, while a singleton-fibre or uniqueness claim gets **easier** as the comparison class shrinks and would have asserted something weaker than print. The identification half is where that bites, and it is this row's own half: `O31IdentifiesCoordinate` and `O31IdentifiesNodeMass` quantify over chart points, while `q:chain` names its comparison class in print — *the models of `MM(sk,lambda)` carrying this chain graph, so that all the parameters are defined* — and issue [#8](https://github.com/lionellevine/MAIS/issues/8) answers that question without redefining the class. `o31IdentifiesCoordinate_iff_class` and `o31IdentifiesNodeMass_iff_class` prove the two predicates **equivalent** to their statements against every model of the printed class carrying the chain graph, so the conjecture is about print's comparison class and not a smaller one. Those fix the *inner* quantifier -- the rivals a coordinate must be identified against. The conjecture's *outer* binder reads `forall M : O31ChainModel n` and is a second exposure of the same kind, since a universal over a smaller class asserts less; `o31Classification_of_candidate` closes it by handing the classification to every model of `MM(sk,lambda)` carrying the chain graph, read at the chart point its own tables name. Both directions of the chart correspondence therefore have a consumer, which is the difference between a surjectivity lemma being available and the claim being stated at print's class. That is the same footing O34 reached with `exists_pairModel_toModel_eq` and `o34_classFibre_iff_candidate`. Stated in `AISafetyAtlas/Conjectures/MAIS/O31Chart.lean` and `O31.lean`, whose headers carry the same reading |
| O32 | `CONJ-022` *blocked* | `NotFormalized` | **Definition-blocked** | Finite communicating controlled Markov processes, composite goals and depth, bounded goal-conditioned agents, first-action families, and their resolution radius | This is the RABE25 goal setting, not the interventional causal model |
| O33 | `CONJ-023` *blocked* | `NotFormalized` | **Definition-blocked** | O32's goal layer plus randomized analysts, polynomial query budgets, persistent corruption, and success probability | Independent channel corruption from O2/O35 is not the persistent corruption in O33 |
| O34 | `CONJ-005` (a) *claim*, `CONJ-009` (a) *answer* | `Same`, `Same` | **Part (a) margin subquestion resolved** — `maisO34_marginAloneDoesNotIdentify`, proved by `maisO34_marginAloneDoesNotIdentify_holds`; **issue [#4](https://github.com/lionellevine/MAIS/issues/4)'s complete part-(a) candidate resolved affirmatively** — `maisO34_exactFiberCandidate_holds`; part (b) blocked | Local constants, singular regimes, and the graph threshold remain unstated | The margin-sufficiency witness is checked on rational literals and transported to the real chart. A narrowing was found and removed on 2026-08-21: the `Prop` had asked for `M.parents != M'.parents` and carried no `M != M'` clause at all, so a same-orientation collision — which answers `prob:starter-set`(a) just as well — was excluded. It now asks only `M != M'`, and the existing two-graph witness still discharges it. For the issue [#4](https://github.com/lionellevine/MAIS/issues/4) chart, `PairModel.toModel_marginClass` proves chart validity gives membership in the printed kernel class, `behaviorEq_iff_kernel` proves chart transform equality is exactly kernel behavior, and `hasSingletonFibre_iff_kernel` transports singleton-fibre claims in both directions. Thus the proved chart criterion is connected formally to `𝕄₂(λ)`, not by prose alone. Since 2026-08-23 the chart is also proved **onto** that class — `exists_pairModel_toModel_eq` names every model of the family carrying an edge, and `PairModel.toModel_injective` names none twice — so `hasSingletonFibre_iff_kernel_class` and `o34_classFibre_iff_candidate` state the criterion against every model of `𝕄₂(λ)`. That direction is the one that needed it: a singleton claim proved only over chart points would have been weaker than print's, since ruling out collisions is easier in a smaller comparison class. `isSemialgebraic_o34GlobalSingletonCandidate` then discharges the printed adjective: the criterion cuts a semialgebraic subset of `def:twovar`'s seven real coordinates, with the two real-quantifier clauses eliminated explicitly by `separatedValues_eq_singleton_iff` and `separatedValues_nonempty_iff` rather than by appeal to Tarski–Seidenberg. Part (a) is therefore covered end to end; part (b) is untouched. Part (b) is untouched and the issue is not accepted as a whole |
| O35 | `CONJ-024` *blocked* | `NotFormalized` | **Definition-blocked** | The O34 two-variable real chart plus sampled-action minimax risk, regret adversaries, switching surfaces, and binary-channel capacity | Exact-query definitions cannot state the sampling/regret/corruption crossover |

## The margin class is certified against print

Every row above is stated over `Skeleton.MarginClass`, whose six conditions are
categorical while `def:margin` prints them for binary variables. Since
2026-08-21 that widening is checked rather than inspected:
`Skeleton.marginClass_iff_printed` proves the categorical class equals the
printed one at `binaryDim`, with `PrintedM1` over the `1`-cells a binary table
actually stores, `PrintedM4` comparing the two parent configurations that differ
in the edge's source, and `PrintedM5` reading `Anc(U)` over `𝐙 ∪ 𝐎` because
`def:cid` gives `U` the parents `{D} ∪ 𝐙` and `D` the parents `𝐎`.

(M2), (M3) and (M6) need no restatement, for a proved reason: `gap_parents` says
the utility gap factors through `𝐙`, so quantifying them over full assignments
*is* quantifying over `dom(𝐙)`, and `m2_of_padded` reduces (M2) to the
`2^{|𝐙|}` padded configurations. No drift was found — which is the result, not a
formality: nothing in the build would have reported one before.

## Counts

- Four source targets have complete truth-valued propositions, all four at
  `Same` scope: O23, O25, O26, and the issue-[#8](https://github.com/lionellevine/MAIS/issues/8) candidate answer to O31. O26
  reached the source's literal standalone quantifier on 2026-08-23 when compact
  semialgebraicity was deleted from its antecedent rather than justified as an
  inherited premise.
- **Four more are `Same` without being propositions**: O24, O27, O29(b) and the
  printed `q:chain` question carry specifications over a candidate answer rather
  than a doubted `Prop`, and the scope grade is on the specification. Seven rows
  are `NotFormalized`, the sentinel for a row with no Lean object and therefore
  nothing to be `Same` as.
- **`Same` grades what is stated, not how much of the problem is stated.** Every
  row's `resolution` opens with a `Coverage:` sentence naming the clause it
  reaches, because the two come apart: O29 is `Same` on (a) and (b) and blocked
  on (c). The printed `q:chain` question is the case where they came apart
  *inside a row* — it was graded `Same` for one day on 2026-08-24 while carrying
  a specification without print's *almost every θ* quantifier, and its own note
  listed that quantifier among what was missing. It was blocked and is `Same`
  again the same day, now against `IsO31IdentifiableSetAlmostEverywhere`: the
  chain's parameters are `ℝ × (Fin n → Fin 2 → ℝ)`, which carries Lebesgue
  measure with no construction of the atlas's own, so print's sentence is
  statable at every chain length rather than only at the two-node case where
  three coordinates had been written out by hand.
  O27 instead has faithful target definitions because the printed
  determine-problem is not truth-valued; its defective candidate is no longer a
  ledger row. Two of its three clauses are nonetheless not untouched, and since
  2026-08-23 all three are stated at `prob:floor`'s own real quantifier. Print
  says (a) refines `q:ident`, and the O23 refutation pins the radius at `1` on
  the collision skeleton, so (a) fails there —
  `not_o27RealRadiusVanishes_collision`, with
  `not_o27RadiusVanishes_collision` the rational instance. The same collision
  refutes (c) at edge strength `lambda`, since its two models carry opposite
  one-edge graphs and share a zero-regret family
  (`not_realEdgesSurviveAt_collision`). One print-legal instance is settled for
  each; the general questions are not, and (b) has no instance either way.
- Two source problems are covered in part: O29, whose part (a) is resolved, whose
  part (b) is answered at one skeleton and nowhere else -- the randomized minimax
  risk is pinned between `1/2` and `1` there, at every budget and every `beta`,
  by `boltzmannMinimaxRisk_collision_bounds` -- and whose part (c) stays blocked;
  and O34, whose part (a) is resolved on both clauses --
  the negative margin subquestion and issue [#4](https://github.com/lionellevine/MAIS/issues/4)'s complete singleton criterion --
  while part (b) stays untouched.
- O24 is a **construction problem** rather than a truth-valued target, so it has
  a complete solution predicate instead of a proposition, and downstream
  statements quantify over solutions.
- Six targets remain definition-blocked: O2, O28, O30, O32, O33, O35.
- Of the seven registered A2 propositions, three are open (O25, O26, O31) and
  four are resolved — three by checked negative witnesses (O23, O34(a)
  margin-sufficiency, O29(a)) and one affirmatively (issue [#4](https://github.com/lionellevine/MAIS/issues/4)'s O34(a)
  singleton criterion). The defective O27 encoding is retained only as history,
  outside the ledger.

The dominant remaining dependencies are two independent foundations:

1. a sampled statistical-experiment layer (O2, O29(b)--(c), O33, O35);
2. a controlled-Markov/composite-goal layer (O32--O33).

The third, a real polynomial/measure parameter space, **landed on 2026-08-21**.
`ParameterChart` supplies the real chart with `K(G)` proved against the printed
formula, `EffectiveGenericity` supplies the polynomial certificate and the
Lebesgue estimate over it, and O25 and O26 are now stated on that layer rather
than on rational stand-ins. What it leaves behind for O28, O30 and O34(b) is not
the parameter space but the *shape* of their answers -- an average-case exception
mass, an almost-every classification, a graph threshold.

Those are definition tasks. Once one lands, each dependent row can move to a
closed `Prop` without anyone proving the mathematical answer.

## Fidelity audit of the O24/O25/O26 rows, 2026-08-22

Method: read each printed clause from the pinned `agendas/A2/MAIS-A2.tex`
(sha256 `d61be3ee…`, re-fetched and re-hashed), then read the atlas side off
**elaborated binders** with `#print`, never off the printed object — the rule
`AGENTS.md` records, because an axis enumerated by eye is priced wrong.

Two readings of the printed text settle the scope of the O24 clauses.

* **The utility is bounded by print.** `def:cid` declares
  `u : {0,1} × dom(𝐙) → [0,1]`. So `Causal.utilityBox`, a `ClosedBox 0 1`, is
  print's own codomain and not an atlas restriction. Conclusion (c)'s
  almost-every-`u` quantifier ranges over exactly the utilities a skeleton has.
* **The exclusion exponents are uniform in `u` by print.** `prob:effective` says
  *"Find constants `a, b > 0` depending only on `(m, S)`"*. `O24Constants.a` and
  `.b` are `ℕ → ℕ → ℝ`, functions of the variable count and `o24Size` alone. That
  is a faithful transcription, which is what makes MAIS issue [#7](https://github.com/lionellevine/MAIS/issues/7) an argument
  against the printed problem rather than against this rendering.

### CONJ-006 (MAIS-O25) — antecedent matches clause for clause

`prob:exact`'s preamble carries four conditions, and `ExactClassAssumptions` has
each exactly once: `𝒩 ⊆ 𝕄(sk,λ)` is `∀ M ∈ modelClass, sk.MarginClass M lam`;
*compact semialgebraic* is `Causal.IsCompactSemialgebraicClass`; *satisfying
conclusions (a)–(b) with modulus `ω(δ) = Lδ`* is the injectivity conjunct
together with `HasLinearRecoveryModulus`; and the *richness* condition is
`Causal.ContainsChartBox modelClass rho`. Nothing else is assumed beyond
well-formedness — `Skeleton.ValidMargin lam`, `0 < L`, and `IsClassChartDim`
binding `K` to `def:margin`'s own maximum. The conclusion is print's two
*"in particular: decide whether"* clauses and no more. `Nonempty C` is not an
extra hypothesis: `(M5)` asks `𝐎 ⊊ 𝐂`, which no empty `𝐂` satisfies. This row is
`Same`, and the *determine*-problem it does not claim is disclosed in its own
docstring.

### CONJ-003 (MAIS-O26) — literal source statement

Checked and faithful:

* `O24Solution.marginClass` unfolds to `effectiveMarginClass`, which is print's
  own `𝕄(sk,λ,μ) := {M ∈ 𝕄(sk,λ) : |Q^G_j(θ,u)| ≥ μ for all j}` from
  `prob:effective`'s preamble.
* The implied constants are constrained **on both sides**. `IsThetaWithMarginBound`
  asks `c₁⁻¹ ≤ A(1 + 1/λ + 1/μ + L)^d` and `c₂ ≤ A(…)^d`; since `0 < c₁`, the
  first is a *lower* bound on `c₁`. That is print's *"implied constants polynomial
  in `1/λ`, `1/μ`, and `L`"*, not a one-sided bound a degenerate constant could
  satisfy.
* `A` and `d` are bound before `∀ m`, and the constant bound mentions neither `m`
  nor `K`. That is print's *"independent of `m` otherwise"*: `K(G) = Σᵢ 2^{|Pa(Cᵢ)|}`
  is itself bounded by a function of `m`, so letting the constants depend on `K`
  would smuggle back the `m`-dependence print excludes.
* `HasLinearRecoveryModulus` is carried because `conj:exact` names `L`; the
  richness condition and its `ρ` are **not** carried, because `conj:exact`'s
  constants are polynomial in `1/λ`, `1/μ` and `L` and say nothing of `ρ`. The
  inheritance from `prob:exact` is selective, and the text is what selects.
`O26ClassAssumptions` contains no compactness, semialgebraicity, richness, or
nonemptiness premise. Those conditions are not printed in O26, so the atlas does
not use them to rescue it. The well-posed nonempty variant remains available as
an explicitly atlas-authored declaration, but it is not a conjecture-ledger row.
`O24Solution.exists_o26ClassAssumptions` proves that the recovery field of any
hypothetical O24 solution supplies the linear modulus O26 names; no manual
choice of `(L, δmax)` remains between the two layers.

**Closed 2026-08-30, against the row.** No `O24Solution` is exhibited because
none exists: `Examples.Causal.O24Refutation.isEmpty_o24Solution` proves
`prob:effective`'s conclusions (a) and (c) incompatible. The non-vacuity debt is
therefore not open but unpayable, and `maisO26_exactRate` is vacuously true
(`Examples.Conjectures.MAIS.maisO26_exactRate_holds`). See
[`mais-o24-refutation.md`](mais-o24-refutation.md).

## Two checks the O31 counterexample rests on, 2026-08-22

`AISafetyAtlas.Examples.Conjectures.MAIS.o31_endpointMarginal_not_identified`
and its box strengthening `o31_endpointMarginal_not_identified_onBox` exhibit
models at which the agenda's heuristic for `q:chain` fails. The reading of that
result depends on two readings of the pinned `.tex`
(`d61be3eed51f618dd3b9389693b14e066e89a9cef5e89985b4226fff658c3c4f`), both
checked here rather than assumed.

**The observer receives behavior, not distributions.** `q:chain` inherits its
identifiability notion from the paragraph opening the subsection on the choice of
interventions, which defines `Sigma_W`-identifiability of a functional `T(M)` at
`M` by requiring `T` to be *"constant on the models in `MM(sk,lambda)` sharing an
optimal-policy family with `M` for every `sigma` in `Sigma_W` and every mask
`O' subseteq O`"*. The quantifier is over shared optimal policies — nothing hands
the analyst a distribution over the chance variables. `O31BehaviorEqAt` is that
relation, with the reading now proved in two steps:
`shareBinaryOptimum_iff_exists_common_action` identifies its sign predicate with
existence of a common optimal binary action, `O31ChainModel.Δ_toModel_endpointGap`
computes the actual normalized utility transform, and
`o31BehaviorEqAt_threshold_iff_utilityKernel` identifies the chart relation with
the shared optimum of the embedded causal-kernel models. Had print
instead given the observer the node distributions, `2/5` and `1/4` would separate
the two models immediately and the theorem would be about a strictly narrower
observation model than print assumes. `q:chain` sets the observation set empty,
so the mask quantifier ranges over the empty mask alone and the Lean statement
needs no mask parameter.

**The heuristic is stated unconditionally.** The parenthetical reads *"mixtures at
`C_j` should reveal the composite transfer map from `C_j` to `C_1` — a product of
2x2 stochastic matrices — and the observational marginal of `C_1`, but not the
individual factors nor anything upstream of `C_j`"*. It carries no chamber
restriction, no informativeness proviso, and no hypothesis beyond the question's
own setup; the question's quantifier is *"for almost every theta"*. Had the
sentence been scoped to the straddling case, the finding would downgrade to "the
heuristic needs a chamber caveat".

**The positive-measure step is now in the Lean, as an explicit box.**
`o31_endpointMarginal_not_identified` states one concrete pair on rational
literals; its type contains no open set, no neighbourhood and no measure, so on
its own it does not reach the printed *"for almost every theta"*, which forgives
a null set. `o31_endpointMarginal_not_identified_onBox` closes that gap. It
quantifies over three free coordinates `(r, theta_0, theta_1)` constrained by
`O31Box` -- `r` in `(3/10, 1/2)`, the `0`-column in `(3/20, 1/4)`, the `1`-column
in `(13/20, 3/4)` -- and reproves every clause there: both models margin-valid at
`1/10`, the transfer map shared, an optimal policy shared under every real
mixture, and the endpoint marginals apart, the gap being
`(r - 1/10)(theta_1 - theta_0)` with both factors strictly positive on the box.
`o31_endpointMarginal_not_identified_kernel_onBox` additionally proves at every
box point that both embedded models inhabit the printed `MarginClass` for the
legal utility gap `(-4/5, 1/5)` and that the restricted behavior is the
causal-kernel computation.

The measure step is proved, not asserted. `o31BoxSet` is `O31Box` read as a
subset of `R^3`, `o31BoxSet_eq` identifies it with a product of three open
intervals, and `o31BoxSet_volume` computes its Lebesgue measure exactly as
`1/500`; `o31_endpointMarginal_not_identified_positiveMeasure` states that
measure claim and the behavioural conclusion together, so the inference from
"open box" to "not a null set" is carried by the kernel rather than left to a
reader. The earlier literal witness sits strictly inside the box
(`o31Witness_mem_box`) and the box model at that point is definitionally the
witness (`o31BoxModel_witness`), so the concrete pair is one member rather than a
separate example. The continuity argument that had stood in for this is
retired: nothing here now rests on an unformalized topological step.

The other coordinates remain one instance -- two nodes, root intervened,
same-side chamber -- and the parametrization does not touch them.

**What the heuristic is not.** `q:chain` asks which of the `2(m-1)+1` *table
parameters* are identifiable. The observational marginal of `C_1` is not one of
them — the count is one root probability plus two CPT entries for each of the
`m-1` non-root nodes — so the counterexample bears on the heuristic sentence and
not on the question's own target set. The distinction is why the row is not
graded as a resolution of `q:chain`.

**Consistency with the candidate on the tracker.** MAIS issue [#8](https://github.com/lionellevine/MAIS/issues/8) claims, for the
same-sign chamber, that *"no table coordinate is identified"*. The counterexample
lies in that chamber and is consistent with it; the marginal of `C_1` is outside the
scope of that claim, being a derived functional rather than a coordinate. The
general theorem `o31_sameSide_root_not_identified` confirms the root-coordinate
part of [#8](https://github.com/lionellevine/MAIS/issues/8)'s same-side prediction for two-node chains with the root intervened;
the two transition coordinates remain open. The box result adds a derived
quantity [#8](https://github.com/lionellevine/MAIS/issues/8) does not address and contradicts nothing in [#8](https://github.com/lionellevine/MAIS/issues/8).

**The induced thresholds are contained in a proper subinterval of the open unit
interval.** Issue [#8](https://github.com/lionellevine/MAIS/issues/8)'s setup says *"let `t` in `(0,1)` be the utility decision
threshold"*. Under (M2) — `|g(z)| >= lambda` — and (M3) — `g` takes both signs,
the observation set being empty — together with the `u` mapping into `[0,1]` of
`def:cid`, the induced threshold satisfies
`lambda/(1+lambda) <= t <= 1/(1+lambda)`. Both halves are proved as of
2026-08-22: `AISafetyAtlas.Conjectures.MAIS.o31Threshold_ge` and
`o31Threshold_le`, combined in `o31Threshold_mem_marginInterval`. The upper half
had previously been asserted in that theorem's own docstring by appeal to
symmetry, without a proof, and is now carried by one. At `lambda = 1/10` the
containing interval is `[1/11, 10/11]`, properly inside `(0,1)`. The witness uses
gap pair `(-4/5, 1/5)` and threshold `4/5`, which lies in that interval.
**Containment is not realizability:** no converse is proved, so nothing here
claims every point of the interval is attained by some margin-admissible
utility. CONJ-010 itself quantifies over every `t ∈ (0,1)`; these derived bounds
describe witness construction and do not restrict its statement.
