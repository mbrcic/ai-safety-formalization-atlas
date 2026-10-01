# CIDs and Ring–Orseau: verified unblocking handoff

Reviewed 2026-09-14, starting from a clean worktree. This pass
supplies proof infrastructure for finishing agents; it does not change scope or
coverage grades. “Unblocked” below applies to the named technical step, never to
an entire paper or theorem.

## What the intervening model finished

An earlier commit integrated ProgramPrior and ValueBounds, their examples, imports,
registry coverage, generated views and six audit regrades. The program mass,
normalization, point-prior/observation bridge, finite-value bounds, ordinary
infinite-value limit and Bellman equation are already there. Do not rebuild them.
The literal two knowledge horizons and mortality goal horizon are already there.

The commit's grades are not independently endorsed by this handoff. In
particular, absolute horizon summability, a total abstract interpreter, and an
attained supremum are distinct obligations. A bounded supremum does not provide
an action realizing it.

## Three technical steps now unblocked

### 1. Delusion Statements 1–3: posterior expectation at every finite depth

In [ProgramPrior.lean](../../AISafetyAtlas/Wireheading/ProgramPrior.lean),
`Model.expectation_eq_programSum` proves, for any uniformly bounded continuation
`f`, that its observation expectation equals

`(Σ_q 1[Consistent q h] weight(q) f(run q h a)) / mass(h)`.

`Model.actionValue_eq_programSum` specializes this to the actual recursive
continuation at **every finite depth**. No finite code or observation alphabet,
no positive-mass premise, and no assumed `MixesAt` are required. The proof checks
absolute summability before interchanging the two sums. At an impossible
history the quotient uses the existing zero convention.

Finishing route: partition consistent programs into box/no-box classes and bound
the same continuation on each class. Use those bounds in the already proved
threshold arithmetic. Do not substitute the component models' separately
optimized continuations: maxima do not generally commute with mixing. This
bridge removes that decomposition obstacle, but does **not** establish the
four payoff bounds, the posterior threshold, or their persistence over time.
Those remain substantive source-specific work, not an automatic regrade.

Witness: `Examples.Wireheading.ProgramPrior.posterior_true` computes a posterior
after an observation eliminates one of two programs; it is not an empty-history
or zero-prior witness.

### 2. CIDs: independent exogenous law beyond finite vertex sets

In [StructuralModel.lean](../../AISafetyAtlas/Causal/StructuralModel.lean),
`SCM.exoPMF` converts the existing marginals, and `SCM.exoLaw` constructs their
independent product as a **probability measure** over arbitrary vertex sets.
`exoLaw_map_eval` recovers each marginal. `exoLaw_eq_pi` recovers the finite
product; `exoLaw_singleton` recovers exactly `ENNReal.ofReal (exoJoint ε)`.
This is connected to the existing data, not a parallel model with unrelated
probabilities.

`SCM.observableLaw` pushes this product through evaluation on an arbitrary set
of vertices. Its measurability argument is mandatory and its result is a
probability measure, so a nonmeasurable map cannot silently yield a zero law.
`SCIM.observableLaw_withPolicy_eq_of_notDownstream` proves policy invariance of
these laws without `Fintype V` or a finite observation set.

Finishing route: express event probabilities and integrable utility expectations
against this law, and recover the old finite sums using `exoLaw_singleton`.
Condition on a measurable positive-probability context for the incentive rows.
For infinite utility families, specify and justify their summation/integrability
separately. The existing expected utility and conditional expectation functions
still use finite sums: their narrowing has **not** disappeared.

Witness: `Examples.Causal.StructuralModel.independentBits` has vertex type `ℕ`;
`independentBits_first_zero` verifies a nontrivial cylinder probability of 1/2.

### 3. Mortality equation (4): convergence through changing code

In [SelfMod.lean](../../AISafetyAtlas/Wireheading/SelfMod.lean),
`abs_smValue_le_horizonBudget` and `abs_smValue_succ_sub_le` control the recursion
that executes the current code and continues at the returned next code.
`smInfiniteValue`, `tendsto_smValue_smInfiniteValue` and
`smValue_error_le_tail` provide its limit and a uniform truncation certificate.
They require subprobability observations, utility bounded in absolute value by
one, and an absolutely summable horizon. No finite or nonempty action/code type
is assumed; the executor supplies the actions it actually uses.

Finishing route: pass the recursive equation through the limit using the uniform
tail estimate, then define the compound-action selector under attainment. This
is distinct from proving an initial program in the chosen language implements
that selector. Do not assume every abstract policy has a bounded-length code.
The author version p.5 explicitly allows the executor to be an oracle performing
infinite computation instantly: ordinary computability is not the right
requirement for this executor.

A further source bridge is required before equation (4) can be called faithful:
p.5 prints the belief at `h a`, extends the history by `(a,o)`, and executes
`c(h a o)`. The present recursion stores compound actions `(a,c)` in history.
For the section-3 model, erase code components before calling the environment
belief and source utility, and prove recovery under that projection. Otherwise
the environment can read code prematurely, a capability introduced only in
section 4. The new convergence theorem remains valid, but does not supply this
projection bridge.

Witness: `Examples.Wireheading.SelfMod.smInfiniteValue_stays` recovers the
previously computed finite-window value 2 for the survival agent.

## Remaining blockers, by family

| Target | What still needs mathematical work |
|---|---|
| §8 Definitions 1–2: arbitrary domains | Replace `Fin`-valued domain families with arbitrary types and recover the finite representation. The new law layer deliberately retains the existing domains. |
| §8 expectation/incentive scope | Integrals, measurable evaluation, conditioning, summable utility families, and finite recovery at the consumers; product-measure existence itself is now available. |
| §8 Definition 6 / downstream graph criteria | **Discharged 2026-09-20.** `CID.dSepSet_iff_dSepPath` is the active-walk-to-active-path equivalence, endpoints and collider activation preserved, proved here because the pinned Causalean DSep files contain no `Nodup` result. The warning in this row was right: deleting a loop does change collider status at the join, and that is the one case the proof spends work on — `CID.not_activated_of_mem_parents` and `forward_of_not_activated` are what close it. The downstream graphical criteria are still absent, for the reason in the row below. |
| §8 missing VoI/response/control results | Definitions 8, 10–11, 13, 15 and Theorems 9, 12, 14, 16 remain absent in the audit. Building a measure does not prove their graphical completeness constructions. |
| §11 Statements 1–3 | Concrete program classes, policy-compatible payoff bounds and posterior thresholds; use the posterior formula above. |
| §11 Statement 4 | A temporal meaning of “not consistently”, then a proof for the prior-tied utility and the true-program value belief. Relative prior weight monotonicity alone is not that conclusion. |
| §13 program class / `A_sm` | Concrete bounded-length codes and execution semantics. `Model.run` is total and abstract; it is not a universal machine or a treatment of nontermination. |
| §13 equation (4) | Infinite recursion equation, compound-action attainment, and realization of the initial maximizing program are separate steps. Only convergence/error control is supplied here. |
| §13 asymptotic optimality | Specify the printed mistake criterion and prove it for the relevant agent/environment class. Point-prior equivalence only identifies the comparator. |
| §13 goal horizon / signed horizons | Constant-one goal convergence needs the at-most-once property; absolute summability does not cover it. A conditionally convergent signed horizon is also not covered by the new limits. |
| §11 fully modifiable agents / §13 Simpleton Gambit and remaining Statements | Still absent or partial as recorded in the audit; do not infer these from the new executor limit. |

## Source and reuse evidence

The source files in the private literature store were reconfirmed by
SHA-256, not filename alone:

- Mortality author version: `e211682aa5cc9e1bcd7f0a277030a4a909ff52695ff4e1d0fa3905d9b223b52d`.
- Delusion HAL version: `a207ab73c87896e0663e4998906aa4c4bcef6d93a43d8e29ebc3cdb81e32ea6d`.
- Everitt et al. AAAI: `31d4a4b277c562b82000c4d2b81660e89464877ec0cad3549a9375c6d4492598`.

Rendered source checks: CIDs printed p.11489 explicitly imposes finite **domains**
at Definition 4 and states policy invariance; mortality author p.4 prints the
constant-one goal horizon, `k+t=m`, and replacement of the prior in value
but not utility. Mortality p.5 supplies the oracle executor and the code-blind
`h a o` continuation; delusion printed p.3 confirms its distinct goal horizon
and the prior replacement only in the value equation. These are not readings
inferred from extracted equations.

Reuse: pinned Mathlib `Probability/ProductMeasure.lean` supplies `infinitePi`,
its coordinate law and `infinitePi_eq_pi`; PMF supplies marginal normalization
and conversion to measures. The program proof reuses `Summable.tsum_comm` and
the existing program partition. The executor limit reuses Mathlib's Cauchy and
tail-distance theorems and the atlas's subprobability expectation bound. No
claim of absence from the wider Lean ecosystem is made.

## Trust and grading boundary

No `sorry`, custom axiom, or unproved-dependency field was added. The new
hypotheses are visible in theorem signatures. Source-realization, measurability,
attainment, and temporal conclusions listed above remain obligations; they are
not smuggled in as established lemmas. Audit grades and totals are left for a
finisher to reassess against the entire cited API after the consumer bridges land.

## Verification

Full `lake build` and all explicit build targets passed. The full repository
gate passed after regenerating its navigation files. Both axiom audits passed:
5,730 declarations in the text-driven audit and 16,096 in the independent module
sweep, using only `propext`, `Classical.choice`, and `Quot.sound`. The coverage
check also passed, with all declarations in its stated scope collected.
