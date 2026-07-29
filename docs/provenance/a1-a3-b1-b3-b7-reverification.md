# A1–A3, B1–B3, and B7 re-verification

Date: 2026-07-29. This is the durable residual-gap record for the
compositional, wireheading, and preference-deduction increment. It consolidates
the useful conclusions from adversarial working reviews; untracked files under
`reviews/` are not part of the repository evidence chain.

This record does not change any `relationship` or `ai_bridge_status`.

## Verification verdict

The increment is kernel-complete within its encoded statements: it builds
without `sorry`, and its public declarations pass the axiom audit. It is not
paper-complete. All affected survey formalizations remain `RELATED`, and the
landscape entries retain their explicit representation limits.

Detailed source-to-Lean correspondences:

- [statement maps](a1-a3-b1-b3-b7-statement-maps.md)
- [primary-source audit and BY-039 retraction](a1-a3-b1-b3-source-audit.md)

## Current status

| Item | Established | Residual paper gap |
|---|---|---|
| A1 hyperproperties | Batch and synchronized-product k-safety reductions; operational prefix topology; k-safety implies hypersafety; safety/liveness decomposition | Product theorem uses a nonempty-system boundary; no complete Rocq reproduction |
| A2 rectangularity | Binary exchange characterization; finite indexed splice characterization; infinite-index counterexample | No named downstream protocol consumer |
| A3 symmetry | Explicit networks, views, automorphisms, round induction, and fixed-point-free leader obstruction | Simplified port routing; no full covering theory or randomized symmetry breaking; not BY-043 |
| B1 objectives | Finite objective locality, scaling, recursive displayed-equation package, and truncation boundary | Real-valued rather than `[0,1]`-valued utility; no AIXI, delusion-box model, or four concrete source agents |
| B2 goal preservation | Finite-percept one-step Theorem 16 argument without naming surjectivity, using a normalized full-support percept distribution | `initial_dominates` / continuation structure assumed; Theorem 20 and modification independence not derived; names and policies not separated; no all-times source theorem |
| B3 reward corruption | Deterministic fixed-transition CRMDP on bounded rewards, action-and-observation histories, observed-channel complement, identical runs, complementary returns, and half-regret theorem | One fixed deterministic transition rather than a class ranging over stochastic kernels; extrema supplied as fields; continuous interval rather than finite uniform reward grid |
| B7 preference deduction | Theorem 1, Definition 5, Lemma 6, source-parameterized Propositions 7–8, conditional Theorem 2 predicate, relativized Definition 11 | Real-valued rather than `[-1,1]`-valued rewards; Conjecture 9 is not proved; Proposition 10 is absent; no nontrivial reasonable-language witness |

## Corrections made by re-verification

### Public facade contract

Every declaration listed in the Compositional, Wireheading, and Preference
primary-surface tables is checked from the root import by
`AISafetyAtlas.Examples.PublicAPI`. Hyperproperty entries use their real
`Compositional.Hyperproperties` namespace.

### B2 scope

`GoalPreservationSource` is a **finite-percept induction step**, not a
source-strength reproduction of Theorem 16. It removes the atlas's earlier
surjectivity premise from the one-step argument, but assumes the domination
property that the paper obtains from deeper modification-independence results.

`AISafetyAtlas.Examples.SixTargets.finitePerceptGoalModel` supplies a concrete
model with two percepts, actions, histories, and policy names, a normalized
uniform full-support percept distribution, and a genuinely dominated
alternative continuation.

### B3 boundedness and nonzero applicability

The first CRMDP interface used unrestricted real-valued true rewards while also
requiring an attained worst environment. Those choices interact badly: scaling
any positive-regret environment preserves its observable histories after
precomposing the corruption channel with inverse scaling, but makes regret
arbitrarily large. Consequently the old interface admitted only zero-regret
models. Merely documenting the missing reward grid was insufficient.

`CRMDP.Reward` now retains the source's load-bearing `[0,1]` bound while omitting
only finite uniform discretization. Policies now receive the source-shaped
initial observation followed by action/observation pairs.
`AISafetyAtlas.Examples.SixTargets.nonzeroCRMDPModel` supplies a two-state,
two-action, horizon-one model and
`nonzeroCRMDPModel_worstCaseRegret` proves that every policy's worst-case regret
is exactly `1`. Extrema remain structure fields in the general interface, so
this does not derive the paper's finiteness result.

### B7 equation (2)

`OverrideModel.mixtureValue` now denotes only the source action that
rationalises the human for `Ragent`. The no-op action has a separate
`noopValue`; it no longer receives an unjustified
`ε * optValue Ragent` contribution. The closing comparison is
`noopValue_lt_mixtureValue_rationalise`.

## Ordered remaining work

1. **B2 derivation depth:** separate policy names from policies and derive a
   reusable fragment of modification independence only if a named consumer
   needs the full trajectory theorem.
2. **B3 source depth:** add stochastic kernels and derive extrema from finite
   state/action/reward-grid assumptions as one coherent package.
3. **B7 research:** retain Conjecture 9 as a predicate; pursue Proposition 10
   only after resource-bounded complexity infrastructure exists; do not fake a
   nontrivial reasonable language by assuming its conclusion in structure
   fields.
4. **A3 source depth:** add inverse-port routing and covering-map machinery only
   for a concrete consumer such as a BY-043 bridge.
5. **B1 source agents:** package the four Ring–Orseau agents only when their
   differing utilities and horizons support a named theorem.

## Stop rules

- Do not count a `RELATED` entry as headline coverage.
- Do not count Conjecture 9 as covered because its predicate is defined.
- Do not call the B2 induction step the full or source-strength Theorem 16.
- Do not call the deterministic B3 model exact Theorem 11.
- Do not infer BY-043 from the A3 dependency alone.
- Do not rely on untracked `reviews/` files for shipped API or strategy claims.

## Verification

```console
./scripts/agent_gate.sh
python3 scripts/check_print_axioms.py
lake build
xargs lake build < scripts/lean_build_targets.txt
```
