# Statement maps: A1-A3, B1-B3, B7

Date: 2026-07-29, revised after the Phase 1 to Phase 3 packages landed. One table per item, mapping source notation to Lean
declarations, with the divergence recorded next to each row.

These maps are a precondition for any relationship-grade upgrade. Everything
below is currently graded `RELATED`; nothing here proposes a change. Source
evidence and the BY-039 retraction are in
[`a1-a3-b1-b3-source-audit.md`](a1-a3-b1-b3-source-audit.md).

Reading the divergence column: **abstraction** means the Lean statement drops
structure the source carries; **generalization** means it assumes strictly less;
**reparameterization** means the hypotheses are recombined and a constant
changes; **specialization** means a source parameter is fixed.

---

## A1 hyperproperties

Clarkson and Schneider, *Hyperproperties*, JCS 18(6), 2010.
Alpern and Schneider, *Defining liveness*, IPL 21(4), 1985.

| Source | Lean | Divergence |
|---|---|---|
| system, a set of traces | `TraceSystem Trace` | none |
| hyperproperty, a set of systems | `Hyperproperty Trace` | none |
| finite observation | `Observation Prefix = Finset Prefix` | none |
| `M ≤ T`, T realizes observation M | `Realizes prefixOf M S` | observation relation is a parameter, not a fixed prefix order |
| bad observation | `IsBadObservation prefixOf H M` | none |
| k-safety | `IsKSafety prefixOf k H` | none |
| Theorem 2, reduction to safety of `S^k` | `k_safety_iff_product_self_composition` | source-shaped satisfaction equivalence over ordered `Fin k` tuples. Carries a nonempty-system hypothesis, which `productSelfComposition_empty` and `finiteSelfComposition_empty` show is necessary for `k > 0` |
| Theorem 2, batch form | `k_safety_iff_finite_self_composition` | **abstraction**: unordered batches. `toBatch`, `padBatch`, `toBatch_padBatch`, `card_toBatch_le`, `toBatch_perm` translate; `selfCompositionSafe_empty_of_any` handles the empty batch |
| induced safety property on `S^k` | `self_composition_is_safety` | **representation cut**: proves finite-observation safety for the unordered batch predicate; the product theorem transports satisfaction, but no separate ordinary-safety predicate over a product trace alphabet is defined |
| hypersafety | `IsHyperSafetyOp prefixOf H` | none; stated without reference to a topology |
| hyperliveness | `IsHyperLivenessOp prefixOf H` | **generalization**: carries an explicit realizability side condition, since a cone over an unrealizable observation is empty |
| topology on systems | `prefixTopology prefixOf` | a `def`, never an `instance`: a global instance cannot mention `prefixOf` and would forget the observation semantics |
| hypersafety = closed | `isClosed_iff_hyperSafety` | none |
| hyperliveness = dense | `dense_iff_hyperLiveness` | none |
| k-safety ⊆ hypersafety | `hyperSafety_of_isKSafety` | none |
| every hyperproperty = hypersafety ∩ hyperliveness | `hyperSafety_hyperLiveness_decomposition` | none |
| — | `topological_decomposition`, `hypersafety_hyperliveness_decomposition` | general topology, retained in the parent module; **not** the operational claim |

Upstream Rocq artifact `secure-compilation/exploring-robust-property-preservation`
at `c68187c`: reproduction **FAILED** under two pinned images. Not upgraded.

---

## A2 rectangularity

Kushilevitz and Nisan, *Communication Complexity*, 1997.
Fagin, *Multivalued Dependencies and a New Normal Form*, ACM TODS 2(3), 1977.

| Source | Lean | Divergence |
|---|---|---|
| combinatorial rectangle | `IsRectangle R` | none |
| mix-and-match closure | `ExchangeClosed R` | none |
| rectangle iff mix-and-match | `rectangle_iff_exchange_closed` | none |
| lossless join, empty determinant | same theorem | **specialization**: only the binary Cartesian case |
| unary contracts, indexed | `IsCoordinateProduct P` | none |
| local splice closure | `SpliceClosed`, `coordinate_product_iff_spliceClosed` | **specialization**: finite index, nonempty `P`; necessity machine-checked |
| — | `RecombinationClosed P`, `coordinate_product_iff_recombination_closed` | near-definitional helper; one inclusion is free, so it reduces to unfolding `Set.pi`. Demoted, not a headline |
| finiteness is necessary | `spliceClosed_finitelySupported`, `coordinateProjection_finitelySupported`, `not_isCoordinateProduct_finitelySupported` | machine-checked counterexample, previously prose only |
| binary case is two-coordinate splicing | `ExchangeClosed.exchange_fst` | lemma-level bridge, not a transport along a product-to-pi equivalence |

---

## A3 Angluin symmetry

Angluin, *Local and Global Properties in Networks of Processors*, STOC 1980.

| Source | Lean | Divergence |
|---|---|---|
| anonymous network, identical processors, no identifiers | `Protocol.symmetric_observation` | **abstraction**: the *consequence*, observational indistinguishability in a symmetric configuration, is a structure field. Absent identifiers and shared code are separate ingredients and are not modelled |
| configuration | `Node → State` | none |
| symmetric configuration | `IsSymmetric` | none |
| synchronous round | `Protocol.step` | none |
| execution | `Protocol.run` | none |
| symmetry is preserved | `step_preserves_symmetry`, `run_preserves_symmetry` | none |
| no unique leader | `symmetric_no_unique_leader`, `no_unique_leader_from_symmetric_start` | none |
| port-labelled network, identical processors | `Networks.Network`, `Networks.Algorithm` | **specialization**: no identifiers and one shared algorithm, but routing reuses the same port index at both endpoints; no reverse-port involution |
| depth-`n` views | `Networks.SameView` | **abstraction**: equality of endpoint labels along common port words, rather than Angluin's full rooted port-labelled view tree with reciprocal incidence data |
| equal views give equal states | `Networks.runFor_eq_of_view_eq` | the Angluin lemma, derived rather than assumed |
| network automorphism | `Networks.Automorphism` | none |
| no unique leader from a nontrivial automorphism | `Networks.no_unique_leader_of_fixedPointFree` | none |
| coverings, universal cover | — | **not formalized** |
| randomized symmetry breaking (Itai-Rodeh) | — | **not formalized**; no randomness in the model |

BY-043 is a survey-original result. This is an upstream dependency for it, not
coverage of it. Registry note says so; `original_source_refs` now cites
`brcic-yampolskiy-2023`.

---

## B1 objective factorization

Ring and Orseau, *Delusion, Survival, and Intelligent Agents*, AGI 2011, §2.

The paper frames its results as statements and arguments and supplies **no
numbered theorem** for this content, so nothing here reproduces a source result.

| Source | Lean | Divergence |
|---|---|---|
| utility `u : H → [0,1]`, horizon `w` | `Objective.utility`, `Objective.horizon` | **generalization**: Lean utility is real-valued without the source range invariant |
| value from `(u, w)` under fixed dynamics | `Objective.value` | **specialization**: finite horizon, explicit `Finset.range` sum |
| the four agents differ only in `(u, w)` | `value_congr`, `optimal_decisions_congr` | record congruence only; proofs never unfold `value`. Renamed from `objective_factorization` / `optimal_decisions_eq`, which overstated them |
| — | `value_eq_of_agree_on_window` | new: value on a window depends only on weights and utilities inside it. Hypotheses indexed by `i < duration`, so objectives may diverge outside |
| — | `value_scaleUtility` | new: homogeneity in utility |
| — | `optimal_decisions_eq_of_pos_scaleUtility` | new: optimal decisions invariant under strictly positive rescaling |
| equations (1), (2), (3) | `AgentEquations.bestAction_max`, `AgentEquations.actionValue`, `AgentEquations.value_succ` | **specialization**: depth-truncated, since the source equations have no base case |
| truncation error | `AgentEquations.truncation_exact`, `value_eq_zero_of_horizon_vanishes` | explicit: exact once the horizon vanishes past the window |
| factorization using the recursion | `AgentEquations.value_eq_of_agree_on_window` | none |
| `ρ` a universal prior | `AgentEquations.Belief.cond` | **generalization**: an arbitrary real weight, unnormalized; sums are `Finset` sums, not expectations |
| AIXI, Solomonoff induction, delusion box, Statements 1-7 | — | **not formalized**; the source states them as arguments, not theorems |

---

## B2 goal preservation

Everitt, Filan, Daswani and Hutter, *Self-Modification of Policy and Utility
Function in Rational Agents*. Canonical text is the **published** chapter, AGI
2016, LNCS 9782, pp. 1–11; the extended `arXiv:1605.03142` is support only.

### Two numberings, and where the proofs are

The published chapter states its theorems and **proves none of them** —
*"Proofs for all theorems are provided in a technical report"*, namely
`arXiv:1605.03142`. So the published text is canonical for **statements** and the
technical report is the only place any **proof** exists. This is the atlas's one
source where those two authorities come apart, and both are needed.

| published (AGI 2016) | technical report (arXiv:1605.03142) |
|---|---|
| Definitions 1, 3, 7, 8, 9 | Definitions 3, 5, 10, 11, 12 |
| Theorem 10, hedonistic agents self-modify | Theorem 14 |
| Theorem 11, ignorant agents may self-modify | Theorem 15 |
| **Theorem 12**, realistic policy-modifying agents make safe modifications | **Theorem 16** |
| — | Lemma 13, Definition 18, Lemma 19, **Theorem 20**, Theorem 21 |

The atlas's target is **published Theorem 12**, whose statement is word-for-word
the report's Theorem 16. The last row is **proof apparatus the published chapter
does not print**, not material it dropped: Theorem 20 (optimal policy existence)
lives in the report's Appendix A, and the proof of Theorem 12 opens by invoking
it — *"By Theorem 20 in Appendix A, there is a non-modifying
modification-independent optimal policy `π′`"* — to make
`Q^re_t(æ_<t π(æ_<t))` modification-independent for optimal `π`. `initial_dominates`
assumes that consequence, so the gap recorded below is real against the only
proof there is.

| Source | Lean | Divergence |
|---|---|---|
| policy names `P`, policies `Π`, naming map `ι : P → Π` | `PolicyName`, `Model.act` | **abstraction**: names and policies are not separated |
| self-modifying action | `act p h = (w, p')` | none |
| realistic value function | `Model.continuation`, `Model.coherent` | none |
| modification-independent belief and utility | — | assumed away by determinism |
| naming map `ι`, full-support percept distribution | `GoalPreservationSource.Model.initial`, `initial_dominates`, `prob_sum_one`, `prob_pos` | **no-surjectivity specialization**: the proof compares only against the initial policy, which is named; `prob` is a normalized finite full-support distribution; domination is assumed rather than derived |
| Theorem 12 induction step (ext. Theorem 16) | `GoalPreservationSource.Model.selected_matches_initial`, `safe_modification`, `qValue_selected_eq_initial` | **specialization**: one-step only, finitely many percepts, discrete expectations rather than integrals |
| optimal-policy existence, modification-independence | — | **not reproduced**; `initial_dominates` assumes its consequence instead. This is the technical report's Appendix-A Theorem 20, which the source's own proof of Theorem 12 invokes as its first step, so this is a real gap against that proof |
| deterministic variant | `GoalPreservation.Model`, `names_surjective` | **stronger than the source**; retained as the simpler model, superseded by the above |
| discount | `discount`, `discount_pos` | **generalization**: only positivity, not `< 1` |
| Theorem 12, on-policy preservation (ext. Theorem 16) | `next_policy_optimal` (substance), `run_optimal` (induction), `goal_preservation` (corollary) | **specialization**: deterministic, finite-step, on-policy only |
| off-policy preservation | — | **not claimed** |

---

## B3 corrupted reward

Everitt, Krakovna, Orseau, Hutter and Legg, IJCAI 2017 / arXiv:1705.08417,
Theorem 11.

| Source | Lean | Divergence |
|---|---|---|
| CRMDP `⟨S, A, R, T, Ṙ, C⟩` and complete hypothesis class | `CRMDP.Model`, `CRMDP.Env` | **specialization/abstraction**: `T` is a deterministic function fixed for one `Model`, whereas the source class may range over transition kernels |
| true reward `Ṙ : S → Ṙ` | `Env.trueReward` | **generalization**: the whole continuous interval `[0,1]`, not a finite uniform grid |
| corruption `C : S × Ṙ → R̂` | `Env.corruption` | **specialization/generalization**: domain and codomain are the same continuous unit interval; no separate finite `Ṙ` / `R̂` grids |
| observed reward `R̂(s) = C_s(Ṙ(s))` | `Env.observed` | none |
| classes contain all `Ṙ` and `C` | `Env` is the full product | structural, so complement closure needs no side condition |
| complement `μ⁻` | `Env.complement` | none |
| `μ` and `μ⁻` induce the same `R̂` | `Env.observed_complement` | **proved**, previously absent |
| same measure over histories | `run_complement`, `history_complement` | **abstraction**: equality of deterministic action-and-observation histories, not equality of measures |
| policy `π : S × R̂ × (A × S × R̂)* → A` | `CRMDP.Policy` | none |
| `G_t(μ, π, s₀)` | `returnOver` | **specialization**: finite horizon |
| equation (3), returns sum to `t` | `return_add_complement` | none |
| `M_µ`, `m_µ`, equation (4) | — | not needed; the Lean proof pairs the witnessing environment with its complement instead |
| Theorem 11 | `CRMDP.Model.everitt_theorem_eleven` | canonical declaration |
| policy reads observed history | `CRMDP.Policy`, `run_complement` | indistinguishability is substantive, not vacuous |
| — | `Corruption.ComplementedClass.everitt_theorem_eleven` | algebraic core, retained as the lemma the model instantiates |
| extrema attained by finiteness | `bestPolicy`, `worstEnvironment`, `worstPolicy` fields | **not derived**; supplied as hypotheses |
| nonzero applicability | `Examples.SixTargets.nonzeroCRMDPModel_worstCaseRegret` | concrete two-state/two-action model has worst-case regret exactly `1`; this is an applicability witness, not the source's general finiteness derivation |
| decoupled feedback, learnability results | — | **not formalized** |

---

## B7 preference deduction

Armstrong and Mindermann, NeurIPS 2018.

| Source | Lean | Divergence |
|---|---|---|
| planner `p : R → Π` | `Planner` | **generalization**: arbitrary behaviour and reward types |
| rewards `R : S × A → [-1,1]` | `RewardFn S A` | **generalization**: Lean rewards are real-valued without the source range invariant |
| compatibility | `Explains`, `ReasonableLanguage.Compatible`, `Source.ReasonableForF.Compatible` | none; `compatible_iff` records the two agree |
| Theorem 1, both directions | `exists_planner`, `exists_reward` | none |
| Definition 5, `-p(R) = p(-R)` | `negPlanner` | **specialization**: state/action rewards and policies |
| Lemma 6, three degenerate pairs compatible | `lemma_six` | **specialization**: finite nonempty action type, needed by the greedy construction |
| basic operations `f₁…f₆` | `op1`…`op6` | none |
| composites `F₁…F₄` | `Source.F₁`…`Source.F₄`, `Source.Fmap` | none |
| `F`-complexity ≤ c, c-reasonable for `F` | `Source.ReasonableForF` | none; indexed by `Fin 4`, no policy complexity, which is why the constant does not double |
| amongst the lowest in `S`, via `min` | `Source.AmongLowestCompatible` | **generalization**: universal over compatible pairs, no attained minimum assumed |
| Proposition 7 | `Source.ReasonableForF.proposition_seven` | distance **`c`**, matching the source |
| Proposition 7 | `ReasonableLanguage.proposition_seven` | **reparameterization**: separate evaluation and construction bounds give `2 * c`. Retained because `Preference.Complexity` instantiates its evaluation bound concretely |
| Proposition 8 | `Source.ReasonableForF.proposition_eight`, `ReasonableLanguage.proposition_eight` | both directions, at `c` |
| §5.1 complexity argument | `explanation_complexity_eq_behaviour` | **abstraction**: quantifies over manufactured strings `encodeExplanation r b`, not arbitrary compatible pairs |
| §4.1.2 half-maximal regret | `RegretModel.cannot_rule_out_half_maximal_regret`, `CRMDP.Model.cannot_rule_out_half_maximal_regret` | the imported bound is a separate `HalfMaximalRegretBound` certificate, discharged from the CRMDP construction, not a field |
| equation (1), regret baseline | `OverrideModel.optValue_isGreatest` | none; the maximum is over agent actions |
| Definition 11, overriding | `OverrideModel.OverridesFor` | relativised to a compatible pair, as in the source; threshold made explicit |
| Definition 11, unrelativised shadow | `OverrideModel.Overrides` | **abstraction**; `overrides_of_overridesFor` relates them |
| equation (2), rationalising-action mixture value | `OverrideModel.mixtureValue`, `mixtureValue_rationalise` | source-shaped: the action is fixed to `rationalise Ragent`, which justifies the `ε V*_{Ragent}` term |
| action `0` / no-op comparison | `OverrideModel.noopValue`, `noopValue_lt_mixtureValue_rationalise` | no-op is evaluated separately; it is not given the optimal-value term from equation (2) |
| "very plausible" that the value can go higher | — | **not formalized**; a non-theorem in the source |
| Propositions 3 and 4 | — | explicitly semi-formal in the source; rigorous counterparts are Propositions 7 and 8 |
| Conjecture 9 | `Source.ReasonableForF.NotAmongLowestCompatible` | a **predicate only**, never assumed. `notAmongLowest_iff` shows it negates `AmongLowestCompatible` |
| informal Theorem 2 | `Source.ReasonableForF.theorem_two_conditional` | **conditional** on the predicate: each degenerate pair is then strictly simpler than the intended one |
| Proposition 10, Appendix A | — | needs resource-bounded complexity (`Kt`, `KT`); blocked upstream |

Existence of a *nontrivial* `c`-reasonable language is the source's informal
claim and is **not** established. The only exhibited inhabitants,
`degenerateLanguage` and `degenerateForF`, have every complexity zero, so the
propositions hold there but say nothing.

---

## Verification

```console
lake build
xargs lake build < scripts/lean_build_targets.txt
python3 scripts/check_print_axioms.py
./scripts/agent_gate.sh
```
