module

public import AISafetyAtlas.Inference.Device
public import AISafetyAtlas.Inference.Complexity
public import AISafetyAtlas.Inference.Complexity.Measure
public import AISafetyAtlas.Inference.Complexity.Halting
public import AISafetyAtlas.Inference.Complexity.EntropyBound
public import AISafetyAtlas.Inference.Complexity.Inversion
public import AISafetyAtlas.Inference.Reality
public import AISafetyAtlas.Inference.Stochastic
public import AISafetyAtlas.Inference.Stochastic.Bridge
public import AISafetyAtlas.Inference.Stochastic.Interop
public import AISafetyAtlas.Inference.Existence
public import AISafetyAtlas.Inference.Stochastic.Bounds
public import AISafetyAtlas.Inference.Stochastic.Sharpness
public import AISafetyAtlas.Inference.Stochastic.Approximation
public import AISafetyAtlas.Inference.SelfAware
public import AISafetyAtlas.Inference.PhysicalKnowledge
public import AISafetyAtlas.Inference.PhysicalKnowledge.Epistemic
public import AISafetyAtlas.Inference.PhysicalKnowledge.Event

/-!
# Inference devices — public facade

What can a device inside a universe conclude about that universe? Wolpert's answer
is that observation, prediction and recollection share one structure — a setup
function and a conclusion function over a set of universes — and that structure
alone already forbids some conclusions, whatever the physical laws turn out to be.

This facade aggregates the 2008 development — the device core, inference
complexity, realities and copies, stochastic devices, and self-aware devices —
and the first source-faithful 2018 extension: physical knowledge by a selector
of setup blocks.

## How to read the status column

`SOURCE-EXACT` — the Lean statement is the printed statement up to notation.
`SPECIALIZED` — faithful on a declared narrower domain (finite `U`, counting
measure, finite index).
`REPAIRED` — the printed statement is defective; Lean proves the intended claim.
Every one has an entry in [`wolpert-2008-source-clashes.md`](../docs/provenance/wolpert-2008-source-clashes.md).
`ASSUMED-STEP` — a theorem about the source's objects, with one named step of the
source's proof taken as a hypothesis rather than proved.
`REFUTED` — machine-checked countermodel to the statement as written.

A declaration that is only a *component* of a printed statement is not listed as
that statement.

## Primary surface

| Source | Status | Declaration | One-line |
|---|---|---|---|
| **Def 1** | SOURCE-EXACT | `InferenceDevice` | A setup function and a conclusion function onto `Bool` |
| **Def 2** | SOURCE-EXACT | `IsSourceProbe` | Onto `𝔹`, true at exactly one argument, on a range with two points |
| Def 2 (working) | — | `IsProbe`, `weaklyInfers_iff_sourceProbes` | Unique-true only; agrees with Def 2 on every range the source admits |
| **Def 3** | SOURCE-EXACT | `WeaklyInfers`, `weaklyInfers_iff_imageProbes` | Per probe, some setup value on whose fibre the conclusion is right |
| **Def 4** | SOURCE-EXACT | `Distinguishable` | Every pair of realized setup values is jointly realizable |
| **Def 5** | SOURCE-EXACT | `StronglyInfers` | Can force the other's setup *and* report its conclusion |
| **Def 6** | SOURCE-EXACT | `inferenceComplexitySum`, `inferenceComplexityOn`, `inferenceComplexity` | Sum of minimal fibre-length costs over the source's **countable** setup and target ranges; `ℒ` is a parameter, and `C > Γ` is carried in the signature |
| **Def 7** | SOURCE-EXACT | `Mimics`, `Copies` | Identical realized `(X,Y)` relations, **across two universes** |
| **Def 8** | SOURCE-EXACT | `SemiControls`, `Controls` | Force any realized value; force the answer *and* the conclusion |
| **Def 9** | SOURCE-EXACT | `inferenceAccuracySupOn`, `inferenceAccuracyOn`, `inferenceAccuracy` | Covariance accuracy over an **arbitrary** `U`, an arbitrary setup range and the source's own finite target range; the printed `max_x` is a supremum over the positive-mass fibres, which is where it denotes |
| **Def 10** | SOURCE-EXACT | `miDistinguishabilitySum`, `miDistinguishabilityOn`, `miDistinguishability` | `1 − M/(H₁+H₂)` with the entropies as `∑'` over the value type, so no range restriction; finite entropy stays forced |
| **Def 11** | SPECIALIZED | `countingDistinguishability` | Fraction of jointly unrealized setup pairs |
| **Def 12** | SOURCE-EXACT | `SelfAwareDevice` | Self-aware devices; questions as a label type plus `eval`, not as a set of functions |
| **Def 13** | SOURCE-EXACT | `Intelligible`, `Infallible` | (i) intelligible, (ii) infallible |
| **Def 14** | SOURCE-EXACT | `Corrects` | `D₁` corrects `D₂` |
| **Prop 1(i)** | SOURCE-EXACT | `exists_weaklyInfers_family_of_two_values_on` | *One* device weakly infers every member of a family |
| **Prop 1(ii)** | SOURCE-EXACT | `exists_not_weaklyInfers` | Every device fails some binary question — its own conclusion |
| **Prop 2(i)** | SOURCE-EXACT | `exists_not_stronglyInfers` | Some device is beyond any given device's emulation |
| **Prop 2(ii)** | SOURCE-EXACT | `exists_stronglyInfers_of_large_fibres` | A strong inferrer exists when every fibre has three points |
| **Prop 3(i)** | SOURCE-EXACT | `exists_pairwise_distinguishable_weak_cycle` | A pairwise-distinguishable weak-inference 3-cycle exists |
| **Prop 3(ii)** | SOURCE-EXACT | `not_mutually_distinguishable_weak_cycle` | No weak cycle when the cycle devices are *mutually (setup) distinguishable* — the source's own prose definition; the finite family need not exhaust the reality |
| **Prop 3(iii)** | SOURCE-EXACT | `not_strong_inference_cycle` | No strong-inference cycle |
| **Prop 4** | SOURCE-EXACT | `unique_strong_root` | Unique root of a **finite** weakly-connected strong-inference graph, over the induced subgraph on `D` as the source's conclusion reads it |
| **Prop 5(i)** | SOURCE-EXACT | `exists_copies_distinguishable_weak` | Finite copies may be distinguishable with one-way weak inference |
| **Prop 5(ii)** | SOURCE-EXACT | `exists_copies_stronglyInfers_infinite`, `copies_stronglyInfers_not_finite` | Copies may strongly infer, but only with infinite setups |
| **Prop 6** | SOURCE-EXACT | `prop6_half_of_miDistinguishabilityOn_eq_one`, `mutualInfo_eq_zero_iff` | Proved from the printed premise, no assumed step: MI-distinguishability `1` gives independence by the equality case of Gibbs. The printed `X₁(U) = X₂(U) = 𝔹` is the source's own; measurability and the two side conditions are forced |
| **Prop 7** | REPAIRED | `exists_not_corrects` | Some self-aware device is uncorrectable; the printed witness fails Def 12 |
| **Thm 1** | SOURCE-EXACT | `not_infersDevice_both_of_distinguishable` | No two distinguishable devices weakly infer each other |
| **Thm 2(i)** | SOURCE-EXACT | `weaklyInfers_of_stronglyInfers` | Strong inference inherits everything weak inference gets |
| **Thm 2(ii)** | SOURCE-EXACT | `stronglyInfers_trans` | Strong inference is transitive |
| **Thm 2 (unnumbered)** | SOURCE-EXACT | `infersDevice_of_stronglyInfers` | Strong inference implies weak inference of the target device |
| **Thm 3** | SOURCE-EXACT | `not_stronglyInfers_both` | No two devices strongly infer each other |
| **Thm 4** | SOURCE-EXACT | `inferenceComplexityOn_le_of_stronglyInfers`, `inferenceComplexity_le_of_stronglyInfers` | Emulation bound on the complexity difference, derived from `C₁ ≫ C₂` and `C₂ > Γ` with no finiteness on either setup range; `Γ(U)` finite is printed. **One-sided in the source** — the bars in `|Γ(U)|` are a cardinality |
| **Thm 5** | SOURCE-EXACT | `setup_partition_eq_of_semiControls_setup` | Mutual semi-control makes the setup partitions identical |
| **Thm 6(i)** | SOURCE-EXACT | `weaklyInfers_of_infallible_semiControls_question` | Infallible + semi-control `Q` infers every intelligible target |
| **Thm 6(ii)** | SOURCE-EXACT | `stronglyInfers_of_infallible_semiControls_question_setup` | Plus semi-control of `(Q,X₂)`, surjective onto `Q₁(U) × X₂(U)` — the product of the two **images**, as printed |
| **Thm 7(i)** | SOURCE-EXACT | `thm7_mk`, `thm7_card` | Equal cardinalities. `thm7_mk` **drops** the finiteness the source's (i) never states, by Schröder–Bernstein; the residual restriction is Lean's, not the paper's — `Cardinal.mk` compares types in one universe, so the four share one, and both question types carry `DecidableEq`, which is classically free. `thm7_card` is the finite instance |
| **Thm 7(ii)** | SOURCE-EXACT | `thm7_ii_chain` | All four printed equalities `Q′ = π(P) = π(Q)`, `Q = π(P′) = π(Q′)`, with the cardinalities discharged from Theorem 7(i) |
| **Cor 1(i)** | SOURCE-EXACT | `exists_weaklyInfers_family_of_values_attained_on` | Values attained on `W` suffice for one device to infer the family |
| **Cor 1(ii)** | **REFUTED** | `Examples.…no_device_weaklyInfers_id_on_bool` | *"any `Γ` is inferred by some device"* is false without a proper `W` |
| **Cor 2** | SOURCE-EXACT | `weaklyInfers_iff_three_setups`, `not_weaklyInfers_of_at_most_two_setups` | With `X` fine-graining `Y`, inferrability iff three setup values. The `←` direction holds for **any** target range |
| **Cor 3(i)** | SOURCE-EXACT | `infersDevice_comm_of_semiControls_setup` | Mutual semi-control of setups makes weak inference symmetric |
| **Cor 3(ii)** | SOURCE-EXACT | `not_stronglyInfers_either_of_semiControls_setup` | Neither strongly infers the other (`¬A ∧ ¬B`, **not** Thm 3's `¬(A∧B)`) |
| **Cor 3(iii)** | SOURCE-EXACT | `not_controls_other_setup_of_semiControls_setup` | Neither then controls the other's setup |
| **Cor 4** | SOURCE-EXACT | `not_mutually_deviceIntelligible_of_finite` | No finite mutual device-intelligibility |
| **Cor 5** | REPAIRED | `not_both_concl_intelligible` | The printed *"if in addition they infer each other"* is vacuous under Thm 1; Lean drops it |
| **Lemma 1** | SOURCE-EXACT | `lemma1_reducedForm_iff_admissible` | `K₁ = K₂`: reduced forms of realities are exactly the admissible tuple families |

## The general-measure layer

`Inference/Stochastic/Measure.lean` and `Inference/Complexity/Measure.lean`
restate sections 5 and 8 over an arbitrary measurable space — no `Fintype U`,
finiteness only where the source puts it, on `X(U)` and `Γ(U)`.
`Inference/Stochastic/Bridge.lean` proves the finite layer is an instance, so a
`FinPMF` model **is** a measure-space model and no worked example is built twice.

These were reachable only through `scripts/lean_build_targets.txt` until now, and
so sat outside this facade's closure — which is what `check_print_axioms.py`
scans. Forty-two public theorems of the general layer had never been kernel
axiom-checked. They are in the closure now.

| Source | Declaration | One-line |
|---|---|---|
| **Def 6**, general `dμ` | `measureLength`, `inferenceComplexityMeasure` | `ℒ(x) = −ln μ(X⁻¹(x))`; the source's Example 6 is the counting case |
| **Thm 4**, general `dμ` | `inferenceComplexityMeasure_le_of_stronglyInfers` | An instantiation, not a second proof — Theorem 4 never unfolds a length |
| **Def 9–11**, general `dμ` | `inferenceAccuracyOn`, `miDistinguishabilityOn`, `countingDistinguishabilityOn` | Definition 9 needs no Bochner integral: `Y·f(Γ)` is `±1`-valued, so the expectation is a ratio of fibre masses |
| **Prop 6**, general `dμ` | `prop6_half_of_miDistinguishabilityOn_eq_one` | The printed premise, no assumed step |
| **Def 9's independence** | `independentOn_iff_indepFun`, `FinPMF.ofPMF`, `FinPMF.ofPMF_toMeasure` | The atlas predicate **is** Mathlib's `IndepFun` on finite-range maps, and a Mathlib `PMF` on a finite universe **is** a `FinPMF` inducing the same measure. A reader holding Mathlib's objects can discharge Proposition 6's hypothesis without restating anything |
| §8 prose, `C̄_ε(Γ∣C)` | `stochasticInferenceComplexity`, `stochasticInferenceComplexity_le`, `stochasticInferenceComplexity_eq` | The `ε = 1` remark in both directions; equality carries the source's second hypothesis as *no point is null* |

Supporting constructions and laws, not themselves numbered items: `probe`,
`exists_isProbe`, `separatingDevice`, `not_stronglyInfers_self`,
`weaklyInfers_of_controls`, `semiControls_of_controls`,
`semiControls_of_controls_classical`, `semiControls_setup_of_stronglyInfers`,
`not_controls_own_concl`, `not_controls_both_of_distinguishable`,
`Mimics.trans`, `Copies.symm`, `Copies.trans`.

## Wolpert 2018 extension

| Source | Declaration | One-line |
|---|---|---|
| Definition 11 | `PhysicalKnowledgeWitness`, `PhysicallyKnows` | A selector of realized setup blocks certifies knowledge of one realized target value over `W` |
| prose after Definition 11 | `PhysicallyKnows.weaklyInfers` | Physical knowledge entails weak inference |
| Lemma 17 | `PhysicalKnowledgeWitness.eq_target_of_mem_knownBlock`, `PhysicalKnowledgeWitness.eq_target_on_of_refinesOn` | The certified value is true on its selected block, and throughout a refining `W` |
| Proposition 18 | `physicallyKnows_false_iff_not_true` | Knowing a Boolean target is false is knowing its negation is true |
| Corollary 19 | `true_on_of_physicallyKnows_true`, `false_on_of_physicallyKnows_false`, `not_physicallyKnows_true_and_false` | Knowledge is truthful on a refining set, and cannot affirm both values |
| Corollary 22 | `exists_never_physicallyKnown` | Every device has a Boolean target it physically knows at no value over any `W` |
| Corollary 20(i–iv) | `corollary20_i`, `corollary20_ii`, `corollary20_iii`, `corollary20_iv` | Truth-preserving consequence and finite implication-chain rules, with every refinement hypothesis explicit |
| Corollary 21(i) | `corollary21_i` | A valid one-known/one-true modus-ponens variant |
| Corollary 21(ii) | `corollary21_ii_repaired`, `Examples.…corollary21_ii_counterexample` | The printed second disjunct is false; Lean proves the valid successive-implication repair and exhibits a countermodel |
| Corollary 23 | `corollary23` | Of two distinguishable devices, one never physically knows the other's conclusion |
| Corollary 24 | `corollary24` | Knowledge of one device's conclusion forces three inequivalent targets unknown to the other |
| equation (11) | `KnowsEvent`, `KnowledgeEvent` | Literal event translation and the event “`C` knows `E`” |
| Corollary 25 | `PositiveIntrospection`, `Examples.…not_positiveIntrospection_observer` | The printed positive-introspection claim is false under equation (11); the predicate is refuted, not asserted |

## Source

D. H. Wolpert, *Physical limits of inference*, Physica D 237(9):1257–1281, 2008,
`doi:10.1016/j.physd.2008.03.040`, arXiv:0708.1362 **v2**, cross-checked statement by statement against the published
Physica D article: no formal statement differs. Every numbered item of
the 2008 inventory (Defs 1–14, Thms 1–7, Props 1–7, Cors 1–5, Lemma 1) has a row
above. The inventory is **45 items** counting split parts; with Theorem 2's unnumbered
third sentence that is **46 tracked statements**. Coverage is `SOURCE-EXACT` for
42, `SPECIALIZED` for 1, `REPAIRED` for 2, `ASSUMED-STEP` for 0, `REFUTED` for 1.
Eleven further rows track unnumbered prose, and six worked examples are tracked
in their own inventory; both are counted separately from the 46.

The separate 2018 source is D. H. Wolpert, *Constraints on physical reality
arising from a formalization of knowledge*, arXiv:1711.03499v3 (2018). The
physical-knowledge cluster above transcribes Definition 11, Lemma 17,
Proposition 18, and Corollaries 19–24. The nested event module transcribes the
event definitions and refutes Corollary 25 as printed. The §III stochastic and
complexity clusters are transcribed too — Definitions 4 and 6 through 9 and
Propositions 7 through 14 — with Proposition 12 refuted. The Kraft direction the
source cites is a citation rather than a claim of the paper, and nothing here
waited on it.

## Explicit non-claims

Corollary 1(ii) is **refuted as literally stated** — see the Device module
docstring and the provenance note. Nothing here makes `U` a set of physical
worldlines merely because the 2018 predicate is named physical knowledge.

`WeaklyInfers` is **not** a form of `Knowledge.Knowable`, in either direction, and
`Examples.Inference.Device` exhibits both countermodels. No AI-system reading
follows without a separate reviewed bridge.
-/
