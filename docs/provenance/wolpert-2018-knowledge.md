# Wolpert 2018 — statement and formalization map

Source-pinned extraction for the 2018 extension. Definition 11 through
Corollary 24 are covered in `AISafetyAtlas.Inference.PhysicalKnowledge` and its
`Epistemic` child; equation (11) is transcribed in the `Event` child and
Corollary 25 is machine-refuted. The §III stochastic and complexity clusters are
closed too: Definitions 4 and 6 through 9 and Propositions 7 through 14 all have
rows and declarations. §0 below is the authority on what is mechanized.
The 2008 oracle (`AISafetyAtlas.Inference`,
[`wolpert-inference-devices.md`](wolpert-inference-devices.md)) is the regression
test for any 2018 encoding.

**Architecture (locked):**

```text
2008 minimal device
  → 2018 physical-knowledge extension
  → epistemic consequences
  → later bridges to Knowable, oversight, AI applications
```

Do **not** identify physical knowledge with `Knowable`. Do **not** label the
epistemic layer “S4” or “S5” in Lean until the exact listed propositions are
pinned and proved.

Every scope restriction in either paper is enumerated in the **scope audit** of
[`wolpert-inference-devices.md`](wolpert-inference-devices.md), which says for
each whether it is the source's own, forced by what the printed formula has to
denote, Lean's, or a real reduction.

## Source

D. H. Wolpert, *Constraints on physical reality arising from a formalization of
knowledge*, arXiv:1711.03499v3. HTML: <https://arxiv.org/html/1711.03499v3>.
The PDF header is `arXiv:1711.03499v3 [physics.hist-ph] 28 Jun 2018`.
Registry: `survey-ref-054` on BY-024 and the source-specific claim row
`CLM-WOLPERT-KNOW-001`.

The paper **reviews** the 2008 ID core (observation, prediction, memory, control
as sharing a pair of functions on a common `U`) and then **extends** it. It
notes that richer modeling may need structure beyond the minimal ID.

Numbering below is **2018’s**. It is not the 2008 numbering (2018 Prop. 1 ≈ 2008
Prop. 1(ii); 2018 Prop. 2 ≈ 2008 Thm 1).

**Cross-source clarification for 2008 Proposition 6.** The 2018 restatement
(Proposition 11) assumes statistical independence of the two setup functions
directly. This supports separating the 2008 proof into two claims: the
conditional-expectation identities follow from independence, while the 2008
sentence taking mutual-information distinguishability one to independence is
a distinct step. The Lean 2008 layer proves the first implication as
`prop6Law_of_independent`, and the second from its own printed premise: the
mutual-information step is the equality case of Gibbs
(`mutualInfoOn_eq_zero_iff`). There is no assumed step in the 2008 map, and its
`ASSUMED-STEP` count is zero.

---

## 0. Complete source inventory

Every numbered item in arXiv:1711.03499v3, plus the displayed equations, the
worked examples and the two prose notions the paper raises without a displayed
claim. **This table is the authority and it is closed**: an item of the source
that is absent here is a gate failure, not an omission the reader is expected to
notice. `scripts/check_wolpert_2018_status_table.py` reads exactly this section.

The guarantee is **closed over the enumerated classes** — every numbered
environment, every displayed equation, every worked example, and every prose
passage that states a claim — established by reading the PDF. The gate keeps
that reading from rotting; it cannot perform it. The list below is the whole
paper; the accounting is about *what is mechanized*.

**Statuses.** `SOURCE-EXACT`, `SPECIALIZED`, `REPAIRED` and `REFUTED` carry the
meanings fixed in [`wolpert-inference-devices.md`](wolpert-inference-devices.md).
Three are specific to a second-source map:

| Status | Meaning |
|---|---|
| `VIA-2008` | The 2018 statement is the 2008 statement. The Lean cell names the 2008 declaration; the note names the 2008 item. No second transcription is made, and none is owed |
| `CORE-ONLY` | The mathematical content is mechanized, the printed statement's own shape is not exposed as one declaration. Naming this separately is what stops "the core is done" from being read as "the proposition is a theorem here" |
| `NOT-MECHANIZED` | No Lean. The note must say **why**, not that it is absent |
| `INTERPRETATION` | The source item makes no mathematical claim to transcribe |

| 2018 item | Status | Lean declaration | Note |
|---|---|---|---|
| Def. 1 | VIA-2008 | `InferenceDevice` | 2008 Def. 1 |
| Def. 2 | VIA-2008 | `WeaklyInfers`, `IsProbe`, `IsSourceProbe` | 2008 Def. 3 |
| Def. 3 | VIA-2008 | `Distinguishable` | 2008 Def. 4 |
| Def. 4 | SOURCE-EXACT | `StronglyInfersPair`, `stronglyInfers_iff_stronglyInfersPair` | Strong inference of a **pair of functions** `(S, T)`: `∀δ ∈ P(T)`, `∀s ∈ S(U)`, `∃x`, `X = x ⇒ {S = s, Y = δ(T)}`. 2008 Def. 5 is device-to-device only, so this is a genuine generalization and not a renaming. `stronglyInfers_iff_stronglyInfersPair` shows Def. 5 is exactly this at a device's own `(setup, concl)` pair, so the generalization is conservative. Stated over arbitrary `S` and `T` in their own universes |
| Def. 5 | VIA-2008 | `StronglyInfers` | 2008 Def. 5 |
| Def. 6 | VIA-2008 | `inferenceAccuracySupOn`, `inferenceAccuracyOn`, `inferenceAccuracy` | 2008 Def. 9. `cov` is the same displayed formula — verified side by side in clash 18 of [`wolpert-2008-source-clashes.md`](wolpert-2008-source-clashes.md). 2008 Definition 9 is `SOURCE-EXACT`. Neither paper states finiteness on `X(U)` for the accuracy definition, and `inferenceAccuracySupOn` does not impose it: the printed `max_x` is a supremum over the positive-mass setups, which is where it denotes. 2018's own Definition 6 prints *"finite range"* on `Γ`, which is matched |
| Def. 7 | SPECIALIZED | `inferenceComplexitySum`, `inferenceComplexityOn`, `inferenceComplexityMeasure`, `measureLength` | The displayed sum with `ℳ_{μ,X}(x) = −ln μ(X⁻¹(x))`. `inferenceComplexityOn` takes the printed `min_x` as an `sInf` over a set of setups and needs no finiteness there; `inferenceComplexitySum` sums over the whole target type with `∑'`. The `\|Γ(U)\|` factor belongs to Proposition 13, not to this definition. On a countable range the printed sum may diverge and the `min` need not be attained, so the source states no condition under which its own display denotes a real number. **scope delta:** the source's `μ` may be a **semi-measure**, rendered here as total mass at most one wherever the distinction is used, which is weaker than the algorithmic-information notion |
| Def. 8 | SOURCE-EXACT | `HaltsAt`, `Recursive`, `recursive_iff_refines`, `haltsAt_of_not_realized` | Halting at `x`, total/recursive over `X(U)`, and the source's own identification *"So an ID `(X, Y)` is recursive iff `X` refines `Y`"* as `recursive_iff_refines`. No finiteness, measurability or decidability anywhere |
| Def. 9 | SPECIALIZED | `haltingSetups`, `PrefixFree`, `PrefixFreeOn`, `prefixFreeOn_iff_prefixFree`, `two_rpow_neg_measureLength`, `measureLengthBase2`, `two_rpow_neg_measureLengthBase2`, `sum_pushOnImage_le_one` | `∑_{x : D halts on x} 2^(−ℳ_{μ,X}(x)) ≤ 1`, transcribed literally. **Source defect, clash 21:** `ℳ` is defined with a natural logarithm and Definition 9 exponentiates in base 2, so the printed summand is `μ(X⁻¹(x))^(ln 2)`, not `μ(X⁻¹(x))`; under the base-consistent reading the condition is automatic and the definition restricts nothing. Both readings are proved. The following Kraft sentence is a **citation**, not a claim of the paper, and it is the existence direction, which Mathlib does not have. `PrefixFreeOn` states the condition in `ℝ≥0∞`, where a sum of nonnegative terms denotes over **any** index set — wider than the source's countable range — and `prefixFreeOn_iff_prefixFree` makes the finite form an instance. **One index restriction is deliberate:** the source writes *"`x` : `D` halts on `x`"* with no realizedness condition, but an unrealized setup halts vacuously and has `massOn = 0`, so `measureLength` is `−log 0`, which Lean totalizes to `0` and contributes `2⁰ = 1` per unrealized value. Indexing literally would break the condition in the totalization rather than in the mathematics. **scope delta:** `μ` is a `Measure`, where the source admits a semi-measure |
| Def. 10 | VIA-2008 | `Mimics`, `Copies` | 2008 Def. 7 |
| Def. 11 | SOURCE-EXACT | `PhysicalKnowledgeWitness`, `PhysicallyKnows` | Selector over realized target values; all three printed clauses. Detail in §1 |
| prose after Def. 11 | SOURCE-EXACT | `PhysicallyKnows.weaklyInfers` | Physical knowledge entails weak inference |
| Prop. 1 | VIA-2008 | `not_weaklyInfers_own_concl`, `exists_not_weaklyInfers` | 2008 Prop. 1(ii) |
| Prop. 2 | VIA-2008 | `not_infersDevice_both_of_distinguishable` | 2008 Thm 1 |
| Cor. 3 | SOURCE-EXACT | `exists_three_inequivalent_not_weaklyInfers` | Three inequivalent surjective binary targets `D` does not infer; consumed by Cor. 24 |
| Prop. 4(i) | VIA-2008 | `weaklyInfers_of_stronglyInfers` | 2008 Thm 2(i) |
| Prop. 4(ii) | VIA-2008 | `stronglyInfers_trans` | 2008 Thm 2(ii) |
| Prop. 4, third sentence | VIA-2008 | `infersDevice_of_stronglyInfers` | 2008 Thm 2, unnumbered third sentence |
| Prop. 5(i) | VIA-2008 | `exists_not_stronglyInfers` | 2008 Prop. 2(i) |
| Prop. 5(ii) | VIA-2008 | `exists_stronglyInfers_of_large_fibres` | 2008 Prop. 2(ii) |
| Prop. 6 | VIA-2008 | `not_stronglyInfers_both` | 2008 Thm 3 |
| Prop. 7(1) | SOURCE-EXACT | `identityDevice`, `identityDevice_weaklyInfers`, `exists_weaklyInfers_of_three_values` | *"For any function `Γ` over `U` such that `\|Γ(U)\| ≥ 3` there is a device `D` that weakly infers `Γ`."* **This is Wolpert's own repair of 2008 Cor. 1(ii)**, which is printed with no cardinality condition and is `REFUTED` in the 2008 map at `\|Γ(U)\| = 2`; clash 20. Proved in `Inference/Existence.lean` **without** the printed hypotheses that `U` be countable and have at least two elements: neither is used. `Examples.…Existence.two_values_is_too_few` puts the repair and the refutation side by side |
| Prop. 7(2) | SOURCE-EXACT | `not_stronglyInfersPair_id`, `exists_pair_not_stronglyInfers` | Some `(S, T)` is strongly inferred by no device. The source's construction, `S = T = ` identity: the first obligation pins the fibre to one point and the second forces the conclusion `true` there, so the conclusion is constant and Def. 1's surjectivity fails. Nothing finite, decidable or countable is used — the probe at each point comes from `exists_isProbe` |
| `cov ≤ 1` and the equality case, prose after Def. 6 | SOURCE-EXACT | `inferenceAccuracy_le_one`, `inferenceAccuracy_eq_one_iff`, `inferenceAccuracy_eq_one_of_weaklyInfers`, `weaklyInfers_of_inferenceAccuracy_eq_one` | *"Clearly, `cov(D, Γ) ≤ 1.0`, and if `P` is nowhere 0, then `cov(D, Γ) = 1.0` iff `D > Γ`."* Both halves, and the `iff` in the printed shape as `inferenceAccuracy_eq_one_iff`. The source's *"clearly"* holds with no hypothesis. The converse direction is the one with content: accuracy `1` forces every probe's term to `1`, a `sup'` over a `Finset` is attained, so some positive-mass setup answers the probe across its whole fibre — and probes at a value are unique, so answering `probe γ` answers every probe of `γ`. 2008 prints only the forward half after its Definition 9. Both halves hold at general measure too: `inferenceAccuracyOn_le_one` and `inferenceAccuracyOn_eq_one_iff`. The `FinPMF` forms remain as the discrete instances. The printed *"if `P` is nowhere 0"* is `hatom`, every singleton of positive measure, and it does **more** work at general measure than in the finite case: over a general measure `cov = 1` forces agreement with the probe only *almost everywhere* on a fibre, while `WeaklyInfers` quantifies over every point of it. `condExpectPmOn_eq_one_iff_forall` is where the null set is collapsed |
| universal device, prose after Def. 10 | SOURCE-EXACT | `IsUniversal`, `universal_unique`, `isStrongRoot_of_isUniversal` | *"Define a universal device as any device in a reality that can strongly infer all other devices and weakly infer all functions in that reality. Prop. 6 means that no reality can contain more than one universal device."* Word for word the 2008 passage after its Definition 7, with Prop. 6 in place of 2008 Thm 3 — the same theorem. Proved **stronger than printed**: uniqueness needs only the strong-inference clause, so `IsUniversal` carries only that one. The graph reading *"a universal device must be a root node of the strong inference graph"* is `isStrongRoot_of_isUniversal`, and *"there cannot be any other root node"* is `strongRoot_eq_of_isUniversal`. Both printed clauses are transcribed on `FullReality.IsUniversalFull`, which carries *"strongly infer all other devices"* **and** *"weakly infer all functions in that reality"* over `FullReality` (the `{Γ_β}` family `DeviceReality` lacks); `FullReality.isUniversalFull_unique` is uniqueness at the printed definition, inherited rather than reproved — the argument never used the second clause. `IsUniversal` stays as the one-clause form because `universal_unique` on it is strictly stronger than the source's |
| `\|U\| > 3` sentence, prose after Def. 10 | REPAIRED | `not_isUniversalFull_of_concl_mem`, `not_isUniversalFull_of_containsEveryTwoValuedBool`, `func_two_of_concl_mem`, `id_is_device_pair_on_bool` | *"Prop. 7(ii) means that no reality with `\|U\| > 3` can have a universal device if the reality contains all functions defined over `U`."* **The conclusion is a theorem; the cited justification cannot support it**, clash 28. Proposition 7(2) is an existential over *pairs*; universality's clause 1 quantifies over *devices*. An existential cannot discharge that, whatever witness is chosen. The source's own witness `S = T = id` is a device pair only at `U = Bool`, which `\|U\| > 3` excludes — `id_is_device_pair_on_bool`. The correct route is 2018 Proposition 1 / 2008 Proposition 1(ii): a universal device must weakly infer its own conclusion once that conclusion is in the family, and `not_weaklyInfers_own_concl` forbids it. `func_two_of_concl_mem` is the honesty check that this does not shift the comparison — a device's conclusion is surjective onto `𝔹`, so it is admissible under `SourceStipulations`. No `\|U\| > 3` is used; the hypothesis is vestigial on every correct route. Graded `REPAIRED` rather than `SOURCE-EXACT` so the row does not launder a route swap into an exact transcription. Premises inhabited by `Examples.…conclInFamilyReality_not_universal` |
| `Ĉ(Γ; D)` after Def. 7 | SOURCE-EXACT | `answeringMassOn`, `unionInferenceComplexityOn`, `unionInferenceComplexity`, `answeringMass_eq_sum`, `answeringMass_eq_sum_exp` | *"A natural modification to Def. 7 is to remove the min by considering all `x`'s that cause `Y = δ(Γ)`, not just of one of them."* A displayed definition plus a displayed equality, announced by no numbered environment. The same text and the same formula appear in 2008 after Definition 6; both are transcribed by the one declaration. `answeringMassOn` takes the union over `answeringSetOn`, and a union needs no finite index. The printed equality `−ln μ(⋃ …) = −ln (Σ e^{−ℳ(x)})` is `answeringMass_eq_sum` composed with `answeringMass_eq_sum_exp`. The source's justification is *"for any `x`, `x' ≠ x`, `X⁻¹(x) ∩ X⁻¹(x') = ∅"*, and that disjointness is exactly what the Lean uses — with **measurability**, which the source does not state and which is not optional: a measure is only sub-additive on arbitrary sets, so without it the printed equality is a `≤`. **What separates this from the 2008 row is the measure class, and only that.** 2018 Definition 7 supplies `μ` as a **semi-measure**, so total mass is at most one and the infinite-mass case `massOn`'s `toReal` sends to `0` cannot arise in the printed setting. 2008 admits an arbitrary `μ`, where counting measure on an infinite `U` does reach it, and that row stays `SPECIALIZED` for exactly that reason |
| Prop. 8 | SOURCE-EXACT | `inferenceAccuracyOn_ge`, `inferenceAccuracy_ge`, `sum_condExpectPmOn_probe`, `measure_sum_fiber`, `massOn_agree_probe`, `sum_boolPm_probe`, `inferenceAccuracy_nonneg_of_card_eq_two` | `cov(D, Γ) ≥ (2 − \|Γ(U)\|) · max_x E_P(Y \| x) / \|Γ(U)\|`, in `Stochastic/Bounds.lean`. The whole content is the pointwise identity `∑_{γ ∈ Γ(U)} δ_γ(Γ(u)) = 2 − \|Γ(U)\|`, isolated as `sum_boolPm_probe`. Nonemptiness of the realized image is **not** assumed — it follows from `concl_surjective`. `inferenceAccuracy_nonneg_of_card_eq_two` is the binary case, where the bound says accuracy is never negative. `inferenceAccuracyOn_ge` is the general-measure statement: `U` arbitrary, `P` any probability measure — the printed quantification. Measurability is not a narrowing: the printed `E_P(· \| x)` presupposes measurable fibres and a measurable integrand, so the print requires it whether or not it writes it, and `IsFiniteMeasure` is weaker than the printed *"probability measure"*. `inferenceAccuracySupOn_ge` proves the printed bound with **no finiteness on the setup range**: `[FiniteRange C.setup]` is replaced by `hne`, the existence of one positive-mass setup value — which is exactly what the printed `max_x` needs in order to denote, since under an arbitrary probability measure every fibre can be null. `accuracySupOn_eq_sup'` proves the two forms are the same object on a finite range. Attainment is not needed: the printed factor `2 − \|Γ(U)\|` is negative once `\|Γ(U)\| ≥ 3`, so pulling it through a supremum flips it to an infimum, but `sup (c · f) = c · inf f ≥ c · sup f` for `c < 0`, so the bound survives the flip. *"for countable `U`"* is local to equation (4), not a hypothesis of Definition 6. `condExpectPmOn` is a ratio of fibre masses, so `sum_boolPm_probe` transports across the `Γ`-partition only with exact additivity (`measure_sum_fiber`, `massOn_agree_probe`). In the finite form the sign of `2 − \|Γ(U)\|` never enters, since the bound is `Finset.le_sup'` under a sum; in the sup form it does, and the proof splits on it |
| Prop. 9 | SOURCE-EXACT | `fig5_stronglyInfers`, `fig5_accuracy_dev1`, `fig5_accuracy_dev2`, `fig5_accuracy_gap` | There are `D`, `D′ ≫ D`, `P`, `Γ` with `cov(D, Γ)` arbitrarily close to 1 while `cov(D′, Γ) = 0`: 2008 Thm 2(i) inheritance has no approximate form. Figure 5 is transcribed state by state. Proved **sharper than printed**: `cov(D, Γ) = p` exactly and `cov(D′, Γ) = 0` for every `0 ≤ p ≤ 1`, so the `p → 1` limit is replaced by naming the `p` that achieves a given `ε` |
| Prop. 10 | SOURCE-EXACT | `fig6_distinguishable`, `fig6_accuracy_dev1`, `fig6_accuracy_dev2`, `fig6_accuracy_near_one`, `exists_distinguishable_accuracy_near_one` | There are setup-distinguishable `D`, `D′` with both `cov(D, D′)` and `cov(D′, D)` arbitrarily close to 1 — the stochastic collapse of Prop. 2 / 2008 Thm 1. Figure 6 is transcribed state by state. Proved **sharper than printed**: `fig6_accuracy_dev1` and `fig6_accuracy_dev2` give both accuracies as the exact identity `(1 − 6b)/(1 − 4b)`, so "arbitrarily close" is algebra rather than an estimate, and `fig6_accuracy_near_one` names the `b` for a given `ε` |
| Prop. 11 | SOURCE-EXACT | `prop11_of_independentOn`, `prop11_of_independent`, `prop6_product_eqOn`, `prop6_product_eq`, `prop6Expr_bddAbove` | Independence ⇒ `ε₁ε₂ ≤ max_{z∈M}\|αβk² + αkm + βkn + mn\|`, and `≤ ¼` at `α = β = ½`. The Lean is **sharper**: `prop6_product_eq` identifies the realized product with the polynomial rather than bounding it, so no supremum over `M` need exist. `prop11_of_independent` exposes the printed `≤ max` shape from the source's own independence premise: `M` is the unit hypercube, which is `Prop6Quadruple`, so the maximum is `⨆ z : Prop6Quadruple` and `prop6Expr_bddAbove` makes it a real number. The printed defect *"`D₂` infers `D₂`"* is in the source; see clash 18. Printed: *"two devices where `X₁(U) = X₂(U) = 𝔹`, and those variables are statistically independent under `P`"*. The two-valued setup ranges are the **source's own hypothesis**. `prop11_of_independentOn` is the general-measure form: `U` arbitrary, `P` any probability measure. Measurability is forced by what `E_P(· \| x)` has to denote and is not a narrowing |
| Prop. 12 | REFUTED | `prop12_refuted`, `prop12_gap`, `prop12_complexity`, `prop12_entropy` | `C_μ(Γ; D) ≤ \|Γ\| × H_μ(X)`. **False**, clash 23. A four-state countermodel meeting every printed hypothesis gives `C_μ = 4 ln 2 − ln 3` and `\|Γ\| H_μ = 4 ln 2 − (3/2) ln 3`, so the inequality fails by exactly `(ln 3)/2` — `prop12_gap` is an identity, not an estimate. The printed proof's last step compares two sums term by term and needs `μ(x) ≥ 1/\|Γ\|` at every setup value, which nothing assumes. **No entropy dependency was needed**: `entropyOn`, built for Def. 10, is the `H_μ(X)` the proposition names |
| Prop. 13 | VIA-2008 | `inferenceComplexityOn_le_of_stronglyInfers`, `inferenceComplexityMeasure_le_of_stronglyInfers`, `measureLength_sub_measureLength` | `C_μ(Γ; D₁) − C_μ(Γ; D₂) ≤ \|Γ(U)\| × max_{x₂} min_{x₁} [ℳ_{μ,X₁}(x₁) − ℳ_{μ,X₂}(x₂)]`. This is 2008 Thm 4 at the measure length, and the source's min is over `{X₁=x₁ ⇒ X₂=x₂, Y₁=Y₂}`, which is `emulationSet` verbatim. `measureLength_sub_measureLength` adds the source's own remark that the difference is `ln(μ(X₂⁻¹(x₂))/μ(X₁⁻¹(x₁)))`, hence unit-independent. The printed statement fixes `Γ(U)` finite and quantifies over *any* distribution — both matched. `inferenceComplexityOn_le_of_stronglyInfers` derives the bound from `C₁ ≫ C₂` and `C₂ > Γ` with no finiteness on the setup ranges, at the cost of hypotheses saying the printed `min` and `max` are attained — which is what writing them asserts. `inferenceComplexityMeasure_le_of_stronglyInfers` keeps `[FiniteRange]` and is an instance, not the claim. Unlike Prop. 14, whose existential *"there are devices…"* is fully served by a finite witness, and unlike Prop. 12, whose refutation by a four-state countermodel is valid against a countable-scope claim because finite ranges are countable |
| Prop. 14 | SOURCE-EXACT | `exists_complexity_inversion`, `inv_complexity`, `inv_complexity'`, `inv_stronglyInfers`, `inv_weaklyInfers` | There are `D > Γ` and `D′ ≫ D` with `C_P(Γ; D)` arbitrarily large while `C_P(Γ; D′)` approaches the minimum `\|Γ(U)\| ln \|Γ(U)\| = 2 ln 2`. **The statement is true; the printed proof is not** — clash 24. Figure 7's two heavy fibres of `D′` both answer the `+1` probe, so its `−1` probe is forced onto a vanishing fibre and `C_P(Γ; D′)` diverges too. Proved instead on an eight-state construction whose two heavy fibres answer *different* probes: `C_P(Γ; D) = −ln ε − ln(1−ε)` and `C_P(Γ; D′) = 2 ln 2 − 2 ln(1−ε)`, both identities, so the `ε` achieving a given `M` and `δ` is named rather than approached |
| Prop. 15(i) | VIA-2008 | `exists_pairwise_distinguishable_weak_cycle` | 2008 Prop. 3(i) |
| Prop. 15(ii) | VIA-2008 | `not_mutually_distinguishable_weak_cycle` | 2008 Prop. 3(ii) |
| Prop. 15(iii) | VIA-2008 | `not_strong_inference_cycle` | 2008 Prop. 3(iii) |
| Prop. 16(i) | VIA-2008 | `exists_copies_distinguishable_weak` | 2008 Prop. 5(i) |
| Prop. 16(ii) | VIA-2008 | `exists_copies_stronglyInfers_infinite`, `copies_stronglyInfers_not_finite` | 2008 Prop. 5(ii) |
| Lemma 17(i) | SOURCE-EXACT | `PhysicalKnowledgeWitness.eq_target_of_mem_knownBlock` | Truth on the selected known-value block inside `W` |
| Lemma 17(ii) | SOURCE-EXACT | `PhysicalKnowledgeWitness.eq_target_on_of_refinesOn` | Truth throughout a refining `W` |
| Proposition 18 | SOURCE-EXACT | `physicallyKnows_false_iff_not_true` | Boolean relabelling by negation |
| Corollary 19 | SOURCE-EXACT | `true_on_of_physicallyKnows_true`, `false_on_of_physicallyKnows_false`, `not_physicallyKnows_true_and_false` | Truth, falsity, and incompatibility under refinement |
| Corollary 20(i) | SOURCE-EXACT | `corollary20_i` | Known antecedent plus true implication |
| Corollary 20(ii) | SOURCE-EXACT | `corollary20_ii` | Known antecedent and implication imply truth, not knowledge, of the consequent |
| Corollary 20(iii) | SOURCE-EXACT | `corollary20_iii` | Two known successive implications make their composite true |
| Corollary 20(iv) | SOURCE-EXACT | `corollary20_iv` | The finite chain, zero-indexed in Lean |
| Corollary 21(i) | SOURCE-EXACT | `corollary21_i` | Either antecedent or implication may be the known premise |
| Corollary 21(ii) | REPAIRED | `corollary21_ii_repaired`, `corollary21_ii_counterexample` | **Transposition in the printed text.** The printed second disjunct reads *"`Γ1 ⇒ Γ2` is true and `D` knows that `Γ1 ⇒ Γ3` is true it follows that `Γ2 ⇒ Γ3` is true"* — verified identical in the published PDF and in the arXiv HTML, so it is the author's text and not an OCR artifact. The lead-in says these *"weaken the last two claims in Coroll. 20"*, and Corollary 20(iii) concludes `Γ1 ⇒ Γ3` from **both** implications being known. A weakening keeps the conclusion and relaxes a premise, so `Γ2 ⇒ Γ3` and `Γ1 ⇒ Γ3` have been swapped. `corollary21_ii_repaired` proves the corrected statement: `W` refining both implications, and either one known with the other merely true, gives `Γ1 ⇒ Γ3` true. `corollary21_ii_counterexample` still refutes the sentence **as literally printed**. Clash 26; §2 |
| Corollary 22 | SOURCE-EXACT | `exists_never_physicallyKnown` | Prop. 1 / 2008 self-conclusion transported through Def. 11 |
| Corollary 23 | SOURCE-EXACT | `corollary23` | Prop. 2 / 2008 Thm 1 transported through Def. 11 |
| Corollary 24 | SOURCE-EXACT | `corollary24` | Three pairwise-inequivalent surjective targets unknown on every refining context; premises inhabited by `corollary24_nonvacuous` |
| Corollary 25 | REFUTED | `PositiveIntrospection`, `not_positiveIntrospection_observer` | Equation (11) may be universal: then the source target is inadmissibly constant, while the natural singleton extension is false; §2 |
| equations (1)–(4) | INTERPRETATION | — | The paper's working notation, introduced before any claim uses it: (1) the partition `Γ ≡ {{u : Γ(u) = γ} : γ ∈ Γ(U)}` induced by a function; (2) the characteristic function `X_R(u) = 1 ⇔ u ∈ R`; (3) the probe `δ_v(v')`, `1` at `v = v'` and `−1` otherwise; (4) the numerator of Def. 6's `cov` written out explicitly *"for countable `U`"*. None states a claim — each fixes a symbol the later displays use, and all four are carried in Lean by the definitions that consume them (`rangeFinset` and fibre preimages, `Set.indicator`-style membership, `IsProbe` with `probe`, and `inferenceAccuracyOn`). Listed because this inventory is closed and tracks equations (5)–(11): an equation absent from a table that calls itself complete is the reader's problem, not the source's |
| equations (5)–(8), (10) | INTERPRETATION | — | Ordinary Boolean conjunction, negation, disjunction, equivalence and biconditional. Lean's `Bool` operations are used directly |
| equation (9) | SOURCE-EXACT | `boolImplies` | The one Boolean connective the theorems consume, so the one that receives a declaration |
| equation (11) | SOURCE-EXACT | `KnowsEvent`, `KnowledgeEvent` | Literal event characteristic and union of selected blocks |
| Example 1 | INTERPRETATION | — | Motivating physical scenario, no displayed claim |
| Example 2 | INTERPRETATION | — | Motivating physical scenario, no displayed claim |
| Example 3 | INTERPRETATION | — | Illustration of Def. 2 holding and failing |
| Example 4 | INTERPRETATION | — | Illustration of the device model |
| Example 5 | INTERPRETATION | — | Weather-prediction reading of Def. 5 |
| Example 6 | REFUTED | `ex6_accuracy`, `ex6_prop8_bound`, `ex6_bound_not_attained`, `ex6_prop8_holds` | *"This bound is sharp, as can be seen from the following example."* **The sharpness claim is false**, clash 25. The construction's central identity `E_P(Yδ_γ(Γ) \| x) = c · E_P(Y \| x)` with `c = (2 − \|Γ(U)\|)/\|Γ(U)\|` is correct and is verified. The next line pulls `c` out of a maximum, which is valid only for `c ≥ 0`; for `\|Γ(U)\| ≥ 3` the factor is negative and the maximum moves to the **minimum** of `E_P(Y \| x)`. On a twelve-state instance of the source's own recipe with non-constant inference power the accuracy is `0` while the bound is `−1/9`, so the bound is strictly not attained. Proposition 8 itself still holds there |
| Example 7 | INTERPRETATION | — | Reading of the complexity layer |
| Example 8 | INTERPRETATION | — | Greenwich-sky reading of Def. 11. Non-vacuity is carried instead by the executable `Bool`-pair certificate, which inherits no physical interpretation |
| Example 9 | SOURCE-EXACT | `distribution_failure` | Both premises known, the consequence true but not known |
| weaker knowledge, prose after Example 9 | REPAIRED | `WeakKnowledgeWitness`, `WeakPhysicallyKnows`, `weakPhysicallyKnows_of_physicallyKnows` | An alternative, weaker knowledge operator: Definition 11 with clause (i)'s biconditional split into a global *"a `true` answer is correct"* half and a `W`-restricted *"a `false` answer is correct"* half. The arXiv HTML and the LaTeX carry the inequality `γ′ ≠ γ`, so the negative-answer clause is well-formed. Graded `REPAIRED` for a printed slip: the clause writes `δ_γ`, demanding `Γ(u) ≠ γ` on the block `ξ(γ′)`, while the sentence immediately after describes the device answering *"does `Γ(u) = γ′`?"*, which is `δ_{γ′}`. Only the `δ_{γ′}` reading makes the modification a **weakening** — `weakPhysicallyKnows_of_physicallyKnows` proves Definition 11 entails it, and under the printed `δ_γ` that implication fails, since Definition 11 permits a state of `ξ(γ′)` to carry the value `γ` while the device answers `false` there. Clash 27, which also records the author comment left in the LaTeX showing the passage was never finished |
| negative introspection, prose | INTERPRETATION | — | Footnote 23 has two halves and they are graded together. The **physical-knowledge** half is genuinely undefined — *"it is not clear how to formalize a physical knowledge version of the negative introspection rule, since that requires defining a function over `U` that captures the case that the device does not know that `u ∈ E`"* — so there is no claim to transcribe. The **event-based** half *is* a definite claim with a proof sketch — *"the event 'Alice does not know `E`' cannot contain any `u` obeying `u ∈ A(u)`"* — but it is a claim about **Aumann structures**, a framework this paper imports and does not define, and which the Atlas does not model at all: there is no `A(u)` here, only devices. Tracking it would mean formalizing a second epistemic framework to state one footnote. Classified `INTERPRETATION` on that ground rather than on the absence of a claim |

**Coverage.** Counts are printed by the gate rather than restated here, so that
this paragraph cannot drift from the table.

The §III material splits into three independent blocks, all mechanized:

1. **Def. 4 with Prop. 7** — pure combinatorics. No measure, no entropy. Def. 4
   is a generalization of `StronglyInfers` from a device to a pair of functions;
   Prop. 7's proofs are identity-setup constructions. No extra dependency.
2. **Props. 8–10** — covariance bounds and two finite worked counterexamples.
   Props. 9 and 10 are finite tables. No extra dependency.
3. **Defs. 7–9 with Props. 12–14** — needs `ℳ_{μ,X}`, semi-measures and halting.
   The Kraft direction the source cites is an existence statement Mathlib does not
   have, and it is a citation rather than a claim of the paper. Shannon entropy
   is used for Prop. 12 alone — `entropyOn`, built for Def. 10. Prop. 12 is
   false.

---

## 1. Knowledge operator (Def. 11) — the genuine extension

**Locator:** §V.1, Definition 11.

**Data.** Device `(X, Y)` over `U`; function `Γ` over `U`; value `γ ∈ Γ(U)`;
subset `W ⊆ U`; a **selector** `ξ : Γ(U) → X̄` where `X̄` is the partition of
`U` induced by `X`.

**“`(X, Y)` physically knows `Γ = γ` over `W`”** iff there exists such a `ξ`
with:

1. **(i) Weak-inference fibre condition (on all of `U`).**  
   `∀ γ′ ∈ Γ(U), u ∈ ξ(γ′) ⇒ Y(u) = δ_{γ′}(Γ(u))`.
2. **(ii) Yes on `W` at `γ`.**  
   `∅ ≠ ξ(γ) ∩ W ⊆ Y⁻¹(1)`.
3. **(iii) No on `W` at every other value.**  
   `∀ γ′ ≠ γ, ∅ ≠ ξ(γ′) ∩ W ⊆ Y⁻¹(−1)`.

Clause (i) is required on **all of `U`**, not only `W`: the agent has no
independent test of `u ∈ W`. Clauses (ii)–(iii) are the extra structure beyond
weak inference (at least one yes and one no on `W`). The paper says most later
analysis does not use (iii); it is kept so the no-logical-omniscience argument
still applies when (iii) holds.

**Not `Knowable`.** `ξ` picks a **setup-partition block per target value**.
`Knowable` is `∃ decoder, ∀ ω`. Different data, different quantifiers. Do not
identify them in the first Lean encoding.

**Immediate paper consequence (prose after Def. 11, not a numbered theorem):**  
Def. 11(i) ⇒ the device **weakly infers** `Γ`. This is the first Lean target
after the definition: `PhysicallyKnows … → WeaklyInfers`. Mechanized as
`PhysicallyKnows.weaklyInfers`.

**Lemma 17.** If the device knows `Γ = γ` over `W` via `ξ`:  
(i) `Γ(u) = γ` for all `u ∈ ξ(γ) ∩ W`;  
(ii) if `W` refines `Γ`, then `Γ` is constantly `γ` on `W`.

Mechanized as `PhysicalKnowledgeWitness.eq_target_of_mem_knownBlock` and
`PhysicalKnowledgeWitness.eq_target_on_of_refinesOn`.

**Proposition 18.** For binary `Γ`: the device knows that `Γ` is false iff it
knows that `¬Γ` is true. (Relabel `ξ`.)

Mechanized as `physicallyKnows_false_iff_not_true`.

---

## 2. Epistemic consequences and source defects

The paper discusses physical knowledge in the context of epistemic logic and
the five S5 rules. The table records source correspondence item by item; it does
not attach an S4 or S5 label to the Lean API.

The subsection opens with **two** standing stipulations, and the Lean drops both:

> *"For the rest of this subsection assume that any space `U` we consider is
> countable. I will consider Boolean-valued functions, i.e., functions `Γ` such
> that `Γ(U) = {−1, 1}`."*

1. **Countability of `U`.** Not used by any displayed argument below, so the Lean
   statements retain the arbitrary universe of Definition 11.
2. **Surjectivity of the binary functions.** Corollaries 20 and 21 are printed for
   *"any binary-valued functions"*, which under that sentence means onto `𝔹`.
   `corollary20_i`–`corollary21_i` take `Γ : U → Bool` with no surjectivity. The
   source is already loose about this itself: `Γ₁ ⇒ Γ₂` need not be onto `𝔹`, yet
   Corollary 20(ii) refines and knows it. This is the 2018 counterpart of the 2008
   global two-value stipulation, dropped there too — clash 13 in
   [`wolpert-2008-source-clashes.md`](wolpert-2008-source-clashes.md).

Both are proved scope generalizations, not omitted hypotheses that a proof needs.
Neither module carries a single `Fintype`, `Finite`, `Countable` or `DecidableEq`
hypothesis; this is measured from the declarations, not asserted.

| 2018 item | Status | Lean declaration | Fidelity note |
|---|---|---|---|
| Def. 11 | SOURCE-EXACT | `PhysicalKnowledgeWitness`, `PhysicallyKnows` | Selector over realized target values; all three printed clauses |
| prose after Def. 11 | SOURCE-EXACT | `PhysicallyKnows.weaklyInfers` | Physical knowledge entails weak inference |
| Lemma 17(i) | SOURCE-EXACT | `PhysicalKnowledgeWitness.eq_target_of_mem_knownBlock` | Truth on the selected known-value block inside `W` |
| Lemma 17(ii) | SOURCE-EXACT | `PhysicalKnowledgeWitness.eq_target_on_of_refinesOn` | Truth throughout a refining `W` |
| Proposition 18 | SOURCE-EXACT | `physicallyKnows_false_iff_not_true` | Boolean relabelling by negation |
| Corollary 19 | SOURCE-EXACT | `true_on_of_physicallyKnows_true`, `false_on_of_physicallyKnows_false`, `not_physicallyKnows_true_and_false` | Truth, falsity, and incompatibility under refinement |
| Corollary 20(i) | SOURCE-EXACT | `corollary20_i` | Known antecedent plus true implication |
| Corollary 20(ii) | SOURCE-EXACT | `corollary20_ii` | Known antecedent and implication imply truth, not knowledge, of the consequent |
| Corollary 20(iii) | SOURCE-EXACT | `corollary20_iii` | Two known successive implications make their composite true |
| Corollary 20(iv) | SOURCE-EXACT | `corollary20_iv` | The finite chain, zero-indexed in Lean |
| Corollary 21(i) | SOURCE-EXACT | `corollary21_i` | Either antecedent or implication may be the known premise |
| Corollary 21(ii) | REPAIRED | `corollary21_ii_repaired`, `corollary21_ii_counterexample` | **Transposition in the printed text.** The printed second disjunct reads *"`Γ1 ⇒ Γ2` is true and `D` knows that `Γ1 ⇒ Γ3` is true it follows that `Γ2 ⇒ Γ3` is true"* — verified identical in the published PDF and in the arXiv HTML, so it is the author's text and not an OCR artifact. The lead-in says these *"weaken the last two claims in Coroll. 20"*, and Corollary 20(iii) concludes `Γ1 ⇒ Γ3` from **both** implications being known. A weakening keeps the conclusion and relaxes a premise, so `Γ2 ⇒ Γ3` and `Γ1 ⇒ Γ3` have been swapped. `corollary21_ii_repaired` proves the corrected statement: `W` refining both implications, and either one known with the other merely true, gives `Γ1 ⇒ Γ3` true. `corollary21_ii_counterexample` still refutes the sentence **as literally printed** |
| Corollary 22 | SOURCE-EXACT | `exists_never_physicallyKnown` | 2018 Proposition 1 / 2008 self-conclusion transported through Def. 11 |
| Corollary 3 | SOURCE-EXACT | `exists_three_inequivalent_not_weaklyInfers` | Earlier three-function gap used by Corollary 24 |
| Corollary 23 | SOURCE-EXACT | `corollary23` | 2018 Proposition 2 / 2008 Theorem 1 transported through Def. 11 |
| Corollary 24 | SOURCE-EXACT | `corollary24` | Three pairwise-inequivalent surjective targets unknown on every refining context; full premises inhabited by `corollary24_nonvacuous` |
| equation (11) | SOURCE-EXACT | `KnowsEvent`, `KnowledgeEvent` | Literal event characteristic and union of selected blocks |
| Corollary 25 | REFUTED | `PositiveIntrospection`, `not_positiveIntrospection_observer` | Equation (11) may be universal: then the source target is inadmissibly constant, while the natural singleton extension is false |
| Example 9 | SOURCE-EXACT | `distribution_failure` | Both premises are known, the consequence is true but not known |

### Corollary 21(ii)

The second printed disjunct assumes that `Γ₁ ⇒ Γ₂` is true and that the
device knows `Γ₁ ⇒ Γ₃`, then concludes that `Γ₂ ⇒ Γ₃` is true.
The valuation `Γ₁ = false`, `Γ₂ = true`, `Γ₃ = false` refutes that
implication, and `corollary21_ii_counterexample` inhabits all knowledge and
refinement premises. `corollary21_ii_repaired` proves the natural weakening of
Corollary 20(iii): one successive implication is known, the other is true, and
their composite `Γ₁ ⇒ Γ₃` is true.

### Corollary 25

Equation (11) unions every setup block selected by every certificate witnessing
knowledge of `E`. Its characteristic is true throughout those blocks.
Definition 11(i), however, makes the characteristic of `E` follow the device's
varying conclusion there. The paper's proof asserts that the two
characteristics agree on the selected blocks; they need not.

The four-state Definition 11 observer is a countermodel. It knows `trueWorlds`;
its selected blocks cover the universe, so its `KnowledgeEvent` is `Set.univ`;
neither setup fibre has constantly true conclusion, so it cannot know that
universal event. `not_positiveIntrospection_observer` refutes the exact
`PositiveIntrospection` predicate under the natural extension of Definition 11
to singleton-image targets. Under the source's standing requirement that the
Boolean functions in this subsection take both values, the universal event's
characteristic is inadmissible, so Corollary 25 is not closed under its own
construction. The published 2018 book chapter does not restate this section and
therefore supplies no alternative definition.

**S5 discussion in the paper (do not over-read):**

- “Knowledge axiom” of S5 ≈ Cor. 19 **when `W` refines `Γ`**.
- **Distribution axiom of S5 fails** for physical knowledge: Cor. 20(ii) gives
  truth of `Γ₂`, not knowledge of `Γ₂`. The paper constructs counterexamples
  (Ex. 9). Reason given: weak inference looks at **counterfactual** setups.
- **Logical omniscience fails:** knowing `A` and that `A` implies `B` makes `B`
  true (under refinement hyps) **without** the agent knowing `B`.
- **Positive introspection is false as printed.** The exact Cor. 25 predicate is
  named and refuted, rather than transferred to `Knowable`.
- **Negative introspection** is discussed; do not claim it until a displayed
  theorem is pinned (this map does **not** treat it as a first target).

The implemented epistemic cluster stops after the Corollary 25 boundary. It
does not identify physical knowledge with `Knowable` or claim an S5 model.

---

## 3. Inference complexity and Kraft — measure before calling cheap

**Locator:** §III.2. Builds on a **size** of a setup (or value) relative to a
measure `μ` on `U`:

`ℳ_{μ;Γ}(γ) ≜ −ln μ(Γ⁻¹(γ))`  
(with a difference-of-logs convention if `μ(U) = ∞`).

**Def. 7 — inference complexity.** If `X(U)` and `Γ(U)` are countable and
`𝒟 > Γ`,

`𝒞_μ(Γ; 𝒟) ≜ ∑_{δ ∈ 𝒫(Γ)} min_{x : X=x ⇒ Y=δ(Γ)} ℳ_{μ,X}(x)`.

`μ` is typically a probability or a **semi-measure**. A max-over-probes variant
is left to future work in the paper.

**Def. 8 — halting setup.** `(X, Y)` **halts** at `x` iff `X = x` forces `Y` to
a **single** value. The device is **total / recursive** iff it halts at every
realized `x`, iff `X` refines `Y`.

**Def. 9 — prefix-free device.** Given semi-measure `μ`,

`∑_{x : 𝒟 halts on x} 2^{−ℳ_{μ,X}(x)} ≤ 1`.

The paper then **invokes Kraft’s inequality**: if the device is prefix-free,
there is a prefix-free code for the halting setups. That is a **citation of
Kraft**, not a claim of the paper. Mathlib's `kraft_mcmillan_inequality` is the
converse direction (code to inequality). See clash 22.

**Prop. 13 — invariance-style bound.** If `𝒟₁ ≫ 𝒟₂` and `𝒟₂ > Γ` (`Γ(U)`
finite), the difference of complexities is bounded by `|Γ(U)|` times a max-min
of `ℳ` differences along strong-inference fibres. Analog of the Kolmogorov
invariance theorem; **no entropy** in the statement. Mechanized as 2008
Theorem 4 at the measure length.

---

## 4. Entropy-dependent proposition

**Prop. 12.** If `μ` is a **probability distribution**, `Γ(U)` countable, and
`𝒟 > Γ`, then

`𝒞_μ(Γ; 𝒟) ≤ |Γ| × H_μ(X)`

where `H_μ(X)` is Shannon entropy of the pushforward of `μ` under `X`.

**False as printed** — clash 23. `entropyOn` is the `H_μ(X)` the proposition
names; no external entropy library is used. The printed proof is a short chain
of inequalities on `ℳ` and `log μ` whose last step needs `μ(x) ≥ 1/|Γ|` at every
setup value.

---

## 5. What 2018 also contains outside the knowledge-operator track

Every numbered item, displayed equation, worked example and prose claim is a
row in [section 0](#0-complete-source-inventory), with a status and a reason.
That table, not this section, is the inventory.

---

## 6. Current boundary

Mechanized: literal `PhysicallyKnows` (`ξ`, `W`, clauses i–iii) over the 2008
`InferenceDevice`, with physical knowledge ⇒ `WeaklyInfers`; Lemma 17,
Proposition 18, Corollaries 19–24, Corollary 3's three-function engine, the
complexity and Kraft material, and executable Definition 11 / Example 9 models.

Refuted rather than proved: Proposition 12, Corollary 25 and Example 6.
Repaired: Corollary 21(ii), the `|U| > 3` sentence after Definition 10, and the
weaker knowledge operator after Example 9. The valid definitions and repairs are
public; no false printed claim is a theorem here.

The deliberate stop: nothing is identified with `Knowable`. Transports between
the two exist in `AISafetyAtlas.Knowledge.Devices` under explicit hypotheses, and
the non-identification is witnessed in both directions.

## 7. Opportunity-space qualifier

“Large” means **a large class of models that can be encoded after an adapter**,
not drop-in reuse of existing atlas modules. The 2018 knowledge operator
**widens** that class (selector + `W` + epistemic consequences) rather than
merely enlarging the 2008 API. Application adapters still supply embedding,
time, and intervention semantics.

*End of statement map.*
