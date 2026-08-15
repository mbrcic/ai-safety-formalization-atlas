# Wolpert 2008 — inference devices (BY-024)

Source pinned and transcribed for `AISafetyAtlas.Inference`. Every statement in
the transcription table is checked against the source text.

## Source

D. H. Wolpert, *Physical limits of inference*, Physica D: Nonlinear Phenomena
237(9):1257–1281, July 2008. `doi:10.1016/j.physd.2008.03.040`.
Preprint: [arXiv:0708.1362](https://arxiv.org/abs/0708.1362), submitted 2007-08-10,
last revised 2008-10-23 (v2). **Read from the v2 full text**, which the arXiv record
describes as the updated version of the Physica D paper.

Every statement in the transcription table has been checked against **both the
preprint and the published article**: the author's LaTeX PDF of v2, the ar5iv/arXiv
HTML conversions of v2, and the Elsevier Physica D typeset article.

The published article has now been read and cross-checked against the disputed
numbered and prose statements. No statement-level change affecting this encoding
was found: the inventory and the recorded source defects are also present in the
journal version. The preprint remains useful as the more searchable rendering;
the journal PDF is the publication authority. See clash 16. No companion reference
was checked.

Registry row `BY-024` cites this as `survey-ref-005`, alongside `survey-ref-053`
(Wolpert 2001, *Computational capabilities of physical systems*), `survey-ref-054`
(Wolpert 2018, *Constraints on physical reality arising from a formalization of
knowledge*) and `survey-ref-055` (Devereaux et al.). **Only `survey-ref-005` is
transcribed in this 2008 map.** The 2018 paper is mapped separately in
[`wolpert-2018-knowledge.md`](wolpert-2018-knowledge.md). The 2008 stochastic
layer also mechanizes the probabilistic and algebraic core used by 2018
Proposition 11 in a sharper pointwise form. It does not expose the published
maximum-bound statement itself; see clash 18. Proposition 6 is graded
`SOURCE-EXACT`, not `ASSUMED-STEP`: the step the 2008 source asserts without
derivation — MI-distinguishability `1` implies independence — is proved here from
the equality case of Gibbs' inequality, so nothing is assumed on its behalf.

## What the paper is

The paper's first claim is structural: physical devices that perform observation,
prediction, or recollection share one mathematical form — a pair of functions on a
set `U` of universes, a *setup* function and a *conclusion* function. Devices with
that form are *inference devices*. The impossibility results then hold whatever the
physical laws are, since nothing beyond the pair structure is assumed.

## Transcription table

| Source | Statement | Lean | Status |
|---|---|---|---|
| Def 1 | device = pair `(X, Y)`, `Y` onto `𝔹` | `InferenceDevice` | **SOURCE-EXACT** |
| Def 2 | probe of `A`: onto `𝔹`, `1` at exactly one argument, `\|A\| ≥ 2` | `IsSourceProbe` | **SOURCE-EXACT**. `IsProbe` is the working predicate in every consumer; `surjective_of_isProbe`, `isSourceProbe_iff` and `weaklyInfers_iff_sourceProbes` show the two agree on every range the source admits — clash 12 |
| Def 3 | weak inference, `C > Γ` | `WeaklyInfers` | **SOURCE-EXACT**. `weaklyInfers_iff_imageProbes` proves that quantifying over ambient probes agrees with the source's `π(Γ)` on the image |
| Def 4 | setup distinguishability | `Distinguishable` | **SOURCE-EXACT** |
| Def 5 | strong inference, `C₁ ≫ C₂` | `StronglyInfers` | **SOURCE-EXACT** |
| Def 8 | control and semi-control | `Controls`, `SemiControls` | **SOURCE-EXACT** |
| Prop 1(i) | **one** device infers a whole family `{Γᵢ}` | `separatingDevice`, `separatingDevice_weaklyInfers`, `exists_weaklyInfers_family_of_two_values_on` | **SOURCE-EXACT** in the source's family form |
| Prop 1(ii) | every device fails some binary function | `not_weaklyInfers_own_concl`, `exists_not_weaklyInfers` | **SOURCE-EXACT** |
| Cor 1(i) | family whose values are all attained on `W` | `exists_weaklyInfers_family_of_values_attained_on` | **SOURCE-EXACT** |
| Cor 1(ii) | *any* `Γ` is inferred by some device | `no_device_weaklyInfers_id_on_bool`, `Examples.…Enumerable.no_finDevice_weaklyInfers_id` | **REFUTED** — false without an extra hypothesis, refuted for **every** device of shape `FinDevice 2 2` by `decide`, not only for one witness, which is what an existential claim needs. **The author supplies the missing hypothesis himself in 2018**: Proposition 7(1) of arXiv:1711.03499v3 states the same existence claim for `\|Γ(U)\| ≥ 3`, and the countermodel here sits at `\|Γ(U)\| = 2`. See below, clash 14, and clash 20 |
| Cor 2 | `\|X(U)\| > 2` iff `C` infers something, when `X` fine-grains `Y` | `weaklyInfers_iff_three_setups`, `not_weaklyInfers_of_at_most_two_setups` | **SOURCE-EXACT**. The `←` direction is stated for an **arbitrary** target range, so the source's "there is a function that `C` infers" is covered; the packaged `iff` names a `Bool` witness because that is what the forward construction builds |
| Thm 1 | no two distinguishable devices weakly infer each other | `not_infersDevice_both_of_distinguishable` | **SOURCE-EXACT**, and stronger than printed on constant-setup pairs — clash 13 |
| Thm 2(i) | `C₁ ≫ C₂` and `C₂ > Γ` ⇒ `C₁ > Γ` | `weaklyInfers_of_stronglyInfers` | **SOURCE-EXACT** |
| Thm 2(ii) | `≫` is transitive | `stronglyInfers_trans` | **SOURCE-EXACT** |
| Thm 2, unnumbered third sentence | `C₁ ≫ C₂` ⇒ `C₁ > C₂` | `infersDevice_of_stronglyInfers` | **SOURCE-EXACT** |
| Prop 2(i) | *"There is a device `C₂` such that `C₁ ⋙̸ C₂`"* | `exists_not_stronglyInfers` | **SOURCE-EXACT** |
| Prop 2(ii) | a device strongly inferring `C₁` exists when every fibre exceeds two states | `exists_stronglyInfers_of_large_fibres` | **SOURCE-EXACT** — named agree/disagree/spare points on each fibre; a different construction from the appendix's stitched partial devices, same claim |
| Thm 3 | no two devices strongly infer each other | `not_stronglyInfers_both` | **SOURCE-EXACT** |
| — | no device strongly infers itself | `not_stronglyInfers_self` | **SOURCE-EXACT** (immediate corollary) |
| — | control implies weak inference (§7 prose) | `weaklyInfers_of_controls` | **SOURCE-EXACT** |
| — | no device controls itself (§7 prose) | `not_controls_own_concl` | **SOURCE-EXACT** |
| — | no two distinguishable devices control each other (§7 prose) | `not_controls_both_of_distinguishable` | **SOURCE-EXACT** |
| Thm 5 | mutual semi-control ⇒ identical setup partitions | `setup_partition_eq_of_semiControls_setup` | **SOURCE-EXACT**, and proved **without the axiom of choice** the source uses |
| Cor 3(i) | mutual weak inference is symmetric under mutual semi-control | `infersDevice_comm_of_semiControls_setup` | **SOURCE-EXACT** |
| Cor 3(ii) | neither device strongly infers the other (`¬A ∧ ¬B` under mutual semi-control) | `not_stronglyInfers_either_of_semiControls_setup` | **SOURCE-EXACT** — both directions separately, **not** Thm 3's `¬(A∧B)` |
| Cor 3(iii) | neither controls the other's setup | `not_controls_other_setup_of_semiControls_setup` | **SOURCE-EXACT** |
| §7 prose | control implies semi-control | `semiControls_of_controls` | **SOURCE-EXACT** |
| §7 prose | strong inference implies semi-control of the target setup | `semiControls_setup_of_stronglyInfers` | **SOURCE-EXACT** |

## Encoding decisions, and why each is faithful

**1. `𝔹 = {-1, +1}` becomes `Bool`.** A renaming of a two-element codomain. The
source's identity probe `f(y) = y` is `id`, and its negation probe `f(y) = -y` is
`not`; `isProbe_id` and `isProbe_not` record exactly that. The proof of Theorem 1
turns on `Y₁(u*) = Y₂(u*) = -Y₁(u*)`, which becomes `b = !b`.

**2. Probes are a predicate on functions, and carry no decidability requirement.**
`IsProbe f a` says `f` is `true` at `a` and nowhere else, and Definition 3
quantifies over probe *functions* — which is what the source's `∀ f ∈ π(Γ)` does.
`WeaklyInfers`, `StronglyInfers` and `Controls` carry no `DecidableEq`. `probe` is
the canonical Kronecker delta for ranges that do have decidable equality, so
finite models stay executable, and `semiControls_of_controls` is the constructive
specialization for decidable target ranges. `semiControls_of_controls_classical`
is the unrestricted source-faithful form and uses the generic probe-existence
theorem; it needs a probe at the controlled value to exist.

The source additionally requires the probed set to have at least two elements, so
the map is genuinely onto `𝔹`, guaranteed there by a global stipulation. That is not
imposed here.

Two questions this raises were checked rather than assumed.

*Can the `∀ f, IsProbe f γ → …` be satisfied vacuously, by a target with no probe?*
No. `exists_isProbe` proves that `decide (· = a)` is a probe at every point of every
type, so the quantifier always ranges over something and any proof of weak inference
must face a real probe. That is what makes dropping the stipulation safe rather than
merely tidy.

*The source probes the image `Γ(U)`, while Lean quantifies over probes on the ambient
`G`.* These agree: a probe on the ambient type restricts to one on the image, an image
probe extends by `false`, and `IsProbe.eq_of_isProbe` shows a probe is determined by
the point it selects, so there is nothing to choose between. The ambient form is used
because it needs no subtype plumbing.

One edge remains: on a **singleton** ambient type the unique-true condition no longer
forces surjectivity onto `Bool`, so `IsProbe` there admits a map the source would not
call a probe. No statement in this module is affected — each applies the definitions to
a surjective `Bool`-valued conclusion function.

**3. `∀ x` means "over realized setup values".** In Definitions 4, 5 and 8 the source
writes `∀ x₁, x₂` without repeating the `∈ X(U)` it makes explicit in Definition 3.
The realized reading is forced: over the whole setup type, no device with an unused
setup value could ever be distinguishable from another. It also makes Theorem 1
stronger, since more device pairs satisfy the hypothesis.

The source's global two-value stipulation is dropped for **setup** functions as well
as targets. Consequence: a constant-setup device is distinguishable from itself
(`Examples.Inference.Device.constSetup_distinguishable_self`), which the source
denies. Theorem 1 applied to that pair only recovers Proposition 1(ii). Recorded
as an undocumented-then-documented strengthening, not as a source match.

**4. "Identical partitions" is kernel equality.** Theorem 5's conclusion is stated
as `C₁.setup w = C₁.setup w' ↔ C₂.setup w = C₂.setup w'`. Two functions induce the
same partition exactly when their same-fibre relations agree, so this is the source's
statement up to the relabelling of setup ranges the source itself describes.

**5. `W` is a characteristic function.** Proposition 1(i) takes `inW : U → Bool`
rather than an arbitrary subset, so the formal statement is about a decidable subset.
Harmless for the finite models here, and it keeps the construction executable, but it
is a representation restriction on the general source proposition. The source's
`|Γᵢ(W)| ≥ 2` likewise appears as explicit witnesses rather than a cardinality.

**6. `Setup` is a structure field, not a parameter.** So that devices with different
setup types appear in one statement, which every pairwise result requires.

**6b. The family is homogeneous.** The source's `{Γᵢ}` is a set of functions on `U`
whose ranges need not be identified — indeed the paper motivates probes partly as a
way to avoid identifying them. The Lean family is `Γ : ι → U → G`, one shared
codomain. The construction is target-independent so nothing is lost for a family that
does share a codomain, but a heterogeneous family is not expressible as stated.

**7. Proposition 1(i) is stated in the source's family form.** The source claims a
single device infers *every* member of `{Γᵢ}`, which is strictly stronger than a
device per target. The construction is therefore exposed as `separatingDevice`,
independent of any target, with `separatingDevice_weaklyInfers` applying to each
member; the family statement follows immediately.

## One strengthening over the source

The paper proves Theorem 5 by using the axiom of choice to select, for each value of
one device's setup, a value of the other's. The proof here needs no such selection:
it shows directly that the block containing any state is common to both partitions.
`#print axioms` reports the measured profile, not a remembered one:

| Declarations | Axioms |
|---|---|
| Prop 1(ii), Thms 1, 2, 3, 5, Cor 3(ii), control transports, Example 5's three general statements | **none** |
| `Mimics.trans`, `Copies.trans` | `Quot.sound` |
| Cor 3(i), Lemma 1 (`lemma1_reducedForm_iff_admissible`) | `propext`, `Quot.sound` |
| `semiControls_of_controls` | `propext` |
| everything classical: `separatingDevice_weaklyInfers`, `exists_isProbe`, Prop 1(i) / Cor 1(i) wrappers, Cor 3(iii), `semiControls_of_controls_classical`, `weaklyInfers_iff_sourceProbes`, Thm 4, Thm 7(ii), Prop 6, §8 entropy lemmas | `propext`, `Classical.choice`, `Quot.sound` |

The pattern is unchanged by the §5–§9 expansion: **refuting** inference needs no
axioms, **constructing** a device, a probe, or a real-analytic bound is classical.

Constructing a device or a probe is where the classical content sits; refuting one
never needs it. The statements are unchanged. Anything added here should re-run
`#print axioms` rather than assume.

| Def 6 | inference complexity `𝒞(Γ∣C)` | `inferenceComplexitySum` (both ranges free), `inferenceComplexityOn` (setup range free), `inferenceComplexityMeasure` (general measure), `inferenceComplexity` (length-parametric core) | **SOURCE-EXACT** — Printed: *"Let `C` be a device and `Γ` a function over `U` where **`X(U)` and `Γ(U)` are countable** and `C > Γ`"*, with the display `∑_{f ∈ π(Γ)} min_x [ℒ(x)]` and **no `\|Γ(U)\|` factor** — that belongs to Theorem 4. Both ranges are free: `inferenceComplexityOn` takes the printed `min_x` as an `sInf` over a set of setups, and `inferenceComplexitySum` sums over the whole target type with `∑'`. `inferenceComplexitySum_eq` recovers `𝒞(Γ ∣ C)` on the finite instance under the source's own `C > Γ`. `ℒ` is a parameter, so counting measure and `−ln μ(X⁻¹(x))` are both instances |
| Thm 4 | complexity difference bounded by `\|Γ(U)\|` times emulation cost | `inferenceComplexityOn_le_of_stronglyInfers` (setup ranges free), `inferenceComplexityMeasure_le_of_stronglyInfers` (general measure), `inferenceComplexity_le_of_stronglyInfers` (length-parametric core) | **SOURCE-EXACT** — Printed: *"`Γ` a function over `U` where **`Γ(U)` is finite**, `C₁ ≫ C₂`, and `C₂ > Γ`"*, so the finite target range is the source's own hypothesis. The setup ranges are free at `inferenceComplexityOn_le_of_stronglyInfers`, which derives the per-probe bound from the printed premises rather than assuming it: `C₂ > Γ` makes each answering set nonempty and `C₁ ≫ C₂` makes each emulation set nonempty. Attainment of the printed `min_{x₁}` and `max_{x₂}` is hypothesised because writing them asserts it. One-sided **in the source**: the bars are a cardinality, see clash 5 |
| Def 7 | mimicry / copies | `Mimics`, `Copies` | **SOURCE-EXACT** — stated across two universes `U`, `Û`, as the source requires. Prose consequences: `Mimics.trans`, `Copies.symm`, `Copies.trans` |
| Lemma 1 | reduced forms of realities `=` admissible tuple families | `lemma1_reducedForm_iff_admissible` | **SOURCE-EXACT** — `K₁ = K₂` proved in both directions, including the source's nonempty-function-family condition, with `FullReality`, `reducedForm`, `AdmissibleTuples`, `IsReducedForm` |
| Prop 3(i) | pairwise-distinguishable weak-inference 3-cycle | `exists_pairwise_distinguishable_weak_cycle` | **SOURCE-EXACT** — one named `cycle3Table` |
| Prop 3(ii) | no mutually distinguishable weak-inference cycle | `not_mutually_distinguishable_weak_cycle` | **SOURCE-EXACT** — `MutuallyDistinguishable` is the source's own prose definition of *mutually (setup) distinguishable*. `DeviceReality` is `n` devices over `U`, not an exhaustive reality, so the Lean hypothesis is the source's restricted to the cycle and the theorem implies the source's. Clash 7 |
| Prop 3(iii) | no strong-inference cycle | `not_strong_inference_cycle` | **SOURCE-EXACT** — walk + Thm 3 |
| Prop 4 | unique root of a finite weakly-connected strong-inference graph | `unique_strong_root` | **SOURCE-EXACT** — The phrase *"over `D`"* occurs twice in the LaTeX source, and in the conclusion — *"has one and only one root **over `D`**"* — it can only mean *restricted to `D`*. Reading the hypothesis the same way makes it the induced subgraph, which is the proof and is what `StrongGraphWeaklyConnected` transcribes. `htwo` is the paper's **own** §1.2 two-value stipulation, reintroduced exactly where the source uses it — reinstating a printed hypothesis locally is not a narrowing. Clash 7 |
| Prop 5(i) | finite copies may be distinguishable with one-way weak inference | `exists_copies_distinguishable_weak` | **SOURCE-EXACT** — the paper's five quadruples as `finiteCopyTable` |
| Prop 5(ii) | copies may strongly infer only if both setups are infinite | `exists_copies_stronglyInfers_infinite`, `copies_stronglyInfers_not_finite` | **SOURCE-EXACT** — existence and necessity |
| Def 9 | weak inference with covariance accuracy | `inferenceAccuracySupOn` (setup range free), `inferenceAccuracyOn` (general measure), `inferenceAccuracy` (finite instance) | **SOURCE-EXACT** — Printed: *"Let `P(u ∈ U)` be a probability measure, `Γ` a function with domain `U` and finite range, and `ε ∈ [0.0, 1.0]`"* — finiteness on the **target** only, nothing on `X(U)`. `inferenceAccuracySupOn` states the printed `max_x` as a supremum over the positive-mass setups and needs only that one such value exists, which is what `max_x` needs to denote; `accuracySupOn_eq_of_isGreatest` says it *is* the printed maximum wherever that exists. No measurability hypothesis. The printed `ε` is unused in the display — clash on Definitions 10 and 11 records the same slip |
| Def 10 | mutual-information distinguishability | `miDistinguishabilitySum` (setup ranges free), `miDistinguishabilityOn` (general measure), `miDistinguishability` (finite instance) | **SOURCE-EXACT** — Printed: *"Let `P(u ∈ U)` be a probability measure, and `ε ∈ [0.0, 1.0]`"* and the display `1 − M_P(X₁,X₂)/(H_P(X₁)+H_P(X₂))` — **no range hypothesis at all**. `entropySum` states the entropy as a `∑'` over the whole value type, so `miDistinguishabilitySum` carries no finiteness. Finiteness of the **entropy** remains forced, since the printed ratio is `∞/∞` where an entropy diverges, and that is the largest domain on which the display denotes. `ε` is again declared and unused |
| Def 11 | counting distinguishability | `countingDistinguishabilityOn` (general), `countingDistinguishability` (finite instance) | **SPECIALIZED** — over an **arbitrary** `U` and, as printed, with **no measure argument**: `P` is named in the preamble and absent from the display. The remaining delta is finite rather than the source's countable setup ranges. Clash 19. **The only numbered `SPECIALIZED` row, and it is forced.** Printed: *"Let `P(u ∈ U)` be a probability measure, and `ε ∈ [0.0, 1.0]`"* with the display `1 − (count of realized pairs)/(\|X₁(U)\| × \|X₂(U)\|)`. On a countably infinite setup range the denominator is infinite and the ratio is `∞/∞`, so the printed formula denotes nowhere beyond finite ranges. No totalization recovers it without choosing mathematics the source does not write. `ε` is declared and unused, as in Definition 10 |
| Prop 6 | product of accuracies, MI-distinguishability 1 | `prop6_half_of_miDistinguishabilityOn_eq_one` (general measure), `prop6_half_of_miDistinguishability_eq_one` (finite instance), `mutualInfo_eq_zero_iff` | **SOURCE-EXACT** — Printed: *"Let `P` be a probability measure over `U`, and `C₁` and `C₂` two devices whose mutual-information distinguishability is 1, **where `X₁(U) = X₂(U) = 𝔹`**"*. The two-valued setup ranges are the **source's own hypothesis**, so the Lean's two realized setup values per device are printed scope, not a narrowing. Measurability and two side conditions — positive fibre mass and `H₁+H₂ ≠ 0` — are **forced**: the printed conditional expectations and the printed ratio do not denote without them. The step the source asserts without derivation — MI-distinguishability `1` implies independence — is proved here from the equality case of Gibbs. Clashes 3 and 19 |
| Def 12 | self-aware device `(X,Y,Q)`, `Y⊗Q` surjective | `SelfAwareDevice`, `FunctionValuedSelfAware`, `FunctionValuedSelfAware.toSelfAware`, `SelfAwareDevice.toFunctionValued` | **SOURCE-EXACT** — The encoding is labels plus an evaluation map where the source's `Q(U)` is a set of binary functions. `FunctionValuedSelfAware` is Definition 12 read literally, with `Y ⊗ Q` onto `𝔹 × Q(U)` — the product with the **image**, as printed — and `toSelfAware` represents it, with `toSelfAware_ask` proving the source's `Q̄` survives and `evalImage_toSelfAware` proving the evaluated questions are exactly the printed `Q(U)`. `toFunctionValued` is the converse, and the round trip is the identity on both. Nothing is added and nothing is lost, so the grade follows the representation rather than the encoding |
| Def 13 | intelligible / infallible | `Intelligible`, `Infallible` | **SOURCE-EXACT** |
| Thm 6(i) | infallible + semi-controls `Q` ⇒ weakly infers every intelligible `Γ` | `weaklyInfers_of_infallible_semiControls_question` | **SOURCE-EXACT** — hypotheses inhabited by `Examples.…saDev`, so the theorem is not vacuous |
| Thm 6(ii) | plus semi-control of `(Q,X₂)` surjective ⇒ strongly infers | `stronglyInfers_of_infallible_semiControls_question_setup` | **SOURCE-EXACT** — the extra hypothesis is surjectivity onto `Q₁(U) × X₂(U)`, the product of the two **images**, as printed. `Examples.…saStrongDev_stronglyInfers_target` inhabits all hypotheses; clash 10 |
| Thm 7(i) | mutual intelligibility of `P`, `P′` ⇒ equal cards | `thm7_mk` (unrestricted), `thm7_card` (finite instance) | **SOURCE-EXACT** — `thm7_mk` states the source's (i) without finiteness, equating `Cardinal.mk` with antisymmetry by Schröder–Bernstein. `thm7_equiv` states the conclusion as `Nonempty (· ≃ ·)`, which puts the two question types and the two label types in **four independent universes**, since `Equiv` is cross-universe where `Cardinal.mk` is not. Only `DecidableEq` on the label types remains, and it is classically free. Clash 8 |
| Thm 7(ii) | finite case: `Q′ = π(P) = π(Q)` and `Q = π(P′) = π(Q′)` | `thm7_ii_chain` (from `thm7_ii`, `probeImage_eq_of_card_eq`, `eq_of_apply_eq_of_card_eq`) | **SOURCE-EXACT** — all four printed equalities, with the cardinality equalities discharged from `thm7_card` rather than assumed, so (ii) follows from (i) as in the source |
| Cor 4 | no finite mutual device-intelligibility | `not_mutually_deviceIntelligible_of_finite` | **SOURCE-EXACT** — `\|(Y,Q)(U)\| = 2\|Q(U)\|` |
| Cor 5 | distinguishable infallible pair cannot have both conclusions intelligible | `not_both_concl_intelligible` | **REPAIRED** — the printed *"if in addition they infer each other"* is vacuous under Thm 1; Lean drops it, clash 11 |
| Def 14 | `C` corrects `D` | `Corrects` | **SOURCE-EXACT** |
| Prop 7 | some self-aware device is uncorrectable | `exists_not_corrects`, `four_states_of_two_questions`, `four_le_card_of_two_questions` | **REPAIRED** — the printed `{Y,¬Y}` witness fails Def 12 surjectivity; the constantly-false replacement satisfies Def 12 in the Atlas's relaxed model but not the paper's global two-image-value convention, clash 2. `pair_surjective` makes `u ↦ (Y(u), Q(u))` onto `𝔹 × Q(U)`, so an **admissible** self-aware device — question map with at least two values, as §1.2 requires — needs four states: `four_le_card_of_two_questions`. On `\|U\| ∈ {2, 3}` no admissible self-aware device exists at all — `question_subsingleton_of_card_lt_four`, `question_constant_of_card_lt_four`, and `no_admissible_selfAware_on_bool` on the smallest universe — so the printed existential has nothing to range over and **is false there**. An admissible self-aware device does exist once four states are available: `Examples/Inference/SelfAwareComplexity.saDevice`, which is also infallible, semi-controls its question and finds its target intelligible. The positive half is proved at the printed quantifier: `exists_admissible_not_corrects_of_four_states` takes a device and `4 ≤ \|U\|` and nothing else — `a` and `b` come from `concl_surjective`, which also makes them distinct and supplies the straddling condition, and `c`, `d` from the states left once `{a, b}` is removed. The four-named-states form remains beneath it: `exists_admissible_not_corrects` builds, for every device over a universe with four distinct states, a self-aware device with a **two-valued** question map that the device cannot correct. **`D`'s device need not be `C`**. Choosing it freely, with `splitOn` as its conclusion so both of its fibres hold two of the four named states, makes `pair_surjective` available for *every* `C`; `crossOn` crosses it into two questions; and `tunedAsk` is chosen so that the agreement function is `¬Y_C`, which no fibre of `C` can report, since that would need `Y_C(w) = ¬Y_C(w)`. `uncorrectable` fails to be admissible only because it sets `D.toDevice := C`, and that is a property of the witness, not of the proposition |

## Worked models of positive hypotheses

A theorem whose hypotheses no model satisfies is true and says nothing.
`scripts/check_example_coverage.py` fails the cheap gate when a module declaring
public API is referenced by no example; that is module-level, so individual
declarations still need named models.

| Item | Model |
|---|---|
| `ContainsEveryTwoValuedBool` — the `\|U\| > 3` sentence's own hypothesis | `Examples/Inference/FunctionFamily.lean`: `U = Fin 4`, family indexed by the subtype of surjective `Fin 4 → Bool`, so the predicate holds by construction. This is a model in the printed `\|U\| > 3` regime — `conclInFamilyReality` sits at `\|U\| = 2` and its family is `id` alone. `stipulations` proves all four of the source's standing conventions rather than dropping them |
| Proposition 8 over a general measure | `StochasticGeneral.p6_prop8_general` |
| Proposition 11 over a general measure | `StochasticGeneral.p6_prop11_general` |
| `PrefixFree` — Definition 9 **as printed** | `Halting.not_prefixFree_haltingDevice`: the identity device on `𝔹` under the uniform measure **fails** the printed reading, while `base2_sum_eq_one` shows the base-consistent reading holds on the same device with sum exactly `1`. One device, one measure, opposite verdicts |
| `Ĉ` — `unionInferenceComplexity`, `answeringMass` | `UnionComplexity.uc_union_lt_min`: `Ĉ` charges `−ln 1 = 0` where the `min` form charges `ln 2`, so the *"natural modification"* modifies |
| `condEntropy` — `ℍ(U ∣ x)` | `ComplexityMeasure.condEntropy_fine` (`0` on singleton fibres) and `neg_condEntropy_coarse` |
| `sourceStochasticComplexity` — the printed `C̄_ε` | `ComplexityMeasure.sourceStochasticComplexity_value` = `−(2 ln 2)` at `ε = 1` |
| `selfAwareInferenceComplexity` — §9's `𝒟` — and `minQuestionLength` | `Examples/Inference/SelfAwareComplexity.lean`: `𝒟(Γ ∣ D) = −(2 ln 2)`, two probes each with a nonempty answering set of two-element fibres, so the value is neither `0` nor reached through the totalization. The device is also a source-admissible self-aware device — two question values over four states, which `four_le_card_of_two_questions` shows is the minimum |
| `FullReality.IsUniversalFull` — a **positive** model | `FunctionFamily.universalReality_isUniversalFull`. One device and one function, so clause 1 is vacuous; **clause 2 is not** — the device weakly infers the reality's function, which by Proposition 1(ii) cannot be its own conclusion, so the model has to separate them |

**Theorem 7(i)'s premise is satisfiable non-degenerately.** A witness with two or
more questions has to ask, as one of its own questions, every probe of the other's
question map. `saSelfProbe` is that device — its question at `q` is *"is my
question `q`?"*, so `eval q` **is** the probe of `Q` at `q`, and `Q` is
intelligible to it with `|Q(U)| = 2` against `saTrivial`'s `1`. Corollary 4 does
not block it because intelligibility here is of the question map alone, not of
the pair `(Y, Q)`. `thm7_mk`, the unrestricted cardinality form, is instantiated
by the same device.

Everything else with a positive hypothesis is inhabited: Theorem 1
(`row_infers_col`), Proposition 3(ii) (`mutualReality_mutuallyDistinguishable`),
Proposition 4 (`prop4_nonvacuous`), Theorem 6(i) and (ii) (`saDev`, `saStrongDev`),
Theorem 7(i) (`thm7_nonvacuous_two_questions`, `thm7_mk_nonvacuous`), Theorem 7(ii)
(`thm7_ii_nonvacuous`), Definition 14 (`saDev_corrects_saSelfProbe`), footnote 9's
variant (`saDev_correctsAlt_saSelfProbe`), Corollary 3 (`corollary3_nonvacuous`),
Corollary 24 (`corollary24_nonvacuous`), Definition 11 of the 2018 paper
(`knowsTrueWitness`), Proposition 6 in both layers
(`p6_half_from_printed_premise`, `p6_general_half`).

**Definition 14 has a positive witness.** `exists_not_corrects` (Proposition 7)
says some device *cannot* be corrected, which is consistent with `Corrects`
holding of nothing whatever. `saDev_corrects_saSelfProbe` inhabits it:
`saDev`'s question-`true` fibre reports the second bit, which is exactly
`Y₂ Q̄₂` for `saSelfProbe`. The same pair witnesses Definition 14 and footnote 9's
variant — two definitions on one model, and **not** a claim that either implies
the other.

**Section 5 is exercised.** Definition 6 totalizes to `0` wherever no setup answers
a probe — so a complexity of `0` proves nothing on its own.
`Examples/Inference/Complexity.lean` computes it on the Proposition 1(i) device,
whose identity setup makes every fibre a singleton and every length `−log 1 = 0`,
and `witness_answeringSet_nonempty` shows the value is reached through genuine
minima rather than through the totalization.

**Theorem 4 is attained, not merely satisfied.** `witness_thm4_tight` puts the
section-6 pair `fineDevice ≫ coarseForcedDevice` against `gamma4`, the target
that agrees with the coarse device's parity conclusion on `{0,1}` and disagrees
on `{2,3}` — the shape forced on it, since otherwise one of the two `Bool` probes
has no answering fibre and `coarseForcedDevice > gamma4` fails. Both sides of the
theorem then equal `2·log 2`:

| Quantity | Value | Why |
|---|---|---|
| `𝒞(Γ∣fineDevice)` | `0` | identity setup, singleton fibres, `ℒ = −log 1` |
| `𝒞(Γ∣coarseForcedDevice)` | `−2·log 2` | two probes, each answered only by a two-element fibre |
| `emulationCost` | `log 2` | `1` and `2` are the only fine setups whose conclusion agrees with the coarse one, and they lie in different coarse fibres |
| `\|Γ(U)\|` | `2` | `gamma4` is onto `Bool` |

An inequality that holds can hold because both sides are degenerate or because
the bound is loose. This one is met exactly, so the factor `|Γ(U)|` in the
source's statement cannot be reduced: the emulation cost is paid once per target
value, and here it is paid in full every time.

**And under a general measure.** `Examples/Inference/ComplexityMeasure.lean`
repeats it with `ℒ(x) = −ln μ(X⁻¹(x))` under the uniform measure on `Fin 4`.
Every length moves — `0 ↦ log 4`, `−log 2 ↦ log 2` — but both sides of Theorem 4
stay at `2·log 2`, because the bound compares lengths and the change of
normalisation shifts them all by the same constant. That is the substantive
content of the general-measure restatement being an instantiation rather than a
second theorem. The same example evaluates `measureLength`,
`inferenceComplexityMeasure`, `accurateSet` and `stochasticInferenceComplexity`.

## Interoperating with Mathlib's probability vocabulary

Section 8 is stated over a `Measure`, which is the source's generality — but it
said *independence* with `IndependentOn`, a predicate of this development, and
took its discrete data as `FinPMF`, a structure of this development. `Bridge.lean`
mapped **out** of those into `Measure`; nothing mapped in. A reader holding
`ProbabilityTheory.IndepFun` or a `PMF` — which is what a reader who did not
write this repository holds — could not discharge Proposition 6's hypothesis
without restating the setup.

`Inference/Stochastic/Interop.lean` closes it, with no new dependency:

| Claim | Declaration |
|---|---|
| `IndependentOn` **is** `IndepFun` on finite-range maps | `independentOn_iff_indepFun` |
| A Mathlib `PMF` on a finite universe **is** a `FinPMF` | `FinPMF.ofPMF` |
| …inducing the same measure, so every model transfers unchanged | `FinPMF.ofPMF_toMeasure` |

Both are exercised on the Proposition 6 model in
`Examples/Inference/StochasticGeneral.lean`, so the translation is not merely
stated. The reverse direction of the independence equivalence is immediate
(specialise to singletons); the forward one decomposes each preimage into fibres
indexed by the **product of the marginal ranges** rather than by the joint range,
because a pair of separately attained values need not be jointly attained — its
fibre is then empty, and independence makes exactly those terms vanish.

## How to check this table

For every row, put the printed statement and the Lean statement side by side. **If
the Lean statement does not mention every object the printed statement quantifies
over, the row is a component, not coverage** — grade it out of the inventory rather
than in.

Sweep the source's **prose** for definitions as well as claims. Numbered
environments are what a transcription table tracks, so anything defined in running
text is invisible to it. That is how *"mutually (setup) distinguishable"* — a
definition the paper gives in a sentence before Proposition 3 — is
`OutsideDistinguishable` in `Inference/Reality.lean`.

`scripts/check_wolpert_status_table.py` enforces the mechanical half of this: it
recomputes the tally from this table, fails when any other surface disagrees, and
rejects a row whose Lean column names no declaration that exists.

## Status vocabulary

| Status | Meaning |
|---|---|
| `SOURCE-EXACT` | The Lean statement is the printed statement up to notation. |
| `SPECIALIZED` | Faithful on a declared narrower domain (finite `U`, counting measure, finite index, product type for an image). |
| `REPAIRED` | The printed statement is defective; Lean proves the intended claim. Every one has a clash-note entry. |
| `ASSUMED-STEP` | A theorem about the source's objects, with one named step of the source's proof taken as a hypothesis rather than proved. |
| `REFUTED` | Machine-checked countermodel to the statement as written. |

A declaration that is only a **component** of a printed statement is not listed as
that statement.

## Coverage

The 2008 numbered inventory is Defs 1–14, Thms 1–7, Props 1–7, Cors 1–5, Lemma 1 —
**45 items** counting split parts, plus Theorem 2's unnumbered third sentence = **46 tracked statements**. Every one has a row.

| Status | Count |
|---|---|
| `SOURCE-EXACT` | 42 |
| `SPECIALIZED` | 1 |
| `REPAIRED` | 2 |
| `ASSUMED-STEP` | 0 |
| `REFUTED` | 1 |
| **not mechanized** | **0** |

Wolpert 2018 is a separate paper. Its first physical-knowledge cluster is mapped
and mechanized separately; it is not part of the 46-row tally above.

## Worked examples

The 46 numbered statements are not the whole paper. Section 2 and section 5 also
carry six worked examples; the denominator above counts the numbered statements
only, and the examples are tracked separately below. An example is not
automatically prose — 2018's Example 6, adduced to show a bound was sharp, is
**refuted**.

These six are counted separately from the 46; the tally above is unchanged.

| Source | Statement | Lean | Status |
|---|---|---|---|
| after Def 9 | *"if `P` is nowhere 0 and `C` weakly infers `Γ`, then `C` infers `Γ` with accuracy 1.0"* | `inferenceAccuracyOn_le_one`, `inferenceAccuracyOn_eq_one_iff`, `inferenceAccuracy_le_one`, `inferenceAccuracy_eq_one_of_weaklyInfers` | **SOURCE-EXACT** — Printed after Definition 9: *"if `P` is nowhere 0 and `C` weakly infers `Γ`, then `C` infers `Γ` with accuracy 1.0"* — the forward half only, with *"`P` is nowhere 0"* printed. Both halves hold at general measure: `inferenceAccuracyOn_le_one` with no hypothesis, and `inferenceAccuracyOn_eq_one_iff` with `hatom`, which is the printed nowhere-zero condition. 2018 states the two-sided form after its Definition 6 and it is proved there too. The nowhere-zero hypothesis does **more** work at general measure than in the finite case: `cov = 1` forces agreement only up to a null set, and `hatom` is what collapses that to the pointwise agreement `WeaklyInfers` asks for |
| §8 prose | `C̄_ε(Γ ∣ C) ≜ Σ_{f ∈ π(Γ)} min_{x : E_P(Y f(Γ) ∣ x) ≥ ε} [−ℍ(U ∣ x)]`: stochastic inference complexity | `sourceStochasticComplexity`, `condEntropy`, `neg_condEntropy_eq_setupLength_of_uniform`, `sourceStochasticComplexity_eq`, `stochasticInferenceComplexity`, `accurateSet` | **SPECIALIZED** — Definition 6 with *exact* answering relaxed to *accurate to within `ε`*. The printed display is `∑_{f ∈ π(Γ)} min_{x : E_P(Y f(Γ) ∣ x) ≥ ε} [−ℍ(U ∣ x)]`, *"assuming the sum exists for `ε`"* — so the length is the **discrete** conditional Shannon entropy, and `dμ` enters only in the following bridge sentence. `condEntropy` is `ℍ(U ∣ x)` and `sourceStochasticComplexity` is `C̄_ε` with `ℓ` fixed at `−ℍ(U ∣ x)`. `neg_condEntropy_eq_setupLength_of_uniform` proves the source's *"these two definitions of the length of `x` are the same"* — at counting measure the printed `P ∝ dμ` on a fibre is uniformity, and then `−ℍ(U ∣ x) = ℒ(x)` — and `sourceStochasticComplexity_eq` is the printed `ε = 1` identity `C̄₁ = 𝒞`. `relativeLength` instantiates `InformationTheory.klDiv` at the conditional law on a setup fibre, and `relativeStochasticComplexity` is `C̄_ε` at that length — a generalization *beyond* the print rather than the way to reach it. **2008 only** — the 2018 paper displays no `C̄_ε`. **Remaining delta:** `condEntropy` is over a `FinPMF`, hence `[Fintype U]`, where the print needs only that `ℍ(U ∣ x)` be finite |
| §9 prose | `𝒟(Γ ∣ (X,Y,Q))`: self-aware inference complexity — Definition 6 with the answering condition moved from the conclusion to the **question** | `selfAwareInferenceComplexity`, `questionAnsweringSet`, `minQuestionLength`, `concl_eq_of_mem_questionAnsweringSet` | **SPECIALIZED** — a displayed definition announced by no numbered environment. `ℒ` is a parameter as in `inferenceComplexityTotal`, so counting measure and `−ln μ(X⁻¹(x))` are both instances. `Q = f(Γ)` equates a question with a function while questions here are a label type plus `eval` (clashes 9–10); the pointwise reading `∀ v, eval (question u) v = f (Γ v)` is taken, which is the one `Intelligible` already uses and the only one under which the source's own *"`Γ` intelligible to `D`"* hypothesis supplies the questions the minimum ranges over. The source's standing hypotheses for the display — infallible, semi-controls `Q`, `Γ(U)` countable, `Γ` intelligible — are **not** attached, so the object is defined for every self-aware device; `concl_eq_of_mem_questionAnsweringSet` recovers the one that matters, that an infallible device asking the probe also answers it. `questionAnsweringSetOn` states the answering condition as a set, `minQuestionLengthOn` the printed `min` as an `sInf`, and `selfAwareInferenceComplexityOn` is `𝒟` with no finiteness on the setup range; `minQuestionLengthOn_eq` recovers the `Finset` form. `FunctionValuedSelfAware` and its round trip make the label-versus-function representation a theorem. **Remaining delta:** `questionAnsweringSet` is a `Finset`, so the printed `min` over answering setups still carries a finite setup range, where §9 inherits Definition 6's *countable* one |
| after Def 7 | universal device: strongly infers every other device and weakly infers every function of the reality; *"Thm. 3 means that no reality can contain more than one universal device"* | `IsUniversal`, `universal_unique`, `isStrongRoot_of_isUniversal`, `subsingleton_isUniversal` | **SOURCE-EXACT** — the printed definition has two clauses and uniqueness uses only the first, so `IsUniversal` carries only the strong-inference clause and rules out more devices than the source's argument does. The paper calls this and Proposition 5 the *"monotheism theorem"*. `FullReality.IsUniversalFull` carries *"strongly infer all other devices"* **and** *"weakly infer all functions in that reality"*, stated over `FullReality`, which has the `{Γ_β}` that `DeviceReality` lacks; `FullReality.isUniversalFull_unique` is the uniqueness claim at the printed definition, inherited rather than reproved — the argument never used the second clause. `IsUniversal` remains as the one-clause form, and `universal_unique` on it is strictly stronger than the source's. The adjacent sentence *"no reality with `\|U\| > 3` can have a universal device if the reality contains all functions defined over `U`"* is **`REPAIRED` in the 2018 map**: `not_isUniversalFull_of_concl_mem` and `not_isUniversalFull_of_containsEveryTwoValuedBool` prove it with no cardinality bound, and clash 28 records why the printed citation of Proposition 7(2) cannot reach it |
| after Def 6 | `Ĉ(Γ ∣ C)`: remove the min, charge the union of all answering fibres | `unionInferenceComplexity`, `answeringMass`, `answeringMass_eq_sum`, `answeringMass_eq_sum_exp` | **SPECIALIZED** — a displayed definition with a displayed equality, announced by no numbered environment. 2018 prints the identical formula after its Definition 7, so one declaration transcribes both. The printed equality is the source's own disjoint-fibre remark; **measurability** is what makes it an equality rather than a `≤`, and the source does not state it. `answeringMassOn` takes the union over `answeringSetOn` — a union needs no finite index — and `unionInferenceComplexityOn_eq` shows the two agree wherever both are defined. The target range stays finite, as the display's sum over `Γ(U)` requires. **Remaining delta is the measure class:** 2008 admits an arbitrary `μ`, so counting measure on an infinite `U` gives a fibre union of infinite mass, which `massOn`'s `ENNReal.toReal` sends to `0` — and the source's own footnote-8 convention there is a limit of differences of logarithms, which this development does not model. 2018 supplies a semi-measure, mass at most one, where that case cannot arise, and that row is `SOURCE-EXACT` |
| Example 1 | general-purpose observation device: scientist, apparatus, configuration `χ`, question `Q` | — | **INTERPRETATION** — a motivating physical scenario. The mathematical content is Definition 3, which §3 states by abstracting exactly this example |
| Example 2 | the same apparatus with the scientist removed | — | **INTERPRETATION** — a variant of Example 1 in the same register; the paper's point is that the formalism does not depend on an observer being animate |
| Example 3 | general-purpose prediction device | — | **INTERPRETATION** — Example 1 with `t₃ < t₂`; no separate claim |
| Example 4 | general-purpose recording and recollection device | — | **INTERPRETATION** — Example 1 in the memory direction; no separate claim |
| Example 5 | grid of yellow/purple particle pairs: the two devices are distinguishable, `C_p > C_y` under an agreeing and an anti-agreeing row, and therefore not conversely | `rowSpinDevice`, `colSpinDevice`, `rowSpinDevice_distinguishable_colSpinDevice`, `rowSpinDevice_infersDevice_colSpinDevice`, `not_colSpinDevice_infersDevice_rowSpinDevice` | **SOURCE-EXACT** — and **wider than printed**. Proved for an arbitrary index pair in their own universes, so the source's *"regardless of the size of the grid and the particular pattern"* is the theorem rather than a remark beside it. The standing assumptions of at least two `i` values and at least two `j` values are **not used**: distinguishability holds unconditionally because every site lies in a row fibre and a column fibre at once. The paper says *"Theorem 1 generalizes this impossibility result"*, and the impossibility half is exactly that application; what Theorem 1 cannot supply is that the hypotheses are inhabited, which `Examples.Inference.SpinGrid` settles on a `2 × 2` grid |
| Example 6 | a real-world computer, its program RAM, complete and partial strings, `Σ_k` | — | **INTERPRETATION** — the prefix-string scaffolding that motivates Definition 6's length function. It fixes an intended reading; the claim it leads to is Definition 6 itself |

| Status | Count |
|---|---|
| `SOURCE-EXACT` | 1 |
| **INTERPRETATION** | **5** |
| **not tracked** | **0** |

## Row-by-row check against the LaTeX

Every row in both maps was checked against `arxiv.org/src/0708.1362` and
`arxiv.org/src/1711.03499v3` on two axes.

**Item existence — complete, both papers.** The 2008 source declares 34 numbered
items (`Definition 1–14`, `Theorem 1–7`, `Proposition 1–7`, `Corollary 1–5`,
`Lemma 1`). Every one has a row, and no row cites an item the source does not
declare — an exact bijection in both directions. The 2018 source declares 45,
under a counter shared across propositions, corollaries and lemmas: `Def. 1–11`,
`Example 1–9`, `Prop. 1–2`, `Cor. 3`, `Prop. 4–16`, `Lemma 17`, `Prop. 18`,
`Cor. 19–25`. Same result. Deriving that numbering turned up a trap worth
recording: the source's **first `definition` environment is entirely commented
out**, so a naive count makes every definition one too high and would have put
physical knowledge at Definition 12 rather than 11, where the maps correctly
have it.

**Quotation fidelity — 69 of 105 verbatim, and the residue is not
misattribution.** Of the 36 that do not match the source byte for byte after
normalisation: roughly eight are the maps quoting **themselves** and are
correctly absent from the papers; roughly thirteen are artefacts of the checker
spanning two adjacent quotations or a blockquote marker; the rest are **loose
quotations** — a dropped parenthetical, `Thm.` written out as `Theorem`, an
interval printed `[0,1]` where the source writes `[0.0, 1.0]`. Nine were
restored to the source's exact wording. No quotation was found that
misrepresents what a statement says, and no row's claim depended on one.

## Scope audit — every restriction, and what causes it

Reducing a printed statement's scope is the failure mode this map exists to
prevent, so the restrictions are enumerated here rather than left implicit in the
per-row notes. Both papers are covered. Each entry names the cause and says
whether the restriction is the **source's own**, **forced** by what the printed
formula has to denote, **Lean's**, or a **real reduction** the atlas could in
principle remove.

### The acceptance rule

> **A Lean statement is at printed scope when it holds on the largest domain
> where the printed formula denotes.**

Adopted in place of a literal *scope ≥ print*. The literal rule is unreachable by
construction on at least two rows: Definition 10's `1 − M/(H₁+H₂)` and Definition
11's cardinality ratio are `∞/∞` on the ranges the print names, so meeting the
literal rule would mean choosing a totalization the source does not supply — and
that choice would be the atlas's mathematics, not Wolpert's. The rule above keeps
the burden on the atlas wherever the print *does* denote, and records the rest as
the source being under-specified.

Two consequences, both applied below:

* **A hypothesis that the printed formula needs in order to denote is not a
  narrowing.** Measurability on the general-measure stochastic layer is the main
  case: `E_P(· ∣ x)` presupposes measurable fibres and a measurable integrand, so
  the print requires it whether or not it writes it. Likewise positive fibre
  mass, and `H₁ + H₂ ≠ 0`.
* **A hypothesis the atlas adds for convenience still is one.** The finite setup
  range on Definitions 9–11 and on Propositions 8 and 11 is the live example: the
  printed `max_x` ranges over conditional expectations bounded in `[-1, 1]`, so a
  **supremum denotes on any setup range**, and finiteness buys only that the
  maximum is *attained*. Those rows stay `SPECIALIZED` and the debt is real.

### Equation (4)'s countable `U` is local to one rewriting

2018 Definition 6 reads, verbatim in the arXiv HTML: *"Let `P(u ∈ U)` be a
probability measure and `Γ` a function with domain `U` and **finite range**."*
No countability on `U`. The phrase *"for countable `U`"* appears only in the
sentence after the display — *"Writing it out explicitly, for countable `U`, the
numerator in Def. 6 is …"* — where the expectation is rewritten as a sum over
`u`. It governs that rewriting, not the definition.

**Consequence:** a `[Countable U]` restatement of Propositions 8 and 11 would
*not* reach printed scope, because the print is stated for an arbitrary
probability measure. The route is closed. What remains for those rows is the
supremum form, above.

### Removed

| Item | Was | Now |
|---|---|---|
| **Def 9** (2008) | `Measurable C.setup` | Not used. Nonemptiness of the maximizing set is `positiveMassSetupsOn_nonempty` from sub-additivity. The row is `SOURCE-EXACT`; the printed `max_x` is a supremum over positive-mass setups |
| **Thm 6(ii)** (2008) | surjectivity onto the ambient product | onto `Q₁(U) × X₂(U)`, the printed product of images — clash 10 |
| **Thm 7(i)** (2008) | finiteness, then a shared universe | `thm7_mk` drops finiteness; `thm7_equiv` states `Nonempty (· ≃ ·)` so the four types may live in independent universes |
| **Prop 7(1)** (2018) | — | proved without the printed *"countable `U` with at least two elements"*; neither hypothesis is used |
| **Prop 8** (2018) | — | proved without assuming the realized image is nonempty; that follows from `concl_surjective` |

### Forced by the printed formula

These are not choices. The source writes *countable*, but on a countably
infinite range the displayed expression need not denote a real number, and the
atlas's finiteness is the largest domain on which it is guaranteed to.

| Item | Printed quantity | Why finiteness is forced |
|---|---|---|
| **Def 11** (2008) | a **ratio of cardinalities** of setup-pair sets | On countably infinite ranges the ratio is `∞/∞`. There is no reading of the printed display that denotes a real number |
| **Def 10** (2008) | `1 − M/(H₁+H₂)` | Entropy over a countably infinite image may be `+∞`, and the ratio is then `∞/∞`. The source states no summability condition, so **the finiteness of the entropy is forced, but the finiteness of the range is not**. `entropySum` states the entropy as a `tsum` over the whole value type, where the unrealized values contribute `0`; `mutualInfoSum` and `miDistinguishabilitySum` follow, and `miDistinguishabilitySum_eq` shows the finite form is the same number wherever it is defined. Countably supported with finite entropy is the largest domain the printed ratio reaches |
| **Def 6** (2008), **Def 7** (2018) | `∑_{γ ∈ Γ(U)} min_x ℳ(x)` | A countable sum may diverge, and `min` over a countable set must become `⨅`, which need not be attained. The source states no convergence condition. The `ℝ≥0∞` route used for 2018 Definition 9 does not transfer: `ℓ` is a parameter, and the source's own counting-measure instance has `setupLength = −log(fibre card) ≤ 0`, so the summands are **not** nonnegative and `ℝ≥0∞` cannot host the paper's own example (Definition 9's summands are `2^(−ℳ) ≥ 0`). A countable form over `ℝ` with `Summable` and an attained-minimum hypothesis would cover every countable instance where the printed display denotes. `EReal` is needed only for a *totalized* object covering divergent cases, which would be the atlas's mathematics rather than Wolpert's. **Largest remaining scope item**: 2008 Def 6 and Thm 4, 2018 Def 7 and Prop 13 |

Recording these as `SPECIALIZED` is the conservative call and is kept. The honest
reading is that the printed statements are under-specified on countable ranges,
not that the atlas narrowed them: widening would mean choosing a totalization the
source does not supply — `ℝ≥0∞`-valued sums, or an explicit summability
hypothesis — and that choice would be the atlas's, not Wolpert's.

**Thm 4** (2008) inherits Def 6's range restriction and adds none of its own.

### Lean's, not the paper's

| Item | Restriction |
|---|---|
| **Thm 7(i)** (2008) | **Removed.** `Cardinal.mk` compares types in a single universe, so `thm7_mk` forced the four types to share one. `thm7_equiv` states the conclusion as `Nonempty (· ≃ ·)` instead: `Equiv` is defined across universes and `Function.Embedding.antisymm` is the Schröder–Bernstein step in that form, so the two question types and the two label types now live in **four independent universes**. Equal cardinality is exactly a bijection, so nothing is weakened, and in one universe `Cardinal.eq` recovers `thm7_mk` conjunct by conjunct. The `DecidableEq` instance arguments remain, and they are classically free — clash 8 |

### Genuine remaining deltas

| Item | Delta | Status |
|---|---|---|
| **Prop 6** (2008) | `Measurable` on both setup maps | Not removable the way Def 9's was: the independence and Gibbs steps need fibre masses to add **exactly**, which is what measurability buys. The two side conditions — positive fibre mass, `H₁ + H₂ ≠ 0` — are forced, since the printed expressions are undefined without them |
| **Def 12** (2008) | questions as a label type plus `eval`, rather than as functions | Clash 9. The surjectivity half of this grade is *not* a restriction — `Question` is forced surjective, so it is `Q(U)` up to labelling and no instance is lost (clash 10). The grade is held by the label-versus-function encoding alone |
| **Def 7** (2018) | semi-measures are not a first-class object | The atlas renders "semi-measure" as a measure of total mass at most one wherever the distinction is used. That covers the inequality in Definition 9 but is weaker than the algorithmic-information notion, which also carries lower semicomputability |

### Not a scope reduction

**Prop 4** (2008) is `SOURCE-EXACT`. Clash 7b: *"over `D`"* occurs in the
hypothesis and in the conclusion, and in the conclusion it can only mean
*restricted to `D`*. Statement and proof agree. `htwo` is the paper's own §1.2
two-value stipulation, reintroduced where the source uses it.

### Where the source is exceeded

Several statements are proved **more generally than printed**, and those are
scope *gains* rather than fidelity concerns: Theorem 5 without the axiom of
choice the source uses; Corollary 2's `←` direction for an arbitrary target
range; Theorem 1 stronger than printed on constant-setup pairs (clash 13);
Proposition 6 from the printed premise with no assumed step; and, in 2018,
Propositions 9, 10 and 14 as exact identities in the figure parameter where the
source takes a limit.

## Source clashes

Every encoding reading and every defective printed statement is recorded in
[`wolpert-2008-source-clashes.md`](wolpert-2008-source-clashes.md), which is
tracked in this directory. The findings include the Def 12 / Prop 7 witness,
Theorem 7's duplicated hypothesis, Proposition 6's assumed step, Proposition
3(ii)'s reading, Corollary 5's vacuous hypothesis, and the dropped global
two-value stipulation.

§8 is the paper's own measure boundary: *"In the analysis above there is no
probability measure `P` over `U`."* It is mechanized with a local discrete Shannon
entropy over the setup image. **No dependency was added for it**: an earlier
revision pinned PFR in `lakefile.toml` with no importer anywhere in the tree, and
that pin has been reverted. If the Gibbs step of clash 3 is ever mechanized, that
is the point at which an entropy dependency would earn its place.

Corollary 1(ii) remains **refuted as stated** — see below.

## Corollary 1(ii) is false as literally stated

The source's Corollary 1(ii) reads: *"For any function `Γ` with domain `U` there is
a device that infers `Γ`."* It is presented as a consequence of Proposition 1(i),
whose construction needs a **proper** subset `W ⊂ U` on which `Γ` already attains
every value.

When `Γ` is injective and `U` has no spare state, no such `W` exists, and the
conclusion itself fails — not merely that construction.
`Examples.Inference.Device.no_device_weaklyInfers_id_on_bool` proves that **no**
device over a two-state universe weakly infers the identity: whichever setup values
answer the two probes, the conclusion function is forced to be constant, which
contradicts the surjectivity Definition 1 requires of it.

The refutation depends on reading `∃ x` as ranging over *realized* setup values —
the source's own convention, written explicitly in Definition 3 as `∃ x ∈ X(U)`.
Permitting an unrealized setup value would make weak inference vacuously true, and
the corollary trivially so.

**This is a missing hypothesis, not a broken theorem.** Over a set of universes
large enough that some value of `Γ` is attained twice, a proper `W` exists,
Proposition 1(i) applies, and the corollary holds — which is plainly the regime the
paper has in mind, `U` being a set of universes. It is recorded because the atlas
grades statements as written.

## Relation to `Knowledge.Knowable` — independent, and this was tested

Weak inference is **not** a form of knowability, in either direction. Both failures
are witnessed by finite models in `Examples.Inference.Device`:

* `negDevice` — setup is the identity, so the target factors through it and
  `Knowable` holds; but the conclusion function is the negation, and a device's
  conclusion is fixed rather than chosen, so it weakly infers nothing.
* `coarseDevice` — a three-state device whose setup cannot separate two states, so
  the target does not factor through it and `Knowable` fails; yet each probe is
  answered on some fibre, so weak inference holds.

The two differences are the quantifier alternation (`∀ probe, ∃ setup, ∀ state in
that fibre` against `∃ decoder, ∀ state`) and the fixed conclusion function. This is
why the registry records `RELATED` against the atlas knowability kernel rather than
packaging one as an instance of the other, and why the fibre-shaped reading proposed
before this check was abandoned.

## Scope of the coverage claim

`BY-024`'s informal claim is *"Embedded physical inference devices face limits on
prediction, observation, and mutual control."* What is mechanized:

* **prediction and observation** — Prop 1(ii) and Thm 1, which the paper reads as
  the sense in which Laplace was wrong;
* **mutual inference** — Thm 1 and Thm 3;
* **mutual control** — control implies weak inference, so both impossibility results
  transport, plus Thm 5 on mutual semi-control.

Every item of the 2008 numbered inventory (Defs 1–14, Thms 1–7, Props 1–7,
Cors 1–5, Lemma 1) has a declaration that states it, at the status recorded in the
transcription table: 42 `SOURCE-EXACT`, 1 `SPECIALIZED`, 2 `REPAIRED`, 0
`ASSUMED-STEP`, 1 `REFUTED`, over the 46 tracked statements.

The three that are not plain source theorems, named here so the grade cannot be
read past them:

* **Cor 1(ii)** is **refuted**, not proved — the statement as written is false.
* **Prop 7** and **Cor 5** are `REPAIRED`: the printed witness fails Definition 12,
  and the printed hypothesis of Cor 5 is vacuous under Theorem 1.

**Proposition 6 carries no assumed step.** `mutualInfo_eq_zero_iff` is
the equality case of Gibbs' inequality, so the source's asserted
*MI-distinguishability 1 ⟹ independence* is derived rather than hypothesized,
and `prop6_half_of_miDistinguishability_eq_one` proves the `1/4` bound from the
printed premise. The row is `SOURCE-EXACT`: the LaTeX prints *"two devices whose mutual-information distinguishability is 1, where `X₁(U) = X₂(U) = 𝔹`"*, so the two-valued setup ranges are the source's own hypothesis and were never an atlas restriction. Measurability and the two side conditions are forced, because the printed conditional expectations and the printed ratio do not denote without them.
* **One** numbered item is `SPECIALIZED`: Definition 11's counting
  distinguishability, whose denominator `\|X₁(U)\| × \|X₂(U)\|` is `∞/∞` on a
  countably infinite setup range, so the printed ratio denotes nowhere beyond
  finite ranges. Three tracked prose rows carry a restriction — §8's `C̄_ε`,
  §9's `𝒟`, and the `Ĉ` display after Definition 6 — each with its reason in the
  row. A hand-maintained sentence of this shape is exactly what drifts, which is
  why the gate computes the tally and cross-checks four surfaces against it.

Nothing in this **2008 inventory** transcribes `survey-ref-053`, `survey-ref-054`
or `survey-ref-055`; the separate `PhysicalKnowledge` module now transcribes the
first `survey-ref-054` cluster.

What is *not* covered by the mechanized statements: the physical reading of `U` as a
set of universes. Nothing in Lean makes `U` physical, and nothing should be read as
establishing a claim about any actual device. That is the paper's own position —
the results hold independent of the physical laws — but it means the AI-system
reading needs a separate reviewed bridge, which does not exist.
