# Wolpert 2008 — source clashes and encoding readings

Companion to [`wolpert-inference-devices.md`](wolpert-inference-devices.md).

Every row is a place where the arXiv:0708.1362 **v2** text does not uniquely
determine a formal statement, or where it determines one that is defective. Each
row says which reading the Lean encodes. **A row here is not a proof gap** — it is
the record that a choice was made, and which one.

This tracked note is the durable evidence behind every `REPAIRED`,
`ASSUMED-STEP`, and representation-status explanation on the Wolpert row.

---

## 1. Theorem 7's duplicated hypothesis

v2: *"If `P` is intelligible to `D′` and `P` is intelligible to `D′` then…"*

The proof uses `P` intelligible to `D′` **and** `P′` intelligible to `D`. The Lean
`thm7_card` takes both directions. The duplicated sentence is treated as a
typesetting error, not as a one-sided hypothesis.

## 2. Proposition 7's printed witness is not a Definition 12 device

The appendix constructs `Y₂ = Y₁` and `Q₂(U) = {Y₁, ¬Y₁}`, with `Q₂ = Y₁` on
`{Y₁ = −1}` and `Q₂ = ¬Y₁` on `{Y₁ = +1}`. Then `Q̄₂` is constantly `−1`, so
`Y₂ Q̄₂ = −Y₁` and no fibre of `Y₁` can report it.

That pair `(Y,Q)` hits only two of the four values of `𝔹 × Q(U)`: `(−1, Y₁)` and
`(+1, ¬Y₁)`. **Definition 12 requires `Y ⊗ Q` surjective onto `𝔹 × Q(U)`, so the
printed witness is not a self-aware device under the printed definition.**

The author's PDF makes the omission explicit: the construction checks
*"guarantees that `|Q₂(U)| ≥ 2`, as required"* — the two-value stipulation — but
never checks Definition 12's surjectivity of `Y ⊗ Q` onto `𝔹 × Q(U)`, which is
the clause it violates.

Lean uses a constantly-false `PUnit` question. `Y ⊗ Q` hits both bits because `Y`
is surjective and `Q` is constant. `ask` is constantly false, so a correcting fibre
would require `Y = ¬Y`. Same impossibility, Definition-12-legal. Status
**REPAIRED**.

That replacement is Definition-12-legal in the Atlas model but violates the
paper's separate §1.2 convention that every function under consideration has at
least two image values. The convention and Definition 12 cannot both be met by
this replacement on every universe: two realized questions plus surjectivity of
`Y ⊗ Q` require at least four states, while Proposition 7 quantifies over an
arbitrary device universe. The theorem is therefore not described as a literal
source witness; `REPAIRED` records both defects.

## 3a. Proposition 6 — three defects in the printed statement and proof

Verified against the author's LaTeX PDF, not only the HTML conversion.

1. **The statement misnames a device.** *"Say that `C₁` infers `C₂` with accuracy
   `ǫ₁`, while **`C₂` infers `C₂`** with accuracy `ǫ₂`."* The second should be
   `C₂` infers `C₁`; the proof computes the mutual product, and the Lean
   `prop6_product_eq` uses `inferenceAccuracy C₁ p C₂.concl * inferenceAccuracy C₂ p C₁.concl`.
2. **The closed form carries a stray symbol.** The displayed `α = β = 1/2`
   reduction reads `| (z₁² − z₂² − z₃² + **d**z₄²)/4 + (z₂z₃ − z₁z₄)/2 |`. There is
   no `d` in the paper; removing it makes the left side equal the right side
   `|((z₁−z₄)² − (z₂−z₃)²)/4|`, which is what `prop6Expr_half_closed` proves.
3. **The independence step is asserted, not proved.** *"Next, since the
   distinguishability is 1.0, `X₁` and `X₂` are statistically independent under
   `P`."* One sentence, no derivation. Lean now isolates exactly that assertion:
   `prop6Law_of_independent` derives all four conditional identities from
   `StatisticallyIndependent` under positive setup support. The remaining gap is
   only `MI-distinguishability = 1 ⟹ independence`, the equality case of Gibbs.

**All three survive into Physica D 237(9):1257–1281** — they are not preprint
artifacts.

Wolpert **2018 Proposition 11** is the same bound with *"those variables are
statistically independent under `P`"* as the direct premise, in place of
MI-distinguishability `1`. Read from arXiv:1711.03499v3; its covariance
accuracy `cov(D, Γ) := [Σ_{δ∈π(Γ)} maxₓ E_P(Y δ(Γ) ∣ x)] / |Γ(U)|` is Definition 9
of the 2008 paper unchanged. Defect 1 survives there too: *"`D₂` infers `D₂`"*.
So the split recorded here is the author's own, ten years later, and the
consequence for coverage is in §18.

## 3. Proposition 6 — what is proved and what is assumed

The source's proof has three steps. Steps 1 and 3 are mechanized; step 2 is split
at the exact remaining source assertion.

| Step | Content | Status |
|---|---|---|
| 1 | With `\|X₁(U)\| = \|X₂(U)\| = 2`, the product of accuracies is `\|E(g∣X₁=1) − E(g∣X₁=−1)\|/2 · \|E(g∣X₂=1) − E(g∣X₂=−1)\|/2`, `g = Y₁Y₂` | `inferenceAccuracy_eq_of_two_setups` |
| 2a | MI-distinguishability `1` ⟹ `X₁ ⊥ X₂` | **proved** by `statisticallyIndependent_of_miDistinguishability_eq_one`, from `mutualInfo_eq_zero_iff` — the equality case of Gibbs. The 2008 source asserts it in one sentence without derivation |
| 2b | Independence ⟹ the four displayed conditional-expectation identities | **proved** by `prop6Law_of_independent`; the identities are packaged as `Prop6Law` |
| 3 | Algebra to `\|αβk² + αkm + βkn + mn\|`, and `≤ 1/4` at `α = β = 1/2` | `prop6_product_eq`, `prop6_half` |

Step 2 needs the **equality case** of Gibbs, `M = 0 ⟹ independence`, which is
strictly stronger than the inequality. **Both are now proved**, from
`Real.log_le_sub_one_of_pos` and `Real.log_lt_sub_one_of_pos`, with no
measure-theoretic entropy API and no dependency: `gibbs_cell_eq_iff` is the
pointwise equality case (`log t ≤ t − 1` is tight exactly at `t = 1`),
`mutualInfo_eq_zero_iff` sums it over the rectangle `X₁(U) × X₂(U)`, and
`statisticallyIndependent_of_miDistinguishability_eq_one` reads it back through
Definition 10. `prop6_half_of_miDistinguishability_eq_one` therefore states
Proposition 6 with the **printed** premise. Status moves from `ASSUMED-STEP` to
**SPECIALIZED**, for finiteness and for two side conditions the printed statement
leaves implicit: positive mass on the four setup fibres, and `H₁ + H₂ ≠ 0`, where
Definition 10's ratio is undefined.

No dependency is needed for this step. Importing PFR's `mutualInfo_eq_zero` or
bridging to Mathlib's `klDiv_eq_zero_iff` would both cost more than the fact
requires: the atlas already applies the inequality whose equality case this is,
and Mathlib already names the strict form of the log bound.

**Closed.** `Examples.Inference.Device.p6_setups_independent` proves independence
for the uniform square, and `p6_law` is obtained through
`prop6Law_of_independent`, so
`prop6_product_eq` is not vacuous. The witness is the source's own extremal case:
the four-point square under the uniform measure, where `X₁ = fst` and `X₂ = snd`
are independent and `α = β = 1/2`, with conclusions agreeing exactly at
`(false, false)` so that `z = (1, 0, 0, 0)`. `p6_product_eq_quarter` then shows the
product of the two accuracies is exactly `1/4` — the paper's remark that *"at these
values, both devices have an inference accuracy of 1/2 at inferring each other"*.

`α`, `β` and `z` are **defined** from the measure — `setupMass`,
`cellAgreeProb`, `prop6QuadrupleOf` — rather than taken as free scalars, so the
identification of the parameters is not assumed on top of step 2.

**Definition 9 support is explicit.** The printed conditional expectation is
undefined on a zero-probability fibre. `inferenceAccuracy` therefore maximizes
over `positiveMassSetups`, not every realized setup value: totalizing
`condExpect = 0` on a null fibre would strictly increase the reported accuracy
whenever all positive-mass conditionals are negative. Proposition 6 carries
positive-mass hypotheses for the four setup values whose conditionals it uses.

Definition 10's remark *"Mutual-information distinguishability is bounded between
0 and 1"* is **unconditional in Lean**: `miDistinguishability_mem_unit_interval`
derives `0 ≤ M` from `mutualInfo_nonneg` and `M ≤ H₁ + H₂` from
`mutualInfo_le_add` (joint entropy is nonnegative). When the printed ratio is
undefined because both entropies vanish, Lean totalizes it to `1`; that is an
explicit convention, not a source theorem about `0/0`.

### Definitions 10 and 11 quantify an unused `ε`

Both printed definitions introduce `ε ∈ [0,1]`, but `ε` occurs in neither
displayed formula. Lean omits the dead parameter. This is a source-level notational
defect, not a restriction of `miDistinguishability` or
`countingDistinguishability`.

## 4. `H` is the unit hypercube, not its vertices

v2 writes *"define `H` as the four-dimensional hypercube `{0,1})^4`"*, but the
`zᵢ` are conditional probabilities `P(g = 1 ∣ x₁, x₂)` and the proof says *"the
4-tuple `(z₁,z₂,z₃,z₄) ∈ H` so long as none of its components equals 0"*. So `H`
is `[0,1]⁴`. `Prop6Quadruple` carries the `[0,1]` bounds.

The notation differs between versions and neither is usable as printed. arXiv v2
writes `{0, 1})^4`, with an unmatched parenthesis. **Physica D balances it to
`({0, 1})^4`, which reads unambiguously as the sixteen-vertex set** — and the proof
then contradicts that reading, since the `zᵢ` are conditional probabilities and the
only case the proof excludes is `0`. The published paper is internally inconsistent
here; the Lean takes the reading the proof requires, the closed unit cube.

`Bool⁴`, the sixteen vertices only, will not do: a `max` over the vertices is
not the source's `max` over `H`, and a bound proved against it would not follow
for a general `α, β`. The `1/4` value is unaffected: the maximizer
`z₁ = 1, z₂ = z₃ = z₄ = 0` is a vertex, and `prop6Expr_half_maximizer` attains it.

## 5. Theorem 4 is one-sided **in the source**

v2 displays

> `𝒞(Γ∣C₁) − 𝒞(Γ∣C₂) ≤ |Γ(U)| max_{x₂} min_{x₁ : X₁=x₁ ⇒ X₂=x₂, Y₁=Y₂} [ℒ(x₁) − ℒ(x₂)]`

The bars in `|Γ(U)|` are the **cardinality** of the target image, fixed in §1.2
(*"For any (potentially infinite) set `W`, `|W|` is the cardinality of `W`"*). There is **no** absolute
value around the complexity difference, and none is available: the hypotheses
`C₁ ≫ C₂` and `C₂ > Γ` are not symmetric in `C₁` and `C₂`.

The cardinality bars are not an absolute value. Verified three ways: the
author's LaTeX PDF of the v2 preprint, `ar5iv.labs.arxiv.org/html/0708.1362`,
and `arxiv.org/html/0708.1362v2`. All three render the difference without bars.

## 6. Definition 6 / Theorem 4 measure

**No longer a clash about the measure.** Section 5 is now stated over an arbitrary
`U` with `ℒ` as a **parameter**, because Theorem 4's proof never unfolds a length:
every step compares them through `inf'` and `sup'`. So counting measure — the
paper's own Example 6, `ℒ(x) = −ln |X⁻¹(x)|` — and the general
`ℒ(x) = −ln μ(X⁻¹(x))` of `Complexity/Measure.lean` are both instantiations of one
theorem, not two developments.

What remains is finiteness of `X(U)` and `Γ(U)` where the source says *countable*,
and that is now the only restriction: `[Fintype U]` is gone from `Complexity.lean`.
The `Finset.filter`s that previously got decidability from a finite `U` now take it
from `open scoped Classical`, which the atlas already permits.

Definition 6 is stated in the source only for `C > Γ`. `inferenceComplexity`
carries that hypothesis in its signature; `inferenceComplexityTotal` is the
totalization, which assigns `0` where no setup answers a probe.

## 7. Proposition 3(ii): "mutually distinguishable" — **not a clash**

The source **defines the term**, in
running prose immediately before Proposition 3, in both arXiv v2 and Physica D:

> *"We say that the reality as a whole is **mutually (setup) distinguishable** iff
> `∀ x₁ ∈ X₁(U), x₂ ∈ X₂(U), … ∃ u ∈ U` s.t. `X₁(u) = x₁, X₂(u) = x₂, …`"*

That is `n`-wise joint realizability — exactly `MutuallyDistinguishable`. So the
*hypothesis* is the source's, not a guess.

`DeviceReality U n = Fin n → InferenceDevice` does **not** make the finite family
the *whole* reality, so it is no ground for grading Proposition 3(ii)
`SPECIALIZED` against the source's cycle inside a possibly countable one.
`DeviceReality` is just *n devices over `U`*; nothing in
it says the list is exhaustive, and no hypothesis or conclusion of 3(ii) or 3(iii)
mentions devices outside the cycle. Given a reality satisfying the source's
hypotheses, the `n` cycle devices satisfy the Lean ones — mutual distinguishability
restricts to a sub-family, since a tuple on the `n` extends to the rest by any
realized value. So the Lean theorem **implies** the source's, and its hypothesis is
if anything weaker. Both are `SOURCE-EXACT`.

Proposition 4 has a clash **inside the source**, not an atlas narrowing. The
statement says *"the strong inference graph **of the reality** is weakly
connected over `D`"*, so a connecting path may pass through devices outside `D`.
The **proof** uses the other hypothesis: *"Since `D` is weakly connected"*, with
`S(D′)` and `P(D′)` defined as unions with *"the set of all nodes **in `D`**"*
that are successors / predecessors. Paths stay inside `D` throughout. The
reality-wide hypothesis is never used.

Clash 7b adopts the reading on which both occurrences of *"over `D`"* mean the
induced subgraph; on that reading statement and proof agree and the row is
`SOURCE-EXACT`. What follows is why the **other** reading — hypothesis taken
reality-wide — is not available: on it the paper's own graph reasoning does not
carry the printed hypothesis to the printed conclusion. The term *"root over
`D`"* is never defined either; under a reality-wide hypothesis and each of the
three available readings of *"root"*, the following graph satisfies the printed
hypothesis and violates the printed conclusion:

> `C₃ ≫ C₁`, `C₃ ≫ C₂`, `C₄ ≫ C₂`, with `D = {C₁, C₂}` incomparable and setup
> distinguishable. The reality graph is weakly connected over `D` via
> `C₁ ← C₃ → C₂ ← C₄`. Roots of the subgraph induced on `D`: **two** (`C₁`, `C₂`).
> Roots of the reality lying in `D`: **zero**. Roots of the component containing
> `D`: **two** (`C₃`, `C₄`). The distinguishability hypothesis constrains only pairs
> *in* `D`, so `C₃` and `C₄` are unconstrained. `D` weakly connected using its own
> edges excludes the graph, since there is no `C₁`–`C₂` edge.

This is a gap at the graph level, which is where the paper's proof works. It is
**not** a counterexample reality: no reality realizing that graph is exhibited here,
and realizability is constrained (Theorem 2(ii) forces transitive closure,
Proposition 3(iii) forces acyclicity, §6 restricts the admissible graphs further).
So the claim recorded is the weaker, checkable one — read reality-wide, the
printed hypothesis does not support the printed conclusion. The blockquote's last
line is what closes the argument: `D` weakly connected using its own edges
excludes the graph, so clash 7b's induced-subgraph reading is untouched by it,
and that reading is the one both Wolpert's proof and the Lean assume.

The Lean proof also differs in skeleton: the source obtains a root from *"acyclic and
finite"* and then finds a node with two root predecessors via `S({C₁}) ⊂ P[S({C₁})]`;
`exists_strong_root` maximizes the successor count and `unique_strong_root` finds a
crossing edge of the cut `{r} ∪ succ(r)`. Same contradiction target — one device
strongly inferred by two distinguishable devices, `not_two_strong_inferrers_conflict`.

The definition was missed because it is prose, not a numbered `Definition`
environment. That is the same structural blind spot this project has hit before:
transcription tables track numbered environments, so prose definitions and prose
claims are invisible to them. The sweep for prose claims must cover definitions
too, not only assertions.

**Still unmechanized, from the same paragraph:** the source also defines a device
being *"outside distinguishable"* in a reality (`∀ xᵢ ∈ Xᵢ(U)` and all `x′₋ᵢ` in the
range of `⊗_{j≠i} X_j`, some `u` realizes both). No numbered result mechanized here
uses it — Proposition 4's hypothesis is pairwise setup distinguishability — so it is
a coverage gap in the prose layer, not in the inventory.

### The prose definitions, and where they now are

Found by re-sweeping the article for defined terms outside numbered environments,
after the *"mutually distinguishable"* miss. None is used by a numbered result, so
none changes the inventory tally — but an unlisted gap reads as coverage, which is
why the list exists. **All four are now mechanized, and all four have a worked
model.**

| Source | Term | Lean | Model |
|---|---|---|---|
| §6, before Prop 3 | *outside distinguishable* | `OutsideDistinguishable`, with `outsideDistinguishable_of_mutuallyDistinguishable`. The paper reads it as free will: *"the way the other devices are setup does not restrict how `C` can be setup"* | `mutualReality_outsideDistinguishable` |
| §8, after Def 10 | **stochastic inference complexity** `C̄_ε(Γ∣C)` | `stochasticInferenceComplexity`; the `ε = 1` remark proved in **both** directions — `stochasticInferenceComplexity_le` needs no extra hypothesis, `stochasticInferenceComplexity_eq` carries the source's *"`P` proportional to `dμ` across the support"* as *no point of a fibre is null* | `witness_stochasticComplexity_eq`, value `2·log 2` |
| §9, after Def 13(ii) | *infallible for `Q₀ ⊆ Q(U)`* | `InfallibleFor`, with the source's own *"infallible iff infallible for `Q(U)`"* as `infallible_iff_infallibleFor_realized` | `saPartial`: infallible for `{true}`, not infallible |
| §9, footnote 9 | the alternative definition of *corrects* | `CorrectsAlt` | `saDev_correctsAlt_saSelfProbe` |

`saPartial` answers question `true` correctly and question `false` backwards. It
matters because the relativized clause would be idle vocabulary if every device
infallible on a nonempty question set were infallible outright, and nothing had
shown otherwise.

Two things footnote 9 leaves implicit, recorded rather than smoothed over.
Definition 14's `D₁` is a **plain device**, while the footnote's variant needs it
**self-aware**, since intelligibility and infallibility are defined only for those.
And `π(Y₂Q̄₂)` is a set of probe *functions* where `InfallibleFor` takes question
labels; the two coincide in the source, where `Q(U)` **is** a function set, so the
Lean clause ranges over the labels whose evaluation is such a probe. No relation
between `CorrectsAlt` and `Corrects` is claimed — the footnote offers a different
definition, and Proposition 7 is stated for Definition 14.

The source also says of §8 that *"one can also define stochastic analogs of
(semi-)control, strong inference, etc. Such extensions are beyond the scope of this
[article]"*. Those are not gaps — the source does not define them.

## 7b. Proposition 4's "over `D`" — **not a clash**

There is an apparent gap between Proposition 4's statement and its proof: the statement says *"the strong inference graph of the reality is weakly
connected **over `D`**"* while the proof argues *"Since `D` is …weakly
connected"*, taking successors and predecessors within `D`.

Checked against the LaTeX source (`arxiv.org/src/0708.1362`). The phrase *"over
`D`"* occurs **twice**, and the second occurrence settles it:

> Then the strong inference graph of the reality has one and only one root
> **over `D`**.

There, *"over `D`"* can only mean *among the nodes of `D`*. Read the hypothesis
the same way — the graph restricted to `D` is weakly connected — and the
statement is the proof, and both are what `StrongGraphWeaklyConnected`
transcribes. There is no gap.

Proposition 4 is `SOURCE-EXACT`. `htwo` is the paper's own §1.2 two-value
stipulation, used where the source uses it.

## 8. Theorem 7(i) is mechanized in the finite case only

The source puts *"If `Q(U)` is finite"* in **(ii)**; (i) is an unrestricted
cardinality equality `|Q(U)| = |Q′(U)| = |P(U)| = |P′(U)|`.

`thm7_mk` states it that way, equating `Cardinal.mk` with no finiteness anywhere.
Antisymmetry on `Cardinal` is Schröder–Bernstein, which is exactly what the printed
proof appeals to when it concludes equality from two dominations. `thm7_card`
remains as the finite instance.

Status stays **SPECIALIZED**, and the reason has changed from the paper's to
Lean's: `Cardinal.mk` compares types in a single universe, so `thm7_mk` puts the
four types in one, where `thm7_card` allows four different universes because
`Fintype.card` lands in `ℕ`. Neither restriction is in the source, which has no
universes at all.

Theorem 7(**ii**) is mechanized as printed: `thm7_ii` is an equality of sets of
functions on `U`, `evalImage D = probeImage pMap`.

## 9. Questions are a label type plus `eval`

Definition 12 takes `Q(U)` to be a set of binary functions on `U`. Lean uses
`Question : Type` with `eval : Question → U → Bool`, so two labels may evaluate
equally.

This is a **generalization**, not a distortion, and it is a theorem rather than
an argument. `FunctionValuedSelfAware`
is Definition 12 read literally, with `Y ⊗ Q` onto `𝔹 × Q(U)`, the product with
the image as the source writes it. `FunctionValuedSelfAware.toSelfAware`
represents it by taking the labels to *be* the image of `Q` and `eval` to be the
inclusion. `toSelfAware_ask` proves the source's `Q̄` survives unchanged, and
`evalImage_toSelfAware` proves the evaluated questions are exactly the printed
`Q(U)` — nothing added, nothing collapsed. `SelfAwareDevice.toFunctionValued` is
the converse, and the round trip is the identity on both. `Intelligible` says a
realized question evaluates to `f ∘ Γ`, which is the source's `f(Γ) ∈ Q(U)`.

The row is `SOURCE-EXACT` on that basis: the grade follows the representation,
not the encoding.

Where the distinction is load-bearing is Theorem 7(ii), whose conclusion is an
equality of *function* sets. That is why `evalImage` compares after evaluation:
labels with equal `eval` collapse to one element, exactly as the source's set
would have them.

## 10. Image-versus-type surjectivity

**Theorem 6(ii).** The source asks that `(Q₁, X₂)` be surjective onto
`Q₁(U) × X₂(U)`, the product of the two **images**. Surjectivity onto the ambient
product `Question × Setup` would be strictly stronger whenever either function
misses a value of its type — a restriction with no source warrant. The hypothesis
reads *any realized question pairs with any realized
setup value*, which is the printed one, and the theorem is **SOURCE-EXACT**.

**Definition 12 — a normalization, kept at SPECIALIZED.** `Y ⊗ Q` onto `𝔹 × Q(U)`
becomes onto `Bool × Question`. Here the two coincide by construction: the Lean
condition forces `question` to be surjective, so `Question` *is* `Q(U)` up to
labelling, and every source device is representable by taking `Question := Q(U)`.
No instance is lost and no theorem is weakened. The `SPECIALIZED` grade is therefore
conservative rather than forced, and is left in place — together with clash 9's
label-versus-function point, which is the part that genuinely differs.

**Universe scope.** `SelfAwareDevice.{u, v, w}` gives the question type its own
universe `w`. Tying it to the device's setup universe `v` would impose a
restriction the source has no analogue of.

## 11. Corollary 5's printed hypothesis is vacuous

v2: *"Let `D₁` and `D₂` be two self-aware devices that are infallible,
semi-control their questions, and are distinguishable. **If in addition they infer
each other**, then it is not possible that both `Y₂` is intelligible to `D₁` and
`Y₁` is intelligible to `D₂`."*

Distinguishable devices that weakly infer each other contradict Theorem 1, so the
printed hypotheses are jointly unsatisfiable and the corollary is vacuously true.

`not_both_concl_intelligible` **drops** that hypothesis and instead derives mutual
weak inference from intelligibility via Theorem 6(i), contradicting Theorem 1.
That is strictly stronger than the printed sentence and is what the surrounding
prose intends. Status **REPAIRED**.

**The printed citation names a theorem part that does not exist; it means
Theorem 6(i).** The lead-in reads *"combining Thm.'s 1 and 3(i) gives the
following result"* — **Theorem 3 has no parts**. Verified hard-coded in the
LaTeX source rather than a `\ref`, so LaTeX never validated it, and identical in
the preprint and the published article. It is **Theorem 6(i)**: Corollary 5's
hypotheses are exactly that theorem's — infallible, semi-controls its questions,
target intelligible — and Theorem 3 (no two devices strongly infer each other)
plays no role in the argument at all, while Theorem 6(i) applied to each device
gives the mutual weak inference that Theorem 1 then contradicts. So the source's
own citation names the repair's exact proof route; `not_both_concl_intelligible`
takes it.

## 12. Definition 2's working predicate

Definition 2 as printed is `IsSourceProbe`: onto `𝔹`, true at exactly one
argument, on a range with at least two elements. `WeaklyInfers`, `StronglyInfers`
and `Controls` quantify over `IsProbe`, which keeps only the unique-true clause.

`surjective_of_isProbe` shows the two coincide as soon as the range has a second
point, and `weaklyInfers_iff_sourceProbes` shows the two quantifications give the
same Definition 3 there. The divergence is confined to a **singleton** range,
which the source's global stipulation excludes.

## 13. The global two-value stipulation is dropped

§1.2: *"For any function `Γ` with domain `U` that we will consider, we implicitly
assume that `Γ(U)` contains at least two distinct elements."* This is not imposed
here, on targets or on setup functions.

On the setup side it is load-bearing: a constant-setup device is `Distinguishable`
from itself, which the source denies immediately after Definition 4. Theorem 1 is
therefore **stronger** here — it covers pairs the source's hypothesis never
reaches — and the witness is
`Examples.Inference.Device.constSetup_distinguishable_self`.

Where a proof needs the stipulation it is reintroduced explicitly: Proposition 4
takes `htwo`, two realized setup values per device, and Lemma 1's
`SourceStipulations` carries all three clauses.

## 14. Corollary 1(ii) is refuted as literally stated

*"For any function `Γ` with domain `U` there is a device that infers `Γ`."* False:
no device over a two-state universe weakly infers the identity, because its
conclusion function would have to be constant against Definition 1's surjectivity.
The countermodel is `no_device_weaklyInfers_id_on_bool`.

This is a **missing hypothesis**, not a broken theorem — the corollary's own proof
uses a proper `W ⊂ U` on which `Γ` attains every value, which exists whenever some
value of `Γ` is attained twice. The refutation quantifies over *all* devices over
`Bool`, so it covers the two-valued-setup devices the source admits; it does not
lean on clash 13.

## 15. Other representation choices

| Choice | Note |
|---|---|
| `𝔹 = {−1,+1}` becomes `Bool` | Renaming; identity and negation probes are `id` and `not`. `boolPm` maps back to `±1` where §8 needs arithmetic |
| `∀ x` reads as "over realized setup values" | The source's own shorthand, explicit in Definition 3 as `∃ x ∈ X(U)` |
| Theorem 5's "identical partitions" is kernel equality | Partition equality up to the relabelling the source itself describes |
| Proposition 1(i)'s `W` is `U → Bool` | A decidable subset; the source's `\|Γᵢ(W)\| ≥ 2` appears as explicit witnesses |
| The Proposition 1(i) family shares one codomain | The source's `{Γᵢ}` need not identify ranges |
| `DeviceReality` is `Fin n → InferenceDevice` | Propositions 3 and 4 are finite-subgraph statements. The source's reality, with its extra functions `{Γ_β}`, is `FullReality`, used by Lemma 1 |
| A reality's function family is nonempty | The source states this explicitly. `FullReality.SourceStipulations.family_nonempty` and the matching first clause of `AdmissibleTuples` exclude the vacuous `A = B = ∅` extension |
| Proposition 5(ii)'s `ℕ` witness is 0-based | The source's is 1-based with a ceiling; the same pairs up to relabelling |
| Proposition 2(ii) uses identity setup and three named points | The source stitches partial devices per fibre; the existence claim is the same |
| Zero-mass and zero-denominator branches | `condExpect`, `miDistinguishability`, `countingDistinguishability` are totalized where the source's formulas are undefined. Definition 9 maximizes only over positive-mass setup fibres; Definition 10's zero-entropy ratio is set to `1`. Lean conventions, not source cases |


## 19. Section 8 over a general measure — the Layer 1 foundation

`Stochastic.lean` states Definitions 9–11 and Proposition 6 for a `FinPMF` on a
`Fintype U`. The paper's `U` is *"the set of worldlines consistent with the laws
of physics"* — uncountable — so that is not the intended model, and clash 17
records it as the largest remaining restriction.

`AISafetyAtlas/Inference/Stochastic/Measure.lean` is the foundation for removing
it. Over an **arbitrary** `[MeasurableSpace U]` with a probability measure, and
finiteness on the **maps** rather than on `U` — which is where the source puts it
(*"a function `Γ` with domain `U` and finite range"*, Definition 9) — it proves:

| | |
|---|---|
| `sum_massOn` | the fibre masses of a finite-range map sum to `1` |
| `sum_massOn_marginal` | joint masses marginalise |
| `entropyOn`, `mutualInfoOn`, `IndependentOn` | Definition 10's ingredients |
| `mutualInfoOn_nonneg` | Gibbs' inequality |
| `mutualInfoOn_eq_zero_iff` | **its equality case** — Proposition 6's step 2a, with `U` arbitrary |

Three fears about a measure-theoretic restatement turned out not to apply, and
each is recorded so it is not re-litigated:

* **No disintegration, no standard Borel.** Conditioning is on `X ⁻¹' {x}` for a
  finite-range map, and Definition 9's maximum already ranges only over
  positive-mass fibres. Regular conditional probability never arises.
* **No measurability hypothesis to *state* anything.** A Mathlib `Measure` is an
  outer measure on every set, so `massOn` is total. Measurability is requested by
  the two additivity lemmas and nowhere else.
* **No dependency.** `FiniteRange` is a local three-line class; the only Lean
  library carrying one is PFR. The equality case comes from
  `Real.log_lt_sub_one_of_pos`, which Mathlib names 47 lines above the
  `Real.log_le_sub_one_of_pos` the inequality already used.

The pointwise steps `gibbs_cell` and `gibbs_cell_eq_iff` are statements about real
numbers with no probability in them. They now live in
`Inference/Stochastic/Gibbs.lean` so the finite layer and the general layer share
them and neither depends on the other.

### Definitions 9–11 on that foundation

`inferenceAccuracyOn`, `miDistinguishabilityOn` and `countingDistinguishabilityOn`
now state Definitions 9, 10 and 11 over an arbitrary `U`, and
`independentOn_of_miDistinguishabilityOn_eq_one` is Proposition 6's step 2a there.

Definition 9 is stated **without a Bochner integral**. The only function it
conditions on is `Y · f(Γ)`, a product of two `±1`-valued functions, so it is `+1`
exactly where the conclusion agrees with the probe. Its conditional expectation is
`2·P(agree ∣ x) − 1`, and that probability is a ratio of two fibre masses. No
integrability side condition arises anywhere.

Definition 11 takes **no measure argument at all**, which is the printed formula:
`P` is named in the preamble and does not appear in the display, which counts
jointly realized setup pairs.

### The finite layer is an instance, not a parallel vocabulary

`Inference/Stochastic/Bridge.lean`: a `FinPMF` induces a measure
(`FinPMF.toMeasure`), every map out of a `Fintype` has finite range, and then
`massOn_toMeasure`, `entropyOn_toMeasure`, `mutualInfoOn_toMeasure` and
`independentOn_toMeasure` show the two layers compute the same numbers. The
executable models in `Examples/` do not need restating; they instantiate.

### Proposition 6's accuracy chain

**Step 1 is transferred.** `inferenceAccuracyOn_eq_of_two_setups` proves the
source's *"for `|X₁(U)| = |X₂(U)| = 2` we can rewrite this as
`|E_P(g ∣ X₁=1) − E_P(g ∣ X₁=−1)| / 2 · …"*, over an arbitrary `U`. The two probes
of a `Bool`-valued target are the identity and the negation, so Definition 9's sum
is `max − min`, and `condExpectPmOn_not` supplies the sign flip from a Bool-fibre
split rather than from any integral.

The measurability hypotheses on `C₁.setup`, `C₁.concl` and `C₂.concl` are what a
general measure costs. The source states none, because it never has to say which
sets it can weigh. Recorded here rather than folded silently into the signature.

The pure algebra `Prop6Quadruple`, `k`/`m`/`n`, `prop6Expr` and the `α = β = 1/2`
closed form contain no probability at all, and now live in
`Inference/Stochastic/Algebra.lean` alongside `Gibbs.lean`, reachable from both
layers and depending on neither.

**Steps 2b and 3 are transferred too.** `condExpectPmOn_eq_of_independent` derives
the source's displayed identity `E(g ∣ X₁ = x₁) = 2[zβ + z′(1−β)] − 1` from
independence, by splitting the agreement fibre over `X₂`'s two values and
reindexing — no integral, and it needs positive mass on `x₁` alone, where the
finite layer asked for all four cells. `prop6_product_eqOn` and
`prop6_half_of_miDistinguishabilityOn_eq_one` complete the chain.

**So Proposition 6 now holds over an arbitrary `U`, from its printed premise, with
no assumed step.**

### What the grades are now, and why they did not move

The transcription table now points Definitions 9–11 and Proposition 6 at the
general declarations, with the `FinPMF` ones named as the finite instance. All
four stay `SPECIALIZED`, and the **reason has changed completely**:

| | Was | Is |
|---|---|---|
| Def 9 | finite `U` with a `FinPMF` | measurability of the setup map |
| Def 10 | finite `U`, local discrete entropy | finite setup range |
| Def 11 | finite cardinalities | finite rather than the source's *countable* range |
| Prop 6 | finite `U`; positive mass on four cells | measurability; positive mass on one fibre; `H₁+H₂ ≠ 0` |

### The general layer was uninhabited, and now is not

Recorded because it was reintroduced by the generalisation itself, after the same
defect had already been caught twice here. When Definitions 9–11 and Proposition 6
first landed over a general measure, **nothing instantiated any of them**: no
example mentioned `massOn`, `IndependentOn`, `inferenceAccuracyOn` or
`prop6_half_of_miDistinguishabilityOn_eq_one`, and no module outside
`Inference/Stochastic/` imported the layer at all. It built, and as far as the
tree could show it was a theorem about nothing.

Worse, Proposition 6's **printed premise** had no witness in *either* layer.
`Prop6Law` was inhabited and independence was inhabited, but
mutual-information distinguishability `1` — what the paper actually assumes — was
never shown satisfiable, so `prop6_half_of_miDistinguishability_eq_one` was a
theorem whose hypothesis might have been unreachable.

Both are closed by the witness the finite layer already had.
`p6_miDistinguishability_eq_one` computes the uniform square's Definition 10 value
as exactly `1`: each fair-coin setup carries entropy `log 2`, and independence
makes the mutual information vanish. `Examples/Inference/StochasticGeneral.lean`
then transports the whole model through `Bridge.lean` and discharges every
hypothesis of the general Proposition 6, measurability included. A `FinPMF` model
*is* a measure-space model, which is what the bridge was for.

`inferenceAccuracyOn` carries its measurability argument **in the definition**, not
only in the theorems, because the `sup'` needs a nonempty index set. It is
proof-irrelevant — `Measurable C.setup` is a `Prop`, so two proofs give the same
real — and it is the same shape as Definition 6's proof-irrelevant `C > Γ`, which
is already recorded. Noted here so the two are read together.

A measurability hypothesis is not notation, so `SOURCE-EXACT` would be wrong.
But the distance to the printed statements is now small and of a different kind:
the source never says which sets it can weigh, because it never has to. Recording
the shrunken reason rather than promoting the grade is the point.

## 17. Scope of quantification — what each part is proved *over*

Measured from the declarations, not asserted: which hypotheses each module actually
carries. `U` is the set of universes; `G`, `α`, `β` are target/setup ranges.

| Source item | Source quantifies over | Lean quantifies over | Added restriction |
|---|---|---|---|
| **Defs 1–5, 8; Prop 1, 2; Thm 1, 2, 3, 5; Cor 1, 2, 3** | arbitrary `U`, arbitrary ranges | arbitrary `U`, arbitrary ranges | **none** |
| **Def 6, Thm 4** | general measure `dμ`; `X(U)` and `Γ(U)` **countable** | counting measure; `[Fintype U]`, `[Fintype G]`, `[DecidableEq]` | measure **and** countable → finite |
| **Def 9** | probability measure `P`; target range **finite** | `FinPMF U`; `[Fintype G]` | `[Fintype U]` only — the finite range is the source's |
| **Def 10** | general `P`; Shannon quantities | `FinPMF U`; discrete Shannon on the setup image | `[Fintype U]` |
| **Def 11** | **pure counting formula** | pure counting formula; finite images | `[Fintype U]` only |
| **Prop 6** | general `P` over `U` | `FinPMF U`, plus the assumed step | `[Fintype U]` + clash 3 |
| **§6 Props 3(i)–(iii)** | cycle inside a possibly countable reality | `n` devices over `U`, any setup universe | **none** — the list need not be exhaustive |
| **§6 Prop 4** | connectivity of the strong inference graph **over `D`** | connectivity within the family | **agrees with both** — see the resolution below |
| **§9 self-aware (Defs 12–14, Thms 6–7, Cors 4–5, Prop 7)** | arbitrary `U`; `Q(U)` a set of binary functions | **arbitrary `U`**; label type plus `eval` | question model only (clash 9); the `Fintype` hypotheses on question and target *images* are the source's own |

Three consequences worth stating plainly.

**The deterministic core is fully general.** `Device.lean` carries no `[Fintype U]`
and no module-level `DecidableEq`: of its 84 public declarations, 81 have no
hypothesis beyond the devices themselves. The three that do — `probe`,
`isProbe_probe`, `semiControls_of_controls` — are decidable-instance conveniences
with classical counterparts already in the tree. Definitions 1–8 and every
impossibility result hold over an arbitrary, possibly infinite `U`.

**§9 does not restrict `U` either.** `SelfAware.lean` has no `[Fintype U]`. Its
finiteness hypotheses are on `Q(U)`, `P(U)` and `Γ(U)` — exactly where the source
puts them (*"If `Q(U)` is finite"*, *"whose question functions have finite
ranges"*). The one deviation there is the question model, not the scope.

**§5 and §8 are finite specializations, and one gap is larger than "finite `U`".**
`Complexity.lean` and `Stochastic.lean` both carry `[Fintype U]` at module level, so
every declaration in them is finite-universe. For Definition 6 that is a *double*
narrowing: the source allows a general measure **and** merely countable `X(U)` and
`Γ(U)`, where the Lean takes counting measure over finite types. Definition 9's
finite target range, by contrast, is the source's own — only `[Fintype U]` is added.

**A correction to a common summary of this scope.** Definition 11 is sometimes
described as a probability-weighted formulation that the Lean replaced with plain
cardinality. It is not: `P` is named in Definition 11's preamble and then **does not
appear in the displayed formula**, which is
`1 − [Σ_{x₁,x₂ : ∃u, X₁(u)=x₁, X₂(u)=x₂} 1] / (|X₁(U)| × |X₂(U)|)` — pure counting.
`countingDistinguishability` takes no `FinPMF` and is faithful on that point.

**Decidability.** Every declaration in `Complexity.lean` and `Stochastic.lean` takes
`[DecidableEq]` on the setup and target ranges, which the source never requires. It
is a representation restriction, discharged classically for any particular range,
and it is confined to those two modules.

## 16. Which text was read

The primary publication pin is the Physica D article, *Physica D*
237(9):1257–1281, DOI `10.1016/j.physd.2008.03.040`.

The source was also checked in the author's arXiv:0708.1362v2 PDF and the
ar5iv/arXiv HTML renderings. The published article and preprint agree on the
numbered and prose statements relevant to this encoding, including the duplicated
Theorem 7(ii) hypothesis, the Proposition 6 notation/proof gap, and the Definition
12/Proposition 7 witness problem. The preprint is retained as an alternate
searchable rendering; the journal PDF is the publication authority.

The author's LaTeX PDF carries the header
`arXiv:0708.1362v2 [cond-mat.stat-mech] 23 Oct 2008` and is therefore the
preprint, not the typeset article.

## 18. What the Proposition 6 layer covers in Wolpert 2018

Measured, not inferred: the 2018 article was opened and its Proposition 11 read in
full.

| | 2008 Proposition 6 | 2018 Proposition 11 |
|---|---|---|
| Premise on the setups | MI-distinguishability `= 1` | *"those variables are statistically independent under `P`"* |
| Accuracy | Definition 9 | `cov`, the same formula |
| Bound | `ε₁ε₂ ≤ max_{z∈H} \|αβk² + αkm + βkn + mn\|` | identical, with `M` for `H` |
| Printed defect 1 | *"`C₂` infers `C₂`"* | *"`D₂` infers `D₂`"* — survives |

`prop6_product_eq` composed with `prop6Law_of_independent` mechanizes the
probabilistic and algebraic core of **2018 Proposition 11** in a sharper
pointwise form: it identifies the realized product with the displayed
polynomial, while `prop6_half` proves the uniform `1/4` bound and
`prop6Expr_half_maximizer` exhibits equality. The public API does **not** expose
the proposition's printed `≤ max_{z∈M}` wrapper as one Lean theorem, so describing
the proposition itself as fully transcribed would overstate the declaration
surface. The Lean development is additionally finite (`FinPMF`) and requires
positive mass on the four setup fibres, which the 2018 text does not state but
which its conditional expectations require exactly as the 2008 proof does.

Two consequences, and the second is a limit on the first:

* The description *"the 2018 extension is pinned, not mechanized"* is obsolete.
  The first physical-knowledge cluster is now in
  `AISafetyAtlas.Inference.PhysicalKnowledge`; the stochastic layer here covers
  Proposition 11's core as described above. Later results, including Proposition
  8's lower bound on `cov`, remain only mapped in
  [`wolpert-2018-knowledge.md`](wolpert-2018-knowledge.md).
* This is **not** what discharged Proposition 6's assumed step. A later paper
  weakening its own hypothesis is not a proof of the earlier one. The step from
  MI-distinguishability `1` to independence is proved directly, from the equality
  case of Gibbs' inequality (§3a above), which is why the grade is `SPECIALIZED`
  and the `ASSUMED-STEP` count is `0`.

## 20. The author repairs Corollary 1(ii) in 2018

Measured, not inferred: both papers were opened and the two statements read side
by side.

| | Text |
|---|---|
| 2008 Corollary 1(ii) | *"For any function `Γ` with domain `U` there is a device that infers `Γ`."* |
| 2018 Proposition 7(1) | *"For any function `Γ` over `U` such that `\|Γ(U)\| ≥ 3` there is a device `D` that weakly infers `Γ`."* |

The 2018 statement adds `|Γ(U)| ≥ 3`. Definition 2 in both papers requires only
`|Γ(U)| ≥ 2`, so this is a strengthened hypothesis and not a restatement of a
standing convention.

`no_device_weaklyInfers_id_on_bool` refutes the 2008 form at `Γ = id` on `Bool`,
where `|Γ(U)| = 2` — precisely the case the 2018 hypothesis excludes. The
`REFUTED` grade was reached from the machine countermodel alone, before this was
noticed; the author's own later text agrees with it.

Two things this is not:

* It is **not** a repair the Atlas may adopt silently. 2018 Proposition 7(1) is a
  different statement with a different hypothesis, recorded `NOT-MECHANIZED` in
  [`wolpert-2018-knowledge.md`](wolpert-2018-knowledge.md) when this clash was
  written; it has since been **proved** as `identityDevice_weaklyInfers`, and
  without the printed countability or `|U| ≥ 2` hypotheses.
  The 2008 row stays `REFUTED`, because the 2008 statement is false as printed.
* It is **not** evidence about any other 2008 defect. One corrected corollary in
  a later paper says nothing about Corollary 5, Proposition 7, or Proposition 4.

Its value is as corroboration: a machine refutation of a published claim is the
kind of finding that most deserves an independent witness, and here the strongest
available witness is the author.

## 21. Definition 9 mixes logarithm bases, and one reading is vacuous

This is a **Wolpert 2018** clash, recorded here because this file is the tracked
register of source defects for both papers.

Definition 7's size is printed with a natural logarithm:

> `ℳ_{μ;Γ}(γ) ≜ −ln μ(Γ⁻¹(γ))`

Definition 9 then exponentiates it in base 2:

> *"Given a semi-measure `μ`, a device `(X, Y)` is prefix(-free) iff
> `∑_{x : D halts on x} 2^(−ℳ_{μ,X}(x)) ≤ 1`."*

The two do not cancel. Taken literally, `two_rpow_neg_measureLength` computes

`2^(−ℳ(x)) = μ(X⁻¹(x))^(ln 2)`,

an exponent of about `0.693`. Under the reading that makes the bases agree — `ℳ`
in base 2 — `two_rpow_neg_measureLengthBase2` gives `2^(−ℳ₂(x)) = μ(X⁻¹(x))`, and
then `sum_pushOnImage_le_one` shows the condition holds for **every** device and
every halting set, because the fibres of the setup map partition `U` and their
masses sum to at most the total mass. On that reading Definition 9 restricts
nothing at all.

So the choice of reading is not cosmetic: one makes the definition a genuine
condition, the other makes it empty. `PrefixFree` transcribes the printed formula
literally — natural-log `ℳ`, base-2 exponent — and both readings are proved
rather than argued.

## 22. The Kraft direction the source needs is not the one Mathlib has

Definition 9 is followed by:

> *"By Kraft's inequality, if `D` is prefix-free for a semi-measure `μ`, then
> there is a prefix-free code for the set of all halting `x ∈ X(U)`."*

That is Kraft's **existence** direction: given lengths satisfying the inequality,
construct codewords. Mathlib's
`Mathlib/InformationTheory/Coding/KraftMcMillan.lean` proves the **converse**,
`kraft_mcmillan_inequality` — for a uniquely decodable code `S` over an alphabet
of size `D`, `∑_{w ∈ S} D^(−|w|) ≤ 1`. It goes from a code to the inequality; the
source goes from the inequality to a code.

Measured by reading the file, not inferred from its name. Two consequences:

* The earlier estimate that this layer is *"not a one-line reuse"* of Mathlib's
  Kraft is confirmed, and for a sharper reason than expected — the needed
  direction is absent, not merely inconvenient to apply.
* The sentence is a **citation of an external theorem**, not a claim Wolpert
  proves. No Lean statement in the atlas asserts it, and `Def. 9`'s
  `SOURCE-EXACT` grade covers the definition, not the cited consequence.

## 23. Proposition 12's entropy bound is false

A **Wolpert 2018** clash. The printed claim:

> **Proposition 12.** *"For any ID `D`, probability distribution `μ`, and function
> `Γ` with a countable image such that `D > Γ`, `C_μ(Γ; D) ≤ |Γ| × H_μ(X)`, where
> `H_μ(X)` is the Shannon entropy of `μ(X)`."*

It is refuted by `prop12_refuted` on a four-state model that satisfies every
printed hypothesis.

### Where the printed proof fails

The proof is a three-step chain whose last step is

`−∑_{x ∈ X(U)} log₂ μ(x)  ≤  |Γ| H_μ(X)  =  −|Γ| ∑_{x ∈ X(U)} μ(x) log₂ μ(x)`.

Compared term by term, this needs `|Γ| · μ(x) ≥ 1` — that is, `μ(x) ≥ 1/|Γ|` — at
**every** setup value. Nothing in the statement assumes it, and a setup fibre of
small mass breaks it.

### The countermodel

`prop12Device` has two setup values over four states, and a binary target. For a
binary `Γ` the two probes disagree at every point, so no single setup can answer
both: one fibre answers the `true` probe, the other answers the `false` probe,
and the complexity is the sum of both fibre lengths. Skewing the mass between the
fibres raises that sum while lowering the entropy.

At fibre masses `3/4` and `1/4`:

| | |
|---|---|
| `C_μ(Γ; D)` | `4 ln 2 − ln 3` |
| `\|Γ\| × H_μ(X)` | `4 ln 2 − (3/2) ln 3` |

`prop12_gap` proves the difference is exactly `(ln 3)/2`, so the refutation is an
identity rather than a numeric estimate. The small fibre carries `1/4` where the
printed proof needs `1/|Γ| = 1/2`, which is the failure made concrete.

The failure is not marginal in the parameter: as the mass on one fibre tends to
zero the complexity grows without bound while the entropy tends to zero, so no
constant multiple of `H_μ(X)` bounds `C_μ(Γ; D)`.

### A second defect in the same proof: the logarithm base

Checked against the LaTeX source (`arxiv.org/src/1711.03499v3`), so this is the
author's text and not an extraction artifact. The middle step is written

```
\le -|\Gamma| \sum_{x\in X(U)} \frac{ {\mbox{log}}_2 \mu(x)}{|\Gamma|}
```

with `log₂`, while `ℳ_{μ,X}` is defined one page earlier with a **natural**
logarithm. This is the same family as clash 21, where Definition 9 exponentiates
in base 2 against a natural-log `ℳ`. It does not change the refutation — the
countermodel above stands under either reading — but the proof is not
dimensionally consistent as printed. Note also that the `|Γ|` and the `1/|Γ|` in
that line cancel, so the expression is `−Σ_x log₂ μ(x)`, which is not
`|Γ| H_μ(X)` either.

### Related 2018 complexity rows

* Proposition 12 needs no extra entropy library: `entropyOn`, the local discrete
  Shannon entropy built for Definition 10, is exactly the `H_μ(X)` the
  proposition names — enough to state it, and to refute it.
* Proposition 13 is `inferenceComplexityMeasure_le_of_stronglyInfers`: 2008
  Theorem 4 at the measure length, with the source's
  `min_{x₁ : {X₁=x₁ ⇒ X₂=x₂, Y₁=Y₂}}` being `emulationSet` verbatim.

Nothing in the 2008 complexity layer depends on Proposition 12; Theorem 4's
emulation bound is a different statement and is unaffected.

## 24. Proposition 14's Figure 7 does not establish Proposition 14

A **Wolpert 2018** clash. The printed statement is true — `exists_complexity_inversion`
proves it — but the printed proof does not prove it.

> **Proposition 14.** *"There are devices `D`, `D′`, probability distribution `P`
> defined over `U`, and function `Γ`, such that `D > Γ`, `D′ ≫ D`, and
> `C_P(Γ; D)` is arbitrarily large, while `C_P(Γ; D′)` is arbitrarily close to
> the minimum value of `|Γ| × ln(|Γ(U)|)`."*

The proof is the twelve-state Figure 7 with `1/4 < p < 1`, completed by taking
`p → 1`. Which device is which is settled by the source's own verification steps,
not by the sentence naming them, whose primes the PDF layer drops: step 1 uses
unprimed setups `x = 1, 2`, so `D = (X, Y)`; step 2 chooses primed `x′` for each
`x`, so `D′ = (X′, Y′)`.

**The first half checks out.** `D` answers the `+1` probe at `x = 1` and the `−1`
probe at `x = 2`, each fibre carrying `(1 − p)/2`, so
`C_P(Γ; D) = −2 ln((1 − p)/2)`, exactly as the source computes, and it diverges.

**The second half does not.** Reading Figure 7's columns fibre by fibre:

| `X′` | states | mass | answers |
|---|---|---|---|
| 1 | A, B | `(1−p)/4` | `+1` |
| 2 | C, D | `(1−p)/4` | `−1` |
| 3 | E, F | `(1−p)/4` | `−1` |
| 4 | G, H | `(1−p)/4` | `+1` |
| 5 | I, J | `p/2` | `+1` |
| 6 | K, L | `p/2` | `+1` |

Both fibres carrying the large mass `p/2` answer the **same** probe. The `−1`
probe is available only on fibres of mass `(1 − p)/4`, so

`C_P(Γ; D′) = −ln(max((1−p)/4, p/2)) − ln((1 − p)/4)`,

which diverges as `p → 1` rather than approaching `2 ln 2`. Minimizing over the
admissible range gives about `3.47` at `p = 1/2`, never near `1.386`. What
Figure 7 does show is an unbounded *gap*, `C(Γ; D) − C(Γ; D′) → ∞`, which is the
phenomenon the figure caption describes — but not the printed convergence to the
floor.

### The repair

`Inference/Complexity/Inversion.lean` proves the statement on eight states. The
missing ingredient is that the two heavy fibres of `D′` must answer *different*
probes. Splitting one heavy `D`-fibre into a half carrying `Y′ = Y` and a half
carrying `Y′ = ¬Y`, over a region where `Y = δ_{+1}(Γ)`, does exactly that:

* `C_P(Γ; D) = −ln ε − ln(1 − ε)` — diverges;
* `C_P(Γ; D′) = 2 ln 2 − 2 ln(1 − ε)` — tends to the floor `2 ln 2`.

Both are identities in `ε`, so `exists_complexity_inversion` names the `ε`
achieving a given bound and tolerance rather than passing to a limit.

The floor itself is not arbitrary: for a binary target the two probes disagree
everywhere, so two distinct answering fibres of masses `m₁ + m₂ ≤ 1` are needed,
and `−ln m₁ − ln m₂ ≥ 2 ln 2` with equality at `m₁ = m₂ = 1/2`.

**A caution recorded with the finding.** The inversion is not monotone in the
parameter. `C(Γ; D) − C(Γ; D′) = −ln ε + ln(1 − ε) − 2 ln 2` is positive only for
`ε < 1/5`; at `ε = 1/4` the emulating device is the *more* expensive one. A first
draft of the worked example asserted the inversion at `ε = 1/4` and Lean rejected
it. `Examples.…Inversion` now records the threshold explicitly.

## 25. Example 6 does not establish that Proposition 8's bound is sharp

A **Wolpert 2018** clash. Proposition 8 is followed by *"This bound is sharp, as
can be seen from the following example"*, and Example 6 supplies the
construction. The construction is fine and its central identity is correct. The
line after that identity is not.

### The identity holds

Example 6 divides each cell of the `X × Y` partition into `|Γ(U)|`
equal-probability parts carrying the `|Γ(U)|` target values, and derives

`E_P(Yδ_γ(Γ) ∣ x) = c · E_P(Y ∣ x)`, with `c = (2 − |Γ(U)|)/|Γ(U)|`.

Checked on a twelve-state instance of exactly that recipe with `|Γ(U)| = 3`, so
`c = −1/3`: the conditional expectations come out `0 = c · 0` at one setup and
`−1/9 = c · (1/3)` at the other. `ex6_condExpect_probe_true` and
`ex6_condExpect_probe_false`.

### The step after it does not

Example 6 continues:

> *"We can use this to evaluate `M_γ := max_x [E_P(Yδ_γ(Γ) ∣ x)] = (2 − |Γ(U)|)
> max_x [E_P(Y ∣ x)] / |Γ(U)|`."*

That pulls a constant out of a maximum. It is valid only for `c ≥ 0`. For `c < 0`
the maximum of a negative multiple is attained where the multiplicand is
**smallest**:

`max_x [c · E_P(Y ∣ x)] = c · min_x [E_P(Y ∣ x)]`.

And `c < 0` precisely when `|Γ(U)| ≥ 3` — the range the source's own footnote to
Proposition 8 singles out. At `|Γ(U)| = 2` the factor is zero and both readings
agree, which is why the slip is invisible in the binary case.

### What the instance shows

The twelve-state model differs from Example 6 in one respect only: the mass is
arranged so that `E_P(Y ∣ x)` is **not** constant in `x`, taking `0` at one setup
and `1/3` at the other.

| | |
|---|---|
| true accuracy, `ex6_accuracy` | `0` |
| Proposition 8's bound, `ex6_prop8_bound` | `−1/9` |
| `ex6_bound_not_attained` | the bound is **strictly** below the accuracy |
| `ex6_prop8_holds` | Proposition 8 nevertheless holds, from `inferenceAccuracy_ge` |

So Proposition 8 is untouched; what fails is the sharpness claim made through
this construction. Example 6 computes the accuracy correctly only when
`E_P(Y ∣ x)` does not depend on `x`, or when `|Γ(U)| = 2`. For a device whose
inference power varies across setups — the general case the example claims to
cover — it overstates how small the accuracy is.

### A smaller slip in the same display

The intermediate numerator is printed as
`a_x + (|Γ(U)|−1)b_x − (|Γ(U)|−1)a_x + b_x`, which expands to
`(2 − |Γ(U)|)a_x + |Γ(U)|·b_x`, not to the `(2 − |Γ(U)|)(a_x − b_x)` the next
equality asserts. Changing the final `+ b_x` to `− b_x` makes the two agree, so
this reads as a typo rather than a mathematical error, and the identity it leads
to is the correct one. Recorded for completeness only.

## 26. Corollary 21(ii)'s two implications are transposed

**The two implications are transposed in the source. The transcription reads
them in the order the proof requires, and the transposition is recorded as the
author's.**

Printed, and identical in the published PDF, the arXiv HTML and the LaTeX source:

> ii) Say that `W` refines `Γ₁ ⇒ Γ₂` and refines `Γ₂ ⇒ Γ₃`. Then if either `D`
> both knows that `Γ₁ ⇒ Γ₂` is true and `Γ₂ ⇒ Γ₃` is true, or `Γ₁ ⇒ Γ₂` is true
> and `D` knows that **`Γ₁ ⇒ Γ₃`** is true it follows that **`Γ₂ ⇒ Γ₃`** is true.

The lead-in says these *"weaken the last two claims in Coroll. 20"*, and
Corollary 20(iii) reads:

> iii) …if `D` both knows that `Γ₁ ⇒ Γ₂` is true and knows that `Γ₂ ⇒ Γ₃` is
> true, it follows that **`Γ₁ ⇒ Γ₃`** is true.

A weakening keeps the conclusion and relaxes a premise. Corollary 20(iii)
concludes `Γ₁ ⇒ Γ₃`; the printed Corollary 21(ii) concludes `Γ₂ ⇒ Γ₃` and puts
`Γ₁ ⇒ Γ₃` in the premise instead. **The two have been swapped.** The single
transposition that repairs it:

> …or `Γ₁ ⇒ Γ₂` is true and `D` knows that `Γ₂ ⇒ Γ₃` is true, it follows that
> `Γ₁ ⇒ Γ₃` is true.

`corollary21_ii_repaired` proves that statement. Status **REPAIRED** rather than
`REFUTED`, on the ruling above: a corrupt sentence whose intended content is
recoverable from the surrounding text is a different thing from a false claim.

`corollary21_ii_counterexample` is **retained** and still refutes the sentence as
literally printed, so nothing about the printed defect is erased by the regrade —
only the grade moves.

## 27. The weakened knowledge operator's probe subscript contradicts its own gloss

**`δ_γ` is a typo for `δ_{γ′}`; the `δ_{γ′}` reading is the transcribed one.**

Verbatim from the LaTeX source (`arxiv.org/src/1711.03499v3`):

```latex
However for all $\gamma' \ne \gamma$,
we only require that for all $u \in W \cap \xi(\gamma')$, if $Y(u) = -1$, then
$\delta_\gamma(\Gamma(u)) = Y(u)$. Under this modification, we would allow there to be $u$ outside
of $W$, and $\gamma' \ne \gamma$, where the device is answering the question, ``does $\Gamma(u) = \gamma'$?'' 
and incorrectly answers `no'.
```

The formula demands `Γ(u) ≠ γ` on the block `ξ(γ′)`. The sentence immediately
after describes the device answering *"does `Γ(u) = γ′`?"*, which is `δ_{γ′}` and
demands `Γ(u) ≠ γ′`. The two are not equivalent, and only one makes the
modification a **weakening**:

* under `δ_{γ′}`, Definition 11 entails it — `weakPhysicallyKnows_of_physicallyKnows`;
* under the printed `δ_γ` it does not, because Definition 11 permits a state of
  `ξ(γ′)` to carry the value `γ` while the device answers `false` there.

Since the paper introduces this as a *weakening*, `δ_{γ′}` is the reading that
makes the paper's own description true. Status **REPAIRED**.

Two pieces of corroborating evidence, both from the source rather than the
rendered text:

1. An **author comment left in the LaTeX**, immediately after this passage:

   ```latex
   %This weakened definition of physical inference would not substantially affect the discussion
   %above. In particular, logical omniscience could still be violated. \dhwc{Check that this weakened
   %form really would solve the problem --- and also would not give logical omniscience.}
   %Since it is more complicated to define and analyze though, it is now pursued here.
   ```

   The author had not finished checking the passage. (Its last line is itself a
   typo for *"is not pursued here"*.)

2. The negative-answer clause **is** stated cleanly enough to lift. A
   `pdftotext` rendering flattens `γ′ ≠ γ` to `γ′, γ`, which does make the clause
   unsatisfiable, and that rendering is not the source. The inequality is present in the HTML and in the source. A
   defect in the extraction had been recorded as a defect in the paper.

## 28. Proposition 7(2) cannot support the `|U| > 3` universal-device sentence

A **cited justification that does not support its conclusion**. Not a false
statement (the conclusion is true) and not a garbled one (the words parse).
Weaker evidence than clashes 26 and 27, where the source's own adjacent text
contradicted itself. This entry states the structural argument and does not
claim to know the author's intent.

2018, after Definition 10, printed:

> *"Prop. 7(ii) means that no reality with `|U| > 3` can have a universal
> device if the reality contains all functions defined over `U`."*

Proposition 7(2) is *"there is a pair of functions `(S, T)` that no device
strongly infers."* An existential over **pairs**. A universal device is one
that strongly infers every other **device** of the reality and weakly infers
every function of the reality. Clause 1 of that definition is a universal
quantifier over the devices *of a reality*.

The gap is that the witness must be **carried by a device of the reality**
before it says anything about that reality's devices. 7(2) exhibits a pair of
functions and no device; universality is refuted only by a device the reality
actually contains.

**The relation itself is not the problem.** `stronglyInfers_iff_stronglyInfersPair`
proves `StronglyInfers C₁ C₂ ↔ StronglyInfersPair C₁ C₂.setup C₂.concl`: at a
device's own pair, Definition 4 and Definition 5 are the same relation, which is
what makes Definition 4 a conservative generalization. So *if* some device of the
reality had `(S, T)` as its setup/conclusion pair, 7(2) would refute clause 1 for
that device exactly. There is one mismatch here, not two, and it is entirely
about the witness.

Which is what makes the source's own witness decisive. Proposition 7(2) takes
`S = T = id`. That pair is a *device* pair only when the second component can
be a conclusion function, i.e. only when `U = Bool` and so `|U| = 2`.
`id_is_device_pair_on_bool` records the one case that works. The printed
`|U| > 3` excludes it outright — so the printed hypothesis destroys the printed
witness, and the citation has nothing left to run on.

The adjacent numbered result that *does* run on clause 1 is Proposition 5(i),
*"there is a device `C₂` such that `C₁ ⋙̸ C₂`"*, which quantifies over devices
and needs no bridge. **This note does not claim that is what was meant.**

The conclusion is nevertheless true, and needs no cardinality. A universal
device must weakly infer every function in the reality. If that family
contains the device's own conclusion — and under the source's two-value
stipulation a conclusion is admissible: it is surjective onto `𝔹`, so
`func_two` holds, `func_two_of_concl_mem` — then Proposition 1(ii) forbids
universality. `not_isUniversalFull_of_concl_mem` is that argument;
`not_isUniversalFull_of_containsEveryTwoValuedBool` is the printed
conclusion, without `|U| > 3`, under the reading of *"all functions"* that
`SourceStipulations` itself permits (constants fail `func_two` and cannot
appear). `|U| > 3` does no work on this route.

Status **REPAIRED**: the statement's conclusion is a theorem; the printed
justification is replaced; the defect is recorded rather than erased. The
`|U| > 3` hypothesis is vestigial on every correct route, and is dropped.

A slip on the surrounding numbering is plausible — `|Γ(U)| ≥ 3` in 7(1), *"at
least two elements"* in the Proposition 7 preamble, `|X(U)| > 2` in 2008
Corollary 2 — but this entry asserts nothing about which was intended.
