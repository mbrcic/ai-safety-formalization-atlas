# Source coverage audit

Every statement in the sections of the five sources the atlas formalizes from,
checked one by one against the Lean and against the published text of each; last
revised 2026-08-17.

**Coverage** is semantic rather than name-based: can a competent reader derive
the printed statement from the cited kernel-checked declarations? `Yes` permits
ordinary specialization, definitional unfolding, algebraic rearrangement, and
an explicitly described representation isomorphism. `Partial` means that a
substantive source conclusion, quantifier, or bridge is still unproved; `No`
means that no part of the printed statement is obtained.

**The object rule.** Notation need not be mirrored, and a definition need not
occur as a separately named declaration — *unless the printed statement is
about that object*. When the source constructs something and then asserts a
property **of the construction** — a minimum over a named family, a maximum
over a named family, a specific feasible set, a specific capacity — then a
proxy for that object does not cover the claim, however close the proxy is and
however safe the inequality between them happens to point. Build the object or
grade `Partial`.

Three rows turn on it, and each names the object the rule required:

* Touchette–Lloyd Theorem 2's *equality case* is about a **minimizer** of eq.
  (28). A realized-policy infimum is a proxy for it;
  `kernelMinControlLoss` declares the printed minimum over `{p(c\|x)}` and the
  two are proved equal. `Yes`.
* Touchette–Lloyd Theorem 10 is about the **maximum** of eq. (48) over an
  arbitrary transition kernel family. A supremum over an independent-noise
  family `F(X,C,Z)`, with no realization theorem connecting the two, is a proxy
  on two counts — family and `max`. Both are closed rather than argued away:
  `AISafetyAtlas.Control.Purification` proves every Markov kernel is `F(x,c,Z)`
  for an exogenous seed and `openLoopMax_purifyMap` proves the two families
  generate the *same set* of reductions, while `isGreatest_kernelOpenLoopMax`
  proves the supremum attained, so `sSup` *is* the printed `max`. The row is
  `Yes`. The rule earns its place here: it named two specific objects to build,
  and both are built.
* Ashby §11/11 is about Ashby's **capacity**. `channelCapacity O = log \|O\|` is
  the noiseless alphabet ceiling, not the §9/15 entropy rate — a proxy. That is
  now closed the way the rule says to close it: `chainRate` declares §9/12's
  printed quantity, `ashbyCapacity` §9/15's rate, and
  `entropy_outcome_ge_sub_chainEntropy` states the row's claim against it. `Yes`.
  All three rows the rule was written for are now `Yes`, and none of them moved
  on a re-reading.

An unproved equality or attainment claim about two infima is likewise not an
ordinary representation change.

**Stability.** A row moves on new Lean, or on source evidence that a quotation
here is wrong. **A row does not move on a re-reading of a text already read.**
Where a grade has been contested, its note names the rendered page that settles
it, so the next reader argues with the page and not with the grade. This rule
exists so that a grade is argued against the page, not re-argued from memory.

No row is held by anything except its own evidence. Every row stands or falls on
the same reading — whether the atlas statement implies the printed one.

**Scope** — how the atlas statement compares in generality:

| verdict | meaning |
|---|---|
| **Wider** | the atlas statement implies the printed one, and not conversely |
| **Same** | they are the same statement |
| **Narrower** | the printed statement implies the atlas one, and not conversely |
| **Mixed** | wider on one axis, narrower on another — the interesting case, always explained |
| **Beyond** | the atlas proves something the source does not state at all |

**The standing rule: scope ≥ print wherever that is achievable.** A `Narrower`
or `Mixed` row is a defect unless the narrowing is discharged, so every narrower
axis must be labelled with which of three states it is in:

* **not a narrowing** — a units restatement or a representation change, with the
  converting lemma named. Regrade it rather than carrying it.
* **provably not closable** — with the witness that proves it. None currently,
  as a graded axis.
* **open, and costed** — with what it would take. Cover & Thomas Thm 2.5.2's
  arity is the only one, and since the sample-space sweep below struck that
  row's widening half it is now the audit's only `Narrower` and there is no
  `Mixed` row left: general `n` needs
  prefix-tuple machinery (`Measurable` and `FiniteRange` transport through
  `fun ω => fun i : Fin k => X i ω`) that neither Mathlib nor PFR has, where
  §2.8 uses only `n = 2`.

**The sample space is not a scope axis.** Taking an arbitrary measurable space
where the source fixes a discrete one is not a widening. The atlas variables are
`FiniteRange`, so they push the measure forward to a pmf on finite alphabets, the
printed statement applies to *that* pmf and returns the same conclusion, and the
atlas statement at `(Ω, μ, X, …)` **is** the printed statement at the pushforward.
The two are inter-derivable, so the space is a presentation and not a generality.
Both sources this bears on — Cover & Thomas §2.8/§2.10 and Touchette–Lloyd —
state their theorems for discrete distributions on finite alphabets, which is the
hypothesis the argument needs; the Touchette–Lloyd setting is recorded in
`touchette-lloyd-control.md` against the published text.
`AISafetyAtlas.Examples.InformationTheory.ContinuousSampleSpace` works the case
out at concrete data.

Two things follow, and neither is a widening either. Proving something a source
asserts without proof is **coverage**. Bringing a `sSup` up to a printed `max`
brings the atlas level with print rather than past it. Both belong in a row's
note, not in its scope cell.

The one object genuinely outside print's reach is the **zero** measure admitted
by `IsZeroOrProbabilityMeasure`, where every entropy is `0` and every inequality
here is `0 ≤ 0`. That is vacuity, it is graded as nothing, and it does not
license a `Wider`.

**Exercises are not graded statements.** What gets a row is what a source
*argues* — theorems, lemmas, corollaries, and the remarks and worked examples
an author asserts in the body. Exercises set for the reader do not, and no
exercise is a graded row anywhere in this audit. The reason is reuse: a theorem
is an object something downstream can be built on, an exercise is a one-off,
and grading the latter lets a puzzle answer set a scope verdict for a section
whose actual claims are covered. Ashby §11/14 was the one row that broke this
and it read `Mixed` for it. Exercises still earn their keep as **checks** —
`Examples…ashbyInsect_rate_eq` evaluates Ashby's own arithmetic term by term,
and `Examples…ashbyControl_capacity_lt_sum` records that his Ex. 4 answer does
not follow from the diagram alone — they just do not grade anything.

The rule licenses dropping a hypothesis the proof does not use. It does **not**
license restating a printed claim as a different one that happens to grade
better — a conditional theorem under an added hypothesis proves something print
did not say, and belongs in a `Beyond` row or nowhere.

Representation alone does not change scope. Replacing `{1, …, n}` by the
order-isomorphic type `Fin n`, changing notation, or exposing an implicit
parameter is `Same`. `Wider` and `Narrower` require a strict logical change in
hypotheses or conclusions, not merely a different encoding.

**Counting.** A row is counted in exactly one column. `Beyond` rows are the ones
whose Coverage cell is `—`: they record something the atlas proves that the
source does not state, so there is no printed statement to grade. A row that
covers a printed statement is counted under `Yes`/`Partial`/`No` even when its
scope verdict is `Beyond`.

A `No` row is not a defect. These are papers, and the atlas formalizes targeted
results from them, not the papers. The point of listing every `No` is that a
reader can see the boundary without having to reconstruct it.

---

## 1. Cover & Thomas, §2.8 → `AISafetyAtlas.InformationTheory.DataProcessing`

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| (2.117) | `p(x,y,z) = p(x) p(y\|x) p(z\|y)` defines `X → Y → Z` | `isMarkovChain_iff_measure_factorizes_singleton`, `measure_factorizes_of_isMarkovChain` | Yes | **Wider** | the factorization cleared of denominators, `p(y)·p(x,y,z) = p(x,y)·p(y,z)`, so no positivity side condition and the right answer on null fibres of `Y`. `isMarkovChain_iff_measure_factorizes` additionally widens it to arbitrary measurable `s`, `t`, needs only `Y` measurable, and drops countability and measurable singletons on `S` and `U`. Witnessed by `Examples…realValuedMarkovChain`: a chain whose outer two variables are **real-valued**, so neither has a probability mass function and the printed statement cannot be written down at these types, let alone proved |
| (2.118) | `X → Y → Z` **iff** `X` and `Z` are conditionally independent given `Y` | `IsMarkovChain`, `isMarkovChain_iff_measure_factorizes_singleton`, `isMarkovChain_iff_condMutualInfo_eq_zero` | Yes | **Wider** | the atlas *defines* `IsMarkovChain X Y Z μ := CondIndepFun X Z Y μ`, taking (2.118)'s right-hand side where the book takes (2.117), so the equivalence has to be earned rather than assumed — and it is, at the printed hypothesis in both directions. `measure_preimage_inter_eq_tsum` is what carries the reverse direction from point masses to measurable sets, by countable additivity in `X` and in `Z`. Wider than print in also giving the set-level form, and in the operative form 2.8.1's proof uses, conditional independence iff `I(X;Z\|Y) = 0` |
| §2.8 | `X → Y → Z` implies `Z → Y → X` | `IsMarkovChain.symm` | Yes | Same | |
| §2.8 | `Z = f(Y)` implies `X → Y → Z` | `isMarkovChain_comp` | Yes | Wider | any measurable `g`, arbitrary measurable spaces |
| Thm 2.8.1 | `X → Y → Z` ⟹ `I(X;Y) ≥ I(X;Z)` | `mutualInfo_le_of_isMarkovChain` | Yes | Same | the variables are countable of finite range, so they push `μ` forward to a pmf on finite alphabets and the printed theorem applies to *that* pmf, returning the same inequality. The atlas statement at `(Ω, μ, X, Y)` is the printed statement at the pushforward, so the two are inter-derivable and the space is a presentation, not a generality. See `AISafetyAtlas.Examples.InformationTheory.ContinuousSampleSpace`, which records the failed witness that settled this. The one object outside print's reach is the **zero** measure admitted by `IsZeroOrProbabilityMeasure`, where every entropy is `0` and the inequality is `0 ≤ 0`; that is vacuity and is not graded as scope |
| 2.8.1 proof | equality iff `X → Z → Y` | `mutualInfo_eq_iff_isMarkovChain` | Yes | Same | as the row above: the space is a presentation, not a generality. That the source asserts this mid-proof without proving it is a **coverage** fact and is why `Cov.` is `Yes`; it is not a scope axis |
| 2.8.1 proof | "similarly, one can prove `I(Y;Z) ≥ I(X;Z)`" | `mutualInfo_le_of_isMarkovChain'` | Yes | Same | as two rows above: the space is a presentation, not a generality. That the source says "similarly, one can prove" and does not is **coverage**, not scope |
| Cor. (unnum.) | `I(X;Y) ≥ I(X;g(Y))` | `mutualInfo_comp_le` | Yes | Wider | |
| Cor. (unnum.) | `X → Y → Z` ⟹ `I(X;Y\|Z) ≤ I(X;Y)` | `condMutualInfo_le_mutualInfo` | Yes | Wider | |
| Thm 2.5.2 at `n = 2`, used inline as (2.119)/(2.120) | `I(X₁,X₂;Y) = Σᵢ I(Xᵢ;Y\|X_{<i})` | `mutualInfo_chain_rule`, `mutualInfo_chain_rule'`, `mutualInfo_sub_eq` | Yes | **Narrower** | the sample space is a presentation and not a generality (see the note above), so the only axis here is that the printed theorem is for `n` variables and this is `n = 2` in both argument orders. The axis is **open, and costed** — see the standing rule above — and this row is now the audit's only `Narrower`. §2.8 uses the two expansions without restating them, and the general form is printed ten pages earlier as Theorem 2.5.2, so this is printed content rather than `Beyond`. `mutualInfo_sub_eq` is the two expansions subtracted, so it belongs here rather than in a `Beyond` row of its own |
| Remark + example | conditioning **can** increase `I` off a Markov chain: `X, Y` fair bits, `Z = X+Y`, `I(X;Y) = 0` but `I(X;Y\|Z) = ½` bit | `Examples…condMutualInfo_eq_half_bit_of_intSum`, `…condMutualInfo_gt_mutualInfo_of_parity` | Yes | **Wider** | the first is the printed example at the printed numbers — `Z` the **integer** sum, three-valued, and `I(X;Y\|Z) = ½` bit, which is what the printed `P(Z=1)` factor requires. The second replaces `Z` by `X ⊕ Y` and gets a full bit, a strictly larger gap. Either makes the Markov hypothesis of `condMutualInfo_le_mutualInfo` load-bearing rather than assumed to be |

**11 Yes, 0 Partial, 0 No.** Section fully formalized, counterexample included, and nothing left in the `Beyond` column. The row that sat there is printed content — Theorem 2.5.2 at `n = 2` — and `mutualInfo_sub_eq` is those two expansions subtracted, so it shares that row.

The first two rows are the section's definitional pair. `IsMarkovChain X Y Z μ`
is `CondIndepFun X Z Y μ`, which is (2.118)'s right-hand side, while the book
starts from the factorization (2.117). Both are graded, and the equivalence
between them is proved at the printed point-mass hypothesis rather than at the
stronger set-level one.

`isMarkovChain_iff_measure_factorizes_singleton` closes it. Both directions now
run at the printed strength:

* **Markov ⟹ factorization** at the printed point masses
  (`measure_factorizes_of_isMarkovChain`), and in fact at every measurable `s`,
  `t`.
* **Factorization ⟹ Markov** from point masses alone, via
  `measure_preimage_inter_eq_tsum` — a measurable slice of a countable-valued
  variable splits over its point masses — applied once in `X` and once in `Z`.

So the choice of definition is a presentation detail and not something the rest
of the section trades on.

The counterexample — `X, Y` fair bits, `Z = X + Y`, where conditioning *raises*
mutual information — is now `condMutualInfo_gt_mutualInfo_of_parity`. Until it
landed, `DataProcessing.lean` asserted in prose that the Markov hypothesis of
`condMutualInfo_le_mutualInfo` is load-bearing and nothing checked it, which is
the standard `nfl_fails_off_permInvariant`, `not_openLoopBound_erase` and
`entropy_eq_fano_of_witness` exist to meet. Every entropy in it is read off a
cardinality: the single bits are uniform, and each pairing of two of the three
variables is an injective recoding of the whole state, so carries `log 4`.

---

## 2. Cover & Thomas, §2.10 → `AISafetyAtlas.InformationTheory.Fano`

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Thm 2.10.1, 1st ineq. | `H(Pe) + Pe·log\|𝒳\| ≥ H(X\|X̂)`, `X̂` alphabet **unrestricted** | `fano_unrestricted`, `fano_of_embedding` | Yes | **Wider** | print says as much (*"we will not restrict the alphabet X̂"*), so that is not the axis. `fano_of_embedding` takes it in a genuinely different *type*, via an injection carrying `X`'s alphabet into it, so "different alphabet" is literal rather than covered through a common ambient. Witnessed by `Examples…fano_of_verdict`, Fano against an estimator that may **abstain**: its extra value is not a value of `X`'s alphabet under any relabelling, so this is not the printed statement at a larger alphabet but at a type the printed statement has no way to name. It is also why the sharp `− 1` is unavailable here — a verdict outside the injection's image excludes nothing |
| Thm 2.10.1, 2nd ineq. | `H(X\|X̂) ≥ H(X\|Y)` under `X → Y → X̂` | `condEntropy_le_condEntropy_of_isMarkovChain` | Yes | Wider | lives in the DataProcessing module |
| Thm 2.10.1, chained | both inequalities together | `Examples…fano_of_markov_unrestricted`, `Examples…fano_of_markov_embedding` | Yes | **Wider** | an arbitrary Markov chain rather than `X̂ = g(Y)`, so randomised estimators are covered; and the estimate may change type |
| Cor. (2.139) | any two r.v.s, `H(p) + p·log\|𝒳\| ≥ H(X\|Y)` | `fano_unrestricted` | Yes | **Wider** | `A` is any `Finset` containing `X`'s range, so the constant is `log\|A\|`, at most the printed `log\|𝒳\|` |
| Cor. (2.140) | `X̂ : 𝒴 → 𝒳` a function ⟹ `H(Pe) + Pe·log(\|𝒳\|−1) ≥ H(X\|Y)` | `Examples…fano_of_estimator_chain`, `…fano_of_markov` | Yes | **Wider** | the printed conclusion bounds `H(X\|Y)`, not `H(X\|X̂)`, so the chained form is the one that matches. `fano_of_estimator_chain` keeps the printed "function of `Y`"; `fano_of_markov` is what drops it, taking an arbitrary Markov chain and so covering randomised estimators. Both carry the sharp constant, and `A ⊊ 𝒳` is allowed |
| (2.131) | `1 + Pe·log\|𝒳\| ≥ H(X\|Y)` | `Examples…fano_le_log_two_add_of_markov` (from `fano_le_log_two_add`) | Yes | **Wider** | the printed weakening bounds `H(X\|Y)`, so the chained form is the one that matches — the same correction row (2.140) received. Printed `1` is one bit; at natural logarithm that is `log 2`, a units restatement and not an axis. `Wider` on one axis only: `A` may be a proper subset of `𝒳`, which is a real sharpening. The sample space was formerly claimed here too and is struck — see the §2.8 regrades |
| (2.132) | `Pe ≥ (H(X\|Y) − 1)/log\|𝒳\|` | `Examples…le_errorProb_of_markov` (from `le_errorProb`) | Yes | **Wider** | the form converses use, and it too bounds `H(X\|Y)`. `2 ≤ \|A\|` is the source's own implicit hypothesis — it divides by `log\|𝒳\|` |
| Remark | no-observation form `H(Pe) + Pe·log(m−1) ≥ H(X)` | `entropy_le_fano` | Yes | Wider | the sharp constant survives, because a fixed guess is a value of the alphabet |
| Example | "Fano's inequality is sharp" | `Examples…entropy_eq_fano_of_witness` | Yes | Same | the printed family: mass `1−p` on the guess, the rest uniform. Equality at **every** `p ∈ [0,1]`, so both coefficients are pinned |
| — | the constant as a parameter | `fano_of_log_le` | — | **Beyond** | any `L` dominating `log\|A.erase (X' ω)\|`; both printed constants are instances, and the proof is written once |
| Lemma 2.10.1 | `Pr(X = X') ≥ 2^(−H(X))` for i.i.d. copies | — | No | — | **not Fano.** A collision-probability bound, printed at the end of §2.10 as a separate lemma with its own proof by Jensen. Nothing in the atlas wants it: no row bounds a probability of agreement between independent draws, and the Fano cluster does not route through it |
| Cor. (2.149)–(2.150) | `Pr(X = X') ≥ 2^(−H(p)−D(p‖r))` and the same with `p` and `r` exchanged, for draws from different distributions | — | No | — | the KL form of the lemma above, and absent for the same reason. It is the only place in either graded section where a divergence appears in a conclusion |

**9 Yes, 0 Partial, 2 No, 1 Beyond.** The **Fano cluster** is complete, at both
printed constants — which is the claim worth making, and is not the same as the
section being complete, and the two rows above are why. Lemma 2.10.1 and
its corollary are printed inside §2.10, they are theorems with proofs, and they
are not in the tree. They are also not Fano, so their absence is not a gap in the
Fano work — same shape as the two `No` rows under Touchette & Lloyd, which are
printed results nothing downstream wants.

Closing it took one observation. The two printed constants differ only in how
many values the truth can still take once the estimate is known wrong: on the
error fibre over `X' = y` that is `A.erase y`, which has `|A|−1` elements when
the estimate is confined to `A` and at most `|A|` when it is not.
`fano_of_log_le` takes that bound as a parameter, so `fano` and
`fano_unrestricted` are both instances of one proof rather than two proofs.

---

## 3. Ashby, *Introduction to Cybernetics* ch. 11 → `AISafetyAtlas.Control.RequisiteVariety`

| § | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| 11/5 | `r` rows, `c` cols, no repeat in a column ⟹ outcome variety `≥ r/c` | `ashby_variety_ge`, `card_ceilDiv_le_admittedOutcomes` | Yes | **Wider** | any `Fintype`; and the bound is proved in its **integer** form `⌈\|D\|/\|R\|⌉`, which is what a count of outcomes can attain — the printed rational `r/c` is not attainable when `c ∤ r` |
| 11/5 gen. | the multiplied form | `card_le_mul_card_admittedOutcomes` | Yes | Wider | any `Finset` of disturbances; and **`Set.InjOn` on the fibre the strategy visits** rather than the whole column. The derived statements still take full column injectivity, because they quantify over strategies |
| 11/6 | `n` moves ⟹ variety reducible to `1/n`, "but not lower" | `card_ceilDiv_le_admittedOutcomes`, `ashby_variety_ge_isSharp` | Yes | **Wider** | both halves, at every shape `(r, c)` — no divisibility assumed. What is attained is `⌈r/c⌉`; the rational `r/c` is **not** attainable when `c ∤ r`, which the source's prose does not distinguish. Existence of one such table, not a claim about every table: `T d r = d` has injective columns and admits everything |
| 11/7 | `V_O ≥ V_D − V_R` | `ashby_logVariety_ge` | Yes | Wider | |
| 11/8 | `H(E) ≥ H(D) + H_D(R) − H(R)` | `entropy_ge_of_condEntropy_ge` | Yes | Wider **(repaired)** | the printed conclusion misprints `H_D(E)` for `H_D(R)` |
| 11/8 hyp. | `H_R(E) ≥ H_R(D)` — *assumed* by the source | `condEntropy_outcome_eq` | Yes | **Wider** | atlas **derives** it, and as an equality, from the column condition |
| 11/8 | headline `H(E) ≥ H(D) − H(R)` for determinate `R` | `entropy_outcome_ge_of_strategy` | Yes | Wider | |
| 11/9 | `k` repeats; entropy slack `K`; printed `V_O ≥ V_D − log k − log V_R`, where `V_R` is already logarithmic | `card_le_mul_card_admittedOutcomes_mul`, `ashby_logVariety_ge_mul`, `entropy_ge_of_condEntropy_ge` | Yes | Wider **(repaired)** | `k` and `K` are parameters of the 11/5 statements, not a second argument; `ashby_logVariety_ge` is the case `k = 1`. The printed line carries a second slip of the same kind as 11/8's: `log V_R` where 11/7 has already made `V_R` logarithmic, and `ashby_logVariety_ge_mul` states the corrected form — hence `(repaired)`, on the same footing as 11/8, which is why the marker was added here. (The scan renders `≥` as `>` throughout, so the relation is transcribed as `≥` here and in 11/7's row alike.) Recorded in the provenance note |
| 11/10 | "the law states that certain events are impossible" — the methodological reading | `two_le_card_admittedOutcomes` | Yes | **Wider** | the section is about the law's status (it "owes nothing to experiment"), and the impossibility it points back to is 11/5's. The atlas states the operative form: below a threshold of regulator variety, two outcomes must occur |
| 11/11 | *"R's capacity as a regulator cannot exceed R's capacity as a channel of communication"* | `chainRate`, `chainRate_eq_condEntropy`, `entropy_traj`, `ashbyCapacity`, `entropy_outcome_ge_sub_chainEntropy`, `channelCapacity`, `entropy_outcome_ge_sub_channelCapacity`, `entropy_le_channelCapacity_of_complete` | Yes | **Wider** | Ashby's capacity here is §9/15's **entropy rate**, and the atlas declares that rate rather than proxying it. `chainRate` is §9/12's printed definition — *"the average of these entropies, each being weighted by the proportion in which that state … occurs when the sequence has settled to its equilibrium"* — written from an equilibrium law and a kernel with no sample space, and `chainRate_eq_condEntropy` identifies it with `H[X₁ \| X₀]`. `ashbyCapacity` is §9/15's per-unit-time rate and `ashbyCapacity_rescale` is its conversion sentence. `entropy_outcome_ge_sub_chainEntropy` is this row's claim against that capacity. `Wider` for two reasons. §9/15 *asserts* that *"the entropy of a length of Markov chain is proportional to its length"*; `entropy_traj` proves it, and sharpens it — the identity is `H[X₀ … Xₙ] = H[X₀] + n · rate`, **affine** and not linear, the two agreeing exactly when `H[X₀]` equals the rate, which is what happens in the spun-coin case Ashby checks it against. Same class of printed slip as §11/8's `H_D(E)` — but this one is **§9/15's**, not this row's own printed sentence, so the row is plain `Wider` and not `Wider (repaired)`, which is reserved for a row that repairs a slip in the very statement it grades. Note also which direction the correction runs: `H[X₀] + n · rate` is a *larger* budget than `n · rate`, so the affine form makes `H[E] ≥ H[D] − budget` a weaker conclusion — a bare capacity-times-time budget is not an upper bound on what a regulator can carry, because the initial state has entropy of its own. And both capacities are kept: the alphabet ceiling is still the sharp form for the four exercises, which count signals. **The definition is checked against Ashby's own arithmetic**, which is what earlier gradings lacked: his chain has the exactly rational equilibrium `(22/49, 21/49, 6/49)`, decimals `0.4490, 0.4286, 0.1224` against his printed `0.449, 0.429, 0.122`. `Examples…ashbyInsect_stationary` proves the balance equations, `…ashbyInsect_proportions_match_print` the rounding, `…ashbyInsect_rate_eq` evaluates `chainRate` to his weighted average term by term. Noisy Shannon capacity `sup I(in ; out)` is still not modelled and is not needed: §9/15 defines capacity by the rate |
| 11/11 | the homology with **Shannon's Theorem 10**: *"the law of Requisite Variety can be shown in exact relation to Shannon's Theorem 10, which says that if noise appears in a message, the amount of noise that can be removed by a correction channel is limited to the amount of information that can be carried by that channel"*, with the dictionary *"his 'noise' corresponds to our 'disturbance', his 'correction channel' to our 'regulator R', and his 'message of entropy H' becomes … a message of entropy zero"* | — | No | — | a printed correspondence claim, book p. 211, PDF p. 112 of `ashby-1961-introduction-to-cybernetics.pdf`, and **not** covered by the row above. Formalizing it needs Shannon's Theorem 10 stated and the atlas's bound identified with its image under Ashby's own dictionary; the noisy Shannon capacity that Theorem 10 is about is not modelled. Ashby writes *"can be shown"* and then gives the dictionary rather than an argument, so print does not prove it either. Split out on 2026-08-17 after being folded into §11/11's `Yes`, which was the audit being generous to itself |
| 11/1–11/4 | regulation restated; play and outcome; the Table | the `admittedOutcomes` model of the Table | No | — | setup and definitions. The Table is transcribed as the model everything else is stated over, but there is no printed statement here to grade |
| 11/14 | **control**: *"perfect regulation of the outcome by R makes possible a complete control over the outcome by C"*, and the compound channel | `IsPerfectRegulator`, `outcome_eq_comp`, `exists_strategy_forcing`, `seq_outcome_eq`, `admittedOutcomes_of_isPerfectRegulator`, `card_disturbance_le_card_regulator`, `card_controller_le_card_regulator`, `FactorsThrough`, `channelCapacity_controller_le_channel`, `channelCapacity_disturbance_le_channel`, `max_channelCapacity_le_channelCapacity_regulator`, `condEntropy_outcome_controller`, `entropy_outcome_eq_entropy_controller`, `mutualInfo_outcome_disturbance_eq_zero` | Yes | **Wider** | `outcome_eq_comp` is the section's first half entire — under perfect regulation the outcome is a function of `C` **alone**, `D` eliminated rather than bounded — with complete control `exists_strategy_forcing` and the printed compound target `a, b, a, c, c, a` `seq_outcome_eq`. The compound-channel picture is both clauses: `entropy_outcome_eq_entropy_controller` is *"transmits fully from C"*, `condEntropy_outcome_controller` is *"transmitting nothing from D"* and needs **no hypothesis on the disturbance's law**, with `mutualInfo_outcome_disturbance_eq_zero` the form under Ashby's own *"D's values and C's not correlated"*. **Wider** on the second half: *"the achievement of control may thus depend necessarily on the achievement of regulation"* is qualitative in print and here is a count, and a count derived from §11/10's own impossibility theorem rather than a fresh argument — perfect regulation collapses `admittedOutcomes` to a singleton, which `two_le_card_admittedOutcomes` forbids below a threshold, giving `\|D\| ≤ \|R\|` and `\|C\| ≤ \|R\|`. Requisite variety charged twice, once per input. **No narrower axis on the graded statement.** The four capacity exercises used to pull this row to `Mixed`; they are **exercises set for the reader**, not claims the section argues, and no exercise is a graded row anywhere in this audit — the printed body is what the scope cell grades. Three clauses were previously listed as narrowings and none of them is one. *Units*: the exercises are quoted in bits per second and these are capacities per use, but that is a restatement the atlas already proves — `ashbyCapacity` divides a rate by a step duration, `ashbyCapacity_rescale` is §9/15's own conversion sentence, and `ashbyCapacity_mul` recovers the entropy from rate times time. *`FactorsThrough`*: Ashby **assumes** the two-input diagram rather than deriving it — he writes *"then a suitable regulator R, taking information from both C and D, and interposed between C and T"*, draws it, and opens Ex. 2 with *"If, in the last diagram of this section…"*, so all three exercises are explicitly conditional on it. Taking it as a hypothesis is what print does, which is `Same`. *Ex. 4*: **recorded because the result is worth knowing, not because it grades the row.** Its printed answer **adds** the two loads, *"as these two are independent (D's values and C's not correlated), the capacity must be at least 22 bits/sec"*; what the model forces is the **maximum**, `max_channelCapacity_le_channelCapacity_regulator`. Additivity is a property of the table, not of the diagram: `Examples…ashbyControl_capacity_lt_sum` runs on Ashby's own answer to Ex. 1 — a perfect regulator on Table 11/3/1 with a repertoire of `log 3` where the additive reading demands `log 9`. This is a limit on what the general model implies and **not** a correction to his arithmetic, since Ex. 4 inherits Ex. 2's attenuating `T` while Table 11/3/1 attenuates nothing. `channelCapacity_prod` is the lemma that would license the sum where the `R → T` link really is two independent sub-channels. **Ashby's answers are not in the pinned scan** — that copy jumps book p. 273 to p. 289, omitting *Answers to Exercises* — so they are read from the Martino Fine Books (2015) reprint, book p. 285, and the reprint is named at every quotation |
| 11/12–11/13, 11/15 | the diagram of immediate effects and Sommerhoff's directive correlation; the biological reading; *"constant" and "varying" often depend on the exact definition of what is being referred to* | — | No | — | §11/12 and §11/13 are the law's application to the gene-pattern and to survival; §11/15 argues that treating every target as *"keep the outcome constant at a"* costs no generality, since a regulator holding `x − y` at zero is forcing `x` to copy `y`. Methodological rather than mathematical: there is no printed statement here to grade. These stay `No` because nothing in them is formalized, not because the means are missing |
| 11/16–11/21 | *Some variations*: compound disturbance, noise, initial states, compound target, internal complexities | — | No | — | §11/16 introduces the part; the five cases argue the basic formulation already covers them by vectorising — `D` for compound disturbance and noise, **`E`** for compound target — which the atlas's arbitrary `D` and `E` permit. No new statement |

**11 Yes, 0 Partial, 4 No.** Chapter 11 runs §11/1–§11/21 over printed pp. 202–218,
and all twenty-one sections are accounted for. The `No` rows cover the setup
(§11/1–11/4), the applications other than §11/14 (§11/12–11/13, §11/15) and the
whole closing part headed *Some variations* (§11/16–11/21). §11/14 is the one
among them carrying a statement rather than a gloss, and it is formalized in
`AISafetyAtlas.Control.CompleteControl`; the remaining `No` rows are setup,
methodology and the closing part's five arguments that the basic formulation
already covers their cases.

**The source page for §11/11's capacity.** §9/15 was rendered and read at book
p. 180, PDF p. 97 of `ashby-1961-introduction-to-cybernetics.pdf`, and the quoted
sentence is recorded verbatim there. That page, not any summary of it, is what
this row's grade answers to.

One gloss offered in review and *not* adopted, because the page refutes it:
that Ashby "then applies Shannon's theorem — any channel with this capacity can
carry the report". No such sentence appears in §9/15. The section ends with the
behavioural definition of "channel" and runs into §9/16 *Redundancy*. Ashby is
measuring capacity by the rate, as printed.

**Why this row needs its own note.** Ashby bounds the regulator by a *capacity*
in bits per second. `entropy_ge_of_sensor` bounds by the entropy of one reading,
and the §11/11 exercises are arithmetic over noiseless signal counts, so neither
is the printed quantity: any grade resting on those alone rests on a reading of
§9/15 rather than on what §9/15 declares.
`AISafetyAtlas.Control.ChannelRate` declares the entropy-rate capacity itself,
and `Examples…ashbyInsect_rate_eq` checks that declaration against Ashby's own
arithmetic, which is what puts this row on the page instead.

Why the reading settled where it did. The sentence about capacity follows a
worked three-state Markov example: Ashby computes its
probability-weighted entropy as `0.842` bits per step, converts it to `2.53` bits
per minute, and calls *such a rate* the natural measure of channel capacity. The
alphabet ceiling would instead be `log₂ 3` bits per step. The later phrase
"variety available at each step" therefore cannot honestly be read as defining
capacity to be the alphabet cardinality in all cases.

The four §11/11 exercises do use noiseless signal counts, so `channelCapacity O
= log |O|`, `channelCapacity_fun`, and `channelCapacity_prod` reproduce their
arithmetic. That established a real partial result and not the general claim,
which is what kept this row `Partial` for six gradings. The general claim is now
covered too: `chainRate` is §9/12's entropy of one step, `ashbyCapacity` is
§9/15's per-unit-time rate, and `entropy_outcome_ge_sub_chainEntropy` is §11/11's
bound against it. Noisy Shannon capacity `sup I(in ; out)` is still not modelled,
and §9/15 does not ask for it — it defines capacity by the rate.

`channelCapacity` closes the exercises' noiseless case.
`entropy_outcome_ge_sub_channelCapacity` is an alphabet-ceiling consequence and
`entropy_le_channelCapacity_of_complete` is the form the exercises use, that
complete regulation *requires* capacity at least the disturbance entropy. Three
of the four printed exercises are worked at Ashby's own numbers: the insect's
optic nerve carries `2000 log 2` a second against ten dangers at `10 log 2`; the
ship's telegraph and wheel together carry `log 9 + 5 log 50` in five seconds,
which is the upper limit on disturbances Ex. 2 asks to be estimated; and the
general's ten signallers carry `576000 log 2` a day against ten divisions at
`10^7 log 2`.

**Two limits stated rather than glossed, one of them since removed.** The
the exercises' noiseless `log |O|` ceiling is the sharp form for those four;
`AISafetyAtlas.Control.ChannelRate` now supplies the general entropy-rate reading
as well, leaving only noisy Shannon capacity unmodelled. And every statement here
is a **necessary**
condition — Ex. 1 asks whether a channel is "sufficient to enable it to defend
itself", and what is proved is only that the constraint does not bind. Ex. 3 asks
in the direction the law settles, and there the conclusion is a real
impossibility.

11/6 was the last `Partial`. Its *"but not lower"* half had been proved in
general while the *achievability* half existed only as a 4×2 example, which made
the row narrower than a source that states the reduction for any number of
moves. `ashby_variety_ge_isSharp` supplies the general witness: a disturbance is
a pair, the regulator's move shifts the second coordinate, and playing that
coordinate cancels it. The regulator absorbs exactly as much variety as it has
moves — matching `ashby_variety_ge` with equality at every shape.

---

## 4. Igel–Toussaint 2004 and Schumacher–Vose–Whitley 2001 → `AISafetyAtlas.Learning.Sharp`

Both papers quantify over **non-repeating black-box** search algorithms, which
choose each query from the costs already seen. That class is `AdaptiveRule` plus
`∀ c, Injective (ruleVisit r c)`, and every row below is stated over it.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| IT Thm 1 | uniform NFL | `no_free_lunch_adaptive_of_sharp`, `no_free_lunch_stochastic_of_sharp`, `nfl_mixture_of_permInvariant` | Yes | **Wider** | print quantifies over *any* performance measure `c` and over `m ∈ {1,…,\|X\|}`, and dropping `m ≤ \|X\|` adds only instances where the no-revisit hypothesis is unsatisfiable, so that is not a widening. **The algorithm class was where it lost, and no longer does.** Print says *"any two (deterministic or stochastic, cf. [1]) algorithms `a` and `b`"*, citing Droste–Jansen–Wegener, and `AdaptiveRule` is deterministic. Igel's own later survey defines what the citation buys: *"a randomized search algorithm a can be described by a probability distribution pₐ over deterministic search behaviors [6]"*, with the performance written as *E{c(Y(f, m, a))} = ∑ over a′ ∈ A of pₐ(a′)·c(Y(f, m, a′))*. `mixtureTrace` **is** that equation and `nfl_mixture_of_permInvariant` is the theorem over it, so the quantifier is now met at the source's own definition rather than at a proxy for it. **Wider on the mixture weight.** DJW write *"a probability distribution p = (p₁, …, p_m)"*; `nfl_mixture_of_permInvariant` takes `p q : AdaptiveRule X Y m → ℝ` with neither nonnegativity nor normalization, requiring only equal total mass, so signed mixtures are admitted. Same widening as the signed objective weights already credited on IT Thm 5, one level up — there on the weight over objectives, here on the weight over algorithms. `nfl_stochastic_of_permInvariant` widens the choice-sequence form the same way |
| IT Thm 2 | sharpened NFL: NFL over a **set** `F` iff `F` c.u.p. | `nfl_adaptive_of_closedUnderPermutation`, `closedUnderPermutation_of_nfl`, `nfl_mixture_of_permInvariant` | Yes | **Wider** | necessity needs the hypothesis only for **schedules** at one length, a strictly smaller family than the source assumes it for. Sufficiency now holds at the source's stochastic class as well as its deterministic one, by `nfl_mixture_of_permInvariant`, so the algorithm axis is met at the source's own definition rather than argued away |
| IT Thm 5 | non-uniform sharpened NFL, for a distribution `p` | `nfl_adaptive_iff_permInvariant`, `nfl_mixture_of_permInvariant` | Yes | **Wider** | weight class wider: any real weight, with neither nonnegativity nor normalization — including **signed** weights, differences of two priors, for which SVW's NFL4 explicitly declines to state anything and "distribution" is the wrong word. `nfl_mixture_of_permInvariant` carries the same widening on the algorithm axis as IT Thm 2, and the `iff`'s sufficiency direction no longer loses on it |
| IT Lemma 1(1)+(2) | c.u.p. sets are unions of basis classes; `B_h` **is** the orbit | `eq_iUnion_permOrbit`, `basisClass_histogram_eq_permOrbit` | Yes | Same | part (2) is the half with content — `histogram` and `permOrbit` are defined independently, and the lemma says they cut the objectives the same way. Without it, `PermInvariant` (orbits) and the source's Theorem 5 hypothesis (histograms) are not known to be the same condition |
| SVW Theorem | trace of a permuted algorithm, points **and** costs | `ruleVisit_permRule`, `observed_permRule` | Yes | Same | the trace has two coordinates; `ruleVisit_permRule` is the points, `observed_permRule` the costs. Stating only the second would cover half the printed conclusion |
| SVW Cor. (Duality) | `V(A, σf) = V(σA, f)` | `observed_permRule` | Yes | Same | the same identity, read the other way |
| SVW Lemma 1 | c.u.p. ⟹ NFL | `nfl_adaptive_of_closedUnderPermutation` | Yes | **Wider** | an indicator instance of the arbitrary-weight statement |
| SVW Lemma 2 | NFL ⟹ c.u.p. (a **set**, not a weight) | `closedUnderPermutation_of_nfl` (via `permInvariant_of_nfl`) | Yes | **Wider** | hypothesis weaker on three axes: schedules rather than the whole algorithm class, one sample length, and **indicator** measures only — which is exactly Igel–Toussaint's `δ(k, c(Y))` form, so no linearity bridge is needed |
| IT Thm 3, count | non-empty c.u.p. subsets of `Y^X` number `2^C(\|X\|+\|Y\|−1, \|X\|) − 1` | `spectrum`, `spectrum_eq_iff_histogram_eq`, `spectrum_eq_iff_mem_permOrbit`, `surjective_spectrum`, `preimage_image_spectrum`, `closedUnderPermutationEquivSet`, `closedUnderPermutationNonemptyEquivSet`, `card_closedUnderPermutation`, `card_closedUnderPermutation_nonempty` | Yes | Same | the count print states, at print's finite alphabets. The content is `closedUnderPermutationEquivSet`: a permutation-closed set is a set of orbits, an orbit is a basis class by their Lemma 1 — already proved here as `basisClass_histogram_eq_permOrbit` — and a basis class is fixed by the multiset of cost values, so the orbits **are** `Sym Y \|X\|` and Mathlib's `Sym.card_sym_eq_choose` finishes it. Stated as `card + 1 = 2^C(…)` so no truncated subtraction appears. Igel–Toussaint attribute the result to their own earlier paper and prove it there, so this transcribes rather than supplies a proof |
| IT Thm 3, fraction | the fraction of non-empty subsets that are c.u.p. | `card_nonempty_set_objective`, `fraction_closedUnderPermutation` | Yes | Same | the second displayed equation, as an equation in `ℚ`. `Examples…fraction_cup_boolean` evaluates it at their own example — Boolean objectives on four points, `31 / 65535` |
| IT Thm 3, asymptotics | *"converges to zero double exponentially fast"* for `\|Y\| > e\|X\|/(\|X\|−e)` | — | No | — | the claim the section exists to make, and the one thing here that is not a count. It needs an asymptotic estimate on binomial coefficients against `\|Y\|^{\|X\|}`; the two counts above are its inputs, not the claim itself. Split out rather than absorbed into the rows that *are* covered |
| IT Thm 4 | non-trivial neighbourhood is not permutation-invariant | `exists_perm_rel_not_iff`, `forall_rel_of_permInvariant`, `rel_diag_iff_of_permInvariant`, `exists_perm_adj_not_iff`, `forall_adj_or_forall_not_adj_of_permInvariant` | Yes | **Wider** | the "why NFL is vacuous in practice" argument. Print, p. 318: *"A neighborhood relation on X is a **symmetric** function n: X × X → {0,1}"*, non-trivial when some pair of **distinct** points neighbours and some pair of distinct points does not. `exists_perm_rel_not_iff` is that statement and its equation (6), **with symmetry dropped**: the argument never uses it, so it is not assumed, and the diagonal is left free. `forall_rel_of_permInvariant` is the content — one instance at a pair of distinct points forces every pair — proved by two-transitivity, a permutation assembled from two transpositions. **And print does not prove Theorem 4**: p. 318 reads *"THEOREM 4 ([6])"*, the same self-citation as Theorem 3, and no proof appears in the text — so unlike the Theorem 3 rows, which transcribe a printed count, this row *supplies* a proof the source delegates. `rel_diag_iff_of_permInvariant` is the diagonal half: an invariant relation is all-or-nothing off the diagonal and all-or-nothing on it, the two independently. The graph forms are corollaries kept for discoverability, and looplessness removes the diagonal degree of freedom. `Examples…oneEdge_not_permInvariant` is one edge on three points; `Examples…loopedEdge_not_permInvariant` is that edge plus every self-loop — non-trivial in print's sense, legal under print's definition, and not a simple graph, so the graph form cannot be *instantiated* at it. That is applicability and not strength: `loopedEdge` is symmetric, and for symmetric `r` the relation `fun a b => a ≠ b ∧ r a b` is a legal `SimpleGraph` carrying both non-triviality clauses, so the conclusion stays derivable from the graph form. **The axis that buys strength is symmetry**, and `Examples…arrowRel_not_permInvariant` is its witness: a single arrow on two points, non-symmetric (`Examples…arrowRel_not_symmetric`), where print's theorem cannot be posed at all since no symmetric relation on a two-element type meets both clauses; `Examples…top_permInvariant` and `Examples…bot_permInvariant` occupy both branches of the graph dichotomy; `Examples…eq_permInvariant` is the diagonal, invariant but *trivial* in print's sense, recorded to show the diagonal is a live degree of freedom rather than as a case Theorem 4 covers |
| SVW NFL1 | equal performance under any overall measure | `no_free_lunch_adaptive_of_sharp` | Yes | **Wider** | the atlas gives the sum for an arbitrary `Ψ`, from which any overall measure follows |
| SVW NFL2 | for any two algorithms and any `f` there is a `g` with `V(A;f) = V(B;g)` | `exists_observed_eq` | Yes | Same | the witness is explicit — relabel by the permutation carrying one trajectory to the other |
| SVW NFL3 | every algorithm generates the same collection of performance vectors | `card_observed_eq` | Yes | **Wider** | at an **arbitrary** sample length `m`, where the source states NFL3 for the complete trace. At full length SVW note the collections are already sets, so counts and supports coincide there — the multiplicity `\|Y\|^{\|X\|−m}` is only visible at partial length |
| — | the adaptive class is strictly larger | `Examples…probeRule_not_schedule`, `…nfl_probeRule_over_orbit` | — | **Beyond** | a branching rule no schedule reproduces, for which NFL still holds over a **non-constant** permutation orbit. The orbit matters: over the constant objectives every rule observes the same sequence, so an equality there would be two identical sums. `observed_probeRule_ne` rules that out |

**14 Yes, 0 Partial, 1 No, 1 Beyond.** The one `No` is the
asymptotic, which is an estimate on binomial coefficients rather than a
statement about search, and is deliberately left.

**NFL4 has no row of its own.** Its declining remark — that a weighted overall
measure is not generally subject to NFL except under equal weighting — is
recorded on the signed-weights row, which is where the atlas exceeds it.

**The two papers do not draw the same algorithm class.** Igel–Toussaint state
Theorem 1 for *"any two (deterministic or stochastic, cf. [1]) algorithms"*;
Schumacher–Vose–Whitley open §2 with *"a framework for the analysis of
**deterministic** non-repeating blackbox search algorithms"*, which is exactly
`AdaptiveRule`. So the stochastic gap is Igel–Toussaint's alone; no SVW row is
affected by it.

**The stochastic axis is what three of the Igel–Toussaint rows turn on**, and it
is charged in the scope column rather than only stated as a non-claim in
`Learning/Sharp.lean` and [`lean-wolpert-nfl.md`](lean-wolpert-nfl.md): a stated
non-claim is not a scope verdict. The source-definition mixture proof closes the
axis, which is what carries all three rows to `Wider`.

Closing it turns on reading what the citation to Droste–Jansen–Wegener actually
buys, which Igel's own later survey spells out: *"a randomized search algorithm
*a* can be described by a probability distribution *pₐ* over deterministic
search behaviors"*, performance being *∑ over a′ ∈ A of pₐ(a′)·c(Y(f, m, a′))*,
with *A*
all deterministic behaviours. **The mixture picture is the source's definition of
a stochastic algorithm, not a proxy for it** — which is the opposite of the usual
situation elsewhere here, where a family standing in for a printed object is the
defect. `mixtureTrace` is that equation, `nfl_mixture_of_permInvariant` the
theorem over it, and `mixtureTrace_pointMass` the survey's *"deterministic
algorithms as a subset … having degenerated probability distributions"*.

`stochasticTrace` is the survey's alternative view in the same paragraph —
*"drawing all realizations … at once prior to the search process"* — kept because
it is the more general object, with `surjective_induced_playChoice` recording
that its finite choice alphabet reaches all of `A`.

**The primary source has now been read, and it is more explicit than the
survey.** Droste–Jansen–Wegener, *Optimization with randomized search heuristics
— the (A)NFL theorem, realistic scenarios, and difficult functions*,
**Theoretical Computer Science 287 (2002) 131–144**, is Igel–Toussaint's
reference [1]. Its Theorem 1 is stated for *"an arbitrary (randomized or
deterministic) search heuristic"*, and the randomized half of the proof, at
book p. 134, is this:

> *"The number of different deterministic search strategies is **finite**. Let m
> be its number. A randomized search strategy is a probability distribution
> p = (p₁, …, p_m) and chooses the ith deterministic strategy with probability
> p_i. … the expected cost of a randomized search heuristic is the weighted
> average of the cost of the deterministic search heuristics. Since all
> deterministic search heuristics have the same cost, this also holds for all
> randomized search heuristics."*

Three things fall out, and each retires a worry recorded earlier on this row.
The mixture model is DJW's **definition** of a randomized strategy, not a
rendering of one. Finiteness of the strategy set is **DJW's own observation**, so
`Fintype (AdaptiveRule X Y m)` is print's setting rather than an atlas
restriction. And *"since all deterministic search heuristics have the same cost,
this also holds for all randomized"* is `mixtureTrace_eq_sum_mul` — the atlas
proof follows the printed one step for step. Scenario 1 also fixes `A` and `B`
finite, and the paper normalizes to non-revisiting explicitly: *"Many popular
search heuristics evaluate certain points more than once but this can be avoided
by using a dictionary."*

Five rows rest on the algorithm class. `nfl_adaptive_of_permInvariant`
proves the sufficient direction over the printed class by a fibre argument: for
a fixed cost sequence `c`, the two rules unroll two schedules from `c`, and a
permutation carrying one to the other maps the fibre of one rule over `c`
bijectively onto the fibre of the other. The permutation is built from `c` alone,
which is why it can reindex the sum over objectives; permutation-invariance says
it leaves the weights alone.

`permInvariant_of_nfl` is graded `Wider` for a reason worth stating explicitly,
since it inverts the usual direction: the algorithm class appears in its
*hypothesis*, so assuming schedule-independence over a **smaller** class makes
the theorem **stronger**, not weaker.

**Why the graded statement is a bare relation and not a graph.** Print's
neighbourhood relation is symmetric and nothing more; `SimpleGraph` is symmetric
*and* irreflexive, so modelling it that way would assume a hypothesis print does
not state. The proof uses neither symmetry nor irreflexivity, so the row's
primary declaration quantifies over an arbitrary binary relation on an arbitrary
type, and the graph forms are corollaries kept because that is the form a reader
looking for graph automorphisms would search for.

**What each axis buys, stated precisely.** `Examples…loopedEdge_not_permInvariant`
is an edge plus every self-loop: legal under print's definition, non-trivial in
print's sense, and not a `SimpleGraph`, so the graph form cannot be
*instantiated* at it. That is applicability rather than strength — `loopedEdge`
is symmetric, and for symmetric `r` the graph `fun a b => a ≠ b ∧ r a b` carries
both non-triviality clauses, so the conclusion stays derivable from the graph
form. The axis that buys **strength** is symmetry, witnessed by
`Examples…arrowRel_not_permInvariant`, where print's theorem cannot be posed at
all. The diagonal witnesses neither: it relates no two distinct points, so it
fails print's first non-triviality clause and Theorem 4 does not speak about it.
`Examples…eq_permInvariant` records it only as a degree of freedom
`forall_rel_of_permInvariant` does not constrain, which is why
`rel_diag_iff_of_permInvariant` is a separate fact.

One sentence of print cuts against the reading here and is quoted rather than
stepped around. Immediately after the definition: *"There are only two trivial
neighborhood relations, either every two points are neighbored or no points are
neighbored."* Print says **two**; leaving the diagonal free gives more. The
reconciliation is that print counts off-diagonal behaviour and treats `n(x, x)`
as immaterial rather than as a parameter. That does not undo the widening — the
looped witness above is a relation print's own definition admits — but the
reading is an inference from a definition that omits the diagonal, not something
print asserts.

The asymptotic row stays `No` on a real judgement rather than a wrong one. It is
an estimate on binomial coefficients — the object is `Nat.choose`, not search —
and it is an endpoint: nothing else in the atlas would use it.

---

## 5. Touchette & Lloyd 2004 → `AISafetyAtlas.Control.InformationLimits`

Governing fact for every row: **the source defines `L_C` with a minimization
over `{p(c|x)}`** — eq. (28), the minimization being there, in the paper's words,
"to ensure that `L_C` reflects the properties of the actuation channel, and does
not depend on one's choice of control inputs". So the source law of `X`, the
noise `Z` and the actuation channel are held fixed and the *controller* varies.

Both readings are now in the atlas. `controlLoss` is the loss of one controller;
`minControlLoss` is an infimum over a set `P` of controllers sharing one plant
(`IsPlant`), which is what the source holds fixed — the actuation channel, with
the source law and the noise — while the policy varies.

**Which `P` is the printed one.** Eq. (28) minimizes over `{p(c|x)}`: channels
from the *state*, which carry nothing about the noise the state does not already
carry. That is `inputPolicies`, defined as conditional independence of `C` and
`Z` given `X`, and `minControlLoss μ F X Z (inputPolicies μ X Z)` is the atlas's
represented-policy rendering of the source constraint on the current `Ω`, and for
finite alphabets it is now *proved equal* to the all-kernel minimum.

The equality is a theorem and not an identification by fiat, which matters
because the represented infimum and the printed `L_C` quantify over different
objects — one over random variables on the ambient `Ω`, the other over channels.
`kernelMinControlLoss` declares eq. (28)'s
own object — an infimum over Markov kernels `S → K` — and
`minControlLoss_inputPolicies_eq_kernelMin` proves the two equal under
`[Fintype S] [Fintype K]`, the printed setting. No realization construction is
involved: eq. (28)'s second displayed line is *linear* in `p(c|x)`, so its
minimum is at a vertex, and the vertices are deterministic state feedbacks, which
need no auxiliary randomness and therefore exist on every sample space. The
pointwise theorems remain the sharper ones and still carry the rows that do not
need a minimizer; the bridge is what the *minimizer-sensitive* row needed.
`Set.univ` is **not** it, and the difference is not bookkeeping: a bare map
`Ω → K` may read the actuation noise, which no `p(c|x)` can, and cancel it.
`Examples…minControlLoss_univ_lt_inputPolicy` exhibits exactly that — a plant
where the noise-reader drives the loss to `0` while the constant controller, an
input policy, loses `log 2` — and `…not_isInputPolicy_noiseReader` checks the
reader is excluded from eq. (28)'s feasible set. Every theorem here is stated for
an arbitrary `P`, so each represented-family statement is available without
depending on this particular `Ω`.

`P` is **not** the printed constraint set, and `Set.univ` is not "the
unconstrained minimum": the atlas set is too *large*, not too small, and the
rows below are graded on that reading.

Each pointwise result is the stronger statement — it holds at *every* controller
— and the printed one is read off the infimum.
`Examples…minControlLoss_lt_controlLoss_gate` exhibits a plant and two
controllers whose losses are `0` and `log 2`, so the minimization is not a
formality either.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Thm 2, ineq. | `L_C ≤ H(Z)` | `minControlLoss_le_entropy_noise`, `controlLoss_le_entropy_noise` | Yes | **Wider** | the printed `L_C` and the pointwise form both. `Wider` on one axis: purification is asked at *one* admitted controller rather than across the family, since an infimum is already capped by a single member. A second axis — an arbitrary sample space — was claimed here and is struck; see the §2.8 regrades, which apply verbatim, this source's setting being discrete distributions on finite alphabets and its atlas variables `FiniteRange` |
| Thm 2, equality case | equality iff `H(Z\|X',X,C) = 0` | `minControlLoss_eq_entropy_noise_iff_of_attained`, `controlLoss_eq_entropy_noise_iff`, `minControlLoss_inputPolicies_eq_kernelMin`, `minControlLoss_inputPolicies_attained` | Yes | **Wider** | the obstruction the kernel bridge clears is that the represented infimum might have exceeded the source's minimum over `{p(c\|x)}`, so a minimizer of one need not minimize the other; `kernelMinControlLoss` now declares the source's object and `minControlLoss_inputPolicies_eq_kernelMin` proves the two equal. Attainment is a conclusion rather than a hypothesis: `minControlLoss_inputPolicies_attained` exhibits the minimizer. `Wider` in holding pointwise at every controller. The sample space was claimed as a second axis and is struck; the finite alphabets are the printed setting and the atlas variables are `FiniteRange`, so the space is a presentation |
| Thm 2, proof (30)+(31) | `H(X';Z\|X,C) = H(Z)` and `H(X';Z\|X,C) = L_C + H(Z\|X',X,C)` | `entropy_noise_sub_controlLoss` | Yes | Same | the atlas states their combination `H(Z) − L_C = H(Z\|X',X,C)` on one line. Both printed halves of Theorem 2 are corollaries of it, so neither needs its own argument — but the identity is one substitution from two consecutively displayed printed equations, not something the source omits |
| Thm 3 | `L_C = I(X';Z\|X,C)` | `minControlLoss_eq_sInf_condMutualInfo`, `controlLoss_eq_condMutualInfo` | Yes | **Wider** | the two quantities are equal at every admitted controller, so their images coincide and so do their infima — the printed equality between minima follows without a minimizer. `Wider` in holding off the minimum as well as at it; the sample space was claimed as a second axis and is struck |
| Thm 4 | `L_C = I(X';X,C,Z) − I(X';X,C)` | `minControlLoss_eq_sInf_mutualInfo_sub`, `controlLoss_eq_mutualInfo_sub` | Yes | **Wider** | as Theorem 3: `Wider` in holding off the minimum as well as at it, with the sample-space claim struck there and here |
| Thm 10 | `ΔH_closed ≤ ΔH_open^max + I(X;C)` | `kernelEntropyReduction_le_kernelOpenLoopMax`, `exists_kernelEntropyReduction_le_at_max`, `isGreatest_kernelOpenLoopMax`, `entropyReduction_le_openLoopMax`, `entropyReduction_le_of_condEntropy_ge`, `entropyReduction_le_of_openLoopBound` | Yes | Same | the paper's stated main result, at print's own scope, closed in two steps. **Family.** `kernelEntropyReduction_le_kernelOpenLoopMax` states it with no `F` and no `Z` — only a joint law `ρ` for `(X,C)` and a Markov kernel `κ` playing `p(x'\|x,c)`. What closed it is the paper's own §2: *"any non-deterministic channel … can be represented abstractly as a randomly selected deterministic channel"*, with (i) determinism given `(c,z)` and (ii) *p(x'\|x,c) = ∑_z p(x'\|x,c,z) p_Z(z)*. `isPurification_purifyMap` proves it; `openLoopMax_purifyMap` shows the two renderings of eq. (48) generate the **same set**. **The word `max`.** Print writes a maximum and the atlas had `sSup` plus boundedness, which is formally weaker since `max ≤ sSup`. `isGreatest_kernelOpenLoopMax` closes it: a probability measure on a finite state space is a point of Mathlib's standard simplex and conversely, the reduction in those coordinates is a finite sum of *negMulLog* terms whose inner argument is *linear* in the weights, so continuity of *negMulLog* plus compactness of the simplex plus finiteness of `K` give attainment. `exists_kernelEntropyReduction_le_at_max` then states Theorem 10 with the bound realized by an explicit input law and action. **`Same`, and formerly `Wider`.** The only widening ever claimed here was that the `F`-form results additionally hold over an arbitrary sample space, and the §2.8 regrades establish that this is a presentation rather than a generality. Nothing else on this row is a scope axis: the kernel form states print's *own* object, closing `max` against `sSup` brings the atlas **up to** print rather than past it, and proving §2's asserted purification is **coverage**. So the atlas statement and the printed one are inter-derivable, which is what `Same` means — it is not a demotion of the work, and `Cov.` stays `Yes`. Note that §2 assumes purification for *any* channel, globally, not only inside Theorem 2 |
| Thm 9 | `ΔH_open ≤ max over c of ΔH_open^c`, with equality attainable | `kernelEntropyReduction_le_iSup_kernelOpenLoop`, `exists_kernelEntropyReduction_dirac_eq_iSup`, `entropyReduction_le_iSup_openLoopReduction`, `exists_entropyReduction_const_eq_iSup_openLoopReduction` | Yes | Same | `Yes` on the object rule, applied uniformly: `kernelEntropyReduction_le_iSup_kernelOpenLoop` states both `ΔH_open` and `ΔH_open^c` from the printed data alone — an input law *ν*, an action law *p_C*, and an arbitrary kernel `κ` — with no plant model in the statement. The `Partial` verdict rested on a sentence that was **false**: that the source does not assume purification in the open-loop section. §2 states it for *any* channel before Section 3, and `isPurification_purifyMap` now proves it besides. The printed attainment clause is separate and proved: `exists_kernelEntropyReduction_dirac_eq_iSup` exhibits a **pure** controller — a Dirac action law at the paper's *ĉ* — whose closed-loop reduction equals the supremum. That supremum is over the finite `K`, so attainment is immediate; eq. (48)'s supremum over all input laws needs compactness and is proved attained separately by `isGreatest_kernelOpenLoopMax`. **`Same`, and formerly `Wider`**, on two grounds now withdrawn. The first was that the `F`-form holds over an arbitrary sample space — a presentation, per the §2.8 regrades. The second was that Lemma 8, which the proof leans on, needs no open-loop hypothesis at all: that is true and is graded on **Lemma 8's own row**, but a scope cell compares *this* row's atlas statement with *this* row's printed one, and the generality of a lemma used in the proof is not an axis of the statement proved. `kernelEntropyReduction_le_iSup_kernelOpenLoop` is stated from the printed data alone, so it is the printed statement |
| Lemma 8 | `ΔH_open ≤ ΔH_open^C` | `entropyReduction_le_condEntropy_form`, `entropyReduction_eq_condEntropy_form_iff` | Yes | **Wider** | wider in a way worth naming: the atlas proves it with **no** open-loop assumption at all. The source states it inside the open-loop section, but its printed proof uses only that conditioning does not raise entropy, so the inequality holds at every controller, observing or not. The equality case at `I(X';C) = 0` is proved too |
| Thm 1 | perfect controllability iff | — | No | — | **not interesting for this atlas, and expensive.** The statement is an existential over conditional distributions `p(c\|x)` satisfying two conditions — a reachability clause and a determinacy clause — so it needs the kernel object as a *quantified witness* rather than as an infimum. It also characterizes reachability, which is not an information limit and nothing downstream consumes |
| Thm 5 | perfect observability iff `H(X\|C) = 0` | `perfectlyObservable_iff_sensorLoss_eq_zero`, `entropy_eq_zero_iff` | Yes | Same | `perfectlyObservable_iff_sensorLoss_eq_zero` carries `[IsProbabilityMeasure μ]` and `[FiniteRange X] [FiniteRange C]`, so the variables push forward to a pmf on finite alphabets — this source's printed setting — and the two statements are inter-derivable. Not even the zero-measure remainder applies, the hypothesis here being a probability measure outright. That the source declines to prove it — *"we omit the proof which readily follows from well-known properties of entropy"* — is **coverage**, and `entropy_eq_zero_iff` not being in the entropy layer is a **dependency** fact; neither is a scope axis |
| Thm 6 | observable ⟹ `I(X;Z\|C) = 0` | `condMutualInfo_eq_zero_of_sensorLoss_eq_zero` | Yes | Same | as Theorem 5's row — `condMutualInfo_eq_zero_of_sensorLoss_eq_zero` carries `[IsProbabilityMeasure μ]` and `FiniteRange` on all three variables. The source's three-line proof, mechanized. The source notes the converse fails and it is not claimed |
| Cor. 7 | `L_S = 0` ⟹ `I(X;C,Z) = I(X;C)` | `mutualInfo_prod_eq_of_sensorLoss_eq_zero` | Yes | Same | as Theorem 5's row — `mutualInfo_prod_eq_of_sensorLoss_eq_zero` carries `[IsProbabilityMeasure μ]` and `FiniteRange` on all three variables. The comma is checked: the published page and the arXiv TeX both give `I(X;C,Z)`, not a three-way information |
| Thm 11 | closed-loop optimal iff `I(X';C) = 0` | — | No | — | **not interesting for this atlas.** It holds only under the constancy condition `ΔH_open^c = ΔH_closed^c = ΔH` for all `c`, and needs a notion of closed-loop *optimality* the atlas does not define. The conclusion it reaches — that gathering information you cannot use is worthless — is already carried by Theorem 10 without the extra model |
| below (50) | *"each conditional distribution `p(x\|c)` is a legitimate input distribution … an element of `P`"*, with the fixed actuation subdynamics inherited | `condEntropy_ge_of_openLoopMax`, `isPurification_purifyMap`, `map_prodMk_cond_eq_prod` | Yes | Same | the recorded defect was that the atlas had no realization theorem showing its `F,η` model covers every printed transition kernel, so the membership argument was mechanized only inside a narrower family. `isPurification_purifyMap` supplies exactly that theorem, and `openLoopMax_purifyMap` shows the induced reduction sets coincide, so the conditional law `p(x\|c)` is an element of eq. (48)'s own `P` for every printed kernel. This is an argument the paper gives in one sentence, now mechanized at the scope the paper gives it |

**12 Yes, 0 Partial, 2 No.** This section was `6 Yes, 1 Partial, 7 No` until the
kernel bridge and the open-loop and sensor axes landed, `9 Yes, 3 Partial, 2 No`
until purification was proved, and `11 Yes, 1 Partial, 2 No` until eq. (48)'s
maximum was proved attained; what changed and why is recorded per row above
rather than only in the totals. **Every graded row from this source is now
covered.** The two `No` rows are results nothing downstream wants, and their rows
say so.

Those three `Partial` rows were one defect, named once by the **object rule**
and then applied uniformly: Theorems 9 and 10 are printed about an arbitrary
actuation kernel `p(x'|c,x)`, while the atlas stated them inside the
independent-noise realization `X' = F(X,C,Z)` with no theorem realizing every
such kernel that way.

**Two things were wrong with that diagnosis, and only one of them was the
atlas's.** The blame was put on the source — the note said the open-loop section
does not assume purification, so the `F`-model was an added hypothesis rather
than the paper's own. That is **false**. §2, in the paragraph introducing Fig. 2
and eq. (7), states purification as a global modelling move for *any* channel,
before Section 3 and long before the open-loop section, in the paper's own
words: *"any non-deterministic channel modeling a source of noise at the level
of actuation or estimation can be represented abstractly as a randomly selected
deterministic channel"*, with condition (i) determinism given `(c,z)` — the
atlas's `IsPlant` — and condition (ii) *p(x'|x,c) = ∑_z p(x'|x,c,z) p_Z(z)* with
*p_Z* and not *p(z|x,c)* — the atlas's `IndepFun ⟨X,C⟩ Z`. The mistake was
reading where purification is *used* rather than where it is *introduced*.

What was genuinely the atlas's is that the paper **asserts** the representation
and never constructs it, and neither did the tree. `AISafetyAtlas.Control.Purification`
constructs it, following the paper's phrase literally: a *randomly selected
deterministic channel* is a random element of `S × K → T`, finite when the
alphabets are, so the seed needs no continuum. So the atlas now proves what print
asserts, which is a better outcome than winning the grading argument would have
been.

Theorem 9 and the step-(50) row move to `Yes` on that. Theorem 10's note named
**two** residuals, and the second — eq. (48) writing `max` where the atlas had
`sSup` — is closed separately by `AISafetyAtlas.Control.OpenLoopAttainment`:
probability measures on a finite state space are exactly the points of the
standard simplex, the reduction is continuous in those coordinates because the
outcome law is linear in them, and a continuous function on a compact simplex
attains its maximum. Lemma 8 and the sensor results were never affected, being
proved for arbitrary variables with no plant model — which is also why Lemma 8
is `Wider`.

Theorem 2 still takes two rows, because its two halves are proved by different
routes — the inequality by capping an infimum with one member, the equality case
by exhibiting the minimizer. It no longer takes two *grades*: the minimizer is
constructed, so the printed equality case is unconditional.

The two remaining `No` rows are the ones nothing downstream wants. Theorem 1
quantifies existentially over conditional distributions and characterizes
reachability rather than an information limit; Theorem 11 needs a notion of
closed-loop optimality the atlas does not define, and its conclusion is already
carried by Theorem 10. Both notes say so on the row.

Theorem 10 is `Yes | Wider`; its row and the totals section say what closed it.
Along the way two claims **about the source** were made here and turned out to be
wrong, and they are recorded rather than quietly dropped.

*"The source writes `ΔH_open^max` without saying which ensemble the maximum is
over."* False. Equation (48) and the sentence under it say it exactly: the
maximum is *"over any input distribution chosen in the set `P` of all probability
distributions"*. There was no implicit uniformity to repair.

*"The source states step (50) in prose and never proves it."* False. The
paragraph below the step gives the argument in one sentence — *"each conditional
distribution `p(x|c)` is a legitimate input distribution for the initial state of
the controlled system. It is, in any cases, an element of `P`"* — which is
exactly the argument the atlas mechanizes. That observation removed a mistaken
`Beyond` reading; what it did **not** do, and was once claimed to do, is supply
the realization bridge from arbitrary transition kernels or turn a bounded
supremum into an attained maximum. Those two are closed by
`isPurification_purifyMap` and `isGreatest_kernelOpenLoopMax`, not by reading the
paper more carefully.

The row is `Yes` on `exists_kernelEntropyReduction_le_at_max`, which is stated
against the printed maximum and does not go through `OpenLoopBound` at all.
`OpenLoopBound` is not eq. (48) and is kept for its incomparable hypothesis — a
fact about that definition, recorded once under *Reading the totals*, not a gap
in a graded claim.

**The minimization, and the one place it still bites.** `minControlLoss` is the
represented-policy infimum, and the printed Theorem 2 inequality together with
the printed Theorems 3 and 4 are obtainable from the arbitrary-`P` statements.
Each follows from the pointwise form without assuming a minimizer — for the
equalities because two functions equal at every point have equal infima, and for
the inequality because an infimum is capped by any single member. The kernel
object is declared rather than silently identified with `inputPolicies` on one
fixed `Ω`, and the identification is proved.

Theorem 2's **equality condition** was the one statement that needed more than the
transfer, since "equality holds iff `H(Z|X',X,C) = 0`" describes a *minimizer*.
`minControlLoss_eq_entropy_noise_iff_of_attained` takes "some admitted controller
realizes the represented infimum" as a hypothesis; what was missing was any
reason to think such a controller exists, or that it minimizes the source's
quantity rather than the represented one. Both are now supplied — the two minima
are equal, and `minControlLoss_inputPolicies_attained` exhibits the minimizer —
so the hypothesis is dischargeable and the row is `Yes`.

Note what does the work here: not a realization construction, and not the
compactness hypothesis the paper does not state, but the observation that eq.
(28)'s displayed objective is **linear**, so the optimum is a vertex and vertices
are realizable everywhere.

---

## Totals

| source | Yes | Partial | No | Beyond |
|---|---|---|---|---|
| Cover & Thomas §2.8 | 11 | 0 | 0 | 0 |
| Cover & Thomas §2.10 | 9 | 0 | 2 | 1 |
| Ashby ch. 11 | 11 | 0 | 4 | 0 |
| Igel–Toussaint / SVW | 14 | 0 | 1 | 1 |
| Touchette & Lloyd | 12 | 0 | 2 | 0 |
| **total** | **57** | **0** | **9** | **2** |

## Reading the totals

**Where the atlas is genuinely stronger:** the `Wider` verdicts rest on six
kinds of widening, and each row's note names which. Note which is *not* among
them — an arbitrary sample space in place of a fixed discrete one is a
presentation, for the reason given above. A hypothesis weakened to only what the
proof uses (Ashby's column condition); a hypothesis *derived*
rather than assumed (Ashby 11/8); a statement the source asserts without proof
(exactly two, both inside the proof of 2.8.1); a wider class of objects or
parameters quantified over (signed weights in IT Thm 5, arbitrary sample length
in SVW NFL3, a different estimate *type* in `fano_of_embedding`); a sharper
conclusion at the same hypotheses (Ashby's integer `⌈r/c⌉`, Fano's surviving
`−1` in the no-observation remark); and a statement proved **off** an optimum as
well as at it, where the source only states it at the optimum (Touchette–Lloyd's
Theorems 2, 3 and 4, each proved at every controller and then transferred to the
minimized `L_C`).

**Where it is weaker, and why — what actually remains:**

2. *(closed)* **Ashby's §11/11 capacity.** Both capacities are now formalized:
   the noiseless alphabet ceiling for the four exercises, and §9/12's weighted
   column entropy with §9/15's per-unit-time rate for the general claim. §9/15's
   asserted proportionality is proved too, and sharpened from linear to affine.
3. *(closed)* **Touchette–Lloyd's Theorem 10.** Both halves of this entry are
   gone. `isPurification_purifyMap` connects every printed transition kernel to
   the independent-noise representation and `openLoopMax_purifyMap` shows the two
   reduction sets coincide; `isGreatest_kernelOpenLoopMax` proves eq. (48)'s
   supremum attained, so it is the printed `max`. `OpenLoopBound` still does not
   nest with eq. (48), and is kept only because its hypothesis is incomparable —
   a fact about that definition, not a gap in a claim.

Two entries that used to sit in this list have been removed rather than
softened, because the tree no longer supports them:

* *"No optimal controller is ever constructed."* False since
  `minControlLoss_inputPolicies_attained`, which exhibits a minimizer — the
  deterministic state feedback playing an argmin action at each state. The
  source still does not construct one, so the atlas is now ahead of print here.
* *"Theorems 5, 6 and 9, Corollary 7 and Lemma 8 are a parallel development."*
  All five are now proved. The observability axis is `sensorLoss` and the
  open-loop axis is `openLoopReduction`; Theorem 9 in particular closes the
  internal weakness this list used to name, since Theorem 10's `Δopen` no longer
  has to be a passed-in parameter.


Two further limits are worth naming even though **neither costs a scope verdict**.

*The Fano module's alphabet hypotheses are pointwise* (`∀ ω, X ω ∈ A`), not
almost-everywhere. That is stronger than the proofs need, so it is a limit
against the usual measure-theoretic idiom — but not against print, where `X` is
typed into a finite alphabet `𝒳` and membership is automatic. Taking `A` to be
`𝒳` recovers the printed statement exactly, so scope is still `≥` print, and an
almost-everywhere version would *exceed* it rather than close a gap. It is not
claimed, and would touch every statement in the module.

*"Arbitrary measurable space"* throughout means an arbitrary **sample space**:
the variables are countable of finite range, so the alphabets are finite here as
in print. No `Wider` verdict in this audit rests on infinite alphabets.

**The `No` column is mostly one thing:** results adjacent to the target — other
problems in the same paper (IT Thm 3/4), or a parallel development.
Touchette–Lloyd's observability half is no
longer: Theorems 5 and 6 and Corollary 7 are proved, leaving only Theorems 1 and
11, whose rows say why they are not worth having. None of the remaining `No` rows
is a gap in a claim the atlas makes.

**No grade here rests on an unread text.** Every row above was graded against the
published text named in its section header, and where a preprint was used
alongside it the two are compared explicitly in this directory's per-source
notes.
