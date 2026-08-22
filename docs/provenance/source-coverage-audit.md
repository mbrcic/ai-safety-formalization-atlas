# Source coverage audit

Every statement in the sections of the eight sources the atlas formalizes from,
checked one by one against the Lean and against the published text of each; last
revised 2026-08-20, when the causal sources — Richens & Everitt 2024, Pearl §1.3,
and Everitt et al. 2021 — were graded for the first time. Those three had been
covered only by hand-written prose in `mais-a2-causal-collision.md`, which no
script read; six of its scope claims had gone stale through four commits with
every gate green. Sections 6 to 8 exist so that cannot recur.

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
* **provably not closable** — with the witness that proves it. **None on this
  table.** One was claimed on 2026-08-22 — the well-foundedness of the parent
  relation that `SCM` and `SCIM` ask for where print writes only *"acyclic"* —
  and it was **retracted, then closed**. The witness proves that `eval` cannot be totalised over print's class; it does not
  prove that the structure must carry the field. `SCM` and `SCIM` now carry
  print's `acyclic` and the recursion's hypothesis lives in `SCM.IsWellFounded`
  and `CID.IsWellFounded`, which is the refactor the retracted paragraph said
  did not exist. The retraction is left visible in the §8 preamble rather than
  deleted.
  The conjecture ledger grades on a dimension this table does not have, so this
  phrase is not a claim about both documents.
**How to read a `Narrower` cell.** The grade is a statement about *classes*: the
atlas admits fewer objects than the printed words do. It is **not** a statement
about whether anything downstream lost a theorem, and the two come apart. Two
kinds occur in this table, and each row now says which it is.

* **Source-class.** The narrowing is against one paper's phrasing, in a module
  nothing else in the tree imports. Everitt Definitions 1, 2 and 5 are this:
  `AISafetyAtlas.Causal.StructuralModel` has **no library-module importer**, so
  no result stated elsewhere is weakened by it. The cost is borne by a future
  consumer who wants to instantiate that module outside the admitted class, not
  by anything already proved.
* **Working-stack.** The narrowing is on an object the rest of the tree is
  stated over, so existing theorems do not transfer to objects outside it. RE24
  §2.2's value and regret are this: the margin, query and MAIS layers are all
  stated over `Model.value`'s unmediated projection, so a mediated diagram —
  which the atlas *can* write down, as `DecisionNetwork` — cannot use them.

The standing rule applies to both without discount: a `Narrower` cell is a
defect until discharged, proved unclosable, or costed. The distinction says
which ones to pay first, not which ones to stop counting.

* **open, and costed** — with what it would take. Every open axis is priced
  in [`causal-scope-open-work.md`](../guide/causal-scope-open-work.md), which also says
  which of them close a row on their own and which do not. **Three are open.**
  Two of the three are in §8. Everitt's finite domains on Definitions 1–2 is one,
  stated with its cost in that section's preamble; it now closes Definition 2
  outright and leaves Definition 1 on one further axis. That further axis is the
  second: the expectation layer's `[Fintype V]`, which was named on the policy
  row and denied on Definition 5 until 2026-08-22, when §8's preamble adjudicated
  it once and applied the result to both. **Every upward revision of this number has been a row carrying an axis this
  list had not enumerated**, which is why axes are now read off the declarations'
  binders rather than off the printed object.
  The other is in §6 and is a different kind: RE24 §2.2's value and regret rows
  are the unmediated projection, because the decision and the utility are not
  vertices of the graph those declarations are stated over. It is not closable by
  generalising anything — it needs a construction — and **half of that
  construction landed on 2026-08-22**. `Causal.DecisionNetwork` is RE24
  Definition 4 with the decision and the utility as vertices, and print's
  expected utility, optimality and regret are stated on it; what is missing is
  the theorem that the projection agrees with it under Assumption 1, and the two
  live in different vertex types, so that is a translation rather than a rewrite.
  Until it exists the two rows stay `Narrower`, listed on the projection's
  declarations alone. §6's own prose carries the detail; this list said "all in
  §8" and was wrong to. Two further axes were open until 2026-08-20 and are closed
  rather than re-argued. The decision
  layer's rational instantiation is closed by the field-parametrization work; its stated obstruction turned
  out not to exist, because `LinearOrder` already bundles the decidable strict
  order that `preferredDecision` needs. The binary-decision restriction in §6's
  eq. (2) row is closed by `Skeleton.realizable_iff_general`, and closed in the
  strong sense this list asks for — the old binary lemma is *derived from* the
  general one rather than left beside it. The former
  Cover & Thomas Theorem 2.5.2 arity
  gap was closed by `observationVector`, `observationPrefix`, and
  `mutualInfo_chain_rule_fin`; the atlas now contains the required measurable
  finite-prefix machinery rather than leaving the printed general `n` theorem
  at its `n = 2` instance.

## Readings that are not transcriptions

**Scope is not the only axis, and this table only grades scope.** A row can be
`Same` — asserting exactly what print asserts — while the *rendering* of a
printed phrase is a choice the atlas made rather than a transcription. The
conjecture ledger records that as a `Bridged` fidelity tag; this table has no
fidelity column, so the readings are listed here instead of being left in the
prose of three long notes. **Nothing below changes a scope grade.** Each is a
place where a reader checking the atlas against print will find a decision, and
should be able to find it in one place.

* **Pearl Def. 1.3.1, conditions (ii) and (iii): tables, where print writes
  conditionals.** Print states (iii) as *P_x(v-i given pa-i) = P(v-i given pa-i)*, a
  quotient. `IsCausalBayesNetwork` states it as equality of *tables*. The two
  differ exactly on parent configurations of probability zero, where the quotient
  is undefined and the table equality still binds. The atlas reading is the
  stronger one, and deliberately: `Causal.MarginClass`'s margin conditions exist
  because null parent fibres are reachable, so a quotient rendering would go
  vacuous precisely where a degenerate mechanism needs constraining. It is a
  choice about behaviour print does not legislate.
* **MAIS-O24 size bounds: one polynomial, chosen before the diagram shape.**
  Print requires *"the list length, degrees, coefficient bit lengths, and
  construction time to be polynomial in `S`"*. That sentence does not say whether
  one polynomial serves every shape or each shape may have its own.
  `HasPolySizeAt` takes the uniform reading, quantifying the polynomial before
  the shape and the graph. The argument for it is that print names `(m, S)` for
  the constants `a, b` and names no `m` for the size quantities — a good
  argument, and an argument is a reading. The uniform reading is the stronger
  one, so it admits fewer solutions.

**One candidate reading was checked and is not one.** `Causal.ShiftedQuery`'s
observation field is a full `Assignment C dim` where print writes its observation in *dom(O'-t)*, an assignment
to the visible subset alone. That looks like a wider query, and a wider query
would make the analyst more powerful than print's and weaken every bound phrased
over `N(ε)`. It is not: `Causal.Policy` carries that constraint as a **structure
field** requiring a policy to agree wherever the visible variables agree, so no policy can read a hidden coordinate, and
`exactPolicyAnswer_congr_observation` derives the consequence at the query level.
The invariant is enforced by the type rather than by a lemma anything could
forget to apply.

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
| Thm 2.5.2, used at `n = 2` inline as (2.119)/(2.120) | `I(X₁,…,Xₙ;Y) = Σᵢ I(Xᵢ;Y\|X_{<i})` | `mutualInfo_chain_rule_fin`; `mutualInfo_chain_rule`, `mutualInfo_chain_rule'`, `mutualInfo_sub_eq` at n = 2 | Yes | **Same** | `mutualInfo_chain_rule_pi` is the printed arbitrary finite-family statement, with **one alphabet per index** as the source has it. `mutualInfo_chain_rule_fin` is the same identity at a single shared codomain, and the first is derived from it by tagging each variable with its index. That reduction used to be this row's justification in prose — differently typed finite alphabets embed injectively in one tagged disjoint union — and is now the proof of an exported theorem, so the uniform `V` is provably a representation rather than a restriction. The two-component declarations remain the direct forms used by §2.8, and `mutualInfo_sub_eq` is their difference identity |
| Remark + example | conditioning **can** increase `I` off a Markov chain: `X, Y` fair bits, `Z = X+Y`, `I(X;Y) = 0` but `I(X;Y\|Z) = ½` bit | `Examples…condMutualInfo_eq_half_bit_of_intSum`, `…condMutualInfo_gt_mutualInfo_of_parity` | Yes | **Wider** | the first is the printed example at the printed numbers — `Z` the **integer** sum, three-valued, and `I(X;Y\|Z) = ½` bit, which is what the printed `P(Z=1)` factor requires. The second replaces `Z` by `X ⊕ Y` and gets a full bit, a strictly larger gap. Either makes the Markov hypothesis of `condMutualInfo_le_mutualInfo` load-bearing rather than assumed to be |

**11 Yes, 0 Partial, 0 No.** Section fully formalized, counterexample included, and nothing left in the `Beyond` column. The row that sat there is printed content — Theorem 2.5.2 at `n = 2` — and `mutualInfo_sub_eq` is those two expansions subtracted, so it shares that row.

There are no `Narrower` or `Mixed` rows in this source section. The first two
rows are the section's definitional pair. `IsMarkovChain X Y Z μ`
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

## 6. Richens & Everitt, ICLR 2024, §2–3 and Appendices A–B → `AISafetyAtlas.Causal.Model`

**Which text grades these rows.** The published ICLR proceedings PDF, sha256
`143d458cbee2f4f5d04d7380f6741e8105965d1ee94834e1ddb3bd231722a0e7`. The atlas
also stores the arXiv working text
(`b25a2c7e8fe27d1dfd00299166197d8f3bd2ac8af7102f3b2a07585cfd6743b2`), and
`mais-a2-causal-collision.md` pinned *that* one. Every numbered statement carries
the same number in both, checked one by one, with a single difference: the
working text adds **Corollary 1** — the regret-bounded-agent restatement of
Theorem 2 — after Theorem 3, and the proceedings has no corollary at all. It is
graded below as a working-text row so that the difference is on the record rather
than resolved silently. The source also numbers two distinct appendix lemmas
"Lemma 4"; the second, in Appendix D, is referred to here as D's Lemma 4.

**What gets a row here.** The printed statements the paper argues, plus the
displayed formulas it introduces definitionally and the atlas transcribes as
theorems — eq. (1), the truncated factorisation, eq. (2), eq. (3). A definition
with no transcribed content is not a row.

**The standing narrowing.** `AISafetyAtlas.Causal.Model` and
`AISafetyAtlas.Causal.MarginClass` carry their value field as a parameter, so the
printed real case is reachable, and it is the case any statement over these
objects is stated at. `AISafetyAtlas.Causal.Decision` was the exception until the
field-parametrization work, and is no longer: it too carries
`𝕜`, including `InIdentifiedSet`'s tolerance. **No row below is narrow on the
value field.** The `Narrower` rows are narrow on structure: their declarations
are the Assumption-1 projection, with the decision and the utility outside the
graph.

**That sentence used to end "and that is not an axis a generalisation closes",
which was wrong twice over.** It is not a generalisation that closes it — it is a
construction — and on 2026-08-22 the construction landed:
`AISafetyAtlas.Causal.DecisionNetwork` is Definition 4 with the decision and the
utility as **vertices**, and Section 2.2's three sentences are stated on it at
print's own quantifiers. The axis therefore moves from *not closable* to **open,
and costed**, which is the state the standing rule actually provides for. What it
costs is named in the two `Narrower` rows below and priced in
[`causal-scope-open-work.md`](../guide/causal-scope-open-work.md).

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| §2.1 truncated factorisation | product of unintervened CPDs when the value is consistent with the forced one, else zero | `hardInterventionProfile`, `Model.jointProb_hardInterventionProfile`, `fixProfile`, `Model.jointProb_fixProfile` | Yes | **Wider** | print states it for hard `do` only; the atlas proves the product form for *every* profile of arbitrary local maps, and the printed case is the constant-map instance. Intervened factors become consistency indicators exactly as printed. Witnessed by `Examples…jointProb_sum_shiftCollapse`, which runs a translation modulo three composed with a non-injective child map — neither is a hard intervention, and neither is expressible in the printed formula |
| Def. 2, eq. (1) | a local intervention transforms the CPD to the preimage sum over states mapping to the realized one | `Model.factor`, `Model.factor_eq_re24` | Yes | Same | `factor_eq_re24` is the literal preimage sum and closes by `rfl`. The printed map is any `f`, and so is the atlas's `LocalIntervention`; the four-map Boolean case is derived, not built in |
| Def. 3 mixture formula | a mixed intervention performs each component with its weight, and the joint is the weighted sum | `Mixture`, `ProbMixture`, `IsProbabilityMixture`, `Model.jointProbMix` | Yes | **Wider** | the simplex is over whichever value field a statement picks, so at the reals it is the printed object. The ambient `Mixture` drops the simplex constraint entirely and carries the linear lemmas. Witnessed by `margin_class_not_identifiable`, which inhabits the rational field, where the printed statement has no reals to quantify over |
| Def. 4 causal influence diagram | a single-decision, single-utility CID is a CBN whose variables are partitioned into decision, utility and chance, with the utility a real-valued function of its parents | `Causal.DecisionNetwork`, `Causal.DecisionPolicy`, `Model.withPolicy`, `Model.withPolicy_parents`, `DecisionNetwork.IsDeterministicUtility`, `DecisionNetwork.exists_utilityFunction`, `Model.cpt_eq_one_unique` | Yes | **Same** | **New on 2026-08-22; this definition had no row before, under this section's rule that a definition with no transcribed content is not one.** Print says a CID *is a CBN* with partitioned variables, so `DecisionNetwork` is built on `Causal.Model` rather than on the structural layer, and the decision and the utility are **vertices**. Distinctness of the decision and utility vertices is the whole of the partition condition a two-element distinguished part needs. **Print's *do(D = π(pa_D))* is rendered as a soft intervention**: `Model.withPolicy` keeps the parent set and swaps the table, and `withPolicy_parents` records it. That is forced by print itself — RE24 Def. 2 severs a hard-intervened vertex's incoming edges, and a policy *reads* its observations, so a hard reading would delete them. **One disclosed widening, with print's case pinned.** Print's clause that the utility is a real-valued function of its parents is carried as `IsDeterministicUtility`, a hypothesis rather than a field, so the atlas defines expected utility on a strictly larger class than print's; `exists_utilityFunction` recovers print's *U(pa_U)* as an actual function wherever the hypothesis holds, which is the same disclosure pattern this section already uses for single-decision restrictions. The widening is in the permitted direction and is why the cell is `Same` rather than `Narrower`. Inherited from `Causal.Model` and graded on its rows, not restated here: a finite vertex set, a `Finset` parent map, and an ℕ-ranked acyclicity witness |
| §2.2 expected utility and optimality | expected utility of a policy, and a policy is optimal if it maximises it | `Model.value`, `Model.value_eq`, `Model.bestPolicy`, `Model.value_bestPolicy` | Yes | **Narrower** | **Working-stack narrowing** — the kind that costs transfer rather than syntax. One axis, and a structural one. These declarations are the unmediated Assumption-1 projection rather than the printed CID equation: their decision and utility are not graph vertices. **The atlas can state a mediated decision task**, and a sentence in an earlier pass of this note said otherwise: `DecisionNetwork` carries the decision and the utility as vertices, Assumption 1 is `IsUnmediated`, a **hypothesis** rather than a field, and a diagram with `Desc_D ∩ Anc_U ≠ ∅` is a `DecisionNetwork` the atlas writes down and evaluates. What does not transfer is everything stated over the projection — the margin layer, the query layer and the MAIS Props all sit on `Model.value` — so a mediated diagram gets the definition and none of the results. **The axis changed state on 2026-08-22 without closing.** The printed CID equation now exists in the tree -- `DecisionNetwork.expectedUtility` and `DecisionNetwork.IsOptimal`, on a diagram whose decision and utility *are* vertices, graded `Same` on the Definition 4 row above. What is still missing, and what this row is graded on, is the theorem tying the two together: nothing yet proves that this projection agrees with `DecisionNetwork.expectedUtility` on a diagram satisfying Assumption 1. **The mediated declarations are deliberately not listed in this row's atlas column.** Adding them beside the projection would give the row a declaration that is print's object while four others are not, and this section grades a row on *every* declaration in its column -- the convention exists precisely so a row cannot be graded on its best declaration. The axis is now **open, and costed**: the agreement theorem needs the joint over the diagram split at the decision and utility coordinates, and the two renderings live in different vertex types, so it is a translation and not a rewrite. The value field is *not* an axis: Stage 3 made `Causal.Decision` generic like the rest of the causal layer, so the printed real case is an instance. `bestPolicy` maximises each visible fibre and `value_bestPolicy` proves it attains the optimum, with ties unconstrained |
| §2.2 regret | the decrease in expected utility against an optimal policy | `Model.regret`, `Model.HasRegretAtMost`, `Model.regret_decomp`, `Model.regret_eq_zero_iff` | Yes | **Narrower** | **Working-stack narrowing**, exactly as the row above. The inequality is the printed one within this representation, with no added zero-regret sign clauses. Same single structural axis as the row above, in the same new state: `DecisionNetwork.regret` is print's δ on a diagram with the decision and the utility as vertices and is graded on the Definition 4 row, this row is the projection, and no theorem yet connects them. Same non-axis as the row above too: the value field is a parameter. `regret_eq_zero_iff` is an atlas converse print does not state: zero regret is exactly positive support on the fibrewise argmax |
| Assumption 1 unmediated decision task | the decision's proper descendants and the utility's proper ancestors are disjoint | `DecisionNetwork.IsUnmediated`, `Model.properAncestors`, `Model.properDescendants`, `Model.mem_properAncestors_iff`, `Model.mem_properDescendants_iff`, `DecisionNetwork.decision_notMem_parents_of_isUnmediated` | Yes | **Same** | **New on 2026-08-22.** **The notation had to be read before the assumption could be stated.** Print's Appendix notation paragraph says *"Anc_i and Desc_i refer to proper ancestors and descendants"*, and the reading matters: on print's own Figure 1 the decision is a parent of the utility, so an improper reading puts the decision in both sets and makes the assumption **unsatisfiable**. Read properly it says the decision's only route to the utility is the direct edge, which is what print's own Appendix argument uses. `decision_notMem_parents_of_isUnmediated` is that content in the form the analysis consumes: no proper ancestor of the utility reads the decision. **Inhabited, not merely defined**: `Examples…figIsUnmediated` discharges it on print's Figure 1 training diagram, without which every theorem conditional on it would be vacuous |
| App. A.1, Lemma 1(iii), graph step | *"D ∈ Anc_U which with Desc_D ∩ Anc_U = ∅ implies D ∈ Pa_U"* | `DecisionNetwork.mem_parents_utility_of_isUnmediated` | Yes | **Same** | **New on 2026-08-22, and it is a slice of Lemma 1, not the lemma.** Print's clause is one sentence and the atlas theorem is that sentence: the decision being a proper ancestor of the utility, together with Assumption 1, forces the direct edge. The proof is the expansion print compresses — any intermediate vertex on a route from the decision to the utility would be a proper descendant of the one and a proper ancestor of the other at once. Formally the utility's ancestor closure minus the decision and its proper descendants is parent-closed and contains the utility, hence contains the whole closure, hence contains the decision, which it does not. **The rest of Lemma 1 is not covered and its own row still says so**: clauses (i) and (ii), and the first half of (iii), run through Assumption 2 (domain dependence), which is not formalized. Slicing a printed statement is this table's existing practice — see the Cover and Thomas Thm. 2 rows |
| App. A.2, eq. (2) | normalise the utility to `[0,1]` by subtracting its minimum over parent states and dividing by its range | `Skeleton.normalizeUtility`, `Skeleton.utilityLo`, `Skeleton.utilityHi`, `Skeleton.normalizeUtility_mem_unitInterval`, `Skeleton.ofUtility`, `Skeleton`, `Skeleton.realizable_iff_general`, `Skeleton.realizable_iff` | Yes | **Wider** | the normalising map is now built, not only its output. `normalizeUtility` is the printed quotient over the utility node's parents — the decision together with the utility parents — and `ofUtility` carries an arbitrary `𝕜`-valued utility into a `Skeleton`, which is what was missing while this row read `Partial`: no unnormalized utility could be written down and then rescaled. On a constant utility the range is zero and the quotient is `0`, still in `[0,1]`, so the invariant is unconditional where print states eq. (2) only for the non-degenerate case. The widening is the converse print does not state: `realizable_iff_general` proves a decision family is realized, up to a fibrewise shift, by a normalized utility exactly when its fibrewise spread is bounded by one, at **any** finite decision arity. The former binary restriction is gone and is not merely claimed gone — `realizable_iff` is now *proved from* the general form via `sup'_sub_inf'_bool`. Witnessed by `Examples…ternaryGap_realizable`, a three-decision family the binary lemma cannot state at all |
| App. A.2, invariance of the optimum under eq. (2) | a positive affine transformation of the utility leaves the set of optimal policies invariant, so regret bounds rescale | — | No | — | the atlas normalises by construction and never states the invariance. Nothing downstream needs it, because no atlas statement transports a regret bound across a rescaling |
| App. B, eq. (3) | expected-utility difference between the two decisions under a hard intervention, as a weighted sum of utility differences | `Model.value_const_sub` | Yes | **Wider** | print gives one two-variable hard-`do` instance with the opposite sign ordering; `value_const_sub` proves the identity for every probability mixture, every visible set, and every model, and the printed instance is a Dirac profile. The sign is an ordering convention, not an axis. Witnessed by `Examples…margin_class_not_identifiable_shared_optimal`, which needs the identity at *every* probability mixture and visible set to place two models in one identified set; print's single hard-`do` instance does not reach it |
| App. A.1, Lemma 1 (clauses (i), (ii), and the Assumption-2 half of (iii)) | domain dependence implies no dominant decision, that the observed parents are a proper subset of the utility ancestors, and that the decision is a utility parent | — | No | — | domain dependence is nowhere in the atlas. It is a hypothesis about the existence of two environment distributions with different optima, and the atlas's margin conditions replace that role with explicit inequalities rather than deriving it |
| App. A.2, parameter space | the CID parameters lie in `[0,1]` and are logically independent, so they define a parameter chart | — | No | — | **no chart over the CID parameters exists**, which is the narrower claim this row used to make as a blanket one. `ChartIndex` with `Model.chartOn` is a real chart, with `K(G)` proved against `def:margin`'s formula by `card_chartIndex`, and MAIS-O24's conclusion (c) carries a Lebesgue estimate over it — but both are charts of the *chance-variable* tables of MAIS's unmediated skeleton, where `D` and `U` are not vertices. RE24's parameter space is over a full CID's parameters, including the decision and utility mechanisms, so it is a different object and this row stays `No`. Its absence is why the four rows below are `No` rather than `Partial` |
| App. A.2, Lemma 2 (Okamoto) | the solutions of a nontrivial polynomial are Lebesgue measure zero in its parameters | — | No | — | cited by the source, not proved by it. The atlas has no measure on a parameter space and no polynomial encoding of a constraint |
| App. A.3, reachability of distributions | mixtures of interventions reach any distribution over the environment variables | `ProbMixture.dirac` | No | — | the atlas has the deterministic profiles print mixes over, and the mixture-to-profile reduction lemma proves that mixture-wise equality is profile-wise equality — but it never states that the mixtures *reach* an arbitrary distribution, which is the printed claim |
| Def. 5, policy oracle | a map from each domain to a policy achieving expected utility within the tolerance of optimal | `InIdentifiedSet`, `not_inIdentifiedSet_of_neg` | No | — | the atlas packages *shared* admissible families rather than a map from domains to policies, so no declaration is the oracle. `InIdentifiedSet` accepts every tolerance in the value field and `not_inIdentifiedSet_of_neg` proves the extension below print's domain is empty, which bounds the packaging but does not build the oracle |
| Thm. 1 | for almost all CIDs, the graph and the joint over the utility ancestors are identifiable from optimal policies across all mixtures of local interventions | — | No | — | needs the parameter chart, the almost-every quantifier, and the oracle — all three absent. The atlas's `Model.ancestors_eq_univ_iff` supplies only the ancestor-closure bookkeeping the statement is phrased over |
| Thm. 2 | for almost all CIDs, a regret-bounded policy family identifies an approximate model whose parameter error is bounded by a function vanishing linearly at zero regret | `InIdentifiedSet`, `modelError`, `IsRadius`, `inIdentifiedSet_zero_of_behaviorEq` | No | — | the atlas objects are **related packaging**, not a transcription: there is no recovered subgraph and no error function. What is machine-checked is one direction of the bridge the theorem's proof uses — `inIdentifiedSet_zero_of_behaviorEq` shows equal masked transforms put two models in the identified set at zero tolerance. The converse, reconstructing the numerical query from an arbitrary optimal-policy oracle, is the printed step and is not formalized |
| Thm. 3 | a causally sufficient model identifies optimal policies for every soft intervention, and an approximate model identifies regret-bounded policies with regret linear in the error | `Model.regret_signPolicy_eq_zero`, `Model.signPolicy_eq_of_behaviorEq` | No | — | the sufficiency direction. The atlas proves a sign policy is optimal and that equal transforms give a shared one, which is the zero-error corner of the printed claim; the linear-in-error statement needs the approximate model the row above lacks |
| §3 remark | Theorems 2 and 3 together make an approximate causal model necessary and sufficient for regret-bounded policies | — | No | — | a conjunction of two `No` rows |
| §3 finely-tuned example | a chain where intervening changes only the variance of the utility, leaving the optimum fixed | — | No | — | print's illustration of why almost-every is needed. It is about a continuous latent, which the finite categorical kernel cannot state |
| App. C–D, Lemmas 3, 4, 5, D's Lemma 4, 6 | a unique deterministic optimum almost everywhere; the query identifiable from an optimal oracle; its point estimate and two-sided bounds from a tolerant oracle; and their expansion at small regret | — | No | — | the identification algorithm. Every one of them quantifies over the parameter chart or the oracle, and grouped as one row because they stand or fall together |
| Cor. 1 (**working text only**) | Theorem 2 restated for an agent meeting a regret bound, obtained by substituting its policy for the oracle's | — | No | — | absent from the published proceedings. Recorded so that a reader working from the arXiv text does not read its absence here as an oversight |
| — | margins in place of the almost-every exception | `Skeleton`, `Skeleton.MarginClass`, `Skeleton.ValidMargin` | — | **Beyond** | the six margin conditions are an explicit-inequality replacement for print's measure-zero exclusion. Print never states them; Uhler et al. motivates the *move* but its object is a partial-correlation bound, not these CPT inequalities |
| — | a margin class does not determine behaviour | `Examples…margin_class_not_identifiable_real`, `Examples…margin_class_not_identifiable_two_graphs_real` | — | **Beyond** | two models in one margin class, over the reals, with opposite one-edge graph shapes and equal complete masked behaviour. Print asserts identifiability for almost all parameters; this exhibits a margin-class pair where it fails, which print does not state either way |
| — | equal behaviour forces one shared optimal policy family | `Examples…margin_class_not_identifiable_shared_optimal` | — | **Beyond** | the bridge applied to the collision: one policy family with zero regret in two distinct models |
| — | rational witnesses transport to any characteristic-zero ordered field | `Model.mapRat`, `Skeleton.marginClass_mapRat`, `Skeleton.behaviorEq_mapRat` | — | **Beyond** | print works over the reals and has no reason to state this. It is what lets a witness be *computed* on rational literals and then hold at print's generality; it is not a cast of its hypothesis, since real mixtures are not images of rational ones |

**10 Yes, 0 Partial, 13 No, 4 Beyond**, up from 7 Yes on 2026-08-22, when
Definition 4, Assumption 1 and the graph step of Lemma 1(iii) gained rows and
`Causal.DecisionNetwork` to sit in. The shape is worth stating plainly: the
atlas covers RE24's **setup** completely, and none of its **results**. The one
gap inside the setup was eq. (2) — the normalised utility carried as an invariant
with no map producing it — and `Skeleton.normalizeUtility` / `Skeleton.ofUtility`
closed it on 2026-08-20.
Every `No` row above fails for one of two reasons, and both are named — there is
no chart over a *CID's* parameters, so no almost-every statement about one can be
phrased; and there is no policy oracle, so no identification claim can be
phrased. Theorems 1 to 3 need both. The first reason is narrower than it was
before 2026-08-21: a real parameter chart now exists for MAIS's unmediated
chance-variable tables, with a Lebesgue estimate over it. What is missing is a
chart of a CID, which needs `D` and `U` as graph vertices — the same object the
`Decision.lean` scope fence names.

That is not a gap left open by neglect. The atlas's causal increment is the
MAIS-A2 composite, whose whole point is to replace the measure-zero exception
with margins, and margins are what the four `Beyond` rows record. The two
`Narrower` rows are all one thing — the unmediated projection — and it is not
closable by generalisation. Since 2026-08-21 the object it needs exists:
`Causal.SCIM` has decision and utility vertices and a policy that is a structural
function. What is not written is the map from a SCIM's decision vertex to
`Model.value`, which is what would make these two rows the printed CID equation.

---

## 7. Pearl, *Causality* 2nd ed. §1.3 → `AISafetyAtlas.Causal.BayesianNetwork`

**Where these declarations live.** Equation (1.37) and the interventional
profile are in `Causal.Model`; Definition 1.3.1 itself — the compatibility
condition, its truncated-product consequence and the counter-witness — is in
`Causal.BayesianNetwork`, hosted by `LAND-CAUSAL-PEARLCBN-001` since 2026-08-22.
Before that row existed this section graded a module no registry row carried, so
the grade was invisible on every generated status page.

Pearl grounds the interventional reading, and nothing else. Definition 1.3.1 is a
*semantic* condition — a DAG is a causal Bayesian network compatible with a whole
family of interventional distributions if three conditions hold for every member.
The atlas kernel is constructive data, a graph together with tables, so it does
not state that condition; it certifies the consequence Pearl derives from it.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| eq. (1.37) | the interventional distribution is the product of unintervened CPDs over values consistent with the forced ones | `hardInterventionProfile`, `Model.jointProb_hardInterventionProfile` | Yes | **Wider** | Pearl derives this from Definition 1.3.1's three conditions; the atlas builds it and proves it, for arbitrary local maps rather than hard interventions only. Same declarations as RE24's truncated-factorisation row, because it is the same formula, and the same witness: `Examples…jointProb_sum_shiftCollapse` runs a translation composed with a non-injective map, neither of which eq. (1.37) can express |
| eq. (1.37) full-profile corollaries | forcing every variable leaves a point mass, and an outcome function is then evaluated at the forced value | `fixProfile`, `Model.jointProb_fixProfile` | Yes | Same | Pearl states the truncated product and does not separately assert this consequence of it. By the rule above that is coverage and not a widening, so the cell stays `Same`; the corollaries are proved for every finite acyclic variable set, which is the printed generality |
| Def. 1.3.1 | a DAG is a causal Bayesian network compatible with a family of interventional distributions iff Markov relative to the graph, forced values have probability one, and unintervened CPDs are invariant | `InterventionalFamily`, `ConditionalTables`, `IsCausalBayesNetwork`, `eq_family_of_isCausalBayesNetwork`, `isCausalBayesNetwork_iff`, `Model.interventionalFamily`, `Model.isCausalBayesNetwork` | Yes | **Same** | built on 2026-08-21, and the row's own diagnosis was the design: the missing object was the family. `InterventionalFamily` is `P_*` at Definition 1.3.1's own index set, hard interventions, so a statement about it grades against the definition rather than past it. Conditions (ii) and (iii) are stated on **tables** rather than on conditionals, deliberately: print writes (iii) as *P_x(v_i given pa_i) = P(v_i given pa_i)*, a quotient, and a parent configuration of zero probability is reachable — the margin conditions of `Causal.MarginClass` exist to exclude it — so a quotient rendering would go vacuous exactly on the fibres where a degenerate mechanism needs constraining. The existential is hoisted once, one observational `q` with each member's own `r` agreeing off the intervened set; `Examples…not_isCausalBayesNetwork_badFamily` witnesses that this constrains, exhibiting a family whose two members are each truncated products and which is still not a causal Bayesian network. The truncated product is **not** part of the definition: `eq_family_of_isCausalBayesNetwork` derives it, as print does |
| Property 1, eq. (1.38) | the conditional given the parents equals the effect of setting the parents by external control | `Model.marginal`, `Model.marginal_insert_parents`, `Model.marginal_eq_sum_ancestral` | Yes | **Same** | the printed identity is *P(v_i given pa_i) = P_pa(v_i)*; the atlas states it multiplied out, as *P(v_i, pa) = P(pa) · P_pa(v_i)*, for the null-fibre reason in the Def. 1.3.1 row. It compares two *marginals* of the family, which is why it needed the marginalization layer and not just the family. The proof marginalizes both sides through the ancestral closure of `{c} ∪ Pa(c)`: erasing `c` from that closure leaves a parent-closed set — no ancestor of `c` has `c` as a parent, by acyclicity — so both marginals run over the same index set and differ by the single factor the printed conditional names |
| Property 2, eq. (1.39) | once the direct causes are controlled, no further intervention on a disjoint set changes the child's probability | `Model.marginal_singleton_do_parents`, `Model.marginal_union_targets` | Yes | **Wider** | **the note said this and the cell did not, until 2026-08-21.** Print states the property for a set disjoint from the variable *and its parents*; the atlas assumes only that the set does not contain the variable, and concludes what print concludes. A weaker hypothesis with the same conclusion is a widening, and the row is graded as one. The rest of the note stands: stated for any `extra` set not containing the variable: the marginal is the variable's own mechanism whatever else is forced. Disjointness from the *parents* is not needed and is not assumed — forcing a parent to the value it already carries changes nothing, which `marginal_union_targets` proves. The hypothesis is therefore weaker than print's and the conclusion the same |
| — | normalisation of the constructed joint | `Model.jointProb_sum`, `jointProb_sum_two` | — | **Beyond** | that the acyclic product of stored simplexes is a probability distribution is assumed in print, not argued. Proved here for every finite acyclic variable set, every positive dimension vector, and every intervention profile |

**5 Yes, 0 Partial, 0 No, 1 Beyond**, revised on 2026-08-21. The three `No` rows
were the same absence three times — no object representing the family of
interventional distributions — and `AISafetyAtlas.Causal.BayesianNetwork` is that
object. The boundary has moved: the atlas now takes Pearl's *definition* as well
as his formula, and derives the formula from it. What remains outside §1.3 is
identification — do-calculus, the back-door criterion, d-separation — which needs
a `do`-expression language rather than another distribution.
The layer was built to a written scope contract, which records what it
deliberately does not claim — notably that the observational member does not
determine the family.

---

## 8. Everitt, Carey, Langlois, Ortega & Legg, AAAI 2021 → `AISafetyAtlas.Causal.StructuralModel`

This source supplies the causal influence diagram the decision layer is a
projection of, and its own results are graphical incentive criteria. The atlas
formalizes the setup — Definitions 1 to 5, in `AISafetyAtlas.Causal.StructuralModel`
— and none of the criteria. The section is graded so that the boundary is visible, which is the reason the audit
lists `No` rows at all.

**Four narrowing axes ran through this section; three are closed and one
remains.** They are not repeated in each note. Print bounds no cardinality anywhere in Definitions 1 to 3: Definition 1
writes `dom(V)` with no condition on it and `Pa_V ⊂ V` with no condition on it,
and Definition 3 is *"a directed acyclic graph"*, full stop. Definition 4 is the
first place finiteness appears, and it restricts the **domains** — not how many
variables there are, not how many parents a variable has, and not the shape of
the acyclicity.

**The source was re-read for a global bound on 2026-08-21 and does not carry
one.** In the pinned PDF *"finite"* occurs exactly twice, both as
*"finite-domain"*, both inside Definition 4; *"discrete"*, *"finitely many"*,
*"countable"* and *"infinite"* do not occur anywhere. There is no preliminaries
sentence, footnote or `throughout`-clause declaring finiteness globally, so the
four axes below were the atlas's and not print's. Three of the four have since
been closed against that reading; the dates are on the bullets.

* **Finitely many variables — CLOSED on 2026-08-21.** `[Fintype V]` was on
  `SCM`, `CID` and `SCIM` alike. It is on none of them now. The constraint moved
  onto the operations that genuinely need it — the `Finset` accessors
  `decisions` / `utilities` / `structureNodes`, and the expectation layer — and
  `CID.IsDecision` / `CID.IsUtility` read print's *"the vertex set is partitioned
  into `X`, `D`, `U`"* as a property of each vertex, which is what a partition
  is. `mem_decisions_iff` and `mem_utilities_iff` recover the `Finset` forms
  whenever `V` happens to be a `Fintype`. Relocating a constraint from a
  definition to its use sites relaxes the definition against its own previous
  form; it is not a hypothesis added to a theorem, and it is not the laundering
  the scope rule forbids.
* **Finite domains — OPEN on Definitions 1 and 2 only.** `dom edom : V → ℕ` is
  on `SCM` and `SCIM`. It is **not** on `CID`, whose four fields are the parent
  map, the acyclicity condition, the vertex kind and the childlessness of utility
  vertices — no domains at all. On Definitions 1 and 2 the domain restriction has
  no printed counterpart; from Definition 4 on it is print's own and costs
  nothing. Closing it turns `dom` into a family of types and touches
  `Assignment`, the structural functions, and every downstream sum. It is scoped
  and not started.
* **Finite indegree — CLOSED on 2026-08-22.** `parents : V → Set V` on both
  `SCM` and `CID`, so a vertex may have infinitely many parents, which is
  print's `Pa_V ⊂ V` at Def. 1 and print's silence at Def. 3. The
  parent-reading obligation on the structural functions quantifies over the set;
  nothing in this section sums over parents, so no finiteness hypothesis was
  needed anywhere. One visible cost: a policy's defining property is no longer
  decidable, so `Fintype SCIM.Policy` is now the classical instance
  `SCIM.instFintypePolicy`. Finiteness of the policy space is unaffected, and
  nothing computes with it.
* **ℕ-ranked acyclicity — CLOSED on 2026-08-22, and the two closures are one
  closure.** `CID.acyclic` is now print's condition and nothing more:
  `∀ v, ¬ Relation.TransGen (` `· ∈ parents ·` `) v v`, no vertex reachable
  from itself. `SCM` and `SCIM` ask instead that the parent relation be
  **well-founded**. That is a genuine strengthening of print's bare word, and
  this audit states it rather than hides it: `V = ℤ` with `parents n = {n-1}`
  is acyclic and is excluded.

  **It was a narrowing, it was graded as one, and it closed on 2026-08-22.**
  An earlier draft of this preamble called it `Same` on the argument that print
  must have meant the narrower class. That is the laundering the standing rule
  forbids, and this table has no fidelity dimension in which to park it: the
  scope cell is the only cell, so a field print does not write makes the row
  `Narrower`. Definitions 1, 2, 4 and 5 read `Narrower` for this reason.

  **The witness.** `chainParents n = {n-1}` on `ℤ` satisfies `CID.acyclic`
  (`chainParents_acyclic`) and fails `SCM.wellFounded`
  (`chainParents_not_wellFounded`). On it, with two states per vertex and the
  structural function that copies the parent, the equation `eval_eq_f` asks for
  is `W v = W (v-1)`, which has **two** solutions —
  `chainParents_fixedPoint_not_unique`. Print's Definition 1 says the value is
  *"given by recursive application of the structural functions"*: one value,
  *the* value. On a diagram print's own words admit, print's own words name no
  unique assignment.

  **Retracted: this axis was labelled *provably not closable*, and the label was
  wrong.** The paragraph that carried it is kept here rather than deleted:

  > **Why that makes the axis not closable rather than merely expensive.** A
  > total `eval` could still be produced on the wider class by choice, and it
  > would even satisfy `eval_eq_f`; what it would lose is that `eval_eq_f` pins
  > it down. The atlas would then be asserting a determinacy Definition 1 does
  > not have. There is no version of this refactor that widens the class and
  > keeps the theorem meaning what it says, which is what *provably not
  > closable* is for.

  Every sentence there is true, and not one of them is about the class this
  table grades. They are about a **total** `eval`, and a total `eval` is not the
  only refactor on offer. Take `SCM.wellFounded` off the structure and `SCIM.graph_wellFounded`
  off its own; give both print's own condition in the `Relation.TransGen` form `CID`
  already carries; pass well-foundedness as a **hypothesis** to `eval` and to
  the declarations that consume it. The admitted class is then print's class
  exactly, `eval` is simply not defined where print's *"recursive application"*
  names nothing, and `eval_eq_f` still pins down what it does define. That is
  the version the old paragraph asserted does not exist. Calling the axis
  unclosable collapsed *"`eval` cannot be totalised over print's class"* into
  *"the structure must carry the field"*, and those are different claims —
  the same collapse, one dimension over, as the `Bridged` grade this preamble
  already retracts below.

  **Done.** `SCM.wellFounded` and `SCIM.graph_wellFounded` are
  gone; `SCM.acyclic` is print's word in the same form `CID` carries it; and the
  recursion's requirement is `SCM.IsWellFounded` and `CID.IsWellFounded`, two
  classes that `eval`, `jointProb`, `expectedUtility`, `optimalValue` and
  `IsMaterial` ask for. Instances carry it across `submodel`, `softIntervention`,
  `withPolicy` and `removeInfoLink`, so no statement asks for it twice.
  **Definition 4 closes**, because its column is the structure alone. Definitions
  1, 2 and 5 do not, on axes that have nothing to do with this one.

  **Why the hypothesis on the operations is not a new narrowing.** Print's
  Definition 1 asserts *"the value ... given by recursive application"* — one
  value — and `chainParents_fixedPoint_not_unique` proves print's own words name
  two on an acyclic chain. The instance is what makes print's sentence denote,
  which is the same test this preamble applies to finite `V` at Definition 5's
  maximum, and the opposite of the test it fails at the expectation layer's sum,
  where print's object denotes without the instance.

  **The witness keeps its job and loses its title.** `chainParents` and its three
  theorems are not evidence that the field belongs on the structure. They are a
  theorem about *print*: on a diagram print's own word admits, print's own words
  name no unique assignment. That is why `eval` asks for `SCM.IsWellFounded`
  wherever it is stated, and none of it is retracted.

  Definition 3 closed first and needed nothing: `CID` evaluates nothing, so it
  never carried well-foundedness and has always had print's word unmodified.
  Definition 4 closed second, once the field moved off `SCIM`.

  **Why this could not be done alone.** `wellFounded_iff_exists_rank` proves
  that while `parents` was a `Finset`, well-foundedness and an `ℕ`-valued rank
  were *equivalent* — the rank is rebuilt by well-founded recursion as one more
  than the largest rank among the parents, and that step is exactly where the
  finiteness of the parent set is spent. Dropping the rank without also dropping
  the `Finset` would have admitted precisely the same models and generalized
  nothing. The triage priced these as two axes that were cheaper together; they
  are one axis, and the note there is corrected.

**Both of the two axes above were missed when the vertex-set axis closed**, and
the Def. 1 row asserted for one day that domains were the only axis left. They
were restrictions in the structure, visible in the field types, with no printed
counterpart. They are recorded here because the miss is the reason this section
now grades on the artifact rather than on the printed object's nearest
counterpart.

**A claim this section used to make, and what replaced it.** It said the vertex
axis was "an implementation choice, not a theorem of the source", because
well-founded recursion on the acyclicity rank would evaluate an infinite diagram
whose nodes all have finite rank. The conclusion was right and the reason was
wrong about the code: `SCM.eval` was an iteration stopped after `Fintype.card V`
applications, so rank recursion was a **rewrite**, not a relabelling. The axis
closed without that rewrite, because the structures' own fields never needed the
instance — only their derived operations did.

**`[Fintype V]` on the derived operations does three jobs, and they do not get
the same verdict.** This paragraph used to give only the first two and conclude
that the instance was print's throughout; that conclusion was applied at
Definition 5 and denied at the policy row two rows apart, which is a
contradiction a reader meets without looking for it. Adjudicated once, on
2026-08-22:

1. **The maximum over policies is attained.** Print writes `V*(M)` as the
   *maximum* of `E_π[U]` over policies, not a supremum, and states no condition
   delivering one; over an infinite policy space it need not be attained. Finite
   `V` delivers it. **Transcribes print** — `optimalValue` as a `Finset.sup'`
   with `exists_isOptimalPolicy` exhibiting the attaining policy is print's own
   sentence made to denote, not a class cut below print's.
2. **The utility total converges.** `E_π[U]` sums over utility vertices, which
   print never bounds; at infinitely many the sum need not converge.
   **Transcribes print**, for the same reason.
3. **The expectation is a finite sum.** `exoJoint` is `∏ v : V`, `jointProb`
   sums over `ExoAssignment V edom`, and `expectedUtility` sums over the same —
   each a `Finset` operation that exists only at `[Fintype V]`. **This one
   cuts.** Print's `P(ε)` is a distribution under which the exogenous variables
   are *mutually independent*, and mutual independence denotes at unbounded `V`:
   it is the product measure, which exists. The atlas renders it as a finite
   product and a finite sum. That is the atlas's elementary choice, not print's
   silence being filled, and it is a **narrowing** — the same one the policy row
   has named all along.

**Which rows carry job 3.** Definition 1, through `jointProb`, `jointProb_sum`
and `exoJoint_mul_prod`; Definition 5, through `optimalValue`, which is a
`Finset.sup'` **of** `expectedUtility` and so inherits its summation; and the
policy row, which named it first. **Definition 2 does not** — `submodel`,
`submodel_eval`, `submodel_eval_notMem` and `softIntervention` every one carry
`omit [Fintype V]`, so that column is instance-free. **Definition 4 does not** —
its column is `Causal.SCIM`, a structure that has carried no `[Fintype V]` since
2026-08-21.

**What this costs, stated plainly: it adds an axis to two rows and closes
none.** Definitions 1 and 5 each gain a third named axis and neither grade
moves, because both were already `Narrower`. The policy row keeps `Mixed` and
gains a sharper reason. The alternative reading — job 3 also transcribes — would
have moved the policy row to `Wider` and gained a cell, and it is the reading
this adjudication rejects.

**The source Definitions 1 and 2 are attributed to, read at last — 2026-08-22.**
Print heads them *"Structural causal model; Pearl 2009, Chapter 7"* and
*"Submodel; Pearl 2009, Chapter 7"*. This section grades against Everitt's
statement of them, because that is the text transcribed, and that convention
stands. But nothing in this audit had ever opened Pearl 7.1.1, and it says three
things that change how the axes here should be read.

* **Pearl's endogenous set is finite.** *"`V` is a set `{V₁, V₂, …, Vₙ}` of
  variables"*, with the structural functions indexed `i = 1, …, n`. So the
  `[Fintype V]` this section removed on 2026-08-21 — as a narrowing against
  Everitt, who never bounds the vertex set — was **Pearl's own condition**.
  Dropping it did not repay a debt; it widened the atlas past *both* sources.
  That is `Wider`, which the standing rule permits, and it is worth saying
  plainly rather than leaving on the books as a closed narrowing.
* **Pearl bounds no domain**, and neither does Everitt before Definition 4. Axis
  B is a narrowing against both, and it is the one axis here that both sources
  agree the atlas invented.
* **Pearl requires unique solvability, in the definition.** Clause (iii) ends
  *"and the entire set `F` has a unique solution `V(u)`"*, with a footnote:
  *"Uniqueness is ensured in recursive (i.e., acyclic) systems. Halpern (1998)
  allows multiple solutions in nonrecursive systems."* So determinacy is part of
  the object for Pearl, and acyclicity is offered as a *sufficient condition* for
  it rather than as the content.

**That third point re-reads this section's largest argument.** `chainParents`
was written as a witness that Everitt's *"acyclic"* fails to name a unique
`W(ε)` at an unbounded vertex set. It is that. But against Pearl it says
something sharper: Everitt's paraphrase **dropped a clause its own cited source
carries**, and the clause it dropped is exactly the one `SCM.IsWellFounded`
restores. Pearl's footnote even anticipates the failure — uniqueness is ensured
in *recursive* systems, which at finite `V` is what acyclicity delivers and at
unbounded `V` is not. So the atlas's shape here — print's `acyclic` as a field,
solvability as a property asked for where the recursion is used — is **not** a
strengthening of the source-of-record. It is the source-of-record's own clause,
carried where it can be discharged rather than assumed everywhere.

**And the treatment that pushes this object as far as it goes — 2026-08-22.**
Bongers, Forré, Peters and Mooij, *Foundations of structural causal models with
cycles and latent variables*, Annals of Statistics 49(5), 2885–2915, read from
the pinned PDF `2021 foundations of structural causal models with cycles and
latent variables.pdf`, sha256
`6ce97700deb27a6e6fc680d0bd8cbfd053f1f67392979afca8e67d9f289a6d31`. It is the
mathematicians' general version — cycles allowed, latent variables, arbitrary
domains — so it is the right place to ask which of this section's axes the field
actually cares about. Definition 2.1 makes an SCM a tuple
`⟨I, J, 𝒳, ℰ, f, P_ℰ⟩` where:

* **`I` is a finite index set of endogenous variables**, and `J` a disjoint
  finite index set of exogenous ones. The most general published treatment of
  this object keeps the vertex set finite, exactly as Pearl does and as Everitt's
  paraphrase does not. **So the `[Fintype V]` this section removed on 2026-08-21
  was a debt to nobody.** It is a `Wider` cell rather than a repaid narrowing,
  and the honest note is that the widening is free and has no known consumer.
* **Domains are arbitrary standard measurable spaces**, `𝒳 = ∏_{i ∈ I} 𝒳_i`, and
  `f : 𝒳 × ℰ → 𝒳` is measurable. **This is where the literature generalizes**,
  and it is exactly axis B taken past `Fin (dom v)` — so of the axes still open
  here, domains is the one that matters to the field, and it is also the one both
  Pearl and Everitt leave unbounded.
* **`P_ℰ` is a product measure.** Print's *"mutually independent"* rendered as a
  product is the general form, not a finite-sum convenience — what this section
  calls axis F is the difference between a product **measure** and a `Finset`
  product, not between independence and something weaker.
* **Acyclicity is not in the tuple.** *"Although it is common to assume the
  absence of cyclic functional relations, we make no such assumption here. In
  particular, we allow for self-cycles."* Definition 2.9 then defines *acyclic*
  as a property of the SCM's graph. And Definition 2.3 makes a **solution** a
  pair of random variables satisfying the structural equations almost surely,
  with Example 2.4 exhibiting one SCM with a continuum of solutions and one with
  none at all. Unique solvability is a **named condition** the theory carries
  where it needs it.

**That is the shape axis E produced, arrived at independently.** Solvability as
a property asked for where the recursion is used, rather than acyclicity as a
field standing in for it. The remaining difference is that `SCM` still carries
`acyclic` as a field where this treatment carries none — which is a further
widening available later, not a defect, since print does write the word.

**Where the rows stand after 2026-08-22.** **Definitions 3 and 4 close.**
Definition 4 closed last, when `SCIM.graph_wellFounded` came off and became
`CID.IsWellFounded` — a property asked for by the declarations that evaluate
rather than a field of the tuple. Definition 5 did not follow, and the reason is
the grading convention rather than the mathematics: its column also holds
`optimalValue` and `removeInfoLink`, so the expectation layer is graded there
and Definition 4's is the structure alone. Definitions 1 and 2 keep domains, and
Definition 1 additionally keeps the expectation layer. **Two open axes remain in
this section** — domains and the expectation layer's `[Fintype V]` — and the
well-foundedness axis is closed rather than open, having been labelled *provably
not closable* in an intermediate revision. The policy row stays `Mixed`.

**This paragraph read "Definitions 3, 4 and 5 close" in an earlier revision**, on
the strength of a `Same`/`Bridged` grade that this table has no fidelity column
to express. The scope cell is the only cell, and a field print does not write
makes a row `Narrower` no matter how good the argument for the field is. The
argument was good and is kept — it is now the *witness* attached to a
`Narrower` axis rather than a reason to call the row `Same`, which is the state
the standing rule actually provides for.

What the refactor did buy on those four rows is real and smaller than claimed:
finite indegree closed outright, and the acyclicity axis **shrank** — an
`ℕ`-valued rank is strictly stronger than well-foundedness once parent sets may
be infinite, so the admitted class genuinely widened. It did not reach print.

The policy row does **not** close, and the triage predicted wrongly that it
would become plainly `Wider`. Its graph-axis half is indeed gone, but a third
narrowing survives and was already named in its own note: `expectedUtility` sums
over `ExoAssignment V edom` and `exists_isOptimalPolicy` needs the policy type
finite, so `[Fintype V]` is still present in that row's operations even though
it is absent from `SCIM` itself. Wider on the decision axis, narrower on the
vertex-set axis: still `Mixed`.

Each note below says only what its row adds to the axes above.

**The convention these rows are graded under, stated because it decides three of
them.** A row is graded on **every declaration in its atlas column**, not on the
printed object's nearest atlas counterpart alone. That is the atlas's existing
convention, written into `registry.yaml` as *"both are in the public types, so
the row is graded on the artifact"*. It matters because `CID.decisions`,
`CID.utilities` and `CID.structureNodes` are `Finset.univ.filter …` and need
`[Fintype V]` even though `CID` does not. Grading the structure alone would let
a row read `Same` while the operations it names are unavailable at the
generality the row claims.

The finiteness axis is **not** applied to Pearl §1.3, which is also formalized over a
`[Fintype C]` graph. That is deliberate and it makes the grading non-uniform:
Everitt's finiteness is load-bearing — `eval` needs it to terminate and
`optimalValue` needs it to be a maximum — whereas Pearl's displayed (1.37) is a
finite product over the graph's own vertices, so a finite index set is what the
printed equation already ranges over. A reader who disagrees should read this
paragraph as the whole of the disagreement.

| # | printed statement | atlas | Cov. | Scope | note |
|---|---|---|---|---|---|
| Def. 1 structural causal model | a tuple `⟨E, V, F, P⟩` with one exogenous variable per endogenous one, structural functions `f^V : dom(Pa_V ∪ {E^V}) → dom(V)` with acyclic dependencies, and a `P(ε)` under which the exogenous variables are mutually independent | `Causal.SCM`, `SCM.eval`, `SCM.eval_eq_f`, `SCM.jointProb`, `SCM.jointProb_sum`, `SCM.exoJoint_mul_prod`, `wellFounded_iff_exists_rank`, `chainParents`, `chainParents_acyclic`, `chainParents_not_wellFounded`, `chainParents_fixedPoint_not_unique` | Yes | **Narrower** | **The `Fintype V` axis closed on 2026-08-21.** Across the whole paper *"finite"* occurs exactly twice, both inside Def. 4 and both qualifying **domains**; the vertex set is never bounded. `SCM`, `CID` and `SCIM` therefore no longer carry `[Fintype V]`: the constraint moved onto the derived operations that genuinely need it — the `Finset` accessors and the expectation layer. That relaxes the definition against its own previous form rather than adding a hypothesis to a theorem, so it moves the row toward print rather than away. `CID.IsDecision` and `CID.IsUtility` read print's *"the vertex set is partitioned into `X`, `D`, `U`"* as a property of each vertex, which is what a partition is; `mem_decisions_iff` and `mem_utilities_iff` recover the `Finset` forms whenever `V` is a `Fintype`. **Source-class narrowing**: this module has no library-module importer, so nothing proved elsewhere in the tree is weaker for it, and the cost falls on a future consumer instantiating `SCM` outside the admitted class. **Two axes remain and both are open, and costed.** (i) Domains — OPEN: print writes `dom(V)` with no cardinality condition and imposes finiteness only at Def. 4, while `SCM` carries `dom edom : V → ℕ`; closing it turns `dom` into a family of types and touches `Assignment`, `f`, and every downstream sum. Scoped, not started, and the only thing keeping this row off `Same`. (ii) Finite indegree — CLOSED 2026-08-22: `parents : V → Set V`, print's unbounded `Pa_V ⊂ V`. (iii) Acyclicity — **CLOSED 2026-08-22, in two steps.** It was an `ℕ`-rank, then well-foundedness of the parent relation, and it is now `SCM.acyclic : ∀ v, ¬ Relation.TransGen (` `· ∈ parents ·` `) v v` — print's *"acyclic"* and nothing more, the same condition `CID` carries. Well-foundedness did not disappear; it moved to `SCM.IsWellFounded`, a class every declaration downstream of the recursion asks for. **That hypothesis is not a fourth axis**, on the criterion the preamble adjudicates: print's Definition 1 asserts *"the value ... given by recursive application of the structural functions"* — one value, *the* value — and `chainParents_fixedPoint_not_unique` proves that on an acyclic chain print's own words name **two**. So the instance is what makes print's sentence denote, exactly as finite `V` is what makes print's *maximum* denote at Definition 5. `chainParents` and its three theorems are the witness for the hypothesis; the earlier reading of them, that the axis was *provably not closable*, was retracted, and the preamble carries the retracted paragraph in full. **This row read `Same` in an intermediate revision** on a `Bridged` fidelity grade this table has no column for. `eval` no longer needs `[Fintype V]` either — it is well-founded recursion rather than an iteration run to a bound, and that iteration together with its two rank lemmas is deleted — so the sentence that graded the instance here no longer has a referent. `wellFounded_iff_exists_rank` is in this row's column because it is the witness that (ii) and (iii) were a single axis: while `parents` was a `Finset` the two acyclicity forms were equivalent. (iv) The expectation layer's `[Fintype V]` — **OPEN, and named here from 2026-08-22**: `jointProb`, `jointProb_sum` and `exoJoint_mul_prod` are `Finset` sums and products over `V`, which exist only at a finite vertex set, while print's `P(ε)` denotes at unbounded `V` because mutual independence gives a product measure. The preamble adjudicates this instance's three jobs and explains why attainment and utility-convergence transcribe print while summation does not. This row carried the axis unnamed until that adjudication; the policy row named it, and the two were graded inconsistently for as long as both existed. **The retracted sentence is left visible rather than deleted**: it once read *"One axis remains and it is domains"* while three remained. It is still not true — domains are the only *open* axis, but well-foundedness is a second axis in a different state, and collapsing the two is the same undercount that produced the retraction. |
| Def. 2 submodel | `M_x := ⟨E, V, F_x, P⟩` with `F_x = {f^V \| V ∉ X} ∪ {X = x}`; more generally a soft intervention replaces `f^X` by a `g^X` on the same domain | `SCM.submodel`, `SCM.submodel_eval`, `SCM.submodel_eval_notMem`, `SCM.softIntervention` | Yes | **Narrower** | print's construction, and **Source-class narrowing**, inherited: same module, same absence of importers. It inherits **one** of Def. 1's two remaining axes — domains, open and costed — because `submodel` copies `parents` and the acyclicity field unchanged and alters only `f`. It does **not** carry the expectation layer's `[Fintype V]`: all four of this column's declarations are `omit [Fintype V]`. Well-foundedness closed here with Definition 1 on 2026-08-22; `submodel` now builds print's `acyclic` by `Relation.TransGen.mono`, and `instIsWellFoundedSubmodel` carries the recursion's hypothesis across an intervention by `Subrelation.wf`, since forcing a variable only deletes edges. The vertex-set axis closed on 2026-08-21 and finite indegree closed on 2026-08-22, so neither is among them; `submodel` now inherits well-foundedness by `Subrelation.wf`, since forcing a variable only deletes edges. `submodel_eval` is *"the original functional relationships of `X ∈ 𝐗` are replaced with the constant functions `X = x`"* read off the evaluation. |
| Def. 3 causal influence diagram | a DAG whose vertex set is partitioned into structure, decision and utility nodes, where utility nodes have no children; `Pa_D` are the observations | `Causal.CID`, `CID.decisions`, `CID.utilities`, `CID.structureNodes`, `CID.observations`, `CID.decisions_disjoint_utilities`, `acyclic_of_rank` | Yes | **Same** | **The `Fintype V` axis closed on 2026-08-21.** Across the whole paper *"finite"* occurs exactly twice, both inside Def. 4 and both qualifying **domains**; the vertex set is never bounded. `SCM`, `CID` and `SCIM` therefore no longer carry `[Fintype V]`: the constraint moved onto the derived operations that genuinely need it — the `Finset` accessors and the expectation layer. That relaxes the definition against its own previous form rather than adding a hypothesis to a theorem, so it moves the row toward print rather than away. `CID.IsDecision` and `CID.IsUtility` read print's *"the vertex set is partitioned into `X`, `D`, `U`"* as a property of each vertex, which is what a partition is; `mem_decisions_iff` and `mem_utilities_iff` recover the `Finset` forms whenever `V` is a `Fintype`. **Def. 3 closed on 2026-08-22, having read `Same` wrongly for one day in between.** A CID carries no domains, so that axis was always absent here; the two that were present were `CID`'s own fields, and both are gone. `parents : V → Set V` is print's unbounded vertex subset. `acyclic` is now `∀ v, ¬ Relation.TransGen (` `· ∈ parents ·` `) v v` — no vertex reachable from itself, which is *"a directed acyclic graph"* and nothing more. **This is the only one of Definitions 1 to 5 that closes.** Definition 3 is a graph and evaluates nothing, so it needs no well-foundedness; that strengthening lives on `SCM` and `SCIM`, which do evaluate, and keeps those rows `Narrower` with the `chainParents` witness attached. `acyclic_of_rank` is in this column as the constructor a finite worked example uses. Under this section's stated convention the row also carries `decisions` / `utilities` / `structureNodes`, which are `Finset.univ.filter …` and need `[Fintype V]`; `IsDecision` and `IsUtility` are the unbounded forms and `mem_decisions_iff` / `mem_utilities_iff` are the bridge, so that part is a genuine relocation rather than a cut, but the two graph axes are not. Childlessness of utility nodes is a structure field with a worked counter-witness in the examples. |
| policy invariance off `Desc_D` (asserted after Def. 4) | *"We use `Pr^π` and `Eπ` to denote probabilities and expectations with respect to `Mπ`. For a set of variables `X` not in `Desc_D`, `Pr^π(x)` is independent of `π` and we simply write `Pr(x)`."* | `CID.IsDescendant`, `CID.NotDownstream`, `CID.not_isDecision_of_notDownstream`, `CID.notDownstream_of_mem_parents`, `SCM.eval_eq_of_f_agree`, `SCM.marginal`, `SCM.marginal_eq_sum_exo`, `SCIM.eval_withPolicy_eq_of_notDownstream`, `SCIM.marginal_withPolicy_eq_of_notDownstream` | Yes | **Mixed** | **New on 2026-08-22. This sentence had no row until then, and that is an inventory gap rather than a coverage one**: it is a printed assertion in the paragraph that introduces `Pr^π`, and this table's rule is that every printed claim gets a row whether or not the atlas covers it. It was missed because it sits in running prose between Definition 4 and Definition 5 rather than in a numbered environment. **Wider on two axes.** Print *asserts* it and proves nothing — the notation *"we simply write `Pr(x)`"* is well defined only if it holds — and the atlas proves it, which is one of this audit's six recognised widenings. And print writes `Desc_D` having already restricted to `𝐃 = {D}`, while `CID.NotDownstream` quantifies over every decision vertex, so the statement holds on the multi-decision diagrams where print states nothing; at print's own restriction it is print's condition exactly. **Narrower on one**, and it is the expectation layer again: `SCM.marginal` is a `Finset` sum over `Assignment V dom` and carries `[Fintype V]`, which `#check` confirms, so this row carries the axis §8's preamble adjudicates. The two `eval`-level declarations do not — `eval_eq_of_f_agree` and `eval_withPolicy_eq_of_notDownstream` are `omit [Fintype V]` — but a row is graded on every declaration in its column. **`Desc_D` is read reflexively, on purpose.** The decision is its own descendant, so the invariance is not claimed at the decision; under a *proper* reading `D` would fall outside *Desc_D* and print's sentence would assert that `Pr^π(d)` does not depend on `π`, which is false. RE24's `Anc`/`Desc` **are** proper and `Model.properAncestors` / `Model.properDescendants` carry that reading — a different paper and a different sentence, and not a discrepancy to reconcile. **What the proof turns on.** `eval_eq_of_f_agree` is the content and says nothing about policies: two models with one parent map whose structural functions agree on an ancestor-closed set evaluate alike there. The complement of `Desc_𝐃` is such a set, and `Mπ` and `Mπ'` differ only at decision vertices. `marginal_eq_sum_exo` is what carries a statement about `W(ε)` to one about `Pr`, by summing `P(ε)` over the fibres of `eval` instead of summing the joint over assignments. Inhabited on print's own Figure 2a: `figCID_notDownstream_zero` puts the opinion outside `Desc_D` and `figSCIM_marginal_opinion_policy_free` is print's `Pr(x)` there |
| policy and optimal policy (asserted after Def. 4) | a policy is a structural function from the decision's observations together with an exogenous randomness variable to the decision; an optimal policy is any policy maximising expected utility | `SCIM.Policy`, `SCIM.withPolicy`, `SCIM.expectedUtility`, `SCIM.IsOptimalPolicy`, `SCIM.exists_isOptimalPolicy`, `SCIM.policy_ext_single` | Yes | **Mixed** | **This row has been regraded more than any other in the table, and the reason is the finding: the regrades turned on miscounts of the narrowing side rather than on new mathematics.** Two of the three narrowing halves really are gone. The vertex-set half closed when `SCIM` shed `[Fintype V]`: `Policy` is indexed by `{d // graph.IsDecision d}`, a subtype over a property, so the policy space is defined at unbounded `V`. The domain half was never the atlas's: this object is asserted **after** Def. 4, where *"finite-domain variables"* and *"finite-domain exogenous variables"* are print's own words, so `Fin (dom d)` and `Assignment V dom` transcribe print. What remains is the widening, which was disclosed all along: print writes a single `π` because it has *already* restricted to `𝐃 = {D}`, and the atlas carries one structural function per decision vertex, so it defines the object at multi-decision diagrams where print defines nothing. `policy_ext_single` proves that at print's own restriction the family is print's datum exactly. Indexing by the decision subtype rather than by a membership proof is what keeps `withPolicy` free of transports between `Fin (dom v)` and `Fin (dom d)`. `Eπ[U]` is taken **in `Mπ`**, which is where print defines `Eπ`, so it is print's definition rather than a formula that agrees with it. **What puts the row back to `Mixed` is the narrowing that was never counted.** `withPolicy` used to build an `SCM` from `M.graph.parents` and `M.graph.acyclic`, so every declaration in this row inherited `CID`'s finite indegree and ℕ-ranked acyclicity, which print's policy paragraph asks for neither of. **Both closed on 2026-08-22** and that half of the narrowing is gone: `withPolicy` now hands `SCM` print's own `CID.acyclic`, and `instIsWellFoundedWithPolicy` supplies the recursion's hypothesis from `CID.IsWellFounded` — a property of the diagram rather than a field of `SCIM`, which is what closed the Definition 4 row. `expectedUtility` additionally sums over `ExoAssignment V edom`, which is a `Fintype` only when `V` is — so the vertex-set constraint is still present in this row's operations even though it is gone from `SCIM` itself. **Sharpened 2026-08-22, and half of what this sentence used to say is withdrawn.** It also cited `exists_isOptimalPolicy` needing the policy type finite. That is not an axis: print writes `V*(M)` as a *maximum* and states no condition delivering one, so finiteness supplies print's own assertion rather than cutting below it, and the Definition 5 row has always graded it that way. What remains an axis is the summation alone — print's `P(ε)` denotes at unbounded `V` as a product measure and a `Finset` sum does not. The preamble adjudicates the instance's three jobs once and applies the result to this row and to Definition 5 together; **until that adjudication the two rows graded the identical hypothesis in opposite directions**, which is the finding rather than either verdict. Wider on the decision axis, narrower on the vertex-set axis: that is what `Mixed` is for, and it is still the honest grade. The triage predicted this row would go plainly `Wider` once the graph axes closed. That prediction was wrong, and it was wrong against information this row's own note already carried: it counted only the graph half of the narrowing. **`Causal.Decision`'s `Policy` keeps its own row and its own grade**: it is the unmediated projection of MAIS `def:cid`, an induced conditional law rather than a structural function, and nothing here widens it |
| Def. 4 structural causal influence model | a CID with finite-domain variables whose utility domains are a subset of `ℝ`, one finite-domain exogenous variable per endogenous one, and structural functions on `𝐕 \ 𝐃` | `Causal.SCIM` | Yes | **Same** | **The `Fintype V` axis closed on 2026-08-21.** Across the whole paper *"finite"* occurs exactly twice, both inside Def. 4 and both qualifying **domains**; the vertex set is never bounded. `SCM`, `CID` and `SCIM` therefore no longer carry `[Fintype V]`: the constraint moved onto the derived operations that genuinely need it — the `Finset` accessors and the expectation layer. That relaxes the definition against its own previous form rather than adding a hypothesis to a theorem, so it moves the row toward print rather than away. `CID.IsDecision` and `CID.IsUtility` read print's *"the vertex set is partitioned into `X`, `D`, `U`"* as a property of each vertex, which is what a partition is; `mem_decisions_iff` and `mem_utilities_iff` recover the `Finset` forms whenever `V` is a `Fintype`. **Def. 4 does not close, and read `Same` twice on two different bad arguments.** Its own addition was always fine: the *domain* finiteness this definition introduces is print's own — *"a CID with finite-domain variables"*, *"finite-domain exogenous variables"* — so `dom edom : V → ℕ` transcribes print from here on and is **not** an axis at this row, which is the one point on which this section's grading is more forgiving than a naive one would be. The vertex-set axis is likewise gone, and what used to remain — Def. 3's finite indegree and ℕ-ranked acyclicity, inherited through `SCIM.graph` — closed with Def. 3. `F` is a function of a proof that the vertex is **not** a decision, which is `¬ IsDecision` rather than `Finset` non-membership. **Closed 2026-08-22 by axis E, and this time by moving Lean rather than prose.** What had kept it `Narrower` was `SCIM.graph_wellFounded`, a field asking the diagram's parent relation to be well-founded where `CID.acyclic` asks only for print's word. That field is **gone**. Definition 4 is where print first writes a model that gets **evaluated** — one definition later, `V*(M)` is the maximum of `Eπ[U]` over policies and runs `W(ε)` in `Mπ` — and that recursion determines a value exactly on well-founded diagrams, so the requirement is real; it is now `CID.IsWellFounded`, a **property of a diagram** that `expectedUtility`, `optimalValue` and `IsMaterial` each ask for, rather than a field of the tuple. `chainParents` and its three theorems keep their job as the witness that print's *"recursive application"* names nothing unique without it. **This row read `Same` twice before, on arguments rather than code** — once on a `Bridged` fidelity grade this table has no column for, once on a `provably not closable` label that confused *"`eval` cannot be totalised"* with *"the structure must carry the field"*. Neither is what closes it now: the class of tuples `SCIM` admits is print's class, which is what this table grades. **The two remaining fields print does not write in so many words, examined rather than assumed.** `SCIM.utilityValue_injective` is print's *"utility variable domains are a subset of `ℝ`"*: a subset of `ℝ` is exactly a set injected into `ℝ`, and the injection is the naming of the states, so this is a representation of print's clause with its own converting fact rather than an addition. `SCIM.dom_pos` asks every domain to be nonempty, which print does not write — and a tuple violating it has **no assignment at all**, so print's own Definition 1 assertion that `W(ε)` has a value is false there. It excludes exactly the tuples on which print's stated conditions cannot hold, which is not the same as excluding tuples that satisfy them; well-foundedness was the second kind, and that is why it had to move and this does not. |
| Def. 5 materiality | `V*(M)` is the maximum of `Eπ[U]` over policies, `M_{X↛D}` is `M` with the information link removed, and `X ∈ Pa_D` is material when `V*(M_{X↛D}) < V*(M)` | `SCIM.optimalValue`, `SCIM.removeInfoLink`, `SCIM.IsMaterial`, `SCIM.removeInfoLink_sub` | Yes | **Narrower** | **Source-class narrowing**: `SCIM.optimalValue` and `SCIM.IsMaterial` are named nowhere outside this module and its examples. **Partly closed on 2026-08-21, and the part that closed is the part where the finiteness is print's own.** Print writes `V*(M)` as the maximum of `E_π[U]` over policies. Without a finite vertex set `U` is a sum over possibly infinitely many utility vertices that need not converge, and that maximum ranges over an infinite policy space and need not be **attained** — print writes a maximum, not a supremum, and states no condition delivering either. Finite `V` delivers both, so `optimalValue` as a `Finset.sup'` transcribes print's content instead of cutting below it; `exists_isOptimalPolicy` exhibits the attaining policy print presumes. `IsMaterial` now takes `IsDecision` rather than `Finset` membership. **That argument survives every pass, and from 2026-08-22 it is no longer the whole story.** It defends two of the three jobs `[Fintype V]` does here — the maximum being attained and the utility total converging — and says nothing about the third. `optimalValue` is a `Finset.sup'` **of** `expectedUtility`, which sums over `ExoAssignment V edom`; print's `P(ε)` denotes at unbounded `V` because mutual independence is a product measure, and a `Finset` sum does not. **So this row does carry the expectation layer's `[Fintype V]` as an axis**, exactly as the policy row two rows above has said all along — the two rows contradicted each other for as long as both existed, and the preamble now adjudicates it once. The consequence is that **this row does not close when well-foundedness does**: Definition 4's column is the structure alone, and this one's is not. **What kept the row `Narrower` until 2026-08-22 has now closed**: `removeInfoLink` and `optimalValue` are taken at a `SCIM` whose graph is a `CID`, and so used to inherit Def. 3's finite indegree and ℕ-ranked acyclicity. Neither survives — the parent map is a `Set` and the diagram's condition is print's own. `removeInfoLink` keeps both by `Subrelation.wf` and `Relation.TransGen.mono`, since deleting an information link only removes edges; `removeInfoLink_sub` is that one fact, used once for acyclicity and once for well-foundedness. **What kept the row `Narrower` here was Def. 4's field rather than anything this row adds**: `V*(M)` evaluates `Mπ`, so well-foundedness is what makes print's own maximum refer to a determinate quantity. **That axis closed on 2026-08-22**: `SCIM` no longer carries the field, `optimalValue` and `IsMaterial` ask for `CID.IsWellFounded` instead, and `instIsWellFoundedRemoveInfoLink` carries it across the deleted information link so print's inequality needs the hypothesis once rather than at each side. The hypothesis is not itself an axis, for the reason the preamble adjudicates: print's *"recursive application"* names nothing unique without it. **Unlike Definition 4, this row did not close when that axis did**, and the reason is the sentence above — Definition 4's column is the structure alone, this one's also holds `optimalValue` and `removeInfoLink`, so the expectation layer is graded here. **It read `Same` in an intermediate revision** on a fidelity grade this table has no column for. The classical `Fintype SCIM.Policy` instance the `Set` parent map forced changes no grade — it is the same finite policy space, decided classically. |
| Thm. 9 value-of-information criterion | an observation has positive value of information exactly under a graphical condition on the diagram | — | No | — | requires the diagram as an object with decision and utility vertices |
| Thm. 14 counterfactual fairness and response incentives | a graphical characterisation relating counterfactual fairness to the response incentive | — | No | — | Definition 4's structural layer now exists; what is missing is the response incentive, the nested counterfactuals it is defined by, and d-separation |
| Thm. 16 value-of-control criterion | a node has positive value of control exactly under a graphical condition | — | No | — | same missing object as Theorem 9 |
| Thm. 18 instrumental control incentive criterion | an instrumental control incentive holds exactly under a directed-path condition through the decision | — | No | — | same |
| — | zero regret characterised, and the optimum attained without a diagram | `Model.regret_decomp`, `Model.regret_eq_zero_iff`, `Model.bestDecision` | — | **Beyond** | the printed source defines regret and reasons about optima; the fibrewise-argmax characterisation, with ties left unconstrained, is proved here and not stated there |

**7 Yes, 0 Partial, 4 No, 1 Beyond**, up from `6 Yes` on 2026-08-22 — not
because anything was proved that was previously missing from this table, but
because a printed sentence was missing **from the table**. Print's *"for a set
of variables `X` not in `Desc_D`, `Pr^π(x)` is independent of `π`"* sits in
running prose between Definitions 4 and 5, and every earlier pass over this
source enumerated the numbered environments. It now has a row, and the atlas
proves it. The setup is formalized and the results
are not. The four `No` rows are the incentive theorems, and they no longer fail
on a missing model: `Causal.SCIM` is Definition 4 and `SCIM.IsMaterial` is
Definition 5. What is absent is **d-separation** — Definition 6, a path algebra
the atlas has no counterpart for — and the incentive concepts themselves, whose
*completeness* halves are constructions of witnessing SCIMs rather than
derivations. That is a second layer on this one, not a continuation of it.

Assumption 1 remains a scope fence in this formalization rather than a
hypothesis — `Causal.Decision` *is* the unmediated projection, and `Causal.SCIM`
is a separate object no statement in that module is phrased over — which is why
there is no declaration stating it. **Nothing here re-grades section 6.**
Richens & Everitt's §2.2 value and regret are still the unmediated projection:
`Model.value` takes a policy on a `Model`, and wiring it to a SCIM's decision
vertex is a construction nobody has written.

**Two ingredient sources are deliberately ungraded.** Uhler, Raskutti, Bühlmann
& Yu 2013 and Meek 1995 motivate replacing a measure-zero exception with an
explicit margin, and are cited for that role in
`mais-a2-causal-collision.md`. No atlas declaration transcribes a statement from
either: strong faithfulness bounds a partial correlation, and the six margin
conditions bound CPT entries and utility gaps. Grading them would produce a
section of `No` rows resting on a single sentence, so they are recorded here
instead of tabulated.

---

## Totals

| source | Yes | Partial | No | Beyond |
|---|---|---|---|---|
| Cover & Thomas §2.8 | 11 | 0 | 0 | 0 |
| Cover & Thomas §2.10 | 9 | 0 | 2 | 1 |
| Ashby ch. 11 | 11 | 0 | 4 | 0 |
| Igel–Toussaint / SVW | 14 | 0 | 1 | 1 |
| Touchette & Lloyd | 12 | 0 | 2 | 0 |
| Richens & Everitt 2024 | 10 | 0 | 13 | 4 |
| Pearl §1.3 | 5 | 0 | 0 | 1 |
| Everitt et al. 2021 | 7 | 0 | 4 | 1 |
| **total** | **79** | **0** | **26** | **8** |

## Reading the totals

**Where the atlas is genuinely stronger:** the `Wider` verdicts rest on six
kinds of widening, and each row's note names which. Note which is *not* among
them — an arbitrary sample space in place of a fixed discrete one is a
presentation, for the reason given above. A hypothesis weakened to only what the
proof uses (Ashby's column condition); a hypothesis *derived*
rather than assumed (Ashby 11/8); a statement the source asserts without proof
(**three as of 2026-08-22**: two inside the proof of 2.8.1, and Everitt's
policy-invariance sentence, which is asserted in running prose between
Definitions 4 and 5 and proved in §8's new row for it); a wider class of objects or
parameters quantified over (signed weights in IT Thm 5, arbitrary sample length
in SVW NFL3, a different estimate *type* in `fano_of_embedding`); a sharper
conclusion at the same hypotheses (Ashby's integer `⌈r/c⌉`, Fano's surviving
`−1` in the no-observation remark); and a statement proved **off** an optimum as
well as at it, where the source only states it at the optimum (Touchette–Lloyd's
Theorems 2, 3 and 4, each proved at every controller and then transferred to the
minimized `L_C`). The causal sections add a seventh: **a scalar field left as a
parameter** where print fixes the reals. `Model` and the margin layer are stated
over any ordered field of characteristic zero, so print's real case is an
instance, witnesses are computed on rational literals, and the transport lemmas
carry them back. That is a strict widening rather than a presentation, and the
rational instance is what witnesses it — `margin_class_not_identifiable` lives
in a field the printed statement cannot name.

**Counting the weak cells, and one warning about how.** As of 2026-08-22 the
scope column holds **five `Narrower` and two `Mixed`**. Six of the seven are
definitions; the seventh, Everitt's policy-invariance sentence, is a printed
*assertion of a fact*. That breaks a line this audit used to carry — that every
`Narrower` or `Mixed` row is a definition and no printed claim is narrower — and
it is worth stating because both `Mixed` labels end in *"(asserted after Def.
4)"*. Anything that sorts rows by matching `Def.` in the label will file the
assertion under definitions and report six definition-level defects where there
are five.

**Where it is weaker, and why — what actually remains:**

1. *(closed)* **The decision layer's rationals.** `AISafetyAtlas.Causal.Decision`
   now carries its value field as a parameter like the rest of the causal layer,
   so the printed real case is an instance. The review that gated this named an
   obstruction which does not exist, and carries a dated addendum saying so.

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

4. **The unmediated projection is structural, not costed.** Decision and utility
   are not vertices of the graph `Causal.Decision` is stated over, so RE24's
   Assumption 1 is a scope fence rather than a hypothesis. **The missing object
   is no longer the CID layer.** `Causal.CID` and `Causal.SCIM` exist, with
   decision and utility vertices, policies as structural functions, and expected
   utility taken in the induced SCM. What is missing is the *wiring*: nothing
   sends a SCIM's decision vertex to `Model.value`, so §2.2's expected utility
   and regret are still the projection. That is a construction, and it is what
   this point now names. Everitt's own graphical criteria need a second thing on
   top of it — d-separation, Definition 6, which has no counterpart here.
5. **Neither identification theorem is reachable.** RE24's Theorems 1 and 2 need
   a chart of a *CID's* parameters carrying an almost-every quantifier, and a
   policy oracle. Neither object exists, which is why §6's thirteen `No` rows are
   `No` and not `Partial`: they fail on a missing object, not on a missing step.
   Since 2026-08-21 the chart half is a narrower gap than it reads: a real
   parameter chart with a Lebesgue estimate over it exists for MAIS's unmediated
   chance-variable tables (`ChartIndex`, `Model.chartOn`, and MAIS-O24's certificate layer).
   It is not RE24's, because `D` and `U` are not vertices in it — so this row
   turns on the same missing wiring as point 4, not on measure theory. A CID with
   those vertices now exists; a chart over *its* parameters does not.

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
