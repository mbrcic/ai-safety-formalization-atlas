# Ashby, requisite variety — source record and scope

Evidence for `BY-004` (Law of Requisite Variety). The Lean is
[`AISafetyAtlas/Control/RequisiteVariety.lean`](../../AISafetyAtlas/Control/RequisiteVariety.lean)
for the law itself,
[`AISafetyAtlas/Control/ChannelRate.lean`](../../AISafetyAtlas/Control/ChannelRate.lean)
for §9/15's entropy-rate capacity, and
[`AISafetyAtlas/Control/CompleteControl.lean`](../../AISafetyAtlas/Control/CompleteControl.lean)
for §11/14's control on top of regulation, each with worked readings alongside it
in [`AISafetyAtlas/Examples/Control/`](../../AISafetyAtlas/Examples/Control/).

## The source

`survey-ref-026` cites *"R. W. Ashby, Introduction to Cybernetics. 1961 Edition.
Chapman & Hall, 1961."* The text read for this formalization is that book,
chapter 11 (*Requisite Variety*), §11/1–§11/21, printed pp. 202–218; page numbers below are
the printed 204–208.

**One gap in the pinned copy.** `ashby-1961-introduction-to-cybernetics.pdf` runs
book p. 273 straight into p. 289, omitting *Answers to Exercises* (pp. 274–288),
which its own table of contents lists. Nothing in this note depends on that
section; where an exercise answer is quoted — §11/14's, below — it is read from
the Martino Fine Books (2015) reprint and the reprint is named at the quotation.
The pinned copy stays canonical for everything it does contain.

**Citation clash, not corrected in the registry.** The author is **W. Ross
Ashby**, not "R. W. Ashby". The initials are transposed in the survey's
reference list, and `survey-ref-026` records the survey's citation text
verbatim, as every `survey-ref-*` entry does. The clash is recorded here rather
than silently repaired in `registry.yaml`, because that catalogue's job is to
say what the survey cited.

## What the chapter states

Ashby gives the law three times over.

| section | statement |
|---|---|
| 11/5 | Rows are disturbances, columns the regulator's moves, entries outcomes. "If no two elements in the same column are equal, and if a set of outcomes is selected by `R`, one from each row, and if the table has `r` rows and `c` columns, then the variety in the selected set of outcomes cannot be fewer than `r/c`." |
| 11/7 | With varieties measured logarithmically, `V_O`'s minimum is `V_D − V_R`. |
| 11/8 | For information sources, assuming `H_R(E) ≥ H_R(D)`: `H(E)` has a minimum, equal to `H(D) − H(R)` when `R` is a determinate function of `D`. |
| 11/9 | With each column entry repeated `k` times, `V_O ≥ V_D − log k − log V_R`; in entropies, with `H_R(E) ≥ H_R(D) − K`, the minimum becomes `H(D) − K − H(R)`. |
| 11/10 | The law "states that certain events are impossible", and the impossibility is not empirical. |

## Source clashes

Three places where the printed text does not determine a formal statement, or
determines a defective one. A row here is a record that a choice was made, not a
proof gap.

### 1. The conclusion of 11/8 is misprinted — REPAIRED

The printed final line is

> `H(E) > H(D) + H_D(E) – H(R)`

The `H_D(E)` cannot be right. Ashby's own derivation, three lines above, runs

```
H(D) + H_D(R) = H(R) + H_R(D)      both sides equal H(R,D)
H(D) + H_D(R) ≤ H(R) + H_R(E)      substituting the hypothesis H_R(E) ≥ H_R(D)
              = H(R,E)
H(R,E)        ≤ H(R) + H(E)        subadditivity
```

which gives `H(E) ≥ H(D) + H_D(R) − H(R)`. The very next sentence confirms it:
*"it can be made least when `H_D(R) = 0`, i.e. when `R` is a determinate
function of `D`"* — a remark that is only meaningful if the term carried into
the conclusion is `H_D(R)`. The formalized statement
`entropy_ge_of_condEntropy_ge` uses `H[R | D]`; the printed `H_D(E)` is treated
as a typesetting error.

### 2. Relation symbols — READING FIXED

The 1961 typesetting renders `≤` and `≥` as `<` and `>` throughout 11/8 and
11/9 (for instance `H(R,E) < H(R) + H(E)`, which is false as a strict
inequality — it is an equality whenever `R` and `E` are independent). The
non-strict reading is the only one the derivation supports and is the one
formalized.

### 3. `log V_R` in 11/9 — REPAIRED BY UNIFICATION

11/9 states `V_O > V_D − log k − log V_R` while also saying the varieties "are
measured logarithmically", which makes `log V_R` a second logarithm of an
already-logarithmic quantity. The intended content is the multiplicative bound
`|D| ≤ k · |outcomes| · |R|`, whose logarithm is `V_O ≥ V_D − log k − V_R`.

Rather than transcribe either reading, the atlas states the multiplicative form
once (`card_le_mul_card_admittedOutcomes_mul`) with `k` as a parameter, and
derives the logarithmic form from it. Ashby's 11/5 is then the `k = 1` case of
the same theorem rather than a separate result.

## Scope: where the Lean exceeds the source

The ambient space is **not** one of these axes. The variables are `FiniteRange`,
so they push forward to a pmf on Shannon's discrete alphabet and the statements
are inter-derivable; see the sample-space note in `source-coverage-audit.md`.

| axis | printed | atlas |
|---|---|---|
| multiplicity | 11/5 and 11/9 are separate arguments | one theorem, `k` a parameter; 11/5 is `k = 1` |
| column condition | *no* column may repeat an entry | `Set.InjOn` on `ρ ⁻¹' {r}` only, **in the two counting theorems** — entries a strategy never selects are unconstrained |
| disturbances | a finite table | any `Finset` of disturbances over arbitrary types |
| table hypothesis | `H_R(E) ≥ H_R(D)` is assumed | `condEntropy_outcome_eq` proves it, as an equality, from the column condition |
| information | §9/15 measures capacity by an entropy rate; §11/11's exercises use noiseless signal counts | both are formalized: `channelCapacity O = log \|O\|` for the exercises' alphabet ceilings, and `chainRate` / `ashbyCapacity` for §9/15's general rate, with `entropy_outcome_ge_sub_chainEntropy` the §11/11 bound against it |

The weakened column condition is substantive where it applies: Ashby's hypothesis
constrains the whole table, whereas only the part of it a given strategy visits
can matter to that strategy's outcomes.

**It applies to two theorems, not to the module.**
`card_le_mul_card_admittedOutcomes` and `card_le_mul_card_admittedOutcomes_mul`
carry the fibre-restricted condition. Everything derived from them —
`ashby_variety_ge`, `card_ceilDiv_le_admittedOutcomes`,
`two_le_card_admittedOutcomes`, `ashby_logVariety_ge`, `entropy_outcome_ge`,
`entropy_outcome_ge_of_strategy` and `entropy_ge_of_sensor` — takes full
`Function.Injective`, because each quantifies over strategies and so cannot name
the fibre in advance. (`condEntropy_outcome_eq` takes the column condition too,
but is `condEntropy_of_injective` and depends on neither counting lemma.) The
weakening does **not** hold for the development as a whole.

## The bound is attained

Ashby's 11/6 asserts the reduction is achievable — "to a half, but not lower" —
and the chapter argues it by example. `ashby_variety_ge_isSharp` supplies the
general witness, at every shape `(r, c)` with `c ≥ 1` and with no divisibility
assumed: a disturbance `d` is read as `(d / c, d % c)`, the regulator's move
shifts the residue, and the strategy that plays the residue cancels it.

Two things the chapter's prose does not distinguish, and the Lean does.

*The attainable bound is the integer one.* Outcomes are counted, so `⌈r/c⌉` is
the obstruction, and `card_ceilDiv_le_admittedOutcomes` proves it. The rational
`r/c` of `ashby_variety_ge` is **not** attainable when `c ∤ r`: at `r = 5`,
`c = 2` three outcomes must occur, not two and a half.

*It is an existence statement about one table.* No table-universal reading is
available, and `T d r = d` is the counterexample — injective columns, and every
outcome admitted under every strategy.

## Scope: where it stops

* **One exercise figure rests on a typographic inference, recorded here rather
  than assumed.** Ex. 3 gives each of ten divisions "a variety of 10⁶ bits in
  each day". The scanned 1961 text renders that as a flat `106`: this edition
  drops body-text superscripts systematically — the same page-range has
  "proportional to 108" and "100,000000 galaxies", while figure subscripts
  survive. `OpposingArmy` is built at `10^6`, not `106`. Read literally as `106`,
  `general_intelligence_insufficient` would be **false** — 1060 bits a day is far
  under the channel's 576000 — and Ex. 4, which asks whether a 500 bits/minute
  order channel suffices against the same army, would be trivial. Anyone
  re-deriving these numbers from the PDF text layer should know the reading is an
  inference.
* **Both capacities are now formalized.** `channelCapacity O = log |O|` is the
  noiseless alphabet ceiling used by all four §11/11 exercises. It is not §9/15's
  general definition: Ashby computes a three-state Markov chain's entropy as
  `0.842` bits per step and calls the resulting `2.53` bits-per-minute rate a
  measure of channel capacity, where the alphabet ceiling would be `log₂ 3` bits
  per step. That general definition is now in
  [`AISafetyAtlas/Control/ChannelRate.lean`](../../AISafetyAtlas/Control/ChannelRate.lean):
  `chainRate` is §9/12's weighted column entropy, `chainRate_eq_condEntropy`
  identifies it with `H[X₁ | X₀]`, `ashbyCapacity` is §9/15's per-unit-time rate,
  and `entropy_outcome_ge_sub_chainEntropy` is §11/11's bound against it. The
  noisy Shannon capacity `sup I(input : output)` is still not modelled, and is not
  needed: §9/15 defines capacity by the rate, not by a supremum of mutual
  information.
* **§9/15's proportionality claim is proved, and sharpened.** Ashby writes that
  *"the entropy of a length of Markov chain is proportional to its length
  (provided always that it has settled down to equilibrium)"*. `entropy_traj`
  proves it, and the exact identity is `H[X₀ … Xₙ] = H[X₀] + n · rate` — affine,
  not linear. The two agree when `H[X₀]` equals the rate, which is exactly what
  happens in the spun-coin illustration Ashby checks it against, so his example
  cannot separate them. Same class of printed slip as §11/8's `H_D(E)`.
* **The definition is checked against Ashby's own arithmetic.** His transition
  matrix has an exactly rational equilibrium, `(22/49, 21/49, 6/49)`, whose
  decimals are `0.4490, 0.4286, 0.1224` — the printed `0.449, 0.429, 0.122`.
  `Examples…ashbyInsect_stationary` proves the balance equations,
  `…ashbyInsect_proportions_match_print` the rounding, and
  `…ashbyInsect_rate_eq` evaluates `chainRate` at that chain to his weighted
  average term by term.
* **Everything about the channel is a necessary condition.** Capacity at least
  the disturbance entropy is what complete regulation requires
  (`entropy_le_channelCapacity_of_complete`); sufficiency is neither proved nor
  implied. Ashby's Ex. 1 asks whether the insect's optic nerve is "sufficient to
  enable it to defend itself", and `insect_optic_nerve_not_binding` answers only
  that the constraint does not bind. Ex. 3 asks in the direction the law settles,
  and `general_intelligence_insufficient` is a genuine impossibility.
* **§11/11 does not assume perfect information, and its bound is a rate.** The
  chapter's regulator reads a channel, so a bound by the entropy of one reading —
  `entropy_ge_of_sensor` — is narrower than the printed statement, and the
  alphabet ceiling `channelCapacity` closes only the four exercises' noiseless
  arithmetic. "Variety available" here is *not* alphabet cardinality: §9/15's
  `0.842`-bit entropy calculation immediately precedes it and is the quantity
  Ashby means, `ashbyCapacity` is that quantity, and
  `entropy_outcome_ge_sub_chainEntropy` is §11/11's bound against it. `BY-004`'s
  informal claim says "under perfect information", which matches the *counting*
  sections §11/5–11/10 rather than §11/11.
* **§11/14 is formalized, in `AISafetyAtlas.Control.CompleteControl`.** Ashby puts
  a controller `C` upstream of the regulator, so that the diagram of immediate
  effects is `D → T → E` with `C → R`, and argues twice. First structurally:
  *"Suppose now that R is a perfect regulator. If C sets a as the target, then
  (through R's agency) E will take the value a, whatever value D may take"*, and
  for a compound target *"a, b, a, c, c, a"* the whole sequence *"will be
  produced, regardless of D's values during the sequence"*, whence *"perfect
  regulation of the outcome by R makes possible a complete control over the
  outcome by C"*. Then as a channel: `R` taking information from both `C` and `D`
  *"may be able to form, with T, a compound channel to E that transmits fully
  from C while transmitting nothing from D"*, so *"the achievement of control may
  thus depend necessarily on the achievement of regulation"*.

  `IsPerfectRegulator` is the hypothesis and `outcome_eq_comp` the first half
  entire: the outcome is a function of `C` alone, with `D` eliminated rather than
  bounded. `exists_strategy_forcing` is complete control, `seq_outcome_eq` the
  compound target. The channel picture is `entropy_outcome_eq_entropy_controller`
  for *"transmits fully from C"* and `condEntropy_outcome_controller` for
  *"transmitting nothing from D"*, the latter needing no hypothesis on the
  disturbance's law at all.
* **The second half is sharpened from a gloss to a count, using §11/10.**
  *"Depend necessarily"* is qualitative in print. Perfect regulation collapses
  `admittedOutcomes` to a singleton, which `two_le_card_admittedOutcomes` already
  forbids below a threshold of regulator variety, so
  `card_disturbance_le_card_regulator` and `card_controller_le_card_regulator`
  give `|D| ≤ |R|` and `|C| ≤ |R|` — requisite variety charged twice, once for
  each of the regulator's two inputs.
* **§11/14's exercises, and one place the printed answer asks for more than the
  model gives.** `FactorsThrough` is the atlas's rendering of the two-input
  diagram, a hypothesis rather than a consequence: the regulator sees `C` only
  through one channel and `D` only through another. Under it, Ex. 3 is
  `channelCapacity_controller_le_channel` and Ex. 2 is
  `channelCapacity_disturbance_le_channel`, both per use where Ashby quotes bits
  per second.

  Ex. 4 asks for the `R → T` link and answers by **adding** the two loads: *"R→T
  must carry 2 bits/sec to neutralise D (from Ex. 2), and 20 bits/sec from C; as
  these two are independent (D's values and C's not correlated), the capacity
  must be at least 22 bits/sec."* What the model forces is the **maximum**,
  `max_channelCapacity_le_channelCapacity_regulator`. Additivity is a property of
  the table rather than of the diagram, and Ashby's own answer to Ex. 1 shows it:
  `Examples.Control.ashbyControl_isPerfectRegulator` checks that answer against
  Table 11/3/1 and `Examples.Control.ashbyControl_capacity_lt_sum` records that
  its regulator's whole repertoire is `log 3` where the additive reading would
  demand `log 9`. **This is not a correction to his arithmetic.** Ex. 4 inherits
  Ex. 2's `T`, stipulated to attenuate — *"if R is constant, E will vary at 2
  bits/second"* against 5 bits/second emitted at `D` — whereas Table 11/3/1
  attenuates nothing, so the two exercises concern different tables. What is
  established is a limit on what §11/14's diagram alone implies.
  `channelCapacity_prod` is the lemma that licenses the sum where the `R → T`
  link really is two independent sub-channels carried side by side.
* **Ashby's answers are not in the pinned scan** (see *The source*); read from
  the Martino Fine Books (2015) reprint, book p. 285, they are: `D → R` at least
  `2` bits/sec — *"D is threatening to transmit to E at 2 bits/sec. To reduce this
  to zero the channel D→R must transmit at not less than this rate"* — `C → R` at
  least `20`, and `R → T` at least `22`. Note that the `5` bits/sec of noise
  stated at `D` is not the operative figure; what matters is the `2` bits/sec that
  reach `E` through `T`.
* **"Unbounded response speed"**, the other qualifier in `BY-004`'s informal
  claim, has no counterpart here. Ashby's chapter 11 is untimed — the table has
  no dynamics — so nothing in this formalization speaks to response latency.
  Chapter 12 and the Conant–Ashby good-regulator theorem (`survey-ref-025`) are
  where that thread continues; neither is formalized.
* **No bridge to a real regulator is claimed.** `ai_bridge_status` stays
  `HUMAN_REVIEW`.

## Reproduction

```
lake build AISafetyAtlas.Control.RequisiteVariety AISafetyAtlas.Examples.Control.RequisiteVariety
lake build AISafetyAtlas.Control.ChannelRate AISafetyAtlas.Examples.Control.ChannelRate
lake build AISafetyAtlas.Control.CompleteControl AISafetyAtlas.Examples.Control.CompleteControl
```

Axioms for every declaration named above are within `{propext,
Classical.choice, Quot.sound}`; `ashbyTable_column_injective` uses only
`{propext, Quot.sound}`. No `sorry`, no `native_decide`.
