# Touchette–Lloyd, information-theoretic control limits — source record and scope

Evidence for `BY-005`. The Lean is
[`AISafetyAtlas/Control/InformationLimits.lean`](../../AISafetyAtlas/Control/InformationLimits.lean),
with worked readings in
[`AISafetyAtlas/Examples/Control/InformationLimits.lean`](../../AISafetyAtlas/Examples/Control/InformationLimits.lean).

## The source, and which text was read

`survey-ref-027` cites H. Touchette and S. Lloyd, *Information-theoretic
approach to the study of control systems*, Physica A 331(1):140–172, Jan. 2004,
doi `10.1016/j.physa.2003.09.007`.

**The published text has been read.** The formalization was originally
carried out against **arXiv:`physics/0104007v2`** (16 May 2003), the authors'
latest preprint. Checking the two against each other: **Theorems 1–11 are
numbered identically**, and Theorems 2, 3, 4 and 10 — the four formalized here —
match statement for statement. The preprint was therefore a faithful stand-in,
and this note records the check rather than assuming it.

Every graded record on this row is nevertheless `RELATED`; see *Scope* below for
what separates it from `EXACT`.

## What is formalized

| source | statement | pointwise in the controller | at the printed `L_C` |
|---|---|---|---|
| Theorem 2 | `L_C ≤ H(Z)` | `entropy_noise_sub_controlLoss`, `controlLoss_le_entropy_noise` | `minControlLoss_le_entropy_noise` |
| Theorem 2 | equality iff `H(Z\|X',X,C) = 0` | `controlLoss_eq_entropy_noise_iff` | `minControlLoss_eq_entropy_noise_iff_of_attained` with `minControlLoss_inputPolicies_attained` |
| Theorem 3 | `L_C = I(X' : Z \| X, C)` | `controlLoss_eq_condMutualInfo` | `minControlLoss_eq_sInf_condMutualInfo` |
| Theorem 4 | `L_C = I(X' : X,C,Z) − I(X' : X,C)` | `controlLoss_eq_mutualInfo_sub` | `minControlLoss_eq_sInf_mutualInfo_sub` |
| eq. (28) | `L_C = min over {p(c\|x)} of ∑ₓ p(x) ∑_c H(X'\|x,c) p(c\|x)` | — | `kernelMinControlLoss`, `kernelControlLoss_eq_sum`, `kernelMinControlLoss_eq` |
| Theorem 10 | `ΔH_closed ≤ ΔH_open^max + I(X ; C)` | `entropyReduction_le_of_condEntropy_ge` | `kernelEntropyReduction_le_kernelOpenLoopMax`, stated for an arbitrary Markov kernel; `entropyReduction_le_openLoopMax` is the plant-model form |
| eq. (7) | purification: any channel is a randomly selected deterministic channel | — | `isPurification_purifyMap`, `exists_isPurification` |
| eq. (48) | `ΔH_open^max = max over p_X ∈ P, c ∈ C` | — | `kernelOpenLoopMax`, with `openLoopMax_purifyMap` proving the plant-model rendering generates the same set and `isGreatest_kernelOpenLoopMax` proving the maximum attained |
| Lemma 8 | `ΔH_open ≤ ΔH_open^C`, equality iff `I(X';C) = 0` | `entropyReduction_le_condEntropy_form`, `entropyReduction_eq_condEntropy_form_iff` | — (needs no minimum) |
| Theorem 9 | `ΔH_open ≤ max_c ΔH_open^c`, with equality attainable | `entropyReduction_le_iSup_openLoopReduction`, `exists_entropyReduction_const_eq_iSup_openLoopReduction` | `kernelEntropyReduction_le_iSup_kernelOpenLoop`, `exists_kernelEntropyReduction_dirac_eq_iSup`, for an arbitrary Markov kernel |
| Theorem 5 | perfectly observable iff `L_S = 0` | `perfectlyObservable_iff_sensorLoss_eq_zero` | — |
| Theorem 6 | `L_S = 0` ⟹ `I(X ; Z \| C) = 0` | `condMutualInfo_eq_zero_of_sensorLoss_eq_zero` | — |
| Corollary 7 | `L_S = 0` ⟹ `I(X ; C,Z) = I(X ; C)` | `mutualInfo_prod_eq_of_sensorLoss_eq_zero` | — |

Theorem 10 is the paper's stated main result: *one bit gathered by the
controller is worth at most one bit of improvement over open-loop control.*

The modules are `AISafetyAtlas/Control/InformationLimits.lean` (the control loss
and Theorem 10), `PolicyKernel.lean` (eq. 28 as a minimum over kernels),
`OpenLoop.lean` (Lemma 8, Theorem 9, eq. 48), `Observability.lean` (the sensor
side), `Purification.lean` (eq. 7, and Theorems 9 and 10 restated for an
arbitrary kernel) and `OpenLoopAttainment.lean` (eq. 48's maximum is attained).

## Scope: where the Lean exceeds the source

The ambient space is **not** one of these axes. The atlas variables are
`FiniteRange`, so they push the measure forward to a pmf on the printed finite
alphabets and the two statements are inter-derivable; see the sample-space note
in `source-coverage-audit.md`.

| axis | printed | atlas |
|---|---|---|
| Theorem 2 | an inequality plus a separately argued equality condition | the exact identity `H(Z) − L_C = H(Z \| X', X, C)`, of which both printed halves are corollaries |
| actuation model for Theorems 9 and 10 | an arbitrary fixed transition kernel `p(x'|x,c)`, with §2 *asserting* that any such channel is a randomly selected deterministic one | the same, with the assertion **proved**: `isPurification_purifyMap` builds the seed and `kernelEntropyReduction_le_kernelOpenLoopMax` states Theorem 10 with no `F` and no `Z` in it |
| eq. (7) | stated as a remark, with two conditions and no construction | a theorem with an explicit witness, the seed being the finite space of deterministic channels |

## Scope: why every record is still `RELATED`

Two independent reasons were recorded here. Both are now addressed for the
printed finite-alphabet setting — the first by `kernelMinControlLoss`, the
second by `isPurification_purifyMap`, which proves the paper's own §2 assertion
that any actuation channel is a randomly selected deterministic one. The records
remain `RELATED` pending a deliberate decision on `EXACT`; the source audit now
grades every graded row from this source `Yes`, Theorem 10 included.

### 1. `L_C` is a minimized quantity, and one half of Theorem 2 needs the minimum to be attained — closed

The paper defines the average control loss with a minimization over all
conditional distributions for `C`, and says why:

> *"The minimization over all conditional distributions for `C` is there to
> ensure that `L_C` reflects the properties of the actuation channel, and does
> not depend on one's choice of control inputs."*

and repeats, before Theorems 3 and 4, that *"the minimization over the set of
conditional probability distributions `{p(c|x)}` is implied at this point"*.

Both quantities are in the atlas. `AISafetyAtlas.Control.controlLoss` is the
loss of the controller at hand; `minControlLoss` is an infimum over a represented
set of controllers sharing one `IsPlant`. That preserves the source distinction
between a fixed plant and a varying policy.

**The source's own object is now declared.** `kernelMinControlLoss` is the
infimum of the control loss over Mathlib `Kernel S K` Markov kernels — eq. (28)'s
`{p(c|x)}`, realized as `μ ⊗ₘ κ.comap X` on `Ω × K` — and
`minControlLoss_inputPolicies_eq_kernelMin` proves it equal to the realized
infimum over `inputPolicies`. The argument is the source's own displayed second
line: eq. (28) minimizes `∑ₓ p_X(x) ∑_c H(X'|x,c) p(c|x)`, which is *linear* in
`p(c|x)` because the numbers `H(X'|x,c)` belong to the actuation channel. A
linear objective on a simplex is minimized at a vertex, so deterministic state
feedback attains it — and deterministic policies need no auxiliary randomness, so
they exist on every sample space. That is why no realization construction is
needed and why the two infima cannot differ. `[Fintype S]` and `[Fintype K]` are
required, which is the printed setting. The
pointwise results are the stronger ones, since they hold at *every* controller,
and the arbitrary-`P` infimum theorems apply to each represented feasible family:

* the **inequality** of Theorem 2, because an infimum is capped by any single
  member — so purification is needed at one admitted controller, not across the
  family, which is a weaker hypothesis than the paper's;
* **Theorems 3 and 4**, because two functions equal at every point have equal
  infima, so the printed equality between minima follows with no minimizer.

`Examples…minControlLoss_lt_controlLoss_gate` shows the two quantities really can
differ — a gate plant with two admitted controllers whose losses are `0` and
`log 2` — so the minimization is not decoration and neither is its formalization.

The audit's current rule is **obtainability**: the pointwise theorem plus the
arbitrary-`P` infimum theorem is enough to read the printed Theorems 2–4 as
consequences for a represented feasible family. A stricter rule requiring the
kernel object itself to be declared would need to be applied repo-wide, not only
to this row. The representation gap that this paragraph used to record as
remaining is now closed by `minControlLoss_inputPolicies_eq_kernelMin`, for the
printed setting of finite alphabets; the obtainability rule above is what carried
the rows *before* that, and it is left standing because it is what the other
sources are graded under.

**Theorem 2's equality condition** was the one row this cost. "Equality holds iff
`H(Z|X',X,C) = 0`" is a statement about a **minimizer**, and a minimizer of the
represented family need not minimize the source's. Both halves are now supplied:
the two minima coincide, and `minControlLoss_inputPolicies_attained` exhibits an
admitted policy that no admitted policy beats. So the attainment hypothesis of
`minControlLoss_eq_entropy_noise_iff_of_attained` is dischargeable and the audit
row is `Yes`.

Worth recording that the *source* never exhibits a minimizer either — it writes
`min` where its own argument supports `inf`. The atlas now has the stronger
object.

### 2. Theorem 10's step (50) — closed

The paper writes that *"a closed-loop controller is formally equivalent to an
ensemble of open-loop controllers acting on the conditional supports
`supp(X|c)` instead of `supp(X)`"*, and derives

> `H(X'|c)_closed ≥ H(X|c) − ΔH_open^max`  for all `c`

from that equivalence. **The paper does justify it**, in one sentence beneath the
proof: *"each conditional distribution `p(x|c)` is a legitimate input
distribution for the initial state of the controlled system. It is, in any cases,
an element of `P`."* So the step is print's own, and the mechanization is a
transcription of it rather than something beyond the source.

Two theorems are supplied, and the difference between them is the point.

* `entropyReduction_le_of_condEntropy_ge` takes the averaged form of step (50)
  as an explicit hypothesis and asserts nothing about the model. This is the
  conservative reading and it is exactly what follows *from* the step.
  `condEntropy_le_condEntropy_of_forall` supplies the averaging from the paper's
  per-action form, and asks for the per-action inequality only where the action
  has positive probability.
* `entropyReduction_le_of_openLoopBound` **derives** step (50), by mechanizing
  that sentence. `IsPlant F X C Z X'` says the final state is `F(X, C, Z)` — the
  actuation channel written as a map.
  `OpenLoopBound μ F X Z Δopen` says no *constant* control reduces the entropy of
  the state by more than `Δopen`, on every **conditional ensemble of `μ`**. On
  the event `C = c` the plant is driven by the constant `c`, so the conditional
  ensemble is acted on open-loop and the bound applies to it.

**How `OpenLoopBound` relates to the printed `ΔH_open^max`: it does not, in
either direction.** The source is explicit about the ensemble: equation (48) and
the sentence under it give the maximum as
*"over any input distribution chosen in the set `P` of all probability
distributions"*. The two families still do not nest: the printed maximum varies
the input distribution with the actuation subdynamics held fixed, whereas
conditioning `μ` on an event can also change the joint law of state and noise.
That non-nesting is a fact about `OpenLoopBound` and it stands.

**The response was to build a useful rendering of the printed object.**
`openLoopMax F η` is a supremum over *all* probability measures on the state
space and all control values, with an independent noise law `η` fixed.
Boundedness is load-bearing, since `Real.sSup` of an unbounded set is `0`;
`[Fintype S]` supplies it via `bddAbove_openLoopReductions`, a reduction being
capped by the entropy of its own input distribution and so by `log |S|`.

Within that realization, step (50) becomes an instance: the conditional law
`p(x|c)` is one of the distributions ranged over.
`condEntropy_ge_of_openLoopMax` is that step and
`entropyReduction_le_openLoopMax` is the resulting inequality. The theorem
requires `IndepFun ⟨X,C⟩ Z`, which `map_prodMk_cond_eq_prod` converts into "a
control fibre is an honest open-loop ensemble".

**That assumption is the paper's own, and the realization theorem exists.** It
might look as though the independence assumption were justified only by
importing step (30), which belongs to Theorem 2's purification argument, while
Theorem 10 is stated for an arbitrary fixed transition subdynamics. That reading
is wrong: the paper does not confine purification to Theorem 2: §2, in the paragraph
introducing Fig. 2 and eq. (7), states it as a modelling move available for
**any** channel, before Section 3 and long before the open-loop section —

> any non-deterministic channel modeling a source of noise at the level of
> actuation or estimation can be represented abstractly as a randomly selected
> deterministic channel with transition matrix containing only zeros and ones

with condition (i) — the extended matrix is deterministic given `c` and `z` —
and condition (ii), eq. (7), `p(x'|x,c) = ∑_z p(x'|x,c,z) p_Z(z)`. Those are
`IsPlant` and `IndepFun ⟨X,C⟩ Z` respectively, the second because the weight is
`p_Z(z)` and not `p(z|x,c)`, which is what "exogenous" means. The error was
reading where purification is *used* instead of where it is *introduced*.

What the paper does not do is construct the representation; it asserts it.
`AISafetyAtlas/Control/Purification.lean` constructs it, taking the paper's own
phrase literally: a *randomly selected deterministic channel* is a random
element of the space `S × K → T` of deterministic channels, which is finite when
the alphabets are, so no continuum seed is needed. `purifySeed κ` is the product
measure drawing each column independently from `κ`, `purifyMap` applies the drawn
channel, and `isPurification_purifyMap` is eq. (7). `exists_isPurification` is
the §2 remark with a witness attached.

Two consequences. `kernelEntropyReduction_le_kernelOpenLoopMax` is Theorem 10
with no `F` and no `Z` in the statement — only a joint law `ρ` and a kernel `κ` —
and `openLoopMax_purifyMap` proves the two renderings of eq. (48) generate the
**same set** of reductions, so their suprema coincide exactly rather than merely
comparing. Theorem 9 gets the same treatment in
`kernelEntropyReduction_le_iSup_kernelOpenLoop`, with its printed attainment
clause in `exists_kernelEntropyReduction_dirac_eq_iSup`: a Dirac action law at
the paper's *ĉ* achieves the supremum, which is a theorem there because that
supremum is over the finite `K`.

**The second residual — eq. (48)'s `max` — is closed too**, in
`AISafetyAtlas/Control/OpenLoopAttainment.lean`. The atlas had
`bddAbove_openLoopReductions` and `sSup`, which is formally weaker than print
because `max ≤ sSup`. The argument that removes the gap is the expected one, with
the work in the plumbing: on a finite state space `weights` and `ofWeights` are
mutually inverse between probability measures and the points of Mathlib's
standard simplex; in those coordinates the reduction is `openLoopObjective`, an
explicit finite sum of *negMulLog* terms whose inner argument is *linear* in the
weights, because `comp_ofWeights_real` says running the kernel averages its
columns; continuity of *negMulLog* and compactness of the simplex then give a
maximizing input law for each action, and the action alphabet is finite.
`isGreatest_kernelOpenLoopMax` is the conclusion — eq. (48)'s value is an element
of the set it is the supremum of — and `exists_kernelEntropyReduction_le_at_max`
restates Theorem 10 with its right-hand side realized by an explicit input
distribution and action.

Theorem 10 is therefore `Yes`, and this source has no `Partial` rows left.

`entropyReduction_le_of_openLoopBound` is kept alongside the kernel-scope
statement. Its hypothesis is incomparable with eq. (48)'s, which is precisely
why both are worth having.

`IsPlant` and `OpenLoopBound` are the atlas's rendering of the paper's model, not
formulas the paper writes. `Examples…openLoopBound_forgetSecond` instantiates the
definition at `Δopen = log 2` for a plant that erases one bit of a two-bit state
— strictly below the trivial ceiling `log 4` — and
`Examples…not_openLoopBound_erase` shows the definition is not satisfied by every
`Δopen`, so it is not vacuous in either direction.

## Also not covered

Two numbered results remain, and the reason in each case is that nothing in the
atlas wants them, not that they are hard.

* **Theorem 1** — perfect controllability at `X = x` iff a reachability clause
  and a determinacy clause hold. It is an *existential* over conditional
  distributions, so it needs the kernel object as a quantified witness rather
  than as an infimum, and what it characterizes is reachability, not an
  information limit.
* **Theorem 11** — closed-loop optimality iff `I(X';C) = 0`, and only under the
  constancy condition `ΔH_open^c = ΔH_closed^c = ΔH` for every `c`. It needs a
  notion of closed-loop optimality the atlas does not define, and the conclusion
  it reaches is already carried by Theorem 10 without the extra model.

Two unnumbered items are also left, and both are the source's own loose ends:

* **`L_S ≤ H(Z_B)`**, the backward-purification analogue of Theorem 2 for the
  sensor. The paper states it in prose on p. 154 and tells the reader to redo
  Theorem 2's proof with `H(X|C,Z_B) = 0` in place of the forward condition. It
  is not an audit row and is not formalized.
* **The converse of Theorem 6.** The source says explicitly that it fails, and
  the atlas claims only the stated direction.

* **The quantum sections.** Out of scope.
* **No AI-system bridge.** `ai_bridge_status` stays `HUMAN_REVIEW`.

## What it composes with

`entropyReduction_le_of_sensor` (in the examples) derives from Theorem 10 that a
controller acting on a sensor reading gains at most `H(obs ∘ X)` over open-loop
control. That is the same conclusion
[`AISafetyAtlas.Control.entropy_ge_of_sensor`](../../AISafetyAtlas/Control/RequisiteVariety.lean)
reaches from Ashby's law — see
[`ashby-requisite-variety.md`](ashby-requisite-variety.md). `BY-004` and `BY-005`
were the two rows `docs/guide/methodology.md` recorded as blocked on a Shannon
entropy layer the atlas lacked; both are now closed, and they meet.

## Reproduction

```
lake build AISafetyAtlas.Control.InformationLimits AISafetyAtlas.Control.PolicyKernel \
  AISafetyAtlas.Control.OpenLoop AISafetyAtlas.Control.Observability \
  AISafetyAtlas.Control.Purification AISafetyAtlas.Control.OpenLoopAttainment \
  AISafetyAtlas.Examples.Control.InformationLimits AISafetyAtlas.Examples.Control.PolicyKernel \
  AISafetyAtlas.Examples.Control.OpenLoop AISafetyAtlas.Examples.Control.Observability \
  AISafetyAtlas.Examples.Control.Purification \
  AISafetyAtlas.Examples.Control.OpenLoopAttainment
```

Axioms for every declaration named above are within `{propext,
Classical.choice, Quot.sound}`. No `sorry`, no `native_decide`.
