# MAIS-A2 causal layer — source concordance

This note separates the peer-reviewed ingredients from the A2 composite and
from the issue-[#6](https://github.com/lionellevine/MAIS/issues/6) construction. It covers `AISafetyAtlas.Causal.Model`,
`MarginClass`, `Decision`, and their two worked examples.

Statement-by-statement status for the A2 targets is recorded with the
conjecture layer, which is where the propositions it tracks are stated.

## Source pins

Sources are identified by SHA-256 of the exact bytes read, which is the evidence a reader can check; no local store path is part of it. The three
files used for the Layer-0/1 definitions were checked on 2026-08-19:

| Work | File | SHA-256 |
|---|---|---|
| Pearl, *Causality*, 2nd ed. (2009) | `pearl-2009-causality-second-edition.pdf` | `0c1e7bd1676260feb5ec909839b01f1ff16538febfe23755192e565895202e4c` |
| Richens--Everitt, ICLR 2024 (working text) | `richens-everitt-2024-iclr-robust-agents-learn-causal-world-models.pdf` | `b25a2c7e8fe27d1dfd00299166197d8f3bd2ac8af7102f3b2a07585cfd6743b2` |
| Everitt et al., AAAI 2021 | `everitt-etal-2021-aaai-ojs.pdf` | `31d4a4b277c562b82000c4d2b81660e89464877ec0cad3549a9375c6d4492598` |

MAIS is a directory and question source, not a definitional authority. Lookup
line numbers refer to `lionellevine/MAIS` commit
`9dd29f8bf5ccd1e7701e300039b09ed4096b6516`; `MAIS-A2.tex` has MD5
`cf0282db5c02e761af0aae7ee43e06bb`, and `MAIS-O23.md` has MD5
`11e7f19c6b967a127159051303fe68ee`.

Grades used below: `SOURCE-EXACT` means the same mathematical object modulo
notation; `EQUIVALENT` names a proved representation change; `NARROWER` or
`WIDER` records scope; `RELATED` means the Lean object is useful packaging but
is not the cited result; `ATLAS` is a derived lemma or composite.

## 1. Finite categorical causal kernel

The kernel is constructive data `(G, θ)`. It is not Pearl Definition 1.3.1,
which is a semantic compatibility condition on a family of distributions.

| Lean | Printed source | Grade and boundary |
|---|---|---|
| `Assignment C dim`, `Model.dim_pos`, full-simplex `Model.cpt` | RE24 Appendix A.2 categorical parameterization | **SOURCE-EXACT** in finite type and, since the value field is a parameter, at the printed real tables. Print omits the last cell only as a free-coordinate chart; Lean stores every cell and its sum-to-one proof. |
| `LocalIntervention dim c = Fin (dim c) → Fin (dim c)` | RE24 Definition 2 | **SOURCE-EXACT**. It is any local map, not a four-constructor Boolean encoding. |
| `identityIntervention`, `fixIntervention`, `flipIntervention` | RE24 Definition 2 examples | **SOURCE-EXACT** instances. `card_binaryLocalIntervention` derives four maps only after specializing to `Fin 2`. |
| `InterventionProfile` | Product of local maps used as `Prof(C)` in A2/RE24 | **EQUIVALENT** product packaging; Definition 2 itself introduces one-variable maps. |
| `Model.factor` / `factor_eq_re24` | RE24 equation (1) | **SOURCE-EXACT**: the literal preimage sum `Σ_{a:f(a)=b} P(a∣pa)`. |
| `factor_congr` | construction from `cpt_parents` | **ATLAS**. This is not Pearl (1.37)(iii); it proves parent dependence by construction. |
| `hardInterventionProfile`, `jointProb_hardInterventionProfile`; `fixProfile`, `jointProb_fixProfile`, `Δ_fixProfile` | Pearl truncated factorization (1.37) | **EQUIVALENT**, **NARROWER** to the finite constructive CBN representation over any one value field: intervened factors become consistency indicators and unselected factors remain. The full-profile corollaries give the Dirac joint and evaluate an outcome function at the target. For arbitrary local maps, `jointProb` is the product of RE24 equation-(1) factors. |
| `jointProb_sum` | the construction denotes a probability | **ATLAS**, proved for every finite acyclic `C`, every positive `dim`, and every profile. `jointProb_sum_two` is only its binary witness-facing corollary. |
| `Mixture`, `ProbMixture`, `jointProbMix`, `Δmix` | RE24 Definition 3 | `ProbMixture C dim 𝕜` is the Definition-3 simplex over whichever field a statement picks, so at `𝕜 := ℝ` it is **SOURCE-EXACT** for the printed real weights. Ambient `Mixture` is **WIDER** than that simplex and remains only for linear lemmas. `Δmix_eq_on_probMixture_iff` proves that equality on probability mixtures is equivalent to equality on deterministic profiles, and that finiteness is what lets `Skeleton.behaviorEq_mapRat` carry a rational witness to the whole real simplex. |
| `Model.Δ` | general unmediated expected-utility gap | **ATLAS**. RE24 Appendix B equation (3) is one two-variable hard-`do(X=0)` instance with the opposite sign, not this definition. |
| `ParentClosed`, `ancestors`, `ancestors_eq_univ_iff` | ancestor closure used by A2 (M5) | **EQUIVALENT** closure representation plus **ATLAS** bridge lemmas. |

`factor_nonneg`, `jointProb_nonneg`, `factor_sum`, the hard-profile lemmas,
`Model.ext`, and the finite-sum splitting lemmas are kernel support. They
establish that the stored simplex and acyclic product really form normalized
finite distributions and certify the stated hard-intervention reading; they do
not add a paper-level identifiability claim.

`AISafetyAtlas.Examples.Causal.Model` is the categorical worked model required
by this foundation. Its ternary root feeds a binary child; the intervention
profile combines translation modulo three with a non-injective child map.
`factor_root`, `factor_child`, and `jointProb_sum_shiftCollapse` exercise the
preimage formula and normalization outside the binary specialization.

## 2. A2 margin and behavioral composite

The six labels come from A2. Uhler et al. 2013 motivates replacing a
measure-zero exception by an explicit margin, but its strong-faithfulness
object is `|ρᵢⱼ·K| ≥ λ`, not these CPT inequalities. No row below is graded
against Uhler's statement.

| Lean | Role | Grade and boundary |
|---|---|---|
| `Skeleton` | unmediated task data `(O,Z,U)` | **NARROWER** only in its full-assignment representation; the value field is a parameter, so the printed real case is reachable. Decision and utility are not graph vertices, so this is not RE24 Definition 4 or a CID. |
| `M1` | all full-simplex cells in `[λ,1-λ]` | **ATLAS categorical extension** of the binary A2 condition; includes the last simplex cell. |
| `M2`, `M3` | nonzero and sign-varying binary utility gap | **ATLAS/A2 composite**, motivated by RE24 Assumption 2. |
| `M4` | a categorical parent-coordinate change moves some child cell by `λ` | **ATLAS categorical max-entry extension** of binary A2 (M4). It is not a partial-correlation or total-variation condition. |
| `M5` | all scored variables ancestral and some state hidden | **EQUIVALENT** to its parent-closure elimination form via `ancestors_eq_univ_iff`. |
| `M6` | each categorical utility parent changes the binary gap by `λ` | **ATLAS categorical extension** of binary A2 (M6). |
| `MarginClass` | `M(s,λ)` | **EQUIVALENT after binary specialization** to the implemented A2 composite, and includes `ValidMargin`, so membership carries `0 < λ < 1/2`. |
| `Δmask`, `BehaviorEq` | A2's named masked transform family | **EQUIVALENT** finite representation over the chosen value field, with a redundant full assignment indexing each visible fibre. **RELATED** to RE24 Section 2.3, where masking drops an information edge inside `Σ`. |

## 3. Generic unmediated decision layer

RE24 Assumption 1 is a scope fence: `D` has no descendants ancestral to `U`.
Lean does not state that graph hypothesis because `D` and `U` are not vertices;
the entire module is the corresponding unmediated projection.

| Lean | Printed source | Grade and boundary |
|---|---|---|
| `Policy visible Decision` | RE24/Everitt policy mechanism `π(d∣pa_D)` | **EQUIVALENT** for any finite decision alphabet: a simplex indexed by full assignments plus a proof that it factors through visible coordinates. |
| `value`, `value_eq` | RE24 Section 2.2 expected utility | **EQUIVALENT under Assumption 1**, finite, at whichever value field a statement picks. Not valid as the full mediated-CID equation. |
| `fibreScore`, `bestDecision`, `bestPolicy`, `optimalValue` | fibrewise finite maximization | **ATLAS** implementation of the printed optimum, with ties allowed. |
| `regret`, `HasRegretAtMost` | RE24 Section 2.2 and Definition 5 | **SOURCE-EXACT** inequality within this representation. `HasRegretAtMost` contains no extra zero-regret sign clauses. |
| `regret_decomp`, `regret_eq_zero_iff` | finite convex decomposition | **ATLAS** converse: zero regret iff positive policy support lies on the fibrewise argmax; ties are unconstrained. |
| `gap`, `signPolicy`, `regret_signPolicy_eq_zero`, `value_const_sub`, strict-gap policy lemmas | binary-decision corollaries | **ATLAS**. The sign policy is proved optimal. `value_const_sub` generalizes the expected-utility-gap algebra around Appendix B (3); it is not equation (3) itself. |
| `signPolicy_eq_of_behaviorEq`, `inIdentifiedSet_zero_of_behaviorEq` | A2 transform-to-policy bridge | **EQUIVALENT forward direction**: equal masked transforms give a common zero-regret policy family. A2's converse reconstruction of the numerical transform from an arbitrary optimal-policy oracle remains cited, not formalized. |
| `InIdentifiedSet`, `modelError`, `IsRadius` | A2 query packaging | **RELATED** to RE24 Theorem 2, not a transcription. The theorem may recover `G' ⊆ G` and bounds error by `γ(δ)`; Lean packages shared low-regret families and a chosen graph-or-table error. The definition accepts every `δ` in the value field; `not_inIdentifiedSet_of_neg` proves the extension below the source domain `δ ≥ 0` is empty. |

No claim here formalizes RE24 Theorems 1–2 or an almost-every statement, and no
declaration in this table reaches a free-coordinate parameter chart or a causal
influence diagram. **Two of those objects have since been built elsewhere in the
atlas and neither is wired to this result**: `AISafetyAtlas.Causal.ParameterChart`
is a real chart over MAIS's unmediated chance tables, and
`AISafetyAtlas.Causal.StructuralModel` carries Everitt's Definitions 1 to 5 with
decision and utility vertices. The sentence above scopes to this section, which
is why the boundary it names still holds here.

## 4. Binary collision witness

MAIS issue [#6](https://github.com/lionellevine/MAIS/issues/6) supplies the construction, not the primitives: `C={X,Y}`,
`O=∅`, `Z={X,Y}`, `λ=1/10`, and
`g(x,y)=1/2-1_{(x,y)=(1,1)}`. The edgeless, `X→Y`, and `Y→X` tables are stored
as full Bernoulli simplexes over `Fin 2`.

The machine-checked identity

`Δ_M(σ) = 1/2 - P_M(X=1,Y=1;σ)`

is a corollary of the general `jointProb_sum`, not the normalization theorem
itself. The three collision theorems quantify over every function-valued local
profile; `Δmix_congr` lifts them to every ambient weight function over the value
field a statement picks, and hence to every `ProbMixture`. All three models inhabit the categorical
`MarginClass` at the same `λ`, and `margin_class_not_identifiable` records
distinct graphs with equal A2 transforms.
`margin_class_not_identifiable_shared_optimal` then applies the generic bridge
to exhibit one policy family with zero regret in both distinct models. This is
**SOURCE-EXACT** for the issue's rational construction and **RELATED** to the
peer-reviewed RE24 identifiability theorems.

The positive-dimensional `arrowXYb` family, `behaviorEq_has_teeth`, sign-changing
transform values, normalized utility witness, and `mm2_shape` are **ATLAS**
non-vacuity or strengthening lemmas derived from that construction.

Because `O=∅`, this witness exercises the one-member masked family. It does not
test the failure mode where an unmasked component is non-injective but a richer
masked family is injective.

## 5. Nearby formal library: CausalForge

CausalForge/Causalean was searched at commit
`0bc3544c2ace84c23806e1b20767a18bb765f244` and recorded under `NC-009`.
It supplies a broad measure-theoretic SCM/SWIG layer, hard `fixSet`
interventions, kernels, do-calculus, and identification. CausalSmith also
contains observed-law statistical policy, welfare-regret, margin/overlap, and
minimax developments. Those are genuine nearby work, but they do not supply the
combined RE24/A2 layer searched here: arbitrary local state-map mixtures, CID
utility and policy-oracle behavior, and the A2 identified-set/error/radius
packaging over causal world models. Its Lean 4.33 pin matched the atlas's own from
2026-08-31, so the toolchain objection recorded here is closed; it remains a
reproduction/adapter candidate rather than a dependency of this increment,
because the carrier mismatch and its vendored dependencies are what actually
block a `require`.

## 6. Residual scope deltas

These are intentional and must not be erased by statement-match wording:

1. The decision layer assumes the unmediated case by construction; it is not a
   CID and has no decision or utility graph vertices.
2. A2's six margins and `Δmask` packaging are composites, not definitions from
   RE24 or Uhler et al.
3. `InIdentifiedSet`, `modelError`, and `IsRadius` are not RE24 Theorem 2 or its
   `γ(δ)` conclusion.
4. Nothing in this layer is stated over a parameter chart or an almost-every
   quantifier, and no RE24 Theorem-1/2 proof is present anywhere.
5. Equal transforms imply shared optimal behavior in Lean; the converse oracle
   reconstruction proposition remains sourced rather than machine-checked.

**One delta was listed here and is closed.** `Causal.Decision` was instantiated
at `ℚ` rather than the printed real case, and this file recorded the closure as
gated on `preferredDecision`'s `decide (0 < ·)` needing a decidable order "that a
general ordered field does not supply." That obstruction does not exist:
Mathlib's `LinearOrder` bundles `decidableLT` as a class field, so the guard
elaborates generically. The field-parametrization work closed it: the whole
decision layer, `InIdentifiedSet`'s `δ` included, now carries `𝕜` like
`Causal.Model` and `Causal.MarginClass`, and the printed real case is an
instance. The obstruction recorded above is retracted, and is left visible here
rather than deleted so the correction is auditable.
