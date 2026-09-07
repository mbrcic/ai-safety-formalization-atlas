# MAIS-O7 and MAIS-O77 verification record

This note records exactly what the Lean development checks, what it reuses from
MAIS-O70, and what remains open. It is not a referee report and does not record
MAIS acceptance. A proposed MAIS countersignature belongs to the later review
record, not here.

## Immutable source receipts

The printed problem source is MAIS commit
`9dd29f8bf5ccd1e7701e300039b09ed4096b6516`. The candidate notes address commit
`43016a3e5c94edfca55ba49bd3e16770f7ac5dae`. Comparing the problem files at
those revisions found only status-link changes; the mathematical statements
used here are unchanged.

| artifact | SHA-256 |
|---|---|
| pinned `agendas/A7/MAIS-A7.tex` | `c645a51bf02b16077d14adce56e1c55a2fcb66f5004bbd0aec57fb01a2d54b52` |
| pinned `open-problems/MAIS-O7.md` | `4b1add32acbf7d0e462e8b9d39144e5588a38cf446a1d57f7495ba183aaa3d8c` |
| pinned `open-problems/MAIS-O77.md` | `07912e8c267f9b7866c12fe09a1277d5c880c0c9e60672c803be83a3b159a043` |
| issue #5 body | `edbaf2f2435c8854ce681a19cc2f5da10474e944fc2c9254624f0db50b5061fa` |
| issue #5 O7 PDF | `907ce2d0a5a11182995c4679acb6812109ecdb90e66da765a6f9037e5e9b59a8` |
| issue #12 body | `c0a2c0a8cb66858ca0160765b1465fb1f55bdd9be47edf79283d43e82af6c984` |
| issue #12 O77 PDF | `5a4a919ffb30a110cd377e4df5c0a829c36ee11696bb8dc4211c6afde149a998` |

Issue bodies are editable. The PDF hashes identify the mathematical candidate
artifacts read for this work.

## Normalization boundary

MAIS-A7 defines the local invariant primarily through the leading pole of a
signed local zeta integral and describes the strict two-sided band volume by an
order comparison. The atlas proves the operational volume-order statement:
two-sided upper and lower constant bounds with the stated power and logarithmic
multiplicity. It does **not** prove the meromorphic continuation, and it assumes
rather than proves the passage from the volume order to the zeta-pole order.

That substitution is carried in Lean, not only in this document. It is
`AISafetyAtlas.Conjectures.MAIS.A7ZetaVolumeBridge`, frozen as
`a7ZetaVolumeBridge_iff` and registered as the frontier `A7-ZETA-BRIDGE`, owed
to the source and on hold. `AISafetyAtlas/Conjectures/MAIS/A7Zeta.lean` states
what it buys: `o7_zeta_refutation` gives MAIS-O7's two rung coefficients and the
failure of the printed increase in A7's own definition, and
`o77_all_saddles_zeta_pair_one` gives MAIS-O77(b) at every point of every
nonterminal critical set in the same, both taking the bridge in their binders.
It is a separate assumption from `O70-ZETA-BRIDGE` and strictly stronger: that
one consumes `HasExactLocalPair` on a germ that vanishes, this one consumes
`HasLocalVolumeOrder` on a germ centred at an arbitrary point, which at a
nonterminal rung is a germ the loss alone does not determine. Nothing unconditional
changed, and the ledger rows are still graded on the volume form.

`HasO7PairAt` and `HasO77TwoSidedPairAt` retain both conventions that are
actually checked:

- `HasLocalVolumeOrder`, using weak sublevels;
- `HasStrictLocalVolumeOrder`, using the strict bands printed by A7.

`hasStrictLocalVolumeOrder_of_hasLocalVolumeOrder` proves the bridge by the
source-neutral squeeze
`{K ≤ ε/2} ⊆ {K < ε} ⊆ {K ≤ ε}`. It assumes no null-boundary or regular-value
claim.

## O7: unconditional negative resolution

`AISafetyAtlas.Conjectures.MAIS.isO7Counterexample` proves the complete scalar
counterexample for every `s > 0` at `M=N=r=1`, `H=2`. Its conclusion includes:

- the whole rank-zero rung is `{0}`;
- the terminal exact-factorization rung is inhabited;
- the pair is `(1,1)` at every rank-zero point and `(1/2,1)` at every terminal
  point;
- the sets of certified exponents are exactly `{1}` and `{1/2}`;
- both infima are attained;
- the printed strict staircase inequality fails.

The origin calculation is frontier-free. It reduces the squared two-vector
dot-product germ to an explicit radial determinant integral and proves its
two-sided bounds. The terminal calculation uses the existing reduced-rank
chart and orbit transports. No eigenvalue law, analytic Morse lemma, zeta-pole
bridge, or hypothesis already containing the candidate answer occurs.

Thus MAIS-O7 is formally refuted at the operational two-sided volume-order
reading. The result does not prove the wider all-saddle statement in O77(b).

## O77(a): reused conditional order theorem and unconditional arithmetic

The issue #12 candidate explicitly says part (a) overlaps the MAIS-O70 solution
in issue #3. `o77Pair M N H r a b` is therefore definitionally
`o70Pair N M H r a b`; no second multiplication-slice proof is presented as
new work.

`isO77SourceFiberVolumeOrderTable_o77Pair` checks the submitted table at the
exact A7 target class. It is conditional on one proposition:

```lean
EigenvalueLawStatement
```

That proposition is the already registered O70-EIGEN-LAW frontier: the real
Wishart eigenvalue density and Jacobian cited by the O70 candidate to Muirhead
after James. It supplies no O77 table entry, rank dependence, or local-pair
conclusion. The stronger target-uniform theorem
`isO77FiberVolumeOrderTable_o77Pair` uses the same single hypothesis and does
not require distinct singular values.

The following parts are unconditional:

- the residual-shape and regular-coordinate identities;
- the table's attained minimum at the printed Aoyagi--Watanabe value;
- the predicate describing all minimum-coefficient rank strata;
- the candidate PDF's extra statement that the largest multiplicity among
  minimum-coefficient strata is the printed global multiplicity.

The last item is not a finite experiment. The proof injects every residual
minimizer of a tied stratum into the minimizers at `(r,r)` and separately proves
that the uniform stratum's parity-sensitive multiplicity equals
`awMultiplicity`.

The third item is arithmetic: `o77_aw_value_strata_correct` holds by `rfl`,
because `o77Minimizers` is *defined* as the admissible strata where the table
meets `awLambda`. That checks a candidate described its own set correctly and
says nothing about germs. Print's clause is about germs — `MAIS-O77.md` fixes
"the minimal stratum in part (a)" as the stratum on which `λ` attains the
Aoyagi–Watanabe value, and `λ` there is the realized local invariant.
`isO77MinimizerCharacterization_o77Minimizers` is that reading: a stratum lies
in the set exactly when the two-sided pair actually realized at its points has
the least coefficient realized anywhere on the same fiber. It is conditional on
`EigenvalueLawStatement` and on nothing else — the fiber table supplies a
realized pair at every factorization, and `volumeOrder_unique` pins its value,
so unlike the O70 counterpart no existence frontier enters. `zeroFrame` and the
`Set.univ` refutation in `AISafetyAtlas/Examples/Conjectures/MAIS/O77.lean` show
the predicate has an inhabited hypothesis and is not satisfied by every set.

This is a conditional formal verification of O77(a) at volume order, not an
unconditional verification of the zeta-pole local pair. Reading the table as
A7's own zeta pair adds `A7-ZETA-BRIDGE` on top, which is what
`o77_fiber_zeta_pair` carries; it is the one clause in this document that needs
both frontiers.

## O77(b): faithful statement, unconditionally verified

`O77SpectralFrame` stores only the target data printed by A7: positive strictly
decreasing singular values, orthonormal mode families, their matrix expansion,
and the target rank. It stores no criticality, Hessian, coordinate splitting,
or volume theorem.

`IsO77SaddleRungPoint` then states the printed membership conditions for
`C_k`: the product is the ordered top-`k` truncation and every discarded mode
is annihilated by `A` and `Bᵀ`. `O77AllSaddlesHavePairOne` asks for `(1,1)` at
every point of every nonterminal rung. A worked scalar frame inhabits the
`r=1`, `H=2`, `k=0` rung, and O7 independently proves that specialization.

**Closed 2026-09-05.** `o77AllSaddlesHavePairOne_holds` in
`Conjectures/MAIS/O77Chart.lean` inhabits `O77AllSaddlesHavePairOne` at print's
own quantifiers — every input and output dimension, every rank `r < H`, every
certified frame, every nonterminal rung `k`, every point of it — with axioms
`propext`, `Classical.choice` and `Quot.sound` and nothing else.

**Everything from here to the end of this section is the record of how that
happened, and it is written as it accrued.** Several entries below state that
something is owed, unavailable, or unsatisfiable as posed. Those were true when
written and each is corrected where it stands rather than deleted, because the
corrections are the substance: four of them are defects this repository shipped,
each compiling and axiom-clean while being about something weaker than print.
Read the section as a history, not as a status; the status is the paragraph
above.

All three obligations named in the plan are now discharged, though the third is
discharged by being replaced rather than by being met.

**The indefinite band estimate is proved.** `hasLocalVolumeOrder_modelBandGerm_of_three_le`
gives local pair `(1,1)` for the germ `|‖u‖² − ‖v‖²|` at every signature with both
blocks nonempty and ambient dimension at least three, unconditionally.
`hasLocalVolumeOrder_abs_of_diagonal` carries that to any germ presented as the
absolute value of a `±1`-weighted sum of squares in some linear coordinates,
which is the form Sylvester's law of inertia delivers. The dimension hypothesis
is not an artefact: `bandLaplace_one_one_ge` shows that at signature `(1,1)` the
transform is at least a constant times `log T / T`, which no bound of the form
`C / T` can dominate, so the pair `(1,1)` is genuinely unavailable there.

**The Hessian block is settled.** `det_hessianBlock_ne_zero` proves the
`2H`-dimensional block nonsingular under the printed spectral condition, going
through the invertible off-diagonal corner because at a rung point both diagonal
blocks are singular and neither Schur complement applies. `hessianBlock_quadForm`
identifies the form as `xᵀPx + yᵀRy − 2s⟨x,y⟩`, and
`hessianBlock_indefinite_at_zero` exhibits both signs at the rank-zero rung.

**What the Morse step actually owes.** Not a parameterized analytic Morse
splitting: three results below fix the obligation more narrowly than that.

`frobeniusSq_rung_variation` expands the loss **exactly**: along the variation
`dA = x vᵀ`, `dB = u yᵀ` at a rung point, the polynomial terminates at

    `L' − L = ‖Bx‖² + ‖Aᵀy‖² − 2s⟨y,x⟩ + ⟨y,x⟩²`,

so the germ supplies its own Hadamard factorisation `G(z) = ½ zᵀ H(z) z` with
`H(z)` the block matrix of §7.2 carrying coupling `s − ⟨x,y⟩/2`. No remainder
estimate and no formal power series are involved; the identity is an algebraic
one. `congruence_of_solution` then converts any `X` solving
`2X + X K⁻¹ X = H(z) − K` into the congruence `(1 + K⁻¹X)ᵀ K (1 + K⁻¹X) = H(z)`,
which is the coordinate change itself.

`quadSolve` solves that equation. In any real normed algebra,
`eventually_quadMap_quadSolve` gives `2X + X C X = D` for every `D` near the
origin, `quadSolve_zero` fixes the rung point, `contDiffAt_quadSolve` makes the
solution `C^n`, and `exists_lipschitzOnWith_quadSolve` extracts the Lipschitz
bound. The worked model in `Examples/SingularLearning/QuadraticSolve.lean`
exhibits the closed form `√(1 + d) − 1` on `ℝ`, so the solution operator is not a
name for an empty promise.

`hasLocalVolumeOrder_comp_of_lipschitz` is why `C^n` suffices. Reading the proof
of `hasLocalVolumeOrder_comp_of_analytic`, analyticity enters in exactly three
places — a Lipschitz ball for `φ` at `w`, one for `ψ` at `φ w`, and continuity of
`φ` at `w` — and nothing is ever differentiated. The Lipschitz form states Lemma
6.4(i) at that strength; the analytic statement is unchanged and is now a
two-line corollary of it.

The Lipschitz form is a genuine strengthening: it states the lemma at the
hypotheses the proof consumes. It is **not** owed to any absence in Mathlib.
Mathlib has the Banach-space analytic inverse function theorem —
`OpenPartialHomeomorph.analyticAt_symm'` in
`Mathlib/Analysis/Calculus/FDeriv/Analytic.lean`, filed under `FDeriv/` rather
than under `InverseFunctionTheorem/` — and the vendored Tau Ceti
`analyticAt_sqrtNearOne` is built on precisely that lemma.

Nothing downstream weakens: `hasLocalVolumeOrder_comp_of_lipschitz` is the
right statement and is what a `C^n` caller needs. What matters is that
`quadSolve` could be upgraded from `ContDiffAt` to `AnalyticAt`, and that the
line "Mathlib does not have this" must not be repeated.

**What remains, stated exactly.** The shape of this changed on 2026-09-05 and the
entry is rewritten rather than amended, because the obstacle it named is gone.

`isO77RungTangent_iff_null` proves that the null space of the Hessian at a rung
point is **exactly** `IsO77RungTangent`, the linearization of the three conditions
cutting out `C_k`. The proof is where the printed strict decrease of the singular
values finally does work: contracting the two null-space equations against a
discarded mode makes `X v_j` an eigenvector of `A Aᵀ Bᵀ B` for `s_j²`, and
`(B A)ᵀ (B A)` — the truncation's Gram matrix — has no such eigenvalue.

**That is not the same as `C_k` being a Morse–Bott critical manifold, and an
earlier version of this entry said it was.** The argument that looked conclusive
was: the loss sees `(A, B)` only through `B * A`, and `B * A` is frozen on `C_k`,
so the null directions are free. Both halves are true and the conclusion does not
follow, because a direction in the *linearization* need not be tangent to any curve
*in* `C_k`. Where `C_k` is singular, the linearization is strictly larger.

`Examples.Conjectures.MAIS.loss_quartic_on_degenerateNull` settles it by exhibiting
the gap rather than arguing about it. At the rank-zero rung of `wideFrame` both
factors vanish, so `IsO77RungTangent` is the full annihilator of the discarded mode
and contains `X = e₀e₁ᵀ`, `Y = e₁e₀ᵀ`. That pair is in the Hessian's null space by
the theorem above. But `Y * X` is the second diagonal cell, which the target does
not see, so the loss along `(tX, tY)` is exactly `t⁴` — proved, not estimated. A
Morse–Bott normal form at that point would make it identically zero, so none
exists.

The consequence for the plan is item 3 below, which asked for a Morse-Bott normal
form at *every* rung point. That obligation is not merely open; it is unsatisfiable
as stated.

**What is refuted is Morse-Bott, not every normal form, and the distinction is the
whole content of the witness.** Morse-Bott asserts that the critical set is a
manifold, that the Hessian is nondegenerate transverse to it, and that the loss is
*constant* along the null directions — so that those directions are free and
`hasLocalVolumeOrder_freeCoords` discharges them. It is the last clause that
`t ^ 4 != 0` refutes.

A *generalized* splitting — Gromoll-Meyer, `L - L(w0) = Q(eta) + g(zeta)` with `Q`
the nondegenerate transverse form and `g` a genuinely degenerate germ on the null
space — is untouched. The witness is not a counterexample to it; it is an instance
of it, with `g` the quartic. The generalized splitting, not a Morse-Bott normal
form, is the shape the answer takes.

So three routes remain, not two: restrict to rung points where `C_k` is smooth of
the linearized dimension and treat the singular ones separately; produce a
generalized splitting with a degenerate `g`; or reach the pair with no normal form
at all.

**The candidate's own argument is the generalized splitting, and is not touched by
the witness.** This was checked against the pinned artifact rather than recalled:
`MAIS-O77-candidate-solution.pdf`, sha256
`5a4a919ffb30a110cd377e4df5c0a829c36ee11696bb8dc4211c6afde149a998`, which is the
hash already recorded in the receipts above. Its equation (9) reads

    L - L(w) = Q_alpha(xi) + g(zeta),    g(0) = 0

with `g(0) = 0` and nothing more asked of `g`. That is Gromoll-Meyer, not
Morse-Bott, and the quartic the witness exhibits is an admissible `g`. The
candidate's Lemma 2 is then exactly the level-uniform band statement: for `Q`
nondegenerate indefinite in `n >= 3` variables and `g` merely continuous with
`g(0) = 0`, `vol{|Q(xi) + g(zeta)| < eps} = Theta(eps)`. Its step establishing a
nondegenerate indefinite `2H`-dimensional Hessian block also holds at the witness
point, where `2H = 4` and the block is `-2 s <y, x>`.

**The deviation was ours.** `reviews/mais-issues-5-12/01-formalization-plan.md`
recorded the obligation as "every O77 saddle has the required Morse normal form",
and the route built from it discharged the degenerate directions with
`hasLocalVolumeOrder_freeCoords`, which requires the loss to be constant along
them. The candidate never claimed that. A formalization that strengthens the
argument it is checking is not a faithful transcription of it, and the
strengthening here happened to be false — which is the only reason it was caught.
The obligation is restated in the candidate's own terms below. Pair `(1,1)` is not refuted at
the witness point, and numerically it holds there. Monte-Carlo sublevel volumes at
`s = 1`, `delta = 0.5`, four million samples per point, over `eps` from `1e-2` to
`1e-5`, give successive log-log slopes 0.975, 0.991, 1.004, 0.996, 1.001, 1.036 —
`lambda = 1` with no systematic drift, so `m = 1` as well. The mechanism is visible
in the algebra: the Hessian at that point is a nondegenerate indefinite form in four
of the eight variables, and the four it misses carry only a quartic. A level-uniform
band estimate — the volume of `|Q - c| <= eps` bounded by a constant times `eps`
with the constant independent of the level `c` — would give `(1,1)` with no normal
form anywhere in the argument, because the shell estimate behind it needs one block
of dimension at least two and nothing else.

That is the route now being tried, and it should be understood as a necessary
primitive rather than a proof: it removes the need for a normal form on the fibre
but does not by itself control the cubic and quartic cross terms in the general
case. Numerics are evidence about the answer, never about the proof.

The two surviving routes meet here, which is the reason to build the primitive
before choosing between them. Given a generalized splitting `Q(eta) + g(zeta)` with
`Q` indefinite and nondegenerate, the level-uniform band is exactly what makes `g`
irrelevant to the pair: for each fixed `zeta` the `eta`-slice is the band of `Q`
about the level `-g(zeta)`, and a bound uniform in the level integrates to `eps`
whatever `g` does. That is why `lambda = 1` survives at a point where the null
directions are not free, and it is why the primitive is worth proving before either
normal form is attempted.

Three things were owed at that point, and they are smaller and better separated
than the splitting was. All three are settled.

1. *Transverse indefiniteness.* Discharged by
   `o77HessianForm_indefinite_of_rung`, unconditionally, at every point of every
   nonterminal rung. The argument is the candidate's own, transcribed rather
   than invented. It runs on the
   two-parameter block `Ẋ = x v_αᵀ`, `Ẏ = u_α yᵀ`, where the earlier witness tied
   both factors to one vector `c ∈ ker B ∩ ker Aᵀ` and so said nothing at the
   generic rung. On the wider block the Hessian is
   `xᵀ(BᵀB)x + yᵀ(AAᵀ)y − 2 s_α ⟨x, y⟩`, positive at `(z, −z)` for every nonzero
   `z`, and negative at `(z, t z)` for small `t > 0` when `B z = 0` — or at
   `(t z, z)` when `Aᵀ z = 0`. One of those kernels is nonzero, because
   `rank (B * A) < H` by `rank_truncation_le` and `r < H`, and Sylvester's
   inequality then forbids both factors from being injective. The earlier
   theorem `o77HessianForm_indefinite` is kept: it is the one statement
   exhibiting both signs on a single variation.
2. *The transverse dimension is at least three*, which is what the band theorem
   asks and what separates pair `(1, 1)` from the logarithmic `(1, 2)` of
   signature `(1, 1)`. **Discharged 2026-09-05**, and by print's own line rather
   than by the dimension count against `dim C_k` that this entry proposed. The
   splitting runs on the `2H` block, so the dimension the band theorem sees is
   `2H`, and `o77_variation_block_dim_ge` gives `2 <= H` and `4 <= 2H` from
   `k < r < H` alone. The numerical observation was consistent with this but was
   measuring the wrong quantity: it measured the rank of the full Hessian, which
   item 3's correction below shows is not what equation (9) is about.
3. *A Morse–Bott normal form — and it does not exist at every rung point.*
   **Withdrawn as an obligation 2026-09-05**, in favour of the generalized
   splitting named in its own last sentence. `exists_gromoll_meyer_splitting`
   builds that splitting and `exists_o77_chart` instantiates it at the O77 loss,
   so nothing here needs a Morse-Bott normal form and the unsatisfiability
   recorded below costs nothing. The rest of this item stands as written.
   Knowing the Hessian's null space is not yet knowing that the loss germ is
   equivalent to its Hessian germ; the cubic and quartic terms of the exact
   expansion still have to be absorbed. The parameterized Morse lemma along `C_k`
   is what would absorb them, and the vendored
   `TauCeti.exists_congruence_of_symmetric_family` is already parameterized in a
   smooth family, which is the engine any such normal form runs on. But
   `loss_quartic_on_degenerateNull` shows a *Morse-Bott* normal form cannot exist
   at rung points where `C_k` is singular, so this item cannot be completed as
   written. It survives in two forms, neither of which is the printed obligation:
   as a restricted statement under a smoothness hypothesis on the rung set that
   the source does not print — which §10 forbids proposing as O77(b) — or as a
   generalized splitting with a degenerate germ on the null space, which the
   witness does not obstruct and which the same TauCeti engine would drive.

A comparability shortcut does not exist here, and the reason is worth recording:
`|Q + higher order|` is not bounded below by a multiple of `|Q|` near the null
cone of `Q`, where `Q` vanishes and the higher-order terms need not, so the
existing `hasLocalVolumeOrder_of_comparable` cannot substitute for the coordinate
change. That is precisely why the printed argument uses a splitting. The one case
it does cover — both diagonal blocks vanishing — is closed separately by
`hasLocalVolumeOrder_hyperbolicGerm`.

**Two narrowings are available and both are refused.** Proving the pair `(1,1)`
only on the `2H`-dimensional slice would be a statement about a restriction of
the loss that print does not make, and would read as O77(b) to anyone not
reading the binders. Assuming the splitting as a hypothesis would open a
frontier row owed to `atlas` — the expensive kind, of our own making — for a
proposition that is hard *and* broadly reusable, which is the shape that belongs
upstream rather than on this repository's frontier register. Neither is taken,
and no narrower theorem is proposed in their place.

Part (b) is closed, and closing it was a research step rather than an assembly
step. It rests on two results absent from the Mathlib revision pinned here and
built in this tree — `exists_gromoll_meyer_splitting` for equation (9) and
`hasLocalVolumeOrder_abs_matrixQuadForm_add_germ` for Lemma 2 (the search is
`NC-012`) — together with the loss's first two Frechet derivatives. Neither
narrowing above is used: the theorem is stated over the whole parameter space,
and no proposition is assumed.

The atlas still does not call issue #12's complete-solution claim verified,
because the claim covers both clauses and part (a) remains conditional on
`EigenvalueLawStatement`. Part (b) alone is unconditional.

## Candidate step to obligation, for part (b)

Written 2026-09-05 after the drift recorded above. Every row quotes the pinned
artifact `MAIS-O77-candidate-solution.pdf`, sha256
`5a4a919ffb30a110cd377e4df5c0a829c36ee11696bb8dc4211c6afde149a998`, and not any
plan that cites it. The point of the table is that a deviation becomes a diff.

| # | candidate's step, as printed | atlas obligation | status |
|---|---|---|---|
| 0 | "Fix `w = (A,B)` in `C_k` with `k < r`" — membership in the nonterminal critical set | `isO77SaddleRungPoint_iff_critical`: the atlas predicate is equivalent to `k < r`, `BA = T_k`, and the two normal equations | proved |
| 1 | `A v_alpha = 0`, `B^T u_alpha = 0` at a rung; the `2H` block `Adot = x v_alpha^T`, `Bdot = u_alpha y^T` | `isO77SaddleRungPoint_of_critical` derives the two clauses; `o77BlockMap`, `o77BlockMap_injective`, `finrank_range_o77BlockMap` give the block | proved |
| 2 | `K_alpha = [[B^T B, -s_alpha I],[-s_alpha I, A A^T]]`, `det K_alpha = (-1)^H det(s_alpha^2 I - QP)`, nonsingular because the nonzero eigenvalues of `QP` are those of `(BA)^T(BA)`, namely `s_1^2..s_k^2`, and `alpha > k` with distinct singular values | `det_o77SaddleBlock_ne_zero`, over `det_hessianBlock_ne_zero` (the determinant identity) and `o77_saddle_spectral_det_ne_zero` / `truncation_gram_no_eigenvector` (the eigenvalue count) | proved |
| 3 | indefinite: positive at `(z,-z)`; at least one of `P = B^T B`, `Q = A A^T` singular, else `rank(BA) = H` against `rank(BA) = k < r < H`; for `z` in `ker P` the value at `(z, tz)` is `t^2 z^T Q z - 2 s_alpha t |z|^2 < 0` for small `t > 0` | `o77HessianForm_indefinite_of_rung`, over `o77HessianForm_blockVariation`, `hessianBlock_quadForm_indefinite`, `exists_mem_ker_gram`, `rank_truncation_le` | proved |
| 4 | eq (9): analytic Morse splitting gives `L - L(w) = Q_alpha(xi) + g(zeta)`, `g(0) = 0`, with `Q_alpha` the `2H` block | `exists_gromoll_meyer_splitting`, over `exists_critical_fiber` (the fibre, by the inverse function theorem) and `exists_partial_congruence_normal_form_of_nhds` (the congruence, localized); the block is `frobeniusSq_rung_blockVariation` + `o77BlockVariation_injective` + `o77_variation_block_dim_ge`, and `Kalpha`'s nondegeneracy is `det_o77SaddleBlock_ne_zero`; the instantiation is `exists_o77_chart` + `exists_o77_block_matrix` | proved |
| 5 | Lemma 2: for `Q` nondegenerate indefinite in `n >= 3` variables and `g` continuous with `g(0) = 0`, `vol{|Q(xi) + g(zeta)| < eps} = Theta(eps)` | `hasLocalVolumeOrder_abs_matrixQuadForm_add_germ`, over `hasLocalVolumeOrder_freeBlockGerm` (which is `exists_freeBlockBand_bounds` for the `zeta`-box and `shiftedBandVolume_le` / `_ge` for the level-uniform band) transported along `exists_model_congruence`, the diagonalization Sylvester's law supplies | proved |
| 6 | assembly: Lemma 2 applied to eq (9) at every rung, giving `(1,1)` | `o77AllSaddlesHavePairOne_holds`, over `hasLocalVolumeOrder_centeredBandGerm_of_indefinite_block` (rows 4 and 5 joined away from O77), `exists_o77_chart` and `exists_o77_block_matrix` (the O77 instantiation), `fderiv_o77_chart_eq_zero` (criticality through the chart) and `contDiff_o77LossCoords` | proved |

**Step 3 was the correction that mattered to the plan, and is now closed.** This
record had said that transverse indefiniteness at a general rung "needs a
variational argument that is not here". The candidate supplied one, five lines,
unconditional, using only that `P` and `Q` are positive semidefinite, that
`s_alpha > 0`, and Sylvester's rank inequality, which this repository already
proved. It is transcribed as `o77HessianForm_indefinite_of_rung`, with the
`2H`-block computation in `o77HessianForm_blockVariation`, the algebra in
`SingularLearning.hessianBlock_quadForm_indefinite` and
`SingularLearning.exists_mem_ker_gram`, and the rank input in
`rank_truncation_le`. Non-vacuity is
`Examples.Conjectures.MAIS.o77_indefinite_of_rung_wideFrame`.

That the atlas theorem was strictly weaker than the printed argument is the same
defect as the drift above, pointing the other way: a verification whose theorem
is weaker than the argument it checks has not checked it.

**The setup line was assumed, and is now derived.** Print's step 1 reads "the
defining criticality conditions give `A v_a = 0`, `B^T u_a = 0`", deriving the
two annihilation clauses from membership in `C_k`. `IsO77SaddleRungPoint` listed
them among its conjuncts, and only the forward implication was proved. That is a
scope question in the dangerous direction: had the clauses been strictly stronger
than criticality-plus-membership, every theorem quantified over the predicate
would have ranged over a proper subset of print's `C_k`, and no check in this
repository would have noticed — the statements compile, are axiom-clean, and read
correctly. `isO77SaddleRungPoint_iff_critical` settles it in both directions, so
the all-saddle quantifier demonstrably ranges over print's set and no smaller one.

**Print's one forbidden substitution is not made.** The candidate's scope
section says part (b) "uses the problem's two-sided band invariant. It must not
be replaced by the one-sided Aoyagi-Watanabe increments associated with
lower-rank model minima." That substitution is available in this tree —
`AoyagiWatanabe.lean` is present and the one-sided machinery it feeds is what
several O70 results use — so the caveat is a live one rather than a formality.
The grading predicate `O77AllSaddlesHavePairOne` is stated through
`HasO77TwoSidedPairAt`, which is `HasLocalVolumeOrder` and
`HasStrictLocalVolumeOrder` of `centeredBandGerm L w = |L - L(w)|`. That germ is
the absolute value of a signed difference, so its sublevel sets are two-sided
bands and not sublevel sets of `L` itself; at a saddle the two differ, which is
the whole reason print insists. The other two caveats match as well: the frame
carries `singularValue_strict`, so the distinct-singular-value setting print
inherits from A7 is the one formalized, and print's own remark that a positive
scalar factor changes neither the coefficient nor the multiplicity is not relied
on, because `rrrLoss` carries print's `1/2` exactly.

**Step 3's transcription is faithful down to the witnesses.** Print exhibits the
positive direction at `(z, -z)` and the negative one at `(z, tz)` "for all
sufficiently small `t > 0`". `hessianBlock_quadForm_indefinite` uses `(z, -z)`
for the positive direction, the same vector, and for the negative one names an
explicit `t = s_a n / (q + 1)` rather than quantifying over small `t` — a
constructive strengthening, not a substitution. Print's second branch, "if
instead `z` is in `ker Q`, use `(tz, z)`", is the symmetric case and is proved
too. The normalisation is print's as well: `rrrLoss` carries the `1/2` of
`L = (1/2)||BA - Phi||^2`, and `rrrLoss_rung_blockVariation` states the block
identity at that normalisation, which is what makes `Kalpha` the Hessian of `L`
rather than of `2L`.

**Step 2 was recorded as proved here, and was proved only halfway.** The entry
cited `det_hessianBlock_ne_zero`, which is the block determinant identity: it
concludes `det K_alpha != 0` **given** `det (P R - s_alpha^2 I) != 0`. That
hypothesis is print's eigenvalue sentence, and nothing in the tree discharged it
at a rung point — the only application anywhere was the module's own example at
the rank-zero rung, where both diagonal blocks vanish and the condition is
trivial. A general matrix lemma with its hypothesis assumed is not a
verification of a step that derives that hypothesis.

**And the fix was half of one, which a later audit found.** Deriving the
hypothesis fixed the theorem. It did not move the witnesses: both O77 frames in
the tree had `r = 1`, and `IsO77SaddleRungPoint` requires `k < r`, so `k = 0` was
the only rung either of them had — the rank-zero rung, where `truncation 0 = 0`
and every witness took `A = B = 0`. There both Gram blocks vanish, so the derived
statement reduces to `det (-s_alpha^2 I) != 0` and the eigenvalue exclusion is
about the spectrum of the zero operator — sound, but not an exercise of the
spectral step. `rank2Frame` and `rungPoint_rank2` supply a point of `C_1` on a
rank-two diagonal target, where the truncation and both Gram blocks are nonzero,
so the step runs in full: `rank2_nondegenerate`,
`rank2_gram_blocks_ne_zero` and `rank2_truncation_gram_ne_zero` proving the
configuration is not the degenerate one, and `pair_rank2` giving the pair there.
It goes through unchanged.

It is now derived. `truncation_gram_no_eigenvector` shows `s_alpha^2` is not an
eigenvalue of the truncation's Gram operator, using only orthonormality of the
right modes and the strict decrease of the singular values — no spectral
theorem, and no appeal to an eigenvalue list the tree cannot state.
`o77_saddle_spectral_det_ne_zero` carries that across the `U V` / `V U` exchange
print also uses, and `det_o77SaddleBlock_ne_zero` is print's conclusion with
nothing assumed. The defect shape this guards against is a statement that
compiles, is axiom-clean, and is about a weaker claim than the one being checked.

**Step 4 is correct.** Equation (9) calls `Q_alpha` nondegenerate indefinite *in
`2H` variables*, while the Hessian's rank at a rung point is much larger —
measured at twelve rung points across six shapes, `rank` was 15 against
`2H = 6`, 20 against 8, 22 against 8, 30 against 10, 25 against 8 and 16 against
6, with signatures `(13,2)`, `(12,2)`, `(17,3)`, `(16,3)`, `(16,6)`, `(27,3)`,
`(26,3)`, `(17,8)`, `(10,6)`. The measurements are recorded because they are
useful, not because they are an objection.

Reading that gap as a defect would require the splitting to run on the
**maximal** nondegenerate part of the Hessian, so that `Q_alpha` would have to
have rank equal to the Hessian's. A Gromoll-Meyer splitting carries no such
requirement: it splits along **any** subspace `W` on which the Hessian's
`W`-block is nondegenerate, leaving an arbitrary germ on a complement of `W`.
Print names that subspace explicitly one paragraph earlier — the `2H`-dimensional
variation block `Adot = x v_alpha^T`, `Bdot = u_alpha y^T` — and proves exactly
what the splitting needs of it, that `Kalpha` is nonsingular. So `Q_alpha`
genuinely is a nondegenerate form in `2H` variables, and equation (9) is correct
as printed. The rank of the full Hessian is not what the step is about.

The atlas confirms print's description of that block, and sharpens it. On the
block the loss variation is not merely quadratic to leading order: it is the
`Kalpha` form plus a single quartic term and nothing else,

    L(A + x v_alpha^T, B + u_alpha y^T) - L(A, B)
      = x^T (B^T B) x + y^T (A A^T) y - 2 s_alpha (x . y) + (x . y)^2,

every cubic contribution cancelling because `B^T u_alpha = 0` and `A v_alpha = 0`.
That is `frobeniusSq_rung_blockVariation`, and it checks print's sentence "the
Hessian of `L` restricted to this block is `Kalpha`" against the loss itself
rather than against the atlas's hand-written `o77HessianForm`. The block is
`2H`-dimensional in the literal sense as well — `o77BlockVariation_injective` —
and `2H >= 4 >= 3` is `o77_variation_block_dim_ge`, which is print's own line
"Because `k < r < H`, one has `H >= 2` and `2H >= 4`".

Step 4 is therefore graded **correct as printed**. The splitting lemma equation
(9) invokes is not in Mathlib, and was not in this tree when the paragraph above
was first written; it is now `exists_gromoll_meyer_splitting`, built from
`exists_critical_fiber` (the fibre, by the inverse function theorem) and
`exists_partial_congruence_normal_form_of_nhds` (the congruence, localized to a
neighbourhood, which is all an implicit function theorem can supply). What step
4 still owed after that was not the lemma but its **instantiation**: the O77
loss's own first and second Frechet derivatives, and the chart bookkeeping
between the matrix-pair parameter space and the product the splitting is stated
on. Both landed the same day. `fderiv_pairLoss_eq_zero_of` and
`fderiv_fderiv_pairLoss_apply` are the derivatives, and
`fderiv_fderiv_pairLoss_diag` is twice `o77HessianForm`, which is the
independent check that Taylor's `1/2 Hess` really is print's `Kalpha` and not
`2 Kalpha`. `exists_o77_chart` supplies the chart, splitting the parameter space
with the `2H` variation block first, and `exists_o77_block_matrix` identifies
that chart's Hessian block with `Kalpha` up to congruence. Step 4 is
instantiated, not merely available.

## Public-review verdict

The material is suitable for public review only with the following labels:

- O7: **unconditionally machine-checked negative resolution at operational
  two-sided volume order**;
- O77(a): **conditionally machine-checked at operational volume order**, with
  the single inherited O70-EIGEN-LAW frontier visible;
- O77(b): **unconditionally machine-checked at operational two-sided volume
  order**, by `o77AllSaddlesHavePairOne_holds`, at print's own quantifiers and
  with no assumed proposition;
- issue #12 overall: **not yet a formally verified complete solution** — the
  claim covers both clauses, and (a) still rests on O70-EIGEN-LAW.

Human countersignature should review the mathematical fidelity of the source
surfaces and the ownership of O70-EIGEN-LAW. It must not be described as a
kernel check, and the kernel check must not be described as human acceptance.
