# A formal system of power and sovereignty — triage, and one result taken

**Date.** 2026-09-12.

**Status.** Not a published source, not graded in
[`source-coverage-audit.md`](source-coverage-audit.md), and no registry row
cites it as print. It is an internal proposal held in the user's own literature
tree, and this note exists so that the one result taken from it has a pinned
origin rather than a remembered one.

## The document

Held privately; the files and their hashes:

| File | sha256 |
|---|---|
| `FORMAL_SYSTEM-power.md` | `2ee1d90530cc43d2cb9eeb065cc9e6f5f78d5d44e9a727ac25989aa011f17584` |
| `finite_models_power.py` | `8ca3f0c35ca15eaf14e4124ebcdcac7eaa47bbd69a34b7f47e9d60961101045e` |
| `formal-power-transcript.md` | `25563b5ac68aa26fa28755d2bf7c052b58e9620634ef089fe2466433e5d2571d` |

*A Formal System of Power, Sovereignty, and Cognitive Sovereignty.* Thirteen
sections: a common dynamic substrate, qualitative power as strategy footprints
and effectivity, quantitative power and influence, sovereignty as a constitution
over a protected catalogue, a dynamic safety game with recovery, cognitive
sovereignty as authorship, an epistemic cluster, adapters to other power
theories. Its results are labelled `P1`–`P12`, `D1`–`D8`, `C1`–`C12`.

`finite_models_power.py` is the accompanying executable model: explicit finite
game tables, footprints, the three effectivity quantifiers, the safety kernel by
a controllable-predecessor iteration, and observation-uniform defences. Under
the repository's search order it is a **computational formalization**, search
step 2, and it is the reason the definitions below could be checked against
something executable rather than only against prose.

## Two of its definitions are already this repository's

Checked against the document, not inferred from the names.

| Document | Atlas |
|---|---|
| §5.4 relative retention, `Retains_κ(G₀,G₁) ⟺ E_X(G₀) ∩ P_κ ⊆ E_X(G₁)` | `AISafetyAtlas.Sovereignty.RetainsFamily` |
| §5.3 demandwise sovereignty at the sure reading, `∀ q ∈ Q_κ ∃σ ∀τ, O(σ,τ) ⊆ Φ_q` | `AISafetyAtlas.Sovereignty.Demandwise` (new) |
| §3.1 α-effectivity / `can` | `Forces`, `effectivity` |
| §5.2 *"distinguishable alternative requests, not only the ability to do nothing"* | `AISafetyAtlas.Sovereignty.Separating` (new) |

The Python's `sovereignty(protected)` is `all(self.can(q) for q in protected)`,
which is `Demandwise` exactly, and its `ValueError("Empty protected-demand
catalogue is vacuous")` is the weaker half of `Separating.nonempty`.

Several of the `P` results are shapes the repository already carries — goal
monotonicity, coalition monotonicity, disjoint superadditivity, the
non-conflict of opposing sure guarantees. Those correspondences have **not**
been checked statement by statement and are not claimed here.

## What was taken

**D8 only.** *"Safety without service is vacuous sovereignty. A controller that
refuses every input can preserve 'no unauthorized change' while failing every
learning, correction, or task-completion demand. Therefore invariant
preservation does not imply the service-based sovereignty definition. This
motivates keeping safety, liveness, and recoverability separate."*

It is in `AISafetyAtlas.Sovereignty.Service`, with witnesses in
`AISafetyAtlas.Examples.Sovereignty.Service`:

* `Inert` — a game form in which nothing anyone does changes the outcome;
* `Inert.forces_iff` — such a game form's effectivity family is the sets
  containing the still point, **at every coalition, including the empty one**;
* `inert_retainsFamily_iff` — a refusing delegate retains a protected family
  iff the still point lies in every protected set the baseline delivered;
* `retainsFamily_and_not_demandwise` — D8;
* `separating_not_demandwise_of_inert` — §5.2 as a condition on the
  specification: a separating catalogue defeats every refusing delegate at
  once, not only one pinned to a chosen point.

## Scope, stated rather than implied

**Narrower than print on one axis.** D8 sits in §6, whose object is a finite
deterministic safety game `s' = F(s,a,b)` with a controlled-invariant kernel
computed by iterating `CPre`. Nothing in `Service.lean` has a transition
relation, a trajectory, or a time index. What is rendered is D8's *mechanism* —
that invariant preservation is met by inaction — in the one-shot effectivity
frame the repository already has.

**Wider on another.** Print exhibits one controller and one failure.
`inert_retainsFamily_iff` characterizes the whole class: it says exactly which
protected families are vacuously retainable, and `Separating` gives the
condition on a catalogue that no refusing delegate can pass.

**Therefore not coverage.** The document is unpublished and this note makes no
coverage claim for it. If it is ever published, D8's row would grade `Partial`
at `Wider` scope for the reason above, and `D1`–`D3` — the safety kernel, the
recovery attractor and its budget monotonicity — would grade `No`, since the
repository has no controlled-predecessor operator.

## What was not taken

`P7` (same-agent conjunction fails), `P10` (projection), `P11`
(strategy-preserving refinement) and `C3` (endorsement factorization) were
scoped alongside D8 and are not built. `P12` and the whole quantitative track
(§4) need a value or probability layer the sovereignty modules do not have.
The five operational verbs of §6.3 are the same five that
[`cognitive-sovereignty-obligation.md`](cognitive-sovereignty-obligation.md)
records as unpublished, and are unchanged by this note.

---

# Full triage, 2026-09-12

The whole document, result by result. It states **64** numbered results in seven
blocks: `P1`–`P12` qualitative power, `Q1`–`Q10` quantitative, `S1`–`S8`
sovereignty, `D1`–`D8` dynamic, `C1`–`C12` cognitive and epistemic, `A1`–`A6`
derived AI-safety, `B1`–`B8` adapters to neighbouring theories. §9's fourteen
specialization types and §11's five worked cases are prose and are not results.

`PowerKernel_uncompiled.lean`, the 236-line draft §12 names, **is not in the
folder** — the transcript links it to a sandbox path that no longer exists. So
there is no prior Lean to reuse or attribute, and everything below is written
here.

**Status values.** `IN_TREE` — already proved, declaration named and checked
against the printed statement. `CHEAP` — reachable on the sovereignty substrate
as it stands. `SUBSTRATE` — needs a layer the repository does not have, named in
the row. `PROSE` — not a mathematical claim.

The three substrate layers the document needs and the atlas lacks, in the order
they are load-bearing:

1. **A probability kernel on a game form**, `K : Σ_X × Σ_Y → Δ(Ω)`, with lower
   and upper values. `Q1`–`Q10`, `C7`, `C8`, `S5`, `B1`, `B5`, `P12` rest on it.
2. **A transition relation with time**, for the §6.1 safety game and its
   controllable predecessor. `D1`–`D5` rest on it.
3. **Complexity**, for `C11` alone.

## §3 Qualitative power

| | Claim | Status | Where |
|---|---|---|---|
| P1 | footprint representation: `Φ ∈ E_X` iff some footprint fits inside `Φ` | `IN_TREE` | `forces_iff_outcomesOf_subset`, with `outcomesOf` the footprint |
| P2 | goal monotonicity | `IN_TREE` | `Forces.mono` |
| P3 | nonvacuity: forces `Ω`, does not force `∅` | `IN_TREE` | `forces_univ`, `not_forces_empty` |
| P4 | resource and threat monotonicity | **done** | `ForcesWithin.mono_resources` |
| P5 | coalition monotonicity | `IN_TREE` | `Forces.mono_coalition`. Print conditions it on an extension property; a `GameForm` has independent strategy spaces, so the property holds by construction |
| P6 | disjoint-coalition superadditivity | `IN_TREE` | `forces_superadditive` |
| P7 | same-agent conjunction fails | **done** | `decider_not_forces_inter`; the positive half is `forces_inter_of_shared_footprint` |
| P8 | quantifier separation, `∃σ∀τ` against `∀τ∃σ` | **done** | `ForcesResp`, separated by `bitMatch` |
| P9 | opposing sure guarantees cannot conflict | `IN_TREE` | `Forces.inter_nonempty_of_disjoint`, `not_forces_compl_of_forces` |
| P10 | projection: power over `B` downstairs is power over `f⁻¹ B` upstairs | **done** | `forces_map_iff_forces_preimage` |
| P11 | strategy-preserving refinement transfers guarantees | **done** | `Simulates`, `forces_of_simulates`; the published anchor is now read and cited — Alur, Henzinger, Kupferman and Vardi 1998, Lemma 1, and their Proposition 2 gives `simulates_univ_iff`, `simulates_empty_iff` and the non-monotonicity witness |
| P12 | qualitative effectivity is not a complete quantitative invariant | **done**, at every non-degenerate pair rather than print's `1/4` and `3/4` | `qualitative_does_not_determine_value`, over `supportEffectivity` |

## §4 Quantitative power

`Q1` minimax inequality, `Q2` exact complement relation, `Q3` finite mixed
minimax, `Q4` supremum 1 without an almost-sure strategy, `Q5` kernel
perturbation, `Q6` conjunction under one shared policy, `Q7` causal null
equivalence, `Q8` coarsening hides influence, `Q9` influence compatible with
full choice control, `Q10` zero Shapley–Shubik identifies a null player only in
a monotone simple game.

**Layer 1 was built on 2026-09-12** — `AISafetyAtlas.Sovereignty.Value`, on
`MeasureTheory.Measure` with `IsProbabilityMeasure`, values in `ℝ≥0∞`, the law
a plain function rather than a `ProbabilityTheory.Kernel` because nothing
measures anything in the strategy argument.

| | Status |
|---|---|
| Q1 | **done**, `OutcomeLaw.lowerValue_le_upperValue` |
| Q2 | **done**, `OutcomeLaw.opponentLowerValue_eq_one_sub_upperValue` |
| Q3 | **done**, `exists_mixed_value`. The earlier entry here said Mathlib has neither a linear program nor a Sion minimax at `db584cd`; the first half is right and **the second half was wrong** — `Mathlib/Topology/Sion.lean` is there, real-valued, and the mixed extension satisfies its hypotheses |
| Q4 | **done**, `OutcomeLaw.ThresholdAbility` with both halves and a non-attaining witness |
| Q5 | **done**, `OutcomeLaw.lowerValue_le_of_law_le`, one-sided as it is used |
| Q6 | **done**, `OutcomeLaw.le_law_inter`, binary; print states it for a finite family |
| Q7 | **done**, `eventGap_eq_zero_iff` and `influenceCapacity_eq_zero_iff` |
| Q8 | **done**, `eventGap_map_le` |
| Q9 | **done**, `accept_forces_false`, `accept_forces_true`, `accept_influence_ne_zero` |
| Q10 | **done**, `shapleyShubik_eq_zero_iff`, with print's quota-3 weights-(3,1,1) example and the nonmonotone cancellation countermodel |

The bridge `lowerValue_diracLaw_eq_one_iff` — sure winning is lower value one —
is what makes the layer trustworthy rather than merely present.

## §5 Sovereignty

| | Claim | Status | Where |
|---|---|---|---|
| S1 | request monotonicity | `IN_TREE` | `Demandwise.mono` |
| S2 | demandwise selector | **done** | `demandwise_iff_exists_selector`, at an arbitrary catalogue |
| S3 | responsive options overestimate sovereignty | **done** | `demandwiseResp_of_demandwise`, strict by `demandwiseResp_not_demandwise` |
| S4 | retention is a preorder | **done** | `RetainsFamily.trans` and `retainsFamily_refl` |
| S5 | average versus critical capability, `S_min ≤ S_μ` | **done** | `iInf_le_lintegral` |
| S6 | non-sovereignty does not entail domination | **done** | `bitMatch_no_sovereignty_no_veto`, over `Veto` |
| S7 | conflicting protected instructions have no joint trace | **done**, in a stronger form | `not_forces_of_disjoint_of_shared`: no single *commitment* serves two disjoint demands, which needs `outcomesOf_nonempty` and is what the shared-witness rule bounds |
| S8 | formal authority and effective control are independent | **done** | `not_authority_implies_control`, `not_control_implies_authority` |

## §6 Dynamic sovereignty

**Layer 2 was built on 2026-09-12** — `AISafetyAtlas.Sovereignty.SafetyGame`,
with the kernel taken as a greatest fixed point rather than by downward
iteration.

| | Claim | Status |
|---|---|---|
| D1 | safety-kernel characterization | **done**, `mem_safetyKernel_iff_exists_maintaining` — at arbitrary types, and print's `|S|`-round *rate* is not proved |
| D2 | recovery-attractor characterization | **done**, `mem_recovery_iff`; `recovery_reaches` builds a positional controller, `mem_recovery_of_recovers` refutes history-dependent ones |
| D3 | recovery-budget monotonicity | **done**, `recovery_mono_budget` and `recovery_mono_viability` |
| D4 | noninteracting composition | **done**, `maintains_prodGame`; print's two hypotheses are the definition of the product game |
| D5 | intervention-latency bound | **done**, `danger_le_of_rate` and `not_crossed_of_rate` |
| D6 | sequential integrity bound | **done in the form print uses it**, `prod_le_of_step_le`; the one-step bound is assumed rather than derived from conditional probabilities, so this is `Partial` against print |
| D7 | assistance raises output and lowers fallback | `IN_TREE`, in a better form than print's arithmetic | `retainsWith_delegateDecides` with `not_retainsAgainst_delegateDecides`: the principal's target is forced with the delegate inside the coalition and not against it |
| D8 | safety without service is vacuous sovereignty | **done** | `AISafetyAtlas.Sovereignty.Service` |

## §8 Cognitive and epistemic

| | Claim | Status | Note |
|---|---|---|---|
| C1 | belief-governed action does not establish upstream sovereignty | **done**, `mem_of_agent_forces` and `beliefDecisive_not_sovereign` | the belief model is `DoxasticAgent`, one step of Rakow's belief formation and doxastic strategy; Rakow read and pinned |
| C2 | authorship is not identifiable from transitions alone | **done** | `not_exists_label_agreeing_with_both` |
| C3 | endorsement factorization | **done** | `residualFree_iff_factors` |
| C4 | positive learning influence is compatible with sovereignty | **done**, `magnitude_does_not_decide_authorship` | `CogSov` transcribed from §7.4 and checked both ways; the separation turns on `C3`, not on the other two hypotheses |
| C5 | constitutional self-modification preserves authorization | **done** | `authorizedFrom_of_stepwise`, with print's caveat stated as `authorizedFrom_of_total` |
| C6 | observation–action uniformization | **done**, at arbitrary types rather than print's finite ones | `exists_uniformDecision_iff` |
| C7 | randomization does not remove the information obstruction | **done**, `exists_measure_le_inv_of_disjoint` | and the bound is attained by print's symmetric construction |
| C8 | quantitative binary evidence bound `(1 + TV)/2` | **done**, `success_add_le_one_add_eventGap` | at every region, since `eventGap` already is print's maximum; abstention is out of scope, as print says |
| C9 | exact auditability | **done** | `auditable_iff_exists_detector`, which is Mathlib's `Function.factorsThrough_iff` under the proposal's reading |
| C10 | monitor-selection characterization | **done** | `selectionAuditable_iff_separates` |
| C11 | minimum-cost monitor selection is NP-hard | **Partial** | the **semantics half is built**: `cover_iff_selectionAuditable` states the set-cover correspondence against `C10`, with the selection the same object on both sides so cost transports unchanged, and witnesses in both directions. The **complexity half is not**, and needs the encoding, the polynomial construction cost and set cover's own hardness in a framework the atlas does not carry |
| C12 | adequate local views need not reveal a joint hazard | **done** at the set level, through `C10`; `SUBSTRATE` for print's distributional form |

## §9 Derived AI-safety results

| | Claim | Status |
|---|---|---|
| A1 | coalition threat monotonicity | **done** qualitatively, `ForcesWithin.mono_threat`; the value form is `SUBSTRATE` |
| A2 | semantic portability preserves power under simulation | **done** | `demandwise_of_simulates` |
| A3 | lost distinctions obstruct exact recovery | **done** | `not_exists_recovery_of_collision` |
| A4 | a signature is not a truth theorem | **done** | `exists_verified_untrue`, a one-liner, as print's own proof is |
| A5 | a delegate-controlled shutdown channel gives no shutdown control | **done** | `gate_obeys_when_delivered` with `gate_principal_cannot_force` |
| A6 | shared witness is the key to compositional assurance | **done** | `forces_inter_of_shared_footprint`, and the `iInter` form |

## §10 Adapters

| | Claim | Status |
|---|---|---|
| B1 | target power is payoff power at an indicator | **done** | `OutcomeLaw.lowerPayoff_indicator` |
| B2 | deterministic finite empowerment is `log₂ \|range f\|` | **done**, `empowerment_eq_log_card_range`, with print's attaining construction carried out |
| B3 | robust zero-error communicative power | **done** | `transmitsZeroError_iff_exists_code` |
| B4 | linear-control specialization and the disturbance quantifier | **done** | `Plant.exists_robustInput_iff`, with `isControllable_iff_reachesEvery` identifying the reachability half with the atlas's own criterion |
| B5 | Bayesian evidence constrains reachable beliefs (martingale of posteriors) | **done**, `sum_marginal_mul_posterior` and `eq_prior_of_constant_posterior` |
| B6 | voting pivotality as average causal influence | **done**, `banzhafRaw_eq_swings_div` and `banzhafRaw_eq_zero_iff`; built rather than ported, since Banzhaf exists in no Lean repository |
| B7 | untyped power-over is not transitive | **done** | `split_opponent_forces_fst`, `split_principal_forces_snd`, `split_opponent_not_forces_snd` |
| B8 | accuracy, privacy, benefit and authorization are not interchangeable | **done** | `exists_all_four_combinations`, a one-liner, as print's own proof is |

## Counts

| Status | Count |
|---|---|
| done | 55 |
| `IN_TREE` | 8 |
| `CHEAP` | 0 |
| Partial | 1 |
| `SUBSTRATE` | 0 |

Counted result by result over the 64 rows of the tables above. `Q10` and `B6`
moved to **done** on 2026-09-12 with `LAND-SOV-VOTINGPOWER-001`.

**What is left. Updated 2026-09-12: one.** `Q10` and `B6` were built together as
`LAND-SOV-VOTINGPOWER-001`, because they are one theorem about one class and
were graded `SUBSTRATE` for the same missing object; building the shared simple-game
layer settled both and made the Econlib port question moot, since `Q10` consumes
the Shapley-Shubik *formula* on simple games and not an axiomatic
characterization. **`C11` alone remains**, and only its complexity half: the
set-cover reduction is a semantics statement that lands on `C10`'s
`selectionAuditable_iff_separates`. **That reduction was then built the same
day** as `cover_iff_selectionAuditable`, so `C11` is now graded **Partial**
rather than `SUBSTRATE`: nothing is blocked on absent substrate, and what is
left is a complexity framework and the decision whether to carry one. **No row
of the sixty-four is `SUBSTRATE` any more.**

The paragraph below is the position as it stood before that build.

**What was left.** Nothing was `CHEAP`. `Q10` and `B6` (Shapley and Banzhaf) and
`C11` (a complexity framework) were the three that remained, and the searches
recorded in the work order found candidates for both: `danlyng/Econlib`
(Apache-2.0, toolchain `v4.29.0`) has the Shapley value with its axioms and
uniqueness but **no Banzhaf index**, and `SamuelSchlesinger/complexitylib`
(Apache-2.0, toolchain `v4.34.0-rc2`) has `NP`, `coNP` and Cook–Levin but **no
set cover**. Both are port-or-build decisions now, not absences.

**`Q3` was never blocked, and the entry saying so was wrong.** It claimed
Mathlib has neither a linear program nor a Sion minimax at the pinned revision.
The first half holds. The second does not: `Mathlib/Topology/Sion.lean` carries
Sion's theorem, `Sion.exists_isSaddlePointOn` is stated for real-valued
functions, and the mixed extension of a finite matrix game satisfies every
hypothesis — simplices are nonempty, convex and compact, and a bilinear payoff
is continuous and both quasiconvex and quasiconcave in each argument. The
lesson is the one already in the searching rule: the earlier search asked
whether a *linear program* exists, which is print's proof route, instead of
asking whether the *statement* is reachable. Mathlib's own `Sion.lean` lists
spelling out the von Neumann case as a TODO, so the finite bilinear instance
was genuinely missing — from Mathlib, not from reach.

`B2` did join the information-theory side, and it was the last one that could
be built here. PFR's entropy library supplied the two halves — a deterministic
output has no conditional entropy, and an entropy is at most the log of the
size of a set the variable lives in — and print's attaining construction, one
input per reachable output taken uniformly, is carried out rather than
asserted. `empowerment_eq_channelCapacity_range` identifies the answer with the
atlas's own `channelCapacity`, which was written for a different purpose.

`C4` was **not** blocked on the authority decision, and the earlier note saying
so was wrong. §7.4's `CogSov` is a hyperproperty over runs, observations and a
defender class; it does not mention the authority predicate. It is transcribed
as written, checked for satisfiability *and* refutability, and `C4` is proved
as a separation rather than print's compatibility claim: two protected
transitions with the same endorsed belief change, one residual-free and one
not. The separation turns on `C3` alone; the other two hypotheses print names
are the clauses of `CogSov` and are not consumed.

**And `CogSov` is now literally a hyperproperty — 2026-09-13.** The sentence
above called it one and the module docstring said, in the same breath, that the
two clusters were *not* connected and that connecting them was a signature
change nobody had made. It is made: `H`'s type is
`AISafetyAtlas.Compositional.Hyperproperties.Hyperproperty` at `Run`. That is an
abbreviation, so no statement and no proof moved.

What it buys is one theorem that could not previously be stated:
`cogSov_mono_of_subsetClosed` — **if the relational specification is
subset-closed, deleting runs cannot destroy cognitive sovereignty**, with the
same defender. `SubsetClosed` is Clarkson and Schneider's page-1167 class, which
landed in `Compositional.Hyperproperties` the same day together with their
Theorem 1.

The hypothesis is not decoration: `Examples.Sovereignty.CogSov.topOnly` accepts
the total run set and nothing less, `topOnly_not_subsetClosed` places it outside
the class, and `shrinking_can_destroy_cogSov` flips the predicate by shrinking
the run set alone. **Whether `H` ought to be required to be subset-closed is
still open**; the transport makes the question askable in the tree and does not
answer it.

`C7`, `C8` and `B5` did not need a new substrate after all. `C7` is a counting
argument over one probability law — the identical-observation hypothesis enters
only as `actionLaw_congr`, which is print's own step — and the examples attain
the bound. `C8` needed nothing beyond `eventGap`, which already *is* the
maximum over decision regions print takes by hand. `B5` is a finite sum
identity with the zero-probability signal handled rather than excluded.

`C1` closed with the belief layer. Rakow 2022 — the only published anchor any
of these 64 results has — was fetched, pinned and **read**: Definitions 3 to 5
and Table 1, at pages 103–114 of EPTCS 371. Its doxastic strategy decides on a
history of beliefs and its belief formation maps histories of observations to
beliefs; `DoxasticAgent` is that pair at one step, with the decisiveness
condition as a *field*, which is what makes print's "instantiate the two maps"
literally the proof. The general statement is `mem_of_agent_forces`: every
target the agent can force already contains the whole range of the sender's
control. The module and the row both say, in their own words, that this is not
a defect in the problem Rakow formalizes and that neither direction of the
scope comparison with Rakow is favourable.

`D2`'s converse and `Q4` closed together. The converse is stated against
controllers that read the whole history of answers, not only positional ones,
so the recovery sets are where *no* controller succeeds from outside; the
forward direction stays positional, and `playH_positional` joins them into
print's equivalence. `Q4` needed no limit: the escalating game succeeds with
chance `1 - n⁻¹`, the supremum is `1` by `ENNReal.sub_iInf` over the
reciprocals of the naturals, and non-attainment is `ENNReal.sub_lt_self` at a
finite cast.

Layer 2 closed `D1`, `D3`, `D4` and `D5` and, with the converse, `D2`.

**The whole `P` block is closed**, and `S`, `C` and `A` are one result each
from it. What remains in `CHEAP` is `C1` (a belief-update model) and `Q4` (a
limit argument over a sequence of strategies). `SUBSTRATE` is now the dynamic
block `D1`–`D6`, the remaining probabilistic results that need more than the
value layer (`S5`, `C4`, `C7`, `C8`, `B1`, `B5`, `D6`), `Q3` and `Q10` under
layers of their own, `C11` under complexity, `B2` and `B6`.

Layer 1 moved `Q1` and `Q2` to done and seven of the `Q` block from
`SUBSTRATE` to `CHEAP`; `Q3` and `Q10` did not move and are now recorded under
layers of their own.

**Recount.** The first version of this table was assembled by block and the
composition was off; the numbers above are counted result by result and sum to
64. The `SUBSTRATE` figure fell because `C12` and `A1` are each split across
two statuses and were previously counted only once.

Updated after three waves. `D8` came first; then `P7`, `P8`, `S3` and `A6`;
then `P4`, `P10`, `P11`, `A1` and `A2`; then `S2`, `S4` and `S7`; then the
auditability cluster `C3`, `C6`, `C9`, `C10` and `A3`; then `B3`, `C5` and
`C12` at the set level, with `D7` found already in the tree.

**What is left in `CHEAP`.** `S6`, `S8`, `C1`, `C2`, `A4`, `A5`, `B7` and `B8`
are eight countermodels that each need an **authority predicate** as an input —
`Auth`, which the proposal's own §1 correction table and §7.4 say the theory
specifies rather than justifies. Building them means introducing an atlas-side
`Authorized` with no source behind it, once, and then refuting eight links
against it. `CHEAP` is now empty. The eight countermodels were built with the authority
predicate carried as a bare `Prop` — never instantiated anywhere in the
repository, present in every binder — a decision taken on 2026-09-12 and
recorded in `LAND-SOV-AUTH-001`. Three of them (`A4`, `B8`, `C2`) are one-line
countermodels, and the module docstring says so rather than dressing them up;
print's own proofs are one line each.

**What is blocked on something outside this repository** is written up as a
work order at
the private manifest of 2026-09-12,
sha256 `4828eea6c477ace660688d016257bf96f5692663e1bca53461efe9d5897fd021`,
rewritten on 2026-09-12 once the session had continued past the questions it
originally asked, and again once its Part B searches came back. Its Part A is now a **record of decisions taken**, each with
what was built and how to veto it: `A1` answered (authority stays undefined,
the eight countermodels carry a bare `Prop`), `A2` settled by reading Rakow and
building `DoxasticAgent` — neither of the two options offered, and anchored
without grading — and `A3` settled by closing the whole `D` block. Its Part B has been **searched**, and each of the
four entries now records what came back: `B1` was the wrong question and `Q3`
needed nothing, `B4` is moot because the `D` block is built, and `B2` and `B3`
found real candidate libraries — `danlyng/Econlib` for the Shapley value (no
Banzhaf anywhere) and `SamuelSchlesinger/complexitylib` for the complexity
classes (no set cover). What remains is a port-or-build decision on each, not
an absence. Part C lists ten works the proposal cites that are not yet
pinned. **None of the ten blocks a proof** — nothing here is graded against the
proposal, because the proposal is unpublished — but the §10 adapters and the §1
corrections cannot be checked without them.

**Where this ended.** Layer 1 (a probability kernel on a game form, built on
`MeasureTheory.Measure` with `IsProbabilityMeasure` rather than on `PMF`) and
layer 2 (a transition relation with a controllable predecessor) were both
built, and together with the belief, evidence, cognitive-sovereignty and
empowerment modules they closed everything that this repository can close on
its own. Four results remain, and each waits on one of the four ecosystem
searches in Part B of the work order: `Q3` on linear-programming duality,
`Q10` and `B6` on Shapley and Banzhaf, `C11` on a complexity framework. There
is no remaining item whose obstacle is effort rather than a missing external
fact.
