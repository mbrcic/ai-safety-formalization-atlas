module

public import AISafetyAtlas.Control.ChannelRate
public import AISafetyAtlas.Control.CompleteControl
public import AISafetyAtlas.Control.InformationLimits
public import AISafetyAtlas.Control.Observability
public import AISafetyAtlas.Control.OpenLoop
public import AISafetyAtlas.Control.OpenLoopAttainment
public import AISafetyAtlas.Control.PolicyKernel
public import AISafetyAtlas.Control.Purification
public import AISafetyAtlas.Control.RequisiteVariety
public import AISafetyAtlas.Control.VarietyCounting

/-!
# Limits on control and regulation — public facade

Two classical developments, carried at their printed quantifiers: **Ashby's**
counting and entropy bounds on what a regulator can do, and
**Touchette–Lloyd's** information-theoretic accounting of what feedback buys
over open loop. Import this module (or `AISafetyAtlas`) for the surface below;
the ten nested modules hold the proofs and remain importable one at a time when
only one result is wanted.

**Every name in the table is in `namespace AISafetyAtlas.Control`**, whichever
module declares it, so it is spelled `AISafetyAtlas.Control.ashby_variety_ge` in
full, or bare after `open AISafetyAtlas.Control`. The module a declaration lives
in is never part of its name.

The two developments answer different questions and are not merged here. Ashby
counts states and compares varieties; Touchette–Lloyd measures entropy
reductions against a plant. What they share is the shape of the conclusion — a
controller cannot produce order it has no capacity to supply.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Law** | `ashby_variety_ge` | §11/5 counting form: outcome variety is at least rows over columns |
| **Law** | `ashby_logVariety_ge` | §11/7: the same bound logarithmically, `V_O ≥ V_D − V_R` |
| **Law** | `entropy_ge_of_condEntropy_ge` | §11/8 in entropies |
| **Boundary** | `ashby_variety_ge_isSharp` | the counting bound is attained, so it cannot be improved |
| **Law** | `entropy_ge_of_sensor` | what the regulator never measured still shows in the outcome |
| **Law** | `entropy_le_channelCapacity_of_complete` | a regulator cannot pass more than its channel carries |
| **Law** | `outcome_eq_comp` | §11/14: under perfect regulation the outcome is a function of the controller alone |
| **Law** | `exists_strategy_forcing` | complete control: every target sequence is forced by some strategy |
| **Boundary** | `card_disturbance_le_card_regulator` | control on top of regulation charges requisite variety twice |
| **Law** | `chainRate_eq_condEntropy` | §9/15: capacity as an entropy *rate*, not an alphabet count |
| **Law** | `controlLoss_eq_condMutualInfo` | Theorem 3: control loss *is* a conditional mutual information |
| **Law** | `controlLoss_le_entropy_noise` | Theorem 2: loss is bounded by the noise entropy |
| **Boundary** | `controlLoss_eq_entropy_noise_iff` | and exactly when that bound is met |
| **Law** | `entropyReduction_le_of_openLoopBound` | Theorem 10: feedback beats open loop by at most `I(X ; C)` |
| **Law** | `perfectlyObservable_iff_sensorLoss_eq_zero` | perfect observability is exactly zero sensor loss |
| **Law** | `entropyReduction_le_openLoopMax` | mixing the control action never beats the best fixed action |
| **Helper** | `exists_isMaxOn_openLoopObjective` | eq. (48) is attained, by compactness of the simplex |
| **Helper** | `minControlLoss_inputPolicies_eq_kernelMin` | eq. (28) as a minimum over kernels |
| **Helper** | `kernelControlLoss_deterministic` | deterministic state feedback attains it |
| **Helper** | `isPurification_purifyMap` | every actuation kernel is a deterministic map of an exogenous seed |

`Purification` is what keeps the open-loop theorems at printed scope: the source
states them for arbitrary actuation channels, and purification is the reduction
that makes the deterministic proofs cover that case rather than a subcase.

## Who consumes this, and who cannot

One cluster consumes `Control`: `Oversight.VarietyBound` takes the counting bound
into an oversight model. That is one consumer, and the rest of this development
is an island. The reason is structural and worth writing down rather than leaving
as an absence a reader has to interpret.

Everything here is **measure-theoretic**. The statements quantify over a measure
on a sample space, entropies of finite-range variables, and Markov kernels. Most
of the rest of the atlas is not: `Knowledge`, `Knowledge.Ambiguity`,
`Compositional`, `Verification` and `Wireheading.ObservationLimits` are counting
and order-theoretic developments with no measure in sight. A theorem cannot cross
that line by being imported; something has to supply the missing layer.

So the blocked consumers, named:

| Cluster | What is missing | What would unblock it |
|---|---|---|
| `Wireheading.ObservationLimits` | no measure on the environment class; `trueReturn` is real-valued and `History` is a `List`, so not even finite | a probability measure on `Env State` with finite-range observables |
| `Oversight.JointObservation` | the hazard is `Bool`, so Fano's converse floor is `(H − log 2)/log 2 ≤ 0` — **vacuous, not merely absent** | a multi-valued decision, or a different bound |
| `Knowledge.Ambiguity` | states in its own docstring that it works with no probability and no entropy | the measure layer `Knowledge.Entropy` now supplies for the kernel |
| `Compositional`, `Verification` | finite/computability arguments with no probabilistic content to bound | a stochastic protocol or verifier model |

**The expiry.** If a measure layer lands on any of those — the most likely being a
probability measure on `Wireheading`'s environment class — the first thing to try
is `entropy_ge_of_sensor` against the observed history, and this table should
shrink. Until then a second consumer would have to be manufactured, and
manufacturing one is the failure mode `docs/guide/methodology.md` warns about:
renaming a regulator does not make a bridge, and it does not make a joint either.

## Explicit non-claims

- **No AI-system reading is asserted here.** Every declaration is about a
  regulator, a plant, and a channel. Reading a learned policy as the regulator
  is an application line, not a theorem in this module; see
  `docs/status/applications.md` for how those are graded and
  `docs/bridges/` for what review a bridge has to survive.
- **Not a claim that a controller with enough variety succeeds.** All of these
  are necessary conditions. `ashby_variety_ge_isSharp` says the
  counting bound is tight, not that meeting it suffices for any particular task.
- **Capacity here is the noiseless kind.** `ChannelRate` and the capacity
  arguments use `AISafetyAtlas.InformationTheory.channelCapacity`, which is
  `log` of the signal count. Capacity as a supremum of mutual information over
  input distributions is not defined and is not needed by anything above.
- **Ashby and Touchette–Lloyd are not identified.** No theorem here transports a
  variety bound into a control-loss bound or back. They sit side by side because
  they are the same question in two idioms, which is a claim about reading, not
  a proved correspondence.
- **The survey's other control rows are still empty.** Dynamical
  uncontrollability, the Good Regulator theorem, and uncontrollability of AI
  carry no Lean on any branch.
-/
