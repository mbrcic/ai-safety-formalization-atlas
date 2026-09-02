module

public import AISafetyAtlas.InformationTheory.DataProcessing

/-!
# Information-theoretic limits on control

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004 — the source cited by `BY-005`.

A controller acts on a system whose initial state is `X`. It issues a control
action `C`; an actuation channel, disturbed by noise `Z`, carries the pair to a
final state `X'`. The paper measures a controller by two quantities. The **control loss**, its
eq. (28), is `L_C = min over {p(c|x)} of H(X' | X, C)` — *minimized*, "to ensure
that `L_C` reflects the properties of the actuation channel, and does not depend
on one's choice of control inputs". The **entropy reduction**
`ΔH = H(X) − H(X')` is how much the controller narrows the state.

Both readings of `L_C` are here. `controlLoss` is the loss of the controller at
hand; `minControlLoss` is a generic realized-policy infimum over a set of
controllers sharing one plant. `inputPolicies` supplies the measurable
conditional-independence set realizable on the current sample space; for finite
alphabets its infimum is proved equal to the source's minimum over all kernels
`p(c|x)` in `AISafetyAtlas.Control.PolicyKernel`. The pointwise results come
first because they are the sharper ones: each is proved at *every* controller,
and the corresponding infimum statement is then obtained for the represented
feasible family. `Examples…minControlLoss_lt_controlLoss_gate`
shows the minimization is not a formality.

Four of the paper's results are proved here.

| source | statement | pointwise in the controller | at a represented policy infimum |
|---|---|---|---|
| Theorem 2 | `L_C ≤ H(Z)`, with equality iff `H(Z | X', X, C) = 0` | `entropy_noise_sub_controlLoss` and its two corollaries | `minControlLoss_le_entropy_noise` for the inequality; the equality case needs a minimizer, which `PolicyKernel` constructs |
| Theorem 3 | `L_C = I(X' : Z | X, C)` | `controlLoss_eq_condMutualInfo` | `minControlLoss_eq_sInf_condMutualInfo` |
| Theorem 4 | `L_C = I(X' : X, C, Z) − I(X' : X, C)` | `controlLoss_eq_mutualInfo_sub` | `minControlLoss_eq_sInf_mutualInfo_sub` |
| Theorem 10 | `ΔH_closed ≤ ΔH_open^max + I(X ; C)` | `entropyReduction_le_of_openLoopBound` | — |

Theorem 10 is the paper's main result and the one with the AI-safety reading:
*one bit gathered by the controller is worth at most one bit of extra entropy
reduction*. Feedback is not free, and it is not better than free.

## Where this is stronger than the printed source

* **Theorem 2 is proved as an identity, not an inequality plus a separate
  equality condition.** `entropy_noise_sub_controlLoss` states
  `H(Z) − L_C = H(Z | X', X, C)` exactly. The printed inequality is that
  quantity being nonnegative and the printed equality condition is it being
  zero, so both are corollaries of one statement and neither needs its own
  argument.
* **No assumption on the sample space — and this is *not* one of the ways it is
  stronger.** Everything here holds over an arbitrary measurable space carrying a
  zero-or-probability measure, where the source works with discrete distributions
  on finite alphabets. But the variables are still countable of finite range, so
  they push the measure forward to a pmf on those same finite alphabets, the
  printed theorem applies to that pmf, and the statement here is the printed
  statement at the pushforward. The two are inter-derivable: `Ω` is a
  presentation, not a generality. What it buys a reader is that a model which is
  not born discrete needs no pushforward constructed by hand. See the
  sample-space note in `docs/provenance/source-coverage-audit.md`.
* **Theorems 2, 3 and 4 are proved at every controller, not at a minimizer.**
  The pointwise statements and the arbitrary-`P` infimum statements are both
  available. The latter apply to a represented feasible family on one sample
  space. Identifying that family's infimum with the source's minimum over every
  kernel `p(c|x)` is `AISafetyAtlas.Control.PolicyKernel`, which also constructs
  the minimizer Theorem 2's *equality* case asks for, so nothing here has to
  assume attainment. See `docs/provenance/touchette-lloyd-control.md`.
* **The purification hypothesis is used exactly where it is needed.** It appears
  as an explicit argument on the statements that use it and nowhere else, so a
  reader can see which results survive without it — Theorem 10 does.

## Step (50)

Theorem 10 rests on the paper's step (50), *"a closed-loop controller is formally
equivalent to an ensemble of open-loop controllers acting on the conditional
supports"*. The paper does justify it, in one sentence beneath the proof: *"each
conditional distribution `p(x|c)` is a legitimate input distribution for the
initial state of the controlled system. It is, in any cases, an element of `P`."*
`P` is the set of all input distributions the maximum in (48) ranges over.

Both readings are available here.

* `entropyReduction_le_of_condEntropy_ge` takes the *averaged* form, printed as
  (51), as a hypothesis and claims nothing about the model. This is the
  conservative form: it is exactly what follows *from* the step.
  `condEntropy_ge_of_openLoopBound` delivers the per-action form (50), and
  `condEntropy_le_condEntropy_of_forall` averages one into the other.
* `entropyReduction_le_of_openLoopBound` **derives** it, by mechanizing that
  sentence. `IsPlant` writes the actuation channel as a map `X' = F(X, C, Z)`;
  `OpenLoopBound` says no constant control reduces the entropy of the state by
  more than `Δopen`, on every conditional ensemble of `μ` — which is the
  "each `p(x|c)` is an element of `P`" clause, stated as a hypothesis.

`IsPlant` and `OpenLoopBound` are the atlas's rendering of the paper's model, not
formulas the paper writes. In particular the paper's `ΔH_open^max` is a maximum
over input distributions with the actuation subdynamics held fixed, whereas
conditioning `μ` on an event can also change the joint law of state and noise; the
two families are close but not literally the same, so no instance relation is
claimed in either direction. See `docs/provenance/touchette-lloyd-control.md`.

## Provenance

The published Physica A text has been read. The formalization was carried out
against arXiv:`physics/0104007v2` (May 2003), the authors' own latest preprint;
Theorems 1–11 are numbered identically in the two, and the four formalized here
match statement for statement. Theorem numbers below are
common to both. See `docs/provenance/touchette-lloyd-control.md`.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uΩ uS uK uN uT

variable {Ω : Type uΩ} {S : Type uS} {K : Type uK} {N : Type uN} {T : Type uT}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K]
variable [MeasurableSpace N] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K]
variable [MeasurableSingletonClass N] [MeasurableSingletonClass T]
variable [Countable S] [Countable K] [Countable N] [Countable T]
variable {μ : Measure Ω}

/-! ## The two measures of a controller -/

/--
**Control loss**: what the actuation leaves undetermined once the initial state
and the control action are both known. Zero exactly when the controller's action
determines the outcome.

The paper's `L_C` (eq. 28) carries a minimization over `{p(c|x)}` that this does
not: this is the pointwise-in-controller version, and it is the *stronger* of the
two, since it holds at every controller rather than at one. `minControlLoss` is
the realized-policy infimum over a caller-supplied `P`. No fixed-space `P` is
identified with all source kernels *in this module*; that identification, for
`P = inputPolicies` and finite alphabets, is
`AISafetyAtlas.Control.minControlLoss_inputPolicies_eq_kernelMin`. Theorem 2's
*equality condition* is additionally about a minimizer, and this module assumes
none exists; `minControlLoss_inputPolicies_attained` supplies one.
-/
@[expose] public noncomputable def controlLoss (μ : Measure Ω)
    (X : Ω → S) (C : Ω → K) (X' : Ω → T) : ℝ :=
  H[X' | ⟨X, C⟩ ; μ]

/--
**Entropy reduction** `ΔH = H(X) − H(X')`: how much the control process narrows
the state of the system.
-/
@[expose] public noncomputable def entropyReduction (μ : Measure Ω)
    (X : Ω → S) (X' : Ω → T) : ℝ :=
  H[X ; μ] - H[X' ; μ]

/--
**Purification of the actuation channel.** Knowing the initial state, the
control action and the actuation noise determines the final state. The paper
states this at Theorems 2–4 as *"the knowledge of the triplet `(x, c, z)` is
sufficient to infer the value of `X'`"*, but it is not local to them: §2
introduces it for *any* actuation channel as printed condition (i) of eq. (7).
`AISafetyAtlas.Control.isPurification_purifyMap` proves every finite kernel
admits such a representation.
-/
@[expose] public def Purified (μ : Measure Ω)
    (X : Ω → S) (C : Ω → K) (Z : Ω → N) (X' : Ω → T) : Prop :=
  H[X' | ⟨⟨X, C⟩, Z⟩ ; μ] = 0

/-! ## Theorem 2: the actuation noise bounds the control loss -/

/--
**Theorem 2, as an exact identity.** Under purification, and with the noise
chosen independently of the state and the action,

`H(Z) − L_C = H(Z | X', X, C)`.

The printed inequality `L_C ≤ H(Z)` is this quantity being nonnegative, and the
printed equality condition is it being zero; both follow, and neither needs a
separate argument. This is the sharper form.
-/
public theorem entropy_noise_sub_controlLoss (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {Z : Ω → N} {X' : Ω → T}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange C] [FiniteRange Z] [FiniteRange X']
    (hpure : Purified μ X C Z X')
    (hindep : H[Z | ⟨X, C⟩ ; μ] = H[Z ; μ]) :
    H[Z ; μ] - controlLoss μ X C X' = H[Z | ⟨X', ⟨X, C⟩⟩ ; μ] := by
  have hXC : Measurable (⟨X, C⟩ : Ω → S × K) := hX.prodMk hC
  -- Split the joint conditional entropy of `(X', Z)` given `(X, C)` two ways.
  have h₁ : H[⟨X', Z⟩ | ⟨X, C⟩ ; μ]
      = H[X' | ⟨X, C⟩ ; μ] + H[Z | ⟨X', ⟨X, C⟩⟩ ; μ] :=
    cond_chain_rule' μ hX' hZ hXC
  have h₂ : H[⟨X', Z⟩ | ⟨X, C⟩ ; μ]
      = H[Z | ⟨X, C⟩ ; μ] + H[X' | ⟨Z, ⟨X, C⟩⟩ ; μ] :=
    cond_chain_rule μ hX' hZ hXC
  -- Purification kills the second term of the second split.
  have hpure' : H[X' | ⟨⟨X, C⟩, Z⟩ ; μ] = 0 := hpure
  have h₃ : H[X' | ⟨Z, ⟨X, C⟩⟩ ; μ] = 0 := by
    rw [← condEntropy_pair_comm μ hX' hZ hXC] at hpure'
    exact hpure'
  rw [controlLoss]
  rw [h₃, hindep] at h₂
  linarith

/--
**Theorem 2** (Touchette–Lloyd): the control loss is at most the entropy of the
actuation noise. A controller cannot be left more uncertain than the channel
disturbing it.
-/
public theorem controlLoss_le_entropy_noise (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {Z : Ω → N} {X' : Ω → T}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange C] [FiniteRange Z] [FiniteRange X']
    (hpure : Purified μ X C Z X')
    (hindep : H[Z | ⟨X, C⟩ ; μ] = H[Z ; μ]) :
    controlLoss μ X C X' ≤ H[Z ; μ] := by
  have h := entropy_noise_sub_controlLoss μ hX hC hZ hX' hpure hindep
  have hnn : 0 ≤ H[Z | ⟨X', ⟨X, C⟩⟩ ; μ] := condEntropy_nonneg _ _ _
  linarith

/--
**Theorem 2's equality case.** The control loss exhausts the noise entropy
exactly when the noise is itself determined by the outcome, the initial state
and the action — that is, when nothing about the disturbance is lost.
-/
public theorem controlLoss_eq_entropy_noise_iff (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {Z : Ω → N} {X' : Ω → T}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange C] [FiniteRange Z] [FiniteRange X']
    (hpure : Purified μ X C Z X')
    (hindep : H[Z | ⟨X, C⟩ ; μ] = H[Z ; μ]) :
    controlLoss μ X C X' = H[Z ; μ] ↔ H[Z | ⟨X', ⟨X, C⟩⟩ ; μ] = 0 := by
  have h := entropy_noise_sub_controlLoss μ hX hC hZ hX' hpure hindep
  constructor
  · intro heq; linarith
  · intro hzero; linarith

/-! ## Theorems 3 and 4: the control loss as an information -/

/--
**Theorem 3.** The control loss is exactly the information the actuation noise
carries about the outcome, given the state and the action:
`L_C = I(X' : Z | X, C)`.
-/
public theorem controlLoss_eq_condMutualInfo (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {Z : Ω → N} {X' : Ω → T}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange C] [FiniteRange Z] [FiniteRange X']
    (hpure : Purified μ X C Z X') :
    controlLoss μ X C X' = I[X' : Z | ⟨X, C⟩ ; μ] := by
  have hXC : Measurable (⟨X, C⟩ : Ω → S × K) := hX.prodMk hC
  rw [condMutualInfo_eq' hX' hZ hXC μ, controlLoss]
  have hpure' : H[X' | ⟨⟨X, C⟩, Z⟩ ; μ] = 0 := hpure
  have h₃ : H[X' | ⟨Z, ⟨X, C⟩⟩ ; μ] = 0 := by
    rw [← condEntropy_pair_comm μ hX' hZ hXC] at hpure'
    exact hpure'
  rw [h₃]
  ring

/--
**Theorem 4.** The control loss is what the noise adds to the information the
state and action already carry about the outcome:
`L_C = I(X' : X, C, Z) − I(X' : X, C)`.
-/
public theorem controlLoss_eq_mutualInfo_sub (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {Z : Ω → N} {X' : Ω → T}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange C] [FiniteRange Z] [FiniteRange X']
    (hpure : Purified μ X C Z X') :
    controlLoss μ X C X'
      = I[X' : ⟨⟨X, C⟩, Z⟩ ; μ] - I[X' : ⟨X, C⟩ ; μ] := by
  have hXC : Measurable (⟨X, C⟩ : Ω → S × K) := hX.prodMk hC
  rw [mutualInfo_eq_entropy_sub_condEntropy hX' (hXC.prodMk hZ) μ,
    mutualInfo_eq_entropy_sub_condEntropy hX' hXC μ, controlLoss,
    show H[X' | ⟨⟨X, C⟩, Z⟩ ; μ] = 0 from hpure]
  ring

/-! ## Theorem 10: feedback is worth at most what it measures

The paper's main result. The step it rests on — that a closed-loop controller is
an ensemble of open-loop controllers acting on the conditional supports — is
hypothesis, not conclusion; see the module docstring. -/

omit [MeasurableSingletonClass S] [MeasurableSingletonClass T] [Countable S] [Countable T]
  [Countable K] in
/--
The paper's step (50) is stated per control action. This is the averaging that
turns it into the form the theorem uses: an inequality holding for every value
of `C` holds for the conditional entropies.
-/
public theorem condEntropy_le_condEntropy_of_forall (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {X' : Ω → T} (hC : Measurable C)
    [FiniteRange C] (Δ : ℝ)
    (h : ∀ c, (μ.map C).real {c} ≠ 0 → H[X | C ← c ; μ] - Δ ≤ H[X' | C ← c ; μ]) :
    H[X | C ; μ] - Δ ≤ H[X' | C ; μ] := by
  classical
  rw [condEntropy_eq_sum _ _ _ hC, condEntropy_eq_sum _ _ _ hC]
  have hweights : ∑ c ∈ FiniteRange.toFinset C, (μ.map C).real {c} = 1 := by
    rw [sum_measureReal_singleton, Measure.real,
      Measure.map_apply hC (FiniteRange.toFinset C).measurableSet]
    have hpre : C ⁻¹' (FiniteRange.toFinset C : Set K) = Set.univ := by
      ext ω
      simp [FiniteRange.mem C ω]
    rw [hpre, measure_univ]
    simp
  have hterm : ∀ c ∈ FiniteRange.toFinset C,
      (μ.map C).real {c} * H[X | C ← c ; μ] - (μ.map C).real {c} * Δ
        ≤ (μ.map C).real {c} * H[X' | C ← c ; μ] := by
    intro c _
    have hp : 0 ≤ (μ.map C).real {c} := measureReal_nonneg
    by_cases hz : (μ.map C).real {c} = 0
    · simp [hz]
    · nlinarith [h c hz]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hweights, one_mul] at hsum
  linarith

/--
**Theorem 10** (Touchette–Lloyd), the paper's main result. Given the *averaged*
form of the paper's step (50) — printed as (51) — as `hstep`, closed-loop control
beats the best open-loop control by at most the information the controller
gathered:

`ΔH_closed ≤ ΔH_open^max + I(X ; C)`.

**One bit measured buys at most one bit of control.** Feedback is not free, and
it is not better than free — its value is bounded by, and only by, what the
sensor actually learned.
-/
public theorem entropyReduction_le_of_condEntropy_ge (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {X' : Ω → T}
    (hX : Measurable X) (hC : Measurable C) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange C] [FiniteRange X']
    (Δopen : ℝ)
    (hstep : H[X | C ; μ] - Δopen ≤ H[X' | C ; μ]) :
    entropyReduction μ X X' ≤ Δopen + I[X : C ; μ] := by
  have hcond : H[X' | C ; μ] ≤ H[X' ; μ] := condEntropy_le_entropy (μ := μ) hX' hC
  have hinfo : I[X : C ; μ] = H[X ; μ] - H[X | C ; μ] :=
    mutualInfo_eq_entropy_sub_condEntropy hX hC μ
  rw [entropyReduction, hinfo]
  linarith

/-! ### Step (50), derived from an explicit open-loop model

The paper asserts step (50) from the informal equivalence *"a closed-loop
controller is an ensemble of open-loop controllers acting on the conditional
supports `supp(X|c)` instead of `supp(X)`"*. Making that equivalence a
definition rather than a sentence turns the assertion into a proof.

Two ingredients. `IsPlant` says the final state is a fixed function of the
initial state, the control action and the noise — the paper's actuation channel,
written as a map. `OpenLoopBound` says no *constant* control reduces the entropy
of the state by more than `Δopen`, **for every ensemble**, which is exactly the
"instead of `supp(X)`" clause: the conditional ensembles `X | C = c` are not the
one the bound was quoted for, so a bound quantified only over `supp(X)` would not
transfer. -/

/-- **The actuation channel as a map.** The final state is determined by the
initial state, the control action and the noise. -/
@[expose] public def IsPlant (F : S → K → N → T)
    (X : Ω → S) (C : Ω → K) (Z : Ω → N) (X' : Ω → T) : Prop :=
  ∀ ω, X' ω = F (X ω) (C ω) (Z ω)

/--
**The open-loop maximum.** No control action applied *without* observing the
state reduces the entropy of the state by more than `Δopen`.

Quantified over the **conditional ensembles** of `μ`, which is the source's own
phrase: step (50) applies the bound on `supp(X|c)`, not on `supp(X)`. Asking for
it on every conditional is exactly what the argument consumes, and no more —
quantifying over all measures on `Ω` would be a strictly stronger hypothesis and
so a weaker theorem.
-/
@[expose] public def OpenLoopBound (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) (Δopen : ℝ) : Prop :=
  ∀ s : Set Ω, MeasurableSet s → μ s ≠ 0 → ∀ k : K,
    H[X ; μ[|s]] - Δopen ≤ H[fun ω => F (X ω) k (Z ω) ; μ[|s]]

omit [MeasurableSpace N] [MeasurableSingletonClass S] [MeasurableSingletonClass N]
  [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable N] [Countable T] in
/--
**Step (50), proved.** On the event `C = c` the plant is driven by the constant
action `c`, so the conditional ensemble is acted on by an open-loop controller
and the open-loop bound applies to it.

This is the paper's prose equivalence, discharged. Note where the strength of
`OpenLoopBound` is spent: it is applied at `μ[|C ⁻¹' {c}]`, not at `μ`.
-/
public theorem condEntropy_ge_of_openLoopBound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : S → K → N → T} {X : Ω → S} {C : Ω → K} {Z : Ω → N} {X' : Ω → T}
    (hC : Measurable C) (hplant : IsPlant F X C Z X') {Δopen : ℝ}
    (hopen : OpenLoopBound μ F X Z Δopen) (c : K) (hc : μ (C ⁻¹' {c}) ≠ 0) :
    H[X | C ← c ; μ] - Δopen ≤ H[X' | C ← c ; μ] := by
  have : IsProbabilityMeasure (μ[|C ⁻¹' {c}]) := cond_isProbabilityMeasure hc
  -- on the fibre the control is constant, so the plant is open-loop there
  have hae : X' =ᵐ[μ[|C ⁻¹' {c}]] fun ω => F (X ω) c (Z ω) := by
    refine ae_cond_of_forall_mem (hC (measurableSet_singleton c)) fun ω hω => ?_
    have hCω : C ω = c := hω
    rw [hplant ω, hCω]
  calc H[X | C ← c ; μ] - Δopen
      ≤ H[fun ω => F (X ω) c (Z ω) ; μ[|C ⁻¹' {c}]] :=
        hopen _ (hC (measurableSet_singleton c)) hc c
    _ = H[X' | C ← c ; μ] := (entropy_congr hae).symm

omit [MeasurableSpace N] [MeasurableSingletonClass N] [Countable N] in
/--
**Theorem 10 without a hypothesis on the model.** The same conclusion as
`entropyReduction_le_of_condEntropy_ge`, with step (50) discharged from
`IsPlant` and `OpenLoopBound` rather than assumed.

Null fibres need no argument: `condEntropy_le_condEntropy_of_forall` asks for the
per-action inequality only where the action has positive probability, which is
also where conditioning is defined.
-/
public theorem entropyReduction_le_of_openLoopBound (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : S → K → N → T} {X : Ω → S} {C : Ω → K} {Z : Ω → N} {X' : Ω → T}
    (hX : Measurable X) (hC : Measurable C) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange C] [FiniteRange X']
    (hplant : IsPlant F X C Z X') {Δopen : ℝ}
    (hopen : OpenLoopBound μ F X Z Δopen) :
    entropyReduction μ X X' ≤ Δopen + I[X : C ; μ] := by
  refine entropyReduction_le_of_condEntropy_ge μ hX hC hX' Δopen ?_
  refine condEntropy_le_condEntropy_of_forall μ hC Δopen fun c hc => ?_
  refine condEntropy_ge_of_openLoopBound μ hC hplant hopen c fun hzero => hc ?_
  rw [Measure.real, Measure.map_apply hC (measurableSet_singleton c), hzero]
  simp

/-! ## Eq. (28): the control loss minimized over the controller

Everything above is pointwise in the controller. The paper's `L_C` is not: eq.
(28) reads

`L_C = min over {p(c|x)} of H(X' | X, C)`,

and the parenthesis under it says why — *"the minimization over all conditional
distributions for `C` is there to ensure that `L_C` reflects the properties of
the actuation channel, and does not depend on one's choice of control inputs."*
So the minimization ranges over the **controller** while the source law of `X`,
the noise `Z` and the actuation channel are held fixed.

That constraint is what `IsPlant` supplies. Varying the controller varies the
final state too, so the printed quantity is a minimum of `H(X' | X, C)` along a
*family* of pairs `(C, X')` sharing one plant — not a minimum over `C` at a fixed
`X'`, which would be the wrong object. -/

/--
**The state a fixed plant produces under a given controller.** With the actuation
map `F`, the initial state `X` and the noise `Z` all fixed, a choice of
controller `C` determines the final state. `isPlant_plantOutcome` records that
this is a plant, by definition.
-/
@[expose] public def plantOutcome (F : S → K → N → T)
    (X : Ω → S) (C : Ω → K) (Z : Ω → N) : Ω → T :=
  fun ω => F (X ω) (C ω) (Z ω)

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace N]
  [MeasurableSpace T] [MeasurableSingletonClass S] [MeasurableSingletonClass K]
  [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
public theorem isPlant_plantOutcome (F : S → K → N → T)
    (X : Ω → S) (C : Ω → K) (Z : Ω → N) :
    IsPlant F X C Z (plantOutcome F X C Z) := fun _ => rfl

omit [MeasurableSingletonClass T] [Countable T] in
/-- The outcome of a measurable controller is measurable: the actuation map
leaves a countable space with measurable singletons, so it is measurable outright.
-/
public theorem measurable_plantOutcome (F : S → K → N → T)
    {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z) :
    Measurable (plantOutcome F X C Z) := by
  have : DiscreteMeasurableSpace ((S × K) × N) :=
    MeasurableSingletonClass.toDiscreteMeasurableSpace
  exact (Measurable.of_discrete (f := fun p : (S × K) × N => F p.1.1 p.1.2 p.2)).comp
    ((hX.prodMk hC).prodMk hZ)

/--
**The controllers eq. (28) minimizes over.** The paper's `{p(c|x)}` are channels
from the *state* to the action: the control input is chosen on `x` and on nothing
else. So a policy tells you nothing about the actuation noise that the state does
not already tell you, which is conditional independence of `C` and `Z` given `X`.

This is not decoration. The paper's proof of Theorem 2 needs it at step (30),
where `H(Z | X, C) = H(Z)` follows "from the fact that `Z` is chosen
independently of `X` and `C`".

Measurability is part of admissibility rather than a side condition carried
separately: a kernel `p(c|x)` is measurable by construction, so a rendering of
`{p(c|x)}` that admitted non-measurable maps would be admitting things the
printed set does not contain. Nothing below breaks either way — every theorem
takes its witness's measurability as a hypothesis — but with it here the
`inputPolicies` instance discharges that hypothesis from membership alone.
-/
@[expose] public def IsInputPolicy (μ : Measure Ω) (X : Ω → S) (Z : Ω → N)
    (C : Ω → K) : Prop :=
  Measurable C ∧ CondIndepFun C Z X μ

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K]
  [MeasurableSingletonClass N] [Countable S] [Countable K] [Countable N] in
public theorem IsInputPolicy.measurable {μ : Measure Ω} {X : Ω → S} {Z : Ω → N}
    {C : Ω → K} (h : IsInputPolicy μ X Z C) : Measurable C := h.1

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K]
  [MeasurableSingletonClass N] [Countable S] [Countable K] [Countable N] in
public theorem IsInputPolicy.condIndep {μ : Measure Ω} {X : Ω → S} {Z : Ω → N}
    {C : Ω → K} (h : IsInputPolicy μ X Z C) : CondIndepFun C Z X μ := h.2

/-- The realized feasible set for eq. (28)'s channel-from-state condition.

This contains the measurable controllers on the current `Ω` that satisfy the
conditional-independence condition. It renders the source constraint; that its
infimum equals the source's minimum over all stochastic kernels `p(c|x)` is
proved separately, in `AISafetyAtlas.Control.PolicyKernel`, and needs finite
alphabets. -/
@[expose] public def inputPolicies (μ : Measure Ω) (X : Ω → S) (Z : Ω → N) :
    Set (Ω → K) :=
  {C | IsInputPolicy μ X Z C}

/--
**Eq. (28): the control loss minimized over a set of admissible controllers**,
with the plant `F`, the initial state `X` and the noise `Z` all held fixed.

`P` is a parameter, and **which `P` renders the source's `L_C` matters**. Eq. (28)
minimizes over `{p(c|x)}`, and the rendering available here is
`minControlLoss μ F X Z (inputPolicies μ X Z)` — the infimum over the policies
realizable on *this* `Ω`, which is `≥` the infimum over all kernels, and (for
finite alphabets) equal to it by
`AISafetyAtlas.Control.minControlLoss_inputPolicies_eq_kernelMin`.
Taking `P = Set.univ` is **not**
the paper's unconstrained minimum: a map `Ω → K` may read the actuation noise,
which no `p(c|x)` can, and such a controller can drive the loss strictly below
the printed value — `Examples…minControlLoss_univ_lt_inputPolicy` exhibits one.
Every theorem below is stated for arbitrary `P`, so the pointwise identities and
represented-family infimum statements do not depend on this particular choice.

Controllers are maps `Ω → K` rather than kernels `x ↦ p(c|x)`, and
`IsInputPolicy` is what keeps a controller's own randomness from being the noise.
Randomization is not lost *across the theorems*, because every one of them is
stated at an **arbitrary** `Ω`: a kernel is realized on a large enough space, so
instantiating there covers it. A *fixed* `Ω` may realize only some kernels, which
is why this infimum is `≥` the kernel infimum a priori. That it is not strictly
greater is a theorem and not an observation: the optimum turns out to be
deterministic, and deterministic policies need no auxiliary randomness.

`sInf` rather than `min`: an infimum always exists, so no attainment has to be
assumed *here*. Where attainment matters — Theorem 2's *equality* case — it is a
named hypothesis in this module; see
`minControlLoss_eq_entropy_noise_iff_of_attained`, and
`minControlLoss_inputPolicies_attained` for the witness that discharges it.
-/
@[expose] public noncomputable def minControlLoss (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) (P : Set (Ω → K)) : ℝ :=
  sInf ((fun C => controlLoss μ X C (plantOutcome F X C Z)) '' P)

omit [MeasurableSpace N] [MeasurableSingletonClass S] [MeasurableSingletonClass K]
  [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
/-- The control losses along a plant are bounded below by `0`, which is what
`csInf_le` needs. It does **not** rule out the `sInf` junk value on the empty
set: `minControlLoss μ F X Z ∅ = 0`, vacuously. Every statement below that reads
the infimum downward supplies a member of `P`. -/
public theorem bddBelow_controlLoss_image (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) (P : Set (Ω → K)) :
    BddBelow ((fun C => controlLoss μ X C (plantOutcome F X C Z)) '' P) := by
  refine ⟨0, ?_⟩
  rintro _ ⟨C, -, rfl⟩
  exact condEntropy_nonneg _ _ _

omit [MeasurableSpace N] [MeasurableSingletonClass S] [MeasurableSingletonClass K]
  [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
/-- The realized-policy infimum is bounded by the loss of any admitted controller. -/
public theorem minControlLoss_le (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) {P : Set (Ω → K)} {C : Ω → K} (hC : C ∈ P) :
    minControlLoss μ F X Z P ≤ controlLoss μ X C (plantOutcome F X C Z) :=
  csInf_le (bddBelow_controlLoss_image μ F X Z P) ⟨C, hC, rfl⟩

omit [MeasurableSpace N] [MeasurableSingletonClass S] [MeasurableSingletonClass K]
  [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
/-- The realized-policy infimum is nonnegative on a nonempty admissible set. -/
public theorem minControlLoss_nonneg (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) {P : Set (Ω → K)} (hP : P.Nonempty) :
    0 ≤ minControlLoss μ F X Z P := by
  refine le_csInf (hP.image _) ?_
  rintro _ ⟨C, -, rfl⟩
  exact condEntropy_nonneg _ _ _

/--
**Theorem 2 for a represented policy infimum.** The realized-policy infimum is
bounded by `H(Z)`, rather than only the loss of one controller.

Only *one* admitted controller has to satisfy the purification and independence
hypotheses: an infimum is below every member of its set, so a single witness
already caps it. That makes this a strictly weaker hypothesis than the paper's,
which imposes purification across the whole family.

The printed *equality* case does not transfer this way, and is not claimed. It
says the bound is met exactly when `H(Z | X', X, C) = 0`, which is a statement
about a minimizer; `sInf` need not be attained, and no attainment is assumed
anywhere here. `controlLoss_eq_entropy_noise_iff` is the pointwise form, which
is what the atlas has.
-/
public theorem minControlLoss_le_entropy_noise (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (F : S → K → N → T) {X : Ω → S} {Z : Ω → N} {P : Set (Ω → K)} {C : Ω → K}
    (hCP : C ∈ P) (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange C] [FiniteRange Z] [FiniteRange (plantOutcome F X C Z)]
    (hpure : Purified μ X C Z (plantOutcome F X C Z))
    (hindep : H[Z | ⟨X, C⟩ ; μ] = H[Z ; μ]) :
    minControlLoss μ F X Z P ≤ H[Z ; μ] :=
  le_trans (minControlLoss_le μ F X Z hCP)
    (controlLoss_le_entropy_noise μ hX hC hZ (measurable_plantOutcome F hX hC hZ) hpure hindep)

/--
**Theorem 2 at the rendered feasible set.** The same bound with `P` taken to be
`inputPolicies` — the one instance the paper names — where the witness's
measurability is no longer a separate hypothesis but comes out of membership.
-/
public theorem minControlLoss_inputPolicies_le_entropy_noise (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    {C : Ω → K} (hCP : C ∈ inputPolicies μ X Z) (hX : Measurable X) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange C] [FiniteRange Z] [FiniteRange (plantOutcome F X C Z)]
    (hpure : Purified μ X C Z (plantOutcome F X C Z))
    (hindep : H[Z | ⟨X, C⟩ ; μ] = H[Z ; μ]) :
    minControlLoss μ F X Z (inputPolicies μ X Z) ≤ H[Z ; μ] :=
  minControlLoss_le_entropy_noise μ F hCP hX hCP.measurable hZ hpure hindep

/--
**Theorem 2's equality case for a represented policy infimum, where the minimum
is attained.** If an admitted controller `C` is a minimizer — `C ∈ P`, and no
other admitted controller loses less — then the equality condition holds for
that represented infimum.

Being a minimizer is a hypothesis, not a theorem: `sInf` need not be reached, and
nothing here constructs an optimal controller. That is the honest reading of the
source, which writes `min` where its own argument supports `inf` and never
exhibits a minimizer either. Without it only `minControlLoss_le_entropy_noise`
survives, and the equality case stays pointwise as
`controlLoss_eq_entropy_noise_iff`.
-/
public theorem minControlLoss_eq_entropy_noise_iff_of_attained (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    {P : Set (Ω → K)} {C : Ω → K} (hCP : C ∈ P)
    (hmin : ∀ C' ∈ P, controlLoss μ X C (plantOutcome F X C Z)
      ≤ controlLoss μ X C' (plantOutcome F X C' Z))
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange C] [FiniteRange Z] [FiniteRange (plantOutcome F X C Z)]
    (hpure : Purified μ X C Z (plantOutcome F X C Z))
    (hindep : H[Z | ⟨X, C⟩ ; μ] = H[Z ; μ]) :
    minControlLoss μ F X Z P = H[Z ; μ]
      ↔ H[Z | ⟨plantOutcome F X C Z, ⟨X, C⟩⟩ ; μ] = 0 := by
  have hattain : minControlLoss μ F X Z P
      = controlLoss μ X C (plantOutcome F X C Z) :=
    le_antisymm (minControlLoss_le μ F X Z hCP)
      (le_csInf ⟨_, C, hCP, rfl⟩ (by rintro _ ⟨C', hC', rfl⟩; exact hmin C' hC'))
  rw [hattain]
  exact controlLoss_eq_entropy_noise_iff μ hX hC hZ
    (measurable_plantOutcome F hX hC hZ) hpure hindep

/--
**Theorem 3 for a represented policy infimum.** The two quantities the paper
equates agree *at every admitted controller*, so they have the same image and
hence the same infimum over any represented family; no minimizer is needed.

This is the shape the paper's own remark points at — after Theorem 2 it says the
next two results hold under the same conditions, "the minimization over the set
of conditional probability distributions `{p(c|x)}` is implied at this point".
-/
public theorem minControlLoss_eq_sInf_condMutualInfo (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    {P : Set (Ω → K)} (hX : Measurable X) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Z]
    (hC : ∀ C ∈ P, Measurable C) (hfr : ∀ C ∈ P, FiniteRange C)
    (hfr' : ∀ C ∈ P, FiniteRange (plantOutcome F X C Z))
    (hpure : ∀ C ∈ P, Purified μ X C Z (plantOutcome F X C Z)) :
    minControlLoss μ F X Z P
      = sInf ((fun C => I[plantOutcome F X C Z : Z | ⟨X, C⟩ ; μ]) '' P) := by
  refine congrArg sInf (Set.image_congr fun C hCP => ?_)
  have := hfr C hCP
  have := hfr' C hCP
  exact controlLoss_eq_condMutualInfo μ hX (hC C hCP) hZ
    (measurable_plantOutcome F hX (hC C hCP) hZ) (hpure C hCP)

/--
**Theorem 4 for a represented policy infimum.** As for Theorem 3: an equality
holding at every admitted controller is an equality of the two infima.
-/
public theorem minControlLoss_eq_sInf_mutualInfo_sub (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    {P : Set (Ω → K)} (hX : Measurable X) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Z]
    (hC : ∀ C ∈ P, Measurable C) (hfr : ∀ C ∈ P, FiniteRange C)
    (hfr' : ∀ C ∈ P, FiniteRange (plantOutcome F X C Z))
    (hpure : ∀ C ∈ P, Purified μ X C Z (plantOutcome F X C Z)) :
    minControlLoss μ F X Z P
      = sInf ((fun C => I[plantOutcome F X C Z : ⟨⟨X, C⟩, Z⟩ ; μ]
          - I[plantOutcome F X C Z : ⟨X, C⟩ ; μ]) '' P) := by
  refine congrArg sInf (Set.image_congr fun C hCP => ?_)
  have := hfr C hCP
  have := hfr' C hCP
  exact controlLoss_eq_mutualInfo_sub μ hX (hC C hCP) hZ
    (measurable_plantOutcome F hX (hC C hCP) hZ) (hpure C hCP)

end AISafetyAtlas.Control
