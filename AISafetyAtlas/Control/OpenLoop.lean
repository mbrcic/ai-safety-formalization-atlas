module

public import AISafetyAtlas.Control.PolicyKernel

/-!
# Open-loop control: mixing the control action never helps

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004, Lemma 8 and Theorem 9.

An **open-loop** controller does not observe the state: its action is drawn
independently of the initial state, which is the source's eq. (opd)
*p(x,x',c)ₒₚₑₙ = p_X(x) p_C(c) p(x'|x,c)*. The paper measures such a controller
by the entropy it removes from the state,
*ΔH_open = H(X) − H(X')_open*, and asks whether *randomizing* the action can beat
every fixed action. It cannot:

> the maximum decrease of entropy achieved by a particular subdynamics of control
> variable *ĉ = arg max over c of ΔH_open^c* is *open-loop optimal* in the sense that no
> random (i.e., non-deterministic) choice of the controller's state can improve
> upon that decrease

and in the paper's vocabulary: a **pure** controller — one that plays a single
action with probability 1 — is optimal, and every **mixed** one either matches it
or does worse.

## Why this sits next to eq. (28)

It is the same fact twice. `AISafetyAtlas.Control.PolicyKernel` shows the control
loss `L_C` is *linear* in the controller's weights, so its minimum is at a vertex.
Here the quantity is *ΔH_open*, and the mechanism is *concavity* of entropy rather
than linearity of the objective — mixing the action mixes the outcome law, and
mixing never lowers entropy. Different mechanism, identical conclusion, and the
source draws it in both places.

## Where the open-loop model is spent, and where it is not

**Lemma 8 needs no independence at all.** `entropyReduction_le_condEntropy_form`
is `H(X') ≥ H(X'|C)` rearranged, which holds for any controller whatsoever. The
source states it inside the open-loop section, but its proof — reproduced here —
uses only that conditioning does not raise entropy.

**Theorem 9 does.** `openLoopEntropy` is the entropy of the outcome when the
constant action `c` is applied, computed against `μ` itself; the conditional
`H(X'|C = c)` is computed against `μ` restricted to the fibre. Those agree exactly
when the action carries nothing about the state *or the noise*, which is
`IndepFun C ⟨X, Z⟩ μ` — the atlas's rendering of eq. (opd). It is a hypothesis
here rather than a standing assumption, so a reader can see which result consumes
it.
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

/-! ## Lemma 8: the averaged open-loop reduction dominates -/

omit [MeasurableSingletonClass S] [MeasurableSingletonClass N] [Countable S] [Countable N] in
/--
**Lemma 8**, *ΔH_open ≤ ΔH_open^C*, where the right-hand side is the average over
the controller's own actions, `H(X) − H(X'|C)`.

The source's proof, and this one: conditioning does not raise entropy, so
`H(X') ≥ H(X'|C)`. No property of open-loop control is used — the inequality
holds at every controller, observing or not.
-/
public theorem entropyReduction_le_condEntropy_form (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] {X : Ω → S} {C : Ω → K} {X' : Ω → T}
    (hX' : Measurable X') (hC : Measurable C) [FiniteRange X'] [FiniteRange C] :
    entropyReduction μ X X' ≤ H[X ; μ] - H[X' | C ; μ] := by
  have := condEntropy_le_entropy (μ := μ) hX' hC
  rw [entropyReduction]
  linarith

omit [MeasurableSingletonClass S] [MeasurableSingletonClass N] [Countable S] [Countable N] in
/--
**Lemma 8's equality case.** Equality holds exactly when `I(X' ; C) = 0` — the
controller's action tells you nothing about the outcome.

The source states this and proves it in the same breath as the inequality; here
it is the same identity read at zero, since `I(X' : C) = H(X') − H(X'|C)`.
-/
public theorem entropyReduction_eq_condEntropy_form_iff (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ] {X : Ω → S} {C : Ω → K} {X' : Ω → T}
    (hX' : Measurable X') (hC : Measurable C) [FiniteRange X'] [FiniteRange C] :
    entropyReduction μ X X' = H[X ; μ] - H[X' | C ; μ] ↔ I[X' : C ; μ] = 0 := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX' hC μ, entropyReduction]
  constructor <;> intro h <;> linarith

/-! ## Theorem 9: a pure controller is open-loop optimal -/

/-- **The outcome entropy under the constant action `c`** — the source's
*H(X'|c)ₒₚₑₙ*. -/
@[expose] public noncomputable def openLoopEntropy (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) (c : K) : ℝ :=
  H[fun ω => F (X ω) c (Z ω) ; μ]

/-- **Eq. (opc), *ΔH_open^c*: what the pure controller `C = c` removes.** -/
@[expose] public noncomputable def openLoopReduction (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) (c : K) : ℝ :=
  H[X ; μ] - openLoopEntropy μ F X Z c

omit [MeasurableSpace K] [MeasurableSpace N] [MeasurableSingletonClass S]
  [MeasurableSingletonClass K] [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
/-- **The pure controller attains its own reduction**, by definition of the plant:
`plantOutcome` at a constant action *is* the constant-action outcome. This is the
"equality can always be achieved" clause of Theorem 9. -/
public theorem entropyReduction_const (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) (c : K) :
    entropyReduction μ X (plantOutcome F X (fun _ => c) Z) = openLoopReduction μ F X Z c :=
  rfl

omit [MeasurableSingletonClass T] [Countable K] [Countable T] in
/--
**The outcome entropy on a fibre is the pure controller's outcome entropy.**

This is the step that consumes the open-loop model. On the event `C = c` the
plant is driven by the constant `c`; for that fibre's outcome law to be the one
the *pure* controller produces against all of `μ`, conditioning on `C = c` must
not move the joint law of state and noise — which is what independence of `C`
from `⟨X, Z⟩` says.
-/
public theorem condEntropy_fibre_eq_openLoopEntropy (μ : Measure Ω) [IsFiniteMeasure μ]
    (F : S → K → N → T) {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    (hindep : IndepFun C (⟨X, Z⟩ : Ω → S × N) μ) (c : K) (hc : μ (C ⁻¹' {c}) ≠ 0) :
    H[plantOutcome F X C Z | C ← c ; μ] = openLoopEntropy μ F X Z c := by
  haveI : IsProbabilityMeasure (μ[|C ⁻¹' {c}]) := cond_isProbabilityMeasure hc
  have hae : plantOutcome F X C Z =ᵐ[μ[|C ⁻¹' {c}]] fun ω => F (X ω) c (Z ω) := by
    refine ae_cond_of_forall_mem (hC (.singleton c)) fun ω hω => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp [plantOutcome, hω]
  haveI : DiscreteMeasurableSpace (S × N) := MeasurableSingletonClass.toDiscreteMeasurableSpace
  have hFm : Measurable (fun p : S × N => F p.1 c p.2) := .of_discrete
  have key : ∀ ν : Measure Ω, Measure.map (fun ω => F (X ω) c (Z ω)) ν
      = (ν.map (⟨X, Z⟩ : Ω → S × N)).map (fun p : S × N => F p.1 c p.2) := by
    intro ν; rw [Measure.map_map hFm (hX.prodMk hZ)]; rfl
  rw [entropy_congr hae, openLoopEntropy, entropy_def, entropy_def, key, key,
    map_cond_eq_of_indepFun hC (hX.prodMk hZ) hindep c hc]

/--
**Theorem 9**, *ΔH_open ≤ max over c of ΔH_open^c*: no controller, however randomized,
removes more entropy than the best single action does.

Proved through Lemma 8 — the mixed controller is dominated by the average of the
pure ones — and then by the average being dominated by its own best term. The
source's *ĉ = arg max over c of ΔH_open^c* is `entropyReduction_const`'s witness, so the
bound is reached and the inequality is tight.
-/
public theorem entropyReduction_le_iSup_openLoopReduction [Fintype K] [Nonempty K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : S → K → N → T)
    {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange (plantOutcome F X C Z)]
    (hindep : IndepFun C (⟨X, Z⟩ : Ω → S × N) μ) :
    entropyReduction μ X (plantOutcome F X C Z) ≤ ⨆ c : K, openLoopReduction μ F X Z c := by
  obtain ⟨ĉ, hĉ⟩ := Finite.exists_min (openLoopEntropy μ F X Z)
  -- the averaged conditional entropy is at least the best pure one
  have hweights : ∑ c : K, μ.real (C ⁻¹' {c}) = 1 := by
    rw [sum_measureReal_preimage_singleton _ fun c _ => hC (.singleton c)]
    simp
  have hge : openLoopEntropy μ F X Z ĉ ≤ H[plantOutcome F X C Z | C ; μ] := by
    rw [condEntropy_eq_sum_fintype _ _ _ hC]
    calc openLoopEntropy μ F X Z ĉ
        = ∑ c : K, μ.real (C ⁻¹' {c}) * openLoopEntropy μ F X Z ĉ := by
          rw [← Finset.sum_mul, hweights, one_mul]
      _ ≤ ∑ c : K, μ.real (C ⁻¹' {c}) * H[plantOutcome F X C Z | C ← c ; μ] := by
          refine Finset.sum_le_sum fun c _ => ?_
          obtain hc | hc := eq_or_ne (μ.real (C ⁻¹' {c})) 0
          · simp [hc]
          refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
          rw [condEntropy_fibre_eq_openLoopEntropy μ F hX hC hZ hindep c
            fun h => hc (by simp [measureReal_def, h])]
          exact hĉ c
  calc entropyReduction μ X (plantOutcome F X C Z)
      ≤ H[X ; μ] - H[plantOutcome F X C Z | C ; μ] :=
        entropyReduction_le_condEntropy_form μ (measurable_plantOutcome F hX hC hZ) hC
    _ ≤ openLoopReduction μ F X Z ĉ := by rw [openLoopReduction]; linarith
    _ ≤ ⨆ c : K, openLoopReduction μ F X Z c := le_ciSup (Finite.bddAbove_range _) ĉ

omit [MeasurableSpace K] [MeasurableSpace N] [MeasurableSingletonClass S]
  [MeasurableSingletonClass K] [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
/-- **Theorem 9's attainment clause.** Some pure controller reaches the best
constant-action reduction, and the constant controller realizes that value.

This is the conclusion the source states separately after its inequality. It is
named rather than left inside the proof of
`entropyReduction_le_iSup_openLoopReduction`, so the coverage row cites a theorem
that actually contains the existential witness. -/
public theorem exists_entropyReduction_const_eq_iSup_openLoopReduction [Fintype K]
    [Nonempty K] (μ : Measure Ω) (F : S → K → N → T) (X : Ω → S) (Z : Ω → N) :
    ∃ c : K, entropyReduction μ X (plantOutcome F X (fun _ => c) Z)
      = ⨆ k : K, openLoopReduction μ F X Z k := by
  obtain ⟨c, hc⟩ := Finite.exists_min (openLoopEntropy μ F X Z)
  refine ⟨c, ?_⟩
  rw [entropyReduction_const]
  apply le_antisymm
  · exact le_ciSup (Finite.bddAbove_range _) c
  · refine ciSup_le fun k => ?_
    rw [openLoopReduction, openLoopReduction]
    linarith [hc k]

/-! ## A supremum rendering of eq. (48)

Eq. (max1) reads

> `ΔH_open^max = max over p_X(x) ∈ P, c ∈ C of ΔH_open^c`

and the sentence beneath it says what `P` is: *"the maximum entropy decrease that
can be obtained by (pure) open-loop control over **any** input distribution
chosen in the set `P` of all probability distributions"*. So the maximum ranges
over two things at once — the input distribution and the control value — with the
actuation subdynamics held fixed.

Declared here as a supremum over all probability measures on the state space,
inside the independent-noise realization `X' = F(X,c,Z)`. `Real.sSup` of an
unbounded set is junk (`0`), so boundedness is not optional: `[Fintype S]`
supplies it, since the reduction never exceeds the entropy of its own input
distribution and that is at most `log |S|`.

**What this buys, and what remains.** The atlas's `OpenLoopBound` quantifies over
the *conditional ensembles of `μ`*, which is a different family: conditioning `μ`
can move the joint law of state and noise together, whereas the printed maximum
moves the input distribution with the actuation channel fixed. Quantifying over
**all** input distributions removes the mismatch, because each conditional law
`p(x|c)` is then simply one of the distributions being maximized over — which is
exactly the source's own one-sentence justification of the step.

This module states the object over a deterministic `F` driven by an independent
seed `Z`, while the source starts from an arbitrary finite transition kernel
`p(x'|x,c)`. Those are the same family, and `AISafetyAtlas.Control.Purification`
is where that is proved: the source's own §2 says any channel is a *randomly
selected deterministic channel*, `isPurification_purifyMap` constructs one, and
`openLoopMax_purifyMap` shows the two renderings generate the **same set** of
reductions. `kernelEntropyReduction_le_kernelOpenLoopMax` is Theorem 10 with no
`F` and no `Z` in the statement.

The source writes a maximum while `openLoopMax` is an `sSup`. Boundedness is
proved below, and attainment over the input-distribution simplex is proved in
`AISafetyAtlas.Control.OpenLoopAttainment`, so the two agree: by
`isGreatest_kernelOpenLoopMax` the supremum is an element of the family it bounds,
which is what eq. (48)'s `max` asserts.
-/

/-- **`ΔH_open^c` at a given input distribution.** The state is drawn from `ν`, the
noise from `η` independently, and the constant action `c` is applied. -/
@[expose] public noncomputable def openLoopReductionAt (F : S → K → N → T) (η : Measure N)
    (ν : Measure S) (c : K) : ℝ :=
  Hm[ν] - Hm[(ν.prod η).map (fun p : S × N => F p.1 c p.2)]

/-- The set eq. (48) maximizes over: every input distribution, every action. -/
@[expose] public def openLoopReductions (F : S → K → N → T) (η : Measure N) : Set ℝ :=
  {r | ∃ ν : Measure S, IsProbabilityMeasure ν ∧ ∃ c : K, openLoopReductionAt F η ν c = r}

/-- **A bounded-supremum rendering of eq. (48)'s `ΔH_open^max`.** -/
@[expose] public noncomputable def openLoopMax (F : S → K → N → T) (η : Measure N) : ℝ :=
  sSup (openLoopReductions F η)

omit [MeasurableSpace Ω] [MeasurableSpace K] [MeasurableSingletonClass K]
  [MeasurableSingletonClass N] [MeasurableSingletonClass T] [Countable S] [Countable K]
  [Countable N] [Countable T] in
/-- The rendered family is bounded, so the supremum is not `Real.sSup`'s junk
value. This is where `[Fintype S]` is spent: a reduction never exceeds the entropy
of its own input distribution, and that is capped by `log |S|`. -/
public theorem bddAbove_openLoopReductions [Fintype S] (F : S → K → N → T) (η : Measure N) :
    BddAbove (openLoopReductions F η) := by
  refine ⟨Real.log (Fintype.card S), ?_⟩
  rintro _ ⟨ν, hν, c, rfl⟩
  have h1 : Hm[ν] ≤ Real.log (Fintype.card S) := measureEntropy_le_log_card ν
  have h2 : (0:ℝ) ≤ Hm[(ν.prod η).map (fun p : S × N => F p.1 c p.2)] :=
    measureEntropy_nonneg _
  rw [openLoopReductionAt]
  linarith

omit [MeasurableSpace Ω] [MeasurableSpace K] [MeasurableSingletonClass K]
  [MeasurableSingletonClass N] [MeasurableSingletonClass T] [Countable S] [Countable K]
  [Countable N] [Countable T] in
/-- Every represented input distribution and action is dominated by the supremum. -/
public theorem le_openLoopMax [Fintype S] (F : S → K → N → T) (η : Measure N)
    (ν : Measure S) [IsProbabilityMeasure ν] (c : K) :
    openLoopReductionAt F η ν c ≤ openLoopMax F η :=
  le_csSup (bddAbove_openLoopReductions F η) ⟨ν, inferInstance, c, rfl⟩

omit [MeasurableSingletonClass T] [Countable K] [Countable T] in
/--
**Conditioning on the control leaves an independent product.** If the noise is
drawn independently of the state *and* the action, then on the event `C = c` the
state and the noise are independent and the noise still has its original law.
The condition is the paper's own, and not only via Theorem 2's step (30): §2
introduces the exogenous seed for *any* actuation channel, with eq. (7) weighting
by `p_Z(z)` rather than `p(z|x,c)`, which is exactly this independence.

This is what makes the fibre an honest open-loop ensemble: an input distribution
paired with the untouched actuation channel.

No hypothesis on the fibre's mass is needed. Conditioning on a null event yields
the zero measure, and both sides are then zero — the identity is not vacuous
there, it is trivial.
-/
public theorem map_prodMk_cond_eq_prod (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {Z : Ω → N} (hX : Measurable X) (hC : Measurable C)
    (hZ : Measurable Z) (hindep : IndepFun (⟨X, C⟩ : Ω → S × K) Z μ) (c : K) :
    (μ[|C ⁻¹' {c}]).map (⟨X, Z⟩ : Ω → S × N)
      = ((μ[|C ⁻¹' {c}]).map X).prod (μ.map Z) := by
  have hCm : MeasurableSet (C ⁻¹' {c}) := hC (.singleton c)
  refine Measure.ext_of_singleton fun p => ?_
  obtain ⟨x, z⟩ := p
  have hsingle : ({(x, z)} : Set (S × N)) = ({x} : Set S) ×ˢ ({z} : Set N) := by
    simp [Set.singleton_prod_singleton]
  rw [Measure.map_apply (hX.prodMk hZ) (MeasurableSet.singleton (x, z)), hsingle,
    Measure.prod_prod,
    Measure.map_apply hX (.singleton x), Measure.map_apply hZ (.singleton z),
    cond_apply hCm, cond_apply hCm]
  have hpre : (⟨X, Z⟩ : Ω → S × N) ⁻¹' (({x} : Set S) ×ˢ ({z} : Set N))
      = X ⁻¹' {x} ∩ Z ⁻¹' {z} := rfl
  rw [hpre]
  -- the state fibre and the control fibre together form an atom of `⟨X, C⟩`
  have hxc : C ⁻¹' {c} ∩ (X ⁻¹' {x} ∩ Z ⁻¹' {z})
      = (⟨X, C⟩ : Ω → S × K) ⁻¹' (({x} : Set S) ×ˢ ({c} : Set K)) ∩ Z ⁻¹' {z} := by
    rw [Set.mk_preimage_prod, Set.inter_left_comm, Set.inter_assoc]
  have hxc' : C ⁻¹' {c} ∩ X ⁻¹' {x}
      = (⟨X, C⟩ : Ω → S × K) ⁻¹' (({x} : Set S) ×ˢ ({c} : Set K)) := by
    rw [Set.mk_preimage_prod, Set.inter_comm]
  rw [hxc, hxc',
    hindep.measure_inter_preimage_eq_mul _ _
      ((MeasurableSet.singleton x).prod (MeasurableSet.singleton c)) (MeasurableSet.singleton z),
    mul_assoc]

omit [MeasurableSingletonClass T] [Countable K] [Countable T] in
/--
**Step (50), inside the independent-noise rendering.** On the event `C = c` the
state's entropy drops by at most the rendered open-loop supremum.

The atlas's earlier rendering `OpenLoopBound` had to be *assumed* to hold on every
conditional ensemble of `μ`, and its relation to the printed `ΔH_open^max` was
recorded as "neither direction". That gap closes here: the conditional law of the
state on the fibre is an input distribution like any other, so eq. (48)'s maximum
covers it by construction. The source's own justification, mechanized —
*"each conditional distribution `p(x|c)` is a legitimate input distribution … it
is, in any cases, an element of `P`"*. The bridge from an arbitrary printed
transition kernel to this independent-noise rendering is
`AISafetyAtlas.Control.isPurification_purifyMap`.
-/
public theorem condEntropy_ge_of_openLoopMax [Fintype S] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    (hindep : IndepFun (⟨X, C⟩ : Ω → S × K) Z μ) (c : K) (hc : μ (C ⁻¹' {c}) ≠ 0) :
    H[X | C ← c ; μ] - openLoopMax F (μ.map Z) ≤ H[plantOutcome F X C Z | C ← c ; μ] := by
  haveI : IsProbabilityMeasure (μ[|C ⁻¹' {c}]) := cond_isProbabilityMeasure hc
  haveI : IsProbabilityMeasure ((μ[|C ⁻¹' {c}]).map X) :=
    Measure.isProbabilityMeasure_map hX.aemeasurable
  haveI : DiscreteMeasurableSpace (S × N) := MeasurableSingletonClass.toDiscreteMeasurableSpace
  have hFm : Measurable (fun p : S × N => F p.1 c p.2) := .of_discrete
  have hae : plantOutcome F X C Z =ᵐ[μ[|C ⁻¹' {c}]] fun ω => F (X ω) c (Z ω) := by
    refine ae_cond_of_forall_mem (hC (.singleton c)) fun ω hω => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
    simp [plantOutcome, hω]
  have houtcome : H[plantOutcome F X C Z | C ← c ; μ]
      = Hm[(((μ[|C ⁻¹' {c}]).map X).prod (μ.map Z)).map (fun p : S × N => F p.1 c p.2)] := by
    rw [entropy_congr hae, entropy_def, ← map_prodMk_cond_eq_prod μ hX hC hZ hindep c,
      Measure.map_map hFm (hX.prodMk hZ)]
    rfl
  have hbound := le_openLoopMax F (μ.map Z) ((μ[|C ⁻¹' {c}]).map X) c
  rw [openLoopReductionAt] at hbound
  rw [houtcome]
  have hstate : H[X | C ← c ; μ] = Hm[(μ[|C ⁻¹' {c}]).map X] := entropy_def X _
  rw [hstate]
  linarith

/--
**Theorem 10 inside the independent-noise rendering of eq. (48).**

`ΔH_closed ≤ ΔH_open^max + I(X ; C)` — one bit gathered by the controller is
worth at most one bit of improvement over open-loop control.

`AISafetyAtlas.Control.entropyReduction_le_of_openLoopBound` proves the same
conclusion from `OpenLoopBound`, which is the atlas's own rendering of the
open-loop model and does not nest with the printed maximum in either direction.
This version proves the printed inequality once the actuation channel is
represented by a deterministic `F` driven by noise independent of the state and
action. The source's Theorem 10 is stated directly for arbitrary fixed transition
kernels, and `AISafetyAtlas.Control.kernelEntropyReduction_le_kernelOpenLoopMax`
is this theorem transported to them, via the realization built in
`AISafetyAtlas.Control.Purification`.
-/
public theorem entropyReduction_le_openLoopMax [Fintype S] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange C] [FiniteRange (plantOutcome F X C Z)]
    (hindep : IndepFun (⟨X, C⟩ : Ω → S × K) Z μ) :
    entropyReduction μ X (plantOutcome F X C Z)
      ≤ openLoopMax F (μ.map Z) + I[X : C ; μ] := by
  refine entropyReduction_le_of_condEntropy_ge μ hX hC (measurable_plantOutcome F hX hC hZ)
    (openLoopMax F (μ.map Z)) (condEntropy_le_condEntropy_of_forall μ hC _ fun c hcz => ?_)
  refine condEntropy_ge_of_openLoopMax μ F hX hC hZ hindep c fun h => hcz ?_
  rw [map_measureReal_apply hC (.singleton c), measureReal_def, h, ENNReal.toReal_zero]

end AISafetyAtlas.Control
