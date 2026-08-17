module

public import AISafetyAtlas.Control.OpenLoop

/-!
# Purification: every actuation channel is a deterministic map of an exogenous seed

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004, §2, the paragraph introducing
Fig. 2 and eq. (7).

The paper sets up its model with an arbitrary transition matrix `p(x'|x,c)` and
then immediately observes that no generality is lost by taking the actuation
channel to be *deterministic* once an extra variable is carried along:

> From a strict mathematical point of view, note that **any** non-deterministic
> channel modeling a source of noise at the level of actuation or estimation can
> be represented abstractly as a **randomly selected deterministic channel** with
> transition matrix containing only zeros and ones. The outcome of a random
> variable undisclosed to the controller can be thought of as being responsible
> for the choice of the channel to use. […] supplementing our original control
> graphs of Fig. 1 with an **exogenous and non-controllable random variable `Z`**
> in order to 'purify' the channel considered.

and states the condition in two printed parts:

> (i) The mapping from `X` to `X'` conditioned on the values `c` and `z`, as
> described by the extended transition matrix `p(x'|x,c,z)`, is deterministic for
> all `c ∈ C` and `z ∈ Z`.
> (ii) When traced out of `Z`, `p(x'|x,c,z)` reproduces the dynamics of
> `p(x'|x,c)`, i.e. `p(x'|x,c) = ∑_z p(x'|x,c,z) p_Z(z)`.   (7)

Part (i) is discharged by *typing*: the atlas writes the purified channel as a
function `F : S → K → N → T`, so it is deterministic by construction and there is
nothing to assume. Part (ii) is `IsPurification` below, one displayed equation.
`p_Z(z)` rather than `p(z|x,c)` is what "exogenous" means, and it is why the
realized seed is independent of the state and the action.

## What this module supplies that the paper does not

The paper **asserts** the representation and does not construct it. This module
constructs it, and the construction is the paper's own phrase read literally: a
*randomly selected deterministic channel* is a random element of the space of
deterministic channels, `S × K → T`. That space is finite when the alphabets are,
so the seed needs no continuum — `purifySeed` is the product measure that draws
the response to every state–action pair independently from its own column of the
kernel, and `purifyMap` reads off the entry that was asked for.

`exists_isPurification` is the resulting statement: **every** Markov kernel on
finite alphabets is purified by some deterministic map with a seed of its own.

## Why it matters here

`AISafetyAtlas.Control.OpenLoop` proves Theorems 9 and 10 for a plant written as
`X' = F(X, C, Z)` with `Z` independent of `(X, C)`. The source states them for an
arbitrary kernel `p(x'|x,c)`. Without a realization theorem those are different
families and the Lean covers the narrower one. With it they are the same family,
and `kernelEntropyReduction_le_kernelOpenLoopMax` states Theorem 10 with no `F`
and no `Z` anywhere in sight — only the printed `ρ` and `κ`.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uS uK uT

variable {S : Type uS} {K : Type uK} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]

/-! ## The purification condition, eq. (7) -/

/--
**Eq. (7), the purification condition.** The seed `η` and the deterministic map
`F` purify the actuation kernel `κ` when tracing out the seed reproduces `κ`:
for every state `x` and action `c`, pushing `η` forward along `F x c` gives the
column `κ (x, c)`.

Printed part (i) — that the extended channel is deterministic — is carried by the
type of `F` rather than by a hypothesis, so this definition is the whole of the
printed condition.
-/
@[expose] public def IsPurification {N : Type*} [MeasurableSpace N]
    (F : S → K → N → T) (η : Measure N) (κ : Kernel (S × K) T) : Prop :=
  ∀ x : S, ∀ c : K, η.map (F x c) = κ (x, c)

/-! ## The construction: a randomly selected deterministic channel -/

/--
**The seed space is the space of deterministic channels.** `purifySeed κ` draws a
deterministic channel `S × K → T` at random, choosing the response to each
state–action pair independently from that pair's column of `κ`. This is the
paper's *"random variable … responsible for the choice of the channel to use"*,
built rather than assumed.
-/
@[expose] public noncomputable def purifySeed [Fintype S] [Fintype K]
    (κ : Kernel (S × K) T) : Measure (S × K → T) :=
  Measure.pi fun a => κ a

/--
**The purified actuation map.** Having drawn a deterministic channel, apply it.
Zeros and ones only, as the paper asks: the extended transition matrix
`p(x'|x,c,z)` is `1` exactly when `z (x, c) = x'`.
-/
@[expose] public def purifyMap : S → K → (S × K → T) → T :=
  fun x c z => z (x, c)

section Instances

variable [Fintype S] [Fintype K]

instance instIsProbabilityMeasurePurifySeed (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    IsProbabilityMeasure (purifySeed κ) := by
  unfold purifySeed; infer_instance

end Instances

variable [Fintype S] [Fintype K]

omit [MeasurableSpace S] [MeasurableSpace K] [MeasurableSingletonClass S]
  [MeasurableSingletonClass K] [MeasurableSingletonClass T] [Fintype S] [Fintype K] in
/-- `purifyMap x c` is evaluation at `(x, c)`, hence measurable. -/
public theorem measurable_purifyMap (x : S) (c : K) :
    Measurable (purifyMap x c : (S × K → T) → T) :=
  measurable_pi_apply (x, c)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T] in
/--
**The construction purifies.** Tracing the seed out of `purifyMap` returns the
kernel it was built from — the printed eq. (7).
-/
public theorem isPurification_purifyMap (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    IsPurification (purifyMap : S → K → (S × K → T) → T) (purifySeed κ) κ := fun x c =>
  (measurePreserving_eval (μ := fun a : S × K => κ a) (x, c)).map_eq

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T] in
/--
**Every actuation channel on finite alphabets is purifiable** — the paper's
"*any* non-deterministic channel can be represented as a randomly selected
deterministic channel", supplied as a theorem rather than as a remark.
-/
public theorem exists_isPurification (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    ∃ (F : S → K → (S × K → T) → T) (η : Measure (S × K → T)),
      IsProbabilityMeasure η ∧ (∀ x c, Measurable (F x c)) ∧ IsPurification F η κ :=
  ⟨purifyMap, purifySeed κ, inferInstance, measurable_purifyMap, isPurification_purifyMap κ⟩

/-! ## Reading a purified system off a joint law and a kernel -/

/-- The measurable map that applies a drawn channel to the pair it was drawn for. -/
@[expose] public def applyChannel : (S × K) × (S × K → T) → T := fun p => p.2 p.1

omit [MeasurableSingletonClass T] in
public theorem measurable_applyChannel : Measurable (applyChannel : (S × K) × (S × K → T) → T) :=
  measurable_from_prod_countable_right fun a => measurable_pi_apply a

omit [MeasurableSingletonClass T] in
/--
**The central pushforward.** Drawing a state–action pair from `σ`, drawing a
deterministic channel independently, and applying one to the other is exactly
running the kernel: the law of the outcome is `κ ∘ₘ σ`.

This is eq. (7) with the state–action pair itself randomized, and it is what
turns every quantity of the purified system into the corresponding quantity of
the printed one.
-/
public theorem map_applyChannel (κ : Kernel (S × K) T) [IsMarkovKernel κ]
    (σ : Measure (S × K)) [IsFiniteMeasure σ] :
    (σ.prod (purifySeed κ)).map applyChannel = κ ∘ₘ σ := by
  ext s hs
  rw [Measure.map_apply measurable_applyChannel hs,
    Measure.prod_apply (measurable_applyChannel hs), Measure.bind_apply hs κ.aemeasurable]
  refine lintegral_congr fun a => ?_
  have hpre : (Prod.mk a ⁻¹' (applyChannel ⁻¹' s)) = purifyMap a.1 a.2 ⁻¹' s := rfl
  rw [hpre, ← Measure.map_apply (measurable_purifyMap a.1 a.2) hs,
    isPurification_purifyMap κ a.1 a.2]

/-! ## The canonical purified system

Given the printed data — a joint law `ρ` for the state and the action, and an
actuation kernel `κ` — this is *a* control system realizing them, with the seed
carried alongside. Nothing is assumed about it: it is built.
-/

/-- The joint law of the canonical purified system: the printed `ρ` on the
state–action pair, and an independently drawn deterministic channel. -/
@[expose] public noncomputable def purifiedLaw (ρ : Measure (S × K)) (κ : Kernel (S × K) T) :
    Measure ((S × K) × (S × K → T)) :=
  ρ.prod (purifySeed κ)

/-- The initial state of the canonical purified system. -/
@[expose] public def purifiedState : (S × K) × (S × K → T) → S := fun p => p.1.1

/-- The control action of the canonical purified system. -/
@[expose] public def purifiedAction : (S × K) × (S × K → T) → K := fun p => p.1.2

/-- The exogenous seed of the canonical purified system. -/
@[expose] public def purifiedSeed : (S × K) × (S × K → T) → (S × K → T) := Prod.snd

section Canonical

variable (ρ : Measure (S × K)) (κ : Kernel (S × K) T)

instance instIsProbabilityMeasurePurifiedLaw [IsProbabilityMeasure ρ] [IsMarkovKernel κ] :
    IsProbabilityMeasure (purifiedLaw ρ κ) := by
  unfold purifiedLaw; infer_instance

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
  [Fintype S] [Fintype K] in
public theorem measurable_purifiedState :
    Measurable (purifiedState : (S × K) × (S × K → T) → S) := measurable_fst.fst

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
  [Fintype S] [Fintype K] in
public theorem measurable_purifiedAction :
    Measurable (purifiedAction : (S × K) × (S × K → T) → K) := measurable_fst.snd

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
  [Fintype S] [Fintype K] in
public theorem measurable_purifiedSeed :
    Measurable (purifiedSeed : (S × K) × (S × K → T) → (S × K → T)) := measurable_snd

omit [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace T] [MeasurableSingletonClass S]
  [MeasurableSingletonClass K] [MeasurableSingletonClass T] [Fintype S] [Fintype K] in
/-- **The purified system runs the kernel.** The final state of the canonical
system is the drawn channel applied to the pair it was drawn for. -/
public theorem plantOutcome_purified :
    plantOutcome (purifyMap : S → K → (S × K → T) → T) purifiedState purifiedAction purifiedSeed
      = (applyChannel : (S × K) × (S × K → T) → T) := rfl

omit [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace T] [MeasurableSingletonClass S]
  [MeasurableSingletonClass K] [MeasurableSingletonClass T] [Fintype S] [Fintype K] in
/-- The state and the action together are the first coordinate. -/
public theorem prodMk_purified :
    (⟨purifiedState, purifiedAction⟩ : (S × K) × (S × K → T) → S × K) = Prod.fst := by
  funext p; exact Prod.mk.eta

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T] in
/-- **The seed is exogenous.** This is the printed `p_Z(z)` of eq. (7) rather than
`p(z|x,c)`: the drawn channel is independent of the state and the action it will
be applied to. It holds by construction, not by hypothesis. -/
public theorem indepFun_purified [IsProbabilityMeasure ρ] [IsMarkovKernel κ] :
    IndepFun (⟨purifiedState, purifiedAction⟩ : (S × K) × (S × K → T) → S × K)
      purifiedSeed (purifiedLaw ρ κ) := by
  rw [prodMk_purified]
  exact indepFun_prod (μ := ρ) (ν := purifySeed κ) measurable_id measurable_id

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T] in
public theorem map_purifiedSeed [IsProbabilityMeasure ρ] [IsMarkovKernel κ] :
    (purifiedLaw ρ κ).map purifiedSeed = purifySeed κ := by
  rw [purifiedLaw, purifiedSeed, Measure.map_snd_prod, measure_univ, one_smul]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T] in
public theorem map_prodMk_purified [IsProbabilityMeasure ρ] [IsMarkovKernel κ] :
    (purifiedLaw ρ κ).map (⟨purifiedState, purifiedAction⟩ : (S × K) × (S × K → T) → S × K)
      = ρ := by
  rw [prodMk_purified, purifiedLaw, Measure.map_fst_prod, measure_univ, one_smul]

end Canonical

/-! ## The printed quantities, stated with no plant and no seed -/

/-- **`ΔH_closed`, from the printed data alone**: the entropy the control process
removes from the state, computed from the joint law `ρ` of `(X, C)` and the
actuation kernel `κ`. No `F`, no `Z`. -/
@[expose] public noncomputable def kernelEntropyReduction (ρ : Measure (S × K))
    (κ : Kernel (S × K) T) : ℝ :=
  Hm[ρ.map Prod.fst] - Hm[κ ∘ₘ ρ]

/-- **`ΔH_open^c` at input distribution `ν`**, from the printed data alone: draw
the state from `ν`, apply the constant action `c`, run the kernel. -/
@[expose] public noncomputable def kernelOpenLoopReductionAt (κ : Kernel (S × K) T)
    (ν : Measure S) (c : K) : ℝ :=
  Hm[ν] - Hm[κ ∘ₘ (ν.map fun x => (x, c))]

/-- The set eq. (48) maximizes over, with `P` the set of *all* input
distributions, exactly as the sentence below eq. (48) says. -/
@[expose] public def kernelOpenLoopReductions (κ : Kernel (S × K) T) : Set ℝ :=
  {r | ∃ ν : Measure S, IsProbabilityMeasure ν ∧ ∃ c : K, kernelOpenLoopReductionAt κ ν c = r}

/-- **Eq. (48), `ΔH_open^max`**, from the printed data alone. -/
@[expose] public noncomputable def kernelOpenLoopMax (κ : Kernel (S × K) T) : ℝ :=
  sSup (kernelOpenLoopReductions κ)

/-! ## Transfer: the purified system computes the printed quantities -/

variable [Fintype T]

omit [MeasurableSingletonClass T] in
/-- **Holding the action fixed.** Running the purified plant at the constant
action `c` on an input distribution `ν` produces the same outcome law as running
the kernel on the pair distribution `ν.map (·, c)`. -/
public theorem map_purifyMap_prod (κ : Kernel (S × K) T) [IsMarkovKernel κ]
    (ν : Measure S) [IsProbabilityMeasure ν] (c : K) :
    (ν.prod (purifySeed κ)).map (fun p : S × (S × K → T) => purifyMap p.1 c p.2)
      = κ ∘ₘ (ν.map fun x => (x, c)) := by
  have hmk : Measurable (fun x : S => (x, c)) := measurable_id.prodMk measurable_const
  have hcomp : (fun p : S × (S × K → T) => purifyMap p.1 c p.2)
      = applyChannel ∘ Prod.map (fun x : S => (x, c)) id := rfl
  rw [hcomp, ← Measure.map_map measurable_applyChannel (hmk.prodMap measurable_id),
    ← Measure.map_prod_map ν (purifySeed κ) hmk measurable_id, Measure.map_id,
    map_applyChannel κ (ν.map fun x => (x, c))]

omit [MeasurableSingletonClass T] in
/-- Fixing the action and drawing the state from `ν` is drawing the pair from
`ν.map (·, c)`. -/
public theorem openLoopReductionAt_purifyMap (κ : Kernel (S × K) T) [IsMarkovKernel κ]
    (ν : Measure S) [IsProbabilityMeasure ν] (c : K) :
    openLoopReductionAt (purifyMap : S → K → (S × K → T) → T) (purifySeed κ) ν c
      = kernelOpenLoopReductionAt κ ν c := by
  rw [openLoopReductionAt, kernelOpenLoopReductionAt, map_purifyMap_prod κ ν c]

omit [MeasurableSingletonClass T] in
/-- The two families of open-loop reductions are the *same set*, so their suprema
are equal on the nose — not merely comparable. -/
public theorem openLoopReductions_purifyMap (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    openLoopReductions (purifyMap : S → K → (S × K → T) → T) (purifySeed κ)
      = kernelOpenLoopReductions κ := by
  ext r
  constructor
  · rintro ⟨ν, hν, c, rfl⟩
    exact ⟨ν, hν, c, (openLoopReductionAt_purifyMap κ ν c).symm ▸ rfl⟩
  · rintro ⟨ν, hν, c, rfl⟩
    exact ⟨ν, hν, c, openLoopReductionAt_purifyMap κ ν c⟩

omit [MeasurableSingletonClass T] in
/-- **Eq. (48) as written is the atlas's `openLoopMax` at the purified plant.** -/
public theorem openLoopMax_purifyMap (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    openLoopMax (purifyMap : S → K → (S × K → T) → T) (purifySeed κ) = kernelOpenLoopMax κ :=
  congrArg sSup (openLoopReductions_purifyMap κ)

omit [MeasurableSingletonClass T] in
/-- The canonical system's entropy reduction is the printed one. -/
public theorem entropyReduction_purified (ρ : Measure (S × K)) [IsProbabilityMeasure ρ]
    (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    entropyReduction (purifiedLaw ρ κ) purifiedState
        (plantOutcome (purifyMap : S → K → (S × K → T) → T)
          purifiedState purifiedAction purifiedSeed)
      = kernelEntropyReduction ρ κ := by
  have hstate : (purifiedLaw ρ κ).map purifiedState = ρ.map Prod.fst := by
    have : (purifiedState : (S × K) × (S × K → T) → S) = Prod.fst ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map measurable_fst measurable_fst, purifiedLaw,
      Measure.map_fst_prod, measure_univ, one_smul]
  have houtcome : (purifiedLaw ρ κ).map applyChannel = κ ∘ₘ ρ := map_applyChannel κ ρ
  rw [entropyReduction, kernelEntropyReduction, plantOutcome_purified, entropy_def, entropy_def,
    hstate, houtcome]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
  [Fintype T] in
/-- The canonical system's state–action mutual information is the printed one. -/
public theorem mutualInfo_purified (ρ : Measure (S × K)) [IsProbabilityMeasure ρ]
    (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    I[purifiedState : purifiedAction ; purifiedLaw ρ κ] = I[Prod.fst : Prod.snd ; ρ] := by
  refine IdentDistrib.mutualInfo_eq ?_
  refine ⟨(measurable_purifiedState.prodMk measurable_purifiedAction).aemeasurable,
    (measurable_fst.prodMk measurable_snd).aemeasurable, ?_⟩
  rw [map_prodMk_purified ρ κ]
  have : (⟨Prod.fst, Prod.snd⟩ : S × K → S × K) = id := by funext p; exact Prod.mk.eta
  rw [this, Measure.map_id]

/-! ## Theorem 10, at the source's own scope -/

/--
**Theorem 10 for an arbitrary actuation kernel.**

> `ΔH_closed ≤ ΔH_open^max + I(X ; C)`

Every quantity here is defined from the printed data — a joint law `ρ` for the
state and the action, and a transition kernel `κ` playing `p(x'|x,c)`. There is no
`F` and no `Z` in the statement: the plant model that
`AISafetyAtlas.Control.entropyReduction_le_openLoopMax` works in is *constructed*
from `κ` by `purifySeed`/`purifyMap`, which is what the paper's §2 says can always
be done and what `isPurification_purifyMap` proves.

`I[Prod.fst : Prod.snd ; ρ]` is the printed `I(X ; C)`, the mutual information of
the two coordinates of the joint law.
-/
public theorem kernelEntropyReduction_le_kernelOpenLoopMax
    (ρ : Measure (S × K)) [IsProbabilityMeasure ρ] (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    kernelEntropyReduction ρ κ ≤ kernelOpenLoopMax κ + I[Prod.fst : Prod.snd ; ρ] := by
  have h := entropyReduction_le_openLoopMax (purifiedLaw ρ κ)
    (purifyMap : S → K → (S × K → T) → T)
    measurable_purifiedState measurable_purifiedAction measurable_purifiedSeed
    (indepFun_purified ρ κ)
  rwa [map_purifiedSeed ρ κ, openLoopMax_purifyMap κ, entropyReduction_purified ρ κ,
    mutualInfo_purified ρ κ] at h

/-! ## Theorem 9, at the source's own scope

Theorem 9 is stated for an **open-loop** controller, whose action is drawn
independently of the state — the source's eq. (opd)
*p(x,x',c)ₒₚₑₙ = p_X(x) p_C(c) p(x'|x,c)*. On the printed data that is `ρ = ν ⊗ p_C`
for an input law `ν` and an action law `pC`, and it is the only extra structure the
theorem needs.
-/

section OpenLoopCanonical

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
  [Fintype S] [Fintype K] [Fintype T] in
/-- **Independence pulls back along a measurable map.** If two functions are
independent under a pushforward, their composites with the pushing map are
independent under the original measure. -/
public theorem indepFun_comp_of_map {Ω Ω' A B : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [MeasurableSpace A] [MeasurableSpace B] {μ : Measure Ω} {f : Ω → Ω'} {g : Ω' → A} {h : Ω' → B}
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h)
    (H : IndepFun g h (μ.map f)) : IndepFun (g ∘ f) (h ∘ f) μ := by
  rw [indepFun_iff_measure_inter_preimage_eq_mul] at H ⊢
  intro s t hs ht
  have hgs : MeasurableSet (g ⁻¹' s) := hg hs
  have hht : MeasurableSet (h ⁻¹' t) := hh ht
  have hinter : (g ∘ f) ⁻¹' s ∩ (h ∘ f) ⁻¹' t = f ⁻¹' (g ⁻¹' s ∩ h ⁻¹' t) := rfl
  rw [hinter, ← Measure.map_apply hf (hgs.inter hht),
    show (g ∘ f) ⁻¹' s = f ⁻¹' (g ⁻¹' s) from rfl, ← Measure.map_apply hf hgs,
    show (h ∘ f) ⁻¹' t = f ⁻¹' (h ⁻¹' t) from rfl, ← Measure.map_apply hf hht]
  exact H s t hs ht

variable (ν : Measure S) (pC : Measure K) (κ : Kernel (S × K) T)

/-- Regroup the canonical system so that the action stands alone. -/
@[expose] public def purifiedRegroup :
    (S × K) × (S × K → T) → (S × (S × K → T)) × K :=
  fun p => ((p.1.1, p.2), p.1.2)

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
  [Fintype S] [Fintype K] [Fintype T] in
public theorem measurable_purifiedRegroup :
    Measurable (purifiedRegroup : (S × K) × (S × K → T) → (S × (S × K → T)) × K) :=
  (measurable_fst.fst.prodMk measurable_snd).prodMk measurable_fst.snd

/-- Under an open-loop law the three factors really are a product, in any
grouping. -/
public theorem map_purifiedRegroup [IsProbabilityMeasure ν] [IsProbabilityMeasure pC]
    [IsMarkovKernel κ] :
    (purifiedLaw (ν.prod pC) κ).map purifiedRegroup
      = (ν.prod (purifySeed κ)).prod pC := by
  refine Measure.ext_of_singleton fun q => ?_
  obtain ⟨⟨x, z⟩, c⟩ := q
  have hpre : (purifiedRegroup : (S × K) × (S × K → T) → (S × (S × K → T)) × K) ⁻¹'
      {((x, z), c)} = ({x} ×ˢ {c} : Set (S × K)) ×ˢ ({z} : Set (S × K → T)) := by
    ext p
    simp [purifiedRegroup, Prod.ext_iff, and_comm, and_assoc, and_left_comm]
  rw [Measure.map_apply measurable_purifiedRegroup (MeasurableSet.singleton _), hpre,
    purifiedLaw, Measure.prod_prod, Measure.prod_prod,
    show ({((x, z), c)} : Set ((S × (S × K → T)) × K))
      = (({x} ×ˢ {z} : Set (S × (S × K → T)))) ×ˢ ({c} : Set K) by
        simp [Set.singleton_prod_singleton],
    Measure.prod_prod, Measure.prod_prod]
  ring

/-- **The open-loop condition, eq. (opd), holds in the canonical system by
construction.** The action is independent of the state *and* of the seed. -/
public theorem indepFun_purified_openLoop [IsProbabilityMeasure ν] [IsProbabilityMeasure pC]
    [IsMarkovKernel κ] :
    IndepFun purifiedAction
      (⟨purifiedState, purifiedSeed⟩ : (S × K) × (S × K → T) → S × (S × K → T))
      (purifiedLaw (ν.prod pC) κ) := by
  have hbase : IndepFun (Prod.snd : (S × (S × K → T)) × K → K)
      (Prod.fst : (S × (S × K → T)) × K → S × (S × K → T))
      ((purifiedLaw (ν.prod pC) κ).map purifiedRegroup) := by
    rw [map_purifiedRegroup ν pC κ]
    exact (indepFun_prod (μ := ν.prod (purifySeed κ)) (ν := pC)
      measurable_id measurable_id).symm
  exact indepFun_comp_of_map measurable_purifiedRegroup measurable_snd measurable_fst hbase

/-- Dropping the action from an open-loop law leaves the state and the seed
independent, with their own laws. -/
public theorem map_dropAction [IsProbabilityMeasure ν] [IsProbabilityMeasure pC]
    [IsMarkovKernel κ] :
    (purifiedLaw (ν.prod pC) κ).map
        (⟨purifiedState, purifiedSeed⟩ : (S × K) × (S × K → T) → S × (S × K → T))
      = ν.prod (purifySeed κ) := by
  have hcomp : (⟨purifiedState, purifiedSeed⟩ : (S × K) × (S × K → T) → S × (S × K → T))
      = Prod.fst ∘ purifiedRegroup := rfl
  rw [hcomp, ← Measure.map_map measurable_fst measurable_purifiedRegroup,
    map_purifiedRegroup ν pC κ, Measure.map_fst_prod, measure_univ, one_smul]

/-- The canonical open-loop system computes the printed `ΔH_open^c`. -/
public theorem openLoopReduction_purified [IsProbabilityMeasure ν] [IsProbabilityMeasure pC]
    [IsMarkovKernel κ] (c : K) :
    openLoopReduction (purifiedLaw (ν.prod pC) κ) (purifyMap : S → K → (S × K → T) → T)
        purifiedState purifiedSeed c
      = kernelOpenLoopReductionAt κ ν c := by
  have hstate : (purifiedLaw (ν.prod pC) κ).map purifiedState = ν := by
    have : (purifiedState : (S × K) × (S × K → T) → S)
        = Prod.fst ∘ (⟨purifiedState, purifiedSeed⟩ : (S × K) × (S × K → T) → S × (S × K → T)) :=
      rfl
    rw [this, ← Measure.map_map measurable_fst
      (measurable_purifiedState.prodMk measurable_purifiedSeed),
      map_dropAction ν pC κ, Measure.map_fst_prod, measure_univ, one_smul]
  have houtcome : (purifiedLaw (ν.prod pC) κ).map
      (fun ω => purifyMap (purifiedState ω) c (purifiedSeed ω))
      = κ ∘ₘ (ν.map fun x => (x, c)) := by
    have hcomp : (fun ω : (S × K) × (S × K → T) => purifyMap (purifiedState ω) c (purifiedSeed ω))
        = (fun p : S × (S × K → T) => purifyMap p.1 c p.2) ∘
          (⟨purifiedState, purifiedSeed⟩ : (S × K) × (S × K → T) → S × (S × K → T)) := rfl
    have hf : Measurable (fun p : S × (S × K → T) => purifyMap p.1 c p.2) :=
      measurable_applyChannel.comp
        ((measurable_id.prodMk measurable_const).prodMap measurable_id)
    rw [hcomp, ← Measure.map_map hf
      (measurable_purifiedState.prodMk measurable_purifiedSeed),
      map_dropAction ν pC κ, map_purifyMap_prod κ ν c]
  rw [openLoopReduction, openLoopEntropy, kernelOpenLoopReductionAt, entropy_def, entropy_def,
    hstate, houtcome]

/--
**Theorem 9 for an arbitrary actuation kernel.**

> `ΔH_open ≤ max over c of ΔH_open^c`

An open-loop controller draws its action from *some* law `p_C` independently of the
state — the source's eq. (opd). No such controller beats the best single action.
Stated on the printed data only: a state law `ν`, an action law `p_C`, and the
kernel `κ`.
-/
public theorem kernelEntropyReduction_le_iSup_kernelOpenLoop [Nonempty K]
    (ν : Measure S) [IsProbabilityMeasure ν] (pC : Measure K) [IsProbabilityMeasure pC]
    (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    kernelEntropyReduction (ν.prod pC) κ ≤ ⨆ c : K, kernelOpenLoopReductionAt κ ν c := by
  have h := entropyReduction_le_iSup_openLoopReduction (purifiedLaw (ν.prod pC) κ)
    (purifyMap : S → K → (S × K → T) → T)
    measurable_purifiedState measurable_purifiedAction measurable_purifiedSeed
    (indepFun_purified_openLoop ν pC κ)
  rw [entropyReduction_purified (ν.prod pC) κ] at h
  simpa only [openLoopReduction_purified ν pC κ] using h

omit [MeasurableSingletonClass T] in
/-- A pure controller is a Dirac action law, and running the kernel on it is
running the kernel at the fixed action. -/
public theorem prod_dirac_eq_map (ν : Measure S) [IsProbabilityMeasure ν] (c : K) :
    ν.prod (Measure.dirac c) = ν.map fun x => (x, c) := by
  have hmk : Measurable (fun x : S => (x, c)) := measurable_id.prodMk measurable_const
  refine Measure.ext_of_singleton fun q => ?_
  obtain ⟨x, c'⟩ := q
  rw [Measure.map_apply hmk (MeasurableSet.singleton _),
    show ({(x, c')} : Set (S × K)) = ({x} : Set S) ×ˢ ({c'} : Set K) by
      simp [Set.singleton_prod_singleton],
    Measure.prod_prod, Measure.dirac_apply' _ (MeasurableSet.singleton c')]
  by_cases hc : c' = c
  · subst hc
    rw [show (fun y : S => (y, c')) ⁻¹' (({x} : Set S) ×ˢ ({c'} : Set K)) = ({x} : Set S) by
      ext y; simp]
    simp
  · have hc' : c ≠ c' := Ne.symm hc
    rw [show (fun y : S => (y, c)) ⁻¹' (({x} : Set S) ×ˢ ({c'} : Set K)) = (∅ : Set S) by
      ext y; simp [hc']]
    simp [hc']

omit [MeasurableSingletonClass T] [Fintype T] in
/-- Under a pure controller the closed-loop reduction *is* the open-loop reduction
at that action. -/
public theorem kernelEntropyReduction_dirac (ν : Measure S) [IsProbabilityMeasure ν]
    (κ : Kernel (S × K) T) [IsMarkovKernel κ] (c : K) :
    kernelEntropyReduction (ν.prod (Measure.dirac c)) κ = kernelOpenLoopReductionAt κ ν c := by
  rw [kernelEntropyReduction, kernelOpenLoopReductionAt, prod_dirac_eq_map ν c]
  congr 1
  rw [← prod_dirac_eq_map ν c, Measure.map_fst_prod, measure_univ, one_smul]

omit [MeasurableSingletonClass T] [Fintype T] in
/--
**Theorem 9's attainment clause, for an arbitrary actuation kernel.** The paper's

> the maximum decrease of entropy achieved by a particular subdynamics of control
> variable *ĉ = arg max over c of ΔH_open^c* is *open-loop optimal*

Some **pure** controller — an action law concentrated on a single `ĉ` — reaches the
supremum, so the bound above is attained and not merely an upper bound.
-/
public theorem exists_kernelEntropyReduction_dirac_eq_iSup [Nonempty K]
    (ν : Measure S) [IsProbabilityMeasure ν] (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    ∃ c : K, kernelEntropyReduction (ν.prod (Measure.dirac c)) κ
      = ⨆ k : K, kernelOpenLoopReductionAt κ ν k := by
  obtain ⟨c, hc⟩ := exists_eq_ciSup_of_finite (f := fun k : K => kernelOpenLoopReductionAt κ ν k)
  exact ⟨c, (kernelEntropyReduction_dirac ν κ c).trans hc⟩

end OpenLoopCanonical

end AISafetyAtlas.Control
