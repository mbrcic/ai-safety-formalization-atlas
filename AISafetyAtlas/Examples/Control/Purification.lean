module

public import AISafetyAtlas.Control.Purification

/-!
# Purification — worked consequences

Three readings of `AISafetyAtlas.Control.Purification`.

1. **The paper's §2 remark, as a theorem.** `every_kernel_is_purifiable` is the
   sentence *"any non-deterministic channel … can be represented abstractly as a
   randomly selected deterministic channel"* with a witness attached.
2. **Theorem 10 with the feedback term removed.** `blind_control_le_open_loop`
   reads the kernel-scope Theorem 10 at `I(X ; C) = 0`: a controller whose action
   carries no information about the state does no better than the best open-loop
   controller on the best input law. This is the statement the atlas's Ashby row
   meets.
3. **Theorem 9 as a two-sided fact.** `pure_control_is_open_loop_optimal` puts the
   bound and its attainment on one line: the supremum over pure actions both
   dominates every open-loop controller and is realized by one of them.
-/

namespace AISafetyAtlas.Examples.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.Control AISafetyAtlas.InformationTheory

universe uS uK uT

variable {S : Type uS} {K : Type uK} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
variable [Fintype S] [Fintype K] [Fintype T]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
  [Fintype T] in
/--
**Every actuation channel is a randomly selected deterministic channel.** The
paper states this in §2 as a remark and moves on; here it is a theorem with an
explicit witness, and it is what lets Theorems 9 and 10 be stated for an arbitrary
kernel rather than for a plant already written in purified form.
-/
public theorem every_kernel_is_purifiable (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    ∃ (F : S → K → (S × K → T) → T) (η : Measure (S × K → T)),
      IsProbabilityMeasure η ∧ (∀ x c, Measurable (F x c)) ∧ IsPurification F η κ :=
  exists_isPurification κ

/--
**A blind controller cannot beat open-loop control.** Theorem 10 at
`I(X ; C) = 0`, stated for an arbitrary actuation kernel: if the action carries no
information about the state, the entropy the closed loop removes is capped by the
printed `ΔH_open^max`.

The same conclusion `AISafetyAtlas.Control.entropy_ge_of_sensor` reaches from
Ashby's law — see the provenance notes for where the two meet.
-/
public theorem blind_control_le_open_loop (ρ : Measure (S × K)) [IsProbabilityMeasure ρ]
    (κ : Kernel (S × K) T) [IsMarkovKernel κ]
    (hblind : I[Prod.fst : Prod.snd ; ρ] = 0) :
    kernelEntropyReduction ρ κ ≤ kernelOpenLoopMax κ := by
  have h := kernelEntropyReduction_le_kernelOpenLoopMax ρ κ
  rwa [hblind, add_zero] at h

/--
**A pure controller is open-loop optimal, both halves at once.** For an arbitrary
actuation kernel: no open-loop controller beats the best single action, and some
single action achieves that bound. The paper's *ĉ = arg max* exists.
-/
public theorem pure_control_is_open_loop_optimal [Nonempty K]
    (ν : Measure S) [IsProbabilityMeasure ν] (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    (∀ pC : Measure K, ∀ _ : IsProbabilityMeasure pC,
        kernelEntropyReduction (ν.prod pC) κ ≤ ⨆ c : K, kernelOpenLoopReductionAt κ ν c)
      ∧ ∃ c : K, kernelEntropyReduction (ν.prod (Measure.dirac c)) κ
          = ⨆ k : K, kernelOpenLoopReductionAt κ ν k :=
  ⟨fun pC _ => kernelEntropyReduction_le_iSup_kernelOpenLoop ν pC κ,
    exists_kernelEntropyReduction_dirac_eq_iSup ν κ⟩

end AISafetyAtlas.Examples.Control
