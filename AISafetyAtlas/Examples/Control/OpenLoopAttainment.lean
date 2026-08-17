module

public import AISafetyAtlas.Control.OpenLoopAttainment

/-!
# Equation (48)'s maximum — worked consequences

Two readings of `AISafetyAtlas.Control.OpenLoopAttainment`.

1. **`sSup` and `max` agree.** `open_loop_supremum_is_a_maximum` says the value
   the atlas computes as a supremum is itself one of the reductions, so nothing
   is lost against the printed `max`.
2. **Theorem 10 with a witness.** `feedback_bounded_by_a_realized_open_loop`
   states the paper's main result with the right-hand side realized by an
   explicit input distribution and action, which is what eq. (48)'s notation
   promises.
-/

namespace AISafetyAtlas.Examples.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.Control AISafetyAtlas.InformationTheory

universe uS uK uT

variable {S : Type uS} {K : Type uK} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
variable [Fintype S] [Fintype K] [Fintype T]

omit [MeasurableSingletonClass K] in
/--
**The supremum is a maximum.** Some input distribution and some action realize
eq. (48)'s value, so reading `ΔH_open^max` as `sSup` costs nothing.
-/
public theorem open_loop_supremum_is_a_maximum [Nonempty S] [Nonempty K]
    (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    kernelOpenLoopMax κ ∈ kernelOpenLoopReductions κ :=
  (isGreatest_kernelOpenLoopMax κ).1

/--
**One bit gathered is worth at most one bit of improvement — against a realized
open-loop controller.** Touchette–Lloyd's stated main result, with the printed
maximum exhibited rather than approached.
-/
public theorem feedback_bounded_by_a_realized_open_loop [Nonempty S] [Nonempty K]
    (ρ : Measure (S × K)) [IsProbabilityMeasure ρ]
    (κ : Kernel (S × K) T) [IsMarkovKernel κ] :
    ∃ (ν : Measure S), IsProbabilityMeasure ν ∧ ∃ c : K,
      kernelEntropyReduction ρ κ
        ≤ kernelOpenLoopReductionAt κ ν c + I[Prod.fst : Prod.snd ; ρ] :=
  exists_kernelEntropyReduction_le_at_max ρ κ

end AISafetyAtlas.Examples.Control
