module

import AISafetyAtlas.Wireheading.ObservationLimits

/-!
# The observation limit is a boundary, not a blanket denial

`Wireheading.ObservationLimits` says the true return does not factor through the
observed history *over a class containing a return-disagreeing complement pair*.
A negative result whose hypothesis were unsatisfiable would say nothing, and one
whose hypothesis were unavoidable would be a blanket denial. Neither holds.

Three things are exhibited:

* the unrestricted failure, on a concrete one-state system;
* the witness pair, with its two returns computed — `0` and `1`;
* a restricted class on which the same return **is** knowable, which is the
  escape route the class-relative statement is for.

The third is the one that keeps the first honest.
-/

namespace AISafetyAtlas.Examples.Wireheading.ObservationLimits

open AISafetyAtlas.Knowledge
open AISafetyAtlas.Wireheading.CRMDP
open AISafetyAtlas.Wireheading.ObservationLimits

/-! ## A one-state, one-action system

Nothing about the failure depends on rich dynamics: the whole obstruction lives
in the reward channel, so the smallest possible transition structure exhibits it.
-/

private def step : Unit → Unit → Unit := fun _ _ => ()

private def alwaysStay : Policy Unit Unit := fun _ => ()

/-! ## The unrestricted failure

Horizon `1`, one observed step. -/

example :
    ¬ Knowable
        (observedHistory step alwaysStay () 1)
        (trueReturn step 1 () alwaysStay) :=
  not_knowable_trueReturn step alwaysStay () 1 1 Nat.one_pos

/-- The same at every positive horizon, so it is not an artifact of `t = 1`. -/
example (t : ℕ) (positive : 0 < t) :
    ¬ Knowable
        (observedHistory step alwaysStay () 5)
        (trueReturn step t () alwaysStay) :=
  not_knowable_trueReturn step alwaysStay () 5 t positive

/-! ## The witness, with both returns computed

`zeroEnv` pays nothing; its complement pays the full horizon. The two are
indistinguishable on the channel, which is what makes the pair a certificate
rather than an assertion. -/

example : returnOver step 1 () (zeroEnv Unit) alwaysStay = 0 :=
  returnOver_zeroEnv step 1 () alwaysStay

example : returnOver step 1 () (zeroEnv Unit).complement alwaysStay = 1 := by
  rw [returnOver_zeroEnv_complement]
  norm_num

/-- And the observed histories they generate are equal. -/
example :
    observedHistory step alwaysStay () 1 (zeroEnv Unit)
      = observedHistory step alwaysStay () 1 (zeroEnv Unit).complement :=
  (history_complement step (zeroEnv Unit) alwaysStay () 1).symm

/-! ## The escape route: restrict the class

The class-relative statement needs a complement pair *inside* the class. A class
that does not contain one is not covered — and here is one where the return is
exactly knowable, by a constant decoder.

This is the precise sense in which the result is a boundary. "The true return is
unknowable from observation" is a statement about an environment class, not about
observation as such. -/

example (μ : Env Unit) (t : ℕ) :
    Knowable
      (fun ν : Subtype (fun ν : Env Unit => ν = μ) =>
        observedHistory step alwaysStay () 1 ν.1)
      (fun ν : Subtype (fun ν : Env Unit => ν = μ) =>
        trueReturn step t () alwaysStay ν.1) :=
  ⟨fun _ => trueReturn step t () alwaysStay μ, fun ν => by
    show trueReturn step t () alwaysStay ν.1 = trueReturn step t () alwaysStay μ
    rw [ν.2]⟩

/-! ## What is not shown

The restricted class above is degenerate: one environment, so nothing is in
question. It marks the direction of the escape, not its practicality. Which
*useful* classes omit every return-disagreeing complement pair is a modelling
question, and a class closed under `Env.complement` — as the full class is by
construction — can never be one of them. -/

end AISafetyAtlas.Examples.Wireheading.ObservationLimits
