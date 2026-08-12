module

public import AISafetyAtlas.Wireheading.CRMDP
public import AISafetyAtlas.Knowledge

/-!
# What the observed history settles about the true return

`Wireheading.CRMDP` proves that an environment and its complement generate the
*same* observed history under every policy (`history_complement`) while their
true returns sum to the horizon (`return_add_complement`). Those are the source's
two steps, already formalized.

This module reads them through `Knowledge.Knowable`. Fix the dynamics, a policy,
a start state and a horizon; treat the **environment** as the unknown. Then the
observed history is an observation map and the true return is a target property,
and the complement pair is exactly a collision: same observation, different
target. `Knowledge.not_knowable_of_collision` does the rest.

## What is stated, precisely

> As a function of the unknown environment, the true finite-horizon return does
> not factor through the observed history that a fixed policy receives.

The quantification is over environments, not over histories or agents. Read the
statement as: *no decoder from observed histories to reals is correct on every
environment in the class*, not as "the agent cannot compute its own return".

## Two layers, and why the class-relative one is primary

`not_knowable_trueReturn_of_complement_mem` asks only that some admissible
environment class contain a complement pair whose returns differ. That is the
real hypothesis: the full `Env State` class is *sufficient*, not necessary.
Stating it class-relatively makes the escape routes exact — restrict the class
until no indistinguishable return-disagreeing pair survives, add information,
relax exactness, or move to a prior.

`not_knowable_trueReturn` is then the unrestricted corollary: over the whole of
`Env State`, the zero environment and its complement witness the failure at every
positive horizon.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Boundary** | `not_knowable_trueReturn_of_complement_mem` | A complement pair inside a class defeats every decoder on that class |
| **Certificate** | `complementWitness` | The pair itself, as an `IndistinguishabilityWitness` |
| **Corollary** | `not_knowable_trueReturn` | The unrestricted class, at any positive horizon |

## Explicit non-claims

- **The impossibility is the source's.** Everitt, Krakovna, Orseau, Hutter and
  Legg supply both ingredients; `CRMDP` already formalizes them. What is added
  here is the factorization reading, the certificate, and the import edge from
  `Wireheading` to `Knowledge`. No novelty is claimed.
- **Not** a claim that restricted environment classes fail: the theorem is
  explicitly relative to a class, and a class without a return-disagreeing
  complement pair is not covered by it.
- **Not** a claim about approximate, probabilistic, or prior-conditional
  estimation. `Knowable` is exact recovery on the nose.
- **Not** a claim that every practical reward channel realizes the complement
  construction.
- **Not** a statement about the agent's introspection, awareness, or any
  phenomenal reading.
- Inherits every non-claim of `Wireheading.CRMDP`, in particular deterministic
  transitions and one fixed transition per model.

Survey / landscape: consumer of BY-039 and `LAND-KNOW-001`; recorded as
`LAND-CRMDP-KNOW-001`. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Wireheading.ObservationLimits

open AISafetyAtlas.Knowledge
open AISafetyAtlas.Wireheading.CRMDP

variable {State Action : Type*}

/-! ## The observation and the target -/

/--
The observation: the history a fixed policy sees after `n` steps, as a function
of the unknown environment.
-/
@[expose] public def observedHistory (transition : State → Action → State)
    (π : Policy State Action) (s₀ : State) (n : ℕ) (μ : Env State) :
    History State Action :=
  historyUpTo transition μ π s₀ n

/--
The target: the true finite-horizon return, as a function of the unknown
environment. This is the quantity the observed reward is supposed to track and,
under corruption, does not.
-/
@[expose] public def trueReturn (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (π : Policy State Action) (μ : Env State) : ℝ :=
  returnOver transition t s₀ μ π

/-! ## The class-relative boundary -/

/--
The negative certificate: an environment and its complement, both in the class,
sharing an observed history and disagreeing on the true return.

A consumer inspects this rather than the bare `¬ Knowable`, because it names
*which* pair the observation fails to resolve.
-/
@[expose] public def complementWitness (transition : State → Action → State)
    (π : Policy State Action) (s₀ : State) (n t : ℕ)
    {C : Env State → Prop} {μ : Env State}
    (memEnv : C μ) (memComplement : C μ.complement)
    (returnsDiffer :
      returnOver transition t s₀ μ π ≠ returnOver transition t s₀ μ.complement π) :
    IndistinguishabilityWitness
      (fun ν : Subtype C => observedHistory transition π s₀ n ν.1)
      (fun ν : Subtype C => trueReturn transition t s₀ π ν.1) where
  left := ⟨μ, memEnv⟩
  right := ⟨μ.complement, memComplement⟩
  sameObservation := (history_complement transition μ π s₀ n).symm
  propertyDiffers := returnsDiffer

/--
**The boundary, class-relative.** If an admissible environment class contains an
environment together with its complement, and their true returns differ, then no
decoder from observed histories recovers the true return on that class.

The hypothesis is the whole content: it is not the size of the class that
matters but whether it contains a return-disagreeing complement pair.
-/
public theorem not_knowable_trueReturn_of_complement_mem
    (transition : State → Action → State) (π : Policy State Action) (s₀ : State)
    (n t : ℕ) {C : Env State → Prop} {μ : Env State}
    (memEnv : C μ) (memComplement : C μ.complement)
    (returnsDiffer :
      returnOver transition t s₀ μ π ≠ returnOver transition t s₀ μ.complement π) :
    ¬ Knowable
        (fun ν : Subtype C => observedHistory transition π s₀ n ν.1)
        (fun ν : Subtype C => trueReturn transition t s₀ π ν.1) :=
  not_knowable_of_witness
    (complementWitness transition π s₀ n t memEnv memComplement returnsDiffer)

/-! ## The unrestricted corollary -/

/--
The environment that pays nothing anywhere and reports its reward unchanged.

Its complement pays `1` everywhere, and by `Env.observed_complement` the two are
indistinguishable on the channel.
-/
@[expose] public def zeroEnv (State : Type*) : Env State where
  trueReward := fun _ => ⟨0, ⟨le_rfl, zero_le_one⟩⟩
  corruption := fun _ x => x

/-- The zero environment returns nothing over any horizon. -/
public theorem returnOver_zeroEnv (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (π : Policy State Action) :
    returnOver transition t s₀ (zeroEnv State) π = 0 := by
  simp [returnOver, zeroEnv]

/-- Hence its complement returns the whole horizon, by the source's equation (3). -/
public theorem returnOver_zeroEnv_complement (transition : State → Action → State)
    (t : ℕ) (s₀ : State) (π : Policy State Action) :
    returnOver transition t s₀ (zeroEnv State).complement π = (t : ℝ) := by
  have hsum := return_add_complement transition t s₀ (zeroEnv State) π
  rw [returnOver_zeroEnv transition t s₀ π] at hsum
  linarith

/--
**The unrestricted corollary.** Over the full environment class, the true
finite-horizon return does not factor through the observed history, at every
positive horizon.

Proved directly rather than through `Subtype (fun _ => True)`, which would only
add plumbing. The witness is `zeroEnv` and its complement, returning `0` and `t`.
-/
public theorem not_knowable_trueReturn (transition : State → Action → State)
    (π : Policy State Action) (s₀ : State) (n t : ℕ) (horizonPos : 0 < t) :
    ¬ Knowable
        (observedHistory transition π s₀ n)
        (trueReturn transition t s₀ π) := by
  refine not_knowable_of_collision
    (ω₁ := zeroEnv State) (ω₂ := (zeroEnv State).complement)
    (history_complement transition (zeroEnv State) π s₀ n).symm ?_
  show returnOver transition t s₀ (zeroEnv State) π
      ≠ returnOver transition t s₀ (zeroEnv State).complement π
  rw [returnOver_zeroEnv, returnOver_zeroEnv_complement]
  exact ne_of_lt (by exact_mod_cast horizonPos)

end AISafetyAtlas.Wireheading.ObservationLimits
