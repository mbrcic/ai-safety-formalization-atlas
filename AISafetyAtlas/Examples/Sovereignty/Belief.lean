module

public import AISafetyAtlas.Sovereignty.Belief

/-!
# The agent that believes what it is told

`trusting` is print's instantiation of `C1`: the belief is the received
message, the action is the belief, and the belief-relative score rewards
exactly the action the belief names. Both maps are the identity, which is why
print calls its proof "instantiate the two maps".

The agent is decisive at every belief -- `decisive` is a field of
`DoxasticAgent` and is discharged here by a two-case split -- and
`trusting_not_sovereign` reads back that the sender forces `{true}` while the
agent does not. Nothing about the agent is defective: it has the same move set
as the sender and takes the best action it can see at every belief it holds.

`coin` is the other side, `B5`: a receiver that knows the experiment and
conditions on its signal. `coin_no_forced_certainty` is print's consequence at
the simplest experiment -- a fair prior cannot be turned into certainty at
every signal, because the posteriors average back to the prior.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Belief

open AISafetyAtlas.Sovereignty

/-- **The agent that believes its messages.** Belief is the message, the action
is the belief, and an action scores one exactly when it matches the belief. -/
@[expose] public def trusting : DoxasticAgent Bool Bool Bool ℕ where
  form o := o
  dec b := b
  value b a := if a = b then 1 else 0
  decisive b a := by by_cases h : a = b <;> simp [h]

/-- **The sender installs `true`.** -/
public theorem sender_forces_true :
    Forces trusting.channel {false} ({true} : Set Bool) :=
  trusting.sender_forces true

/-- **And the sender installs `false`.** Full binary control of the action. -/
public theorem sender_forces_false :
    Forces trusting.channel {false} ({false} : Set Bool) :=
  trusting.sender_forces false

/--
**`C1`: the agent forces neither.**

Its decisions are maximal at every belief it holds, and it still cannot
guarantee any action, because the belief is not its own.
-/
public theorem trusting_not_sovereign :
    Forces trusting.channel {false} ({true} : Set Bool) ∧
      ¬ Forces trusting.channel {true} ({true} : Set Bool) :=
  trusting.beliefDecisive_not_sovereign (o := true) (o' := false) (by decide)

/-- **Nor the other one.** -/
public theorem trusting_not_sovereign_false :
    ¬ Forces trusting.channel {true} ({false} : Set Bool) := fun h =>
  absurd (trusting.mem_of_agent_forces h true) (by decide)

/-! ## `B5`: a fair prior cannot be argued into certainty -/

open scoped ENNReal

/-- A fair prior over two worlds, and a signal that reveals the world. -/
@[expose] public noncomputable def coin : SignalExperiment Bool Bool where
  prior _ := 1 / 2
  law w s := if s = w then 1 else 0
  prior_sum := by
    simp only [Fintype.sum_bool, one_div]
    rw [ENNReal.inv_two_add_inv_two]
  law_sum w := by cases w <;> simp

/--
**`B5`: no signal policy installs certainty.**

A belief that is held after every signal that can occur must be the prior, so
a receiver with a fair prior who knows the experiment cannot be brought to
certainty about either world whatever the signal is.
-/
public theorem coin_no_forced_certainty (ν : Bool → ℝ≥0∞) (hν : ν true = 1)
    (h : ∀ s, coin.marginal s ≠ 0 → coin.posterior s true = ν true) : False := by
  have hprior := coin.eq_prior_of_constant_posterior ν true h
  rw [hν] at hprior
  simp only [coin] at hprior
  exact absurd hprior.symm (by simp)

/-! ## What the sender's control actually covers -/

/-- **Every action the trusting agent ever takes is one the sender installs.**

`sender_forces_range` quantifies over the range of the composite; here the
composite is the identity, so the range is everything and the sender's control
is total. The agent has no action outside the sender's reach. -/
public theorem trusting_sender_forces_every_action (x : Bool) :
    Forces trusting.channel {false} ({x} : Set Bool) :=
  trusting.sender_forces_range x ⟨x, rfl⟩

/-! ## The signal law sits at its ceiling -/

/-- **The revealing signal is as informative as a signal can be.** At each world
the matching signal carries all the mass, and `law_le_one` is the statement that
nothing exceeds it -- so this experiment attains the bound rather than merely
respecting it. -/
public theorem coin_law_at_ceiling (w : Bool) :
    coin.law w w = 1 ∧ ∀ s, coin.law w s ≤ 1 :=
  ⟨by simp [coin], fun s => SignalExperiment.law_le_one coin w s⟩

end AISafetyAtlas.Examples.Sovereignty.Belief
