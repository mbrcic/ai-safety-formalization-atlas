module

public import AISafetyAtlas.Sovereignty.Separations
public import Mathlib.Data.ENNReal.Inv
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Acting on one's own beliefs, while somebody else writes them

The proposal's `C1` is a limitation on belief-relative notions of autonomy, and
it names the notion it is a limitation on: Rakow's *autonomous-decisive system*
[EPTCS 371 (2022), 103-119, arXiv:2209.14038], where a doxastic strategy
`s_d : B⁺ → Act` decides on the history of beliefs and the belief formation
function `ℬ` maps histories of observations to beliefs.

`DoxasticAgent` is that pair flattened to one step: a belief formation
`form : O → Bel`, a decision `dec : Bel → Act` that reads nothing but the
belief, and a belief-relative score `value : Bel → Act → R` with `decisive`
saying the decision is maximal at every belief. `decisive` is a *field*, not a
hypothesis to be discharged, because print's construction supplies it by
instantiation and because the point of the result is that it costs nothing.

`channel` is the two-party game form in which the observation is the other
party's move: the sender commits an observation, the agent's own commitment is
read by nothing, and the outcome is the action. Then

* `sender_forces`: the sender forces the action singleton at every message;
* `mem_of_agent_forces`: **every** set the agent forces contains the whole
  range of the sender's control, so the agent forces no proper part of it;
* `beliefDecisive_not_sovereign`: at two messages with different actions, the
  sender forces a singleton that the agent does not.

`B5` is the other half of the module and points the other way: a receiver that
knows the experiment and updates by Bayes' rule has posteriors that average
back to its prior, `sum_marginal_mul_posterior`, so a sender cannot install one
fixed belief at every signal unless that belief was already the prior --
`eq_prior_of_constant_posterior`. The two results are not in tension. `C1` is
about an agent that takes its message *as* its belief; `B5` is about one that
knows the experiment generating the message and conditions on it.

## What this is not

It is not a defect in the problem Rakow formalizes. Rakow's question is whether
a system can act on the content of its beliefs at all, and Definition 5 there
answers it relative to a fixed belief formation. Nothing in that definition
claims the belief formation is the system's own, and `C1` is the observation
that a notion silent about the provenance of beliefs is silent about
sovereignty over them. The scope difference is real and is in both directions:
this module has no temporal logic, no goal list and no dominance ordering, so
it does not state Rakow's notion; and Rakow has no second party, so it does not
state this.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
proposal is unpublished and nothing here is coverage of it or of Rakow.
-/

namespace AISafetyAtlas.Sovereignty

open scoped ENNReal

universe u v w r

/--
**An agent that decides on its beliefs.** `form` builds the belief from what
was received, `dec` reads nothing but the belief, and `decisive` says the
decision maximizes the belief-relative score -- Rakow's "best according to the
simulation within the belief", with the simulation abstracted to its score.
-/
public structure DoxasticAgent (O : Type u) (Bel : Type v) (Act : Type w)
    (R : Type r) [Preorder R] where
  /-- Belief formation: what is believed after receiving `o`. -/
  form : O → Bel
  /-- The doxastic decision: a function of the belief alone. -/
  dec : Bel → Act
  /-- How good an action looks from inside a belief. -/
  value : Bel → Act → R
  /-- The decision is maximal at every belief. -/
  decisive : ∀ b a, value b a ≤ value b (dec b)

namespace DoxasticAgent

variable {O : Type u} {Bel : Type v} {Act : Type w} {R : Type r} [Preorder R]

/--
**The channel game.** `false` is the sender, `true` is the agent. Both commit a
message, only the sender's is read, and the outcome is the action the agent
takes on the belief that message forms.

The agent's strategy type is not empty and not a singleton: it has exactly the
moves the sender has, and they do nothing. That is the content -- the agent is
a player with a full repertoire and no effect.
-/
@[expose] public def channel (D : DoxasticAgent O Bel Act R) :
    GameForm.{0, w, u} Bool Act where
  strategy _ := O
  outcome s := D.dec (D.form (s false))

/-- **The sender forces the action**, at every message it might send. -/
public theorem sender_forces (D : DoxasticAgent O Bel Act R) (o : O) :
    Forces D.channel {false} {D.dec (D.form o)} := by
  refine ⟨fun _ => show D.channel.strategy false from o, fun s hs => ?_⟩
  have hso : s false = o := hs ⟨false, rfl⟩
  show D.dec (D.form (s false)) ∈ _
  rw [hso]
  rfl

/--
**Whatever the agent forces, it forces at every message.**

The agent's commitment does not enter the outcome, so any target it can
guarantee must already contain the action at every belief the sender can
install. In particular the agent forces no proper part of the range of
`dec ∘ form`.
-/
public theorem mem_of_agent_forces (D : DoxasticAgent O Bel Act R) {A : Set Act}
    (h : Forces D.channel {true} A) (o : O) : D.dec (D.form o) ∈ A := by
  obtain ⟨sC, hsC⟩ := h
  exact hsC (fun i => Bool.rec (motive := fun i => D.channel.strategy i)
      (show D.channel.strategy false from o) (sC ⟨true, rfl⟩) i)
    (by rintro ⟨i, rfl⟩; rfl)

/--
**`C1`: belief-governed action does not establish sovereignty upstream.**

The agent is decisive relative to its beliefs everywhere -- that is a field of
the structure, discharged by construction -- and yet at any two messages
leading to different actions the sender forces a singleton the agent cannot.
Consistency with one's own beliefs is compatible with somebody else choosing
them.
-/
public theorem beliefDecisive_not_sovereign (D : DoxasticAgent O Bel Act R)
    {o o' : O} (h : D.dec (D.form o) ≠ D.dec (D.form o')) :
    Forces D.channel {false} {D.dec (D.form o)} ∧
      ¬ Forces D.channel {true} {D.dec (D.form o)} := by
  refine ⟨D.sender_forces o, fun hagent => ?_⟩
  exact h (D.mem_of_agent_forces hagent o').symm

/--
**And the sender's control is exactly the range of the composite.** Every
action the agent ever takes is one the sender can install, which is the
one-line reading of print's "Y controls B".
-/
public theorem sender_forces_range (D : DoxasticAgent O Bel Act R) :
    ∀ x ∈ Set.range (D.dec ∘ D.form), Forces D.channel {false} {x} := by
  rintro _ ⟨o, rfl⟩
  exact D.sender_forces o

end DoxasticAgent

/-! ## `B5`: Bayesian evidence averages back to the prior -/

/--
**A signal experiment.** A prior over worlds and, at each world, a law over
signals. Both are probability vectors on finite carriers, which is the finite
explicit model print's `B5` is stated in.
-/
public structure SignalExperiment (W : Type u) (S : Type v) [Fintype W] [Fintype S] where
  /-- The receiver's prior over worlds. -/
  prior : W → ℝ≥0∞
  /-- The chance of each signal at each world. -/
  law : W → S → ℝ≥0∞
  /-- The prior is a probability vector. -/
  prior_sum : ∑ w, prior w = 1
  /-- Each world's signal law is a probability vector. -/
  law_sum : ∀ w, ∑ s, law w s = 1

namespace SignalExperiment

variable {W : Type u} {S : Type v} [Fintype W] [Fintype S]

/-- **The chance of a signal**, before it is seen. -/
@[expose] public noncomputable def marginal (E : SignalExperiment W S) (s : S) : ℝ≥0∞ :=
  ∑ w, E.prior w * E.law w s

/-- **The posterior after a signal**, by Bayes' rule. At a signal of
probability zero this is zero, which is the convention `ℝ≥0∞` division carries
and which the statements below never rely on. -/
@[expose] public noncomputable def posterior (E : SignalExperiment W S) (s : S)
    (w : W) : ℝ≥0∞ :=
  E.prior w * E.law w s / E.marginal s

/-- A world's contribution to a signal is at most that signal's probability. -/
public theorem le_marginal (E : SignalExperiment W S) (s : S) (w : W) :
    E.prior w * E.law w s ≤ E.marginal s :=
  Finset.single_le_sum (f := fun w => E.prior w * E.law w s)
    (fun _ _ => bot_le) (Finset.mem_univ w)

/-- Each signal law is bounded by one. -/
public theorem law_le_one (E : SignalExperiment W S) (w : W) (s : S) :
    E.law w s ≤ 1 :=
  E.law_sum w ▸ Finset.single_le_sum (f := fun s => E.law w s)
    (fun _ _ => bot_le) (Finset.mem_univ s)

/-- Signal probabilities are finite. -/
public theorem marginal_ne_top (E : SignalExperiment W S) (s : S) :
    E.marginal s ≠ ⊤ := by
  have : E.marginal s ≤ 1 := by
    calc E.marginal s ≤ ∑ w, E.prior w * 1 :=
          Finset.sum_le_sum fun w _ => by gcongr; exact E.law_le_one w s
      _ = 1 := by simpa using E.prior_sum
  exact ne_top_of_le_ne_top ENNReal.one_ne_top this

/-- **The signals form a probability vector too.** -/
public theorem sum_marginal (E : SignalExperiment W S) : ∑ s, E.marginal s = 1 := by
  calc ∑ s, E.marginal s = ∑ w, E.prior w * ∑ s, E.law w s := by
        simp only [marginal, Finset.mul_sum]
        exact Finset.sum_comm
    _ = 1 := by simp only [E.law_sum, mul_one]; exact E.prior_sum

/--
**`B5`: the posteriors average back to the prior.**

Print writes it as `∑ₛ P(s) μₛ(w) = μ(w)` and proves it by clearing the
division. Nothing here needs the signal to have positive probability: at a
signal that cannot occur both the weight and the world's contribution are zero.
-/
public theorem sum_marginal_mul_posterior (E : SignalExperiment W S) (w : W) :
    ∑ s, E.marginal s * E.posterior s w = E.prior w := by
  have hterm : ∀ s : S, E.marginal s * E.posterior s w = E.prior w * E.law w s := by
    intro s
    rcases eq_or_ne (E.marginal s) 0 with h0 | h0
    · have hz : E.prior w * E.law w s = 0 :=
        le_antisymm (h0 ▸ E.le_marginal s w) bot_le
      rw [h0, hz, zero_mul]
    · exact ENNReal.mul_div_cancel' (fun h => absurd h h0)
        (fun h => absurd h (E.marginal_ne_top s))
  calc ∑ s, E.marginal s * E.posterior s w = ∑ s, E.prior w * E.law w s :=
        Finset.sum_congr rfl fun s _ => hterm s
    _ = E.prior w := by rw [← Finset.mul_sum, E.law_sum w, mul_one]

/--
**So no sender installs a belief that was not already the prior.**

Print's consequence: an interested sender cannot make one fixed posterior occur
with probability one while the receiver knows the experiment and updates by
Bayes' rule. Unknown selection, deception about the experiment, and a
compromised update are different models, and print says so.
-/
public theorem eq_prior_of_constant_posterior (E : SignalExperiment W S)
    (ν : W → ℝ≥0∞) (w : W) (h : ∀ s, E.marginal s ≠ 0 → E.posterior s w = ν w) :
    ν w = E.prior w := by
  rw [← E.sum_marginal_mul_posterior w]
  have hterm : ∀ s : S, E.marginal s * E.posterior s w = E.marginal s * ν w := by
    intro s
    rcases eq_or_ne (E.marginal s) 0 with h0 | h0
    · rw [h0, zero_mul, zero_mul]
    · rw [h s h0]
  rw [Finset.sum_congr rfl fun s _ => hterm s, ← Finset.sum_mul, E.sum_marginal,
    one_mul]

end SignalExperiment

end AISafetyAtlas.Sovereignty
