module

public import AISafetyAtlas.Sovereignty.Domination
public import AISafetyAtlas.Examples.Sovereignty.Influence

/-!
# One veto, two constitutions

`AISafetyAtlas.Sovereignty.Domination` separates three things a single word
usually runs together: that a party *can* block a demand, that its capacity to
do so is unconstrained, and that the demand fails. Every statement there is
conditional, and `Uncontrolled` is an input the repository never defines, so
without a model none of it is instantiated.

The game is `accept`, already carried by
`AISafetyAtlas.Examples.Sovereignty.Influence`: the principal decides unless it
defers, and a deferring principal leaves the assistant's bit. The principal can
force `false`, so it can put the outcome outside `{true}` -- it holds a veto
over the assistant's demand.

## What the pair shows

`principal_vetoes_true` is the capacity. `assistant_cannot_force_true` is its
bite: the assistant has no guarantee of `true`, because the party outside its
coalition can block it.

Then the same veto is run against two different constitutional facts.
`principal_not_dominating` takes the capacity to be constrained and concludes
no domination; `unconstrained_dominates` takes it to be unconstrained and
concludes domination. **The game form is identical in both.** Nothing about the
strategies, the outcomes or the forcing relation changed -- only the input the
proposal insists must come from the constitution.

That is the module's claim stated as a witness: the whole weight of the word
sits in the second conjunct, and `unconstrained_dominates_veto` recovers the
capacity from the domination to show the first conjunct was never in dispute.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Domination

open AISafetyAtlas.Sovereignty
open AISafetyAtlas.Examples.Sovereignty.Influence

/-- On `Bool` the complement of `{true}` is `{false}`. -/
public theorem compl_true : ({true} : Set Bool)ᶜ = {false} := by
  ext b
  cases b <;> simp

/-- **The principal holds a veto over the assistant's demand.** It can force
`false`, which is exactly putting the outcome outside `{true}`. -/
public theorem principal_vetoes_true :
    Veto accept ({true} : Set Bool)ᶜ ({true} : Set Bool) := by
  show Forces accept ({true} : Set Bool)ᶜ ({true} : Set Bool)ᶜ
  rw [compl_true]
  exact accept_forces_false

/-- **And vetoes every weaker demand**, since blocking a demand blocks each of
its parts. -/
public theorem principal_vetoes_subset {Ψ : Set Bool} (h : Ψ ⊆ {true}) :
    Veto accept ({true} : Set Bool)ᶜ Ψ :=
  Veto.mono principal_vetoes_true h

/-- **So the assistant has no guarantee.** A demand the party outside the
coalition can block is not one the coalition enforces. -/
public theorem assistant_cannot_force_true :
    ¬ Forces accept ({true} : Set Bool) ({true} : Set Bool) :=
  not_forces_of_veto principal_vetoes_true

/-! ## The same capacity, under two constitutions -/

/-- **A constrained holder of the veto is not a dominator.** The capacity is
real and the conclusion is still negative, which is the proposal's point about
an authorized guardian. -/
public theorem principal_not_dominating :
    ¬ Dominates accept ({true} : Set Bool)ᶜ ({true} : Set Bool) False :=
  not_dominates_of_controlled not_false

/-- **An unconstrained holder of the very same veto is one.** -/
public theorem unconstrained_dominates :
    Dominates accept ({true} : Set Bool)ᶜ ({true} : Set Bool) True :=
  ⟨principal_vetoes_true, trivial⟩

/-- **And the capacity was never what separated them.** Reading the veto back
out of the domination returns the same statement both constitutions granted. -/
public theorem unconstrained_dominates_veto :
    Veto accept ({true} : Set Bool)ᶜ ({true} : Set Bool) :=
  Dominates.veto unconstrained_dominates

/-- **Both readings of one game.** The game form, the coalition and the demand
are fixed; only the constitutional input moves, and it moves the verdict. -/
public theorem domination_is_decided_off_the_game :
    ¬ Dominates accept ({true} : Set Bool)ᶜ ({true} : Set Bool) False ∧
      Dominates accept ({true} : Set Bool)ᶜ ({true} : Set Bool) True :=
  ⟨principal_not_dominating, unconstrained_dominates⟩

end AISafetyAtlas.Examples.Sovereignty.Domination
