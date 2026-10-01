module

public import AISafetyAtlas.Wireheading.AgentEquations
public import AISafetyAtlas.Decision.MDP

/-!
# Ring and Orseau's histories are the carrier's histories

`AISafetyAtlas.Wireheading.AgentEquations` defines its own interaction history,
`List (Action × Obs)`, and evaluates `value` by recursion along it. The
`AISafetyAtlas.Decision` cluster defines another, `Obs × List (Action × Obs)`,
and runs policies along that. Nothing related them, so a value recursion could
not be evaluated along a run and a run could not be scored by an agent's
utility -- two trees, no chain.

**They are the same list with one datum in front.** `Decision.History Obs
Action` is an initial observation paired with exactly the list
`AgentEquations.History Action Obs` is, so the transport is a pairing and a
projection and both round trips are `rfl`. This module states that, and then
states the consequence that makes it worth having: **an agent's value is
well-defined along a determined run**, with the window the theorem needs read
off the run's length.

## What this buys

`value_eq_of_agree_on_window` says the depth-`n` value from a history depends
only on the utility and horizon inside the reachable window. Stated at a bare
history that is a claim about lists. Stated along a run it is a claim about an
agent in a world: **two agents that agree on everything the run can reach in
`n + m` steps score it identically, however wildly they differ past the
horizon** -- which is the statement the source's argument actually uses.

## Explicit non-claims

* **No reward, no corruption.** The transport carries histories, not the MDP's
  reward. `AISafetyAtlas.Wireheading.CRMDP` is the module that puts a reward on
  this carrier; nothing here duplicates it.
* **Determined runs only.** The results below are stated for `detRun`, whose
  policy and transition are functions. The drawn run is a `PMF`, and relating
  `value` to an expectation over it is a different statement, not proved here.
* **Not a claim that the two clusters agree on anything else.** `Agent` and
  `MDP` remain distinct structures; this joins their histories and nothing more.

Landscape entry: `LAND-WIRE-AGENTHISTORY-001`. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Wireheading.AgentEquations

open AISafetyAtlas.Decision

variable {Action Obs State : Type*}

/-! ## The transport

Spelled with full names rather than dot notation: `History` is an abbreviation
for `List`, so `h.toDecisionHistory` would resolve against `List` and not
against anything here.
-/

/-- An interaction history, read as a history of the `Decision` carrier by
supplying the initial observation the recursion never needed. -/
@[expose] public def toDecisionHistory (o₀ : Obs) (h : History Action Obs) :
    Decision.History Obs Action :=
  (o₀, h)

/-- A history of the `Decision` carrier, read as an interaction history by
forgetting the initial observation. -/
@[expose] public def ofDecisionHistory (h : Decision.History Obs Action) :
    History Action Obs :=
  h.2

/-- Forgetting the initial observation after supplying it changes nothing. -/
public theorem ofDecisionHistory_toDecisionHistory (o₀ : Obs) (h : History Action Obs) :
    ofDecisionHistory (toDecisionHistory o₀ h) = h := rfl

/-- And supplying the observation a history already carries changes nothing. -/
public theorem toDecisionHistory_ofDecisionHistory (h : Decision.History Obs Action) :
    toDecisionHistory h.1 (ofDecisionHistory h) = h := rfl

/-- So the transport is injective at a fixed initial observation: no two
interaction histories become the same run history. -/
public theorem toDecisionHistory_injective (o₀ : Obs) :
    Function.Injective (toDecisionHistory (Action := Action) o₀) :=
  fun _ _ h => congrArg Prod.snd h

/-- The transport does not change the length the window is measured in. -/
public theorem length_ofDecisionHistory (h : Decision.History Obs Action) :
    (ofDecisionHistory h).length = h.2.length := rfl

/-! ## The history a run produces -/

/-- **The interaction history of a determined run.** The `Decision` cluster's
`detHistoryUpTo`, read in the recursion's own carrier. -/
@[expose] public def runHistory (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State) (n : ℕ) : History Action Obs :=
  ofDecisionHistory (detHistoryUpTo f obs π s₀ n)

/-- **A run of `n` steps produces a history of length `n`.** This is what lets
the window in `value_eq_of_agree_on_window` be named in steps rather than in
list length. -/
public theorem runHistory_length (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State) (n : ℕ) :
    (runHistory f obs π s₀ n).length = n :=
  detHistoryUpTo_length f obs π s₀ n

/-- The run of zero steps is the empty interaction history, so the value at
depth `n` from a fresh start is `value ρ ag t n []`. -/
public theorem runHistory_zero (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State) :
    runHistory f obs π s₀ 0 = [] := rfl

/-! ## The window, along a run -/

/--
**Two agents agreeing on the reachable window score a run identically.**

`value_eq_of_agree_on_window` stated where it has content: the history is not an
arbitrary list but the one a policy and a transition actually produced, and the
window is `n + m` steps -- the `n` already run plus the `m` still to be looked
ahead. Outside that window the two agents may disagree completely.
-/
public theorem value_runHistory_eq_of_agree_on_window
    (ρ : Belief Action Obs) (ag₁ ag₂ : Agent Action Obs) (t n m : ℕ)
    (f : State → Action → State) (obs : State → Obs)
    (π : DetPolicy Obs Action) (s₀ : State)
    (hu : ∀ h' : History Action Obs, h'.length ≤ n + m → ag₁.utility h' = ag₂.utility h')
    (hw : ∀ k ≤ n + m, ag₁.horizon t k = ag₂.horizon t k) :
    value ρ ag₁ t m (runHistory f obs π s₀ n)
      = value ρ ag₂ t m (runHistory f obs π s₀ n) := by
  have hlen : (runHistory f obs π s₀ n).length = n := runHistory_length f obs π s₀ n
  refine value_eq_of_agree_on_window ρ ag₁ ag₂ t m _ (fun h' hh' => hu h' ?_)
    (fun k hk => hw k ?_)
  · rw [hlen] at hh'; exact hh'
  · rw [hlen] at hk; exact hk

end AISafetyAtlas.Wireheading.AgentEquations
