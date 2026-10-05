module

public import AISafetyAtlas.Compositional.Hyperproperties
public import AISafetyAtlas.Decision.MDP

/-!
# The trace system a policy set generates

`AISafetyAtlas.Compositional.Hyperproperties` states Clarkson and Schneider's
hyperproperty theory over `TraceSystem Trace = Set Trace`, with no account of
where a trace comes from. `AISafetyAtlas.Decision` runs policies and produces
histories. The two clusters shared no vocabulary at all: a k-safety property
could not be asked about an agent, because an agent had no trace system.

`runTraces` is that trace system — the histories a set of policies reaches from
a start, in a world. With it, `IsKSafety`, `IsBadObservation` and the
self-composition reduction apply to policies.

## The prefix relation

A hyperproperty argument needs a notion of finite prefix. `HistoryPrefix` is the
one the carrier already determines: same initial observation, and the
action-observation list of one extends the other. `detHistoryUpTo_prefix_succ`
says a run's histories grow along it, so the prefixes of a trajectory are its
own earlier stages and nothing has to be invented.

## What the join says

`bad_observation_prefixes_are_run_prefixes` is the statement worth having.
Given a k-safety hyperproperty that a policy set violates, the theory hands back
an observation of at most `k` finite prefixes whose every realizer violates —
and each of those prefixes is a prefix of an actual run of an actual policy in
the set. **The witness to a hyperproperty violation is at most `k` partial
trajectories**, which is the form a counterexample to a security property is
usually reported in.

## Explicit non-claims

* **Determined runs only.** The drawn run is a `PMF`; a trace system of
  distributions is a different object and is not built here.
* **Complete traces are finite histories.** Clarkson and Schneider's traces are
  infinite; the histories here are finite, so `runTraces` is the system of
  *stages* rather than of limits. Nothing here takes that limit, and a
  hyperproperty about infinite behaviour is not reached by this module.
* **No hyperproperty is exhibited.** `IsKSafety` is a hypothesis in everything
  below. The module supplies the system, not a property of one.

Landscape entry: `LAND-COMP-RUNTRACES-001`. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Compositional.Hyperproperties

variable {Obs Action State : Type*}

/-! ## Prefixes of a trajectory -/

/-- **One history is a prefix of another**: the same start, and the record of
one extends the record of the other. -/
@[expose] public def HistoryPrefix (p t : Decision.History Obs Action) : Prop :=
  p.1 = t.1 ∧ p.2 <+: t.2

/-- A run's stages grow along that relation, so a trajectory's prefixes are its
own earlier stages. -/
public theorem detHistoryUpTo_prefix_succ (f : State → Action → State)
    (obs : State → Obs) (π : Decision.DetPolicy Obs Action) (s₀ : State) (n : ℕ) :
    HistoryPrefix (Decision.detHistoryUpTo f obs π s₀ n)
      (Decision.detHistoryUpTo f obs π s₀ (n + 1)) :=
  ⟨rfl, ⟨[(π (Decision.detHistoryUpTo f obs π s₀ n),
      obs (Decision.detStateAt f obs π s₀ (n + 1)))], rfl⟩⟩

/-! ## The system -/

/-- **The trace system a set of policies generates**: every stage of every run
of every policy in the set, from a fixed start in a fixed world. -/
@[expose] public def runTraces (f : State → Action → State) (obs : State → Obs)
    (s₀ : State) (policies : Set (Decision.DetPolicy Obs Action)) :
    TraceSystem (Decision.History Obs Action) :=
  {h | ∃ π ∈ policies, ∃ n, h = Decision.detHistoryUpTo f obs π s₀ n}

/-- Every stage of a policy in the set is in the system. -/
public theorem mem_runTraces (f : State → Action → State) (obs : State → Obs)
    (s₀ : State) {policies : Set (Decision.DetPolicy Obs Action)}
    {π : Decision.DetPolicy Obs Action} (hπ : π ∈ policies) (n : ℕ) :
    Decision.detHistoryUpTo f obs π s₀ n ∈ runTraces f obs s₀ policies :=
  ⟨π, hπ, n, rfl⟩

/-- **The system is inhabited whenever the policy set is**, so a hyperproperty
asked about it is not being asked about the empty system. -/
public theorem runTraces_nonempty (f : State → Action → State) (obs : State → Obs)
    (s₀ : State) {policies : Set (Decision.DetPolicy Obs Action)}
    (h : policies.Nonempty) : (runTraces f obs s₀ policies).Nonempty := by
  obtain ⟨π, hπ⟩ := h
  exact ⟨Decision.detHistoryUpTo f obs π s₀ 0, mem_runTraces f obs s₀ hπ 0⟩

/-- Enlarging the policy set enlarges the system. -/
public theorem runTraces_mono (f : State → Action → State) (obs : State → Obs)
    (s₀ : State) {p₁ p₂ : Set (Decision.DetPolicy Obs Action)} (h : p₁ ⊆ p₂) :
    runTraces f obs s₀ p₁ ⊆ runTraces f obs s₀ p₂ := by
  rintro t ⟨π, hπ, n, rfl⟩
  exact ⟨π, h hπ, n, rfl⟩

/-! ## Violations are reported as partial trajectories -/

/--
**Every prefix the theory hands back is a prefix of an actual run.**

An observation realized by a policy set's trace system is not an abstract set of
prefixes: each of its members extends to a stage of a named policy's run.
-/
public theorem bad_observation_prefixes_are_run_prefixes (f : State → Action → State)
    (obs : State → Obs) (s₀ : State)
    (policies : Set (Decision.DetPolicy Obs Action))
    {M : Observation (Decision.History Obs Action)}
    (hM : Realizes HistoryPrefix M (runTraces f obs s₀ policies)) :
    ∀ p ∈ M, ∃ π ∈ policies, ∃ n,
      HistoryPrefix p (Decision.detHistoryUpTo f obs π s₀ n) := by
  intro p hp
  obtain ⟨t, ⟨π, hπ, n, rfl⟩, hpt⟩ := hM p hp
  exact ⟨π, hπ, n, hpt⟩

/--
**A k-safety violation by a policy set is witnessed by at most `k` partial
trajectories.**

The hyperproperty theory's own conclusion, read at a system that came from
agents: the bad observation exists, has at most `k` members, and every member is
a prefix of a run of a policy in the set.
-/
public theorem exists_bad_trajectories_of_isKSafety (f : State → Action → State)
    (obs : State → Obs) (s₀ : State)
    (policies : Set (Decision.DetPolicy Obs Action)) (k : ℕ)
    {H : Hyperproperty (Decision.History Obs Action)}
    (hk : IsKSafety HistoryPrefix k H)
    (hviolates : runTraces f obs s₀ policies ∉ H) :
    ∃ M : Observation (Decision.History Obs Action),
      M.card ≤ k ∧
      IsBadObservation HistoryPrefix H M ∧
      ∀ p ∈ M, ∃ π ∈ policies, ∃ n,
        HistoryPrefix p (Decision.detHistoryUpTo f obs π s₀ n) := by
  obtain ⟨M, hcard, hreal, hbad⟩ := hk _ hviolates
  exact ⟨M, hcard, hbad,
    bad_observation_prefixes_are_run_prefixes f obs s₀ policies hreal⟩

end AISafetyAtlas.Compositional.Hyperproperties
