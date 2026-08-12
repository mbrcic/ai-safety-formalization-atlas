module

public import Mathlib.Order.Preorder.Finite
public import Mathlib.Order.Lattice

/-!
# Limited self-awareness through strict awareness extension

This module formalizes the process-compositional core of Brcic and
Yampolskiy, “Impossibility Results in AI: A Survey,” §4.3: Definition 4.6,
Proposition 4.7, and Theorem 4.8.

The source distinguishes merely executing a process from observing and
predictively modelling it. The formal model makes the resource consequence of
that distinction explicit: an awareness process added to its target increases
the joint composite's cost by at least a positive minimum. Awareness therefore
cannot collapse into a constituent already contained in the target.

`Process` values are process or composite instances relevant during one fixed
bounded awareness horizon. The semilattice order is constituent containment and
`p ⊔ q` is their joint composite. `available` records which composites the
agent can realize during the horizon.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `Model` | Finite horizon-relative composites, awareness, cost, and closure |
| **Model** | `AgentAware` | Some available internal process is aware of the target |
| **Model** | `PerfectlySelfAware` | Every available internal process has such an observer |
| **Boundary** | `Model.not_aware_of_le` | A constituent cannot completely model its containing composite |
| **Proposition 4.7** | `Model.process_not_self_aware` | No process is aware of itself |
| **Boundary** | `Model.not_agentAware_of_maximal` | Every maximal available composite lacks an internal observer |
| **Theorem 4.8** | `Model.limited_self_awareness` | Some available process has no available internal observer |
| **Corollary** | `Model.not_perfectlySelfAware` | Perfect self-awareness is impossible in the model |

## Why the two proofs are different

`process_not_self_aware` is the vertical, higher-order obstruction: identifying
an awareness computation with the process already containing it would require a
strict positive cost increase without changing the composite.

`limited_self_awareness` is horizontal composition. It chooses a maximal
available composite. Any outside observer creates a larger available composite;
any observer forced inside the maximal composite is excluded by Proposition
4.7's constituent form.

## Cycles

No acyclicity assumption appears. Two incomparable processes may observe one
another. Their joint composite is then the higher-level target whose complete
internal observation the theorem excludes.

## Explicit non-claims

- `aware` means the source's active observation-and-predictive-modelling notion
  within the fixed horizon, not static self-description, cached prediction, or
  selected-property knowability.
- `awareness_cost` explicitly formalizes the non-cancellation/additivity used by
  the source's regress. It is the resource consequence of reading awareness as
  distinct active observation and predictive modelling, not a new physical
  premise. The bare numerical statement that unrelated processes have positive
  costs would not express that semantic non-collapse by itself.
- Positive propagation time and bounded lag are absorbed into the
  horizon-relative `aware` relation; no clock or physical propagation theory is
  derived here.
- Finiteness is the fixed-horizon consequence of the source's bounded budget and
  positive minimum process cost. `available_finite` records that consequence
  directly: this module does not derive it from a scalar budget, which would
  additionally require an accounting law for the joint cost of all simultaneous
  process instances. Nor does it derive thermodynamic or physical bounds.
- This is not a consciousness theorem, a Lawvere/Wolpert diagonal theorem, a
  Breuer self-measurement theorem, or a prohibition on partial self-monitoring.

## Relation to `AISafetyAtlas.Knowledge`

Both carry the registry group *limits of self-knowledge and reflection*, and the
machinery is disjoint. `Knowledge` and its specializations obstruct knowledge by
observation fibres and decoders; the obstruction here is a cost law over a
semilattice of composites. No declaration below uses `Knowable`, and neither
module imports the other. The grouping is thematic, so this module stays a
single surface of its own rather than a `Knowledge` specialization.

The source map and fidelity residual are recorded in
`docs/provenance/limited-self-awareness.md`.
-/

namespace AISafetyAtlas.SelfAwareness

universe u

/--
A bounded-horizon model of internal processes and complete process awareness.

The order inherited from `SemilatticeSup Process` means constituent containment;
`target ⊔ observer` is their joint composite. `available` is finite because it
contains only process/composite instances realizable within the fixed resource
and awareness horizon.

`awareness_cost` is the formal non-collapse condition. If `observer` is aware of
`target`, adding that awareness activity to the target costs at least
`minAwarenessCost`. `awareness_closed` states the source's component-to-composite
move: a witnessed awareness relation between available processes makes their
joint process an available target too.
-/
public structure Model (Process : Type u) [SemilatticeSup Process] where
  /-- Process and composite instances available inside the agent during the horizon. -/
  available : Set Process
  /-- Bounded resources and positive minimum process cost make that horizon finite. -/
  available_finite : available.Finite
  /-- An agent has at least one internal process during the horizon. -/
  available_nonempty : available.Nonempty
  /-- `aware observer target`: active observation and predictive modelling of the target. -/
  aware : Process → Process → Prop
  /-- Resource cost assigned to a process/composite instance. -/
  cost : Process → ℕ
  /-- Positive minimum cost contributed by an awareness activity. -/
  minAwarenessCost : ℕ
  /-- The minimum awareness cost is strictly positive. -/
  minAwarenessCost_pos : 0 < minAwarenessCost
  /-- Awareness strictly increases the cost of the observer-target composite. -/
  awareness_cost : ∀ {observer target}, aware observer target →
    cost target + minAwarenessCost ≤ cost (target ⊔ observer)
  /-- An awareness edge makes its observer-target composite available. -/
  awareness_closed : ∀ {observer target},
    target ∈ available → observer ∈ available → aware observer target →
      target ⊔ observer ∈ available

/-- The agent is aware of `target` when some available internal process observes
and predictively models it. -/
@[expose] public def AgentAware {Process : Type u} [SemilatticeSup Process]
    (M : Model Process) (target : Process) : Prop :=
  ∃ observer ∈ M.available, M.aware observer target

/-- Perfect self-awareness: every available internal process or composite has an
available internal observer. -/
@[expose] public def PerfectlySelfAware {Process : Type u} [SemilatticeSup Process]
    (M : Model Process) : Prop :=
  ∀ target ∈ M.available, AgentAware M target

/--
No constituent can provide complete awareness of the composite containing it.

If `observer ≤ target`, then `target ⊔ observer = target`. The strict positive
awareness cost would therefore require the unchanged target to cost strictly
more than itself.
-/
public theorem Model.not_aware_of_le {Process : Type u} [SemilatticeSup Process]
    (M : Model Process) {observer target : Process} (hcontains : observer ≤ target) :
    ¬ M.aware observer target := by
  intro haware
  have hcost := M.awareness_cost haware
  rw [sup_eq_left.mpr hcontains] at hcost
  exact (Nat.not_lt_of_ge hcost) (Nat.lt_add_of_pos_right M.minAwarenessCost_pos)

/--
**Proposition 4.7 (Process Self-awareness).** A process cannot be aware of
itself.

This is the reflexive special case of `not_aware_of_le`. The source explains the
same non-collapse as an awareness-of-awareness regress.
-/
public theorem Model.process_not_self_aware {Process : Type u}
    [SemilatticeSup Process] (M : Model Process) (process : Process) :
    ¬ M.aware process process :=
  M.not_aware_of_le le_rfl

/--
Every maximal available composite lacks an available complete observer.

This is the reusable maximal-target form of the horizontal argument in Theorem
4.8. It strengthens the existential source-facing statement without asserting
that an agent must have more than one maximal composite.
-/
public theorem Model.not_agentAware_of_maximal {Process : Type u}
    [SemilatticeSup Process] (M : Model Process) {target : Process}
    (hmax : Maximal (· ∈ M.available) target) :
    ¬ AgentAware M target := by
  rintro ⟨observer, hobserver, haware⟩
  have hcomposite : target ⊔ observer ∈ M.available :=
    M.awareness_closed hmax.1 hobserver haware
  have hcomposite_le : target ⊔ observer ≤ target :=
    hmax.2 hcomposite le_sup_left
  have hobserver_le : observer ≤ target :=
    le_sup_right.trans hcomposite_le
  exact M.not_aware_of_le hobserver_le haware

/--
**Theorem 4.8 (Limited Self-awareness).** Some available internal process or
composite has no available internal observer.

This is the existential source-facing corollary of
`not_agentAware_of_maximal`: finiteness and nonemptiness provide a maximal
available composite.
-/
public theorem Model.limited_self_awareness {Process : Type u}
    [SemilatticeSup Process] (M : Model Process) :
    ∃ target ∈ M.available,
      ∀ observer ∈ M.available, ¬ M.aware observer target := by
  obtain ⟨target, hmax⟩ :=
    M.available_finite.exists_maximal M.available_nonempty
  refine ⟨target, hmax.1, ?_⟩
  intro observer hobserver haware
  exact M.not_agentAware_of_maximal hmax ⟨observer, hobserver, haware⟩

/-- Perfect self-awareness is impossible in a bounded strict-extension model. -/
public theorem Model.not_perfectlySelfAware {Process : Type u}
    [SemilatticeSup Process] (M : Model Process) :
    ¬ PerfectlySelfAware M := by
  rintro hperfect
  obtain ⟨target, htarget, hunaware⟩ := M.limited_self_awareness
  obtain ⟨observer, hobserver, haware⟩ := hperfect target htarget
  exact hunaware observer hobserver haware

end AISafetyAtlas.SelfAwareness
