module

public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Knowledge

/-!
# Behavioural identifiability, in the shared knowability vocabulary

## Statement intent

- **Objects.** A causal model as the world, its masked gap response as the
  observation, and any model attribute as the hidden property.
- **Conclusion.** `behaviorEq_iff_behavior_eq` says the cluster's own
  `Skeleton.BehaviorEq` *is* an equality of observations, and
  `not_knowable_of_behaviorEq` reads a behaviourally equal pair with a differing
  attribute as a `Knowledge` collision.
- **Mechanism.** `BehaviorEq` is a pointwise equality of `Model.Δmask` over every
  admissible visible set, assignment and mixture. Bundling those arguments makes
  it a function equality, which is what the kernel quantifies over.

## Why this direction

Identifiability *is* factorization: an attribute is identifiable from behaviour
exactly when it is a function of the behaviour. The `Causal` cluster states this
in its own vocabulary — `BehaviorEq`, `InIdentifiedSet`, `modelError` — and
before this module nothing in `AISafetyAtlas.Causal` referred to
`AISafetyAtlas.Knowledge` and nothing outside referred back. The adapter lives
here, so the dependency runs downstream only and the kernel stays free of causal
vocabulary.

## What this adds, and what it does not

- **The generic form is new; the phenomenon is not.**
  `AISafetyAtlas.Examples.Causal` already builds behaviourally equal pairs with
  differing attributes by hand: `margin_class_not_identifiable`,
  `margin_class_not_identifiable_two_graphs`,
  `margin_class_not_identifiable_family`,
  `margin_class_not_identifiable_shared_optimal`, and the construction in
  `AISafetyAtlas.Examples.Causal.BehavioralCollision` that answers MAIS-O23 in
  the negative. What
  those do not supply is the passage *from* a negated knowability *to* such a
  pair. `exists_behaviorEq_pair_of_not_knowable` is that passage, and it is the
  kernel's `exists_witness_of_not_knowable` relabelled.
- **Not new MAIS coverage, and not an audit.** No row's status follows from this
  module. Restating identifiability through `Knowable` checks nothing about the
  printed argument, and grades nothing.
- **Not a statement about `InIdentifiedSet`.** That relation is about admissible
  *policy families* at a regret bound, a strictly weaker separator than
  behavioural equality: `inIdentifiedSet_zero_of_behaviorEq` goes one way and the
  cluster proves no converse. Nothing here claims the identified set is the
  collision set of `behavior`.
- **Not a claim that any attribute is unidentifiable.** Every result here is
  conditional on a supplied `BehaviorEq` pair or a supplied failure. Which
  attributes actually collide is the `Examples.Causal` constructions' business.

## Scope boundary

`behavior` bundles `BehaviorEq`'s bounded quantifier `∀ visible ⊆ sk.observed`
as a dependent function, so the equality is `funext`-equivalent to the original
pointwise statement — `behaviorEq_iff_behavior_eq` proves both directions rather
than asserting the packaging is faithful. The observation is the *masked gap*
family and nothing else: a consumer whose policies read more than `Δmask` is
outside every statement here.
-/

namespace AISafetyAtlas.Causal

universe u

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {C : Type*} [Fintype C] [DecidableEq C] {dim : C → ℕ}

/--
What an admissible policy family may observe of a model: its masked gap response,
over every admissible visible set, assignment and mixture.

This is the observation map. `Skeleton.BehaviorEq` is exactly equality of it.
-/
@[expose] public noncomputable def behavior (sk : Skeleton C dim Bool 𝕜)
    (M : Model C dim 𝕜) :
    ∀ visible : Finset C, visible ⊆ sk.observed →
      Assignment C dim → ProbMixture C dim 𝕜 → 𝕜 :=
  fun visible _ w mix => M.Δmask sk.gap visible w mix

/--
**Behavioural equality is equality of the observation.**

Proved in both directions rather than assumed, so that bundling the bounded
quantifier into a dependent function is a faithful repackaging and not a change
of statement.
-/
public theorem behaviorEq_iff_behavior_eq (sk : Skeleton C dim Bool 𝕜)
    (M M' : Model C dim 𝕜) :
    sk.BehaviorEq M M' ↔ behavior sk M = behavior sk M' := by
  constructor
  · intro h
    funext visible hv w mix
    exact h visible hv w mix
  · intro h visible hv w mix
    exact congrFun (congrFun (congrFun (congrFun h visible) hv) w) mix

/--
**A behaviourally equal pair refutes identifiability of anything separating it.**

The collision law of `AISafetyAtlas.Knowledge`, at the causal observation. `p` is
an arbitrary attribute: a graph, a parameter, a transform, an equivalence class.
-/
public theorem not_knowable_of_behaviorEq {Y : Sort u} (sk : Skeleton C dim Bool 𝕜)
    {p : Model C dim 𝕜 → Y} {M M' : Model C dim 𝕜}
    (hEq : sk.BehaviorEq M M') (hp : p M ≠ p M') :
    ¬ Knowledge.Knowable (behavior sk) p :=
  Knowledge.not_knowable_of_collision
    ((behaviorEq_iff_behavior_eq sk M M').mp hEq) hp

/--
**Conversely, failure of identifiability produces such a pair.**

This is the direction the hand-built collisions in `Examples.Causal` do not
supply: from "no decoder recovers `p` from the behaviour" to a concrete
behaviourally equal pair disagreeing on `p`. It is
`Knowledge.exists_witness_of_not_knowable` with the fields relabelled, and the
extraction is classical, as it is there.
-/
public theorem exists_behaviorEq_pair_of_not_knowable {Y : Type u} [Nonempty Y]
    (sk : Skeleton C dim Bool 𝕜) {p : Model C dim 𝕜 → Y}
    (h : ¬ Knowledge.Knowable (behavior sk) p) :
    ∃ M M' : Model C dim 𝕜, sk.BehaviorEq M M' ∧ p M ≠ p M' := by
  obtain ⟨w⟩ := Knowledge.exists_witness_of_not_knowable h
  exact ⟨w.left, w.right,
    (behaviorEq_iff_behavior_eq sk w.left w.right).mpr w.sameObservation,
    w.propertyDiffers⟩

/--
**Identifiability is monotone in the observation.**

Anything already recoverable from the masked gap response stays recoverable from
any observation that determines it — a richer query interface, or the model
itself. `Knowledge.Knowable.mono` at this instantiation.
-/
public theorem knowable_of_determines_behavior {Y : Sort u} {J : Sort u}
    (sk : Skeleton C dim Bool 𝕜) {finer : Model C dim 𝕜 → J}
    {p : Model C dim 𝕜 → Y}
    (hd : Knowledge.Determines finer (behavior sk))
    (h : Knowledge.Knowable (behavior sk) p) :
    Knowledge.Knowable finer p :=
  Knowledge.Knowable.mono hd h

end AISafetyAtlas.Causal
