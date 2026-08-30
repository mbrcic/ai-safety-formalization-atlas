module

public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Positivity

/-!
# Finite controlled Markov processes

The environment MAIS-A2's goal-based problems are stated over: *"a finite
communicating stationary controlled Markov process `E = (𝐒, 𝐀, P)`"*, with
`P_{ss'}(a)` constant in time and every state reachable from every other.

This module is the environment alone. The goal formalism is
`AISafetyAtlas.Causal.Goal`; agents, trajectory laws and the query model are what
MAIS-O33 needs next and are not here.

## Communicating, and the cheap sufficient condition

`Communicating` is print's own condition, the reflexive-transitive closure of
*"some action gives positive probability"*. `communicating_of_fullSupport` is
the one-line route every explicit construction in this area takes: a kernel with
no zero entry reaches everything in a single step.

## Separation, and why it is stated pointwise

MAIS-A2 measures reconstruction error in the entrywise sup norm. Rather than
introduce a norm on kernels for one use, `SeparatedBy` says pointwise what the
sup norm would say, and `not_withinBall_both` is the fact any indistinguishability
argument needs: two kernels more than `2τ` apart have disjoint closed `τ`-balls,
so no single estimate is accurate for both.
-/

namespace AISafetyAtlas.Causal

variable {S A : Type*}

/-- A finite controlled Markov process: `prob s a s'` is `P_{ss'}(a)`, constant
in time, which is print's stationarity. -/
public structure ControlledMarkovProcess (S A : Type*) [Fintype S] where
  /-- `P_{ss'}(a)`. -/
  prob : S → A → S → ℝ
  /-- Probabilities are nonnegative. -/
  prob_nonneg : ∀ s a s', 0 ≤ prob s a s'
  /-- Each row is a distribution over the next state. -/
  prob_sum : ∀ s a, ∑ s', prob s a s' = 1

namespace ControlledMarkovProcess

variable [Fintype S]

/-- One step with positive probability under some action. -/
@[expose] public def OneStep (E : ControlledMarkovProcess S A) (s t : S) : Prop :=
  ∃ a, 0 < E.prob s a t

/-- Reachability: print's *"every state reachable from every other"*. -/
@[expose] public def Reachable (E : ControlledMarkovProcess S A) : S → S → Prop :=
  Relation.ReflTransGen E.OneStep

/-- Print's communicating condition. -/
@[expose] public def Communicating (E : ControlledMarkovProcess S A) : Prop :=
  ∀ s t, E.Reachable s t

/-- Every entry positive. -/
@[expose] public def FullSupport (E : ControlledMarkovProcess S A) : Prop :=
  ∀ s a s', 0 < E.prob s a s'

/-- **A kernel with no zero entry is communicating**, in one step. -/
public theorem communicating_of_fullSupport [Nonempty A]
    {E : ControlledMarkovProcess S A} (h : E.FullSupport) : E.Communicating := by
  intro s t
  exact Relation.ReflTransGen.single ⟨Classical.arbitrary A, h s _ t⟩

/-- Every entry is at most one, since the row sums to one and no entry is
negative. -/
public theorem prob_le_one (E : ControlledMarkovProcess S A) (s : S) (a : A) (s' : S) :
    E.prob s a s' ≤ 1 := by
  classical
  have hsum := E.prob_sum s a
  have hmem : s' ∈ (Finset.univ : Finset S) := Finset.mem_univ s'
  have := Finset.single_le_sum (f := fun t ↦ E.prob s a t)
    (fun t _ ↦ E.prob_nonneg s a t) hmem
  linarith [hsum, this]

/-- **Action-independent**: the transition law does not read the action, which is
the class print's own myopic converse is stated over (*"communicating
action-independent environments (`P_{ss'}(a)` constant in `a`)"*). Nothing in
`prob:rate` or `prob:corruption` excludes them: they are finite, stationary, and
communicating as soon as the rows have full support. -/
@[expose] public def ActionIndependent (E : ControlledMarkovProcess S A) : Prop :=
  ∀ s a a' s', E.prob s a s' = E.prob s a' s'

/-! ## Separation in the entrywise sup norm -/

/-- The two kernels differ by at least `d` somewhere, and nowhere by more. -/
@[expose] public def SeparatedBy (E F : ControlledMarkovProcess S A) (d : ℝ) : Prop :=
  ∃ s a s', d ≤ |E.prob s a s' - F.prob s a s'|

/-- An estimate within `τ` of `E` everywhere. -/
@[expose] public def WithinBall (E : ControlledMarkovProcess S A)
    (Q : S → A → S → ℝ) (τ : ℝ) : Prop :=
  ∀ s a s', |Q s a s' - E.prob s a s'| ≤ τ

/-- **Disjoint reconstruction balls.** If two environments are more than `2τ`
apart in the entrywise sup norm, no single estimate is within `τ` of both — so
an analyst that cannot distinguish them cannot be accurate in both worlds. -/
public theorem not_withinBall_both {E F : ControlledMarkovProcess S A} {d τ : ℝ}
    (hsep : E.SeparatedBy F d) (hd : 2 * τ < d) {Q : S → A → S → ℝ}
    (hE : E.WithinBall Q τ) (hF : F.WithinBall Q τ) : False := by
  obtain ⟨s, a, s', hle⟩ := hsep
  have h1 := hE s a s'
  have h2 := hF s a s'
  have htri : |E.prob s a s' - F.prob s a s'|
      ≤ |E.prob s a s' - Q s a s'| + |Q s a s' - F.prob s a s'| :=
    abs_sub_le _ _ _
  rw [abs_sub_comm (E.prob s a s') (Q s a s')] at htri
  linarith

end ControlledMarkovProcess

/-! ## The reconstruction radius

MAIS-O33 asks for accuracy `2/√((n-1)(1-δ))` with probability at least `2/3`, on
instances with `(n-1)(1-δ) > 4`. -/

/-- Print's reconstruction radius `τ(n, δ)`. -/
@[expose] public noncomputable def reconstructionRadius (n : ℕ) (δ : ℝ) : ℝ :=
  2 / Real.sqrt ((n - 1) * (1 - δ))

/-- **A `2/3` success probability cannot be had in two worlds at once.** The
two events are disjoint, so their probabilities under one law would sum above
one. This is the whole of the indistinguishability step, stated without a
measure: it is arithmetic on two numbers a common output law assigns. -/
public theorem not_both_two_thirds {p q : ℝ} (hsum : p + q ≤ 1)
    (hp : 2 / 3 ≤ p) (hq : 2 / 3 ≤ q) : False := by linarith

end AISafetyAtlas.Causal
