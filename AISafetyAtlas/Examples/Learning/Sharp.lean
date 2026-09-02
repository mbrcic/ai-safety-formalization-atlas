module

public import AISafetyAtlas.Learning.Sharp
public import Mathlib.Tactic.NormNum.Pow

/-!
# The sharp NFL — worked consequences

Seven checks on `AISafetyAtlas.Learning.Sharp`.

1. **The condition has content.** `nfl_fails_off_permInvariant` exhibits a
   two-point domain, a weight concentrated on a single objective, and two
   one-query schedules with *different* aggregate performance. So the necessary
   direction is not vacuous: drop permutation-invariance and NFL genuinely
   fails.
2. **A non-trivial prior satisfies it.** The constant objectives form a proper
   permutation-closed subset, so NFL holds over that prior
   (`nfl_over_constants`) — Schumacher–Vose–Whitley's set form, instantiated.
3. **It subsumes the uniform core.** Already recorded in the library as
   `no_free_lunch_embedding_of_sharp`; `uniform_is_permInvariant` names the
   reason.

4. **The algorithm class is genuinely larger.** `probeRule` branches on the cost
   it observes, so no fixed schedule reproduces it (`probeRule_not_schedule`),
   and NFL still holds for it against a single permutation orbit
   (`nfl_probeRule_over_orbit`). The orbit is non-constant, which matters:
   `observed_probeRule_ne` checks the rule really does read different cost
   sequences within it, so the equality is not two identical sums. Without that
   the adaptive quantifier would be decoration.

5. **Randomness is not a way out.** `coinRule_realizations_differ` shows two
   choice sequences induce rules that open at different points, so the
   stochastic quantifier is not decoration, and `nfl_coinRule_vs_probeRule`
   scores that coin against the branching deterministic `probeRule`.

6. **The condition is met by almost nothing.** `card_cup_boolean` and
   `fraction_cup_boolean` evaluate Igel–Toussaint's count and fraction at
   print's own Boolean example: `31` of `65535`.

7. **Structure rules it out entirely.** `oneEdge_not_permInvariant` and
   `loopedEdge_not_permInvariant` are Theorem 4 at its smallest instances, and
   `top_permInvariant`/`bot_permInvariant` occupy both branches of the graph
   dichotomy so it is not a theorem with one live case.

Together these say that the `iff` separates two non-empty cases over a class
that is strictly bigger than schedules — which is what makes it a
characterization rather than a restatement.
-/

namespace AISafetyAtlas.Examples.Learning

open AISafetyAtlas.Learning
open AISafetyAtlas.Combinatorics

/-! ## A counterexample off the condition

Domain and codomain are both `Fin 2`. The weight is concentrated on the identity
objective, which is not permutation-symmetric. -/

/-- The weight concentrated on the identity objective on `Fin 2`. -/
@[expose] public noncomputable def pointWeight : ObjectiveWeight (Fin 2) (Fin 2) :=
  fun f => if f = id then (1 : ℝ) else 0

/-- Score a single query by the value it returns. -/
@[expose] public def observedValue : CostPerformance 1 (Fin 2) :=
  fun c => ((c 0).val : ℝ)

/-- Query the first point. -/
@[expose] public def queryFirst : Fin 1 ↪ Fin 2 :=
  ⟨fun _ => 0, fun a b _ => Subsingleton.elim a b⟩

/-- Query the second point. -/
@[expose] public def querySecond : Fin 1 ↪ Fin 2 :=
  ⟨fun _ => 1, fun a b _ => Subsingleton.elim a b⟩

/-- The weight is not invariant under swapping the two domain points. -/
public theorem pointWeight_not_permInvariant : ¬ PermInvariant pointWeight := by
  intro h
  have hswap := h (Equiv.swap 0 1) id
  have hne : ⇑(Equiv.swap (0 : Fin 2) 1) ≠ (id : Fin 2 → Fin 2) := by
    intro hcontra
    have hval := congrFun hcontra 0
    simp [Equiv.swap_apply_left] at hval
  simp [pointWeight, hne] at hswap

/--
**Off the condition, NFL fails.** Querying the first point scores `0` and
querying the second scores `1`, under the same weight and the same performance
measure. So `permInvariant_of_nfl` is not vacuously true.
-/
public theorem nfl_fails_off_permInvariant :
    weightedPerformance pointWeight observedValue queryFirst
      ≠ weightedPerformance pointWeight observedValue querySecond := by
  have hfirst : weightedPerformance pointWeight observedValue queryFirst
      = observedValue (fun i => (id : Fin 2 → Fin 2) (queryFirst i)) :=
    weightedPerformance_pointMass id observedValue queryFirst
  have hsecond : weightedPerformance pointWeight observedValue querySecond
      = observedValue (fun i => (id : Fin 2 → Fin 2) (querySecond i)) :=
    weightedPerformance_pointMass id observedValue querySecond
  rw [hfirst, hsecond]
  -- `norm_num` now stops at the embedding application rather than reducing it.
  norm_num [observedValue, queryFirst, querySecond]
  decide

/-! ## A proper prior that satisfies it -/

/-- The constant objectives: a proper subset of all objectives, closed under
relabelling the domain because a relabelled constant is constant. -/
@[expose] public def constantObjectives (X Y : Type*) : Set (X → Y) :=
  {f | ∃ y, f = fun _ => y}

/-- Constants are closed under permutation — Schumacher–Vose–Whitley's condition. -/
public theorem closedUnderPermutation_constants (X Y : Type*) :
    ClosedUnderPermutation (constantObjectives X Y) := by
  rintro π f ⟨y, rfl⟩
  exact ⟨y, rfl⟩

/--
**NFL over the constants prior.** A non-uniform, proper prior for which every
schedule is still equally good. Obtained by composing the set form with the
sufficient direction; nothing is reproved.
-/
public theorem nfl_over_constants {X Y : Type*} [Fintype X] [Fintype Y]
    [DecidablePred (· ∈ constantObjectives X Y)] {m : ℕ}
    (Φ : CostPerformance m Y) (σ τ : Fin m ↪ X) :
    weightedPerformance (fun f => if f ∈ constantObjectives X Y then (1 : ℝ) else 0) Φ σ
      = weightedPerformance (fun f => if f ∈ constantObjectives X Y then (1 : ℝ) else 0) Φ τ :=
  nfl_of_permInvariant
    (permInvariant_of_closedUnderPermutation (closedUnderPermutation_constants X Y)) Φ σ τ

/-- The uniform prior of `AISafetyAtlas.Learning` is permutation-invariant, which
is why the earlier cores are the trivial case of the sharp theorem. -/
public theorem uniform_is_permInvariant (X Y : Type*) :
    PermInvariant (fun _ : X → Y => (1 : ℝ)) :=
  fun _ _ => rfl

/-! ## The adaptive class is genuinely larger

`nfl_adaptive_of_permInvariant` quantifies over rules that choose each query from
the costs already seen. This section checks the quantifier is not decoration:
`probeRule` is a rule that no schedule reproduces, and NFL still holds for it. -/

/--
A rule on a three-point domain that branches on what it saw: query point `0`
first, then go to `1` or to `2` according to the cost observed there.
-/
@[expose] public def probeRule : AdaptiveRule (Fin 3) (Fin 2) 2
  | ⟨0, _⟩ => fun _ => 0
  | ⟨1, _⟩ => fun h => if h 0 = 0 then 1 else 2

/-- **The rule is genuinely adaptive.** Two cost sequences send it to different
second points, which no fixed schedule can do. -/
public theorem probeRule_not_schedule :
    ruleVisit probeRule (fun _ => 0) 1 ≠ ruleVisit probeRule (fun _ => 1) 1 := by
  decide

/-- The rule never revisits, so it is in the class both printed sources
quantify over. -/
public theorem probeRule_noRevisit (c : Fin 2 → Fin 2) :
    Function.Injective (ruleVisit probeRule c) := by
  revert c
  decide

/-- A non-constant objective on the three-point domain: it is `1` at the point
`probeRule` queries first, and `0` elsewhere. -/
@[expose] public def splitObjective : Fin 3 → Fin 2 := ![1, 0, 0]

/-- **The prior is not degenerate.** `probeRule` reads different cost sequences
from the two objectives `splitObjective` and `splitObjective ∘ swap 0 1`, both of
which lie in the orbit. So the equality below is not two identical sums. -/
public theorem observed_probeRule_ne :
    observed probeRule splitObjective
      ≠ observed probeRule (splitObjective ∘ (Equiv.swap 0 1 : Equiv.Perm (Fin 3))) := by
  decide

/--
**NFL holds for the adaptive rule too.** The prior is a single permutation orbit
— proper, non-uniform, permutation-closed by
`closedUnderPermutation_permOrbit` — and the branching rule scores exactly what a
fixed schedule scores on it.

The orbit is chosen non-constant on purpose. Over the *constant* objectives every
rule whatsoever observes the same cost sequence, so an equality there would hold
for reasons that never touch permutation invariance, never touch the no-revisit
hypothesis, and never exercise `probeRule`'s branch. `observed_probeRule_ne`
records that this prior does not collapse that way.
-/
public theorem nfl_probeRule_over_orbit
    [DecidablePred (· ∈ permOrbit splitObjective)]
    (Ψ : (Fin 2 → Fin 2) → ℝ) (σ : Fin 2 ↪ Fin 3) :
    weightedTrace
        (fun f => if f ∈ permOrbit splitObjective then (1 : ℝ) else 0) Ψ probeRule
      = weightedTrace
        (fun f => if f ∈ permOrbit splitObjective then (1 : ℝ) else 0) Ψ (scheduleRule σ) :=
  nfl_adaptive_of_permInvariant
    (permInvariant_of_closedUnderPermutation
      (closedUnderPermutation_permOrbit splitObjective))
    probeRule (scheduleRule σ) probeRule_noRevisit
    (injective_ruleVisit_scheduleRule σ) Ψ

/-! ## The randomness is genuinely used

`nfl_stochastic_of_permInvariant` quantifies over rules that read a choice at
each step. This section checks that quantifier is not decoration either: a rule
whose *realizations differ* still scores what a deterministic rule scores.

Without `coinRule_realizations_differ` the theorem would be indistinguishable
from the deterministic one applied under a weighted sum, which is the failure
mode `observed_probeRule_ne` guards against one level up. -/

/--
A coin-flipping rule on the three-point domain: the **first** query is point `0`
or point `1` according to the choice drawn, and the second is always point `2`.

Fixing the choice sequence gives an ordinary `AdaptiveRule` by `induced`, which
is the whole modelling point — there is no factorization theorem in between.
-/
@[expose] public def coinRule : StochasticRule (Fin 3) (Fin 2) (Fin 2) 2
  | ⟨0, _⟩ => fun _ c => if c = 0 then 0 else 1
  | ⟨1, _⟩ => fun _ _ => 2

/-- **The choice changes the algorithm.** Two choice sequences induce
deterministic rules that open at different points, so the theorem below is not
the deterministic statement wearing a weight. -/
public theorem coinRule_realizations_differ :
    ruleVisit (induced coinRule ![0, 0]) (fun _ => 0) 0
      ≠ ruleVisit (induced coinRule ![1, 1]) (fun _ => 0) 0 := by
  decide

/-- Every realization never revisits, so the whole family lies in the class the
printed sources quantify over. -/
public theorem coinRule_noRevisit (c d : Fin 2 → Fin 2) :
    Function.Injective (ruleVisit (induced coinRule c) d) := by
  revert c d
  decide

/-- The fair coin: each of the four choice sequences drawn with probability
`1/4`. -/
@[expose] public noncomputable def coinWeight : (Fin 2 → Fin 2) → ℝ := fun _ => 1 / 4

/-- The coin is a probability distribution. -/
public theorem sum_coinWeight : ∑ c : Fin 2 → Fin 2, coinWeight c = 1 := by
  simp [coinWeight, Finset.sum_const]

/-- `probeRule` as a stochastic rule with no randomness to draw on: the
deterministic class sits inside the stochastic one, with `Unit` as the choice
alphabet. -/
@[expose] public def probeStochastic : StochasticRule (Fin 3) (Fin 2) Unit 2 :=
  fun k h _ => probeRule k h

/-- Fixing the only choice sequence recovers `probeRule` itself. -/
public theorem induced_probeStochastic (c : Fin 2 → Unit) :
    induced probeStochastic c = probeRule := rfl

/-- The trivial weight on the single `Unit` choice sequence. -/
@[expose] public noncomputable def trivialWeight : (Fin 2 → Unit) → ℝ := fun _ => 1

/-- It too has total mass one — there is exactly one choice sequence. -/
public theorem sum_trivialWeight : ∑ c : Fin 2 → Unit, trivialWeight c = 1 := by
  simp [trivialWeight, Finset.sum_const]

/--
**A coin-flipping rule scores exactly what a deterministic one scores.** Against
the uniform weighting of the objectives — permutation-invariant by
`uniform_is_permInvariant` — the fair-coin rule and the branching deterministic
`probeRule` have the same aggregate performance.

This is Igel–Toussaint's *"deterministic or stochastic"* quantifier on a witness
where both sides are non-trivial: `coinRule_realizations_differ` shows the coin
genuinely selects between different algorithms, and `probeRule_not_schedule`
shows the comparator is not a fixed schedule.
-/
public theorem nfl_coinRule_vs_probeRule (Ψ : (Fin 2 → Fin 2) → ℝ) :
    stochasticTrace (fun _ : Fin 3 → Fin 2 => (1 : ℝ)) Ψ coinWeight coinRule
      = stochasticTrace (fun _ : Fin 3 → Fin 2 => (1 : ℝ)) Ψ trivialWeight
          probeStochastic :=
  nfl_stochastic_of_permInvariant (uniform_is_permInvariant _ _)
    (sum_coinWeight.trans sum_trivialWeight.symm) coinRule probeStochastic
    coinRule_noRevisit
    (fun c d => by rw [induced_probeStochastic c]; exact probeRule_noRevisit d) Ψ

/-! ## The condition is met by almost nothing

Igel–Toussaint's Theorem 3 at their own example: the Boolean functions
`{0,1}² → {0,1}`, so a four-point domain and a two-point codomain.

Of the `2^16 − 1 = 65535` non-empty sets of objectives, exactly `2^5 − 1 = 31`
are permutation-closed. So the `iff` proved above characterizes No Free Lunch by
a condition that a randomly chosen prior meets with probability about `5·10⁻⁴`,
and the printed point is that this collapses further, fast, as the alphabets
grow. -/

/-- **The count, at print's own example.** Stated with `+ 1` on the left, as in
the library, so `31` appears as `32 − 1`. -/
public theorem card_cup_boolean :
    Nat.card {F : Set (Fin 4 → Fin 2) //
        ClosedUnderPermutation F ∧ F.Nonempty} + 1 = 32 := by
  simpa using card_closedUnderPermutation_nonempty (X := Fin 4) (Y := Fin 2)

/-- The denominator: all non-empty sets of Boolean objectives on four points. -/
public theorem card_nonempty_boolean :
    Nat.card {F : Set (Fin 4 → Fin 2) // F.Nonempty} + 1 = 65536 := by
  simpa using card_nonempty_set_objective (X := Fin 4) (Y := Fin 2)

/-- **The fraction, at print's own example**: `31 / 65535`, well under a
thousandth. -/
public theorem fraction_cup_boolean :
    (Nat.card {F : Set (Fin 4 → Fin 2) // ClosedUnderPermutation F ∧ F.Nonempty} : ℚ)
        / (Nat.card {F : Set (Fin 4 → Fin 2) // F.Nonempty} : ℚ)
      = 31 / 65535 := by
  rw [fraction_closedUnderPermutation (X := Fin 4) (Y := Fin 2)]
  norm_num [show (2 : ℕ) + 2 + 1 = 5 from rfl, show (2 : ℕ) ^ 4 = 16 from rfl]

/-! ## And structured spaces never meet it

Theorem 3 counts; Theorem 4 rules out. Three points and a single edge already
show both sides of the disjunction, and that neither is idle. -/

/-- Three points, one edge. The smallest non-trivial neighbourhood relation:
`0` and `1` neighbour, nothing else does. -/
@[expose] public def oneEdge : SimpleGraph (Fin 3) where
  Adj a b := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
  symm := ⟨by intro a b h; tauto⟩
  loopless := ⟨by rintro a (⟨h, h'⟩ | ⟨h, h'⟩) <;> exact absurd (h.symm.trans h') (by decide)⟩

/-- **Theorem 4 at the smallest instance.** One edge on three points is enough:
some relabelling moves the edge off itself. What that does *not* say is that no
permutation-closed prior can be built here — see the non-claim in
`AISafetyAtlas.Learning.Sharp`; that step is print's Examples 2 and 3 and is not
formalized. -/
public theorem oneEdge_not_permInvariant :
    ∃ (a b : Fin 3) (π : Equiv.Perm (Fin 3)),
      ¬ (oneEdge.Adj (π a) (π b) ↔ oneEdge.Adj a b) :=
  exists_perm_adj_not_iff oneEdge ⟨0, 1, Or.inl ⟨rfl, rfl⟩⟩
    ⟨0, 2, by decide, by rintro (⟨-, h⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)⟩

/-- The complete graph *is* fixed by every relabelling — one of the two escapes
`forall_adj_or_forall_not_adj_of_permInvariant` leaves open. -/
public theorem top_permInvariant (π : Equiv.Perm (Fin 3)) (a b : Fin 3) :
    (⊤ : SimpleGraph (Fin 3)).Adj (π a) (π b) ↔ (⊤ : SimpleGraph (Fin 3)).Adj a b := by
  simp [π.injective.ne_iff]

/-- And so is the empty graph, which is the other. Both escapes are occupied, so
the disjunction is a real dichotomy and not a theorem with one live branch. -/
public theorem bot_permInvariant (π : Equiv.Perm (Fin 3)) (a b : Fin 3) :
    (⊥ : SimpleGraph (Fin 3)).Adj (π a) (π b) ↔ (⊥ : SimpleGraph (Fin 3)).Adj a b := by
  simp

/-- One edge on three points, **plus every self-loop**. Print's neighbourhood
relation is required symmetric and nothing more, so this is a legal one, and it
is non-trivial in print's own sense: `0` and `1` neighbour, `0` and `2` do not.

It is not a `SimpleGraph`, so `exists_perm_adj_not_iff` cannot be *instantiated*
at it. Be precise about what that is worth: `loopedEdge` is symmetric, and for a
symmetric relation `fun a b => a ≠ b ∧ r a b` is a legal `SimpleGraph` carrying
both non-triviality clauses, so the conclusion is still *derivable* from the
graph form. Dropping irreflexivity buys applicability, not strength. The axis
that buys strength is symmetry — see `arrowRel` below. -/
@[expose] public def loopedEdge (a b : Fin 3) : Prop :=
  a = b ∨ (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)

/-- **Theorem 4 at a relation no graph can be instantiated at.** -/
public theorem loopedEdge_not_permInvariant :
    ∃ (a b : Fin 3) (π : Equiv.Perm (Fin 3)),
      ¬ (loopedEdge (π a) (π b) ↔ loopedEdge a b) :=
  exists_perm_rel_not_iff ⟨0, 1, by decide, Or.inr (Or.inl ⟨rfl, rfl⟩)⟩
    ⟨0, 2, by decide, by rintro (h | ⟨-, h⟩ | ⟨h, -⟩) <;> exact absurd h (by decide)⟩

/-- The **diagonal** relation is permutation-invariant. It is *trivial* in
print's sense — no two distinct points are related — so Theorem 4 says nothing
about it, and it is not a counterexample to anything.

It is here for `rel_diag_iff_of_permInvariant`: the diagonal is a live degree of
freedom that `forall_rel_of_permInvariant` does not constrain, which is why the
two are separate facts rather than one. -/
public theorem eq_permInvariant (π : Equiv.Perm (Fin 3)) (a b : Fin 3) :
    (π a = π b) ↔ (a = b) :=
  π.injective.eq_iff

/-- **A single arrow on two points.** Print requires a neighbourhood relation to
be symmetric; this one is not, and it is where the widening is real rather than
merely convenient.

On a two-element type *no* symmetric relation can be non-trivial in print's
sense: the only distinct pairs are `(0,1)` and `(1,0)`, and symmetry forces them
to agree, so one of the two clauses always fails. `arrowRel` satisfies both. So
print's Theorem 4 cannot even be *posed* here, while
`exists_perm_rel_not_iff` decides it — and unlike `loopedEdge` this is not a
`SimpleGraph` in disguise, since the symmetrization that rescues the looped case
is exactly what is unavailable. -/
@[expose] public def arrowRel (a b : Fin 2) : Prop := a = 0 ∧ b = 1

/-- `arrowRel` is not symmetric, so the graph form has nothing to be applied
to. -/
public theorem arrowRel_not_symmetric : ¬ ∀ a b : Fin 2, arrowRel a b → arrowRel b a :=
  fun h => absurd (h 0 1 ⟨rfl, rfl⟩).1 (by decide)

/-- **Theorem 4 on the axis that genuinely widens print.** -/
public theorem arrowRel_not_permInvariant :
    ∃ (a b : Fin 2) (π : Equiv.Perm (Fin 2)),
      ¬ (arrowRel (π a) (π b) ↔ arrowRel a b) :=
  exists_perm_rel_not_iff ⟨0, 1, by decide, ⟨rfl, rfl⟩⟩
    ⟨1, 0, by decide, fun h => absurd h.1 (by decide)⟩

end AISafetyAtlas.Examples.Learning
