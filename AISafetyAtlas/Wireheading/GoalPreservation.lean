module

public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# On-policy goal preservation under realistic self-modification

This is a deterministic finite-step specialization of Everitt, Filan, Daswani
and Hutter, *Self-Modification of Policy and Utility Function in Rational
Agents*, **AGI 2016, LNCS 9782, Theorem 12** — *"Realistic policy-modifying
agents make safe modifications"*.

## Two numberings, and where the proofs are

The published chapter states its theorems and **proves none of them**:

> Proofs for all theorems are provided in a technical report

— which is `arXiv:1605.03142`. So for this source the published text is
canonical for **statements**, and the technical report is the only place any
**proof** exists. The two number the same results differently:

| published (AGI 2016) | technical report (arXiv:1605.03142) |
|---|---|
| Theorem 10, hedonistic agents self-modify | Theorem 14 |
| Theorem 11, ignorant agents may self-modify | Theorem 15 |
| **Theorem 12**, realistic policy-modifying agents make safe modifications | **Theorem 16** |
| Definitions 1, 3, 7, 8, 9 | Definitions 3, 5, 10, 11, 12 |
| — | Lemma 13, Definition 18, Lemma 19, **Theorem 20**, Theorem 21 |

The last row is proof apparatus the published chapter does not print, **not**
material it dropped. Theorem 20 (optimal policy existence) sits in the report's
Appendix A and the proof of Theorem 12 opens by invoking it:

> By Theorem 20 in Appendix A, there is a non-modifying modification-independent
> optimal policy `π′`.

That is what makes `Q^re_t(æ_<t π(æ_<t))` modification-independent for optimal
`π`, and it is what `GoalPreservationSource.Model.initial_dominates` assumes
instead of deriving. So the gap the atlas records there is a real gap against
the only proof that exists.

The source theorem assumes modification-independent belief and current utility,
full-support stochastic percepts, and realistic value functions that anticipate
the future policy.  Here a named-policy model exposes the same proof mechanism:
the current objective evaluates the continuation actually selected by a
self-modifying action.  Strictly positive discounting makes an inferior next
policy produce an inferior current action, so optimality propagates on-policy.

This theorem is deliberately only deterministic.  It does not claim the full
stochastic theorem or off-policy preservation.
-/

namespace AISafetyAtlas.Wireheading.GoalPreservation

/--
A deterministic named-policy model of explicit self-modification.

`act p h = (w, p')` selects a world action and the policy name used next.
`continuation p h` is evaluated using the fixed initial objective.  `coherent`
is the realistic Bellman equation.  `names_surjective` is a deliberately strong
deterministic replacement for the source's stochastic/full-support step: at
each history, every candidate action pair is produced by some represented
policy.  It is stronger than the source's policy-naming assumption, and the
source explicitly notes that not every policy can have a name.

**Cardinality consequence.**  `names_surjective` demands a surjection
`PolicyName → WorldAction × PolicyName` at every history.  If `WorldAction` has
at least two elements then no finite nonempty `PolicyName` admits one, so every
model with a genuine choice of world action has an infinite name type.
`AISafetyAtlas.Examples.SixTargets.twoActionGoalModel` witnesses that the field
is nonetheless satisfiable, at `WorldAction = Bool` and `PolicyName = ℕ`.

**Division of labour.**  `next_policy_optimal` is where the assumptions do
work: it consumes `names_surjective` and `discount_pos`.  `run_optimal` lifts it
by induction along the reached path.  `goal_preservation` is then a corollary
about two maximizers of the same function agreeing, and should not be read as
carrying the module's content on its own.
-/
public structure Model (History WorldAction PolicyName : Type*) where
  act : PolicyName → History → WorldAction × PolicyName
  next : History → WorldAction → History
  utility : History → WorldAction → ℝ
  discount : ℝ
  discount_pos : 0 < discount
  continuation : PolicyName → History → ℝ
  coherent :
    ∀ p h,
      continuation p h =
        utility h (act p h).1 +
          discount * continuation (act p h).2 (next h (act p h).1)
  names_surjective :
    ∀ h (a : WorldAction × PolicyName), ∃ p, act p h = a

namespace Model

variable {History WorldAction PolicyName : Type*}

/-- Realistic current-objective value of a world-action/next-policy pair. -/
@[expose] public def qValue (M : Model History WorldAction PolicyName)
    (h : History) (a : WorldAction × PolicyName) : ℝ :=
  M.utility h a.1 + M.discount * M.continuation a.2 (M.next h a.1)

/-- A named policy chooses a maximizing self-modifying action at `h`. -/
@[expose] public def OptimalAt (M : Model History WorldAction PolicyName)
    (p : PolicyName) (h : History) : Prop :=
  ∀ a, M.qValue h a ≤ M.qValue h (M.act p h)

/--
The policy selected by an optimal realistic action is optimal at the reached
next history.
-/
public theorem next_policy_optimal
    (M : Model History WorldAction PolicyName)
    {p : PolicyName} {h : History}
    (optimal : M.OptimalAt p h) :
    let selected := M.act p h
    M.OptimalAt selected.2 (M.next h selected.1) := by
  dsimp only
  intro candidate
  let selected := M.act p h
  let nextHistory := M.next h selected.1
  obtain ⟨named, hnamed⟩ := M.names_surjective nextHistory candidate
  have hcompare := optimal (selected.1, named)
  have hcontinuation :
      M.continuation named nextHistory ≤
        M.continuation selected.2 nextHistory := by
    dsimp [qValue, selected, nextHistory] at hcompare
    have hmul :
        M.discount * M.continuation named (M.next h (M.act p h).1) ≤
          M.discount *
            M.continuation (M.act p h).2 (M.next h (M.act p h).1) := by
      linarith
    dsimp [selected, nextHistory]
    nlinarith [M.discount_pos]
  calc
    M.qValue nextHistory candidate =
        M.qValue nextHistory (M.act named nextHistory) := by rw [hnamed]
    _ = M.continuation named nextHistory := (M.coherent named nextHistory).symm
    _ ≤ M.continuation selected.2 nextHistory := hcontinuation
    _ = M.qValue nextHistory (M.act selected.2 nextHistory) :=
      M.coherent selected.2 nextHistory

/-- The policy name and history reached after `steps` on-policy modifications. -/
@[expose] public def run (M : Model History WorldAction PolicyName) :
    ℕ → PolicyName → History → PolicyName × History
  | 0, p, h => (p, h)
  | n + 1, p, h =>
      let current := M.run n p h
      let selected := M.act current.1 current.2
      (selected.2, M.next current.2 selected.1)

/-- Optimality propagates along the actually selected self-modification path. -/
public theorem run_optimal
    (M : Model History WorldAction PolicyName)
    (initialPolicy : PolicyName) (initialHistory : History)
    (initiallyOptimal : ∀ h, M.OptimalAt initialPolicy h)
    (steps : ℕ) :
    let current := M.run steps initialPolicy initialHistory
    M.OptimalAt current.1 current.2 := by
  induction steps with
  | zero => exact initiallyOptimal initialHistory
  | succ n ih =>
      simp only [run]
      exact M.next_policy_optimal ih

/--
**On-policy goal preservation (deterministic specialization of published
Theorem 12, extended-version Theorem 16).**

At every reached history, the current self-modified policy and the initial
policy obtain the same maximizing value under the fixed initial objective.
-/
public theorem goal_preservation
    (M : Model History WorldAction PolicyName)
    (initialPolicy : PolicyName) (initialHistory : History)
    (initiallyOptimal : ∀ h, M.OptimalAt initialPolicy h)
    (steps : ℕ) :
    let current := M.run steps initialPolicy initialHistory
    M.qValue current.2 (M.act current.1 current.2) =
      M.qValue current.2 (M.act initialPolicy current.2) := by
  let current := M.run steps initialPolicy initialHistory
  have hcurrent : M.OptimalAt current.1 current.2 :=
    M.run_optimal initialPolicy initialHistory initiallyOptimal steps
  have hinitial : M.OptimalAt initialPolicy current.2 :=
    initiallyOptimal current.2
  exact le_antisymm
    (hinitial (M.act current.1 current.2))
    (hcurrent (M.act initialPolicy current.2))

end Model
end AISafetyAtlas.Wireheading.GoalPreservation
