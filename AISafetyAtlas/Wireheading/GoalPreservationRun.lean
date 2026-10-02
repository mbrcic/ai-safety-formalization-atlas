module

public import AISafetyAtlas.Wireheading.GoalPreservationSource

/-!
# Theorem 16 itself, run out over the whole trajectory, with no naming
surjectivity

Everitt, Filan, Daswani and Hutter, *Self-Modification of Policy and Utility
Function in Rational Agents*, arXiv:1605.03142v1, **Theorem 16** (published as
AGI 2016, LNCS 9782, Theorem 12; only the arXiv report has been read here).
Print's conclusion is its equation (13):

> Let `ρ` and `u₁` be modification-independent. Consider a self-modifying agent
> whose initial policy `π₁ = ι(p₁)` optimises the realistic value function
> `V₁^re`. Then, for every `t ≥ 1`, for all percept sequences `e_<t`, and for
> the action sequence `a_<t` given by `a_i = π_i(æ_<i)`, we have
> `Q₁^re(æ_<t π_t(æ_<t)) = Q₁^re(æ_<t π₁(æ_<t))`.

## Why this module exists

The atlas had the two halves and not the whole.

* `Wireheading.GoalPreservation` reaches equation (13) at every reached history,
  but only under `names_surjective` — *every* world-action/next-policy pair is
  emitted by some **named** policy. That premise is not print's. Print
  maximises over `Π`, the full policy space, which is a function space into
  `Ǎ × P` and therefore realises every pair for free; `P` is the set of *names*,
  and print says explicitly that not every policy has one. Requiring the named
  policies to be surjective conflates `Π` with `P`.
* `Wireheading.GoalPreservationSource` removes that premise from the **one-step**
  argument, but stops there: it never iterates, and it takes `initial_dominates`
  as a primitive.

This module supplies the missing induction and derives `initial_dominates`.

## What replaces the surjectivity assumption

Two fields, both printed:

* `bellman` is print's Definition 12 written out: equation (7),
  `V_t^{re,π}(æ_<k) = Q_t^re(æ_<k π(æ_<k))`, composed with the Q-recursion of
  equation (8). `GoalPreservationSource.Model` has no such field, which is
  exactly why it could not iterate: nothing there tied `contValue` to `qValue`.
* `initial_optimal` is print's hypothesis that `π₁` optimises `V₁^re`, unfolded
  through equation (7) and through `Π` being a full function space:
  the supremum over named policies of `Q(h, ·)` is the supremum over all action pairs. It quantifies over **all** action
  pairs, and that quantifier is print's, not an extra strength — it is the same
  supremum over actions that print's own equation (14) takes.

`initial_dominates` is then a theorem (`contValue_le_initial`), not an
assumption: `contValue p h = qValue h (act p h) ≤ qValue h (act initial h) =
contValue initial h`.

## Which numbering this module uses

All numbers here are the **arXiv technical report's** (`1b7a3c09…`): Definition
12, Lemma 13, equations (7), (8) and (13), Theorem 16, and Appendix A's
Theorems 20 and 21. The publisher-typeset AGI 2016 chapter (LNAI 9782, pp. 1–11,
in `4486e912…`) numbers the same material differently and prints no proofs at
all — it says "Proofs for all theorems are provided in a technical report". The
concordance for what this module uses:

| arXiv technical report | AGI 2016 chapter |
|---|---|
| Definition 12 (realistic value functions), eqs. (7)–(8) | Definition 9 |
| Lemma 13 (iterative value functions), eqs. (9)–(11) | *absent* |
| Theorem 16, conclusion eq. **(13)** | Theorem 12, conclusion eq. **(7)** |
| Appendix A, Theorems 20 and 21 | *absent* |

The collision is worth stating outright: "equation (7)" means the arXiv V-from-Q
identity throughout this module, **not** the chapter's numbering of Theorem 16's
conclusion. The two statements of the theorem were read side by side — the
chapter's page rendered as an image, the report's from its text layer — and they
agree word for word, lead-in sentence included, up to that renumbering.

## The reading of "for all percept sequences"

Print quantifies over percept sequences `e_<t` and takes the action sequence
on-policy. `run` is that: a percept stream `ℕ → Percept` is given, and the
policy name and history at step `n` are what the actually-selected
self-modifications produce. So the theorem is on-policy in the actions and
universal in the percepts, which is print's shape.

## Explicit non-claims

* **Finitely many percepts**, as in `GoalPreservationSource`: `E_{e_t}` is a
  normalised `Finset` sum, not an integral. No measure theory.
* **Not modification-independence itself.** Print derives `Q_t^re(æ_<t π(æ_<t))`
  modification-independent from modification-independent `ρ` and `u_t` together
  with its Appendix A Theorem 20 (optimal policy existence) and Theorem 21
  (optimal policy name). Neither is reproduced. Here `contValue` is a function
  of the name and the history, so modification-independence is built into the
  signature rather than proved; `initial_optimal` asserts what Theorems 20 and
  21 would supply. **This is the gap the atlas still owes on this source**, and
  it is the same one `GoalPreservationSource` records.
* **Policy modification only**, not utility modification. Print's Theorems 14
  and 15 (hedonistic and ignorant agents) are not formalized anywhere in the
  atlas.
* **Not a claim about real self-modifying systems.** No AI-system bridge is
  asserted.

Landscape entry: `LAND-GOAL-001` (this module is a second declaration set on
that row's source).
-/

namespace AISafetyAtlas.Wireheading.GoalPreservationRun

open AISafetyAtlas.Wireheading

/-- **Print's `Π`, the set of all policies.**

Definition 3 reads: *"Let `Π = {(𝒜 × ℰ)* → 𝒜}` be the set of all policies, and
let `ι : 𝒫 → Π` assign names to policies."*  So `Π` is the full function space
from histories to actions, with `𝒜 = 𝒜̌ × 𝒫` — a world action paired with the
name of the next policy.  That is exactly the codomain of `Model.act`, which is
therefore `ι` and not merely an action-selection rule.

Naming `Π` costs nothing and buys the distinction print draws immediately after:
`𝒫` and `Π` are different sets, `ι` need not be onto, and *"some policies will
necessarily lack names"*.  Nothing in this module assumes otherwise. -/
public abbrev Policy (History WorldAction PolicyName : Type*) : Type _ :=
  History → WorldAction × PolicyName

/--
A realistic policy-self-modification model at print's own hypotheses.

Every field but `bellman` and `initial_optimal` is `GoalPreservationSource.Model`'s.
Those two replace its `initial_dominates`, which becomes a theorem.
-/
public structure Model (History WorldAction PolicyName Percept : Type*)
    [Fintype Percept] where
  /-- `ι(p)` applied at `h`: a world action and the *name* of the next policy. -/
  act : PolicyName → History → WorldAction × PolicyName
  /-- History extension by a world action and the percept received. -/
  extend : History → WorldAction → Percept → History
  /-- The initial utility `u₁`. -/
  utility : History → ℝ
  /-- Discount factor `γ`. -/
  discount : ℝ
  /-- It is positive. -/
  discount_pos : 0 < discount
  /-- Probability mass over the next percept. -/
  prob : History → WorldAction → Percept → ℝ
  /-- Normalised for every history and world action. -/
  prob_sum_one : ∀ h a, ∑ e : Percept, prob h a e = 1
  /-- **Full support.** What turns a pointwise strict inequality into a strict
  inequality of expectations. -/
  prob_pos : ∀ h a e, 0 < prob h a e
  /-- `V_1^{re,ι(p)}`, the realistic continuation value of a named policy under
  the initial utility. -/
  contValue : PolicyName → History → ℝ
  /-- The initial policy's name `p₁`. -/
  initial : PolicyName
  /-- **Print's Definition 12**, equation (7) `V^{re,π}(æ_<k) = Q^re(æ_<k
  π(æ_<k))` composed with the Q-recursion of equation (8), written out. This is
  what `GoalPreservationSource.Model` lacks, and the reason it cannot iterate
  its own induction step. -/
  bellman : ∀ p h,
    contValue p h =
      ∑ e : Percept, prob h (act p h).1 e *
        (utility (extend h (act p h).1 e) +
          discount * contValue (act p h).2 (extend h (act p h).1 e))
  /-- **`π₁` optimises `V₁^re`**, print's hypothesis, unfolded through equation
  (7) and through `Π` being the full function space into `Ǎ × P`. -/
  initial_optimal : ∀ (h : History) (a : WorldAction × PolicyName),
    (∑ e : Percept, prob h a.1 e *
        (utility (extend h a.1 e) + discount * contValue a.2 (extend h a.1 e)))
      ≤ ∑ e : Percept, prob h (act initial h).1 e *
        (utility (extend h (act initial h).1 e) +
          discount * contValue (act initial h).2 (extend h (act initial h).1 e))

namespace Model

variable {History WorldAction PolicyName Percept : Type*} [Fintype Percept]
variable (M : Model History WorldAction PolicyName Percept)

/-- **Print's `ι`.**  Definition 3's naming map, which `act` already is: it
sends a name to the policy that name denotes.  Stated separately so the
quadruple `(𝒜̌, ℰ, 𝒫, ι)` has all four components present as objects.

`ι` is **not** assumed surjective anywhere, which is print's own reading: it
says *"some policies will necessarily lack names"*. -/
@[expose] public def name : PolicyName → Policy History WorldAction PolicyName :=
  M.act

/-- `ι(p)` is `act p`, definitionally: naming the map changed nothing. -/
public theorem name_eq_act (p : PolicyName) : M.name p = M.act p := rfl



/-! ## `initial_dominates` is derived, not assumed -/

/--
Print's domination fact, obtained from equation (7) and the optimality of `π₁`:
no named policy's continuation value beats the initial policy's.

`GoalPreservationSource.Model` takes this as a field. Here it is a two-line
consequence, which is the point: it was never an independent assumption.
-/
public theorem contValue_le_initial (p : PolicyName) (h : History) :
    M.contValue p h ≤ M.contValue M.initial h := by
  rw [M.bellman p h, M.bellman M.initial h]
  exact M.initial_optimal h (M.act p h)

/-- The source-aligned one-step interface, with `initial_dominates` discharged. -/
@[expose] public noncomputable def toSource :
    GoalPreservationSource.Model History WorldAction PolicyName Percept where
  act := M.act
  extend := M.extend
  utility := M.utility
  discount := M.discount
  discount_pos := M.discount_pos
  prob := M.prob
  prob_sum_one := M.prob_sum_one
  prob_pos := M.prob_pos
  contValue := M.contValue
  initial := M.initial
  initial_dominates := M.contValue_le_initial

/-- `Q₁^re`, taken from the source-aligned interface so that nothing is
redefined. -/
@[expose] public noncomputable def qValue (h : History)
    (a : WorldAction × PolicyName) : ℝ :=
  M.toSource.qValue h a

/-- Acting `Q₁^re`-optimally at a history. The quantifier is over all
world-action/next-policy pairs, which is print's supremum over actions in
equation (14). -/
@[expose] public def OptimalAt (p : PolicyName) (h : History) : Prop :=
  M.toSource.OptimalAt p h

/-- Equations (7) and (8) in the vocabulary of `qValue`. -/
public theorem contValue_eq_qValue (p : PolicyName) (h : History) :
    M.contValue p h = M.qValue h (M.act p h) := by
  rw [M.bellman p h]
  rfl

/-- The initial policy is `Q₁^re`-optimal at every history. -/
public theorem optimalAt_initial (h : History) : M.OptimalAt M.initial h :=
  fun a => M.initial_optimal h a

/-! ## The induction step

`GoalPreservationSource.Model.selected_matches_initial` does the work; all that
is added is the conversion from "the selected continuation matches the initial
one" to "the selected policy is itself optimal", which is where `bellman` and
`initial_optimal` are spent.
-/

/--
**The induction step.** If the current policy acts `Q₁^re`-optimally, then the
policy it self-modifies into acts `Q₁^re`-optimally at every successor history.

No condition whatever is imposed on which policies have names.
-/
public theorem optimalAt_next {p : PolicyName} {h : History}
    (hopt : M.OptimalAt p h) (e : Percept) :
    M.OptimalAt (M.act p h).2 (M.extend h (M.act p h).1 e) := by
  intro a
  have hmatch := M.toSource.selected_matches_initial hopt e
  have hsel : M.contValue (M.act p h).2 (M.extend h (M.act p h).1 e)
      = M.contValue M.initial (M.extend h (M.act p h).1 e) := hmatch
  calc M.toSource.qValue (M.extend h (M.act p h).1 e) a
      ≤ M.toSource.qValue (M.extend h (M.act p h).1 e)
          (M.act M.initial (M.extend h (M.act p h).1 e)) :=
        M.optimalAt_initial (M.extend h (M.act p h).1 e) a
    _ = M.contValue M.initial (M.extend h (M.act p h).1 e) :=
        (M.contValue_eq_qValue M.initial (M.extend h (M.act p h).1 e)).symm
    _ = M.contValue (M.act p h).2 (M.extend h (M.act p h).1 e) := hsel.symm
    _ = M.toSource.qValue (M.extend h (M.act p h).1 e)
          (M.act (M.act p h).2 (M.extend h (M.act p h).1 e)) :=
        M.contValue_eq_qValue (M.act p h).2 (M.extend h (M.act p h).1 e)

/-! ## The trajectory

`percepts` is print's arbitrary percept sequence `e_<t`; the actions are
on-policy, `a_i = π_i(æ_<i)`.
-/

/-- The policy name and history after `n` steps, under a given percept stream. -/
@[expose] public def run (percepts : ℕ → Percept) (start : History) :
    ℕ → PolicyName × History
  | 0 => (M.initial, start)
  | n + 1 =>
      let current := run percepts start n
      let selected := M.act current.1 current.2
      (selected.2, M.extend current.2 selected.1 (percepts n))

/-- **Optimality propagates along the whole trajectory.** -/
public theorem run_optimal (percepts : ℕ → Percept) (start : History) :
    ∀ n : ℕ, M.OptimalAt (M.run percepts start n).1 (M.run percepts start n).2 := by
  intro n
  induction n with
  | zero =>
      simp only [run]
      exact M.optimalAt_initial start
  | succ n ih =>
      simp only [run]
      exact M.optimalAt_next ih (percepts n)

/--
**Theorem 16, equation (13).**

At every step of every percept sequence, the action the current
self-modified policy takes has exactly the `Q₁^re` value of the action the
initial policy would have taken there. Self-modification is value-neutral for
the initial objective.

This is the full printed conclusion — `GoalPreservation.goal_preservation`
reaches it only under naming surjectivity, and `GoalPreservationSource` reaches
only its one-step ingredient.
-/
public theorem equation_thirteen (percepts : ℕ → Percept) (start : History)
    (n : ℕ) :
    M.qValue (M.run percepts start n).2
        (M.act (M.run percepts start n).1 (M.run percepts start n).2) =
      M.qValue (M.run percepts start n).2
        (M.act M.initial (M.run percepts start n).2) :=
  le_antisymm
    (M.optimalAt_initial (M.run percepts start n).2
      (M.act (M.run percepts start n).1 (M.run percepts start n).2))
    (M.run_optimal percepts start n
      (M.act M.initial (M.run percepts start n).2))

/--
The continuation-value form of the same conclusion: the policy in force at step
`n` is worth exactly what the initial policy is worth there.
-/
public theorem run_contValue_eq_initial (percepts : ℕ → Percept)
    (start : History) (n : ℕ) :
    M.contValue (M.run percepts start n).1 (M.run percepts start n).2 =
      M.contValue M.initial (M.run percepts start n).2 := by
  rw [M.contValue_eq_qValue (M.run percepts start n).1 (M.run percepts start n).2,
    M.contValue_eq_qValue M.initial (M.run percepts start n).2]
  exact M.equation_thirteen percepts start n

end Model
end AISafetyAtlas.Wireheading.GoalPreservationRun
