module

public import AISafetyAtlas.Wireheading.GoalPreservationSource
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

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
* **Not the existence of an optimal named policy.** Print derives `Q_t^re(æ_<t π(æ_<t))`
  modification-independent from modification-independent `ρ` and `u_t` together
  with its Appendix A Theorem 20 (optimal policy existence) and Theorem 21
  (optimal policy name). Neither is reproduced. Here `contValue` is a function
  of the name and the history, so modification-independence is built into the
  signature rather than proved; `initial_optimal` asserts what Theorems 20 and
  21 would supply. On histories that record names, `ModIndepModel` derives the
  modification-independence of `V₁^{re,π₁}` from modification-independent `ρ`
  and `u₁`, `γ < 1` and a bounded `V₁^{re,π₁}` (`ModIndepModel.initial_check`);
  the existence of an optimal named policy (`initial_optimal`, Theorems 20 and
  21) is still asserted there. **That existence is the gap the atlas still owes
  on this source**, and `GoalPreservationSource` records it too.
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

/-!
## Histories that record the selected policy name

Print's Definition 3 (arXiv:1605.03142v1, PDF p. 5) takes actions
`𝒜 = 𝒜̌ × 𝒫`, a world action paired with the name of the next policy, and
histories over `𝒜 × ℰ`; Definition 12 (PDF p. 8) extends the history by the full
action `a_k`. `Model.extend` receives only the world action, so in it no policy
can read which name was selected at an earlier step, although `Π` is all
functions on `(𝒜 × ℰ)*` and Assumption 8 (PDF p. 7) makes only `ρ` and `u`
modification-independent.

`NamedModel` is the carrier with `extend` receiving the full action. It is wider
than `Model`: `Model.toNamed` embeds every `Model`, with every `Q` value unchanged
(`Model.toNamed_namedQValue`).

**What the wider history costs.** Erasing the names made print's
modification-independence hold by construction. Once names are recorded it must
be stated, at exactly the two places the one-step argument compares a selected
continuation `(ǎ, q)` with `(ǎ, p₁)`:

* `utility_modIndep`, print's hypothesis of Theorem 16 that `u₁` is
  modification-independent (Definition 7 / Assumption 8);
* `initial_modIndep`, that `V₁^{re,π₁}` is: print derives it from
  modification-independent `ρ` and `u₁` through Appendix A, Theorems 20 and 21,
  which are not reproduced, so it is asserted here as `initial_optimal` asserts
  what those theorems supply. Both hold in every `Model.toNamed` by `rfl`, and
  both are theorems on `ModIndepModel` (below), which states print's
  modification-independent `ρ` and `u₁`, `γ < 1` and a bounded `V₁^{re,π₁}`
  instead (`ModIndepModel.toNamedModel`).
-/

/-- A realistic policy-self-modification model whose histories record the full
selected action, world action and next policy name (print's Definition 3 and
Definition 12). -/
public structure NamedModel (History WorldAction PolicyName Percept : Type*)
    [Fintype Percept] where
  /-- `ι(p)` applied at `h`: a world action and the *name* of the next policy. -/
  act : PolicyName → History → WorldAction × PolicyName
  /-- History extension by the full selected action and the percept received. -/
  extend : History → WorldAction × PolicyName → Percept → History
  /-- The initial utility `u₁`. -/
  utility : History → ℝ
  /-- Discount factor `γ`. -/
  discount : ℝ
  /-- It is positive. -/
  discount_pos : 0 < discount
  /-- Probability mass over the next percept, indexed by the world action. -/
  prob : History → WorldAction → Percept → ℝ
  /-- Normalised for every history and world action. -/
  prob_sum_one : ∀ h a, ∑ e : Percept, prob h a e = 1
  /-- Full support. -/
  prob_pos : ∀ h a e, 0 < prob h a e
  /-- `V_1^{re,ι(p)}`, the realistic continuation value of a named policy. -/
  contValue : PolicyName → History → ℝ
  /-- The initial policy's name `p₁`. -/
  initial : PolicyName
  /-- **`u₁` is modification-independent** (print's hypothesis of Theorem 16): it
  does not read which policy name the last action selected. -/
  utility_modIndep : ∀ h w p p' e, utility (extend h (w, p) e) = utility (extend h (w, p') e)
  /-- **`V₁^{re,π₁}` is modification-independent**, which print derives from its
  Appendix A Theorems 20 and 21 (not reproduced); derived on `ModIndepModel`
  (`ModIndepModel.initial_modIndep`). -/
  initial_modIndep : ∀ h w p p' e,
    contValue initial (extend h (w, p) e) = contValue initial (extend h (w, p') e)
  /-- Print's Definition 12, equations (7) and (8), with the full action in the
  history. -/
  bellman : ∀ p h,
    contValue p h =
      ∑ e : Percept, prob h (act p h).1 e *
        (utility (extend h (act p h) e) +
          discount * contValue (act p h).2 (extend h (act p h) e))
  /-- `π₁` optimises `V₁^re`, unfolded through equation (7) and `Π` being the
  full function space into `𝒜̌ × 𝒫`. -/
  initial_optimal : ∀ (h : History) (a : WorldAction × PolicyName),
    (∑ e : Percept, prob h a.1 e *
        (utility (extend h a e) + discount * contValue a.2 (extend h a e)))
      ≤ ∑ e : Percept, prob h (act initial h).1 e *
        (utility (extend h (act initial h) e) +
          discount * contValue (act initial h).2 (extend h (act initial h) e))

namespace NamedModel

variable {History WorldAction PolicyName Percept : Type*} [Fintype Percept]
variable (M : NamedModel History WorldAction PolicyName Percept)

/-- `Q₁^re` with the full action in the history (print's equation (8)). -/
@[expose] public noncomputable def namedQValue (h : History)
    (a : WorldAction × PolicyName) : ℝ :=
  ∑ e : Percept, M.prob h a.1 e *
    (M.utility (M.extend h a e) + M.discount * M.contValue a.2 (M.extend h a e))

/-- Acting `Q₁^re`-optimally at a history, over all action pairs. -/
@[expose] public def NamedOptimalAt (p : PolicyName) (h : History) : Prop :=
  ∀ a, M.namedQValue h a ≤ M.namedQValue h (M.act p h)

/-- Equations (7) and (8) in the vocabulary of `namedQValue`. -/
public theorem namedContValue_eq_qValue (p : PolicyName) (h : History) :
    M.contValue p h = M.namedQValue h (M.act p h) :=
  M.bellman p h

/-- No named policy's continuation value beats the initial policy's. -/
public theorem namedContValue_le_initial (p : PolicyName) (h : History) :
    M.contValue p h ≤ M.contValue M.initial h := by
  rw [M.bellman p h, M.bellman M.initial h]
  exact M.initial_optimal h (M.act p h)

/-- The initial policy is `Q₁^re`-optimal at every history. -/
public theorem namedOptimalAt_initial (h : History) : M.NamedOptimalAt M.initial h :=
  fun a => M.initial_optimal h a

/-- **The one-step argument with names in the history.** If the current policy
acts optimally, the continuation it selects is worth exactly the initial policy's
value at every successor. The comparison against `(ǎ, p₁)` uses the two
modification-independence fields, because the two histories now differ in the
recorded name. -/
public theorem named_selected_matches_initial {p : PolicyName} {h : History}
    (hopt : M.NamedOptimalAt p h) (e : Percept) :
    M.contValue (M.act p h).2 (M.extend h (M.act p h) e) =
      M.contValue M.initial (M.extend h (M.act p h) e) := by
  by_contra hne
  set w := (M.act p h).1
  set q := (M.act p h).2
  have hpair : M.act p h = (w, q) := rfl
  rw [hpair] at hne
  have hstrict : M.contValue q (M.extend h (w, q) e) <
      M.contValue M.initial (M.extend h (w, q) e) :=
    lt_of_le_of_ne (M.namedContValue_le_initial q _) hne
  have hlt : M.namedQValue h (w, q) < M.namedQValue h (w, M.initial) := by
    refine Finset.sum_lt_sum (fun e' _ => ?_) ⟨e, Finset.mem_univ e, ?_⟩
    · have hle := M.namedContValue_le_initial q (M.extend h (w, q) e')
      rw [M.initial_modIndep h w q M.initial e'] at hle
      have hu := M.utility_modIndep h w q M.initial e'
      have hdisc := mul_le_mul_of_nonneg_left hle M.discount_pos.le
      exact mul_le_mul_of_nonneg_left (by simp only; linarith) (M.prob_pos h w e').le
    · rw [M.initial_modIndep h w q M.initial e] at hstrict
      have hu := M.utility_modIndep h w q M.initial e
      have hdisc := mul_lt_mul_of_pos_left hstrict M.discount_pos
      exact mul_lt_mul_of_pos_left (by simp only; linarith) (M.prob_pos h w e)
  have hcmp := hopt (w, M.initial)
  rw [hpair] at hcmp
  exact absurd hcmp (not_le.mpr hlt)

/-- **The induction step**: optimality passes to the selected policy at every
successor history. -/
public theorem namedOptimalAt_next {p : PolicyName} {h : History}
    (hopt : M.NamedOptimalAt p h) (e : Percept) :
    M.NamedOptimalAt (M.act p h).2 (M.extend h (M.act p h) e) := by
  intro a
  calc M.namedQValue (M.extend h (M.act p h) e) a
      ≤ M.namedQValue (M.extend h (M.act p h) e) (M.act M.initial (M.extend h (M.act p h) e)) :=
        M.namedOptimalAt_initial _ a
    _ = M.contValue M.initial (M.extend h (M.act p h) e) :=
        (M.namedContValue_eq_qValue M.initial _).symm
    _ = M.contValue (M.act p h).2 (M.extend h (M.act p h) e) :=
        (M.named_selected_matches_initial hopt e).symm
    _ = M.namedQValue (M.extend h (M.act p h) e)
          (M.act (M.act p h).2 (M.extend h (M.act p h) e)) :=
        M.namedContValue_eq_qValue _ _

/-- The policy name and history after `n` steps, the history recording each
selected action in full. -/
@[expose] public def namedRun (percepts : ℕ → Percept) (start : History) :
    ℕ → PolicyName × History
  | 0 => (M.initial, start)
  | n + 1 =>
      let current := namedRun percepts start n
      let selected := M.act current.1 current.2
      (selected.2, M.extend current.2 selected (percepts n))

/-- Optimality propagates along the whole trajectory. -/
public theorem namedRun_optimal (percepts : ℕ → Percept) (start : History) :
    ∀ n : ℕ, M.NamedOptimalAt (M.namedRun percepts start n).1 (M.namedRun percepts start n).2 := by
  intro n
  induction n with
  | zero => exact M.namedOptimalAt_initial start
  | succ n ih => exact M.namedOptimalAt_next ih (percepts n)

/--
**Theorem 16, equation (13), with the selected names in the history**
(arXiv:1605.03142v1, Theorem 16): at every step of every percept sequence, the
current self-modified policy's action has the `Q₁^re` value of the initial
policy's action.
-/
public theorem named_equation_thirteen (percepts : ℕ → Percept) (start : History) (n : ℕ) :
    M.namedQValue (M.namedRun percepts start n).2
        (M.act (M.namedRun percepts start n).1 (M.namedRun percepts start n).2) =
      M.namedQValue (M.namedRun percepts start n).2
        (M.act M.initial (M.namedRun percepts start n).2) :=
  le_antisymm
    (M.namedOptimalAt_initial _ _)
    (M.namedRun_optimal percepts start n _)

end NamedModel

namespace Model

variable {History WorldAction PolicyName Percept : Type*} [Fintype Percept]
variable (M : Model History WorldAction PolicyName Percept)

/-- Every name-erasing model is a `NamedModel` whose extension ignores the name;
modification-independence then holds by `rfl`. -/
@[expose] public noncomputable def toNamed :
    NamedModel History WorldAction PolicyName Percept where
  act := M.act
  extend := fun h a e => M.extend h a.1 e
  utility := M.utility
  discount := M.discount
  discount_pos := M.discount_pos
  prob := M.prob
  prob_sum_one := M.prob_sum_one
  prob_pos := M.prob_pos
  contValue := M.contValue
  initial := M.initial
  utility_modIndep := fun _ _ _ _ _ => rfl
  initial_modIndep := fun _ _ _ _ _ => rfl
  bellman := M.bellman
  initial_optimal := M.initial_optimal

/-- The embedding keeps every `Q₁^re` value. -/
public theorem toNamed_namedQValue :
    M.toNamed.namedQValue = M.qValue :=
  rfl

end Model

/-!
## Definition 12 for every policy self-modification model

Print's Definition 12 (arXiv:1605.03142v1, PDF p. 8) defines `V^{re,π}` and
`Q^re` by equations (7) and (8) for any policy self-modification model `(𝒫, ι)`
of Definition 3; optimality enters only afterwards, in *"A realistic agent is a
policy optimising the realistic value functions"*. `NamedModel` also carries an
optimal initial name and the two modification-independence fields Theorem 16
uses. `RealisticModel` is the carrier of Definition 12 alone: full-action
histories, a normalised full-support percept distribution, and a solution of
(7)∘(8) on the named policies, with no initial name, no optimality and no
modification-independence. `NamedModel.toRealistic` forgets the extra fields
and keeps every `Q` value (`NamedModel.toRealistic_qValue`).

Equation (7) is stated for **every** policy of `Π`, named or not:
`realisticValue π h := Q^re(h, π(h))`, and on a named policy it is the
continuation value (`realisticValue_name`).
-/

/-- **Print's Definition 12 setting** (arXiv:1605.03142v1, Definitions 3 and 12):
a policy self-modification model with full-action histories and a solution of
the realistic value recursion (7)∘(8) on its named policies. -/
public structure RealisticModel (History WorldAction PolicyName Percept : Type*)
    [Fintype Percept] where
  /-- `ι(p)` applied at `h`: a world action and the *name* of the next policy. -/
  act : PolicyName → History → WorldAction × PolicyName
  /-- History extension by the full selected action and the percept received. -/
  extend : History → WorldAction × PolicyName → Percept → History
  /-- The utility `u₁`. -/
  utility : History → ℝ
  /-- Discount factor `γ`. -/
  discount : ℝ
  /-- It is positive. -/
  discount_pos : 0 < discount
  /-- Probability mass over the next percept, indexed by the world action. -/
  prob : History → WorldAction → Percept → ℝ
  /-- Normalised for every history and world action. -/
  prob_sum_one : ∀ h a, ∑ e : Percept, prob h a e = 1
  /-- Full support. -/
  prob_pos : ∀ h a e, 0 < prob h a e
  /-- `V_1^{re,ι(p)}`, the realistic continuation value of a named policy. -/
  contValue : PolicyName → History → ℝ
  /-- Print's Definition 12, equations (7) and (8), with the full action in the
  history. -/
  bellman : ∀ p h,
    contValue p h =
      ∑ e : Percept, prob h (act p h).1 e *
        (utility (extend h (act p h) e) +
          discount * contValue (act p h).2 (extend h (act p h) e))

namespace RealisticModel

variable {History WorldAction PolicyName Percept : Type*} [Fintype Percept]
variable (M : RealisticModel History WorldAction PolicyName Percept)

/-- `Q₁^re(h a)`, print's equation (8), with the full action in the history. -/
@[expose] public noncomputable def qValue (h : History)
    (a : WorldAction × PolicyName) : ℝ :=
  ∑ e : Percept, M.prob h a.1 e *
    (M.utility (M.extend h a e) + M.discount * M.contValue a.2 (M.extend h a e))

/-- Acting `Q₁^re`-optimally at a history, over all action pairs. -/
@[expose] public def OptimalAt (p : PolicyName) (h : History) : Prop :=
  ∀ a, M.qValue h a ≤ M.qValue h (M.act p h)

/-- Equations (7) and (8) in the vocabulary of `qValue`, for a named policy. -/
public theorem contValue_eq_qValue (p : PolicyName) (h : History) :
    M.contValue p h = M.qValue h (M.act p h) :=
  M.bellman p h

/-- **Print's equation (7) for every policy** (arXiv:1605.03142v1, Definition 12:
`V_t^{re,π}(æ_<k) = Q_t^re(æ_<k π(æ_<k))`, for `π ∈ Π`, which print notes need
not have a name): the realistic value of an arbitrary policy. -/
@[expose] public noncomputable def realisticValue
    (π : Policy History WorldAction PolicyName) (h : History) : ℝ :=
  M.qValue h (π h)

/-- On a named policy the realistic value is the continuation value. -/
public theorem realisticValue_name (p : PolicyName) (h : History) :
    M.realisticValue (M.act p) h = M.contValue p h :=
  (M.bellman p h).symm

end RealisticModel

namespace NamedModel

variable {History WorldAction PolicyName Percept : Type*} [Fintype Percept]
variable (M : NamedModel History WorldAction PolicyName Percept)

/-- Forget the initial name, its optimality and the modification-independence
fields: a `NamedModel` is a `RealisticModel`. -/
@[expose] public def toRealistic :
    RealisticModel History WorldAction PolicyName Percept where
  act := M.act
  extend := M.extend
  utility := M.utility
  discount := M.discount
  discount_pos := M.discount_pos
  prob := M.prob
  prob_sum_one := M.prob_sum_one
  prob_pos := M.prob_pos
  contValue := M.contValue
  bellman := M.bellman

/-- The projection keeps every `Q₁^re` value. -/
public theorem toRealistic_qValue : M.toRealistic.qValue = M.namedQValue :=
  rfl

/-- **Print's equation (7) for every policy** on a `NamedModel`
(arXiv:1605.03142v1, Definition 12): `V^{re,π}(h) = Q^re(h π(h))`. -/
@[expose] public noncomputable def realisticValue
    (π : Policy History WorldAction PolicyName) (h : History) : ℝ :=
  M.namedQValue h (π h)

/-- On a named policy the realistic value is the continuation value. -/
public theorem realisticValue_name (p : PolicyName) (h : History) :
    M.realisticValue (M.act p) h = M.contValue p h :=
  (M.namedContValue_eq_qValue p h).symm

end NamedModel

/-!
## Modification-independence of `V₁^{re,π₁}`, derived

`NamedModel.initial_modIndep` asserts that `V₁^{re,π₁}` does not read the
recorded policy name. Print derives this in the proof of Theorem 16
(arXiv:1605.03142v1, PDF p. 12) from its hypotheses: `ρ` and `u₁`
modification-independent (Definition 7, Assumption 8: they depend only on the
check-history `ǎe_{1:t}`, the history with the names erased), `π₁` optimal,
`u ∈ [0, 1]` and `γ ∈ (0, 1)` (setting, p. 3).

`ModIndepModel` states those hypotheses. `check` is the check-projection; a
`check`-equal pair of histories stays `check`-equal after the same world action
and percept, whatever names are recorded; `prob` and `utility` agree on
`check`-equal histories. Print's `u ∈ [0,1]` and `γ < 1` enter as `discount < 1`
and a bound on `contValue initial`: print's `V₁^{re,π₁}` is an expected
discounted sum and lies in `[0, 1/(1-γ)]`, and the bound picks it out among the
solutions of the recursion (an arbitrary solution of (7)∘(8) can be unbounded).

The proof is a contraction. For `D` the supremum of `V(x) - V(x')` over
`check`-equal pairs, optimality of `π₁` at `x'` against the action `π₁` takes at
`x` (with its name replaced by `p₁`) gives `V(x) - V(x') ≤ γ D`, so `D ≤ γ D`
and `D = 0`.

**Still asserted.** `initial_optimal`, the existence of an optimal named policy
(print's Appendix A, Theorems 20 and 21), remains a field.
-/

/-- **Print's Theorem 16 hypotheses with names recorded** (arXiv:1605.03142v1,
Theorem 16, Definition 7, Assumption 8, setting p. 3): the Definition 12 model,
an optimal initial name, `ρ` and `u₁` modification-independent through the
check-projection `check`, `γ < 1`, and a bounded `V₁^{re,π₁}`. -/
public structure ModIndepModel (History WorldAction PolicyName Percept Check : Type*)
    [Fintype Percept] extends RealisticModel History WorldAction PolicyName Percept where
  /-- The initial policy's name `p₁`. -/
  initial : PolicyName
  /-- `π₁` optimises `V₁^re`, unfolded through equation (7) and `Π` being the
  full function space into `𝒜̌ × 𝒫`. -/
  initial_optimal : ∀ (h : History) (a : WorldAction × PolicyName),
    (∑ e : Percept, prob h a.1 e *
        (utility (extend h a e) + discount * contValue a.2 (extend h a e)))
      ≤ ∑ e : Percept, prob h (act initial h).1 e *
        (utility (extend h (act initial h) e) +
          discount * contValue (act initial h).2 (extend h (act initial h) e))
  /-- The check-projection `ǎe_{1:t}`: the history with the policy names erased. -/
  check : History → Check
  /-- Extending by the same world action and percept keeps `check`-equal histories
  `check`-equal, whatever names are recorded. -/
  check_extend : ∀ h h' w p p' e, check h = check h' →
    check (extend h (w, p) e) = check (extend h' (w, p') e)
  /-- **`ρ` is modification-independent** (Definition 7, Assumption 8). -/
  prob_check : ∀ h h', check h = check h' → prob h = prob h'
  /-- **`u₁` is modification-independent** (Definition 7, Theorem 16). -/
  utility_check : ∀ h h', check h = check h' → utility h = utility h'
  /-- `γ < 1` (setting, p. 3). -/
  discount_lt_one : discount < 1
  /-- `V₁^{re,π₁}` is bounded, as print's expected discounted sum of utilities in
  `[0, 1]` is. -/
  initial_bounded : ∃ B, ∀ h, |contValue initial h| ≤ B

namespace ModIndepModel

variable {History WorldAction PolicyName Percept Check : Type*} [Fintype Percept]
variable (M : ModIndepModel History WorldAction PolicyName Percept Check)

/-- No named policy's continuation value beats the initial policy's. -/
public theorem contValue_le_initial (p : PolicyName) (h : History) :
    M.contValue p h ≤ M.contValue M.initial h := by
  rw [M.bellman p h, M.bellman M.initial h]
  exact M.initial_optimal h (M.act p h)

/-- `u₁` does not read the last recorded name. -/
public theorem utility_modIndep (h : History) (w : WorldAction) (p p' : PolicyName)
    (e : Percept) : M.utility (M.extend h (w, p) e) = M.utility (M.extend h (w, p') e) :=
  M.utility_check _ _ (M.check_extend h h w p p' e rfl)

/-- One contraction step: on `check`-equal histories, the initial value differs
by at most `γ` times any bound on its differences over `check`-equal pairs. -/
private theorem initial_sub_le (D : ℝ)
    (hD : ∀ y y', M.check y = M.check y' → M.contValue M.initial y - M.contValue M.initial y' ≤ D)
    (x x' : History) (hx : M.check x = M.check x') :
    M.contValue M.initial x - M.contValue M.initial x' ≤ M.discount * D := by
  set V := M.contValue M.initial
  set w := (M.act M.initial x).1
  set q := (M.act M.initial x).2
  have hact : M.act M.initial x = (w, q) := rfl
  have h1 : V x ≤ ∑ e : Percept, M.prob x w e *
      (M.utility (M.extend x (w, q) e) + M.discount * V (M.extend x (w, q) e)) := by
    rw [show V x = _ from M.bellman M.initial x, hact]
    refine Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left ?_ (M.prob_pos x w e).le
    have := mul_le_mul_of_nonneg_left (M.contValue_le_initial q (M.extend x (w, q) e))
      M.discount_pos.le
    linarith
  have h2 : (∑ e : Percept, M.prob x' w e *
      (M.utility (M.extend x' (w, M.initial) e) +
        M.discount * V (M.extend x' (w, M.initial) e))) ≤ V x' := by
    rw [show V x' = _ from M.bellman M.initial x']
    exact M.initial_optimal x' (w, M.initial)
  have hp : M.prob x' = M.prob x := (M.prob_check x x' hx).symm
  have hsum : (∑ e : Percept, M.prob x w e *
        (M.utility (M.extend x (w, q) e) + M.discount * V (M.extend x (w, q) e))) -
      (∑ e : Percept, M.prob x' w e *
        (M.utility (M.extend x' (w, M.initial) e) +
          M.discount * V (M.extend x' (w, M.initial) e))) ≤ M.discount * D := by
    rw [hp, ← Finset.sum_sub_distrib]
    calc (∑ e : Percept, (M.prob x w e *
            (M.utility (M.extend x (w, q) e) + M.discount * V (M.extend x (w, q) e)) -
          M.prob x w e * (M.utility (M.extend x' (w, M.initial) e) +
            M.discount * V (M.extend x' (w, M.initial) e))))
        ≤ ∑ e : Percept, M.prob x w e * (M.discount * D) := by
          refine Finset.sum_le_sum fun e _ => ?_
          have hc := M.check_extend x x' w q M.initial e hx
          have hu := M.utility_check _ _ hc
          have hd := mul_le_mul_of_nonneg_left (hD _ _ hc) M.discount_pos.le
          rw [hu, ← mul_sub]
          exact mul_le_mul_of_nonneg_left (by linarith) (M.prob_pos x w e).le
      _ = M.discount * D := by rw [← Finset.sum_mul, M.prob_sum_one, one_mul]
  linarith

/-- **`V₁^{re,π₁}` is modification-independent** (arXiv:1605.03142v1, proof of
Theorem 16, PDF p. 12, there obtained through Appendix A): the initial
continuation value agrees on histories with the same check-projection. -/
public theorem initial_check (x x' : History) (hx : M.check x = M.check x') :
    M.contValue M.initial x = M.contValue M.initial x' := by
  obtain ⟨B, hB⟩ := M.initial_bounded
  set V := M.contValue M.initial
  set S : Set ℝ := {d | ∃ y y', M.check y = M.check y' ∧ d = V y - V y'}
  have hbdd : BddAbove S := by
    refine ⟨2 * B, ?_⟩
    rintro d ⟨y, y', -, rfl⟩
    have := abs_le.mp (hB y)
    have := abs_le.mp (hB y')
    linarith
  have hmem : ∀ y y', M.check y = M.check y' → V y - V y' ≤ sSup S :=
    fun y y' hy => le_csSup hbdd ⟨y, y', hy, rfl⟩
  have hD0 : 0 ≤ sSup S := by simpa using hmem x x rfl
  have hDle : sSup S ≤ M.discount * sSup S :=
    csSup_le ⟨_, x, x, rfl, rfl⟩ (by
      rintro d ⟨y, y', hy, rfl⟩
      exact M.initial_sub_le (sSup S) hmem y y' hy)
  have hD : sSup S ≤ 0 := by nlinarith [M.discount_lt_one]
  have h₁ := hmem x x' hx
  have h₂ := hmem x' x hx.symm
  linarith

/-- `V₁^{re,π₁}` does not read the last recorded name: the field
`NamedModel.initial_modIndep`, here a theorem. -/
public theorem initial_modIndep (h : History) (w : WorldAction) (p p' : PolicyName)
    (e : Percept) :
    M.contValue M.initial (M.extend h (w, p) e) = M.contValue M.initial (M.extend h (w, p') e) :=
  M.initial_check _ _ (M.check_extend h h w p p' e rfl)

/-- Every model of print's Theorem 16 hypotheses is a `NamedModel`, with both
modification-independence fields proved. -/
@[expose] public def toNamedModel : NamedModel History WorldAction PolicyName Percept where
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
  utility_modIndep := M.utility_modIndep
  initial_modIndep := M.initial_modIndep
  bellman := M.bellman
  initial_optimal := M.initial_optimal

/-- **The induction step of Theorem 16** (arXiv:1605.03142v1, eq. (14) and the
proof of Theorem 16) at print's hypotheses, with names recorded and
modification-independence of `V₁^{re,π₁}` derived: if the current policy acts
`Q₁^re`-optimally, the policy it selects acts `Q₁^re`-optimally at every
successor history. -/
public theorem optimalAt_next {p : PolicyName} {h : History}
    (hopt : M.OptimalAt p h) (e : Percept) :
    M.OptimalAt (M.act p h).2 (M.extend h (M.act p h) e) :=
  M.toNamedModel.namedOptimalAt_next hopt e

end ModIndepModel

end AISafetyAtlas.Wireheading.GoalPreservationRun
