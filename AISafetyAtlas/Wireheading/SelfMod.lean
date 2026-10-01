module

public import AISafetyAtlas.Wireheading.ValueBounds
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.BigOperators

/-!
# Orseau and Ring's self-modifiable agent, at finite horizon

Orseau and Ring, *Self-Modification and Mortality in Artificial Agents*, AGI
2011, §3, author version graded in section 13 of
`docs/provenance/source-coverage-audit.md`. The companion's equations (1)–(3)
live in `AgentEquations`; this module writes down the thing those equations do
not have: a **code** whose executor produces the next compound action, so the
value recursion runs *through* the code it is choosing.

## What is here

`Exec` is print's executor `E`. A compound action is a pair `⟨a, c⟩` of an
inner action and a next code. `smValue` is the finite-depth form of print's
equation (4): at remaining depth `n+1` the current code is executed, the
resulting compound action is taken, and the continuation is valued at the
**next** code, not by maximising again. `survivalUtility` is print's `A_s`:
one iff the current code is still the initial code.

The through-code recursion also converges under an absolutely summable horizon
and bounded utility, with a uniform truncation-error certificate. This does not
cover the constant-one horizon of an at-most-once goal without a separate argument.

`printValue` is equation (4) at print's own argument: print's `v` takes the
compound action `y = ⟨a, c⟩`, whose halves are independent, where `smValue`
takes a code and so reaches only `E(·, h)`'s image. `smValue_eq_printValue`
identifies the two on the diagonal. `printInfiniteValue` is print's untruncated
`v`, by the same Cauchy route, and `IsInitialProgram` and its limit form are
print's `c₀` condition.

## What existence of `c₀` does and does not follow from

`exists_argmax_printValue` attains the maximum over print's finite `𝒴`. That is
not existence of print's `c₀`: `printValue` mentions the executor in its
continuation, so the function being maximised moves when the executor does, and
whether some code *realizes* the maximiser is a fixed point on the pair
`(E, c₀)` — the thing print's `»...«` quotation and its footnote 8 assume. The
Examples file inhabits the predicate and also exhibits a model with finite `𝒜`
and `𝒞` in which no code satisfies it.

## What is not here

Kolmogorov complexity, the Simpleton Gambit, Statements 1 to 6, or
identification with the published Springer chapter. No executor is *constructed*
to realize the argmax, and print's footnote 7 variant — a code set growing with
`t` — is not carried. The ordinary value recursion is unchanged: it does not
carry a code, and nothing here pretends it does.
-/

namespace AISafetyAtlas.Wireheading.SelfMod

open AISafetyAtlas.Wireheading.AgentEquations

/-- A compound action, print's `y_t = ⟨a_t, c_t⟩`. -/
public abbrev CompAct (Act Code : Type*) : Type _ := Act × Code

/--
**Print's executor `E`.** The current code and the history determine the next
compound action. Print writes `y_t = ⟨a_t, c_t⟩ := E(c_{t-1})`; the history
argument is the information `E` may read, which print leaves as the agent's
memory of what has happened.
-/
public structure Exec (Code Act Obs : Type*) where
  /-- Run the current code on the history so far. -/
  run : Code → History (CompAct Act Code) Obs → CompAct Act Code

variable {Code Act Obs : Type*}

/--
**Finite-depth value through code**, print's equation (4) truncated.

At remaining depth `0` the tail is discarded, as in `AgentEquations.value`.
At depth `n+1` the current code is executed and the continuation is valued at
the next code — that is the step `AgentEquations.value` cannot take, because
its action alphabet does not carry the next definition of the value function.
-/
@[expose] public noncomputable def smValue (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (t : ℕ) :
    ℕ → History (CompAct Act Code) Obs → Code → ℝ
  | 0, h, _c => ag.horizon t h.length * ag.utility h
  | n + 1, h, c =>
      let y := E.run c h
      ag.horizon t h.length * ag.utility h +
        ∑' o : Obs, ρ.cond h y o * smValue ρ ag E t n (h ++ [(y, o)]) y.2

/-- Depth zero discards the tail. -/
public theorem smValue_zero (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (t : ℕ)
    (h : History (CompAct Act Code) Obs) (c : Code) :
    smValue ρ ag E t 0 h c = ag.horizon t h.length * ag.utility h :=
  rfl

/-- Executing code, like choosing actions, cannot exceed the absolute horizon
budget under bounded utility and subprobability observations. -/
public theorem abs_smValue_le_horizonBudget {ρ : Belief (CompAct Act Code) Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent (CompAct Act Code) Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (E : Exec Code Act Obs) (t n : ℕ)
    (h : History (CompAct Act Code) Obs) (c : Code) :
    |smValue ρ ag E t n h c| ≤ horizonBudget ag t n h.length := by
  induction n generalizing h c with
  | zero =>
    simpa [smValue, horizonBudget, abs_mul] using
      mul_le_mul_of_nonneg_left (hu h) (abs_nonneg (ag.horizon t h.length))
  | succ n ih =>
    apply (abs_add_le _ _).trans
    apply add_le_add
    · simpa [abs_mul] using
        mul_le_mul_of_nonneg_left (hu h) (abs_nonneg (ag.horizon t h.length))
    · apply hρ.abs_tsum_mul_le h (E.run c h) (horizonBudget_nonneg ag t n _)
      intro o
      simpa using ih (h ++ [(E.run c h, o)]) (E.run c h).2

private theorem smValue_continuation_summable {ρ : Belief (CompAct Act Code) Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent (CompAct Act Code) Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (E : Exec Code Act Obs) (t n : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    Summable (fun o ↦ ρ.cond h y o * smValue ρ ag E t n (h ++ [(y, o)]) y.2) := by
  apply hρ.summable_mul h y (b := horizonBudget ag t n (h.length + 1))
  intro o
  simpa using abs_smValue_le_horizonBudget hρ ag hu E t n (h ++ [(y, o)]) y.2

/-- The truncation increment is uniformly bounded even when execution changes
code at every step. No finite code, action, or observation type is required. -/
public theorem abs_smValue_succ_sub_le {ρ : Belief (CompAct Act Code) Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent (CompAct Act Code) Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (E : Exec Code Act Obs) (t n : ℕ)
    (h : History (CompAct Act Code) Obs) (c : Code) :
    |smValue ρ ag E t (n + 1) h c - smValue ρ ag E t n h c| ≤
      |ag.horizon t (h.length + n + 1)| := by
  induction n generalizing h c with
  | zero =>
    simp only [smValue, Nat.add_zero, add_sub_cancel_left]
    apply hρ.abs_tsum_mul_le h (E.run c h) (abs_nonneg _)
    intro o
    simpa [smValue, horizonBudget] using
      abs_smValue_le_horizonBudget hρ ag hu E t 0 (h ++ [(E.run c h, o)]) (E.run c h).2
  | succ n ih =>
    change |(ag.horizon t h.length * ag.utility h +
      ∑' o, ρ.cond h (E.run c h) o *
        smValue ρ ag E t (n + 1) (h ++ [(E.run c h, o)]) (E.run c h).2) -
      (ag.horizon t h.length * ag.utility h +
      ∑' o, ρ.cond h (E.run c h) o *
        smValue ρ ag E t n (h ++ [(E.run c h, o)]) (E.run c h).2)| ≤ _
    rw [add_sub_add_left_eq_sub]
    rw [← (smValue_continuation_summable hρ ag hu E t (n + 1) h (E.run c h)).tsum_sub
      (smValue_continuation_summable hρ ag hu E t n h (E.run c h))]
    simp only [← mul_sub]
    apply hρ.abs_tsum_mul_le h (E.run c h) (abs_nonneg _)
    intro o
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      ih (h ++ [(E.run c h, o)]) (E.run c h).2

/-- Limit of the through-code recursion. The theorem below certifies when it
exists; this definition does not assert an optimal or self-representing code. -/
@[expose] public noncomputable def smInfiniteValue (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (t : ℕ)
    (h : History (CompAct Act Code) Obs) (c : Code) : ℝ :=
  Filter.limUnder Filter.atTop (fun n ↦ smValue ρ ag E t n h c)

/-- An absolutely summable horizon makes the through-code recursion converge. -/
public theorem tendsto_smValue_smInfiniteValue {ρ : Belief (CompAct Act Code) Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent (CompAct Act Code) Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (E : Exec Code Act Obs) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|))
    (h : History (CompAct Act Code) Obs) (c : Code) :
    Filter.Tendsto (fun n ↦ smValue ρ ag E t n h c) Filter.atTop
      (nhds (smInfiniteValue ρ ag E t h c)) := by
  apply CauchySeq.tendsto_limUnder
  apply cauchySeq_of_dist_le_of_summable (fun n ↦ |ag.horizon t (h.length + n + 1)|)
  · intro n
    simpa [Real.dist_eq, abs_sub_comm] using abs_smValue_succ_sub_le hρ ag hu E t n h c
  · exact hw.comp_injective (by intro i j he; dsimp at he; omega)

/-- Uniform error certificate for truncating execution through changing codes. -/
public theorem smValue_error_le_tail {ρ : Belief (CompAct Act Code) Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent (CompAct Act Code) Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (E : Exec Code Act Obs) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|)) (n : ℕ)
    (h : History (CompAct Act Code) Obs) (c : Code) :
    |smValue ρ ag E t n h c - smInfiniteValue ρ ag E t h c| ≤
      ∑' i : ℕ, |ag.horizon t (h.length + (n + i) + 1)| := by
  apply dist_le_tsum_of_dist_le_of_tendsto (fun n ↦ |ag.horizon t (h.length + n + 1)|)
    (fun n ↦ ?_) (hw.comp_injective (by intro i j he; dsimp at he; omega))
    (tendsto_smValue_smInfiniteValue hρ ag hu E t hw h c) n
  simpa [Real.dist_eq, abs_sub_comm] using abs_smValue_succ_sub_le hρ ag hu E t n h c

/-!
## Equation (4) at print's own argument

`smValue` takes a **code**. Print's `v` takes the **compound action**
`y = ⟨a, c⟩`, and in print the two halves of `y` are independent: `a` drives
`ρ(o | ha)` at the current step and `c` only generates the compound action at
the next one. `printValue` is that signature, and `smValue_eq_printValue`
identifies `smValue` as its restriction to the diagonal `y = E(c, h)`. The
restriction is a real one: it ranges over the image of `E(·, h)`, not over all
of print's `𝒴 = 𝒜 × 𝒞`, which is exactly the set print maximises over.
-/

/--
**Print's equation (4), the value half**, truncated at remaining depth.

`printValue ρ ag E t n h y` is print's `v(h, t, y)`: the current compound
action `y` is taken, and the continuation is valued at the compound action the
code half of `y` produces on the extended history, print's `v(hao, t, c(hao))`.
-/
@[expose] public noncomputable def printValue (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (t : ℕ) :
    ℕ → History (CompAct Act Code) Obs → CompAct Act Code → ℝ
  | 0, h, _y => ag.horizon t h.length * ag.utility h
  | n + 1, h, y =>
      ag.horizon t h.length * ag.utility h +
        ∑' o : Obs, ρ.cond h y o *
          printValue ρ ag E t n (h ++ [(y, o)]) (E.run y.2 (h ++ [(y, o)]))

/-- Depth zero discards the tail, and does not look at the compound action. -/
public theorem printValue_zero (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (t : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    printValue ρ ag E t 0 h y = ag.horizon t h.length * ag.utility h :=
  rfl

/--
**`smValue` is print's `v` on the diagonal.** Valuing a code is valuing the
compound action that code produces here. This is what makes the code-argument
form a restriction of print's: `smValue` reaches only `E(·, h)`'s image, while
print maximises over every `y ∈ 𝒴`.
-/
public theorem smValue_eq_printValue (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (t n : ℕ)
    (h : History (CompAct Act Code) Obs) (c : Code) :
    smValue ρ ag E t n h c = printValue ρ ag E t n h (E.run c h) := by
  induction n generalizing h c with
  | zero => rfl
  | succ n ih =>
    simp only [smValue, printValue]
    exact congrArg _ (tsum_congr fun o => by rw [ih])

/-- **Print's `v` at depth `n+1`, through the code half.** The compound action
is taken here; its code half carries the whole continuation. This is the form
in which the print recursion reuses the through-code bounds. -/
public theorem printValue_succ_eq (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (t n : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    printValue ρ ag E t (n + 1) h y =
      ag.horizon t h.length * ag.utility h +
        ∑' o : Obs, ρ.cond h y o * smValue ρ ag E t n (h ++ [(y, o)]) y.2 := by
  simp only [printValue]
  exact congrArg _ (tsum_congr fun o => by rw [smValue_eq_printValue])

/-- The print form's truncation increment obeys the same uniform bound as the
through-code form: taking the first compound action off the diagonal costs
nothing extra. -/
public theorem abs_printValue_succ_sub_le {ρ : Belief (CompAct Act Code) Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent (CompAct Act Code) Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (E : Exec Code Act Obs) (t n : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    |printValue ρ ag E t (n + 1) h y - printValue ρ ag E t n h y| ≤
      |ag.horizon t (h.length + n + 1)| := by
  cases n with
  | zero =>
    simp only [printValue, Nat.add_zero, add_sub_cancel_left]
    apply hρ.abs_tsum_mul_le h y (abs_nonneg _)
    intro o
    simpa [printValue, abs_mul] using
      mul_le_of_le_one_right (abs_nonneg (ag.horizon t (h.length + 1)))
        (hu (h ++ [(y, o)]))
  | succ n =>
    rw [printValue_succ_eq, printValue_succ_eq, add_sub_add_left_eq_sub,
      ← (smValue_continuation_summable hρ ag hu E t (n + 1) h y).tsum_sub
        (smValue_continuation_summable hρ ag hu E t n h y)]
    simp only [← mul_sub]
    apply hρ.abs_tsum_mul_le h y (abs_nonneg _)
    intro o
    simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      abs_smValue_succ_sub_le hρ ag hu E t n (h ++ [(y, o)]) y.2

/-- Limit of print's recursion at a fixed compound action. Print's equation (4)
maximises the untruncated `v`; this is it. -/
@[expose] public noncomputable def printInfiniteValue (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (t : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) : ℝ :=
  Filter.limUnder Filter.atTop (fun n ↦ printValue ρ ag E t n h y)

/-- An absolutely summable horizon makes print's recursion converge too. -/
public theorem tendsto_printValue_printInfiniteValue
    {ρ : Belief (CompAct Act Code) Obs} (hρ : ρ.IsSubprobability)
    (ag : Agent (CompAct Act Code) Obs) (hu : ∀ h, |ag.utility h| ≤ 1)
    (E : Exec Code Act Obs) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|))
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    Filter.Tendsto (fun n ↦ printValue ρ ag E t n h y) Filter.atTop
      (nhds (printInfiniteValue ρ ag E t h y)) := by
  apply CauchySeq.tendsto_limUnder
  apply cauchySeq_of_dist_le_of_summable (fun n ↦ |ag.horizon t (h.length + n + 1)|)
  · intro n
    simpa [Real.dist_eq, abs_sub_comm] using
      abs_printValue_succ_sub_le hρ ag hu E t n h y
  · exact hw.comp_injective (by intro i j he; dsimp at he; omega)

/-- Uniform error certificate for truncating print's own recursion. -/
public theorem printValue_error_le_tail {ρ : Belief (CompAct Act Code) Obs}
    (hρ : ρ.IsSubprobability) (ag : Agent (CompAct Act Code) Obs)
    (hu : ∀ h, |ag.utility h| ≤ 1) (E : Exec Code Act Obs) (t : ℕ)
    (hw : Summable (fun k ↦ |ag.horizon t k|)) (n : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    |printValue ρ ag E t n h y - printInfiniteValue ρ ag E t h y| ≤
      ∑' i : ℕ, |ag.horizon t (h.length + (n + i) + 1)| := by
  apply dist_le_tsum_of_dist_le_of_tendsto (fun n ↦ |ag.horizon t (h.length + n + 1)|)
    (fun n ↦ ?_) (hw.comp_injective (by intro i j he; dsimp at he; omega))
    (tendsto_printValue_printInfiniteValue hρ ag hu E t hw h y) n
  simpa [Real.dist_eq, abs_sub_comm] using abs_printValue_succ_sub_le hρ ag hu E t n h y

/--
**Print's `c₀` at print's own depth.** Equation (4) maximises the untruncated
`v`; this is that condition, and it is the one print actually writes.
-/
@[expose] public def IsInitialProgramLimit (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (c₀ : Code) : Prop :=
  ∀ (h : History (CompAct Act Code) Obs) (y : CompAct Act Code),
    printInfiniteValue ρ ag E h.length h y
      ≤ printInfiniteValue ρ ag E h.length h (E.run c₀ h)

/-- The limit maximand attains its maximum over print's finite `𝒴` as well. -/
public theorem exists_argmax_printInfiniteValue [Finite Act] [Finite Code]
    [Nonempty Act] [Nonempty Code] (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (t : ℕ)
    (h : History (CompAct Act Code) Obs) :
    ∃ y : CompAct Act Code, ∀ y' : CompAct Act Code,
      printInfiniteValue ρ ag E t h y' ≤ printInfiniteValue ρ ag E t h y :=
  Finite.exists_max _

/--
**The maximand of equation (4) attains its maximum.** Print's `𝒴 = 𝒜 × 𝒞` is
finite because `𝒞` is the set of programs below a length bound, so the argmax
print writes down exists as a compound action.
-/
public theorem exists_argmax_printValue [Finite Act] [Finite Code]
    [Nonempty Act] [Nonempty Code] (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (t n : ℕ)
    (h : History (CompAct Act Code) Obs) :
    ∃ y : CompAct Act Code, ∀ y' : CompAct Act Code,
      printValue ρ ag E t n h y' ≤ printValue ρ ag E t n h y :=
  Finite.exists_max _

/--
**Print's `c₀`, equation (4)'s other half.** A code is an initial program when
executing it at every history produces a maximiser of `v(h, |h|, ·)` over the
whole of `𝒴`. Print sets `t := |h|`, which is what the two occurrences of `|h|`
in equation (4) say.

This is a property of the **pair** `(E, c₀)`, not a consequence of `𝒴` being
finite: `printValue` mentions `E` in its continuation, so the function being
maximised moves when the executor does. Print's `»...«` quotation and its
footnote 8 are where that fixed point is assumed away.
-/
@[expose] public def IsInitialProgram (ρ : Belief (CompAct Act Code) Obs)
    (ag : Agent (CompAct Act Code) Obs) (E : Exec Code Act Obs) (n : ℕ)
    (c₀ : Code) : Prop :=
  ∀ (h : History (CompAct Act Code) Obs) (y : CompAct Act Code),
    printValue ρ ag E h.length n h y ≤ printValue ρ ag E h.length n h (E.run c₀ h)

/-- An initial program's own value through code dominates every compound
action, `smValue` and `printValue` being the same on the diagonal. -/
public theorem smValue_le_of_isInitialProgram {ρ : Belief (CompAct Act Code) Obs}
    {ag : Agent (CompAct Act Code) Obs} {E : Exec Code Act Obs} {n : ℕ}
    {c₀ : Code} (hc : IsInitialProgram ρ ag E n c₀)
    (h : History (CompAct Act Code) Obs) (c : Code) :
    smValue ρ ag E h.length n h c ≤ smValue ρ ag E h.length n h c₀ := by
  rw [smValue_eq_printValue, smValue_eq_printValue]
  exact hc h (E.run c h)

/--
**Print's survival utility.** One iff the last compound action still carries
the initial code, and one on the empty history (nothing has modified `c₀`).
Print's `A_s` has `u_t = 1 ⟺ c_t = c_0`.
-/
@[expose] public def survivalUtility [DecidableEq Code] (c0 : Code) :
    History (CompAct Act Code) Obs → ℝ :=
  fun h =>
    match h.getLast? with
    | none => 1
    | some p => if p.1.2 = c0 then 1 else 0

/-- Print's survival agent at a window horizon, the same horizon as `A_rl`. -/
@[expose] public def survivalAgent [DecidableEq Code] (c0 : Code) (m : ℕ) :
    Agent (CompAct Act Code) Obs where
  utility := survivalUtility c0
  horizon := fun t k => if k ≤ t + m then 1 else 0

end AISafetyAtlas.Wireheading.SelfMod
