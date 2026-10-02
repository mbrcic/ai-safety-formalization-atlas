module

public import AISafetyAtlas.Wireheading.SelfMod
public import Mathlib.Tactic.NormNum

/-!
# A code that never modifies itself

`AISafetyAtlas.Wireheading.SelfMod` states Orseau and Ring's executor and the
finite-depth value that runs through it. This file inhabits them with two
codes, one of which is a simpleton, and an executor that ignores the history
and returns a fixed inner action together with whatever code it was given —
so a code that is still `c₀` stays `c₀`, and a simpleton stays a simpleton.

That is enough to see that `smValue` actually depends on the code: at remaining
depth one, the survival agent is worth one if it still holds `c₀` and zero if
it has become the simpleton, against a belief that puts mass one on a single
observation.

It also carries both sides of equation (4)'s existence question. `stay` at
`c₀ = false` is an initial program, at a truncation and at the limit;
`alwaysSimpleton` is an executor over the same finite `𝒜` and `𝒞` for which no
code is one, so attainment of the argmax does not give print's `c₀`. `Prog` is
print's own code set — the programs below a length bound — which is where the
finiteness that attainment rests on actually comes from.
-/

namespace AISafetyAtlas.Examples.Wireheading.SelfMod

open AISafetyAtlas.Wireheading.AgentEquations
open AISafetyAtlas.Wireheading.SelfMod

/-- Two codes: `false` is the initial program, `true` is the simpleton. -/
public abbrev Code := Bool
/-- One inner action; the compound action varies only in the code. -/
public abbrev Act := Unit
/-- One observation, so the belief's sum is a single term. -/
public abbrev Obs := Unit

/-- An executor that never changes the code it is given. -/
@[expose] public def stay : Exec Code Act Obs where
  run := fun c _ => ((), c)

/-- A point-mass belief on the only observation. -/
@[expose] public def sure : Belief (CompAct Act Code) Obs where
  cond := fun _ _ _ => 1

/-- The survival agent whose initial code is `false`, at a one-step window. -/
@[expose] public def survivor : Agent (CompAct Act Code) Obs :=
  survivalAgent (false : Code) 1

/-- At remaining depth zero the survival agent is worth one, whatever the code:
nothing has happened yet. -/
public theorem smValue_zero_empty (c : Code) :
    smValue sure survivor stay 0 0 [] c = 1 := by
  simp [smValue_zero, survivor, survivalAgent, survivalUtility]

/-- At remaining depth one, still holding `c₀` is worth two: the empty-history
utility plus the one-step continuation, which still carries `c₀`. -/
public theorem smValue_one_stays :
    smValue sure survivor stay 0 1 [] false = 2 := by
  simp [smValue, survivor, survivalAgent, survivalUtility, stay, sure]
  norm_num

/-- And becoming the simpleton is worth one: the empty history still scores,
the continuation does not. -/
public theorem smValue_one_simpleton :
    smValue sure survivor stay 0 1 [] true = 1 := by
  simp [smValue, survivor, survivalAgent, survivalUtility, stay, sure]

/-- So the finite-depth value through code depends on the code. -/
public theorem smValue_depends_on_code :
    smValue sure survivor stay 0 1 [] false ≠
      smValue sure survivor stay 0 1 [] true := by
  rw [smValue_one_stays, smValue_one_simpleton]
  norm_num

/-- The point-mass belief is a subprobability. -/
public theorem sure_isSubprobability : sure.IsSubprobability :=
  ⟨by intros; norm_num [sure], by intros; exact Summable.of_finite,
    by intros; simp [sure]⟩

/-- Survival utility is bounded by one. -/
public theorem survivor_abs_utility_le_one (h : History (CompAct Act Code) Obs) :
    |survivor.utility h| ≤ 1 := by
  simp only [survivor, survivalAgent, survivalUtility]
  split
  · norm_num
  · split_ifs <;> norm_num

/-- The one-step window horizon has finite support, so it is summable. -/
public theorem survivor_horizon_summable (t : ℕ) :
    Summable (fun k ↦ |survivor.horizon t k|) := by
  apply summable_of_ne_finset_zero (s := Finset.range (t + 2))
  intro k hk
  have hk' : t + 2 ≤ k := by simpa only [Finset.mem_range, not_lt] using hk
  simp [survivor, survivalAgent, show ¬ k ≤ t + 1 by omega]

/-- The infinite recursion recovers the already checked finite-window value. -/
public theorem smInfiniteValue_stays : smInfiniteValue sure survivor stay 0 [] false = 2 := by
  have hρ := sure_isSubprobability
  have hu := survivor_abs_utility_le_one
  have hw := survivor_horizon_summable 0
  have hz (i : ℕ) : |survivor.horizon 0 (0 + (1 + i) + 1)| = 0 := by
    simp [survivor, survivalAgent]
  have he := smValue_error_le_tail hρ survivor hu stay 0 hw 1 [] false
  simp only [List.length_nil, hz, tsum_zero, abs_nonpos_iff, sub_eq_zero] at he
  exact he.symm.trans smValue_one_stays

/-!
## Equation (4): the argmax, and what finiteness does not buy

`printValue` is print's `v` at print's own argument, and `exists_argmax_printValue`
says the maximum over `𝒴` is attained. Attainment is not existence of print's
`c₀`: the function being maximised mentions the executor, so whether some code
*realises* the maximiser depends on the executor. The two theorems below are
the two sides of that, in the smallest model where both are visible.
-/

/-- The depth-one print value here: the current history's utility, plus one
exactly when the compound action keeps the initial code. -/
public theorem printValue_one (E : Exec Code Act Obs)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    printValue sure survivor E h.length 1 h y
      = survivor.utility h + (if y.2 = false then 1 else 0) := by
  simp [printValue, survivor, survivalAgent, survivalUtility, sure]

/-- **`stay` at `c₀ = false` is print's initial program.** It executes to a
maximiser of `v(h, |h|, ·)` at every history, so equation (4)'s argmax is
realised by a code and not merely attained by a compound action. -/
public theorem stay_isInitialProgram :
    IsInitialProgram sure survivor stay 1 (false : Code) := by
  intro h y
  rw [printValue_one, printValue_one]
  simp only [stay]
  split_ifs <;> norm_num

/-- An executor that turns every code into the simpleton. -/
@[expose] public def alwaysSimpleton : Exec Code Act Obs where
  run := fun _ _ => ((), true)

/-- **Finiteness of `𝒴` does not give print's `c₀`.** Here `𝒜` and `𝒞` are
both finite, so `exists_argmax_printValue` applies and the maximum is attained
at `⟨(), false⟩` — yet no code is an initial program, because this executor's
image misses the maximiser at every history. Print's equation (4) assumes the
fixed point that the quotation marks hide. -/
public theorem not_exists_isInitialProgram_alwaysSimpleton :
    ¬ ∃ c₀ : Code, IsInitialProgram sure survivor alwaysSimpleton 1 c₀ := by
  rintro ⟨c₀, hc⟩
  have h := hc [] ((), false)
  rw [printValue_one, printValue_one] at h
  simp [alwaysSimpleton] at h
  norm_num at h

/-- The attained maximiser exists in this model, which is what
`exists_argmax_printValue` asserts. -/
public theorem exists_argmax_printValue_stay (n : ℕ)
    (h : History (CompAct Act Code) Obs) :
    ∃ y : CompAct Act Code, ∀ y' : CompAct Act Code,
      printValue sure survivor stay h.length n h y'
        ≤ printValue sure survivor stay h.length n h y :=
  exists_argmax_printValue sure survivor stay h.length n h

/-- Valuing a code is valuing what it executes to. -/
public theorem smValue_eq_printValue_stay (n : ℕ)
    (h : History (CompAct Act Code) Obs) (c : Code) :
    smValue sure survivor stay h.length n h c
      = printValue sure survivor stay h.length n h (stay.run c h) :=
  smValue_eq_printValue sure survivor stay h.length n h c

/-- Every code is dominated by the initial program. -/
public theorem smValue_le_stay (h : History (CompAct Act Code) Obs) (c : Code) :
    smValue sure survivor stay h.length 1 h c
      ≤ smValue sure survivor stay h.length 1 h false :=
  smValue_le_of_isInitialProgram stay_isInitialProgram h c

/-!
## Equation (4) at print's own depth

Print maximises the untruncated `v`. The survival agent's horizon closes after
one step, so print's recursion here is settled at depth one and its limit is
that value — which is what lets the limit-form initial program be exhibited
rather than only defined.
-/

/-- Depth zero ignores the compound action. -/
public theorem printValue_zero_empty (y : CompAct Act Code) :
    printValue sure survivor stay 0 0 [] y = 1 := by
  simp [printValue_zero, survivor, survivalAgent, survivalUtility]

/-- Print's recursion, one unfolding, against the through-code value. -/
public theorem printValue_succ_eq_stay (n : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    printValue sure survivor stay h.length (n + 1) h y =
      survivor.horizon h.length h.length * survivor.utility h +
        ∑' o : Obs, sure.cond h y o *
          smValue sure survivor stay h.length n (h ++ [(y, o)]) y.2 :=
  printValue_succ_eq sure survivor stay h.length n h y

/-- The truncation increment is bounded here too. -/
public theorem abs_printValue_succ_sub_le_stay (t n : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    |printValue sure survivor stay t (n + 1) h y
        - printValue sure survivor stay t n h y|
      ≤ |survivor.horizon t (h.length + n + 1)| :=
  abs_printValue_succ_sub_le sure_isSubprobability survivor
    survivor_abs_utility_le_one stay t n h y

/-- Print's recursion converges in this model. -/
public theorem tendsto_printValue_stay (t : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    Filter.Tendsto (fun n ↦ printValue sure survivor stay t n h y) Filter.atTop
      (nhds (printInfiniteValue sure survivor stay t h y)) :=
  tendsto_printValue_printInfiniteValue sure_isSubprobability survivor
    survivor_abs_utility_le_one stay t (survivor_horizon_summable t) h y

/-- And the truncation error is certified. -/
public theorem printValue_error_le_tail_stay (t n : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    |printValue sure survivor stay t n h y - printInfiniteValue sure survivor stay t h y|
      ≤ ∑' i : ℕ, |survivor.horizon t (h.length + (n + i) + 1)| :=
  printValue_error_le_tail sure_isSubprobability survivor
    survivor_abs_utility_le_one stay t (survivor_horizon_summable t) n h y

/-- One unfolding of print's recursion in this model: a single observation and
a code-preserving executor leave one continuation term. -/
public theorem printValue_succ_stay (t n : ℕ)
    (h : History (CompAct Act Code) Obs) (y : CompAct Act Code) :
    printValue sure survivor stay t (n + 1) h y
      = survivor.horizon t h.length * survivor.utility h
        + printValue sure survivor stay t n (h ++ [(y, ())]) ((), y.2) := by
  rw [printValue]
  simp [sure, stay]

/-- **Inside the window, print's recursion is settled at depth one.** Once the
history is at least as long as the horizon's origin, everything past the next
step falls outside the one-step window, so deeper truncations agree. -/
public theorem printValue_stay_window (t : ℕ) :
    ∀ (n : ℕ) (h : History (CompAct Act Code) Obs) (y : CompAct Act Code),
      t ≤ h.length →
      printValue sure survivor stay t (n + 1) h y
        = survivor.horizon t h.length * survivor.utility h
          + survivor.horizon t (h.length + 1) * survivor.utility (h ++ [(y, ())]) := by
  intro n
  induction n with
  | zero =>
    intro h y _
    rw [printValue_succ_stay, printValue_zero]
    simp
  | succ n ih =>
    intro h y ht
    have hlen : t ≤ (h ++ [(y, ())]).length := by simp; omega
    have hzero : survivor.horizon t ((h ++ [(y, ())]).length + 1) = 0 := by
      simp only [survivor, survivalAgent, List.length_append, List.length_cons,
        List.length_nil]
      rw [if_neg]; omega
    rw [printValue_succ_stay, ih (h ++ [(y, ())]) ((), y.2) hlen, hzero]
    simp

/-- The limit of print's recursion in the window is that settled value. -/
public theorem printInfiniteValue_stay (h : History (CompAct Act Code) Obs)
    (y : CompAct Act Code) :
    printInfiniteValue sure survivor stay h.length h y
      = survivor.utility h + (if y.2 = false then 1 else 0) := by
  have hconst : ∀ n : ℕ, printValue sure survivor stay h.length (n + 1) h y
      = survivor.utility h + (if y.2 = false then 1 else 0) := by
    intro n
    rw [printValue_stay_window h.length n h y le_rfl]
    simp only [survivor, survivalAgent, survivalUtility, List.getLast?_concat]
    rw [if_pos (le_refl _), if_pos (by omega)]
    split_ifs <;> norm_num
  have ht := tendsto_printValue_stay h.length h y
  have : Filter.Tendsto (fun n ↦ printValue sure survivor stay h.length n h y)
      Filter.atTop (nhds (survivor.utility h + (if y.2 = false then 1 else 0))) := by
    rw [← Filter.tendsto_add_atTop_iff_nat 1]
    simp [hconst]
  exact (tendsto_nhds_unique ht this)

/-- **`stay` at `c₀ = false` is print's initial program at print's own depth**,
not only at a truncation. -/
public theorem stay_isInitialProgramLimit :
    IsInitialProgramLimit sure survivor stay (false : Code) := by
  intro h y
  rw [printInfiniteValue_stay, printInfiniteValue_stay]
  simp only [stay]
  split_ifs <;> norm_num

/-- **The two renderings agree at the limit, on the diagonal.** The print form
evaluated at what `c₀` executes to is the through-code limit already checked to
be two — the limit statement of `smValue_eq_printValue`. -/
public theorem printInfiniteValue_eq_smInfiniteValue_stays :
    printInfiniteValue sure survivor stay 0 [] (stay.run false [])
      = smInfiniteValue sure survivor stay 0 [] false := by
  rw [smInfiniteValue_stays]
  have h := printInfiniteValue_stay [] (stay.run false [])
  simp only [List.length_nil] at h
  rw [h]
  simp [stay, survivor, survivalAgent, survivalUtility]
  norm_num

/-- The limit maximand attains its maximum here. -/
public theorem exists_argmax_printInfiniteValue_stay (t : ℕ)
    (h : History (CompAct Act Code) Obs) :
    ∃ y : CompAct Act Code, ∀ y' : CompAct Act Code,
      printInfiniteValue sure survivor stay t h y'
        ≤ printInfiniteValue sure survivor stay t h y :=
  exists_argmax_printInfiniteValue sure survivor stay t h

/-!
## Print's `𝒞` as an object

Print's code set is "all programs whose length (in the language of `E`) is less
than a small, arbitrary value". The library keeps `Code` an arbitrary type,
which is wider. This is print's set itself, at a two-symbol language and the
bound three, so the finiteness `exists_argmax_printValue` needs is print's own
reason for it.
-/

/-- **Print's `𝒞`**: the programs over a two-symbol language shorter than `b`. -/
public abbrev Prog (b : ℕ) : Type := Σ n : Fin b, List.Vector Bool n

/-- Print's defining property of `𝒞`: every program is below the bound. -/
public theorem prog_length_lt {b : ℕ} (c : Prog b) : c.2.toList.length < b := by
  simp

/-- The empty program, print's shortest code. -/
@[expose] public def emptyProg {b : ℕ} (hb : 0 < b) : Prog b :=
  ⟨⟨0, hb⟩, List.Vector.nil⟩

/-- A point-mass belief over compound actions carrying a bounded program. -/
@[expose] public def sureProg (b : ℕ) : Belief (CompAct Act (Prog b)) Obs where
  cond := fun _ _ _ => 1

/-- An executor over print's `𝒞` that keeps the code it is given. -/
@[expose] public def stayProg (b : ℕ) : Exec (Prog b) Act Obs where
  run := fun c _ => ((), c)

/-- **Equation (4)'s maximum is attained over print's own `𝒴 = 𝒜 × 𝒞`.**
`𝒞` here is the length-bounded program set print defines, so the finiteness the
argmax rests on is the one print gives, not an added hypothesis. -/
public theorem exists_argmax_printValue_prog (n t : ℕ)
    (h : History (CompAct Act (Prog 3)) Obs) :
    ∃ y : CompAct Act (Prog 3), ∀ y' : CompAct Act (Prog 3),
      printValue (sureProg 3) (survivalAgent (emptyProg (by norm_num)) 1)
          (stayProg 3) t n h y'
        ≤ printValue (sureProg 3) (survivalAgent (emptyProg (by norm_num)) 1)
          (stayProg 3) t n h y :=
  exists_argmax_printValue _ _ _ t n h

end AISafetyAtlas.Examples.Wireheading.SelfMod

