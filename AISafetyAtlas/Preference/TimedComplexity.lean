module

public import AISafetyAtlas.Preference.SourceComplexity
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.ENNReal.Real
public import Mathlib.Data.ENNReal.Operations

/-!
# Proposition 10: Proposition 7 under the time-bounded complexities Kt_L and KT_L

Armstrong and Mindermann, appendix A (amapp-def-time-bounded, amapp-prop10,
PDF p. 1, printed p. 13):

  *"Kt_L(p, R) = min over α_p, α_R of l(α_p) + l(α_R) + log(t(α_p(α_R))),
  KT_L(p, R) = min over α_p, α_R of l(α_p) + l(α_R) + t(α_p(α_R))."*

  *"Proposition 10. The results of Proposition 7 still apply to (p_π̇, 0) if
  Kt_L or KT_L are used instead of K_L. If planner can take in algorithms
  generating reward functions, rather than simply reward functions, then the
  results of Proposition 7 still apply to (p_g, R_π̇) and (−p_g, −R_π̇) in this
  situation."*

`AISafetyAtlas.Preference.Source.indifferent_amongLowestFor` and its siblings
take the bound on each composite operation as a hypothesis. This module derives
those bounds for Kt_L and KT_L from print's proof sketch, whose premise is "L is
reasonable": the algorithm for the zero reward is short, the indifferent planner
need not read its input, and the wrappers W(α_π̇), W′(α_{p_g}) are *"of length
only slightly longer … and of runtime also only slightly longer"*.

## The interface

Print never fixes the language L. `AISafetyAtlas.Preference.Source.TimedLanguage`
is an abstract language with algorithm lengths l, running times t, application
α_S(α_T) and generation relations; its fields state the semantic correctness of
each program transform the sketch uses and an additive overhead c on its length
or running time. No field mentions Kt_L or KT_L of a pair: the complexity bounds
are theorems. `AISafetyAtlas.Preference.Source.CodePlanning` adds planners that
take reward code, and `AISafetyAtlas.Preference.Source.CodePlanning.Wrapping`
the wrappers W, W′, once for (p_g, R_π̇) and once for (−p_g, −R_π̇).

A concrete universal machine is deliberately not chosen: on a standard one the
simulation in W′(α_{p_g})(W(α_π̇)) need not have additive time overhead, and the
review panel warns that the KT_L half of the second sentence may then fail; that
was not checked here. Print's "L reasonable" is the overhead assumption, so it
is the interface.

## Results

* **Sentence 1** (`AISafetyAtlas.Preference.Source.TimedLanguage.proposition_ten_indifferent`):
  (p_π, 0) is amongst the lowest-Kt_L and amongst the lowest-KT_L pairs
  compatible with π, at distances 3c + log(1 + c) and 4c.
* **Sentence 2** (`AISafetyAtlas.Preference.Source.CodePlanning.proposition_ten_greedy`,
  `AISafetyAtlas.Preference.Source.CodePlanning.proposition_ten_antigreedy`):
  with planners taking reward code, (p_g, R_π) and (−p_g, −R_π) are amongst the
  lowest-Kt_L and lowest-KT_L compatible code-planner pairs, at distances
  l(α_{p_g}) + 3c + log(1 + c) and l(α_{p_g}) + 4c. The constants depend on the
  language and the fixed greedy-planner code only, never on π or the competitor.

## Readings

* Print's min is an infimum in the extended nonnegative reals: a pair no
  algorithm generates (a reward with a non-computable value, say) has complexity
  infinity, and the infimum is the minimum whenever print's min exists.
* The running time is an abstract field of `TimedLanguage`; print does not say
  whether the running time of an algorithm outputting a policy is per query,
  worst case or for the whole table, and any choice meeting the fields is
  covered. The logarithm is `Real.log`, whose value at 0 is 0, so a zero-step run
  counts as one step.
* A code-planner pair (q, R) is compatible with π when every code of R makes q
  output π (`AISafetyAtlas.Preference.Source.TimedLanguage.CodeCompatible`). For a
  planner whose output depends only on the reward its input computes, this is
  print's p(R) = π̇, and the existential reading over codes agrees
  (`AISafetyAtlas.Preference.Source.TimedLanguage.codeCompatible_iff_of_extensional`).
-/

namespace AISafetyAtlas.Preference.Source

open AISafetyAtlas.Preference
open scoped ENNReal

variable {S A Alg : Type*}

/-! ## Amongst the lowest, at any pair type -/

/-- **Amongst the lowest complexity in a set** (Armstrong and Mindermann, §5.1.3,
am-lowest), at any type of pairs: x satisfies Compat and no pair satisfying
Compat beats it by more than c. `AmongLowestFor` is the case of ordinary
planner-reward pairs (`amongLowestFor_iff_amongLowestIn`); appendix A's second
sentence needs it at planners taking code. -/
@[expose] public def AmongLowestIn {P α : Type*} [Add α] [LE α] (Compat : P → Prop)
    (K : P → α) (c : α) (x : P) : Prop :=
  Compat x ∧ ∀ y : P, Compat y → K x ≤ K y + c

/-- `AmongLowestFor` is `AmongLowestIn` at the compatible ordinary pairs. -/
public theorem amongLowestFor_iff_amongLowestIn {α : Type*} [Add α] [LE α]
    (K : Pair S A → α) (c : α) (π : Policy S A) (x : Pair S A) :
    AmongLowestFor K c π x ↔ AmongLowestIn (fun y => ReasonableForF.Compatible y π) K c x :=
  Iff.rfl

/-! ## The time-bounded measures -/

/-- **log t as an extended nonnegative cost**, the time term of Kt_L. -/
@[expose] public noncomputable def logTime (t : ℕ) : ℝ≥0∞ := ENNReal.ofReal (Real.log t)

/-- The time term of Kt_L is monotone in the step count. -/
public theorem logTime_mono : Monotone logTime := by
  intro m n hmn
  unfold logTime
  refine ENNReal.ofReal_le_ofReal ?_
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · simpa using Real.log_natCast_nonneg n
  · exact Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmn)

/-- An additive time overhead c costs at most log(1 + c) in the time term of
Kt_L. -/
public theorem logTime_add_le (t c : ℕ) :
    logTime (t + c) ≤ logTime t + ENNReal.ofReal (Real.log (1 + c)) := by
  unfold logTime
  have hc : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  rw [← ENNReal.ofReal_add (Real.log_natCast_nonneg t) (Real.log_nonneg (by linarith))]
  refine ENNReal.ofReal_le_ofReal ?_
  push_cast
  rcases Nat.eq_zero_or_pos t with rfl | ht
  · rcases Nat.eq_zero_or_pos c with rfl | hc'
    · simp
    · simp only [Nat.cast_zero, zero_add, Real.log_zero]
      exact Real.log_le_log (by exact_mod_cast hc') (by linarith)
  · have ht' : (1 : ℝ) ≤ t := by exact_mod_cast ht
    rw [← Real.log_mul (by positivity) (by positivity)]
    exact Real.log_le_log (by positivity) (by nlinarith)

/-- **A language with lengths and running times** (appendix A: *"if α is an
algorithm in the language of L, l(α) its length, and t(α) its running time"*),
with the constructions print's proof sketch of Proposition 10 uses, each correct
and each costing at most c extra length or time. Every field is about a
construction; none is a bound on Kt_L or KT_L.

* The application field is print's α_S(α_T), which *"generates S(T) by
  generating S with α_S, whenever S needs to look at T, it uses α_T"*; as an
  algorithm for the policy p(R) it is at most c longer than its parts.
* The zero algorithm generates the reward 0: *"l(α_0) can be very small (it's
  simply the zero function)"*.
* The hard-wiring field builds the indifferent planner p_π from an algorithm for
  π: it ignores its input and runs that algorithm (*"since p_π̇ need not
  actually look at its input, t(α_{p_π̇}(α_0)) can be simplified to t(α_π̇)"*). -/
public structure TimedLanguage (S A Alg : Type*) where
  /-- The length l(α) of an algorithm. -/
  len : Alg → ℕ
  /-- The running time t(α) of an algorithm. -/
  time : Alg → ℕ
  /-- α_S(α_T): run α_S, consulting α_T for its argument. -/
  app : Alg → Alg → Alg
  /-- The algorithm generates the policy. -/
  GenPolicy : Alg → Policy S A → Prop
  /-- The algorithm generates the reward function. -/
  GenReward : Alg → RewardFn S A → Prop
  /-- The algorithm generates the planner. -/
  GenPlanner : Alg → Planner (RewardFn S A) (Policy S A) → Prop
  /-- α_p(α_R) generates p(R). -/
  genPolicy_app : ∀ {αp αR : Alg} {p : Planner (RewardFn S A) (Policy S A)}
    {R : RewardFn S A}, GenPlanner αp p → GenReward αR R → GenPolicy (app αp αR) (p R)
  /-- The overhead constant of the language. -/
  c : ℕ
  /-- α_p(α_R), as an algorithm, is at most c longer than its parts. -/
  len_app_le : ∀ αp αR : Alg, len (app αp αR) ≤ len αp + len αR + c
  /-- α_0, an algorithm for the zero reward. -/
  zeroAlg : Alg
  genReward_zeroAlg : GenReward zeroAlg 0
  len_zeroAlg_le : len zeroAlg ≤ c
  /-- The indifferent planner hard-wired from an algorithm for its policy. -/
  hardwire : Alg → Alg
  genPlanner_hardwire : ∀ {α : Alg} {π : Policy S A},
    GenPolicy α π → GenPlanner (hardwire α) (indifferentPlanner π)
  len_hardwire_le : ∀ α : Alg, len (hardwire α) ≤ len α + c
  /-- Applied to α_0, the hard-wired planner just runs the algorithm it wraps. -/
  time_app_hardwire_le : ∀ α : Alg, time (app (hardwire α) zeroAlg) ≤ time α + c

namespace TimedLanguage

variable (L : TimedLanguage S A Alg)

/-- The cost of describing a pair by (α_p, α_R), with time cost g:
l(α_p) + l(α_R) + g(t(α_p(α_R))). -/
@[expose] public def descCost (g : ℕ → ℝ≥0∞) (αp αR : Alg) : ℝ≥0∞ :=
  (L.len αp : ℝ≥0∞) + L.len αR + g (L.time (L.app αp αR))

/-- **The time-bounded complexity of a planner-reward pair with time cost g**:
the least description cost over the algorithms generating its planner and its
reward. -/
@[expose] public noncomputable def pairComplexity (g : ℕ → ℝ≥0∞) (x : Pair S A) : ℝ≥0∞ :=
  ⨅ d : {d : Alg × Alg // L.GenPlanner d.1 x.1 ∧ L.GenReward d.2 x.2},
    L.descCost g d.1.1 d.1.2

/-- **Kt_L(p, R) = min l(α_p) + l(α_R) + log t(α_p(α_R))** (appendix A,
amapp-def-time-bounded, after Levin). -/
@[expose] public noncomputable def Kt (x : Pair S A) : ℝ≥0∞ := L.pairComplexity logTime x

/-- **KT_L(p, R) = min l(α_p) + l(α_R) + t(α_p(α_R))** (appendix A,
amapp-def-time-bounded, after Allender). -/
@[expose] public noncomputable def KT (x : Pair S A) : ℝ≥0∞ :=
  L.pairComplexity (fun t => (t : ℝ≥0∞)) x

/-- **The bound on the first composite operation, at any monotone time cost**:
`F₁` raises the complexity of every pair by at most 3c + e, where e bounds what
c extra steps cost. Print's sketch: from (α_p, α_R), the hard-wired planner
around α_p(α_R), paired with α_0, describes (p_{p(R)}, 0). -/
public theorem pairComplexity_F₁_le (g : ℕ → ℝ≥0∞) (hmono : Monotone g) (e : ℝ≥0∞)
    (hg : ∀ t, g (t + L.c) ≤ g t + e) (x : Pair S A) :
    L.pairComplexity g (F₁ x) ≤ L.pairComplexity g x + (3 * L.c + e) := by
  unfold pairComplexity
  rw [ENNReal.iInf_add]
  refine le_iInf fun d => ?_
  obtain ⟨⟨αp, αR⟩, hp, hR⟩ := d
  have hα : L.GenPolicy (L.app αp αR) (op3 x) := L.genPolicy_app hp hR
  refine (iInf_le _ ⟨(L.hardwire (L.app αp αR), L.zeroAlg),
    L.genPlanner_hardwire hα, L.genReward_zeroAlg⟩).trans ?_
  simp only [descCost]
  have h1 : (L.len (L.hardwire (L.app αp αR)) : ℝ≥0∞) ≤ L.len αp + L.len αR + 2 * L.c := by
    have := (L.len_hardwire_le _).trans (Nat.add_le_add_right (L.len_app_le αp αR) _)
    calc (L.len (L.hardwire (L.app αp αR)) : ℝ≥0∞)
        ≤ ((L.len αp + L.len αR + L.c + L.c : ℕ) : ℝ≥0∞) := by exact_mod_cast this
      _ = L.len αp + L.len αR + 2 * L.c := by push_cast; ring
  have h2 : (L.len L.zeroAlg : ℝ≥0∞) ≤ L.c := by exact_mod_cast L.len_zeroAlg_le
  have h3 : g (L.time (L.app (L.hardwire (L.app αp αR)) L.zeroAlg)) ≤
      g (L.time (L.app αp αR)) + e :=
    (hmono (L.time_app_hardwire_le _)).trans (hg _)
  calc (L.len (L.hardwire (L.app αp αR)) : ℝ≥0∞) + L.len L.zeroAlg +
        g (L.time (L.app (L.hardwire (L.app αp αR)) L.zeroAlg))
      ≤ (L.len αp + L.len αR + 2 * L.c) + L.c + (g (L.time (L.app αp αR)) + e) := by
        gcongr
    _ = L.len αp + L.len αR + g (L.time (L.app αp αR)) + (3 * L.c + e) := by ring

/-- **`F₁` raises Kt_L by at most 3c + log(1 + c).** -/
public theorem Kt_F₁_le (x : Pair S A) :
    L.Kt (F₁ x) ≤ L.Kt x + (3 * L.c + ENNReal.ofReal (Real.log (1 + L.c))) :=
  L.pairComplexity_F₁_le logTime logTime_mono _ (fun t => logTime_add_le t L.c) x

/-- **`F₁` raises KT_L by at most 4c.** -/
public theorem KT_F₁_le (x : Pair S A) : L.KT (F₁ x) ≤ L.KT x + 4 * L.c := by
  have h := L.pairComplexity_F₁_le (fun t => (t : ℝ≥0∞))
    (fun _ _ h => by dsimp only; exact_mod_cast h) (L.c : ℝ≥0∞) (fun t => by push_cast; rfl) x
  calc L.KT (F₁ x) ≤ L.KT x + (3 * L.c + L.c) := h
    _ = L.KT x + 4 * L.c := by ring

/-- **Proposition 10, first sentence** (Armstrong and Mindermann, appendix A,
amapp-prop10, PDF p. 1: *"The results of Proposition 7 still apply to (p_π̇, 0)
if Kt_L or KT_L are used instead of K_L"*). In any time-bounded language
meeting the overhead fields, the indifferent pair (p_π, 0) is amongst the
lowest-Kt_L pairs compatible with π, within 3c + log(1 + c), and amongst the
lowest-KT_L ones, within 4c. Any policy, any state and action types; the
competitors are all planner-reward pairs compatible with π. -/
public theorem proposition_ten_indifferent (π : Policy S A) :
    AmongLowestFor L.Kt (3 * L.c + ENNReal.ofReal (Real.log (1 + L.c))) π (op1 (op5 π)) ∧
      AmongLowestFor L.KT (4 * L.c) π (op1 (op5 π)) :=
  ⟨indifferent_amongLowestFor L.Kt _ L.Kt_F₁_le π,
    indifferent_amongLowestFor L.KT _ L.KT_F₁_le π⟩

/-! ## Planners taking reward code -/

/-- **A planner-reward pair whose planner reads reward code** (appendix A: *"a
planner takes as input not a reward function R ∈ ℛ, but the source code in L of
an algorithm that computes R"*). -/
public abbrev CodePair (S A Alg : Type*) : Type _ := (Alg → Policy S A) × RewardFn S A

/-- **Compatibility of a code-planner pair**: every code of the reward makes the
planner output the policy. -/
@[expose] public def CodeCompatible (y : CodePair S A Alg) (π : Policy S A) : Prop :=
  ∀ β : Alg, L.GenReward β y.2 → y.1 β = π

/-- **For a planner that reads only the reward its input computes, compatibility
is print's p(R) = π̇**, and the universal and existential readings over codes
agree, for any reward with a code. -/
public theorem codeCompatible_iff_of_extensional {q : Alg → Policy S A}
    {p : Planner (RewardFn S A) (Policy S A)}
    (hq : ∀ β R', L.GenReward β R' → q β = p R') {R : RewardFn S A} {β₀ : Alg}
    (hβ₀ : L.GenReward β₀ R) (π : Policy S A) :
    (L.CodeCompatible (q, R) π ↔ ReasonableForF.Compatible (p, R) π) ∧
      (L.CodeCompatible (q, R) π ↔ ∃ β, L.GenReward β R ∧ q β = π) := by
  refine ⟨⟨fun h => (hq β₀ R hβ₀).symm.trans (h β₀ hβ₀), fun h β hβ => (hq β R hβ).trans h⟩,
    ⟨fun h => ⟨β₀, hβ₀, h β₀ hβ₀⟩, fun ⟨β, hβ, h⟩ β' hβ' => ?_⟩⟩
  show q β' = π
  rw [hq β' R hβ', ← hq β R hβ, h]

/-- **The policy complexity**: the least l(α) + g(t(α)) over the algorithms
generating the policy, print's *"the Kt_L and KT_L complexities of π̇
itself"*. -/
@[expose] public noncomputable def policyComplexity (g : ℕ → ℝ≥0∞) (π : Policy S A) :
    ℝ≥0∞ :=
  ⨅ α : {α : Alg // L.GenPolicy α π}, (L.len α.1 : ℝ≥0∞) + g (L.time α.1)

end TimedLanguage

/-- **Planners taking reward code in a time-bounded language**: an algorithm
generates a code-planner q, and α_q(α_R) generates q(α_R). -/
public structure CodePlanning (L : TimedLanguage S A Alg) where
  /-- The algorithm generates the code-planner. -/
  GenCodePlanner : Alg → (Alg → Policy S A) → Prop
  /-- α_q(α_R) generates q(α_R). -/
  genPolicy_app_code : ∀ {αq αR : Alg} {q : Alg → Policy S A} {R : RewardFn S A},
    GenCodePlanner αq q → L.GenReward αR R → L.GenPolicy (L.app αq αR) (q αR)

namespace CodePlanning

variable {L : TimedLanguage S A Alg} (P : CodePlanning L)

/-- **The wrappers W and W′** for a reward built from a policy by ρ (print's
sketch: ρ π = R_π for (p_g, R_π̇), and −R_π for (−p_g, −R_π̇)).

* The reward wrapper is W(α): *"first it takes inputs s and a, then runs α on
  s, then returns 1 if the output of that is a and 0 otherwise. Thus W(α_π̇) is
  an algorithm for R_π̇."*
* The planner wrapper is W′(α): *"when provided with an input algorithm β, will
  check whether it is in the specific form β = W(α). If it is, it will run α,
  and output its output. If it is not, it will run α_{p_g} on β."* So W′(α)
  generates whatever code-planner α does, provided that planner already outputs,
  on each W(α′), the policy α′ computes.
* Both are at most c longer, and W′(α) run on W(α′) takes at most c more steps
  than α′. -/
public structure Wrapping (ρ : Policy S A → RewardFn S A) where
  /-- W(α). -/
  wrapReward : Alg → Alg
  /-- W′(α). -/
  wrapPlanner : Alg → Alg
  genReward_wrapReward : ∀ {α : Alg} {π : Policy S A},
    L.GenPolicy α π → L.GenReward (wrapReward α) (ρ π)
  genCodePlanner_wrapPlanner : ∀ {α : Alg} {q : Alg → Policy S A},
    P.GenCodePlanner α q → (∀ (α' : Alg) (π : Policy S A), L.GenPolicy α' π →
      q (wrapReward α') = π) → P.GenCodePlanner (wrapPlanner α) q
  len_wrapReward_le : ∀ α : Alg, L.len (wrapReward α) ≤ L.len α + L.c
  len_wrapPlanner_le : ∀ α : Alg, L.len (wrapPlanner α) ≤ L.len α + L.c
  time_app_wrap_le : ∀ α α' : Alg,
    L.time (L.app (wrapPlanner α) (wrapReward α')) ≤ L.time α' + L.c

/-- **The time-bounded complexity of a code-planner pair with time cost g**: the
least l(α_q) + l(α_R) + g(t(α_q(α_R))), print's formula with the planner now
reading α_R. -/
@[expose] public noncomputable def codePairComplexity (g : ℕ → ℝ≥0∞)
    (y : TimedLanguage.CodePair S A Alg) : ℝ≥0∞ :=
  ⨅ d : {d : Alg × Alg // P.GenCodePlanner d.1 y.1 ∧ L.GenReward d.2 y.2},
    L.descCost g d.1.1 d.1.2

/-- **Kt_L of a code-planner pair.** -/
@[expose] public noncomputable def codeKt (y : TimedLanguage.CodePair S A Alg) : ℝ≥0∞ :=
  P.codePairComplexity logTime y

/-- **KT_L of a code-planner pair.** -/
@[expose] public noncomputable def codeKT (y : TimedLanguage.CodePair S A Alg) : ℝ≥0∞ :=
  P.codePairComplexity (fun t => (t : ℝ≥0∞)) y

/-- **A compatible pair is no simpler than its policy, up to c**: α_q(α_R) is an
algorithm for the policy. -/
public theorem policyComplexity_le_codePairComplexity (g : ℕ → ℝ≥0∞)
    {y : TimedLanguage.CodePair S A Alg} {π : Policy S A} (hy : L.CodeCompatible y π) :
    L.policyComplexity g π ≤ P.codePairComplexity g y + L.c := by
  rw [codePairComplexity, ENNReal.iInf_add]
  refine le_iInf fun d => ?_
  obtain ⟨⟨αq, αR⟩, hq, hR⟩ := d
  have hα : L.GenPolicy (L.app αq αR) π := hy αR hR ▸ P.genPolicy_app_code hq hR
  refine (iInf_le _ ⟨L.app αq αR, hα⟩).trans ?_
  simp only [TimedLanguage.descCost]
  have h : (L.len (L.app αq αR) : ℝ≥0∞) ≤ L.len αq + L.len αR + L.c := by
    exact_mod_cast L.len_app_le αq αR
  calc (L.len (L.app αq αR) : ℝ≥0∞) + g (L.time (L.app αq αR))
      ≤ L.len αq + L.len αR + L.c + g (L.time (L.app αq αR)) := by gcongr
    _ = L.len αq + L.len αR + g (L.time (L.app αq αR)) + L.c := by ring

/-- **The wrapped pair is no more complex than its policy, up to
l(α_q) + 2c + e** (print's sketch: *"when running the algorithm W′(α_{p_g}) with
W(α_π̇) as input, this is only slightly longer in both senses than simply running
α_π̇"*). -/
public theorem codePairComplexity_wrap_le {ρ : Policy S A → RewardFn S A}
    (W : P.Wrapping ρ) (g : ℕ → ℝ≥0∞) (hmono : Monotone g) (e : ℝ≥0∞)
    (hg : ∀ t, g (t + L.c) ≤ g t + e) {αq : Alg} {q : Alg → Policy S A}
    (hαq : P.GenCodePlanner αq q)
    (hq : ∀ (α' : Alg) (π : Policy S A), L.GenPolicy α' π → q (W.wrapReward α') = π)
    (π : Policy S A) :
    P.codePairComplexity g (q, ρ π) ≤ L.policyComplexity g π + (L.len αq + 2 * L.c + e) := by
  rw [TimedLanguage.policyComplexity, ENNReal.iInf_add]
  refine le_iInf fun a => ?_
  obtain ⟨α, hα⟩ := a
  refine (iInf_le _ ⟨(W.wrapPlanner αq, W.wrapReward α),
    W.genCodePlanner_wrapPlanner hαq hq, W.genReward_wrapReward hα⟩).trans ?_
  simp only [TimedLanguage.descCost]
  have h1 : (L.len (W.wrapPlanner αq) : ℝ≥0∞) ≤ L.len αq + L.c := by
    exact_mod_cast W.len_wrapPlanner_le αq
  have h2 : (L.len (W.wrapReward α) : ℝ≥0∞) ≤ L.len α + L.c := by
    exact_mod_cast W.len_wrapReward_le α
  have h3 : g (L.time (L.app (W.wrapPlanner αq) (W.wrapReward α))) ≤ g (L.time α) + e :=
    (hmono (W.time_app_wrap_le αq α)).trans (hg _)
  calc (L.len (W.wrapPlanner αq) : ℝ≥0∞) + L.len (W.wrapReward α) +
        g (L.time (L.app (W.wrapPlanner αq) (W.wrapReward α)))
      ≤ (L.len αq + L.c) + (L.len α + L.c) + (g (L.time α) + e) := by gcongr
    _ = L.len α + g (L.time α) + (L.len αq + 2 * L.c + e) := by ring

/-- **A wrapped pair is amongst the lowest compatible code-planner pairs**, at
any monotone time cost, within l(α_q) + 3c + e. -/
public theorem amongLowestIn_wrap {ρ : Policy S A → RewardFn S A} (W : P.Wrapping ρ)
    (g : ℕ → ℝ≥0∞) (hmono : Monotone g) (e : ℝ≥0∞) (hg : ∀ t, g (t + L.c) ≤ g t + e)
    {αq : Alg} {q : Alg → Policy S A} (hαq : P.GenCodePlanner αq q)
    (hq : ∀ (α' : Alg) (π : Policy S A), L.GenPolicy α' π → q (W.wrapReward α') = π)
    {π : Policy S A} (hcompat : L.CodeCompatible (q, ρ π) π) :
    AmongLowestIn (fun y => L.CodeCompatible y π) (P.codePairComplexity g)
      (L.len αq + 3 * L.c + e) (q, ρ π) := by
  refine ⟨hcompat, fun y hy => ?_⟩
  calc P.codePairComplexity g (q, ρ π)
      ≤ L.policyComplexity g π + (L.len αq + 2 * L.c + e) :=
        P.codePairComplexity_wrap_le W g hmono e hg hαq hq π
    _ ≤ P.codePairComplexity g y + L.c + (L.len αq + 2 * L.c + e) := by
        gcongr; exact P.policyComplexity_le_codePairComplexity g hy
    _ = P.codePairComplexity g y + (L.len αq + 3 * L.c + e) := by ring

variable [Fintype A] [Nonempty A] [DecidableEq A]

/-- **Proposition 10, second sentence, greedy pair** (Armstrong and Mindermann,
appendix A, amapp-prop10: *"If planner can take in algorithms generating reward
functions, rather than simply reward functions, then the results of
Proposition 7 still apply to (p_g, R_π̇)"*). In any time-bounded language with
code planners and the wrappers W, W′, let q be the greedy planner on codes (on a
code of R it outputs p_g(R)) and α_{p_g} an algorithm for it. Then for every
policy π, (q, R_π) is amongst the lowest-Kt_L code-planner pairs compatible with
π, within l(α_{p_g}) + 3c + log(1 + c), and amongst the lowest-KT_L ones, within
l(α_{p_g}) + 4c. -/
public theorem proposition_ten_greedy (W : P.Wrapping rewardOf) {αg : Alg}
    {qg : Alg → Policy S A} (hαg : P.GenCodePlanner αg qg)
    (hqg : ∀ (β : Alg) (R : RewardFn S A), L.GenReward β R → qg β = greedyPlanner R)
    (π : Policy S A) :
    AmongLowestIn (fun y => L.CodeCompatible y π) P.codeKt
        (L.len αg + 3 * L.c + ENNReal.ofReal (Real.log (1 + L.c))) (qg, rewardOf π) ∧
      AmongLowestIn (fun y => L.CodeCompatible y π) P.codeKT
        (L.len αg + 4 * L.c) (qg, rewardOf π) := by
  have hq : ∀ (α' : Alg) (σ : Policy S A), L.GenPolicy α' σ → qg (W.wrapReward α') = σ :=
    fun α' σ h => (hqg _ _ (W.genReward_wrapReward h)).trans (op3_op2_op6 σ)
  have hc : L.CodeCompatible (qg, rewardOf π) π :=
    fun β hβ => (hqg β _ hβ).trans (op3_op2_op6 π)
  refine ⟨P.amongLowestIn_wrap W logTime logTime_mono _ (fun t => logTime_add_le t L.c)
    hαg hq hc, ?_⟩
  have h := P.amongLowestIn_wrap W (fun t => (t : ℝ≥0∞))
    (fun _ _ h => by dsimp only; exact_mod_cast h) (L.c : ℝ≥0∞) (fun t => by push_cast; rfl)
    hαg hq hc
  rwa [show (L.len αg : ℝ≥0∞) + 3 * L.c + L.c = L.len αg + 4 * L.c by ring] at h

/-- **Proposition 10, second sentence, anti-rational pair** (amapp-prop10:
*"… and (−p_g, −R_π̇) in this situation"*). As `proposition_ten_greedy`, with q
the planner −p_g on codes (on a code of R it outputs p_g(−R), print's
Definition 5) and the wrappers for −R_π. -/
public theorem proposition_ten_antigreedy (W : P.Wrapping fun π => -rewardOf π) {αn : Alg}
    {qn : Alg → Policy S A} (hαn : P.GenCodePlanner αn qn)
    (hqn : ∀ (β : Alg) (R : RewardFn S A), L.GenReward β R → qn β = greedyPlanner (-R))
    (π : Policy S A) :
    AmongLowestIn (fun y => L.CodeCompatible y π) P.codeKt
        (L.len αn + 3 * L.c + ENNReal.ofReal (Real.log (1 + L.c))) (qn, -rewardOf π) ∧
      AmongLowestIn (fun y => L.CodeCompatible y π) P.codeKT
        (L.len αn + 4 * L.c) (qn, -rewardOf π) := by
  have hq : ∀ (α' : Alg) (σ : Policy S A), L.GenPolicy α' σ → qn (W.wrapReward α') = σ :=
    fun α' σ h => (hqn _ _ (W.genReward_wrapReward h)).trans (op3_op4_op2_op6 σ)
  have hc : L.CodeCompatible (qn, -rewardOf π) π :=
    fun β hβ => (hqn β _ hβ).trans (op3_op4_op2_op6 π)
  refine ⟨P.amongLowestIn_wrap W logTime logTime_mono _ (fun t => logTime_add_le t L.c)
    hαn hq hc, ?_⟩
  have h := P.amongLowestIn_wrap W (fun t => (t : ℝ≥0∞))
    (fun _ _ h => by dsimp only; exact_mod_cast h) (L.c : ℝ≥0∞) (fun t => by push_cast; rfl)
    hαn hq hc
  rwa [show (L.len αn : ℝ≥0∞) + 3 * L.c + L.c = L.len αn + 4 * L.c by ring] at h

end CodePlanning

end AISafetyAtlas.Preference.Source
