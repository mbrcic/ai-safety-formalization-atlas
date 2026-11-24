module

public import AISafetyAtlas.Preference.TimedComplexity

/-!
# A toy timed language for Proposition 10

`toyLanguage` is a small language with syntax (`ToyCode`), a denotation into
semantic values (`toyDen`), lengths and step counts, every one at least 1, and
overhead constant 1. Policy, reward and reward-planner tables are primitive
codes; the constructors `ToyCode.hard`, `ToyCode.wrapR` and `ToyCode.wrapP` are
print's hard-wired indifferent planner and the wrappers W, W′, and `ToyCode.app`
is α_S(α_T). The greedy code planner runs its argument once per action, so its
time is |A| · t + 1: the overhead print's appendix A complains of, which the
wrappers bypass.

Every code denotes at most one policy and at most one reward
(`toy_genPolicy_unique`, `toy_genReward_unique`), so the generation relations are
not trivial; the degenerate pairs and ordinary competitors have finite KT_L
(`toy_KT_indifferent_le`, `toy_KT_greedy_pair_le`, `toy_codeKT_greedy_le`,
`toy_codeKT_competitor_le`), so "amongst the lowest" compares real numbers.
-/

namespace AISafetyAtlas.Examples.Preference.TimedComplexity

open AISafetyAtlas.Preference AISafetyAtlas.Preference.Source
open scoped ENNReal

variable {S A : Type}

/-- **Codes of the toy language.** -/
public inductive ToyCode (S A : Type) where
  /-- A policy table. -/
  | pol : Policy S A → ToyCode S A
  /-- A reward table. -/
  | rew : RewardFn S A → ToyCode S A
  /-- A reward-function planner, as a black box. -/
  | plan : Planner (RewardFn S A) (Policy S A) → ToyCode S A
  /-- The greedy planner on reward code. -/
  | greedy : ToyCode S A
  /-- The anti-greedy planner −p_g on reward code. -/
  | antigreedy : ToyCode S A
  /-- The indifferent planner hard-wired around a policy algorithm. -/
  | hard : ToyCode S A → ToyCode S A
  /-- W(α) (sign false) and its negated twin (sign true). -/
  | wrapR : Bool → ToyCode S A → ToyCode S A
  /-- W′(α) (sign false) and its negated twin (sign true). -/
  | wrapP : Bool → ToyCode S A → ToyCode S A
  /-- α_S(α_T). -/
  | app : ToyCode S A → ToyCode S A → ToyCode S A

/-- **Semantic values of toy codes.** A reward code built by W records the
policy it wraps, which is what lets W′ recognise it. -/
public inductive ToyVal (S A : Type) where
  | pol : Policy S A → ToyVal S A
  | rew : RewardFn S A → ToyVal S A
  | wrapped : Bool → Policy S A → ToyVal S A
  | plan : Planner (RewardFn S A) (Policy S A) → ToyVal S A
  | greedy : ToyVal S A
  | antigreedy : ToyVal S A
  | const : Option (Policy S A) → ToyVal S A
  | wrapP : Bool → ToyVal S A → ToyVal S A
  | junk : ToyVal S A

/-- The reward a wrapped policy computes: R_π (sign false) or −R_π (sign true). -/
@[expose] public def signedReward [DecidableEq A] : Bool → Policy S A → RewardFn S A
  | false, π => rewardOf π
  | true, π => -rewardOf π

/-- The reward a value computes, if any. -/
@[expose] public def toyRew [DecidableEq A] : ToyVal S A → Option (RewardFn S A)
  | .rew R => some R
  | .wrapped b π => some (signedReward b π)
  | _ => none

/-- The policy a value is, if any. -/
@[expose] public def toyPol : ToyVal S A → Option (Policy S A)
  | .pol π => some π
  | _ => none

variable [Fintype A] [Nonempty A] [DecidableEq A]

/-- **Applying a planner value to an argument value.** W′ checks whether its
argument is a wrapped policy of its own sign and, if so, outputs that policy;
otherwise it runs the planner it wraps. -/
@[expose] public noncomputable def toyApply : ToyVal S A → ToyVal S A → Option (Policy S A)
  | .plan p, v => (toyRew v).map p
  | .greedy, v => (toyRew v).map greedyPlanner
  | .antigreedy, v => (toyRew v).map fun R => greedyPlanner (-R)
  | .const o, _ => o
  | .wrapP b f, v =>
      match v with
      | .wrapped b' π => if b = b' then some π else toyApply f v
      | _ => toyApply f v
  | _, _ => none

/-- **The denotation of a toy code.** -/
@[expose] public noncomputable def toyDen : ToyCode S A → ToyVal S A
  | .pol π => .pol π
  | .rew R => .rew R
  | .plan p => .plan p
  | .greedy => .greedy
  | .antigreedy => .antigreedy
  | .hard a => .const (toyPol (toyDen a))
  | .wrapR b a =>
      match toyDen a with
      | .pol π => .wrapped b π
      | _ => .junk
  | .wrapP b a => .wrapP b (toyDen a)
  | .app a b =>
      match toyApply (toyDen a) (toyDen b) with
      | some π => .pol π
      | none => .junk

omit [Fintype A] [Nonempty A] [DecidableEq A] in
/-- **The length of a toy code**: one per constructor. -/
@[expose] public def toyLen : ToyCode S A → ℕ
  | .hard a => toyLen a + 1
  | .wrapR _ a => toyLen a + 1
  | .wrapP _ a => toyLen a + 1
  | .app a b => toyLen a + toyLen b + 1
  | _ => 1

/-- **The running time of a toy code.** A hard-wired planner just runs its
policy; W′ on a W of its sign just runs the wrapped algorithm; the greedy
planner runs its argument once per action. -/
@[expose] public def toyTime : ToyCode S A → ℕ
  | .app (.hard a) _ => toyTime a + 1
  | .app (.wrapP b a) (.wrapR b' α) => if b = b' then toyTime α + 1 else toyTime a + toyTime α + 2
  | .app .greedy β => Fintype.card A * toyTime β + 1
  | .app .antigreedy β => Fintype.card A * toyTime β + 1
  | .app a β => toyTime a + toyTime β + 1
  | .hard a => toyTime a + 1
  | .wrapR _ a => toyTime a + 1
  | .wrapP _ a => toyTime a + 1
  | _ => 1

/-- **The toy timed language**, with overhead constant 1. -/
@[expose] public noncomputable def toyLanguage : TimedLanguage S A (ToyCode S A) where
  len := toyLen
  time := toyTime
  app := .app
  GenPolicy α π := toyDen α = .pol π
  GenReward α R := toyRew (toyDen α) = some R
  GenPlanner α p := ∀ v R, toyRew v = some R → toyApply (toyDen α) v = some (p R)
  genPolicy_app := by
    intro αp αR p R hp hR
    simp [toyDen, hp _ _ hR]
  c := 1
  len_app_le _ _ := le_rfl
  zeroAlg := .rew 0
  genReward_zeroAlg := rfl
  len_zeroAlg_le := le_rfl
  hardwire := .hard
  genPlanner_hardwire := by
    intro α π h v R _
    simp [toyDen, h, toyPol, toyApply, indifferentPlanner]
  len_hardwire_le _ := le_rfl
  time_app_hardwire_le _ := le_rfl

/-- **Code planners in the toy language**: an algorithm generates a code
planner when, on every reward code, applying the algorithm gives the planner's
output. -/
@[expose] public noncomputable def toyCodePlanning :
    CodePlanning (toyLanguage (S := S) (A := A)) where
  GenCodePlanner α q :=
    ∀ β R, toyRew (toyDen β) = some R → toyApply (toyDen α) (toyDen β) = some (q β)
  genPolicy_app_code := by
    intro αq αR q R hq hR
    show toyDen (.app αq αR) = .pol (q αR)
    simp [toyDen, hq _ _ hR]

/-- Only W builds a wrapped value, and only around a policy algorithm. -/
public theorem toyDen_eq_wrapped {β : ToyCode S A} {b : Bool} {π : Policy S A}
    (h : toyDen β = .wrapped b π) : ∃ α, β = .wrapR b α ∧ toyDen α = .pol π := by
  cases β with
  | wrapR b' a =>
    simp only [toyDen] at h
    split at h
    · rename_i σ hσ
      cases h
      exact ⟨a, rfl, hσ⟩
    · cases h
  | app a c =>
    simp only [toyDen] at h
    split at h <;> cases h
  | _ => simp [toyDen] at h

/-- **The toy wrappers W, W′** of a given sign. -/
@[expose] public noncomputable def toyWrapping (b : Bool) :
    (toyCodePlanning (S := S) (A := A)).Wrapping (signedReward b) where
  wrapReward := .wrapR b
  wrapPlanner := .wrapP b
  genReward_wrapReward := by
    intro α π h
    have h' : toyDen α = .pol π := h
    show toyRew (toyDen (.wrapR b α)) = some (signedReward b π)
    simp [toyDen, h', toyRew]
  genCodePlanner_wrapPlanner := by
    intro α q hα hq β R hR
    show toyApply (.wrapP b (toyDen α)) (toyDen β) = some (q β)
    cases hβ : toyDen β with
    | wrapped b' σ =>
      by_cases hb : b = b'
      · subst hb
        obtain ⟨α', rfl, hα'⟩ := toyDen_eq_wrapped hβ
        simp [toyApply, hq α' σ hα']
      · rw [← hβ]
        simp only [toyApply, hβ, hb, if_false]
        rw [← hβ]
        exact hα β R hR
    | _ =>
      rw [← hβ]
      simp only [toyApply, hβ]
      rw [← hβ]
      exact hα β R hR
  len_wrapReward_le _ := le_rfl
  len_wrapPlanner_le _ := le_rfl
  time_app_wrap_le _ _ := by
    show toyTime (.app (.wrapP b _) (.wrapR b _)) ≤ _
    simp [toyTime, toyLanguage]

/-- **The greedy planner on toy codes**: p_g of the reward its argument
computes. -/
@[expose] public noncomputable def toyGreedy (β : ToyCode S A) : Policy S A :=
  match toyRew (toyDen β) with
  | some R => greedyPlanner R
  | none => greedyPlanner 0

/-- **The anti-greedy planner on toy codes**: p_g(−R) for the reward R its
argument computes. -/
@[expose] public noncomputable def toyAntiGreedy (β : ToyCode S A) : Policy S A :=
  match toyRew (toyDen β) with
  | some R => greedyPlanner (-R)
  | none => greedyPlanner 0

public theorem toy_genCodePlanner_greedy :
    (toyCodePlanning (S := S) (A := A)).GenCodePlanner .greedy toyGreedy := by
  intro β R h
  simp [toyDen, toyApply, toyGreedy, h]

public theorem toy_genCodePlanner_antigreedy :
    (toyCodePlanning (S := S) (A := A)).GenCodePlanner .antigreedy toyAntiGreedy := by
  intro β R h
  simp [toyDen, toyApply, toyAntiGreedy, h]

public theorem toyGreedy_spec (β : ToyCode S A) (R : RewardFn S A)
    (h : (toyLanguage (S := S) (A := A)).GenReward β R) : toyGreedy β = greedyPlanner R := by
  simp only [toyGreedy]
  rw [show toyRew (toyDen β) = some R from h]

public theorem toyAntiGreedy_spec (β : ToyCode S A) (R : RewardFn S A)
    (h : (toyLanguage (S := S) (A := A)).GenReward β R) :
    toyAntiGreedy β = greedyPlanner (-R) := by
  simp only [toyAntiGreedy]
  rw [show toyRew (toyDen β) = some R from h]

/-! ## The toy language is not degenerate -/

/-- **A toy code generates at most one policy.** -/
public theorem toy_genPolicy_unique {α : ToyCode S A} {π π' : Policy S A}
    (h : (toyLanguage (S := S) (A := A)).GenPolicy α π)
    (h' : (toyLanguage (S := S) (A := A)).GenPolicy α π') : π = π' := by
  have : (ToyVal.pol π : ToyVal S A) = .pol π' := h.symm.trans h'
  cases this; rfl

/-- **A toy code generates at most one reward.** -/
public theorem toy_genReward_unique {α : ToyCode S A} {R R' : RewardFn S A}
    (h : (toyLanguage (S := S) (A := A)).GenReward α R)
    (h' : (toyLanguage (S := S) (A := A)).GenReward α R') : R = R' :=
  Option.some_injective _ (h.symm.trans h')

/-- **The indifferent pair has finite KT_L**: (hard (pol π), rew 0) describes
it at length 3 and time 2. -/
public theorem toy_KT_indifferent_le (π : Policy S A) :
    AISafetyAtlas.Preference.Source.TimedLanguage.KT toyLanguage (op1 (op5 π)) ≤ 5 := by
  refine (iInf_le _ ⟨(ToyCode.hard (.pol π), ToyCode.rew 0),
    (toyLanguage (S := S) (A := A)).genPlanner_hardwire (π := π) rfl, rfl⟩).trans ?_
  simp [TimedLanguage.descCost, toyLanguage, toyLen, toyTime]
  norm_num

/-- **An ordinary compatible competitor has finite KT_L**: the greedy pair
(p_g, R_π) on reward functions, described by two black-box tables. -/
public theorem toy_KT_greedy_pair_le (π : Policy S A) :
    AISafetyAtlas.Preference.Source.TimedLanguage.KT toyLanguage
      (greedyPlanner, rewardOf π) ≤ 5 := by
  refine (iInf_le _ ⟨(ToyCode.plan greedyPlanner, ToyCode.rew (rewardOf π)),
    fun v R h => by simp [toyDen, toyApply, h], rfl⟩).trans ?_
  simp [TimedLanguage.descCost, toyLanguage, toyLen, toyTime]
  norm_num

/-- **The greedy code-planner pair has finite KT_L**: (W′(greedy), W(pol π))
describes it at length 4 and time 2. -/
public theorem toy_codeKT_greedy_le (π : Policy S A) :
    AISafetyAtlas.Preference.Source.CodePlanning.codeKT toyCodePlanning
      (toyGreedy, rewardOf π) ≤ 6 := by
  refine (iInf_le _ ⟨(ToyCode.wrapP false .greedy, ToyCode.wrapR false (.pol π)),
    (toyWrapping false).genCodePlanner_wrapPlanner toy_genCodePlanner_greedy
      (fun α' σ h => (toyGreedy_spec _ _ ((toyWrapping false).genReward_wrapReward h)).trans
        (op3_op2_op6 σ)),
    (toyWrapping false).genReward_wrapReward (π := π) rfl⟩).trans ?_
  simp [TimedLanguage.descCost, toyLanguage, toyLen, toyTime]
  norm_num

/-- The planner that outputs π on every code, from the black-box table of the
indifferent planner. -/
@[expose] public def toyConstCP (π : Policy S A) : ToyCode S A → Policy S A := fun _ => π

/-- **A compatible code-planner competitor has finite KT_L**: the indifferent
planner, as a black box, paired with the zero reward. -/
public theorem toy_codeKT_competitor_le (π : Policy S A) :
    AISafetyAtlas.Preference.Source.TimedLanguage.CodeCompatible toyLanguage
        (toyConstCP π, 0) π ∧
      AISafetyAtlas.Preference.Source.CodePlanning.codeKT toyCodePlanning
        (toyConstCP π, 0) ≤ 5 := by
  refine ⟨fun _ _ => rfl, (iInf_le _ ⟨(ToyCode.plan (indifferentPlanner π), ToyCode.rew 0),
    fun β R h => by simp [toyDen, toyApply, h, toyConstCP, indifferentPlanner], rfl⟩).trans ?_⟩
  simp [TimedLanguage.descCost, toyLanguage, toyLen, toyTime]
  norm_num

/-! ## Proposition 10 in the toy language -/

/-- **Proposition 10, first sentence, in the toy language**: the indifferent pair
is amongst the lowest-Kt_L compatible pairs within 3 + log 2, and amongst the
lowest-KT_L ones within 4. -/
public theorem toy_proposition_ten_indifferent (π : Policy S A) :
    AmongLowestFor (TimedLanguage.Kt toyLanguage)
        (3 * (1 : ℕ) + ENNReal.ofReal (Real.log (1 + (1 : ℕ)))) π (op1 (op5 π)) ∧
      AmongLowestFor (TimedLanguage.KT toyLanguage) (4 * (1 : ℕ)) π (op1 (op5 π)) :=
  AISafetyAtlas.Preference.Source.TimedLanguage.proposition_ten_indifferent toyLanguage π

/-- **Proposition 10, second sentence, greedy pair, in the toy language**:
(p_g, R_π) with planners reading code, within l(greedy) + 3 + log 2 = 4 + log 2
for Kt_L and 5 for KT_L. -/
public theorem toy_proposition_ten_greedy (π : Policy S A) :
    AmongLowestIn (fun y => TimedLanguage.CodeCompatible toyLanguage y π)
        (CodePlanning.codeKt toyCodePlanning)
        ((1 : ℕ) + 3 * (1 : ℕ) + ENNReal.ofReal (Real.log (1 + (1 : ℕ))))
        (toyGreedy, rewardOf π) ∧
      AmongLowestIn (fun y => TimedLanguage.CodeCompatible toyLanguage y π)
        (CodePlanning.codeKT toyCodePlanning) ((1 : ℕ) + 4 * (1 : ℕ))
        (toyGreedy, rewardOf π) :=
  AISafetyAtlas.Preference.Source.CodePlanning.proposition_ten_greedy toyCodePlanning
    (toyWrapping false) toy_genCodePlanner_greedy toyGreedy_spec π

/-- **Proposition 10, second sentence, anti-rational pair, in the toy
language.** -/
public theorem toy_proposition_ten_antigreedy (π : Policy S A) :
    AmongLowestIn (fun y => TimedLanguage.CodeCompatible toyLanguage y π)
        (CodePlanning.codeKt toyCodePlanning)
        ((1 : ℕ) + 3 * (1 : ℕ) + ENNReal.ofReal (Real.log (1 + (1 : ℕ))))
        (toyAntiGreedy, -rewardOf π) ∧
      AmongLowestIn (fun y => TimedLanguage.CodeCompatible toyLanguage y π)
        (CodePlanning.codeKT toyCodePlanning) ((1 : ℕ) + 4 * (1 : ℕ))
        (toyAntiGreedy, -rewardOf π) :=
  AISafetyAtlas.Preference.Source.CodePlanning.proposition_ten_antigreedy toyCodePlanning
    (toyWrapping true) toy_genCodePlanner_antigreedy toyAntiGreedy_spec π

/-- **The comparison bites**: the indifferent pair's KT_L is within 4 of the
ordinary greedy competitor's, and the greedy code pair's within 5 of the
code competitor's, both finite. -/
example (π : Policy S A) :
    TimedLanguage.KT toyLanguage (op1 (op5 π)) ≤
        TimedLanguage.KT toyLanguage (greedyPlanner, rewardOf π) + (4 * (1 : ℕ)) ∧
      CodePlanning.codeKT toyCodePlanning (toyGreedy, rewardOf π) ≤
        CodePlanning.codeKT toyCodePlanning (toyConstCP π, 0) + ((1 : ℕ) + 4 * (1 : ℕ)) :=
  ⟨(toy_proposition_ten_indifferent π).2.2 _ (op3_op2_op6 π),
    (toy_proposition_ten_greedy π).2.2 _ (toy_codeKT_competitor_le π).1⟩

/-- A code-planner pair, named through
`AISafetyAtlas.Preference.Source.TimedLanguage.CodePair`: the greedy code
planner with the reward of a policy. -/
@[expose] public noncomputable def toyGreedyPair (π : Policy S A) :
    AISafetyAtlas.Preference.Source.TimedLanguage.CodePair S A (ToyCode S A) :=
  (toyGreedy, rewardOf π)

example (π : Policy S A) :
    TimedLanguage.CodeCompatible toyLanguage (toyGreedyPair π) π :=
  (toy_proposition_ten_greedy π).1.1

/-! ## The intermediate bounds -/

/-- The `F₁` bounds for Kt_L and KT_L, at the toy language. -/
example (x : Pair S A) :
    TimedLanguage.Kt toyLanguage (F₁ x) ≤ TimedLanguage.Kt toyLanguage x +
        (3 * (1 : ℕ) + ENNReal.ofReal (Real.log (1 + (1 : ℕ)))) ∧
      TimedLanguage.KT toyLanguage (F₁ x) ≤ TimedLanguage.KT toyLanguage x + 4 * (1 : ℕ) :=
  ⟨AISafetyAtlas.Preference.Source.TimedLanguage.Kt_F₁_le toyLanguage x,
    AISafetyAtlas.Preference.Source.TimedLanguage.KT_F₁_le toyLanguage x⟩

/-- The generic `F₁` bound at the time cost log t. -/
example (x : Pair S A) :
    TimedLanguage.pairComplexity toyLanguage logTime (F₁ x) ≤
      TimedLanguage.pairComplexity toyLanguage logTime x +
        (3 * (1 : ℕ) + ENNReal.ofReal (Real.log (1 + (1 : ℕ)))) :=
  AISafetyAtlas.Preference.Source.TimedLanguage.pairComplexity_F₁_le toyLanguage logTime
    AISafetyAtlas.Preference.Source.logTime_mono _
    (fun t => AISafetyAtlas.Preference.Source.logTime_add_le t 1) x

/-- A compatible code pair is no simpler than its policy, and the wrapped greedy
pair no more complex than its policy, up to the constants. -/
example (π : Policy S A) :
    TimedLanguage.policyComplexity toyLanguage logTime π ≤
        CodePlanning.codePairComplexity toyCodePlanning logTime (toyConstCP π, 0) + (1 : ℕ) ∧
      CodePlanning.codePairComplexity toyCodePlanning logTime (toyGreedy, signedReward false π) ≤
        TimedLanguage.policyComplexity toyLanguage logTime π +
          ((1 : ℕ) + 2 * (1 : ℕ) + ENNReal.ofReal (Real.log (1 + (1 : ℕ)))) :=
  ⟨AISafetyAtlas.Preference.Source.CodePlanning.policyComplexity_le_codePairComplexity
      toyCodePlanning logTime (toy_codeKT_competitor_le π).1,
    AISafetyAtlas.Preference.Source.CodePlanning.codePairComplexity_wrap_le toyCodePlanning
      (toyWrapping false) logTime AISafetyAtlas.Preference.Source.logTime_mono _
      (fun t => AISafetyAtlas.Preference.Source.logTime_add_le t 1) toy_genCodePlanner_greedy
      (fun _α' σ h => (toyGreedy_spec _ _ ((toyWrapping false).genReward_wrapReward h)).trans
        (op3_op2_op6 σ)) π⟩

/-- **A wrapped pair is amongst the lowest at any monotone time cost**: here at
KT_L's, through the generic lemma. -/
example (π : Policy S A) :
    AmongLowestIn (fun y => TimedLanguage.CodeCompatible toyLanguage y π)
      (CodePlanning.codePairComplexity toyCodePlanning (fun t => (t : ℝ≥0∞)))
      ((1 : ℕ) + 3 * (1 : ℕ) + (1 : ℕ)) (toyGreedy, signedReward false π) :=
  AISafetyAtlas.Preference.Source.CodePlanning.amongLowestIn_wrap toyCodePlanning
    (toyWrapping false) (fun t => (t : ℝ≥0∞)) (fun _ _ h => by dsimp only; exact_mod_cast h)
    _ (fun t => by simp [toyLanguage]) toy_genCodePlanner_greedy
    (fun α' σ h => (toyGreedy_spec _ _ ((toyWrapping false).genReward_wrapReward h)).trans
      (op3_op2_op6 σ))
    (fun β h => (toyGreedy_spec β _ h).trans (op3_op2_op6 π))

/-- **Compatibility of the greedy code planner is print's p_g(R) = π**, and the
universal and existential readings agree, at a reward with a code. -/
example (π : Policy S A) (R : RewardFn S A) :
    (TimedLanguage.CodeCompatible toyLanguage (toyGreedy, R) π ↔
        ReasonableForF.Compatible (greedyPlanner, R) π) ∧
      (TimedLanguage.CodeCompatible toyLanguage (toyGreedy, R) π ↔
        ∃ β, (toyLanguage (S := S) (A := A)).GenReward β R ∧ toyGreedy β = π) :=
  AISafetyAtlas.Preference.Source.TimedLanguage.codeCompatible_iff_of_extensional toyLanguage
    toyGreedy_spec (β₀ := ToyCode.rew R) rfl π

/-- `AmongLowestFor` is `AmongLowestIn` at the compatible ordinary pairs. -/
example (π : Policy S A) :
    AmongLowestIn (fun y => ReasonableForF.Compatible y π) (TimedLanguage.KT toyLanguage)
      (4 * (1 : ℕ)) (op1 (op5 π)) :=
  (AISafetyAtlas.Preference.Source.amongLowestFor_iff_amongLowestIn _ _ π _).1
    (toy_proposition_ten_indifferent π).2

end AISafetyAtlas.Examples.Preference.TimedComplexity
