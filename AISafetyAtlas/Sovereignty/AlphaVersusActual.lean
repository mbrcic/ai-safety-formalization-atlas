module

public import AISafetyAtlas.Sovereignty.ConcurrentGameFrame

/-!
# Alpha powers versus actual powers: Chen, Ju and Ågotnes, §1.2 and Example 1

Chen, Ju & Ågotnes, *Representation theorems for actual and alpha powers over
general concurrent game frames without assuming independence of agents*,
arXiv:2607.10567v1, §1.2, PDF pp. 2--3:

> Actual powers provide a more precise account of coalition power in concurrent
> game frames than alpha powers. Consider the following example.

followed by Example 1, *Same alpha powers, different actual powers*, which ends
*"Thus the two scenarios are indistinguishable by alpha powers but are
distinguished by actual powers."*

"More precise" has two halves, and both are here.

* **Actual powers determine alpha powers.** `alphaEff_eq_supersets_actualEff`:
  at every action frame, coalition and state, the alpha powers are exactly the
  supersets of actual powers. `alphaEff_eq_of_actualEff_eq` is the consequence
  across two frames: equal actual powers give equal alpha powers.
* **Alpha powers do not determine actual powers.** `exists_alphaEff_eq_actualEff_ne`:
  two frames in print's most restrictive class SID (so in all eight classes, by
  `isFrame_of_sid`) with the same alpha powers for every coalition at every state
  and different actual powers at one coalition. The witness is print's Example 1,
  built in the namespace WarehouseGate with print's names.

The earlier non-monotonicity witness, `pinned_actualPower_singleton` with
`pinned_not_actualPower_pair`, does not give the second half: there the actual
powers are still the minimal alpha powers, so they can be read off the alpha
powers. In Example 1 the whole state set is an actual power of robot a in the
first scenario without being a minimal alpha power, and that is the information
alpha powers lose.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w u' w'

/-! ## Actual powers determine alpha powers -/

/--
**Alpha powers are the supersets of actual powers** (Chen, Ju & Ågotnes,
arXiv:2607.10567v1, §1.2 and §2.2). At any action frame, coalition and state, a
set is an alpha power exactly when it contains an actual power. This is the half
of print's *"actual powers provide a more precise account ... than alpha powers"*
that says the actual powers carry all the information the alpha powers do; it
packages `ActualPowerAt.alphaPower`, `AlphaPower.mono` and `mem_actualEff_iff`.
-/
public theorem alphaEff_eq_supersets_actualEff {AG : Type u} {ST : Type v} {AC : Type w}
    (F : ActionFrame AG ST AC) (C : Set AG) (s : ST) :
    alphaEff F C s = {X | ∃ Y ∈ actualEff F C s, Y ⊆ X} := by
  ext X
  constructor
  · rintro ⟨σ, hσ, hsafe⟩
    exact ⟨F.out C s σ, ⟨σ, hσ, rfl⟩, hsafe⟩
  · rintro ⟨Y, hY, hYX⟩
    exact (mem_actualEff_iff.1 hY).alphaPower.mono hYX

/--
**Equal actual powers give equal alpha powers**, across two action frames over
the same state set, whatever their agents and action sets (Chen, Ju & Ågotnes,
arXiv:2607.10567v1, §1.2). Example 1's converse failure is
`exists_alphaEff_eq_actualEff_ne`.
-/
public theorem alphaEff_eq_of_actualEff_eq {AG : Type u} {AG' : Type u'} {ST : Type v}
    {AC : Type w} {AC' : Type w'} {F : ActionFrame AG ST AC} {F' : ActionFrame AG' ST AC'}
    {C : Set AG} {C' : Set AG'} {s s' : ST}
    (h : actualEff F C s = actualEff F' C' s') :
    alphaEff F C s = alphaEff F' C' s' := by
  rw [alphaEff_eq_supersets_actualEff, alphaEff_eq_supersets_actualEff, h]

/-! ## Example 1: the warehouse gate -/

namespace WarehouseGate

/-- Print's two AI-driven robots controlling a warehouse gate; a has higher
authority than b. -/
public inductive Robot
  | a
  | b
deriving DecidableEq

/-- Print's two relevant states: w₁, the gate is closed, and w₂, the gate is
open. Print's W is the whole of this type. -/
public inductive GateState
  | w₁
  | w₂
deriving DecidableEq

/-- Robot a's three actions: open the gate, close it, delegate to robot b. -/
public inductive ActionA
  | open_a
  | close_a
  | delegate_a
deriving DecidableEq

/-- Robot b's two actions. -/
public inductive ActionB
  | open_b
  | close_b
deriving DecidableEq

/-- Each robot's own actions. -/
@[expose] public def gateStrategy : Robot → Type
  | .a => ActionA
  | .b => ActionB

/--
The state the gate ends in. In both scenarios open_a opens the gate and
close_a closes it whatever b does; the scenarios differ only in
delegate_a. When delegation works, b's action decides; when it is
ineffective, the gate closes regardless of b's action.
-/
@[expose] public def gateResult (delegationWorks : Bool) : ActionA → ActionB → GateState
  | .open_a, _ => .w₂
  | .close_a, _ => .w₁
  | .delegate_a, .open_b => if delegationWorks then .w₂ else .w₁
  | .delegate_a, .close_b => .w₁

/-- The round both robots play: they send their inputs simultaneously, each from
its own action set. -/
@[expose] public def gateGame (delegationWorks : Bool) : GameForm.{0, 0, 0} Robot GateState where
  strategy := gateStrategy
  outcome t := gateResult delegationWorks (t .a) (t .b)

/-- The action set shared by the robots: a robot together with one of its own
actions, so print's five actions open_a, close_a, delegate_a, open_b,
close_b. -/
public abbrev GateAction : Type := Σ i : Robot, gateStrategy i

/-- A scenario as an action frame. The dynamics are state-independent, as in
print: from either state the same round is played. -/
@[expose] public def scenario (delegationWorks : Bool) : ActionFrame Robot GateState GateAction :=
  gameFrame (gateGame delegationWorks)

/-- **Print's first scenario**: delegation works as intended. -/
@[expose] public def firstScenario : ActionFrame Robot GateState GateAction := scenario true

/-- **Print's second scenario**: delegation is ineffective. -/
@[expose] public def secondScenario : ActionFrame Robot GateState GateAction := scenario false

private instance gateStrategy_nonempty : ∀ i, Nonempty ((gateGame w).strategy i)
  | .a => ⟨ActionA.open_a⟩
  | .b => ⟨ActionB.open_b⟩

/-- A complete profile with a's action x and b opening. -/
private def withA (x : ActionA) : ∀ i, gateStrategy i
  | .a => x
  | .b => ActionB.open_b

/-- a's action that puts the gate in a given state, whatever b does. -/
private def forceA : GateState → ActionA
  | .w₁ => ActionA.close_a
  | .w₂ => ActionA.open_a

private theorem gateResult_forceA (w : Bool) (x : GateState) (y : ActionB) :
    gateResult w (forceA x) y = x := by
  cases x <;> rfl

/-- Both scenarios are SID frames, so they lie in every one of print's eight
classes. -/
public theorem scenario_isFrame_sid (delegationWorks : Bool) :
    IsFrame FrameClass.sid (scenario delegationWorks) :=
  gameFrame_isFrame_sid

private theorem forces_iff_of_mem (w : Bool) {C : Set Robot} (ha : Robot.a ∈ C)
    {A : Set GateState} : Forces (gateGame w) C A ↔ A.Nonempty := by
  classical
  constructor
  · rintro ⟨sC, hsC⟩
    let t : ∀ i, gateStrategy i := fun i => if hi : i ∈ C then sC ⟨i, hi⟩ else withA .open_a i
    exact ⟨_, hsC t (fun i => dif_pos i.2)⟩
  · rintro ⟨x, hx⟩
    refine ⟨fun i => withA (forceA x) i.1, fun t ht => ?_⟩
    have hta : t .a = forceA x := ht ⟨Robot.a, ha⟩
    have e : gateResult w (t .a) (t .b) = x := by
      rw [hta]; exact gateResult_forceA w x (t .b)
    change gateResult w (t .a) (t .b) ∈ A
    rw [e]
    exact hx

private theorem forces_iff_of_not_mem (w : Bool) {C : Set Robot} (ha : Robot.a ∉ C)
    {A : Set GateState} : Forces (gateGame w) C A ↔ A = Set.univ := by
  classical
  constructor
  · rintro ⟨sC, hsC⟩
    refine Set.eq_univ_of_forall fun x => ?_
    let t : ∀ i, gateStrategy i :=
      fun i => if hi : i ∈ C then sC ⟨i, hi⟩ else withA (forceA x) i
    have h := hsC t (fun i => dif_pos i.2)
    have hta : t .a = forceA x := dif_neg ha
    have e : gateResult w (t .a) (t .b) = x := by
      rw [hta]; exact gateResult_forceA w x (t .b)
    change gateResult w (t .a) (t .b) ∈ A at h
    rwa [e] at h
  · rintro rfl
    exact ⟨fun i => withA .open_a i.1, fun _ _ => Set.mem_univ _⟩

/-- **Print's alpha table, rows {a} and {a, b}**: a coalition containing a
has as alpha powers exactly the non-empty sets of states, in either scenario. -/
public theorem alphaEff_scenario_of_mem (delegationWorks : Bool) {C : Set Robot}
    (ha : Robot.a ∈ C) (s : GateState) :
    alphaEff (scenario delegationWorks) C s = {X | X.Nonempty} := by
  ext X
  exact (alphaPower_gameFrame C s X).trans (forces_iff_of_mem delegationWorks ha)

/-- **Print's alpha table, rows ∅ and {b}**: a coalition without a has the
whole state set as its only alpha power, in either scenario. -/
public theorem alphaEff_scenario_of_not_mem (delegationWorks : Bool) {C : Set Robot}
    (ha : Robot.a ∉ C) (s : GateState) :
    alphaEff (scenario delegationWorks) C s = {Set.univ} := by
  ext X
  exact (alphaPower_gameFrame C s X).trans (forces_iff_of_not_mem delegationWorks ha)

/-- **Print's "the two scenarios induce the same alpha powers for every
coalition"**, at every state. -/
public theorem alphaEff_firstScenario_eq_secondScenario (C : Set Robot) (s : GateState) :
    alphaEff firstScenario C s = alphaEff secondScenario C s := by
  by_cases ha : Robot.a ∈ C
  · rw [firstScenario, secondScenario, alphaEff_scenario_of_mem true ha,
      alphaEff_scenario_of_mem false ha]
  · rw [firstScenario, secondScenario, alphaEff_scenario_of_not_mem true ha,
      alphaEff_scenario_of_not_mem false ha]

/-- The outcome set of each of a's actions. -/
private def outA (w : Bool) : ActionA → Set GateState
  | .open_a => {.w₂}
  | .close_a => {.w₁}
  | .delegate_a => if w then Set.univ else {.w₁}

private theorem outcomesOf_singleton_a (w : Bool)
    (sC : ∀ i : ({Robot.a} : Set Robot), (gateGame w).strategy i) :
    outcomesOf (gateGame w) {Robot.a} sC = outA w (sC ⟨Robot.a, rfl⟩) := by
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    have hta : t .a = sC ⟨Robot.a, rfl⟩ := ht ⟨Robot.a, rfl⟩
    change gateResult w (t .a) (t .b) ∈ _
    rw [hta]
    generalize sC ⟨Robot.a, rfl⟩ = y
    generalize t .b = z
    cases y <;> cases z <;> cases w <;> simp [gateResult, outA]
  · intro hx
    have key : ∀ y : ActionA, x ∈ outA w y → ∃ z : ActionB, gateResult w y z = x := by
      intro y hy
      cases y <;> cases w <;> cases x <;> simp [outA, gateResult] at hy ⊢ <;>
        first | exact ⟨.open_b⟩ | exact ⟨.close_b, rfl⟩ | exact ⟨.open_b, rfl⟩
    obtain ⟨z, hz⟩ := key _ hx
    let t : ∀ i, gateStrategy i := fun
      | .a => sC ⟨Robot.a, rfl⟩
      | .b => z
    refine ⟨t, fun i => ?_, hz⟩
    obtain ⟨i, hi⟩ := i
    rw [Set.mem_singleton_iff] at hi
    subst hi
    rfl

private theorem actualEff_scenario_singleton_a (w : Bool) (s : GateState) :
    actualEff (scenario w) {Robot.a} s = Set.range (outA w) := by
  ext X
  rw [mem_actualEff_iff]
  refine (actualPowerAt_gameFrame (G := gateGame w) _ s X).trans ?_
  rw [actualPower_iff]
  constructor
  · rintro ⟨sC, rfl⟩
    exact ⟨_, (outcomesOf_singleton_a w sC).symm⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i => withA y i.1, outcomesOf_singleton_a w _⟩

/-- **Print's actual powers of {a} in the first scenario**: {w₁}, {w₂} and
W, because a can close, open or delegate. -/
public theorem actualEff_firstScenario_a (s : GateState) :
    actualEff firstScenario {Robot.a} s = {{.w₁}, {.w₂}, Set.univ} := by
  rw [firstScenario, actualEff_scenario_singleton_a]
  ext X
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩
    cases y <;> simp [outA]
  · rintro (rfl | rfl | rfl)
    exacts [⟨.close_a, rfl⟩, ⟨.open_a, rfl⟩, ⟨.delegate_a, rfl⟩]

/-- **Print's actual powers of {a} in the second scenario**: only {w₁} and
{w₂}; choosing delegate_a has the same exact outcome set as close_a. -/
public theorem actualEff_secondScenario_a (s : GateState) :
    actualEff secondScenario {Robot.a} s = {{.w₁}, {.w₂}} := by
  rw [secondScenario, actualEff_scenario_singleton_a]
  ext X
  simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨y, rfl⟩
    cases y <;> simp [outA]
  · rintro (rfl | rfl)
    exacts [⟨.close_a, rfl⟩, ⟨.open_a, rfl⟩]

/-- **Print's "the actual powers of {a} differ"**: the whole state set is an
actual power of a in the first scenario and not in the second. -/
public theorem univ_mem_actualEff_first_not_second (s : GateState) :
    Set.univ ∈ actualEff firstScenario {Robot.a} s ∧
      Set.univ ∉ actualEff secondScenario {Robot.a} s := by
  rw [actualEff_firstScenario_a, actualEff_secondScenario_a]
  refine ⟨Or.inr (Or.inr rfl), ?_⟩
  rintro (h | h)
  · exact absurd (h ▸ Set.mem_univ GateState.w₂ : GateState.w₂ ∈ ({.w₁} : Set GateState))
      (by simp)
  · exact absurd (h ▸ Set.mem_univ GateState.w₁ : GateState.w₁ ∈ ({.w₂} : Set GateState))
      (by simp)

end WarehouseGate

open WarehouseGate in
/--
**Alpha powers do not determine actual powers** (Chen, Ju & Ågotnes,
arXiv:2607.10567v1, §1.2 and Example 1): there are two frames, with finitely many
agents, in print's class SID (hence in all eight classes, by `isFrame_of_sid`),
that have the same alpha powers for every coalition at every state and different
actual powers at some coalition and state. With `alphaEff_eq_of_actualEff_eq` this
is print's *"actual powers provide a more precise account of coalition power ...
than alpha powers"*. The witnesses are `WarehouseGate.firstScenario` and
`WarehouseGate.secondScenario`.
-/
public theorem exists_alphaEff_eq_actualEff_ne :
    ∃ (AG ST AC : Type) (_ : Finite AG) (F₁ F₂ : ActionFrame AG ST AC),
      IsFrame FrameClass.sid F₁ ∧ IsFrame FrameClass.sid F₂ ∧
      (∀ C s, alphaEff F₁ C s = alphaEff F₂ C s) ∧
      ∃ C s, actualEff F₁ C s ≠ actualEff F₂ C s :=
  ⟨Robot, GateState, GateAction,
    Finite.of_injective (β := Bool) (fun | .a => false | .b => true)
      (by rintro (_ | _) (_ | _) h <;> first | rfl | cases h), firstScenario, secondScenario,
    scenario_isFrame_sid true, scenario_isFrame_sid false,
    alphaEff_firstScenario_eq_secondScenario, {Robot.a}, .w₁, fun h =>
      (univ_mem_actualEff_first_not_second .w₁).2 (h ▸ (univ_mem_actualEff_first_not_second .w₁).1)⟩

end AISafetyAtlas.Sovereignty
