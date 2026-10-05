module

public import AISafetyAtlas.Sovereignty.ConcurrentGameFrame

/-!
# Frames off the SID corner

`AISafetyAtlas.Sovereignty.ConcurrentGameFrame` states Chen, Ju and Ågotnes's
Definitions 1, 5, 8 and 9 and their Fact 1 at print's own carrier, where a frame
has a state set, availability is indexed by state, and a joint action has a *set*
of possible successors. The atlas's older carrier, `GameForm`, is the `SID`
corner of that taxonomy and cannot express a frame that leaves it.

This file inhabits the three axes print separates, so that *not imposed* is
tested rather than asserted.

| Witness | Shows |
|---|---|
| `endFrame_not_serial` | print's motivating case: a game that ends, so some state has nothing available. A game form cannot express this — inhabitance there is a property of the strategy *types* |
| `endFrame_alphaPower_univ` | coalition monotonicity of alpha powers, at a frame that is not serial: the hypothesis `Forces.mono_coalition` carries is not needed |
| `coinFrame_not_deterministic` | a grand-coalition action with two possible successors |
| `clashFrame_not_independent` | two agents whose individually available actions are not jointly available |
| `exists_gcgf_not_superadditive` | and the consequence: **superadditivity fails** off the independent classes, where `forces_superadditive` makes it a theorem about every game form |
| `vetoGame_alphaPower_iff` | the bridge, instantiated: alpha power in the frame a game form induces is that game form's `α`-forcing |

The last two are the pair that matter. `forces_superadditive` is a theorem in
`AISafetyAtlas.Sovereignty.Separations` — no game form can fail it — and
`clashFrame` is a general concurrent game frame that does. So that theorem is a
fact about the `SID` corner rather than about print's carrier, which is print's
own caution about the eight labels read in the useful direction.
-/

namespace AISafetyAtlas.Examples.Sovereignty

open AISafetyAtlas.Sovereignty

/-- A `Bool` different from another is its negation. -/
private theorem eq_not_of_ne {b a : Bool} (h : b ≠ a) : b = !a := by
  cases b <;> cases a <;> simp at h ⊢

/-! ## A game that ends -/

/--
**Print's motivating failure of seriality.** One agent, two states: `false` is
live and steps to `true`, and `true` is the end of the game, from which nothing
is available.
-/
@[expose] public def endOut : Bool → (↥(Set.univ : Set Unit) → Unit) → Set Bool :=
  fun s _ => if s then (∅ : Set Bool) else {true}

/-- The frame that game determines, by print's own two conditions. -/
@[expose] public def endFrame : ActionFrame Unit Bool Unit :=
  ActionFrame.ofGrand endOut

/-- It is a general concurrent game frame. -/
public theorem endFrame_isGCGF : IsGCGF endFrame :=
  ofGrand_isGCGF endOut

/--
**Seriality fails, and it fails at a state.** Nothing is available to anybody
once the game has ended.

This is one of the two axes section 23 recorded four rows as narrower than print
on. `AISafetyAtlas.Sovereignty.Separations` carries print's seriality as the
instance hypothesis that each strategy type is inhabited, which is a property of
the types and therefore cannot hold at one state and fail at another.
-/
public theorem endFrame_not_serial : ¬ Serial endFrame := by
  intro h
  obtain ⟨σ, x, σ', -, hx⟩ := h (Set.univ : Set Unit) true
  simp only [endOut] at hx
  exact hx

/-- At the live state the **empty** coalition is already effective for the state
the game ends in: nobody has a choice to make. -/
public theorem endFrame_alphaPower_empty_coalition :
    AlphaPower endFrame (∅ : Set Unit) false {true} := by
  refine ⟨fun i => i.2.elim, ⟨true, fun _ => (), funext fun i => i.2.elim, ?_⟩, ?_⟩
  · exact rfl
  · rintro x ⟨σ', -, hx⟩
    exact hx

/--
**Coalition monotonicity of alpha powers, at a frame that is not serial.**

`Forces.mono_coalition` carries inhabitance of every strategy type, which is the
`SID`-corner form of print's seriality. The general statement
`IsGCGF.alphaPower_mono_coalition` needs no such hypothesis, and this
instantiates it at `endFrame`, where seriality is false.
-/
public theorem endFrame_alphaPower_univ :
    AlphaPower endFrame (Set.univ : Set Unit) false {true} :=
  endFrame_isGCGF.alphaPower_mono_coalition (Set.empty_subset _)
    endFrame_alphaPower_empty_coalition

/-! ## A frame that is not deterministic -/

/-- One agent whose single action leaves both states open. -/
@[expose] public def coinOut : Bool → (↥(Set.univ : Set Unit) → Unit) → Set Bool :=
  fun _ _ => Set.univ

/-- The frame it determines. -/
@[expose] public def coinFrame : ActionFrame Unit Bool Unit :=
  ActionFrame.ofGrand coinOut

/-- It is a general concurrent game frame. -/
public theorem coinFrame_isGCGF : IsGCGF coinFrame :=
  ofGrand_isGCGF coinOut

/--
**Determinism fails.** The grand coalition's available action has two possible
successors, which is the other axis a game form cannot reach: there `outcome` is
a function, so every complete profile has exactly one outcome.
-/
public theorem coinFrame_not_deterministic : ¬ Deterministic coinFrame := by
  intro h
  obtain ⟨t, ht⟩ := h true (fun _ => ()) ⟨true, fun _ => (), rfl, trivial⟩
  simp only [coinFrame, ofGrand_out_univ, coinOut] at ht
  have h₁ : true ∈ ({t} : Set Bool) := ht ▸ Set.mem_univ true
  have h₂ : false ∈ ({t} : Set Bool) := ht ▸ Set.mem_univ false
  rw [Set.mem_singleton_iff] at h₁ h₂
  exact Bool.noConfusion (h₁.trans h₂.symm)

/-! ## A frame that is not independent, and superadditivity falling with it -/

/--
**Two agents who must differ.** Agents, actions and states are all `Bool`. When
the two agents choose the same action nothing is possible; when they differ, the
state the game moves to is the *first* agent's choice.

Each agent alone is therefore effective for a state — whatever it plays, the
other must play the opposite for anything to be possible at all — and the two
states they are effective for are different.
-/
@[expose] public def clashOut : Bool → (↥(Set.univ : Set Bool) → Bool) → Set Bool :=
  fun _ σ =>
    if σ ⟨false, Set.mem_univ _⟩ = σ ⟨true, Set.mem_univ _⟩ then (∅ : Set Bool)
    else {σ ⟨false, Set.mem_univ _⟩}

/-- The frame it determines. -/
@[expose] public def clashFrame : ActionFrame Bool Bool Bool :=
  ActionFrame.ofGrand clashOut

/-- It is a general concurrent game frame: print's two conditions hold by
construction. -/
public theorem clashFrame_isGCGF : IsGCGF clashFrame :=
  ofGrand_isGCGF clashOut

/-- The grand-coalition action in which the first agent plays `a` and the second
plays `!a`. -/
@[expose] public def clashProfile (a : Bool) : ↥(Set.univ : Set Bool) → Bool :=
  fun i => if i.1 then !a else a

private theorem clashOut_clashProfile (s a : Bool) :
    clashOut s (clashProfile a) = {a} := by
  cases a <;> rfl

/-- **The first agent's outcome set, exactly.** Playing `a`, the first agent's
possible successors are exactly `{a}` — the second agent must play `!a` for
anything to be possible, and then the state is the first agent's choice. -/
public theorem clashFrame_out_fst (s a : Bool) :
    clashFrame.out {false} s (fun _ => a) = {a} := by
  ext x
  constructor
  · rintro ⟨σ', hσ', hx⟩
    have h0 : σ' ⟨false, Set.mem_univ _⟩ = a := congrFun hσ' ⟨false, rfl⟩
    by_cases hne : σ' ⟨false, Set.mem_univ _⟩ = σ' ⟨true, Set.mem_univ _⟩
    · rw [clashOut, if_pos hne] at hx; exact hx.elim
    · rw [clashOut, if_neg hne, h0] at hx; exact hx
  · intro hx
    refine ⟨clashProfile a, ?_, ?_⟩
    · funext i
      have hi : i.1 = false := i.2
      simp [restrictJA, clashProfile, hi]
    · rw [clashOut_clashProfile]; exact hx

/-- **The second agent's outcome set, exactly.** Playing `a`, its possible
successors are `{!a}`: the first agent must play `!a`, and the state is the first
agent's choice. -/
public theorem clashFrame_out_snd (s a : Bool) :
    clashFrame.out {true} s (fun _ => a) = {!a} := by
  ext x
  constructor
  · rintro ⟨σ', hσ', hx⟩
    have h1 : σ' ⟨true, Set.mem_univ _⟩ = a := congrFun hσ' ⟨true, rfl⟩
    by_cases hne : σ' ⟨false, Set.mem_univ _⟩ = σ' ⟨true, Set.mem_univ _⟩
    · rw [clashOut, if_pos hne] at hx; exact hx.elim
    · rw [clashOut, if_neg hne, Set.mem_singleton_iff] at hx
      rw [h1] at hne
      rw [Set.mem_singleton_iff, hx]
      exact eq_not_of_ne hne
  · intro hx
    refine ⟨clashProfile (!a), ?_, ?_⟩
    · funext i
      have hi : i.1 = true := i.2
      simp [restrictJA, clashProfile, hi]
    · rw [clashOut_clashProfile]; exact hx

/-- **Print's outcome-driven availability condition, read forwards.** Every
action of the first agent is available, because something is always possible. -/
public theorem clashFrame_av_fst (s a : Bool) :
    (fun _ => a : ↥({false} : Set Bool) → Bool) ∈ clashFrame.av {false} s :=
  (IsGCGF.mem_av_iff clashFrame_isGCGF).2 (by rw [clashFrame_out_fst]; exact ⟨a, rfl⟩)

/-- The same for the second agent. -/
public theorem clashFrame_av_snd (s a : Bool) :
    (fun _ => a : ↥({true} : Set Bool) → Bool) ∈ clashFrame.av {true} s :=
  (IsGCGF.mem_av_iff clashFrame_isGCGF).2 (by rw [clashFrame_out_snd]; exact ⟨!a, rfl⟩)

/-- **The first agent alone is effective for `a`.** -/
public theorem clashFrame_alphaPower_fst (s a : Bool) :
    AlphaPower clashFrame {false} s {a} :=
  ⟨fun _ => a, clashFrame_av_fst s a, (clashFrame_out_fst s a).le⟩

/-- **The second agent alone is effective for `!a`.** -/
public theorem clashFrame_alphaPower_snd (s a : Bool) :
    AlphaPower clashFrame {true} s {!a} :=
  ⟨fun _ => a, clashFrame_av_snd s a, (clashFrame_out_snd s a).le⟩

/-- Each is an **actual** power too: the outcome set is hit exactly, not merely
landed inside. -/
public theorem clashFrame_actualPowerAt_fst (s a : Bool) :
    ActualPowerAt clashFrame {false} s {a} :=
  actualPowerAt_iff_out_eq.2 ⟨fun _ => a, clashFrame_av_fst s a, clashFrame_out_fst s a⟩

/-- …and so it is in the actual effectivity function of the first agent. -/
public theorem clashFrame_mem_actualEff (s a : Bool) :
    ({a} : Set Bool) ∈ actualEff clashFrame {false} s :=
  mem_actualEff_iff.2 (clashFrame_actualPowerAt_fst s a)

/-- Dropping tightness leaves the alpha notion, on this frame. -/
public theorem clashFrame_alphaPower_of_actual (s a : Bool) :
    AlphaPower clashFrame {false} s {a} :=
  ActualPowerAt.alphaPower (clashFrame_actualPowerAt_fst s a)

/-- **Print's grand-coalition-induced outcome condition, pointwise**, on this
frame: a possible successor of the first agent's action comes from a
grand-coalition action extending it. -/
public theorem clashFrame_mem_out_iff (s a x : Bool) :
    x ∈ clashFrame.out {false} s (fun _ => a) ↔
      ∃ σ' : ↥(Set.univ : Set Bool) → Bool,
        restrictJA (Set.subset_univ ({false} : Set Bool)) σ' = (fun _ => a) ∧
          x ∈ clashFrame.out (Set.univ : Set Bool) s σ' :=
  IsGCGF.mem_out_iff clashFrame_isGCGF

/-- **Print's Fact 1 item 2** on this frame: the same union over the grand
coalition's *available* actions only. -/
public theorem clashFrame_out_eq_iUnion_av (s a : Bool) :
    clashFrame.out {false} s (fun _ => a) =
      ⋃ σ' ∈ {σ' : ↥(Set.univ : Set Bool) → Bool |
          σ' ∈ clashFrame.av (Set.univ : Set Bool) s ∧
            restrictJA (Set.subset_univ ({false} : Set Bool)) σ' = (fun _ => a)},
        clashFrame.out (Set.univ : Set Bool) s σ' :=
  IsGCGF.out_eq_iUnion_av clashFrame_isGCGF _ _ _

/-- **It is an `ε`-frame** — print's label imposing nothing — and, by
`clashFrame_not_independent`, not an `I`-frame. -/
public theorem clashFrame_isFrame_epsilon : IsFrame FrameClass.epsilon clashFrame :=
  isFrame_epsilon_iff.2 clashFrame_isGCGF

/--
**Independence fails.** Each agent alone may play `true`, and the two choices are
not jointly available: playing the same action leaves nothing possible.
-/
public theorem clashFrame_not_independent : ¬ Independent clashFrame := by
  intro h
  obtain ⟨x, σ', hσ', hx⟩ :=
    h true {false} {true} (Set.disjoint_singleton.2 Bool.false_ne_true)
      _ (clashFrame_av_fst true true) _ (clashFrame_av_snd true true)
  have h0 : σ' ⟨false, Set.mem_univ _⟩ = true := by
    have e := congrFun hσ' ⟨false, Or.inl rfl⟩
    simp only [restrictJA] at e
    rw [e]
    exact dif_pos rfl
  have h1 : σ' ⟨true, Set.mem_univ _⟩ = true := by
    have e := congrFun hσ' ⟨true, Or.inr rfl⟩
    simp only [restrictJA] at e
    rw [e]
    exact dif_neg (by simp)
  rw [clashOut, if_pos (h0.trans h1.symm)] at hx
  exact hx

/--
**Superadditivity is not a theorem of general concurrent game frames.**

`forces_superadditive` says every *game form* is superadditive, and section 21
uses that to conclude the axiom carries no information about domination. It is a
theorem there because print's independence condition holds by construction in a
game form. Here are two disjoint coalitions, each effective for a state, whose
union is not effective for the intersection — because the intersection is empty
and `IsGCGF.not_alphaPower_empty` says no coalition is ever effective for that.
-/
public theorem exists_gcgf_not_superadditive :
    ∃ (F : ActionFrame Bool Bool Bool) (C D : Set Bool) (s : Bool) (A B : Set Bool),
      IsGCGF F ∧ Disjoint C D ∧ AlphaPower F C s A ∧ AlphaPower F D s B ∧
        ¬ AlphaPower F (C ∪ D) s (A ∩ B) := by
  refine ⟨clashFrame, {false}, {true}, true, {true}, {false}, clashFrame_isGCGF,
    Set.disjoint_singleton.2 Bool.false_ne_true,
    clashFrame_alphaPower_fst true true, clashFrame_alphaPower_snd true true, ?_⟩
  have hAB : ({true} : Set Bool) ∩ {false} = (∅ : Set Bool) := by
    ext x
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨rfl, h⟩
    exact Bool.noConfusion h
  rw [hAB]
  exact clashFrame_isGCGF.not_alphaPower_empty _ _

/-! ## The bridge, instantiated -/

/-- The veto game's strategy sets are inhabited, which is print's seriality at
the `SID` corner. -/
public instance vetoGame_nonempty_strategy (i : Bool) : Nonempty (vetoGame.strategy i) :=
  ⟨true⟩

/--
**The frame the veto game induces, at print's Definition 5.** Alpha power there
is `α`-forcing here, at every state.
-/
public theorem vetoGame_alphaPower_iff (C : Set Bool) (s : Bool) (A : Set Bool) :
    AlphaPower (gameFrame vetoGame) C s A ↔ Forces vetoGame C A :=
  alphaPower_gameFrame C s A

/-- **The veto game's frame is an `SID`-frame**, which is where every row section
23 graded against a game form lives. -/
public theorem vetoGame_isFrame_sid : IsFrame FrameClass.sid (gameFrame vetoGame) :=
  gameFrame_isFrame_sid

/-- Neither player alone is effective for the good outcome, read off the frame
rather than off the game form. -/
public theorem vetoGame_not_alphaPower (s : Bool) :
    ¬ AlphaPower (gameFrame vetoGame) {true} s {true} :=
  fun h => vetoGame_not_forces ((vetoGame_alphaPower_iff _ s _).1 h)

/-- The veto game's frame is also an `ε`-frame, a `S`-frame, and so on through
print's eight labels — print's caution that the classes are not disjoint. -/
public theorem vetoGame_isFrame (Xc : FrameClass) : IsFrame Xc (gameFrame vetoGame) :=
  isFrame_of_sid Xc vetoGame_isFrame_sid

/-- Print's `ES` has eight labels, and the veto game's frame inhabits every one
of them — which is print's caution that the classes are not disjoint, on an
object. -/
public theorem vetoGame_isFrame_all_eight :
    Fintype.card FrameClass = 8 ∧ ∀ Xc : FrameClass, IsFrame Xc (gameFrame vetoGame) :=
  ⟨card_frameClass, vetoGame_isFrame⟩

/-- **The frame's alpha effectivity function is the game form's effectivity
family**, at every state. -/
public theorem vetoGame_alphaEff (C : Set Bool) (s : Bool) :
    alphaEff (gameFrame vetoGame) C s = effectivity vetoGame C :=
  alphaEff_gameFrame C s

/-- **Actual power in the frame is the game form's actual power.** -/
public theorem vetoGame_actualPowerAt_iff (C : Set Bool) (s : Bool) (A : Set Bool) :
    ActualPowerAt (gameFrame vetoGame) C s A ↔ ActualPower vetoGame C A :=
  actualPowerAt_gameFrame C s A

/-- Neither player alone has *actual* power over the good outcome either: actual
power implies alpha power, and that already fails. -/
public theorem vetoGame_not_actualPowerAt (s : Bool) :
    ¬ ActualPowerAt (gameFrame vetoGame) {true} s {true} :=
  fun h => vetoGame_not_alphaPower s (ActualPowerAt.alphaPower h)

/-- Alpha powers are closed under supersets, on the frame that ends. -/
public theorem endFrame_alphaPower_univ_target :
    AlphaPower endFrame (Set.univ : Set Unit) false (Set.univ : Set Bool) :=
  AlphaPower.mono endFrame_alphaPower_univ (Set.subset_univ _)

end AISafetyAtlas.Examples.Sovereignty
