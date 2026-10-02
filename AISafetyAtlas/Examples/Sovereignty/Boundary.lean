module

public import AISafetyAtlas.Sovereignty.Boundary
public import AISafetyAtlas.Sovereignty.Separations

/-!
# A boundary, held and overrun

The sovereignty module states that a coalition is sovereign over a boundary when
nothing outside it can move what the boundary sees, and proves that a sovereign
coalition is immune to power at every target its boundary expresses. Both claims
are about all games. This module runs them on one game, and adds the two facts
that keep the definition honest and cannot be proved in general because they are
existence claims.

## The game

Two parties and two coordinates. Party `0` sets the first, party `1` sets the
second, and the outcome is the pair. Read `0` as an agent and the first
coordinate as its cognition, or as a country and the first coordinate as its
territory: whichever reading, `0` owns one coordinate and `1` owns the other.

It is the simplest game in which a boundary can be drawn at all, because a
boundary needs something to be inside it and something outside.

## What these theorems say together

* `splitGame_sovereign_inside` — `0` is sovereign over its own coordinate.
  Nothing `1` does moves it.
* `splitGame_not_sovereign_outcome` — `0` is **not** sovereign over the whole
  outcome. So the boundary is doing work: drop it and the claim is false.
* `splitGame_not_sovereign_outside` — one outsider with one alternative move is
  enough to refute sovereignty over a view, with no claim about how likely that
  move is. This is the Carter–Shnayderman ubiquity objection, made concrete.
* `splitGame_hasPowerOver_outside` — `1` **does** have power over `0` at a
  target the boundary cannot express. Sovereignty is not immunity; it is
  immunity inside a boundary, and the qualifier is not decoration.
* `splitGame_dictates_outside` and `splitGame_inside_cannot_force_snd_false` —
  `1` puts the outside coordinate where it likes, and `0` then cannot guarantee
  anything about that coordinate which excludes what `1` chose.
* `splitGame_sovereign_and_powerful` — `0` is sovereign over its boundary **and**
  has power over `1`. Defence and influence are independent, so being sovereign
  is not a way of being harmless.

The last of these is the one worth stating aloud. Sovereignty is defensive by
construction — it quantifies over everyone outside and names no adversary — but
a sovereign party is not thereby a passive one, and nothing in the definition
says otherwise.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Boundary

open AISafetyAtlas.Sovereignty

/-- Party `0` sets the first coordinate, party `1` the second. -/
@[expose] public def splitGame : GameForm (Fin 2) (Bool × Bool) where
  strategy := fun _ ↦ Bool
  outcome := fun s ↦ (s 0, s 1)

/-- The boundary: what the outcome looks like inside `0`'s own coordinate. -/
@[expose] public def inside : Bool × Bool → Bool := Prod.fst

/-- **The boundary holds.** Whatever `1` plays, `0`'s coordinate is what `0`
made it. -/
public theorem splitGame_sovereign_inside :
    Sovereign splitGame {0} inside := by
  intro s s' hss'
  have h0 : s 0 = s' 0 := hss' ⟨0, rfl⟩
  show (splitGame.outcome s).1 = (splitGame.outcome s').1
  simpa [splitGame] using h0

/-- **The boundary is doing work.** `0` is not sovereign over the whole outcome:
`1` moves the second coordinate and the outcome moves with it.

Without a boundary the notion would be false here, which is why sovereignty is
stated relative to one. -/
public theorem splitGame_not_sovereign_outcome :
    ¬ Sovereign splitGame {0} (id : Bool × Bool → Bool × Bool) := by
  intro h
  have := h (fun _ ↦ false) (fun i ↦ if i = 1 then true else false)
    (by rintro ⟨i, hi⟩; simp at hi; subst hi; rfl)
  simp [splitGame] at this

/--
**The Carter-Shnayderman ubiquity argument, on the smallest game that shows it.**

Agent `1` sits outside `{0}` and has an alternative move that shifts the second
coordinate. That single fact -- one outsider, one deviation, no claim about how
likely it is -- is enough to refute sovereignty of `{0}` over the second
coordinate. The
argument scales exactly as the paper says it does: any view an outsider can move
at all is a view you are not sovereign over.
-/
public theorem splitGame_not_sovereign_outside :
    ¬ Sovereign splitGame {0} (Prod.snd : Bool × Bool → Bool) := by
  refine not_sovereign_of_outsider_moves_view (j := 1) (by decide)
    (fun _ ↦ false) true ?_
  simp [splitGame]

/-- **Sovereignty is not immunity.** `1` has power over `0` at the target
`{(true, true)}`, which `0`'s boundary cannot express: whether `0` can reach it
is settled by what `1` commits to.

A state sovereign over its territory is still subject to the price of wheat. -/
public theorem splitGame_hasPowerOver_outside :
    HasPowerOver splitGame {1} {0} {((true, true) : Bool × Bool)} := by
  refine ⟨?_, ⟨fun _ ↦ true, fun _ ↦ true, ?_⟩, ⟨fun _ ↦ false, ?_⟩⟩
  · rw [Set.disjoint_left]
    rintro i hi hi'
    simp at hi hi'
    exact absurd (hi.symm.trans hi') (by decide)
  · intro s hC hD
    have h1 : s 1 = true := hC ⟨1, rfl⟩
    have h0 : s 0 = true := hD ⟨0, rfl⟩
    show (s 0, s 1) ∈ _
    rw [h0, h1]; rfl
  · rintro ⟨sD, hsD⟩
    have h := hsD (fun i ↦ if i = 1 then false else sD ⟨0, rfl⟩)
      (by rintro ⟨i, hi⟩; simp at hi; subst hi; rfl)
      (by rintro ⟨i, hi⟩; simp at hi; subst hi; rfl)
    simp [splitGame] at h
    exact Bool.noConfusion (congrArg Prod.snd h)

/-- **Defence does not exclude influence.** `0` is sovereign over its boundary
and has power over `1` at the same time.

So sovereignty is not a way of being harmless, and the two notions are
independent rather than opposite. -/
public theorem splitGame_sovereign_and_powerful :
    Sovereign splitGame {0} inside ∧
      HasPowerOver splitGame {0} {1} {((true, true) : Bool × Bool)} := by
  refine ⟨splitGame_sovereign_inside, ?_, ⟨fun _ ↦ true, fun _ ↦ true, ?_⟩,
    ⟨fun _ ↦ false, ?_⟩⟩
  · rw [Set.disjoint_left]
    rintro i hi hi'
    simp at hi hi'
    exact absurd (hi.symm.trans hi') (by decide)
  · intro s hC hD
    have h0 : s 0 = true := hC ⟨0, rfl⟩
    have h1 : s 1 = true := hD ⟨1, rfl⟩
    show (s 0, s 1) ∈ _
    rw [h0, h1]; rfl
  · rintro ⟨sD, hsD⟩
    have h := hsD (fun i ↦ if i = 0 then false else sD ⟨1, rfl⟩)
      (by rintro ⟨i, hi⟩; simp at hi; subst hi; rfl)
      (by rintro ⟨i, hi⟩; simp at hi; subst hi; rfl)
    simp [splitGame] at h
    exact Bool.noConfusion (congrArg Prod.fst h)

/-- **The general theorem, instantiated.** No coalition has power over `0` at any
target its boundary expresses -- in particular at "`0`'s coordinate is `true`",
which is the thing `0` actually cares about. -/
public theorem splitGame_no_power_inside (C : Set (Fin 2)) (B : Set Bool) :
    ¬ HasPowerOver splitGame C {0} (inside ⁻¹' B) := by
  have : ∀ i, Nonempty (splitGame.strategy i) := fun _ ↦ ⟨true⟩
  exact not_hasPowerOver_of_sovereign splitGame_sovereign_inside B


/-! ## Dictation, and what it leaves the other party

`splitGame` shows the asymmetry directly. Agent `1` sets the second coordinate
and agent `0` receives it: not because `0` is idle, but because whatever `0`
guarantees about that coordinate has to be compatible with what `1` already set.
-/

/-- Agent `1` dictates the outside coordinate: its commitment settles what that
coordinate shows, whatever `0` plays. -/
public theorem splitGame_dictates_outside :
    Dictates splitGame {1} (Prod.snd : Bool × Bool → Bool) := by
  refine ⟨fun _ ↦ true, fun s s' hs hs' ↦ ?_⟩
  show (splitGame.outcome s).2 = (splitGame.outcome s').2
  simp only [splitGame]
  rw [hs ⟨1, rfl⟩, hs' ⟨1, rfl⟩]

/-- Agent `1` forces the outside coordinate to `true`. -/
public theorem splitGame_forces_snd_true :
    Forces splitGame {1} ((Prod.snd : Bool × Bool → Bool) ⁻¹' {true}) := by
  refine ⟨fun _ ↦ true, fun s hs ↦ ?_⟩
  show (splitGame.outcome s).2 ∈ ({true} : Set Bool)
  simp only [splitGame]
  rw [hs ⟨1, rfl⟩]
  rfl

/--
**The taker has no say about what the dictator set.** Agent `0` cannot guarantee
the outside coordinate is `false`, and the reason is not that `0` is weak in
general -- `splitGame_sovereign_and_powerful` shows `0` has power -- but that `1`
has already put that coordinate where `1` likes it.

This is `mem_of_forces_of_dictated` on the smallest game that carries it.
-/
public theorem splitGame_inside_cannot_force_snd_false :
    ¬ Forces splitGame {0} ((Prod.snd : Bool × Bool → Bool) ⁻¹' {false}) := by
  have hne : ∀ i, Nonempty (splitGame.strategy i) := fun _ ↦ ⟨true⟩
  intro h
  have hdisj : Disjoint ({1} : Set (Fin 2)) {0} := by
    rw [Set.disjoint_singleton]
    decide
  have : (true : Bool) ∈ ({false} : Set Bool) :=
    mem_of_forces_of_dictated hdisj splitGame_forces_snd_true h
  simp at this

/-! ## Options cut, outcomes unchanged -/

/-- Three actions into two outcomes, one of which an outsider can take away.

Action `0` produces `true`; actions `1` and `2` both produce `false`. With
`e = true` all three are available; with `e = false` action `2` is gone.

The outcome type is genuinely two-valued and both values are realised on both
sides, so the separation below is not an artefact of a degenerate outcome
space. -/
@[expose] public def twoRoutes : Curtailment Bool (Fin 3) Bool where
  available := fun e ↦ if e then Set.univ else {0, 1}
  outcome := fun a ↦ if a = 0 then true else false

/-- Both outcomes stay reachable whatever the outsider does. -/
public theorem twoRoutes_reach (e : Bool) :
    twoRoutes.reach e = (Set.univ : Set Bool) := by
  ext b
  simp only [Set.mem_univ, iff_true, Curtailment.reach, Set.mem_image]
  cases b
  · exact ⟨1, by cases e <;> simp [twoRoutes], by simp [twoRoutes]⟩
  · exact ⟨0, by cases e <;> simp [twoRoutes], by simp [twoRoutes]⟩

/-- **The separation the outcome view cannot see.** `twoRoutes` is curtailed --
an outsider removes one of the holder's actions -- while its reach is invariant,
because the removed action was a duplicate route to an outcome that stays
reachable.

So `Uncurtailed` is strictly stronger than `ReachInvariant`, and an account of
sovereignty stated only over outcomes scores this intrusion as no loss at all.
Whether it *should* count as a loss is a substantive question and not a formal
one; what is formal is that the two notions differ, and that they differ exactly
at the removal of options that do not change what is achievable. -/
public theorem curtailed_but_reach_unchanged :
    ¬ twoRoutes.Uncurtailed ∧ twoRoutes.ReachInvariant := by
  refine ⟨fun h ↦ ?_, fun e e' ↦ by rw [twoRoutes_reach, twoRoutes_reach]⟩
  have h2 : (2 : Fin 3) ∈ twoRoutes.available false := by
    rw [← h true false]; simp [twoRoutes]
  simp [twoRoutes] at h2

/-! ## Every boundary lemma, applied

`AISafetyAtlas.Sovereignty.Boundary` proves eighteen results that nothing
instantiated. Each is applied below on `splitGame` and `twoRoutes`. Where the
only honest instance is degenerate the docstring says so.
-/

/-- Both coordinates are `Bool`, so every strategy set is inhabited; several of
the lemmas below ask for that. -/
public instance : ∀ i : Fin 2, Nonempty (splitGame.strategy i) :=
  fun _ => ⟨(false : Bool)⟩

/-- **`0` can set its own coordinate either way.** This is what makes `{0}`
dictate the boundary rather than merely preserve it, and it is the premise pair
`hasPowerOver_of_dictates_two` and `not_sovereign_of_dictates_two` both take. -/
public theorem inside_forces (b : Bool) :
    Forces splitGame {0} (inside ⁻¹' {b}) :=
  ⟨fun _ => b, fun _ hs => hs ⟨0, rfl⟩⟩

/-- Dictating two different values of a view is power over anyone outside, and
is incompatible with their sovereignty over the same view. -/
public theorem boundary_dictates_two :
    HasPowerOver splitGame {0} {1} (inside ⁻¹' {true}) ∧
      ¬ Sovereign splitGame {1} inside :=
  have hCD : Disjoint ({0} : Set (Fin 2)) {1} := by
    rw [Set.disjoint_left]; rintro i hi hi'; simp at hi hi'; omega
  ⟨hasPowerOver_of_dictates_two hCD (by decide) (inside_forces true) (inside_forces false),
    not_sovereign_of_dictates_two hCD (by decide) (inside_forces true)
      (inside_forces false)⟩

/-- Sovereignty is preserved by post-composing the view, widening the coalition,
and reading it as a dictation. -/
public theorem boundary_sovereign_readings :
    Sovereign splitGame {0} (not ∘ inside) ∧
      Sovereign splitGame (Set.univ : Set (Fin 2)) inside ∧
      Dictates splitGame {0} inside :=
  ⟨Sovereign.comp splitGame_sovereign_inside not,
    Sovereign.mono (Set.subset_univ _) splitGame_sovereign_inside,
    Sovereign.dictates splitGame_sovereign_inside⟩

/-- A sovereign forces the view it in fact produced, whatever the outsider does. -/
public theorem boundary_forces_own_view :
    Forces splitGame {0}
      (inside ⁻¹' {inside (splitGame.outcome (fun _ => false))}) :=
  Sovereign.forces_own_view splitGame_sovereign_inside (fun _ => false)

/-- The environment-indexed form, at the trivial environment and then weakened. -/
public theorem boundary_sovereignEnv :
    SovereignEnv splitGame {0} (fun _ => True) inside ∧
      SovereignEnv splitGame {0} (fun _ => False) inside ∧
      Sovereign splitGame {0} inside :=
  have h := sovereignEnv_true_iff.mpr splitGame_sovereign_inside
  ⟨Sovereign.sovereignEnv splitGame_sovereign_inside (fun _ => True),
    SovereignEnv.mono_env (fun _ hs => hs.elim) h,
    sovereignEnv_true_iff.mp h⟩

/-- The two extremes: a constant view is sovereign to everyone, and everyone
together is sovereign over anything. The empty coalition is sovereign over a
view exactly when that view is constant on outcomes, which the constant view
satisfies. -/
public theorem boundary_extremes :
    Sovereign splitGame {0} (fun _ => true) ∧
      Sovereign splitGame (Set.univ : Set (Fin 2)) inside ∧
      Sovereign splitGame (∅ : Set (Fin 2)) (fun _ => true) :=
  ⟨Sovereignty.sovereign_const {0} true, sovereign_univ inside,
    (sovereign_empty_iff _).mpr (fun _ _ => rfl)⟩

/-- Sovereignty over a view is exactly factoring through the coalition's own
strategies. -/
public theorem boundary_factors :
    ∃ f : (∀ i : ({0} : Set (Fin 2)), splitGame.strategy i) → Bool,
      ∀ s : ∀ i, splitGame.strategy i,
        inside (splitGame.outcome s) = f (fun i : ({0} : Set (Fin 2)) => s i) :=
  (sovereign_iff_factors {0} inside).mp splitGame_sovereign_inside

/-- **Degenerate by necessity.** `outsider_forces_trivially` and
`eq_of_dictate_disjoint` both take a coalition disjoint from the sovereign's
that forces a view-preimage. In `splitGame` the only view `{1}` forces is a
constant one, so these are instantiated at the constant view -- which is the
content of the lemmas, not a shortcut: a disjoint coalition can only pin a view
the sovereign was going to produce anyway. -/
public theorem boundary_outsider (s : ∀ i, splitGame.strategy i) :
    inside (splitGame.outcome s) ∈ (Set.univ : Set Bool) ∧
      (() : Unit) = () :=
  have hCD : Disjoint ({1} : Set (Fin 2)) {0} := by
    rw [Set.disjoint_left]; rintro i hi hi'; simp at hi hi'; omega
  have hU : Forces splitGame {1} (inside ⁻¹' (Set.univ : Set Bool)) := by
    rw [Set.preimage_univ]; exact Sovereignty.forces_univ (G := splitGame) {1}
  have hpt : ∀ C : Set (Fin 2),
      Forces splitGame C ((fun _ : Bool × Bool => ()) ⁻¹' {()}) := by
    intro C
    have hset : ((fun _ : Bool × Bool => ()) ⁻¹' {()}) = Set.univ := by ext x; simp
    rw [hset]; exact Sovereignty.forces_univ (G := splitGame) C
  ⟨Sovereign.outsider_forces_trivially splitGame_sovereign_inside hCD hU s,
    eq_of_dictate_disjoint (G := splitGame) (view := fun _ => ()) hCD
      (hpt {1}) (hpt {0})⟩

/-- A curtailment with every action always available is uncurtailed, so its
reach cannot move; and shrinking what is available can only shrink the reach. -/
@[expose] public def unrestricted : Curtailment Bool (Fin 3) Bool where
  available := fun _ => Set.univ
  outcome := fun a => if a = 0 then true else false

public theorem boundary_curtailment :
    unrestricted.ReachInvariant ∧
      twoRoutes.reach false ⊆ twoRoutes.reach true :=
  ⟨Curtailment.reachInvariant_of_uncurtailed (fun _ _ => rfl),
    Curtailment.reach_mono twoRoutes (by simp [twoRoutes])⟩

/-! ## Actual power, and the dictation it forces

`ActualPower` is strictly more than `α`-forcing: clause (1) is the guarantee,
and clause (2) says the coalition's commitment leaves **no slack** -- every
outcome in the target is actually attained. `splitGame_dictates_outside` above
proves dictation directly; this derives the same conclusion through the stronger
notion, which is the route `ActualPower.dictates` exists to license. -/

/-- **`1` has actual power over its own coordinate being `true`.** Committing to
`true` guarantees it, and every outcome with that coordinate is still reachable,
so the commitment constrains exactly the coordinate it names and nothing else. -/
public theorem splitGame_actualPower_outside :
    ActualPower splitGame {1} (Prod.snd ⁻¹' ({true} : Set Bool)) := by
  refine ⟨fun _ ↦ true, fun s hs ↦ ?_, fun x hx ↦ ?_⟩
  · show (splitGame.outcome s).2 ∈ ({true} : Set Bool)
    show (s 0, s 1).2 ∈ ({true} : Set Bool)
    rw [hs ⟨1, rfl⟩]
    exact rfl
  · have hx2 : x.2 = true := hx
    refine ⟨fun i ↦ if i = 0 then x.1 else true, fun i ↦ ?_, ?_⟩
    · obtain ⟨i, hi⟩ := i
      obtain rfl : i = 1 := hi
      show (if (1 : Fin 2) = 0 then x.1 else true) = true
      simp
    · show ((if (0 : Fin 2) = 0 then x.1 else true),
            (if (1 : Fin 2) = 0 then x.1 else true)) = x
      simp [← hx2]

/-- **And actual power over a view value is dictation of that view.** The same
conclusion `splitGame_dictates_outside` reaches directly, reached instead from
the stronger hypothesis -- so the two routes agree where both apply. -/
public theorem splitGame_dictates_outside_via_actualPower :
    Dictates splitGame {1} (Prod.snd : Bool × Bool → Bool) :=
  ActualPower.dictates splitGame_actualPower_outside

end AISafetyAtlas.Examples.Sovereignty.Boundary
