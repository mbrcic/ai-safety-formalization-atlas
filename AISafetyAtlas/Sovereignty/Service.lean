module

public import AISafetyAtlas.Sovereignty.Mandate

/-!
# Service, and why retention alone does not ask for it

A delegate that refuses every input keeps every protected guarantee that the
still point already satisfies, and delivers nothing. This module states that,
and states exactly when it can happen.

## The two notions, and where they come from

The source is an unpublished internal proposal, *A Formal System of Power,
Sovereignty, and Cognitive Sovereignty*, pinned in
`docs/provenance/formal-power-proposal-triage.md`. Two of its definitions are
already this repository's, under other names:

* its §5.4 relative retention, `Retains(G₀, G₁) ⟺ E(G₀) ∩ P ⊆ E(G₁)`, is
  `RetainsFamily` with the protected family in the role of `P`;
* its §5.3 demandwise sovereignty at the sure reading,
  `∀ q ∈ Q, ∃ σ, ∀ τ, O(σ, τ) ⊆ Φ_q`, is `Demandwise` below, which is
  `Forces` at every demand in a catalogue.

Its result D8 says the first does not imply the second. `Inert` is the object
that separates them: a game form in which nothing anyone does changes the
outcome.

## What is proved here, and what is not

`inert_retainsFamily_iff` is the exact characterization, and it is the reason
the separation is not an accident of one example: an inert delegate retains a
protected family **iff** the still point lies in every protected set the
baseline actually delivered. Safety sets contain the still point by
construction -- "no unauthorized change" is satisfied by changing nothing --
so retention of a safety-only family is automatic.

`not_demandwise_of_inert` is the other half, and
`retainsFamily_and_not_demandwise` is D8 itself.

`separating_not_demandwise_of_inert` is the catalogue-side repair, and it is
the proposal's §5.2 rather than its §6: a catalogue is *separating* when no
single outcome meets all of it, and a separating catalogue rules out **every**
refusing delegate at once, not only the one pinned to a particular point. That
is strictly more than D8 needs and is the form a specification can be checked
against.

**Scope.** D8 is stated in the proposal's §6, a dynamic safety game with a
controlled-invariant kernel computed by a controllable predecessor operator.
Nothing here has a transition relation, a trajectory or a time index. The
rendering is one-shot: narrower than print in that it has no dynamics, wider in
that it characterizes an arbitrary protected family rather than exhibiting one
controller. It is not offered as coverage of D8.

**Non-vacuity.** Every hypothesis below is inhabited, and the witnesses are in
`AISafetyAtlas.Examples.Sovereignty.Service`: a separating catalogue, a game
form that is demandwise sovereign at it, and an inert game form that is not.
-/

namespace AISafetyAtlas.Sovereignty

universe u v w

variable {N : Type u} {X : Type v}

/-! ## The refusing delegate -/

/--
A game form is **inert** at `x₀` when nothing anyone does changes the outcome.

This is the controller that refuses every input, with the refusal pushed all the
way into the game form: the strategy spaces may be as rich as one likes and the
outcome map ignores them.
-/
@[expose] public def Inert (G : GameForm.{u, v, w} N X) (x₀ : X) : Prop :=
  ∀ s : ∀ i, G.strategy i, G.outcome s = x₀

/-- **In an inert game a coalition forces exactly the sets containing the still
point** -- every coalition, including the empty one. Power is not distributed in
such a game; it is absent, and what looks like universal effectivity is the
outcome having been settled in advance. -/
public theorem Inert.forces_iff {G : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G.strategy i)] {x₀ : X} (h : Inert G x₀) {C : Set N}
    {A : Set X} : Forces G C A ↔ x₀ ∈ A := by
  classical
  constructor
  · rintro ⟨sC, hsC⟩
    refine (h _) ▸ hsC (fun i => if hi : i ∈ C then sC ⟨i, hi⟩
      else Classical.arbitrary _) ?_
    rintro ⟨i, hi⟩
    simp [hi]
  · exact fun hx => ⟨fun _ => Classical.arbitrary _, fun s _ => (h s) ▸ hx⟩

/-- The effectivity family of an inert game, at every coalition. -/
public theorem Inert.effectivity_eq {G : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G.strategy i)] {x₀ : X} (h : Inert G x₀) (C : Set N) :
    effectivity G C = {A : Set X | x₀ ∈ A} :=
  Set.ext fun _ => h.forces_iff

/-! ## Demandwise sovereignty -/

/--
**Demandwise sovereignty** at the sure reading: every demand in the catalogue
`𝒬` is forceable by `C`.

The proposal's §5.3 boxed definition replaces the probability bound by set
inclusion for the sure case, and that inclusion is `Forces`. Its accompanying
finite model computes `all(self.can(q) for q in protected)`, which is this
predicate.

`𝒬` is an input. Nothing in a game form supplies it, for the same reason the
mandate family of `RetainsFamily` is an input.
-/
@[expose] public def Demandwise (G : GameForm.{u, v, w} N X) (C : Set N)
    (𝒬 : Set (Set X)) : Prop :=
  ∀ Φ ∈ 𝒬, Forces G C Φ

/-- Demandwise sovereignty is exactly containment of the catalogue in the
effectivity family. -/
public theorem demandwise_iff_subset {G : GameForm.{u, v, w} N X} {C : Set N}
    {𝒬 : Set (Set X)} : Demandwise G C 𝒬 ↔ 𝒬 ⊆ effectivity G C :=
  Iff.rfl

/-- It is antitone in the catalogue: fewer demands are easier to meet. -/
public theorem Demandwise.mono {G : GameForm.{u, v, w} N X} {C : Set N}
    {𝒬 ℛ : Set (Set X)} (h : Demandwise G C ℛ) (h𝒬 : 𝒬 ⊆ ℛ) :
    Demandwise G C 𝒬 :=
  fun Φ hΦ => h Φ (h𝒬 hΦ)

/-- **An inert delegate meets exactly the demands the still point already
satisfies.** -/
public theorem Inert.demandwise_iff {G : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G.strategy i)] {x₀ : X} (h : Inert G x₀) {C : Set N}
    {𝒬 : Set (Set X)} : Demandwise G C 𝒬 ↔ ∀ Φ ∈ 𝒬, x₀ ∈ Φ :=
  forall₂_congr fun _ _ => h.forces_iff

/-- **One demand the still point misses refutes demandwise sovereignty.** This
is the second half of D8: a refusing controller fails every demand that asks for
a change. -/
public theorem not_demandwise_of_inert {G : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G.strategy i)] {x₀ : X} (h : Inert G x₀) {C : Set N}
    {𝒬 : Set (Set X)} {Φ : Set X} (hΦ : Φ ∈ 𝒬) (hx : x₀ ∉ Φ) :
    ¬ Demandwise G C 𝒬 :=
  fun hd => hx (h.demandwise_iff.mp hd Φ hΦ)

/-! ## Retention by a delegate that does nothing -/

/--
**Exactly when a refusing delegate retains a protected family.**

The right-hand side is the proposal's `E(G₀) ∩ P`: the protected sets the
baseline actually delivered. An inert delegate retains them iff its still point
lies in all of them.

Read the other way, this is a test on the protected family rather than on the
delegate. A family whose members have a common outcome is retainable by a game
form that does nothing, so retention of that family is no evidence about the
delegate at all.
-/
public theorem inert_retainsFamily_iff {G₀ G₁ : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G₁.strategy i)] {x₀ : X} (h : Inert G₁ x₀) {C₀ C₁ : Set N}
    {𝒜 : Set (Set X)} :
    RetainsFamily G₀ G₁ C₀ C₁ 𝒜 ↔ x₀ ∈ ⋂₀ (𝒜 ∩ effectivity G₀ C₀) := by
  constructor
  · intro hr
    rw [Set.mem_sInter]
    rintro A ⟨hA𝒜, hA₀⟩
    exact h.forces_iff.mp (hr A hA𝒜 hA₀)
  · intro hx A hA𝒜 hA₀
    exact h.forces_iff.mpr (Set.mem_sInter.mp hx A ⟨hA𝒜, hA₀⟩)

/-- **Safety-shaped protection is retained by doing nothing.** Every protected
set that the still point already satisfies survives a delegate that refuses
everything -- which is the first half of D8, and the reason "no unauthorized
change" is not on its own a retention result. -/
public theorem retainsFamily_of_inert {G₀ G₁ : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G₁.strategy i)] {x₀ : X} (h : Inert G₁ x₀) {C₀ C₁ : Set N}
    {𝒜 : Set (Set X)} (h𝒜 : ∀ A ∈ 𝒜, x₀ ∈ A) :
    RetainsFamily G₀ G₁ C₀ C₁ 𝒜 :=
  fun A hA𝒜 _hA₀ => h.forces_iff.mpr (h𝒜 A hA𝒜)

/--
**D8: safety without service is vacuous sovereignty.**

One delegate, at once: it retains every protected set that the still point
satisfies, and it fails demandwise sovereignty at any catalogue containing a
demand the still point misses. So retention does not imply demandwise
sovereignty, and the two must be asked for separately.
-/
public theorem retainsFamily_and_not_demandwise {G₀ G₁ : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G₁.strategy i)] {x₀ : X} (h : Inert G₁ x₀) {C₀ C₁ : Set N}
    {𝒜 𝒬 : Set (Set X)} (h𝒜 : ∀ A ∈ 𝒜, x₀ ∈ A) {Φ : Set X} (hΦ : Φ ∈ 𝒬)
    (hx : x₀ ∉ Φ) :
    RetainsFamily G₀ G₁ C₀ C₁ 𝒜 ∧ ¬ Demandwise G₁ C₁ 𝒬 :=
  ⟨retainsFamily_of_inert h h𝒜, not_demandwise_of_inert h hΦ hx⟩

/-! ## The catalogue-side repair

D8 exhibits a controller and shows a catalogue it fails. The proposal's §5.2
asks for the opposite quantifier -- a catalogue that no refusing controller can
pass -- as a well-formedness obligation on the specification: *"a claim of
substantive choice should identify distinguishable alternative requests, not
only the ability to do nothing."*
-/

/--
A demand catalogue is **separating** when no single outcome meets all of it.

This is the proposal's §5.2 nonvacuity condition. It is strictly stronger than
what D8 needs: D8 fixes a still point and finds a demand missing it, while this
rules out every still point at once.
-/
@[expose] public def Separating (𝒬 : Set (Set X)) : Prop :=
  ⋂₀ 𝒬 = (∅ : Set X)

/-- **No refusing delegate passes a separating catalogue.** The quantifier is
over the delegate, not inside it: this holds for every inert game form and every
still point, so it is a property of the specification. -/
public theorem separating_not_demandwise_of_inert {G : GameForm.{u, v, w} N X}
    [∀ i, Nonempty (G.strategy i)] {x₀ : X} (h : Inert G x₀) {C : Set N}
    {𝒬 : Set (Set X)} (hsep : Separating 𝒬) : ¬ Demandwise G C 𝒬 := by
  intro hd
  have : x₀ ∈ ⋂₀ 𝒬 := Set.mem_sInter.mpr (h.demandwise_iff.mp hd)
  rw [hsep] at this
  exact this

/-- A separating catalogue is nonempty, since the empty intersection is
everything -- so the condition subsumes the proposal's other stated minimum. -/
public theorem Separating.nonempty [Nonempty X] {𝒬 : Set (Set X)}
    (h : Separating 𝒬) : 𝒬.Nonempty := by
  rcases Set.eq_empty_or_nonempty 𝒬 with rfl | h𝒬
  · have h' : (Set.univ : Set X) = ∅ := by rw [← Set.sInter_empty]; exact h
    exact absurd (Set.univ_eq_empty_iff.mp h') (not_isEmpty_of_nonempty X)
  · exact h𝒬

/-- **Separating survives adding demands**, which is why it is checkable on a
sub-catalogue and then inherited. -/
public theorem Separating.mono {𝒬 ℛ : Set (Set X)} (h : Separating 𝒬)
    (h𝒬 : 𝒬 ⊆ ℛ) : Separating ℛ :=
  Set.eq_empty_of_subset_empty (h ▸ Set.sInter_subset_sInter h𝒬)

/-! ## The pinned game form is inert -/

/-- Everyone has a strategy in the pinned game form, which is what the
effectivity lemmas above require of a delegate. -/
public instance pinnedForm_nonempty (x₀ : X) (i : Bool) :
    Nonempty ((pinnedForm x₀).strategy i) := ⟨PUnit.unit⟩

/-- `pinnedForm` is the smallest inert witness: two agents, one strategy each,
one outcome. -/
public theorem inert_pinnedForm (x₀ : X) : Inert (pinnedForm x₀) x₀ :=
  fun _ => rfl

/--
**A protected family is vacuously retainable exactly when it has a common
point after intersecting with the baseline.**

The existential is over the still point, so this is the full statement of when
retention carries no information: some refusing delegate passes iff the
protected sets the baseline delivered all share an outcome.
-/
public theorem exists_pinned_retainsFamily_iff {G₀ : GameForm.{0, v, v} Bool X}
    {C₀ C₁ : Set Bool} {𝒜 : Set (Set X)} :
    (∃ x₀ : X, RetainsFamily G₀ (pinnedForm x₀) C₀ C₁ 𝒜) ↔
      (⋂₀ (𝒜 ∩ effectivity G₀ C₀)).Nonempty := by
  constructor
  · rintro ⟨x₀, hr⟩
    exact ⟨x₀, (inert_retainsFamily_iff (inert_pinnedForm x₀)).mp hr⟩
  · rintro ⟨x₀, hx⟩
    exact ⟨x₀, (inert_retainsFamily_iff (inert_pinnedForm x₀)).mpr hx⟩

end AISafetyAtlas.Sovereignty
