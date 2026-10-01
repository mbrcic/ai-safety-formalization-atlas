module

public import AISafetyAtlas.Knowledge.UniformAction

/-!
# Four small worlds for the uniform decision boundary

Everything here is `Fin 2` or `Fin 3` with a blind or an exact observation, so
that each claim is a finite check.

* `blindObs` with `exactDemand` is the obstruction: two states an observation
  cannot separate, each demanding its own action. No rule works, and
  `blindConflict` exhibits the pair.
* `sightedObs` is the first repair applied to the same acceptability: keep the
  states and the demands, sharpen the observation, and a rule appears.
* `fallbackDemand` is the second repair: keep the blind observation, add one
  action acceptable everywhere.
* `tripleDemand` is the counterexample that keeps the pairwise certificate
  honest. Three states on one fibre, each rejecting only itself. Every *pair*
  of them shares an action, so **no `ActionConflict` exists**; the fibre still
  has no common action, so no rule exists either. This is why the module's
  necessary certificate is an empty fibre and not a pair, unlike the `Knowable`
  kernel.
-/

namespace AISafetyAtlas.Examples.Knowledge.UniformAction

open AISafetyAtlas.Knowledge

/-! ## The obstruction: two demands, one observation -/

/-- The observation that sees nothing. -/
@[expose] public def blindObs : Fin 2 → Unit := fun _ => ()

/-- State `ω` accepts action `ω` and nothing else. Written in the kernel's
orientation (`property ω = a`) so that `knowable_iff_uniformlyActionable`
applies to it definitionally. -/
@[expose] public def exactDemand (ω : Fin 2) (a : Fin 2) : Prop := ω = a

/-- The two states are indistinguishable and share no acceptable action. -/
@[expose] public def blindConflict : ActionConflict blindObs exactDemand where
  left := 0
  right := 1
  sameObservation := rfl
  noSharedAction a := by
    show ¬ ((0 : Fin 2) = a ∧ (1 : Fin 2) = a)
    revert a
    decide

/-- **GE6.** No observation-based rule serves both states. -/
public theorem not_uniformlyActionable_blind :
    ¬ UniformlyActionable blindObs exactDemand :=
  not_uniformlyActionable_of_conflict blindConflict

/-! ## Repair one: sharpen the observation -/

/-- The same two states, now told apart. -/
@[expose] public def sightedObs : Fin 2 → Fin 2 := id

/-- **Adding discriminating information closes the gap**, with the demands
unchanged. -/
public theorem uniformlyActionable_sighted :
    UniformlyActionable sightedObs exactDemand :=
  ⟨id, fun _ => rfl⟩

/-! ## Repair two: supply a common action -/

/-- Each state still accepts its own index, and both accept the third action. -/
@[expose] public def fallbackDemand (ω : Fin 2) (a : Fin 3) : Prop :=
  a = ω.castSucc ∨ a = 2

/-- **A universally acceptable action closes the gap** with the observation
still blind. The rule is constant, so it reads nothing at all. -/
public theorem uniformlyActionable_fallback :
    UniformlyActionable blindObs fallbackDemand :=
  uniformlyActionable_of_universal (a := 2) fun _ => Or.inr rfl

/-- And the repair is not vacuous: on the original action type the same blind
observation has no rule. -/
public theorem fallback_repairs_a_real_failure :
    ¬ UniformlyActionable blindObs exactDemand ∧
      UniformlyActionable blindObs fallbackDemand :=
  ⟨not_uniformlyActionable_blind, uniformlyActionable_fallback⟩

/-! ## The general statements, run at these three models -/

/-- **The criterion as an intersection.** A uniform rule exists exactly when
every fibre's acceptable sets meet, and at `sightedObs` the fibres are
singletons, so the intersection is the state's own set. -/
public theorem sighted_iInter_nonempty :
    ∀ i ∈ Set.range sightedObs,
      (⋂ ω ∈ {ω | sightedObs ω = i}, {a | exactDemand ω a}).Nonempty :=
  (uniformlyActionable_iff_iInter_nonempty sightedObs exactDemand).mp
    uniformlyActionable_sighted

/-- **An injective observation always suffices**, provided every state accepts
something. `sightedObs` is the identity, so this is a second and independent
route to `uniformlyActionable_sighted` — the first exhibits the rule, this one
derives its existence from the shape of the observation. -/
public theorem uniformlyActionable_sighted_by_injectivity :
    UniformlyActionable sightedObs exactDemand :=
  uniformlyActionable_of_injective Function.injective_id fun ω => ⟨ω, rfl⟩

/-- **A uniform rule agrees pairwise.** The converse fails — that is what the
triple below is for — so this direction is the one worth naming. -/
public theorem sighted_pairwiseAgreeable : PairwiseAgreeable sightedObs exactDemand :=
  PairwiseAgreeable.of_uniformlyActionable uniformlyActionable_sighted

/-! ## The only two repairs there are -/

/-- Seeing the state tells you what the blind observation would have said,
trivially: it says the same thing everywhere. -/
public theorem sighted_determines_blind : Determines sightedObs blindObs :=
  ⟨fun _ => (), fun _ => rfl⟩

/-- **Repair one as the general lemma.** Sharpening the observation cannot lose
a rule, so the blind fallback rule survives being given more information. The
module says this is one of exactly two repairs; here it is at a witness. -/
public theorem sighted_fallback_still_actionable :
    UniformlyActionable sightedObs fallbackDemand :=
  UniformlyActionable.mono sighted_determines_blind uniformlyActionable_fallback

/-- **Repair two as the general lemma.** Widening what counts as acceptable
cannot lose a rule either. Widened here to the demand that accepts anything,
which is the extreme case and makes the direction unmistakable. -/
public theorem sighted_widened_still_actionable :
    UniformlyActionable sightedObs (fun (_ : Fin 2) (_ : Fin 2) => True) :=
  UniformlyActionable.mono_good uniformlyActionable_sighted fun _ _ _ => trivial

/-! ## Pairwise compatibility is not enough -/

/-- Three states, none of them separated. -/
@[expose] public def tripleObs : Fin 3 → Unit := fun _ => ()

/-- State `ω` accepts every action except `ω`. The three acceptable sets are
`{1,2}`, `{0,2}` and `{0,1}`: pairwise intersecting, jointly empty. -/
@[expose] public def tripleDemand (ω : Fin 3) (a : Fin 3) : Prop := a ≠ ω

/--
**No `ActionConflict` exists here.** Any two of the three states share an
action, so the pairwise certificate cannot be produced -- whatever pair a
conflict names.
-/
public theorem no_conflict_triple (c : ActionConflict tripleObs tripleDemand) : False := by
  have h : ∀ a : Fin 3, ¬ (a ≠ c.left ∧ a ≠ c.right) := c.noSharedAction
  revert h
  generalize c.left = x
  generalize c.right = y
  revert x y
  decide

/--
**Yet no uniform rule exists.** The rule's single output is rejected by the
state that equals it.

So `not_uniformlyActionable_of_conflict` is sufficient and not necessary, and
the completeness statement of the module is
`not_uniformlyActionable_iff_exists_unservable` instead.
-/
public theorem not_uniformlyActionable_triple :
    ¬ UniformlyActionable tripleObs tripleDemand := by
  rintro ⟨rule, hrule⟩
  exact hrule (rule ()) rfl

/-- The two halves together: the pairwise certificate is strictly weaker than
the fibre certificate. -/
public theorem conflict_is_not_complete :
    (ActionConflict tripleObs tripleDemand → False) ∧
      ¬ UniformlyActionable tripleObs tripleDemand :=
  ⟨no_conflict_triple, not_uniformlyActionable_triple⟩

/--
**And the completeness statement, at the model that needed it.** The docstring
above says `not_uniformlyActionable_of_conflict` is sufficient and not
necessary, and names `not_uniformlyActionable_iff_exists_unservable` as what
replaces it — this runs that replacement. It returns the unservable state: one
whose fibre defeats *every* action, which is the form the obstruction takes when
no pair of states carries it.
-/
public theorem triple_has_an_unservable_state :
    ∃ ω, ∀ a, ∃ τ, tripleObs τ = tripleObs ω ∧ ¬ tripleDemand τ a :=
  (not_uniformlyActionable_iff_exists_unservable tripleObs tripleDemand).mp
    not_uniformlyActionable_triple

/-! ## The kernel sits inside -/

/-- `exactDemand` is the acceptability relation of the identity property, so
the failure at `blindObs` is also the kernel's: the state is not knowable from
nothing.
-/
public theorem blind_not_knowable : ¬ Knowable blindObs (id : Fin 2 → Fin 2) := by
  rw [knowable_iff_uniformlyActionable]
  exact not_uniformlyActionable_blind

/-! ## Where the pairwise certificate stops being complete -/

/--
**The three-state fibre agrees pairwise.** Any two of the three states share an
action -- the one that is neither of them.

With `not_uniformlyActionable_triple`, this is the sharpness witness for
`uniformlyActionable_of_pairwiseAgreeable_of_card_le_two`: at three actions,
pairwise agreement no longer forces a uniform rule.
-/
public theorem triple_pairwiseAgreeable : PairwiseAgreeable tripleObs tripleDemand := by
  intro ω τ _
  have h : ∀ x y : Fin 3, ∃ a : Fin 3, a ≠ x ∧ a ≠ y := by decide
  unfold tripleDemand
  exact h ω τ

/-- **The bound of two is sharp.** Three actions, pairwise agreement, no rule. -/
public theorem pairwise_not_complete_at_three :
    PairwiseAgreeable tripleObs tripleDemand ∧
      ¬ UniformlyActionable tripleObs tripleDemand :=
  ⟨triple_pairwiseAgreeable, not_uniformlyActionable_triple⟩

/--
**And at two actions the same pattern cannot arise.** The demand "anything but
my own index" over a two-element action type is uniformly actionable as soon as
it agrees pairwise -- whatever `f` is, and with no rule exhibited by hand.

This is the contrast that makes the theorem say something: identical shape of
demand, identical blind observation, three actions versus two.
-/
public theorem binary_triple_uniformlyActionable (f : Fin 3 → Fin 2)
    (h : PairwiseAgreeable tripleObs (fun ω a => a ≠ f ω)) :
    UniformlyActionable tripleObs (fun ω a => a ≠ f ω) :=
  uniformlyActionable_of_pairwiseAgreeable_of_card_le_two (by decide) h

end AISafetyAtlas.Examples.Knowledge.UniformAction
