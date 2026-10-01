module

public import AISafetyAtlas.Sovereignty.Auditability
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Tactic.FinCases

/-!
# A detector that cannot tell, and a channel that need not

Four contexts, `Fin 4`, read as a pair of bits: whether the write was
authorized, and which of two documents it touched.

`chan` shows only the document. `authorized` is the label a detector would have
to certify. `not_auditable` says it cannot: contexts `0` and `1` differ in
authorization and agree on everything the channel shows. That is `C9`
negatively, and `no_recovery` is `A3` at the same collision.

`safeAction` is what a controller must do, and it is deliberately *not* a
function of the label: in both document-0 contexts the action `0` is
acceptable, and in both document-1 contexts the action `1` is. So
`uniform_exists` gives a controller that works on the same channel that defeats
the detector -- print's point that full state observation is unnecessary when
the merged contexts agree on an action.

`mon` carries a monitor that would separate the collision, and
`selection_separates` is `C10` saying so; `empty_not_separates` is the same
criterion refusing the empty selection.

`leaky` is `C3` failing: a transition that reads the unendorsed channel.
-/

namespace AISafetyAtlas.Examples.Sovereignty.Auditability

open AISafetyAtlas.Sovereignty

/-- The channel shows the document and hides the authorization. -/
@[expose] public def chan : Fin 4 → Fin 2
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1

/-- The label a detector would have to certify: was the write authorized. -/
@[expose] public def authorized : Fin 4 → Bool
  | 0 => true
  | 1 => false
  | 2 => true
  | 3 => false

/-- **`C9` negatively: no detector on this channel certifies authorization.**
Contexts `0` and `1` agree on everything shown and disagree on the label. -/
public theorem not_auditable :
    ¬ ∀ θ θ' : Fin 4, chan θ = chan θ' → authorized θ = authorized θ' := by
  intro h
  exact Bool.noConfusion (h 0 1 rfl)

/-- **`A3` at the same collision: no deterministic recovery either.** -/
public theorem no_recovery : ¬ ∃ d : Fin 2 → Bool, authorized = d ∘ chan :=
  not_exists_recovery_of_collision chan authorized (θ := 0) (θ' := 1) rfl
    (by decide)

/-- The actions that are acceptable in each context: act on the document the
context concerns, whatever its authorization. -/
@[expose] public def safeAction : Fin 4 → Set (Fin 2)
  | 0 => {0}
  | 1 => {0}
  | 2 => {1}
  | 3 => {1}

/-- **`C6` positively, on the very channel that defeats the detector.** Every
fibre of `chan` has an action good in both of its contexts, so a uniform
controller exists. Certifying authorship and acting safely are different
demands on the same observation. -/
public theorem uniform_exists :
    ∃ d : Fin 2 → Fin 2, UniformDecision chan safeAction d := by
  refine ⟨id, fun θ => ?_⟩
  fin_cases θ <;> exact rfl

/-- **What a uniform controller amounts to, read off the same channel.** The
characterisation turns the existence of a controller into a condition on the
channel's fibres: every observation must leave some action good in *all* the
contexts it cannot tell apart. Run here in the direction that consumes
`uniform_exists`, so the condition is exhibited rather than assumed. -/
public theorem chan_fibres_have_a_common_action :
    ∀ θ₀ : Fin 4, (⋂ θ ∈ {θ : Fin 4 | chan θ = chan θ₀}, safeAction θ).Nonempty :=
  (exists_uniformDecision_iff chan safeAction).mp uniform_exists

/-! ## `C10`: a monitor that would have separated the pair -/

/-- Two monitors: one reads the document, one reads the authorization. -/
@[expose] public def mon : Bool → Fin 4 → Fin 2
  | false => chan
  | true => fun θ => if authorized θ then 1 else 0

/-- **Buying the authorization monitor separates every differently labelled
pair**, so by `C10` that selection audits the label. -/
public theorem selection_separates :
    ∀ θ θ' : Fin 4, authorized θ ≠ authorized θ' →
      ∃ j ∈ ({true} : Set Bool), mon j θ ≠ mon j θ' := by
  decide

/-- **And the empty selection separates nothing**, so by the same criterion it
audits nothing. -/
public theorem empty_not_separates :
    ¬ ∀ θ θ' : Fin 4, authorized θ ≠ authorized θ' →
      ∃ j ∈ (∅ : Set Bool), mon j θ ≠ mon j θ' := by
  intro h
  obtain ⟨j, hj, _⟩ := h 0 1 (by decide)
  exact hj

/-! ## `C12`: two monitors that each see nothing and together see everything -/

/-- Four joint states of two bits, read as the pair `(θ.val / 2, θ.val % 2)`.
The hazard is the parity: the state is safe when the bits agree. -/
@[expose] public def bit : Bool → Fin 4 → Bool
  | false => fun θ => θ = 2 ∨ θ = 3
  | true => fun θ => θ = 1 ∨ θ = 3

/-- The label: the two bits disagree. -/
@[expose] public def hazard : Fin 4 → Bool
  | 0 => false
  | 1 => true
  | 2 => true
  | 3 => false

/-- **Neither monitor alone separates a hazardous state from a safe one.** Each
coordinate takes both values in both classes, so by `C10` a selection holding
only one of them audits nothing. -/
public theorem single_monitor_not_separates (j₀ : Bool) :
    ¬ ∀ θ θ' : Fin 4, hazard θ ≠ hazard θ' →
      ∃ j ∈ ({j₀} : Set Bool), bit j θ ≠ bit j θ' := by
  revert j₀
  decide

/-- **Together they separate every differently labelled pair**, so by `C10` the
pair audits the hazard exactly. Equality of each monitor's own view is not
equality of the joint information state. -/
public theorem both_monitors_separate :
    ∀ θ θ' : Fin 4, hazard θ ≠ hazard θ' →
      ∃ j ∈ (Set.univ : Set Bool), bit j θ ≠ bit j θ' := by
  decide

/-! ## `C3`: a transition that reads the unendorsed channel -/

/-- A protected transition that copies the unendorsed input. -/
@[expose] public def leaky : Unit → Unit → Bool → Bool :=
  fun _ _ u => u

/-- **So it does not factor through the endorsed interface**, by `C3`. -/
public theorem leaky_not_factors :
    ¬ ∃ F' : Unit → Unit → Bool, ∀ e j u, leaky e j u = F' e j := by
  rw [← residualFree_iff_factors]
  intro h
  exact Bool.noConfusion (h () () true false)

/-! ## `C11`: the reduction is not vacuous in either direction -/

/-- A universe of two elements and two sets, `{0}` and `{1}`. -/
@[expose] public def twoSets : Bool → Set (Fin 2)
  | false => {0}
  | true => {1}

/-- **Both sets together cover**, so buying both audits the instance. -/
public theorem twoSets_cover_univ :
    ∀ θ θ' : Option (Fin 2),
      selectionObs (coverMonitor twoSets) (Set.univ : Set Bool) θ =
          selectionObs (coverMonitor twoSets) (Set.univ : Set Bool) θ' →
        coverLabel θ = coverLabel θ' := by
  rw [← cover_iff_selectionAuditable]
  intro u
  fin_cases u
  · exact ⟨false, Set.mem_univ _, rfl⟩
  · exact ⟨true, Set.mem_univ _, rfl⟩

/-- **One set alone does not**, so a strictly smaller purchase fails -- which is
what makes the budgeted question nontrivial rather than always answerable by
buying nothing. -/
public theorem twoSets_one_not_cover :
    ¬ ∀ θ θ' : Option (Fin 2),
        selectionObs (coverMonitor twoSets) ({false} : Set Bool) θ =
            selectionObs (coverMonitor twoSets) ({false} : Set Bool) θ' →
          coverLabel θ = coverLabel θ' := by
  rw [← cover_iff_selectionAuditable]
  intro h
  obtain ⟨j, hj, hmem⟩ := h 1
  rw [Set.mem_singleton_iff] at hj
  subst hj
  exact absurd (Set.mem_singleton_iff.mp hmem) (by decide)

/-! ## `C10` monotone: a monitor already bought is never wasted -/

/-- **The authorization monitor alone audits the label**, which is
`selection_separates` read through the observational criterion. -/
public theorem single_monitor_audits :
    ∀ θ θ' : Fin 4,
      selectionObs mon ({true} : Set Bool) θ = selectionObs mon ({true} : Set Bool) θ' →
        authorized θ = authorized θ' :=
  (selectionAuditable_iff_separates mon authorized {true}).mpr selection_separates

/-- **And buying the document monitor as well cannot take that away.** The
selection grows from `{true}` to both monitors and the label stays auditable.
That is `selectionAuditable_mono`, and it is why an auditability argument never
has to be redone when a programme adds instrumentation -- only when it removes
some. -/
public theorem more_monitors_still_audit :
    ∀ θ θ' : Fin 4,
      selectionObs mon (Set.univ : Set Bool) θ =
          selectionObs mon (Set.univ : Set Bool) θ' →
        authorized θ = authorized θ' :=
  selectionAuditable_mono (Set.subset_univ _) single_monitor_audits

/-! ## `C9` positively: the observation that does yield a detector -/

/-- **A channel that determines the label hands back an explicit detector.**

`chan` does not, which is `not_auditable`. The authorization monitor does, and
`auditable_iff_exists_detector` is what converts the agreement condition into
the function -- so the same criterion that refuses a detector on one channel
produces one on another. -/
public theorem authorization_monitor_has_detector :
    ∃ d : Fin 2 → Bool, authorized = d ∘ mon true :=
  (auditable_iff_exists_detector (mon true) authorized).mp (by decide)

end AISafetyAtlas.Examples.Sovereignty.Auditability
