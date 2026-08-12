module

import AISafetyAtlas.Explainability
import AISafetyAtlas.Verification.AgentBehavior
import AISafetyAtlas.Knowledge.Embedded
import AISafetyAtlas.Knowledge.Embedded.Composition
import AISafetyAtlas.Knowledge.Embedded.Finite
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Non-vacuity witnesses for published gate predicates

These anonymous compile-time examples provide concrete inhabitants for the
hypotheses used by the published Rice and attribution bridges, and for the
abstract Breuer measurement core. The regret gate is witnessed in
`Examples.WorkbenchConsumers` by `binaryCorruption.halfMaximalRegretBound`.
No public declarations are added.
-/

open Nat.Partrec (Code)
open Nat.Partrec.Code

namespace AISafetyAtlas.Examples.NonVacuity

private def zeroOnly : AISafetyAtlas.Verification.BehavioralProperty :=
  {behavior | behavior 0 = Part.some 0}

/-! A total, extensional property with one accepted and one rejected code. -/
example : AISafetyAtlas.Verification.Nontrivial zeroOnly := by
  constructor
  · refine ⟨Code.const 0, ?_⟩
    simp [AISafetyAtlas.Verification.Holds, zeroOnly]
  · refine ⟨Code.const 1, ?_⟩
    simp [AISafetyAtlas.Verification.Holds, zeroOnly]

example : AISafetyAtlas.Verification.AgentBehavior.SpecNontrivial zeroOnly := by
  constructor
  · refine ⟨Code.const 0, ?_⟩
    simp [AISafetyAtlas.Verification.Holds, zeroOnly]
  · refine ⟨Code.const 1, ?_⟩
    simp [AISafetyAtlas.Verification.Holds, zeroOnly]

private def twoFeatures : AISafetyAtlas.Explainability.FeatureIndex where
  P := 2
  L := 1
  hP := by decide
  groupOf := fun _ => 0

private def oppositeAttribution : Fin 2 → Bool → ℝ :=
  fun feature model =>
    if feature.val = 0 then
      if model then 1 else 0
    else
      if model then 0 else 1

/-! Two features in one group exchange order across two concrete models. -/
example : AISafetyAtlas.Explainability.RashomonProperty
    twoFeatures Bool oppositeAttribution := by
  intro ℓ j k hj hk hjk
  dsimp [twoFeatures] at ℓ j k hj hk hjk ⊢
  fin_cases ℓ
  all_goals fin_cases j
  all_goals fin_cases k
  · exact (hjk rfl).elim
  · refine ⟨true, false, ?_, ?_⟩ <;> norm_num [oppositeAttribution]
  · refine ⟨false, true, ?_, ?_⟩ <;> norm_num [oppositeAttribution]
  · exact (hjk rfl).elim

/-! A concrete Breuer-core model satisfying both hypotheses at once.

The global state is `Bool`, the apparatus has one reading, restriction is
constant, and every nonempty reading set infers every global state.  The
inference map meshes because the only apparatus reading is `()`, while proper
inclusion is witnessed by `false` and `true`.  Thus the two no-go propositions
below are not vacuous consequences of an inconsistent pair of hypotheses.
-/
private def unitRestriction : Bool → Unit := fun _ => ()

private def unitInference : AISafetyAtlas.Knowledge.Embedded.InferenceMap Bool Unit where
  infer _ := Set.univ
  infer_eq_union_singletons := by
    intro U
    ext s
    constructor
    · intro _
      obtain ⟨a, ha⟩ := U.2
      exact ⟨a, ha, Set.mem_univ _⟩
    · intro _
      exact Set.mem_univ _

private theorem unitMeshing :
    AISafetyAtlas.Knowledge.Embedded.Meshing unitRestriction unitInference := by
  intro a
  ext x
  constructor
  · rintro ⟨s, -, -⟩
    simp
  · intro hx
    cases a
    cases x
    exact ⟨false, Set.mem_univ _, rfl⟩

example : AISafetyAtlas.Knowledge.Embedded.Meshing unitRestriction unitInference :=
  unitMeshing

example : AISafetyAtlas.Knowledge.Embedded.ProperInclusion unitRestriction := by
  exact ⟨false, true, rfl, by decide⟩

/-- Proposition 1 in the source's printed existential form, on that model: some
state no reading set pins down. Both statements of the proposition are therefore
inhabited, not only the negated-universal one the proof produces. -/
example : ∃ s : Bool, ∀ U : AISafetyAtlas.Knowledge.Embedded.ReadingSet Unit,
    unitInference.infer U ≠ {s} :=
  AISafetyAtlas.Knowledge.Embedded.exists_state_not_exactly_measurable
    unitRestriction unitInference ⟨false, true, rfl, by decide⟩
    (by
      intro a
      ext x
      constructor
      · rintro ⟨s, -, -⟩
        simp
      · intro hx
        cases a
        cases x
        exact ⟨false, Set.mem_univ _, rfl⟩)

/-! ### Why there is no empty-apparatus witness here

Neither proposition assumes `Nonempty A`, which matches the printed statements.
Its absence is **faithfulness, not strength**, and no example can show otherwise:
a restriction `Ω → A` with `A` empty forces `Ω` empty, so there are no states
`s₁ s₂` to feed the proposition in the first place. Dropping the hypothesis
closes a gap in the *statement*, not in what the statement can be applied to.
Recorded here so nobody looks for the missing witness. -/

/-! ## Both Breuer hypotheses are load-bearing

The witnesses above inhabit the *hypotheses* of the two propositions. These
inhabit their *conclusions*, which is the half that stops them being vacuous: if
no meshing map ever measured every state, `no_meshing_inference_measures_all_states`
would hold for free and `ProperInclusion` would carry no weight; likewise if
`Distinguishes` were uninhabited.

One model settles both. The apparatus reads the whole state (`restrict = id` on
`Bool`), so proper inclusion *fails* — and exactly then the map does measure
every state and does distinguish the two. -/

private def boolRestriction : AISafetyAtlas.Knowledge.Embedded.Restriction Bool Bool :=
  id

private def boolInference : AISafetyAtlas.Knowledge.Embedded.InferenceMap Bool Bool where
  infer := fun U => U.1
  infer_eq_union_singletons := by
    intro U
    ext s
    constructor
    · intro hs
      exact ⟨s, hs, rfl⟩
    · rintro ⟨a, ha, hsa⟩
      have : s = a := hsa
      exact this ▸ ha

example : AISafetyAtlas.Knowledge.Embedded.Meshing boolRestriction boolInference := by
  intro a
  ext x
  constructor
  · rintro ⟨s, hs, rfl⟩
    exact hs
  · intro hx
    exact ⟨x, hx, rfl⟩

/-- Proper inclusion fails here: the apparatus reading *is* the global state. -/
example : ¬ AISafetyAtlas.Knowledge.Embedded.ProperInclusion boolRestriction := by
  rintro ⟨s₁, s₂, heq, hne⟩
  exact hne heq

/-- The conclusion of Breuer Proposition 1 is not vacuous: this meshing map does
measure every state. -/
example : AISafetyAtlas.Knowledge.Embedded.MeasuresAllStates boolInference := by
  intro s
  exact ⟨AISafetyAtlas.Knowledge.Embedded.ReadingSet.singleton s, rfl⟩

/-- The conclusion of Breuer Proposition 2 is not vacuous: this meshing map does
distinguish two states with different restrictions. -/
example : AISafetyAtlas.Knowledge.Embedded.Distinguishes boolInference false true := by
  refine ⟨AISafetyAtlas.Knowledge.Embedded.ReadingSet.singleton false,
          AISafetyAtlas.Knowledge.Embedded.ReadingSet.singleton true,
          rfl, ?_, rfl, ?_⟩
  · intro h
    exact Bool.noConfusion h
  · intro h
    exact Bool.noConfusion h

/-! ## Physical bridges (Composition / Finite)

These inhabit the *derived* proper-inclusion hypotheses, not the abstract
Breuer core alone: nontrivial remainder ⇒ collision, and a strict finite
cardinality gap ⇒ collision. The core module is unchanged. -/

open AISafetyAtlas.Knowledge.Embedded
open AISafetyAtlas.Knowledge.Embedded.Composition
open AISafetyAtlas.Knowledge.Embedded.Finite

/-- Product apparatus × remainder with two remainders: proper inclusion. -/
example : ProperInclusion (productRestriction Unit Bool) :=
  properInclusion_of_nontrivial_remainder (r₁ := false) (r₂ := true) (by decide)

/-- Finite gap `|Unit| < |Bool|` forces proper inclusion for any restriction. -/
example (restrict : Restriction Bool Unit) :
    ProperInclusion restrict :=
  properInclusion_of_card_lt restrict (by decide : Fintype.card Unit < Fintype.card Bool)

/-- Positive boundary: injective restriction measures every state via fibres. -/
example : MeasuresAllStates (fibreInference (id : Bool → Bool)) :=
  measuresAll_fibreInference_of_injective id Function.injective_id

/-- The bijective positive boundary packages meshing and measurement together. -/
example :
    Meshing (id : Bool → Bool) (fibreInference (id : Bool → Bool)) ∧
      MeasuresAllStates (fibreInference (id : Bool → Bool)) :=
  meshing_and_measuresAll_fibreInference_of_bijective id Function.bijective_id

/-! ### The bridged no-go results are not vacuous

The witnesses above inhabit the *hypotheses* the bridges derive
(`ProperInclusion`). These inhabit the bridges' full antecedent — a meshing map
**and** a cardinality gap at once — which is the half that shows the composite
theorems say something. Without them a reader cannot rule out that no meshing map
survives the gap and the conclusions hold for free.

`unitRestriction : Bool → Unit` with `unitInference` is exactly such a model:
`card Unit = 1 < 2 = card Bool`, and `unitMeshing` proves it meshes. -/

example : ¬ MeasuresAllStates unitInference :=
  no_meshing_measures_all_of_card_lt unitRestriction unitInference
    (by decide : Fintype.card Unit < Fintype.card Bool) unitMeshing

/-- The same for the structural bridge. `Bool ≃ Unit × Bool` is the apparatus
reading paired with an independently varying remainder, and the projection is
`unitRestriction` up to that identification. -/
example : ¬ MeasuresAllStates unitInference :=
  no_meshing_inference_measures_all_states unitRestriction unitInference
    (properInclusion_of_card_lt unitRestriction
      (by decide : Fintype.card Unit < Fintype.card Bool))
    unitMeshing

/-- The third region of the boundary is inhabited too: an injective restriction
that is not surjective admits **no** meshing map at all. -/
example (M : InferenceMap Bool (Option Bool)) :
    ¬ Meshing (some : Bool → Option Bool) M :=
  not_meshing_of_not_surjective some
    (fun hsurj => by
      obtain ⟨b, hb⟩ := hsurj none
      exact absurd hb (Option.some_ne_none b))
    M

end AISafetyAtlas.Examples.NonVacuity
