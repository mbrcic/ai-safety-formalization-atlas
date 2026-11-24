module

public import AISafetyAtlas.Knowledge.Embedded
public import AISafetyAtlas.Knowledge.Embedded.Composition
public import AISafetyAtlas.Knowledge.Embedded.Finite
public import Mathlib.Data.Set.Finite.Range

/-!
# Breuer's embedded observer, at two bits

`Knowledge.Embedded` carries Breuer's results on an apparatus that is part of the
system it measures: meshing, exact measurability, and the two directions of the
impossibility. None of them reached an `Examples/` application, so the
hypotheses — `ProperInclusion`, `Meshing`, `MeasuresAllStates` — had never been
inhabited or refuted at a model.

The model is the smallest one that says anything: two bits, of which the
apparatus is the first. The second bit is the part of the world the apparatus
does not reach, and its existence is exactly `ProperInclusion`.

**The meshing inference map is the library's own.** `fibreInference` reports,
for an apparatus reading `a`, every global state whose apparatus part is `a` —
which is all an embedded observer can say. It meshes, and by Breuer's theorem it
therefore cannot measure every state exactly; `fibre_not_measuresAllStates` is
that, and `measuresAll_forces_named_failure` is the contrapositive at a named
state.
-/

namespace AISafetyAtlas.Examples.Knowledge.Embedded

open AISafetyAtlas.Knowledge.Embedded
open AISafetyAtlas.Knowledge.Embedded.Composition
open AISafetyAtlas.Knowledge.Embedded.Finite

/-- Two bits: the apparatus reads the first, the second is the rest of the
world. -/
public abbrev TwoBits : Type := Bool × Bool

/-- The apparatus sees its own bit and nothing else. -/
@[expose] public def readFirst : Restriction TwoBits Bool := Prod.fst

/-- **The apparatus does not determine the state.** Two worlds differing only in
the bit the apparatus cannot reach — Breuer's proper inclusion, which is the
whole hypothesis of the impossibility. -/
public theorem readFirst_properInclusion : ProperInclusion readFirst :=
  ⟨(true, false), (true, true), rfl, by decide⟩

/-- Every reading is realized. -/
public theorem readFirst_surjective : Function.Surjective readFirst :=
  fun a => ⟨(a, false), rfl⟩

/-- **So the global state is not knowable from the apparatus.** The knowability
reading of proper inclusion, which is how this module meets
`AISafetyAtlas.Knowledge`. -/
public theorem not_knowable_twoBits :
    ¬ AISafetyAtlas.Knowledge.Knowable readFirst (id : TwoBits → TwoBits) :=
  not_knowable_state_of_properInclusion readFirst readFirst_properInclusion

/-! ## The meshing inference map

`fibreInference` is the library's own construction of it — a reading set read as
the states restricting into it — and `meshing_fibreInference_of_surjective` is
its meshing proof. Both were here before this file was written; an earlier draft
of it rebuilt the map and the proof by hand, which is the duplication the
reuse policy exists to prevent.
-/

/-- **It meshes**, because every reading is realized. -/
public theorem fibre_meshing : Meshing readFirst (fibreInference readFirst) :=
  meshing_fibreInference_of_surjective readFirst readFirst_surjective

/-- **A meshing observer inside its own world cannot measure every state.**
Breuer's central result, at the model. The apparatus reads one bit honestly and
the second bit is permanently beyond it. -/
public theorem fibre_not_measuresAllStates : ¬ MeasuresAllStates (fibreInference readFirst) :=
  no_meshing_inference_measures_all_states_direct readFirst (fibreInference readFirst)
    readFirst_properInclusion fibre_meshing

/-- **Reading a single value returns exactly the worlds with that value**, given
meshing — the computation the impossibility runs on. -/
public theorem fibre_infer_singleton (a : Bool) :
    (fibreInference readFirst).infer (ReadingSet.singleton a)
      = {s | s ∈ (fibreInference readFirst).infer ReadingSet.univ ∧ readFirst s = a} :=
  infer_singleton_eq_of_meshing readFirst (fibreInference readFirst) fibre_meshing a

/-! ## The contrapositive, and the state it names -/

/-- **Suppose instead an observer measured every state exactly.** Then meshing
fails somewhere, and the failure is at a *named* state rather than merely
somewhere — which is what makes the impossibility usable rather than only true.
Stated as an implication, because the antecedent is what `fibreInference` refutes. -/
public theorem measuresAll_forces_named_failure (M : InferenceMap TwoBits Bool)
    (hall : MeasuresAllStates M) :
    ∃ s₀ : TwoBits,
      Set.image readFirst (M.infer (ReadingSet.singleton (readFirst s₀)))
        ≠ {readFirst s₀} :=
  exists_state_meshing_failure_of_measuresAllStates readFirst M
    readFirst_properInclusion readFirst_surjective hall

/-! ## The product form, where the remainder is explicit

`Knowledge.Embedded.Composition` states the same obstruction with the global
state written as `apparatus × remainder`, which is the shape a decomposition
argument uses. Two bits is that shape already, so the product results run here
without a second model.
-/

/-- **Knowability of the whole state is injectivity of the reading**, and
nothing else. The characterisation that makes proper inclusion and unknowability
the same fact rather than two. -/
public theorem product_knowable_iff_injective :
    AISafetyAtlas.Knowledge.Knowable (productRestriction Bool Bool) (id : Bool × Bool → Bool × Bool)
      ↔ Function.Injective (productRestriction Bool Bool) :=
  knowable_whole_state_iff_injective (productRestriction Bool Bool)

/-- **A remainder with two states already defeats it.** No cardinality argument
and no finiteness: two distinct remainder values collide the projection. -/
public theorem product_not_knowable :
    ¬ AISafetyAtlas.Knowledge.Knowable (productRestriction Bool Bool) id :=
  not_knowable_productState_of_nontrivial_remainder (A := Bool) (show false ≠ true by decide)

/-- **And no meshing observer measures every state**, in the product form. -/
public theorem product_no_meshing_measures_all :
    ¬ MeasuresAllStates (fibreInference (productRestriction Bool Bool)) :=
  no_meshing_measures_all_of_nontrivial_remainder (A := Bool)
    (fibreInference (productRestriction Bool Bool)) (show false ≠ true by decide)
    (meshing_fibreInference_of_surjective (productRestriction Bool Bool)
      fun a => ⟨(a, false), rfl⟩)

/-- **The counting form of the same hypothesis.** Where the two results above
take a pair of distinct remainder states, this takes the cardinality bound --
the form a finite model supplies without naming the pair. -/
public theorem product_properInclusion_by_card :
    ProperInclusion (productRestriction Bool Bool) :=
  properInclusion_product_of_card_rest_ge_two (A := Bool) (by decide)

/-! ## A state space that is not a product on its face

`no_meshing_measures_all_of_nontrivial_remainder_of_equiv` is the same
obstruction through a *representation* rather than through a literal product,
and that is the whole of its content: the apparatus need not sit inside a state
space already written as `apparatus × remainder`. Run at `Equiv.refl` it would
say nothing the product form does not.

So the state space here is `Fin 4`, which is not a pair, and `fourEquiv` is one
of the relabellings that makes it one. Breuer's conclusion survives the
relabelling, which is what lets the impossibility be applied to a system whose
decomposition is a choice rather than a given.
-/

/-- Four states, relabelled as a pair of bits: the low bit is what the apparatus
reads, the high bit is the rest of the world. -/
@[expose] public def fourEquiv : Fin 4 ≃ ProductState Bool Bool where
  toFun := fun i => (i.val % 2 == 1, i.val / 2 == 1)
  invFun := fun p => ⟨(if p.1 then 1 else 0) + 2 * (if p.2 then 1 else 0), by
    rcases p with ⟨a, b⟩
    cases a <;> cases b <;> simp⟩
  left_inv := by intro i; revert i; decide
  right_inv := by rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

/-- Every reading is realized through the relabelling. -/
public theorem fourEquiv_surjective :
    Function.Surjective (equivalentProductRestriction fourEquiv) := by
  intro a
  cases a
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩

/-- **The apparatus still does not determine the state**, read through the
representation. -/
public theorem fourEquiv_properInclusion :
    ProperInclusion (equivalentProductRestriction fourEquiv) :=
  properInclusion_of_nontrivial_remainder_of_equiv fourEquiv
    (show (false : Bool) ≠ true by decide)

/-- **And no meshing observer measures every one of the four states.** Breuer's
impossibility on a state space that had to be represented before it was a
product. -/
public theorem fourEquiv_not_measuresAllStates :
    ¬ MeasuresAllStates (fibreInference (equivalentProductRestriction fourEquiv)) :=
  no_meshing_measures_all_of_nontrivial_remainder_of_equiv fourEquiv
    (fibreInference (equivalentProductRestriction fourEquiv))
    (show (false : Bool) ≠ true by decide)
    (meshing_fibreInference_of_surjective _ fourEquiv_surjective)

/-! ## §3.4, *A First Attempt*: counting before meshing

Breuer's §3.4 argues by counting, before the meshing condition exists. The
library's §3.4 statements take no meshing hypothesis, so the witnesses below use
inference maps that do **not** mesh — the class the §3.5 theorems cannot reach. -/

/-- An apparatus that reports the wrong bit: the reading `b` is taken to mean the
world `(!b, false)`. A point-map inference that does not mesh. -/
@[expose] public def swapRead : InferenceMap TwoBits Bool :=
  InferenceMap.ofFun (fun b => (!b, false))

/-- **`swapRead` does not mesh**: the reading `true` infers a world whose
apparatus bit is `false`. So the §3.5 results, which assume meshing, say nothing
about it. -/
public theorem swapRead_not_meshing : ¬ Meshing readFirst swapRead := by
  intro hm
  have h := hm true
  rw [swapRead, ofFun_infer_singleton] at h
  simp [readFirst] at h

/-- **Breuer §3.4's finite remark, at a non-meshing map.** Two readings, four
worlds: no inference map measures every world, meshing or not. -/
public theorem swapRead_not_measuresAllStates : ¬ MeasuresAllStates swapRead :=
  AISafetyAtlas.Knowledge.Embedded.Finite.not_measuresAllStates_of_card_lt swapRead
    (by simp [TwoBits])

/-- **Breuer §3.4: proper inclusion leaves strictly more worlds than readings**,
at the two-bit model. -/
public theorem twoBits_card_lt : Fintype.card Bool < Fintype.card TwoBits :=
  AISafetyAtlas.Knowledge.Embedded.Finite.card_lt_of_properInclusion readFirst
    readFirst_surjective readFirst_properInclusion

/-- The reading-for-the-world identity map: a surjective point map, so it
measures every state. -/
@[expose] public def idRead : InferenceMap Bool Bool := InferenceMap.ofFun id

/-- **The necessary surjection, at a map that measures everything.**
`exists_surjective_of_measuresAllStates` with its hypothesis discharged. -/
public theorem idRead_exists_surjective : ∃ f : Bool → Bool, Function.Surjective f :=
  AISafetyAtlas.Knowledge.Embedded.exists_surjective_of_measuresAllStates idRead
    (measuresAllStates_ofFun_of_surjective Function.surjective_id)

/-- An inference map that ignores its reading and reports every world. -/
@[expose] public def blindRead : InferenceMap Bool Bool where
  infer _ := Set.univ
  infer_eq_union_singletons := fun U => by
    obtain ⟨a, ha⟩ := U.2
    ext s
    exact ⟨fun _ => ⟨a, ha, trivial⟩, fun _ => trivial⟩

/-- **Breuer §3.4's *"but not sufficient"*.** Readings and worlds are both `Bool`,
so a surjection from readings onto worlds exists, yet `blindRead` measures no
world exactly. Sufficiency fails for a given inference map; it cannot fail as
*"no map measures everything"*, since `idRead` does. -/
public theorem surjection_not_sufficient :
    (∃ f : Bool → Bool, Function.Surjective f) ∧ ¬ MeasuresAllStates blindRead := by
  refine ⟨⟨id, Function.surjective_id⟩, fun hall => ?_⟩
  obtain ⟨U, hU⟩ := hall true
  have hfalse : false ∈ blindRead.infer U := trivial
  rw [hU] at hfalse
  exact Bool.false_ne_true hfalse

/-! ## Breuer's footnote 4, at `ℕ × Bool`

Countably many readings, two worlds behind each: a bijection between readings and
worlds exists, and none of them meshes. -/

/-- The apparatus reads the natural-number part; the bit is beyond it. -/
@[expose] public def readNat : Restriction (ℕ × Bool) ℕ := Prod.fst

/-- Every reading is realized. -/
public theorem readNat_surjective : Function.Surjective readNat := fun a => ⟨(a, false), rfl⟩

/-- Each reading has two worlds behind it: finitely many. -/
public theorem readNat_finite_fibres (a : ℕ) : (readNat ⁻¹' {a}).Finite :=
  (Set.finite_range fun b : Bool => (a, b)).subset fun p hp => ⟨p.2, Prod.ext hp.symm rfl⟩

/-- The bit the apparatus cannot reach. -/
public theorem readNat_properInclusion : ProperInclusion readNat :=
  ⟨(0, false), (0, true), rfl, by decide⟩

/-- **Breuer footnote 4, at the model**: a bijection `ℕ ≃ ℕ × Bool` exists, and
every one of them, read as an inference map, fails meshing at some reading. -/
public theorem readNat_footnote4 :
    Nonempty (ℕ ≃ ℕ × Bool) ∧ ∀ e : ℕ ≃ ℕ × Bool, ∃ a : ℕ,
      Set.image readNat ((InferenceMap.ofFun e).infer (ReadingSet.singleton a)) ≠ {a} :=
  nonempty_equiv_and_meshing_failure_of_finite_fibres readNat readNat_surjective
    readNat_finite_fibres readNat_properInclusion

/-- **The §3.4 surjection exists here too, and still no meshing map measures
everything**: `ℕ` maps onto `ℕ × Bool`, yet proper inclusion rules every meshing
inference map out (Proposition 1). The necessary condition holds and is not
sufficient, now at an infinite model and for every meshing map at once. -/
public theorem readNat_surjection_not_sufficient :
    (∃ f : ℕ → ℕ × Bool, Function.Surjective f) ∧
      ∀ M : InferenceMap (ℕ × Bool) ℕ, Meshing readNat M → ¬ MeasuresAllStates M := by
  obtain ⟨e⟩ := (readNat_footnote4).1
  exact ⟨⟨e, e.surjective⟩, fun M hm =>
    no_meshing_inference_measures_all_states readNat M readNat_properInclusion hm⟩

/-- `exists_injective_of_measuresAllStates` at `idRead`, which measures every
state. -/
example : ∃ g : Bool → Bool, Function.Injective g :=
  AISafetyAtlas.Knowledge.Embedded.exists_injective_of_measuresAllStates idRead
    (AISafetyAtlas.Knowledge.Embedded.Composition.measuresAllStates_ofFun_of_surjective
      Function.surjective_id)

/-- `nonempty_equiv_of_finite_fibres` at `readNat`: the bijection alone, without
proper inclusion. -/
example : Nonempty (ℕ ≃ ℕ × Bool) :=
  AISafetyAtlas.Knowledge.Embedded.Composition.nonempty_equiv_of_finite_fibres readNat
    readNat_surjective readNat_finite_fibres

/-- `not_meshing_ofFun_of_surjective` at `readNat`, for any bijection. -/
example (e : ℕ ≃ ℕ × Bool) : ¬ Meshing readNat (InferenceMap.ofFun e) :=
  AISafetyAtlas.Knowledge.Embedded.Composition.not_meshing_ofFun_of_surjective readNat
    readNat_properInclusion e.surjective

/-- A two-state apparatus inside a composite with a one-state rest: restriction is onto. -/
example : Function.Surjective (Prod.fst : Restriction (Bool × Unit) Bool) :=
  composite_restrict_surjective

end AISafetyAtlas.Examples.Knowledge.Embedded
