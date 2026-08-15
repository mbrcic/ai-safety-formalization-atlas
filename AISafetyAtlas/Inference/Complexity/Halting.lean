module

public import AISafetyAtlas.Inference.Complexity.Measure
public import AISafetyAtlas.Inference.Stochastic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Halting and prefix-free devices

Wolpert 2018 §III.2 borrows two notions from Turing-machine theory. Definition 8
says when a device *halts*, and Definition 9 says when it is *prefix-free*. Both
are stated here, and the second turns out to carry a defect in the source that is
worth being explicit about.

## Definition 8 is a refinement statement

*"A device `(X, Y)` halts for setup value `x` iff `X = x ⇒ Y = y` for some single
value `y`. … An ID is total, or recursive iff it halts for all `x ∈ X(U)`. So an
ID `(X, Y)` is recursive iff `X` refines `Y`."*

That last sentence is the content, and `recursive_iff_refines` is it. Nothing
finite, measurable or decidable is involved.

## Definition 9 has a base-of-logarithm defect

*"Given a semi-measure `μ`, a device `(X, Y)` is prefix(-free) iff
`∑_{x : D halts on x} 2^(−ℳ_{μ,X}(x)) ≤ 1`."*

The size `ℳ` is defined two pages earlier as `ℳ_{μ;Γ}(γ) ≜ −ln μ(Γ⁻¹(γ))` — a
**natural** logarithm — and Definition 9 exponentiates it in **base 2**. The two
do not cancel, and `two_rpow_neg_measureLength` computes what the printed formula
actually says: `2^(−ℳ(x)) = μ(X⁻¹(x))^(ln 2)`, an exponent of about `0.693`, not
`μ(X⁻¹(x))`.

Under the reading that makes the two bases agree — `ℳ` in base 2 —
`two_rpow_neg_measureLengthBase2` gives `2^(−ℳ₂(x)) = μ(X⁻¹(x))` exactly, and
then `sum_pushOnImage_le_one` shows the condition is **automatic** for every
device and every halting set: the fibres partition `U`, so their masses sum to at
most the total mass, which is at most one. On that reading Definition 9 restricts
nothing.

So the source's two readings are not interchangeable: one makes the definition a
real restriction, the other makes it empty. Both are proved here rather than
argued, and neither is silently adopted — `PrefixFree` transcribes the printed
formula literally, natural-log `ℳ` and base-2 exponent included.

## What Kraft does and does not give

The source continues: *"By Kraft's inequality, if `D` is prefix-free for a
semi-measure `μ`, then there is a prefix-free code for the set of all halting
`x ∈ X(U)`."*

That is the **existence** direction — codewords built from prescribed lengths.
Mathlib's `Mathlib/InformationTheory/Coding/KraftMcMillan.lean` proves the
**converse**, `kraft_mcmillan_inequality`: for a uniquely decodable code `S`,
`∑_{w ∈ S} D^(−|w|) ≤ 1`. It derives the inequality *from* a code; the source
needs a code *from* the inequality. Measured, not assumed — and it is why this
layer was never a one-line reuse of an existing Mathlib result. That sentence of
the source is a citation of an external theorem, not a claim the paper proves,
and no Lean statement here asserts it.
-/

namespace AISafetyAtlas.Inference

open MeasureTheory

variable {U : Type u}

/-! ## Definition 8 -/

/--
**Wolpert 2018, Definition 8.** *"A device `(X, Y)` halts for setup value `x` iff
`X = x ⇒ Y = y` for some single value `y`."*
-/
@[expose] public def HaltsAt (C : InferenceDevice.{u, v} U) (x : C.Setup) : Prop :=
  ∃ y : Bool, ∀ u : U, C.setup u = x → C.concl u = y

/--
**Wolpert 2018, Definition 8, second half.** *"An ID is total, or recursive iff it
halts for all `x ∈ X(U)`."* The source's `X(U)` is the realized setups, so the
quantifier is over those.
-/
@[expose] public def Recursive (C : InferenceDevice.{u, v} U) : Prop :=
  ∀ x : C.Setup, C.Realized x → HaltsAt C x

/--
**Wolpert 2018, Definition 8, the identification.** *"So an ID `(X, Y)` is
recursive iff `X` refines `Y`."*

`X` refines `Y` is the partition statement: any two universes with the same setup
have the same conclusion.
-/
public theorem recursive_iff_refines (C : InferenceDevice.{u, v} U) :
    Recursive C ↔ ∀ u u' : U, C.setup u = C.setup u' → C.concl u = C.concl u' := by
  constructor
  · intro h u u' huu'
    obtain ⟨y, hy⟩ := h (C.setup u) ⟨u, rfl⟩
    rw [hy u rfl, hy u' huu'.symm]
  · intro h x hx
    obtain ⟨u₀, hu₀⟩ := hx
    exact ⟨C.concl u₀, fun u hu => h u u₀ (hu.trans hu₀.symm)⟩

/-- Every device halts at a setup value no universe realizes: the condition is
vacuous there. This is why Definition 8's second half quantifies over `X(U)`. -/
public theorem haltsAt_of_not_realized (C : InferenceDevice.{u, v} U) {x : C.Setup}
    (hx : ¬ C.Realized x) : HaltsAt C x :=
  ⟨true, fun u hu => absurd ⟨u, hu⟩ hx⟩

/-! ## Definition 9 -/

variable [MeasurableSpace U]

/-- The set of halting setups, as the source's index of summation. -/
@[expose] public noncomputable def haltingSetups (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] [DecidablePred (HaltsAt C)] :
    Finset C.Setup :=
  (realizedSetups C).filter (HaltsAt C)

/--
**Wolpert 2018, Definition 9.** *"Given a semi-measure `μ`, a device `(X, Y)` is
prefix(-free) iff `∑_{x : D halts on x} 2^(−ℳ_{μ,X}(x)) ≤ 1`."*

Transcribed literally: `ℳ` is `measureLength`, the source's natural-logarithm
size, and the exponent base is the printed `2`. See the module header for why
those two do not cancel.
-/
@[expose] public noncomputable def PrefixFree (μ : Measure U) (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] [DecidablePred (HaltsAt C)] : Prop :=
  (haltingSetups C).sum (fun x => (2 : ℝ) ^ (-measureLength μ C x)) ≤ 1

/-- **What the printed formula says.** With `ℳ = −ln μ` and a base-2 exponent,
`2^(−ℳ(x))` is `μ(X⁻¹(x))` raised to `ln 2 ≈ 0.693`, not `μ(X⁻¹(x))`. -/
public theorem two_rpow_neg_measureLength (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (x : C.Setup) (h : 0 < massOn μ C.setup x) :
    (2 : ℝ) ^ (-measureLength μ C x) = massOn μ C.setup x ^ Real.log 2 := by
  unfold measureLength
  rw [neg_neg, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    Real.rpow_def_of_pos h]
  ring_nf

/-- The base-2 size, which is the reading under which Definition 9's exponent
and its `ℳ` agree. -/
@[expose] public noncomputable def measureLengthBase2 (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (x : C.Setup) : ℝ :=
  -(Real.log (massOn μ C.setup x) / Real.log 2)

/-- Under that reading the summand is the fibre mass itself. -/
public theorem two_rpow_neg_measureLengthBase2 (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (x : C.Setup) (h : 0 < massOn μ C.setup x) :
    (2 : ℝ) ^ (-measureLengthBase2 μ C x) = massOn μ C.setup x := by
  have h2 : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  unfold measureLengthBase2
  rw [neg_neg, Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
    show Real.log 2 * (Real.log (massOn μ C.setup x) / Real.log 2) =
      Real.log (massOn μ C.setup x) from by field_simp]
  exact Real.exp_log h

omit [MeasurableSpace U] in
/-- **The base-2 reading makes Definition 9 vacuous.** Fibres of the setup map
partition `U`, so their masses sum to at most the total mass. For any measure of
total mass at most one — which is what a semi-measure gives — the base-2 form of
Definition 9's sum is therefore at most one for *every* device, halting set and
choice of `μ`. Nothing is being restricted.

Stated for the finite mass function of the Definition 9 layer, where the total is
exactly one; a semi-measure only lowers it. -/
public theorem sum_pushOnImage_le_one [Fintype U] (p : FinPMF U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] (s : Finset C.Setup) :
    s.sum (fun x => pushOnImage p C.setup x) ≤ 1 := by
  classical
  set A := Finset.univ.filter (fun u : U => C.setup u ∈ s) with hA
  have hmaps : ∀ u ∈ A, C.setup u ∈ s := by
    intro u hu
    simpa [hA] using (Finset.mem_filter.mp hu).2
  have hfib : ∀ x ∈ s, A.filter (fun u => C.setup u = x)
      = Finset.univ.filter (fun u : U => C.setup u = x) := by
    intro x hx
    ext u
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hx, h⟩⟩
  have hsplit := Finset.sum_fiberwise_of_maps_to hmaps p.mass
  have hcollect : s.sum (fun x => pushOnImage p C.setup x) = A.sum p.mass := by
    rw [← hsplit]
    exact Finset.sum_congr rfl (fun x hx => by rw [pushOnImage, ← hfib x hx])
  rw [hcollect, ← p.sum_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
    (fun u _ _ => p.nonneg u)


/-! ### Definition 9 over an arbitrary setup range

Definition 7 prints **countable** `X(U)`, and `PrefixFree` above is stated over a
`Finset`. Unlike Definition 7 this restriction is not forced by the display
having to denote: the prefix-free condition needs no `min` to be attained, only a
sum of nonnegative terms, and in `ℝ≥0∞` such a sum denotes over **any** index
set. So the widening below is not merely to the source's countable range but past
it, to an arbitrary one.

**The realized restriction is kept, and it is load-bearing.** The source indexes
the sum by *"`x` : `D` halts on `x`"*, with no realizedness condition. But an
unrealized setup halts vacuously (`haltsAt_of_not_realized`) and its fibre has
`massOn = 0`, so `measureLength` is `−log 0`, which Lean totalizes to `0`, and
the summand becomes `2⁰ = 1`. Indexing literally would therefore add `1` to the
sum for every unrealized setup value and make the condition fail for trivial
reasons in the totalization rather than in the mathematics. This is a delta from
the printed index and is recorded as such.
-/

/-- **Definition 9 over an arbitrary setup range**, in `ℝ≥0∞` where the sum always
denotes. `PrefixFree` is the finite instance. -/
@[expose] public noncomputable def PrefixFreeOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) : Prop :=
  ∑' x : {x : C.Setup // C.Realized x ∧ HaltsAt C x},
      ENNReal.ofReal ((2 : ℝ) ^ (-measureLength μ C x.1)) ≤ 1

omit [MeasurableSpace U] in
/-- The halting-and-realized setups are exactly `haltingSetups`. -/
public theorem mem_haltingSetups_iff (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] [DecidablePred (HaltsAt C)]
    (x : C.Setup) :
    x ∈ haltingSetups C ↔ C.Realized x ∧ HaltsAt C x := by
  unfold haltingSetups realizedSetups
  rw [Finset.mem_filter, mem_rangeFinset]
  exact Iff.rfl

/-- **The finite statement is the instance of the general one.** So widening the
index costs nothing: every theorem about `PrefixFree` transfers. -/
public theorem prefixFreeOn_iff_prefixFree (μ : Measure U)
    (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] [DecidablePred (HaltsAt C)] :
    PrefixFreeOn μ C ↔ PrefixFree μ C := by
  classical
  let hequiv : {x : C.Setup // C.Realized x ∧ HaltsAt C x} ≃
      {x : C.Setup // x ∈ haltingSetups C} :=
    { toFun := fun x => ⟨x.1, (mem_haltingSetups_iff C x.1).mpr x.2⟩
      invFun := fun x => ⟨x.1, (mem_haltingSetups_iff C x.1).mp x.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have key : ∑' x : {x : C.Setup // C.Realized x ∧ HaltsAt C x},
        ENNReal.ofReal ((2 : ℝ) ^ (-measureLength μ C x.1))
      = ∑' x : {x : C.Setup // x ∈ haltingSetups C},
        ENNReal.ofReal ((2 : ℝ) ^ (-measureLength μ C x.1)) :=
    by exact hequiv.tsum_eq (fun x => ENNReal.ofReal ((2 : ℝ) ^ (-measureLength μ C x.1)))
  unfold PrefixFreeOn PrefixFree
  rw [key]
  rw [Finset.tsum_subtype (haltingSetups C)
    (fun x => ENNReal.ofReal ((2 : ℝ) ^ (-measureLength μ C x)))]
  rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => Real.rpow_nonneg (by norm_num) _)]
  exact ENNReal.ofReal_le_one

end AISafetyAtlas.Inference
