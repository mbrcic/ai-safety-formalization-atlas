module

public import AISafetyAtlas.Inference.Stochastic
public import AISafetyAtlas.Inference.Stochastic.Bounds

/-!
# Mutual information is nonnegative, and the bound is both reached and missed

`mutualInfo_nonneg` is Gibbs' inequality in the form Wolpert's Proposition 6
uses. Nothing applied it, so the bound had never been read at a pair of
variables — and a nonnegativity statement is exactly the kind that can be
uninteresting, since `0 ≤ 0` satisfies it forever.

Both sides are here.

* Two **independent** coordinates of a uniform pair of bits.
  `mutualInfo_eq_zero_iff` turns independence into `M = 0`, so the bound is
  **attained** and cannot be strengthened to a strict inequality.
* Two **perfectly correlated** coordinates. They are not independent, so the
  same equivalence gives `M ≠ 0`, and with the bound that is `0 < M`. So the
  bound is not always attained either, and `mutualInfo_nonneg` is carrying
  content rather than restating a definition.
-/

namespace AISafetyAtlas.Examples.Inference.Stochastic

open AISafetyAtlas.Inference

/-! ## Two independent coins, where the bound is attained -/

/-- The uniform mass on a pair of bits. -/
@[expose] public noncomputable def uniformPair : FinPMF (Bool × Bool) where
  mass := fun _ => 1 / 4
  nonneg := fun _ => by norm_num
  sum_one := by simp [Finset.sum_const, Finset.card_univ]

/-- **The two coordinates are independent**, pointwise on the joint
pushforward. -/
public theorem uniformPair_independent :
    StatisticallyIndependent uniformPair Prod.fst Prod.snd := by
  intro x y
  simp only [pushOnImage, uniformPair, Finset.sum_filter, Fintype.sum_prod_type]
  cases x <;> cases y <;> norm_num

/-- **So their mutual information is zero.** -/
public theorem uniformPair_mutualInfo_eq_zero :
    mutualInfo uniformPair Prod.fst Prod.snd = 0 :=
  (mutualInfo_eq_zero_iff uniformPair Prod.fst Prod.snd).mpr uniformPair_independent

/-- **The bound, at that pair, is attained**: nonnegativity holds and the value
is exactly the bound, so no strict form of the inequality is available. -/
public theorem uniformPair_bound_attained :
    0 ≤ mutualInfo uniformPair Prod.fst Prod.snd ∧
      mutualInfo uniformPair Prod.fst Prod.snd = 0 :=
  ⟨AISafetyAtlas.Inference.mutualInfo_nonneg uniformPair Prod.fst Prod.snd, uniformPair_mutualInfo_eq_zero⟩

/-! ## Two copies of one coin, where it is not -/

/-- A pair of bits that always agree, each value equally likely. -/
@[expose] public noncomputable def corrPair : FinPMF (Bool × Bool) where
  mass := fun x => if x.1 = x.2 then 1 / 2 else 0
  nonneg := fun x => by split <;> norm_num
  sum_one := by simp [Fintype.sum_prod_type]

/-- **They are not independent.** The joint gives `(false, true)` no mass while
the product of the marginals gives it a quarter. -/
public theorem corrPair_not_independent :
    ¬ StatisticallyIndependent corrPair Prod.fst Prod.snd := by
  intro h
  have hkey := h false true
  simp only [pushOnImage, corrPair, Finset.sum_filter, Fintype.sum_prod_type] at hkey
  norm_num at hkey

/-- **So here the bound is strict.** `mutualInfo_nonneg` gives `0 ≤ M` and
independence is what `M = 0` would require, so the information between two
copies of a coin is positive. This is the half that makes the bound a fact about
dependence rather than a typing accident.

Written with its full name, so the use grounds this declaration and no other
with the same leaf. -/
public theorem corrPair_mutualInfo_pos :
    0 < mutualInfo corrPair Prod.fst Prod.snd :=
  lt_of_le_of_ne (AISafetyAtlas.Inference.mutualInfo_nonneg corrPair Prod.fst Prod.snd)
    (fun he => corrPair_not_independent
      ((mutualInfo_eq_zero_iff corrPair Prod.fst Prod.snd).mp he.symm))

/-! ## Proposition 11, at two devices that meet every one of its hypotheses

`prop11_of_independent` carries fourteen hypotheses: two devices, each with
exactly two realized setup values of positive mass, and statistical
independence between the two setups. A bound with that many conditions is
exactly the kind that can be true because nothing satisfies them, and nothing
did.

The uniform pair of bits satisfies all of them at once. One device reads the
first coordinate and reports the second; the other does the reverse. Each setup
is two-valued with mass a half, and `uniformPair_independent` above is the
independence the proposition asks for -- reused rather than reproved.
-/

/-- Read the first bit, report the second. -/
public abbrev fstDevice : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

/-- Read the second bit, report the first. -/
public abbrev sndDevice : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.snd
  concl := Prod.fst
  concl_surjective := fun b => ⟨(b, false), rfl⟩

/-- Each setup value carries half the mass, so both are of positive mass and
neither is the whole. -/
public theorem fstDevice_setupMass (x : Bool) :
    setupMass uniformPair fstDevice x = 1 / 2 := by
  simp only [setupMass, pushOnImage, uniformPair, fstDevice, Finset.sum_filter,
    Fintype.sum_prod_type]
  cases x <;> norm_num

/-- And the same on the other side. -/
public theorem sndDevice_setupMass (x : Bool) :
    setupMass uniformPair sndDevice x = 1 / 2 := by
  simp only [setupMass, pushOnImage, uniformPair, sndDevice, Finset.sum_filter,
    Fintype.sum_prod_type]
  cases x <;> norm_num

/-- The two setups are independent -- the same independence proved above, at the
devices' own setup maps. -/
public theorem devices_independent :
    StatisticallyIndependent uniformPair fstDevice.setup sndDevice.setup := by
  intro x y
  simp only [pushOnImage, uniformPair, fstDevice, sndDevice, Finset.sum_filter,
    Fintype.sum_prod_type]
  cases x <;> cases y <;> norm_num

/--
**Wolpert's Proposition 11, at a pair of devices that meets it.**

The product of the two inference accuracies is bounded by the supremum of the
Proposition 6 expression at the two setup masses. Every hypothesis is
discharged: realized, distinct, exhaustive and of positive mass on both sides,
and independent between them.
-/
public theorem prop11_at_uniform_pair :
    inferenceAccuracy fstDevice uniformPair sndDevice.concl
        * inferenceAccuracy sndDevice uniformPair fstDevice.concl ≤
      ⨆ z : Prop6Quadruple,
        prop6Expr (setupMass uniformPair fstDevice false)
          (setupMass uniformPair sndDevice false) z :=
  prop11_of_independent fstDevice sndDevice uniformPair
    ⟨(false, false), rfl⟩ ⟨(true, false), rfl⟩ (by decide)
    (fun w => by cases w.1 <;> simp)
    (by rw [fstDevice_setupMass]; norm_num) (by rw [fstDevice_setupMass]; norm_num)
    ⟨(false, false), rfl⟩ ⟨(false, true), rfl⟩ (by decide)
    (fun w => by cases w.2 <;> simp)
    (by rw [sndDevice_setupMass]; norm_num) (by rw [sndDevice_setupMass]; norm_num)
    devices_independent

end AISafetyAtlas.Examples.Inference.Stochastic
