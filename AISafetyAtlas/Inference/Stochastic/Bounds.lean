module

public import AISafetyAtlas.Inference.Stochastic

/-!
# How low covariance accuracy can go

Definition 9's accuracy is an average of per-probe best-case conditional
expectations, and each of those lives in `[-1, 1]`, so the accuracy does too.
That much is arithmetic. This module holds the source's sharper statement: the
accuracy is bounded below by a quantity that factors into a term depending only
on `|Γ(U)|` and a term depending only on the device.

The device term, `max_x E_P(Y ∣ x)`, is what the source calls the *inference
power* of `D` — its ability to say yes. The cardinality term `(2 − |Γ(U)|)/|Γ(U)|`
is negative once the target has three or more values, which the source flags in
its own footnote as an artefact of the `±1` coding of `𝔹` rather than a claim
that accuracy is usually negative.

## Where the bound comes from

The whole content is one pointwise identity. For any `u`, summing the probe
values over the realized image gives

`∑_{γ ∈ Γ(U)} δ_γ(Γ(u)) = 1 − (|Γ(U)| − 1) = 2 − |Γ(U)|`,

because exactly one probe fires at `Γ(u)` and every other answers `−1`. Multiply
by `Y(u)`, take the conditional expectation at the `x` maximizing `E_P(Y ∣ x)`,
and the definition's `sup` over setups is bounded below by that one setup's
value — `Proposition_8` is that chain.

## Scope

Stated over the finite `FinPMF` layer of Definition 9, and **without** the
source's standing hypothesis that `|Γ(U)|` be finite as a side condition: `G` is
a `Fintype` here, so the realized image is a `Finset` and its cardinality is the
source's `|Γ(U)|`. Nonemptiness of that image is not assumed either — it follows
from `concl_surjective`, which makes `U` inhabited.
-/

namespace AISafetyAtlas.Inference

open Finset

variable {U : Type u} [Fintype U]

/-- The realized image of `Γ`, which is Definition 9's index set and the source's
`Γ(U)`. -/
@[expose] public def realizedValues {G : Type v'} [Fintype G] [DecidableEq G]
    (Γ : U → G) : Finset G :=
  Finset.univ.filter (fun γ : G => ∃ w, Γ w = γ)

public theorem mem_realizedValues {G : Type v'} [Fintype G] [DecidableEq G]
    {Γ : U → G} {γ : G} : γ ∈ realizedValues Γ ↔ ∃ w, Γ w = γ := by
  simp [realizedValues]

/-- **The pointwise identity.** Summing every realized probe at one point gives
`2 − |Γ(U)|`: one probe fires, the rest answer `−1`. -/
public theorem sum_boolPm_probe {G : Type v'} [Fintype G] [DecidableEq G]
    (Γ : U → G) (u : U) :
    (realizedValues Γ).sum (fun γ => boolPm (probe γ (Γ u))) =
      2 - ((realizedValues Γ).card : ℝ) := by
  have hmem : Γ u ∈ realizedValues Γ := mem_realizedValues.mpr ⟨u, rfl⟩
  have hrw : ∀ γ : G, boolPm (probe γ (Γ u)) = -1 + (if γ = Γ u then (2 : ℝ) else 0) := by
    intro γ
    by_cases hg : γ = Γ u
    · subst hg; simp [probe, boolPm]; norm_num
    · have hne : Γ u ≠ γ := fun h => hg h.symm
      simp [probe, boolPm, hne, hg]
  simp only [hrw, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul,
    Finset.sum_ite_eq' (realizedValues Γ) (Γ u) (fun _ => (2 : ℝ)), if_pos hmem]
  ring

/--
**Wolpert 2018, Proposition 8.** *"Let `P` be a probability measure over `U`,
`D = (X, Y)` a device, and `Γ` a function over `U` with finite `|Γ(U)|`. Then
`cov(D, Γ) ≥ (2 − |Γ(U)|) max_x E_P(Y ∣ x) / |Γ(U)|`."*

The source's `max_x E_P(Y ∣ x)` is the maximum over the setup values Definition 9
already maximizes over — those of positive mass, where its conditional
expectations are defined.
-/
public theorem inferenceAccuracy_ge (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] {G : Type v'} [Fintype G] [DecidableEq G]
    (p : FinPMF U) (Γ : U → G) :
    ((2 - ((realizedValues Γ).card : ℝ)) *
        (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
          (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))) /
      ((realizedValues Γ).card : ℝ)
      ≤ inferenceAccuracy C p Γ := by
  classical
  obtain ⟨w₀, -⟩ := C.concl_surjective true
  have hSne : (realizedValues Γ).Nonempty := ⟨Γ w₀, mem_realizedValues.mpr ⟨w₀, rfl⟩⟩
  have hcard : (0 : ℝ) < ((realizedValues Γ).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hSne
  -- `x_m := argmax_x E_P(Y ∣ x)`, which exists because the `sup'` is over a
  -- nonempty finite set.
  obtain ⟨xm, hxm, hxmeq⟩ :=
    Finset.exists_mem_eq_sup' (positiveMassSetups_nonempty C p)
      (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))
  have hunfold : inferenceAccuracy C p Γ =
      (realizedValues Γ).sum (fun γ =>
        (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
          (fun x => condExpect p C.setup x
            (fun u => boolPm (C.concl u) * boolPm (probe γ (Γ u))))) /
        ((realizedValues Γ).card : ℝ) := by
    unfold inferenceAccuracy realizedValues
    rw [if_neg (by exact_mod_cast hcard.ne')]
  rw [hunfold, div_le_div_iff_of_pos_right hcard]
  -- Every probe's `sup` is at least its value at `x_m`.
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum (fun γ _ => Finset.le_sup' _ hxm))
  -- and the sum at `x_m` is the pointwise identity, scaled.
  rw [condExpect_sum]
  have hpt : ∀ u : U,
      (realizedValues Γ).sum (fun γ => boolPm (C.concl u) * boolPm (probe γ (Γ u))) =
        (2 - ((realizedValues Γ).card : ℝ)) * boolPm (C.concl u) := by
    intro u
    rw [← Finset.mul_sum, sum_boolPm_probe]
    ring
  simp only [hpt]
  rw [condExpect_const_mul, hxmeq]

/--
**A binary target's accuracy is never negative.** The source's footnote observes
that `(2 − |Γ(U)|)/|Γ(U)|` goes negative once the target has three or more
values. At exactly two values it is zero, and Proposition 8 then says the
accuracy is bounded below by zero — with no hypothesis on the device or the
distribution at all.

This is where the bound has teeth: Definition 9's accuracy is an average of
conditional expectations of a `±1`-valued product, so nothing in its shape
prevents it from being negative, and for a binary target it cannot be.
-/
public theorem inferenceAccuracy_nonneg_of_card_eq_two (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] {G : Type v'} [Fintype G] [DecidableEq G]
    (p : FinPMF U) (Γ : U → G) (h : (realizedValues Γ).card = 2) :
    0 ≤ inferenceAccuracy C p Γ := by
  have hbound := inferenceAccuracy_ge C p Γ
  rw [h] at hbound
  norm_num at hbound
  exact hbound

/-! ## Proposition 11 as printed

The 2008 layer proves the *sharper* statement `prop6_product_eq`: the product of
the two accuracies **equals** the source's polynomial at the realized quadruple.
That is strictly more than the printed `≤ max`, but it is not the printed shape,
and the ledger recorded the difference rather than papering over it.

The printed shape needs the maximum to exist. `M` is the unit hypercube, which is
`Prop6Quadruple` — its membership conditions are structure fields — so the
maximum is `⨆ z : Prop6Quadruple`, and `prop6Expr_bddAbove` is what makes that a
real number rather than a junk value.
-/

/--
**Wolpert 2018, Proposition 11, printed shape.**
*"`ε₁ε₂ ≤ max_{z⃗ ∈ M} |αβ[k(z⃗)]² + αk(z⃗)m(z⃗) + βk(z⃗)n(z⃗) + m(z⃗)n(z⃗)|`."*

Derived from the sharper `prop6_product_eq` by bounding the realized quadruple's
value by the supremum over `M`.
-/
public theorem prop6_product_le_iSup (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (p : FinPMF U)
    {a₁ b₁ : C₁.Setup} {a₂ b₂ : C₂.Setup}
    (ha₁ : C₁.Realized a₁) (hb₁ : C₁.Realized b₁) (hne₁ : a₁ ≠ b₁)
    (hall₁ : ∀ w : U, C₁.setup w = a₁ ∨ C₁.setup w = b₁)
    (hpa₁ : 0 < pushOnImage p C₁.setup a₁) (hpb₁ : 0 < pushOnImage p C₁.setup b₁)
    (ha₂ : C₂.Realized a₂) (hb₂ : C₂.Realized b₂) (hne₂ : a₂ ≠ b₂)
    (hall₂ : ∀ w : U, C₂.setup w = a₂ ∨ C₂.setup w = b₂)
    (hpa₂ : 0 < pushOnImage p C₂.setup a₂) (hpb₂ : 0 < pushOnImage p C₂.setup b₂)
    (law : Prop6Law C₁ C₂ p a₁ b₁ a₂ b₂) :
    inferenceAccuracy C₁ p C₂.concl * inferenceAccuracy C₂ p C₁.concl ≤
      ⨆ z : Prop6Quadruple,
        prop6Expr (setupMass p C₁ a₁) (setupMass p C₂ a₂) z := by
  rw [prop6_product_eq C₁ C₂ p ha₁ hb₁ hne₁ hall₁ hpa₁ hpb₁ ha₂ hb₂ hne₂ hall₂
    hpa₂ hpb₂ law]
  exact le_ciSup (prop6Expr_bddAbove _ _) _

/--
**Wolpert 2018, Proposition 11, from its own premise.** The 2018 restatement takes
*statistical independence of the two setup functions* as the hypothesis, where
2008 Proposition 6 takes mutual-information distinguishability `1` and derives
independence from it. This is that version: independence in, the printed bound
out.

The printed defect survives in the source — it says *"`D₂` infers `D₂` with
accuracy `ε₂`"* where it means `D₂` infers `D₁`, exactly as the 2008 text says
*"`C₂` infers `C₂`"*. The Lean statement uses the intended reading; see clash 18.
-/
public theorem prop11_of_independent (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (p : FinPMF U)
    {a₁ b₁ : C₁.Setup} {a₂ b₂ : C₂.Setup}
    (ha₁ : C₁.Realized a₁) (hb₁ : C₁.Realized b₁) (hne₁ : a₁ ≠ b₁)
    (hall₁ : ∀ w : U, C₁.setup w = a₁ ∨ C₁.setup w = b₁)
    (hpa₁ : 0 < setupMass p C₁ a₁) (hpb₁ : 0 < setupMass p C₁ b₁)
    (ha₂ : C₂.Realized a₂) (hb₂ : C₂.Realized b₂) (hne₂ : a₂ ≠ b₂)
    (hall₂ : ∀ w : U, C₂.setup w = a₂ ∨ C₂.setup w = b₂)
    (hpa₂ : 0 < setupMass p C₂ a₂) (hpb₂ : 0 < setupMass p C₂ b₂)
    (hind : StatisticallyIndependent p C₁.setup C₂.setup) :
    inferenceAccuracy C₁ p C₂.concl * inferenceAccuracy C₂ p C₁.concl ≤
      ⨆ z : Prop6Quadruple,
        prop6Expr (setupMass p C₁ a₁) (setupMass p C₂ a₂) z :=
  prop6_product_le_iSup C₁ C₂ p ha₁ hb₁ hne₁ hall₁ hpa₁ hpb₁ ha₂ hb₂ hne₂ hall₂
    hpa₂ hpb₂
    (prop6Law_of_independent p C₁ C₂ ha₁ hb₁ hne₁ hall₁ hpa₁ hpb₁
      ha₂ hb₂ hne₂ hall₂ hpa₂ hpb₂ hind)

end AISafetyAtlas.Inference
