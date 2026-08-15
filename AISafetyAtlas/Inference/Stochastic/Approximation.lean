module

public import AISafetyAtlas.Inference.Stochastic
public import AISafetyAtlas.Inference.Stochastic.Bounds

/-!
# Approximate inference: which impossibility results survive a measure

Two of the deterministic results are measured here against covariance accuracy,
and neither survives.

**Theorem 2(i) / 2018 Proposition 4(i)** — `weaklyInfers_of_stronglyInfers` —
says a device that strongly infers another inherits everything the other infers.
In accuracy terms that reads *"if `D′ ≫ D` and `cov(D, Γ) = 1` then
`cov(D′, Γ) = 1`"*. Proposition 9 shows the implication has no approximate form
at all: `cov(D, Γ)` can be arbitrarily close to 1 while `cov(D′, Γ)` is exactly
zero. The reason is visible in the construction — the setup value under which
`D′` emulates `D` may be precisely the one on which `D` performs badly.

**Theorem 1** — `not_infersDevice_both_of_distinguishable` — says no two
distinguishable devices weakly infer each other, and it is the result the
registry advertises. It is a statement about *exact* inference, and this module
is the measurement of what happens to it when inference is allowed to be
approximate.

The answer is that it does not survive at all. Under Definition 9 covariance
accuracy, two setup-distinguishable devices can each infer the other to within
any `ε`. The theorem is exactly, and only exactly, true.

This is Wolpert 2018 Proposition 10, whose printed proof is the sixteen-state
Figure 6: two devices and a one-parameter family of distributions with
`0 < b < 1/6` and `a = (1 − 6b)/2`. The eight zero-mass states are not padding —
they are what makes the two setups *distinguishable*, which is a condition on the
setup functions and not on the measure.

## Sharper than the printed statement

The source says the accuracies can be made "arbitrarily close to 1" and takes
`b → 0`. `fig6_accuracy_dev1` and `fig6_accuracy_dev2` instead compute both
accuracies exactly, as the identity `(1 − 6b)/(1 − 4b)` in `b`, so the limit
claim follows from algebra rather than from an estimate, and
`fig6_accuracy_near_one` names the `b` that achieves a given `ε` outright.
-/

namespace AISafetyAtlas.Inference

open Finset


/-- Figure 6, column `X`: `+1` on the first eight states, `−1` on the rest. -/
public abbrev fig6X : Fin 16 → Bool :=
  ![true, true, true, true, true, true, true, true,
    false, false, false, false, false, false, false, false]

/-- Figure 6, column `Y`. -/
public abbrev fig6Y : Fin 16 → Bool :=
  ![true, true, false, false, true, true, false, false,
    true, true, false, false, true, true, false, false]

/-- Figure 6, column `X′`. -/
public abbrev fig6X' : Fin 16 → Bool :=
  ![true, true, true, true, false, false, false, false,
    true, true, true, true, false, false, false, false]

/-- Figure 6, column `Y′`. -/
public abbrev fig6Y' : Fin 16 → Bool :=
  ![true, false, true, false, true, false, true, false,
    true, false, true, false, true, false, true, false]

/-- Figure 6, column `P`, with `a = (1 − 6b)/2` written out. Two states carry `a`
and six carry `b`, so the masses sum to `2a + 6b = 1` identically in `b`. -/
public noncomputable def fig6Mass (b : ℝ) : Fin 16 → ℝ :=
  ![(1 - 6 * b) / 2, 0, 0, (1 - 6 * b) / 2, 0, b, b, 0,
    0, b, b, 0, 0, b, b, 0]

/-- The source's distribution, for `0 ≤ b ≤ 1/6`. -/
public noncomputable def fig6PMF (b : ℝ) (hb : 0 ≤ b) (hb6 : b ≤ 1 / 6) :
    FinPMF (Fin 16) where
  mass := fig6Mass b
  nonneg := by
    intro u
    fin_cases u <;> simp only [fig6Mass] <;> norm_num <;> linarith
  sum_one := by
    simp [fig6Mass, Fin.sum_univ_succ]
    ring

/-- `D` of Figure 6.

`abbrev` rather than `def` so that `fig6Dev1.Setup` reduces to `Bool` during
instance search: Definition 9's accuracy needs `DecidableEq` on the setup type,
and a `def` hides it behind a projection. -/
public abbrev fig6Dev1 : InferenceDevice.{0, 0} (Fin 16) :=
  { Setup := Bool, setup := fig6X, concl := fig6Y, concl_surjective := by decide }

/-- `D′` of Figure 6. -/
public abbrev fig6Dev2 : InferenceDevice.{0, 0} (Fin 16) :=
  { Setup := Bool, setup := fig6X', concl := fig6Y', concl_surjective := by decide }

/-- *"By inspection, `X` and `X′` are setup distinguishable."* All four pairs of
setup values occur, including at the zero-mass states — which is why they are in
the figure. -/
public theorem fig6_distinguishable : Distinguishable fig6Dev1 fig6Dev2 := by
  intro x₁ _ x₂ _
  -- States `M`, `I`, `E`, `A` of the figure. The first three carry mass zero,
  -- which is exactly why distinguishability is a condition on `X` and `X′` and
  -- not on `P`.
  cases x₁ <;> cases x₂
  · exact ⟨12, rfl, rfl⟩
  · exact ⟨8, rfl, rfl⟩
  · exact ⟨4, rfl, rfl⟩
  · exact ⟨0, rfl, rfl⟩

/-! ### The four conditional expectations

`g = Y · Y′` in the source's `±1` coding. The paper reports
`E_P(YY′ ∣ X = 1) = (a − b)/(a + b)` and `E_P(YY′ ∣ X = −1) = −1`, and these are
those two numbers with `a = (1 − 6b)/2` substituted.
-/

/-- `g = Y · Y′`, the product whose conditional expectations the source computes. -/
public noncomputable def fig6Prod : Fin 16 → ℝ :=
  fun u => boolPm (fig6Y u) * boolPm (fig6Y' u)

section Values

variable {b : ℝ} (hb : 0 ≤ b) (hb6 : b ≤ 1 / 6)

/-- `P(X = 1) = 2a + 2b = 1 − 4b`. -/
public theorem fig6_mass_X_true :
    pushOnImage (fig6PMF b hb hb6) fig6X true = 1 - 4 * b := by
  simp [pushOnImage, fig6PMF, fig6Mass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

/-- `P(X = −1) = 4b`. -/
public theorem fig6_mass_X_false :
    pushOnImage (fig6PMF b hb hb6) fig6X false = 4 * b := by
  simp [pushOnImage, fig6PMF, fig6Mass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

/-- `P(X′ = 1) = 1 − 4b`, by the column symmetry of the figure. -/
public theorem fig6_mass_X'_true :
    pushOnImage (fig6PMF b hb hb6) fig6X' true = 1 - 4 * b := by
  simp [pushOnImage, fig6PMF, fig6Mass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

/-- `P(X′ = −1) = 4b`. -/
public theorem fig6_mass_X'_false :
    pushOnImage (fig6PMF b hb hb6) fig6X' false = 4 * b := by
  simp [pushOnImage, fig6PMF, fig6Mass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

end Values

private theorem fig6_one_sub_four_pos {b : ℝ} (hb6 : b < 1 / 6) :
    (0 : ℝ) < 1 - 4 * b := by linarith

section Expectations

variable {b : ℝ} (hb : 0 < b) (hb6 : b < 1 / 6)

/-- *"`E_P(YY′ ∣ X = 1) = (a − b)/(a + b)`"*, which is `(1 − 8b)/(1 − 4b)`. -/
public theorem fig6_condExpect_X_true :
    condExpect (fig6PMF b hb.le hb6.le) fig6X true fig6Prod = (1 - 8 * b) / (1 - 4 * b) := by
  have hw := fig6_mass_X_true hb.le hb6.le
  have hne : (1 : ℝ) - 4 * b ≠ 0 := ne_of_gt (fig6_one_sub_four_pos hb6)
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg hne]
  congr 1
  simp [fig6PMF, fig6Mass, fig6Prod, boolPm, Finset.sum_filter, Fin.sum_univ_succ]
  ring

/-- *"`E_P(YY′ ∣ X = −1) = −1`"*: on the `X = −1` fibre the two conclusions
disagree at every state of positive mass. -/
public theorem fig6_condExpect_X_false :
    condExpect (fig6PMF b hb.le hb6.le) fig6X false fig6Prod = -1 := by
  have hw := fig6_mass_X_false hb.le hb6.le
  have hne : (4 : ℝ) * b ≠ 0 := by positivity
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg hne]
  rw [div_eq_iff hne]
  simp [fig6PMF, fig6Mass, fig6Prod, boolPm, Finset.sum_filter, Fin.sum_univ_succ]
  ring

/-- The same two numbers for `X′`, by the column symmetry of the figure. -/
public theorem fig6_condExpect_X'_true :
    condExpect (fig6PMF b hb.le hb6.le) fig6X' true fig6Prod = (1 - 8 * b) / (1 - 4 * b) := by
  have hw := fig6_mass_X'_true hb.le hb6.le
  have hne : (1 : ℝ) - 4 * b ≠ 0 := ne_of_gt (fig6_one_sub_four_pos hb6)
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg hne]
  congr 1
  simp [fig6PMF, fig6Mass, fig6Prod, boolPm, Finset.sum_filter, Fin.sum_univ_succ]
  ring

public theorem fig6_condExpect_X'_false :
    condExpect (fig6PMF b hb.le hb6.le) fig6X' false fig6Prod = -1 := by
  have hw := fig6_mass_X'_false hb.le hb6.le
  have hne : (4 : ℝ) * b ≠ 0 := by positivity
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg hne]
  rw [div_eq_iff hne]
  simp [fig6PMF, fig6Mass, fig6Prod, boolPm, Finset.sum_filter, Fin.sum_univ_succ]
  ring

end Expectations

/-! ### The accuracies, exactly

The source says *"plugging in yields `cov(D, D′) = cov(D, Y′) = a/(a + b)`"* and
then takes `b → 0`. With `a = (1 − 6b)/2` that ratio is `(1 − 6b)/(1 − 4b)`, and
it is computed here as an **identity in `b`** rather than estimated, so the
printed "arbitrarily close to 1" falls out of algebra.
-/

section Accuracy

variable {b : ℝ} (hb : 0 < b) (hb6 : b < 1 / 6)

private theorem fig6_dev1_hall (w : Fin 16) :
    fig6Dev1.setup w = true ∨ fig6Dev1.setup w = false :=
  (Bool.dichotomy (fig6Dev1.setup w)).elim Or.inr Or.inl

private theorem fig6_dev2_hall (w : Fin 16) :
    fig6Dev2.setup w = true ∨ fig6Dev2.setup w = false :=
  (Bool.dichotomy (fig6Dev2.setup w)).elim Or.inr Or.inl

/-- **`cov(D, D′) = (1 − 6b)/(1 − 4b)`.** -/
public theorem fig6_accuracy_dev1 :
    inferenceAccuracy fig6Dev1 (fig6PMF b hb.le hb6.le) fig6Dev2.concl
      = (1 - 6 * b) / (1 - 4 * b) := by
  have hpos := fig6_one_sub_four_pos hb6
  have hpa : 0 < pushOnImage (fig6PMF b hb.le hb6.le) fig6Dev1.setup true := by
    rw [show fig6Dev1.setup = fig6X from rfl, fig6_mass_X_true]; exact hpos
  have hpb : 0 < pushOnImage (fig6PMF b hb.le hb6.le) fig6Dev1.setup false := by
    rw [show fig6Dev1.setup = fig6X from rfl, fig6_mass_X_false]; linarith
  rw [inferenceAccuracy_eq_of_two_setups fig6Dev1 fig6Dev2 (fig6PMF b hb.le hb6.le)
    (show fig6Dev1.Realized true from ⟨0, rfl⟩)
    (show fig6Dev1.Realized false from ⟨8, rfl⟩) fig6_dev1_hall hpa hpb]
  rw [show (fun u => boolPm (fig6Dev1.concl u) * boolPm (fig6Dev2.concl u)) = fig6Prod from rfl,
    show fig6Dev1.setup = fig6X from rfl,
    fig6_condExpect_X_true hb hb6, fig6_condExpect_X_false hb hb6]
  have h4 : (1 : ℝ) - 4 * b ≠ 0 := ne_of_gt hpos
  have hgap : (1 - 8 * b) / (1 - 4 * b) - -1 = (2 - 12 * b) / (1 - 4 * b) := by
    rw [sub_neg_eq_add, div_add_one h4]
    congr 1
    ring
  rw [hgap, abs_of_nonneg (div_nonneg (by linarith) hpos.le)]
  field_simp
  ring

/-- **`cov(D′, D) = (1 − 6b)/(1 − 4b)`** — *"by symmetry of the columns in
Fig. 6"*, which is here a second computation rather than an appeal. -/
public theorem fig6_accuracy_dev2 :
    inferenceAccuracy fig6Dev2 (fig6PMF b hb.le hb6.le) fig6Dev1.concl
      = (1 - 6 * b) / (1 - 4 * b) := by
  have hpos := fig6_one_sub_four_pos hb6
  have hpa : 0 < pushOnImage (fig6PMF b hb.le hb6.le) fig6Dev2.setup true := by
    rw [show fig6Dev2.setup = fig6X' from rfl, fig6_mass_X'_true]; exact hpos
  have hpb : 0 < pushOnImage (fig6PMF b hb.le hb6.le) fig6Dev2.setup false := by
    rw [show fig6Dev2.setup = fig6X' from rfl, fig6_mass_X'_false]; linarith
  rw [inferenceAccuracy_eq_of_two_setups fig6Dev2 fig6Dev1 (fig6PMF b hb.le hb6.le)
    (show fig6Dev2.Realized true from ⟨0, rfl⟩)
    (show fig6Dev2.Realized false from ⟨4, rfl⟩) fig6_dev2_hall hpa hpb]
  rw [show (fun u => boolPm (fig6Dev2.concl u) * boolPm (fig6Dev1.concl u)) =
      fig6Prod from funext (fun u => mul_comm _ _),
    show fig6Dev2.setup = fig6X' from rfl,
    fig6_condExpect_X'_true hb hb6, fig6_condExpect_X'_false hb hb6]
  have h4 : (1 : ℝ) - 4 * b ≠ 0 := ne_of_gt hpos
  have hgap : (1 - 8 * b) / (1 - 4 * b) - -1 = (2 - 12 * b) / (1 - 4 * b) := by
    rw [sub_neg_eq_add, div_add_one h4]
    congr 1
    ring
  rw [hgap, abs_of_nonneg (div_nonneg (by linarith) hpos.le)]
  field_simp
  ring

end Accuracy

/--
**Wolpert 2018, Proposition 10.** *"There are devices `D` and `D′` with `X` and
`X′` setup-distinguishable and a distribution `P` where both `cov(D, D′)` and
`cov(D′, D)` are arbitrarily close to 1."*

Put beside `not_infersDevice_both_of_distinguishable` — 2008 Theorem 1, *"no two
distinguishable devices can each infer the other"* — this says that theorem has
no approximate version. Exact mutual inference between distinguishable devices is
impossible; mutual inference to within any `ε` is not.

The source takes `b → 0`. Here `b := ε / (4 + 8ε)` is named outright, so nothing
is left to a limit: it satisfies `0 < b < 1/6` for every `ε > 0`, and
`fig6_accuracy_dev1` and `fig6_accuracy_dev2` then give both accuracies as the
same exact ratio.
-/
public theorem fig6_accuracy_near_one {ε : ℝ} (hε : 0 < ε) :
    ∃ (b : ℝ) (hb : 0 < b) (hb6 : b < 1 / 6),
      Distinguishable fig6Dev1 fig6Dev2 ∧
      1 - ε < inferenceAccuracy fig6Dev1 (fig6PMF b hb.le hb6.le) fig6Dev2.concl ∧
      1 - ε < inferenceAccuracy fig6Dev2 (fig6PMF b hb.le hb6.le) fig6Dev1.concl := by
  have hden : (0 : ℝ) < 4 + 8 * ε := by linarith
  refine ⟨ε / (4 + 8 * ε), div_pos hε hden, ?_, fig6_distinguishable, ?_, ?_⟩
  · rw [div_lt_iff₀ hden]; linarith
  all_goals
    set b : ℝ := ε / (4 + 8 * ε) with hbdef
    have hb : 0 < b := div_pos hε hden
    have hb6 : b < 1 / 6 := by rw [hbdef, div_lt_iff₀ hden]; linarith
    have hpos := fig6_one_sub_four_pos hb6
    have hbe : b * (2 + 4 * ε) = ε / 2 := by rw [hbdef]; field_simp; ring
    have hkey : 1 - ε < (1 - 6 * b) / (1 - 4 * b) := by
      rw [lt_div_iff₀ hpos]
      nlinarith [hbe, hε]
    first
      | rw [fig6_accuracy_dev1 hb hb6]; exact hkey
      | rw [fig6_accuracy_dev2 hb hb6]; exact hkey

/--
The same statement with the devices genuinely quantified, which is how the source
writes it. The `DecidableEq` on the setup type has to be bound explicitly:
Definition 9's accuracy needs it, and a device bound by an existential carries no
instance. Its value does not depend on which instance is supplied.
-/
public theorem exists_distinguishable_accuracy_near_one {ε : ℝ} (hε : 0 < ε) :
    ∃ (D₁ D₂ : InferenceDevice.{0, 0} (Fin 16)) (i₁ : DecidableEq D₁.Setup)
      (i₂ : DecidableEq D₂.Setup) (p : FinPMF (Fin 16)),
      Distinguishable D₁ D₂ ∧
      1 - ε < @inferenceAccuracy (Fin 16) _ D₁ i₁ Bool _ _ p D₂.concl ∧
      1 - ε < @inferenceAccuracy (Fin 16) _ D₂ i₂ Bool _ _ p D₁.concl := by
  obtain ⟨b, hb, hb6, hdist, h1, h2⟩ := fig6_accuracy_near_one hε
  exact ⟨fig6Dev1, fig6Dev2, inferInstance, inferInstance, fig6PMF b hb.le hb6.le,
    hdist, h1, h2⟩

/-! ## Proposition 9

The source's Figure 5: ten states, a target `Γ`, two devices with `D′ ≫ D`, and
a one-parameter family of distributions with `0 ≤ p ≤ 1`. Eight states share the
mass `(1 − p)/8` and the last two carry `p/2` each, so the total is `1` for every
`p`.

The two states carrying the mass `p` are what makes `cov(D, Γ)` large. They are
also the two that `D′` separates into its fifth setup value — the one the strong
inference never uses — which is exactly the source's explanation of why `D′`
inherits nothing.
-/

section Prop9

/-- Figure 5, column `X`. -/
public abbrev fig5X : Fin 10 → Bool :=
  ![true, true, true, true, false, false, false, false, true, false]

/-- Figure 5, column `Y`. -/
public abbrev fig5Y : Fin 10 → Bool :=
  ![true, false, true, false, true, false, true, false, true, false]

/-- Figure 5, column `X′`, which takes five values where `X` takes two. -/
public abbrev fig5X' : Fin 10 → Fin 5 :=
  ![0, 0, 1, 1, 2, 2, 3, 3, 4, 4]

/-- Figure 5, column `Y′`. -/
public abbrev fig5Y' : Fin 10 → Bool :=
  ![true, false, false, true, true, false, false, true, true, false]

/-- Figure 5, column `Γ`. -/
public abbrev fig5Gamma : Fin 10 → Bool :=
  ![true, true, true, true, false, false, false, false, true, true]

/-- Figure 5, column `P`. -/
public noncomputable def fig5Mass (p : ℝ) : Fin 10 → ℝ :=
  ![(1 - p) / 8, (1 - p) / 8, (1 - p) / 8, (1 - p) / 8,
    (1 - p) / 8, (1 - p) / 8, (1 - p) / 8, (1 - p) / 8, p / 2, p / 2]

/-- The source's distribution, for `0 ≤ p ≤ 1`. -/
public noncomputable def fig5PMF (p : ℝ) (h0 : 0 ≤ p) (h1 : p ≤ 1) : FinPMF (Fin 10) where
  mass := fig5Mass p
  nonneg := by
    intro u
    fin_cases u <;> simp only [fig5Mass] <;> norm_num <;> linarith
  sum_one := by
    simp [fig5Mass, Fin.sum_univ_succ]
    ring

/-- `D` of Figure 5. -/
public abbrev fig5Dev1 : InferenceDevice.{0, 0} (Fin 10) :=
  { Setup := Bool, setup := fig5X, concl := fig5Y, concl_surjective := by decide }

/-- `D′` of Figure 5. Five setup values, and the fifth is the one the strong
inference below never selects. -/
public abbrev fig5Dev2 : InferenceDevice.{0, 0} (Fin 10) :=
  { Setup := Fin 5, setup := fig5X', concl := fig5Y', concl_surjective := by decide }

/-- `Γ` presented as a device, so that Definition 9's accuracy — which is stated
against a device's conclusion — applies to it. The setup is trivial and is never
used; only `concl` is read. -/
public abbrev fig5Target : InferenceDevice.{0, 0} (Fin 10) :=
  { Setup := Unit, setup := fun _ => (), concl := fig5Gamma, concl_surjective := by decide }

/-- *"To verify that `D′ ≫ D`, for the 1-probe, for `x = 1, 2` choose
`x′ = 1, 3`; for the −1-probe, for `x = 1, 2` choose `x′ = 2, 4`."* The fifth
setup value of `D′` is never chosen — it is the one whose fibre carries the mass
`p`, and where `X` is not even constant. -/
public theorem fig5_stronglyInfers : StronglyInfers fig5Dev2 fig5Dev1 := by
  intro γ f hf _ x₂ _
  have hfeq : f = probe γ := IsProbe.eq_of_isProbe hf (isProbe_probe γ)
  subst hfeq
  -- `x′ = 1, 3` for the identity probe and `x′ = 2, 4` for the negation probe,
  -- zero-indexed.
  cases γ <;> cases x₂
  · exact ⟨3, ⟨6, rfl⟩, by decide⟩
  · exact ⟨1, ⟨2, rfl⟩, by decide⟩
  · exact ⟨2, ⟨4, rfl⟩, by decide⟩
  · exact ⟨0, ⟨0, rfl⟩, by decide⟩

section Values

variable {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1)

private theorem fig5_mass_X_true :
    pushOnImage (fig5PMF p h0 h1) fig5X true = 1 / 2 := by
  simp [pushOnImage, fig5PMF, fig5Mass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

private theorem fig5_mass_X_false :
    pushOnImage (fig5PMF p h0 h1) fig5X false = 1 / 2 := by
  simp [pushOnImage, fig5PMF, fig5Mass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

/-- `g = Y · Γ`, whose conditional expectations the source evaluates. -/
public noncomputable def fig5Prod : Fin 10 → ℝ :=
  fun u => boolPm (fig5Y u) * boolPm (fig5Gamma u)

/-- *"For the 1-probe, `max_x E_P(Y δ₁(Γ) ∣ x) = p`, the maximum occurring for
`x = 1`."* -/
private theorem fig5_condExpect_true :
    condExpect (fig5PMF p h0 h1) fig5X true fig5Prod = p := by
  have hw := fig5_mass_X_true h0 h1
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg (by norm_num)]
  rw [div_eq_iff (by norm_num : (1 : ℝ) / 2 ≠ 0)]
  simp [fig5PMF, fig5Mass, fig5Prod, boolPm, Finset.sum_filter, Fin.sum_univ_succ]
  ring

/-- *"Similarly, for the −1-probe, `max_x E_P(Y δ₋₁(Γ) ∣ x) = p`, the maximum
occurring for `x = 2`."* -/
private theorem fig5_condExpect_false :
    condExpect (fig5PMF p h0 h1) fig5X false fig5Prod = -p := by
  have hw := fig5_mass_X_false h0 h1
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg (by norm_num)]
  rw [div_eq_iff (by norm_num : (1 : ℝ) / 2 ≠ 0)]
  simp [fig5PMF, fig5Mass, fig5Prod, boolPm, Finset.sum_filter, Fin.sum_univ_succ]
  ring

end Values

/-- **`cov(D, Γ) = p`.** -/
public theorem fig5_accuracy_dev1 {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    inferenceAccuracy fig5Dev1 (fig5PMF p h0 h1) fig5Target.concl = p := by
  have hpa : 0 < pushOnImage (fig5PMF p h0 h1) fig5Dev1.setup true := by
    rw [show fig5Dev1.setup = fig5X from rfl, fig5_mass_X_true h0 h1]; norm_num
  have hpb : 0 < pushOnImage (fig5PMF p h0 h1) fig5Dev1.setup false := by
    rw [show fig5Dev1.setup = fig5X from rfl, fig5_mass_X_false h0 h1]; norm_num
  rw [inferenceAccuracy_eq_of_two_setups fig5Dev1 fig5Target (fig5PMF p h0 h1)
    (show fig5Dev1.Realized true from ⟨0, rfl⟩)
    (show fig5Dev1.Realized false from ⟨4, rfl⟩)
    (fun w => (Bool.dichotomy (fig5Dev1.setup w)).elim Or.inr Or.inl) hpa hpb]
  rw [show (fun u => boolPm (fig5Dev1.concl u) * boolPm (fig5Target.concl u)) =
      fig5Prod from rfl,
    show fig5Dev1.setup = fig5X from rfl,
    fig5_condExpect_true h0 h1, fig5_condExpect_false h0 h1]
  rw [show p - -p = 2 * p by ring, abs_of_nonneg (by linarith)]
  ring

/-- **`cov(D′, Γ) = 0`.** *"To see this for both probes, note that
`E_P(Y′ δ(Γ) ∣ x′) = 0` for each `x′`."* Every one of the five fibres splits its
mass evenly between agreement and disagreement, so every conditional expectation
vanishes and the maximum over setups is zero for both probes. -/
public theorem fig5_accuracy_dev2 {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    inferenceAccuracy fig5Dev2 (fig5PMF p h0 h1) fig5Target.concl = 0 := by
  classical
  have hzero : ∀ (γ : Bool) (x : Fin 5),
      condExpect (fig5PMF p h0 h1) fig5X' x
        (fun u => boolPm (fig5Y' u) * boolPm (probe γ (fig5Gamma u))) = 0 := by
    intro γ x
    have hnum : (Finset.univ.filter (fun u : Fin 10 => fig5X' u = x)).sum
        (fun u => (fig5PMF p h0 h1).mass u *
          (boolPm (fig5Y' u) * boolPm (probe γ (fig5Gamma u)))) = 0 := by
      fin_cases x <;> cases γ <;>
        simp [fig5PMF, fig5Mass, boolPm, probe, Finset.sum_filter, Fin.sum_univ_succ]
    unfold condExpect
    by_cases hw : (Finset.univ.filter (fun u : Fin 10 => fig5X' u = x)).sum
        (fig5PMF p h0 h1).mass = 0
    · simp [hw]
    · simp only [hw, if_false]
      rw [hnum, zero_div]
  have hsup : ∀ γ : Bool,
      (positiveMassSetups fig5Dev2 (fig5PMF p h0 h1)).sup'
        (positiveMassSetups_nonempty fig5Dev2 (fig5PMF p h0 h1))
        (fun x => condExpect (fig5PMF p h0 h1) fig5Dev2.setup x
          (fun u => boolPm (fig5Dev2.concl u) *
            boolPm (probe γ (fig5Target.concl u)))) = 0 := by
    intro γ
    have hfun : (fun x => condExpect (fig5PMF p h0 h1) fig5Dev2.setup x
        (fun u => boolPm (fig5Dev2.concl u) *
          boolPm (probe γ (fig5Target.concl u)))) = fun _ => (0 : ℝ) :=
      funext (hzero γ)
    rw [hfun, Finset.sup'_const]
  unfold inferenceAccuracy
  simp only [hsup, Finset.sum_const, smul_zero, zero_div, ite_self]

/--
**Wolpert 2018, Proposition 9.** *"There are devices `D`, `D′`, probability
distribution `P` defined over `U`, and function `Γ`, such that `D′ ≫ D` and
`cov(D, Γ)` is arbitrarily close to 1.0 while `cov(D′, Γ) = 0`."*

Put beside `weaklyInfers_of_stronglyInfers` — 2008 Theorem 2(i), *"strong
inference inherits everything weak inference gets"* — this says that inheritance
has no approximate form. Exact inference is inherited; inference of accuracy
`1 − ε` is inherited to accuracy exactly zero, for every `ε`.

The source takes `p → 1`. Here `p := 1 − min ε 1 / 2` is named outright: it lies
in `[1/2, 1)` for every `ε > 0`, and `fig5_accuracy_dev1` then gives
`cov(D, Γ) = p` exactly rather than as a limit.
-/
public theorem fig5_accuracy_gap {ε : ℝ} (hε : 0 < ε) :
    ∃ (q : ℝ) (h0 : 0 ≤ q) (h1 : q ≤ 1),
      StronglyInfers fig5Dev2 fig5Dev1 ∧
      1 - ε < inferenceAccuracy fig5Dev1 (fig5PMF q h0 h1) fig5Target.concl ∧
      inferenceAccuracy fig5Dev2 (fig5PMF q h0 h1) fig5Target.concl = 0 := by
  have hmin0 : 0 < min ε 1 := lt_min hε one_pos
  have hmin1 : min ε 1 ≤ 1 := min_le_right _ _
  have hminε : min ε 1 ≤ ε := min_le_left _ _
  refine ⟨1 - min ε 1 / 2, by linarith, by linarith, fig5_stronglyInfers, ?_, ?_⟩
  · rw [fig5_accuracy_dev1]
    linarith
  · exact fig5_accuracy_dev2 _ _


end Prop9

end AISafetyAtlas.Inference
