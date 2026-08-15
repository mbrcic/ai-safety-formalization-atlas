module

public import AISafetyAtlas.Inference.Stochastic.Bounds

/-!
# Is Proposition 8's bound attained?

Proposition 8 bounds covariance accuracy below by
`(2 − |Γ(U)|) max_x E_P(Y ∣ x) / |Γ(U)|`, and the source follows it with:

> *"This bound is sharp, as can be seen from the following example."*
>
> **Example 6.** *"Fix some device `D` and a value `|Γ(U)| < ∞`. Next divide each
> cell of the partition `X × Y` into `|Γ(U)|` parts and assign them equal
> probability. Also map those cells to `1, …, |Γ(U)|` … For any `x ∈ X(U)`,
> `γ ∈ Γ(U)` and associated probe `δ_γ`,
> `E_P(Yδ_γ(Γ) ∣ x) = (2 − |Γ(U)|) E_P(Y ∣ x) / |Γ(U)|`. We can use this to
> evaluate `M_γ := max_x [E_P(Yδ_γ(Γ) ∣ x)] = (2 − |Γ(U)|) max_x [E_P(Y ∣ x)] /
> |Γ(U)|`. Since this is the same for all probe parameter values `γ`,
> `cov(D, Γ) = (2 − |Γ(U)|) max_x [E_P(Y ∣ x)] / |Γ(U)|`, which establishes the
> claim."*

**The pointwise identity is right. The step after it is not.**

## The sign

Write `c = (2 − |Γ(U)|)/|Γ(U)|`, so the identity reads
`E_P(Yδ_γ(Γ) ∣ x) = c · E_P(Y ∣ x)`. Passing to the maximum,

`max_x [c · E_P(Y ∣ x)] = c · max_x [E_P(Y ∣ x)]` **only when `c ≥ 0`**;

for `c < 0` the maximum of a negative multiple is taken at the **minimum**, so
the correct value is `c · min_x [E_P(Y ∣ x)]`. And `c < 0` exactly when
`|Γ(U)| ≥ 3` — which the source's own footnote to Proposition 8 points out is
the interesting range, since at `|Γ(U)| = 2` the factor is zero.

So Example 6 computes the accuracy correctly only when `E_P(Y ∣ x)` does not
depend on `x` (or when `|Γ(U)| = 2`, where both sides vanish). Otherwise it
overstates how small the accuracy is, and the bound it claims to attain is *not*
attained. Recorded as clash 25.

## What is checked here

`ex6Device` follows the source's recipe exactly — four `X × Y` cells, each split
into `|Γ(U)| = 3` equal-probability parts carrying the three target values — and
differs from Example 6 in one respect only: the mass is arranged so that
`E_P(Y ∣ x)` is **not** constant in `x`. It takes `0` at one setup and `1/3` at
the other.

* `ex6_accuracy` — the true accuracy is `0`;
* `ex6_prop8_bound` — Proposition 8's bound is `−1/9`;
* `ex6_bound_not_attained` — they differ, so this instance of the source's own
  construction does not attain the bound.

Proposition 8 itself is untouched: `0 > −1/9`, so the inequality holds. What
fails is the claim of sharpness *via this construction*, for a device whose
inference power varies across setups.
-/

namespace AISafetyAtlas.Inference

/-! ## The construction

Twelve states: cells `(x, y) ∈ {t, f} × {T, F}`, each split into three parts
carrying `Γ = 0, 1, 2`.
-/

/-- Setup: the first six states, then the last six. -/
public abbrev ex6X : Fin 12 → Bool :=
  ![true, true, true, true, true, true, false, false, false, false, false, false]

/-- Conclusion: `T` on the first half of each setup fibre, `F` on the second. -/
public abbrev ex6Y : Fin 12 → Bool :=
  ![true, true, true, false, false, false, true, true, true, false, false, false]

/-- Target: the three parts of every cell, exactly as the source prescribes. -/
public abbrev ex6Gamma : Fin 12 → Fin 3 :=
  ![0, 1, 2, 0, 1, 2, 0, 1, 2, 0, 1, 2]

/-- Equal mass within every cell — the source's requirement — with cell totals
`1/5, 1/5, 2/5, 1/5`. That makes `E_P(Y ∣ t) = 0` and `E_P(Y ∣ f) = 1/3`, which
is the only way this differs from Example 6. -/
public noncomputable def ex6Mass : Fin 12 → ℝ :=
  ![1/15, 1/15, 1/15, 1/15, 1/15, 1/15, 2/15, 2/15, 2/15, 1/15, 1/15, 1/15]

public noncomputable def ex6PMF : FinPMF (Fin 12) where
  mass := ex6Mass
  nonneg := by intro u; fin_cases u <;> simp only [ex6Mass] <;> norm_num
  sum_one := by simp [ex6Mass, Fin.sum_univ_succ]; norm_num

public abbrev ex6Device : InferenceDevice.{0, 0} (Fin 12) :=
  { Setup := Bool, setup := ex6X, concl := ex6Y, concl_surjective := by decide }

/-! ## Both sides, computed -/

private theorem sup'_pair {α : Type w} [DecidableEq α] {a b : α} (f : α → ℝ)
    (h : ({a, b} : Finset α).Nonempty) :
    ({a, b} : Finset α).sup' h f = max (f a) (f b) := by
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun x hx => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup' _ (by simp)) (Finset.le_sup' _ (by simp))

public theorem ex6_mass_true : pushOnImage ex6PMF ex6X true = 2 / 5 := by
  simp [pushOnImage, ex6PMF, ex6Mass, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

public theorem ex6_mass_false : pushOnImage ex6PMF ex6X false = 3 / 5 := by
  simp [pushOnImage, ex6PMF, ex6Mass, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

public theorem ex6_positiveMassSetups :
    positiveMassSetups ex6Device ex6PMF = {true, false} := by
  refine positiveMassSetups_eq_pair ex6Device ex6PMF ⟨0, rfl⟩ ⟨6, rfl⟩
    (fun w => (Bool.dichotomy (ex6Device.setup w)).elim Or.inr Or.inl) ?_ ?_
  · rw [show ex6Device.setup = ex6X from rfl, ex6_mass_true]; norm_num
  · rw [show ex6Device.setup = ex6X from rfl, ex6_mass_false]; norm_num

/-- `E_P(Y ∣ t) = 0`: the two conclusions carry equal mass on that fibre. -/
public theorem ex6_condExpect_Y_true :
    condExpect ex6PMF ex6X true (fun u => boolPm (ex6Y u)) = 0 := by
  have hw := ex6_mass_true
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg (by norm_num)]
  simp [ex6PMF, ex6Mass, boolPm, Finset.sum_filter, Fin.sum_univ_succ]

/-- `E_P(Y ∣ f) = 1/3`: the device's inference power differs across setups, which
is the whole point of the instance. -/
public theorem ex6_condExpect_Y_false :
    condExpect ex6PMF ex6X false (fun u => boolPm (ex6Y u)) = 1 / 3 := by
  have hw := ex6_mass_false
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg (by norm_num), div_eq_iff (by norm_num : (3 : ℝ) / 5 ≠ 0)]
  simp [ex6PMF, ex6Mass, boolPm, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

/-- The source's pointwise identity at the first setup: `c · 0 = 0`. -/
public theorem ex6_condExpect_probe_true (γ : Fin 3) :
    condExpect ex6PMF ex6X true
      (fun u => boolPm (ex6Y u) * boolPm (probe γ (ex6Gamma u))) = 0 := by
  have hw := ex6_mass_true
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg (by norm_num)]
  fin_cases γ <;>
    simp [ex6PMF, ex6Mass, boolPm, probe, Finset.sum_filter, Fin.sum_univ_succ]

/-- And at the second: `c · (1/3) = −1/9`. -/
public theorem ex6_condExpect_probe_false (γ : Fin 3) :
    condExpect ex6PMF ex6X false
      (fun u => boolPm (ex6Y u) * boolPm (probe γ (ex6Gamma u))) = -(1 / 9) := by
  have hw := ex6_mass_false
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg (by norm_num), div_eq_iff (by norm_num : (3 : ℝ) / 5 ≠ 0)]
  fin_cases γ <;>
    simp [ex6PMF, ex6Mass, boolPm, probe, Finset.sum_filter, Fin.sum_univ_succ] <;>
    norm_num

public theorem ex6_realizedValues : realizedValues ex6Gamma = Finset.univ := by
  ext γ
  simp only [Finset.mem_univ, iff_true, mem_realizedValues]
  fin_cases γ
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

/-! ## The verdict

The pointwise identity the source derives is **correct** here: with
`c = (2 − 3)/3 = −1/3`, the computations above give `0 = c · 0` at the first
setup and `−1/9 = c · (1/3)` at the second. What fails is the next line.
-/

/-- **The true accuracy is `0`.** For every probe the maximum over setups is
attained at the setup where `E_P(Y ∣ x)` is *smallest*, because the factor `c` is
negative. -/
public theorem ex6_accuracy : inferenceAccuracy ex6Device ex6PMF ex6Gamma = 0 := by
  have hcard : (realizedValues ex6Gamma).card = 3 := by rw [ex6_realizedValues]; decide
  have hne : ((realizedValues ex6Gamma).card : ℝ) ≠ 0 := by rw [hcard]; norm_num
  have hunfold : inferenceAccuracy ex6Device ex6PMF ex6Gamma =
      (realizedValues ex6Gamma).sum (fun γ =>
        (positiveMassSetups ex6Device ex6PMF).sup'
          (positiveMassSetups_nonempty ex6Device ex6PMF)
          (fun x => condExpect ex6PMF ex6Device.setup x
            (fun u => boolPm (ex6Device.concl u) * boolPm (probe γ (ex6Gamma u))))) /
        ((realizedValues ex6Gamma).card : ℝ) := by
    unfold inferenceAccuracy realizedValues
    rw [if_neg (by exact_mod_cast hne)]
  rw [hunfold]
  have hterm : ∀ γ : Fin 3,
      (positiveMassSetups ex6Device ex6PMF).sup'
        (positiveMassSetups_nonempty ex6Device ex6PMF)
        (fun x => condExpect ex6PMF ex6Device.setup x
          (fun u => boolPm (ex6Device.concl u) * boolPm (probe γ (ex6Gamma u)))) = 0 := by
    intro γ
    have hmem : true ∈ positiveMassSetups ex6Device ex6PMF := by
      rw [ex6_positiveMassSetups]; simp
    have hval : condExpect ex6PMF ex6Device.setup true
        (fun u => boolPm (ex6Device.concl u) * boolPm (probe γ (ex6Gamma u))) = 0 :=
      ex6_condExpect_probe_true γ
    refine le_antisymm (Finset.sup'_le _ _ (fun x _ => ?_)) ?_
    · cases x
      · rw [show ex6Device.setup = ex6X from rfl, ex6_condExpect_probe_false γ]; norm_num
      · rw [show ex6Device.setup = ex6X from rfl, ex6_condExpect_probe_true γ]
    · rw [← hval]
      exact Finset.le_sup'
        (fun x => condExpect ex6PMF ex6Device.setup x
          (fun u => boolPm (ex6Device.concl u) * boolPm (probe γ (ex6Gamma u)))) hmem
  rw [Finset.sum_congr rfl (fun γ _ => hterm γ)]
  simp

/-- **Proposition 8's bound here is `−1/9`.** -/
public theorem ex6_prop8_bound :
    ((2 - ((realizedValues ex6Gamma).card : ℝ)) *
        (positiveMassSetups ex6Device ex6PMF).sup'
          (positiveMassSetups_nonempty ex6Device ex6PMF)
          (fun x => condExpect ex6PMF ex6Device.setup x
            (fun u => boolPm (ex6Device.concl u)))) /
      ((realizedValues ex6Gamma).card : ℝ) = -(1 / 9) := by
  have hcard : (realizedValues ex6Gamma).card = 3 := by rw [ex6_realizedValues]; decide
  have hmem : false ∈ positiveMassSetups ex6Device ex6PMF := by
    rw [ex6_positiveMassSetups]; simp
  have hsup : (positiveMassSetups ex6Device ex6PMF).sup'
      (positiveMassSetups_nonempty ex6Device ex6PMF)
      (fun x => condExpect ex6PMF ex6Device.setup x
        (fun u => boolPm (ex6Device.concl u))) = 1 / 3 := by
    have hval : condExpect ex6PMF ex6Device.setup false
        (fun u => boolPm (ex6Device.concl u)) = 1 / 3 := ex6_condExpect_Y_false
    refine le_antisymm (Finset.sup'_le _ _ (fun x _ => ?_)) ?_
    · cases x
      · rw [show ex6Device.setup = ex6X from rfl, ex6_condExpect_Y_false]
      · rw [show ex6Device.setup = ex6X from rfl, ex6_condExpect_Y_true]; norm_num
    · rw [← hval]
      exact Finset.le_sup'
        (fun x => condExpect ex6PMF ex6Device.setup x
          (fun u => boolPm (ex6Device.concl u))) hmem
  rw [hcard, hsup]
  norm_num

/--
**Example 6 does not attain Proposition 8's bound here.** The accuracy is `0`
and the bound is `−1/9`.

Proposition 8 itself is unaffected — `−1/9 < 0`, so the inequality holds, as
`inferenceAccuracy_ge` independently guarantees. What fails is the claim that
this construction *attains* it, and with it the claim of sharpness for any
`|Γ(U)| ≥ 3` and any device whose inference power varies across setups.
-/
public theorem ex6_bound_not_attained :
    ((2 - ((realizedValues ex6Gamma).card : ℝ)) *
        (positiveMassSetups ex6Device ex6PMF).sup'
          (positiveMassSetups_nonempty ex6Device ex6PMF)
          (fun x => condExpect ex6PMF ex6Device.setup x
            (fun u => boolPm (ex6Device.concl u)))) /
      ((realizedValues ex6Gamma).card : ℝ)
      < inferenceAccuracy ex6Device ex6PMF ex6Gamma := by
  rw [ex6_prop8_bound, ex6_accuracy]
  norm_num

/-- Proposition 8 still holds on this instance, as it must. -/
public theorem ex6_prop8_holds :
    ((2 - ((realizedValues ex6Gamma).card : ℝ)) *
        (positiveMassSetups ex6Device ex6PMF).sup'
          (positiveMassSetups_nonempty ex6Device ex6PMF)
          (fun x => condExpect ex6PMF ex6Device.setup x
            (fun u => boolPm (ex6Device.concl u)))) /
      ((realizedValues ex6Gamma).card : ℝ)
      ≤ inferenceAccuracy ex6Device ex6PMF ex6Gamma :=
  inferenceAccuracy_ge ex6Device ex6PMF ex6Gamma

end AISafetyAtlas.Inference
