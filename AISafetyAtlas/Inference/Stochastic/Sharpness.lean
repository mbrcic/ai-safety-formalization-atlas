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
depend on `x` (or when `|Γ(U)| = 2`, where both sides vanish, or `|Γ(U)| = 1`,
where the factor is `+1`). Otherwise it
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

## The repair

Example 6's construction is `CellUniform`: every realized value of `Γ` takes a
`1/|Γ(U)|` share of every `X × Y` cell. For any device and distribution,
`refineDevice`/`refinePMF` with `Γ = Prod.snd` builds it by splitting each
universe into `n` equal-mass labelled copies (`refine_cellUniform`).

* `condExpect_probe_of_cellUniform` — the source's pointwise identity, proved for
  every cell-uniform `Γ`.
* **Corrected computation.** `inferenceAccuracy_eq_of_cellUniform`: for `|Γ(U)| ≥ 2`
  the accuracy is `(2 − |Γ(U)|) · min_x E_P(Y ∣ x) / |Γ(U)|`. `example6_accuracy`
  states the same for Example 6's split of an arbitrary device, in terms of that
  device's own `E_P(Y ∣ x)`. `example6_power_accuracy` instantiates it on a
  two-setup family with arbitrary `E_P(Y ∣ x) = e(x)`, and `ex6_accuracy_via_min`
  on the instance above.
* **When the bound is attained.** `example6_attains_prop8_bound_iff`: Example 6's
  split of any device attains Proposition 8's bound if and only if `n ≤ 2` or
  `max_x E_P(Y ∣ x) = min_x E_P(Y ∣ x)`. The general cell-uniform forms are
  `inferenceAccuracy_eq_prop8_bound_iff_of_cellUniform` (`|Γ(U)| ≥ 2`) and
  `inferenceAccuracy_eq_prop8_bound_of_card_eq_one` (`|Γ(U)| = 1`, where the
  factor is `+1`).
* **Sharpness restored.** `example6_attains_prop8_bound` and
  `inferenceAccuracy_eq_prop8_bound_of_cellUniform`: if `E_P(Y ∣ x)` does not
  depend on `x`, Example 6's construction attains the bound at every `|Γ(U)|`.
  `prop8_bound_sharp`: for every `n ≥ 1` and every `e ∈ [−1, 1]` there is a model
  with `|Γ(U)| = n`, two positive-mass setups, `E_P(Y ∣ x) = e` at both, and
  accuracy equal to the bound `(2 − n) e / n`.

So "this bound is sharp" holds at every finite `|Γ(U)|` and every value of
`max_x E_P(Y ∣ x)`. The printed computation of `cov(D, Γ)` holds exactly when
`|Γ(U)| ≤ 2` or `E_P(Y ∣ x)` is constant over the positive-mass setups.
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
this construction *attains* it at this device, whose inference power varies across
setups. The bound itself is sharp at every `|Γ(U)|`: see `prop8_bound_sharp`.
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

/-! ## The repair: Example 6 for a general device

Example 6's construction is a property of `Γ` relative to the device: inside every
cell of the `X × Y` partition, each realized value of `Γ` carries the same share
`1/|Γ(U)|` of the cell's mass. Under that property alone the source's pointwise
identity holds at every setup, and the accuracy is computed exactly — with the
minimum, not the maximum, once `|Γ(U)| ≥ 2`.
-/

section Repair

variable {U : Type u} [Fintype U]

/-- **Example 6's construction, as a hypothesis.** *"divide each cell of the
partition `X × Y` into `|Γ(U)|` parts and assign them equal probability. Also map
those cells to `1, …, |Γ(U)|`"*: every realized value of `Γ` takes exactly a
`1/|Γ(U)|` share of the mass of every `X × Y` cell. -/
@[expose] public def CellUniform (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    {G : Type v'} [Fintype G] [DecidableEq G] (p : FinPMF U) (Γ : U → G) : Prop :=
  ∀ (x : C.Setup) (y : Bool), ∀ γ ∈ realizedValues Γ,
    (Finset.univ.filter (fun u => C.setup u = x ∧ C.concl u = y ∧ Γ u = γ)).sum p.mass =
      (Finset.univ.filter (fun u => C.setup u = x ∧ C.concl u = y)).sum p.mass /
        ((realizedValues Γ).card : ℝ)

/-- **Example 6's pointwise identity, proved.**
`E_P(Yδ_γ(Γ) ∣ x) = (2 − |Γ(U)|) E_P(Y ∣ x) / |Γ(U)|` at every setup `x` and
every realized `γ`, for any cell-uniform `Γ`. This is the step of the source's
argument that is right. -/
public theorem condExpect_probe_of_cellUniform (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] {G : Type v'} [Fintype G] [DecidableEq G]
    (p : FinPMF U) (Γ : U → G) (h : CellUniform C p Γ) (x : C.Setup) {γ : G}
    (hγ : γ ∈ realizedValues Γ) :
    condExpect p C.setup x (fun u => boolPm (C.concl u) * boolPm (probe γ (Γ u))) =
      (2 - ((realizedValues Γ).card : ℝ)) / ((realizedValues Γ).card : ℝ) *
        condExpect p C.setup x (fun u => boolPm (C.concl u)) := by
  classical
  have hn : ((realizedValues Γ).card : ℝ) ≠ 0 := by
    have : 0 < (realizedValues Γ).card := Finset.card_pos.mpr ⟨γ, hγ⟩
    exact_mod_cast this.ne'
  have hBt := h x true γ hγ
  have hBf := h x false γ hγ
  rw [← condExpect_const_mul]
  unfold condExpect
  simp only
  split_ifs with hw
  · rfl
  · congr 1
    have hL : (Finset.univ.filter (fun u => C.setup u = x)).sum
          (fun u => p.mass u * (boolPm (C.concl u) * boolPm (probe γ (Γ u)))) =
        2 * ((Finset.univ.filter
              (fun u => C.setup u = x ∧ C.concl u = true ∧ Γ u = γ)).sum p.mass -
            (Finset.univ.filter
              (fun u => C.setup u = x ∧ C.concl u = false ∧ Γ u = γ)).sum p.mass) -
          ((Finset.univ.filter (fun u => C.setup u = x ∧ C.concl u = true)).sum p.mass -
            (Finset.univ.filter (fun u => C.setup u = x ∧ C.concl u = false)).sum p.mass) := by
      simp only [Finset.sum_filter]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum,
        ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases hx : C.setup u = x
      · by_cases hg : Γ u = γ <;> cases C.concl u <;> simp [hx, hg, boolPm, probe] <;> ring
      · simp [hx]
    have hR : (Finset.univ.filter (fun u => C.setup u = x)).sum
          (fun u => p.mass u * ((2 - ((realizedValues Γ).card : ℝ)) /
            ((realizedValues Γ).card : ℝ) * boolPm (C.concl u))) =
        (2 - ((realizedValues Γ).card : ℝ)) / ((realizedValues Γ).card : ℝ) *
          ((Finset.univ.filter (fun u => C.setup u = x ∧ C.concl u = true)).sum p.mass -
            (Finset.univ.filter (fun u => C.setup u = x ∧ C.concl u = false)).sum p.mass) := by
      simp only [Finset.sum_filter]
      rw [← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun u _ => ?_)
      by_cases hx : C.setup u = x
      · cases C.concl u <;> simp [hx, boolPm] <;> ring
      · simp [hx]
    rw [hL, hR, hBt, hBf]
    field_simp

/-- The maximum of a nonpositive multiple is that multiple of the minimum — the
step the source took with the wrong extremum. -/
private theorem sup'_nonpos_mul {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ)
    {c : ℝ} (hc : c ≤ 0) : s.sup' hs (fun i => c * f i) = c * s.inf' hs f := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i hi => mul_le_mul_of_nonpos_left (Finset.inf'_le _ hi) hc)
  · obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_inf' hs f
    rw [hieq]
    exact Finset.le_sup' (fun i => c * f i) hi

/-- And of a nonnegative multiple, that multiple of the maximum. -/
private theorem sup'_nonneg_mul {ι : Type*} {s : Finset ι} (hs : s.Nonempty) (f : ι → ℝ)
    {c : ℝ} (hc : 0 ≤ c) : s.sup' hs (fun i => c * f i) = c * s.sup' hs f := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun i hi => mul_le_mul_of_nonneg_left (Finset.le_sup' f hi) hc)
  · obtain ⟨i, hi, hieq⟩ := Finset.exists_mem_eq_sup' hs f
    rw [hieq]
    exact Finset.le_sup' (fun i => c * f i) hi

/-- Under cell-uniformity every probe contributes the same maximum, so the
accuracy is that one maximum. -/
private theorem inferenceAccuracy_eq_sup'_of_cellUniform (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] {G : Type v'} [Fintype G] [DecidableEq G]
    (p : FinPMF U) (Γ : U → G) (h : CellUniform C p Γ) :
    inferenceAccuracy C p Γ =
      (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
        (fun x => (2 - ((realizedValues Γ).card : ℝ)) / ((realizedValues Γ).card : ℝ) *
          condExpect p C.setup x (fun u => boolPm (C.concl u))) := by
  classical
  obtain ⟨w₀, -⟩ := C.concl_surjective true
  have hSne : (realizedValues Γ).Nonempty := ⟨Γ w₀, mem_realizedValues.mpr ⟨w₀, rfl⟩⟩
  have hcard : (0 : ℝ) < ((realizedValues Γ).card : ℝ) := by
    exact_mod_cast Finset.card_pos.mpr hSne
  have hunfold : inferenceAccuracy C p Γ =
      (realizedValues Γ).sum (fun γ =>
        (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
          (fun x => condExpect p C.setup x
            (fun u => boolPm (C.concl u) * boolPm (probe γ (Γ u))))) /
        ((realizedValues Γ).card : ℝ) := by
    unfold inferenceAccuracy realizedValues
    rw [if_neg (by exact_mod_cast hcard.ne')]
  have hterm : ∀ γ ∈ realizedValues Γ,
      (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
          (fun x => condExpect p C.setup x
            (fun u => boolPm (C.concl u) * boolPm (probe γ (Γ u)))) =
        (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
          (fun x => (2 - ((realizedValues Γ).card : ℝ)) / ((realizedValues Γ).card : ℝ) *
            condExpect p C.setup x (fun u => boolPm (C.concl u))) := by
    intro γ hγ
    simp_rw [condExpect_probe_of_cellUniform C p Γ h _ hγ]
  rw [hunfold, Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul,
    mul_div_cancel_left₀ _ hcard.ne']

/--
**Example 6, corrected computation.** For a cell-uniform `Γ` with `|Γ(U)| ≥ 2`,
`cov(D, Γ) = (2 − |Γ(U)|) · min_x E_P(Y ∣ x) / |Γ(U)|`.

The source printed `max_x`; the factor `(2 − |Γ(U)|)/|Γ(U)|` is nonpositive in this
range, so the maximum over setups of `c · E_P(Y ∣ x)` sits at the minimum of
`E_P(Y ∣ x)`. The minimum ranges over the same positive-mass setups as Proposition
8's maximum.
-/
public theorem inferenceAccuracy_eq_of_cellUniform (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] {G : Type v'} [Fintype G] [DecidableEq G]
    (p : FinPMF U) (Γ : U → G) (h : CellUniform C p Γ)
    (hn : 2 ≤ (realizedValues Γ).card) :
    inferenceAccuracy C p Γ =
      ((2 - ((realizedValues Γ).card : ℝ)) *
          (positiveMassSetups C p).inf' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))) /
        ((realizedValues Γ).card : ℝ) := by
  have hn' : (2 : ℝ) ≤ ((realizedValues Γ).card : ℝ) := by exact_mod_cast hn
  have hc : (2 - ((realizedValues Γ).card : ℝ)) / ((realizedValues Γ).card : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  rw [inferenceAccuracy_eq_sup'_of_cellUniform C p Γ h, sup'_nonpos_mul _ _ hc]
  ring

/-- **At `|Γ(U)| = 1` the factor is `+1`**, so the maximum is the right extremum
and every cell-uniform model attains Proposition 8's bound. -/
public theorem inferenceAccuracy_eq_prop8_bound_of_card_eq_one (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] {G : Type v'} [Fintype G] [DecidableEq G]
    (p : FinPMF U) (Γ : U → G) (h : CellUniform C p Γ)
    (hn : (realizedValues Γ).card = 1) :
    inferenceAccuracy C p Γ =
      ((2 - ((realizedValues Γ).card : ℝ)) *
          (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))) /
        ((realizedValues Γ).card : ℝ) := by
  rw [inferenceAccuracy_eq_sup'_of_cellUniform C p Γ h, hn]
  rw [sup'_nonneg_mul _ _ (by norm_num)]
  ring

/--
**When Example 6 attains Proposition 8's bound.** For a cell-uniform `Γ` with
`|Γ(U)| ≥ 2`, the accuracy equals the bound exactly when `|Γ(U)| = 2` (both
sides then vanish, whatever `E_P(Y ∣ x)` is) or `max_x E_P(Y ∣ x) = min_x
E_P(Y ∣ x)` over the positive-mass setups.
-/
public theorem inferenceAccuracy_eq_prop8_bound_iff_of_cellUniform
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    {G : Type v'} [Fintype G] [DecidableEq G]
    (p : FinPMF U) (Γ : U → G) (h : CellUniform C p Γ)
    (hn : 2 ≤ (realizedValues Γ).card) :
    inferenceAccuracy C p Γ =
        ((2 - ((realizedValues Γ).card : ℝ)) *
            (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
              (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))) /
          ((realizedValues Γ).card : ℝ) ↔
      (realizedValues Γ).card = 2 ∨
        (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u))) =
          (positiveMassSetups C p).inf' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u))) := by
  have hpos : ((realizedValues Γ).card : ℝ) ≠ 0 := by
    have : (2 : ℝ) ≤ ((realizedValues Γ).card : ℝ) := by exact_mod_cast hn
    linarith
  rw [inferenceAccuracy_eq_of_cellUniform C p Γ h hn, div_left_inj' hpos]
  constructor
  · intro heq
    have h0 : (2 - ((realizedValues Γ).card : ℝ)) *
        ((positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u))) -
          (positiveMassSetups C p).inf' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))) = 0 := by
      rw [mul_sub]; linarith
    rcases mul_eq_zero.mp h0 with h2 | h2
    · left
      have : ((realizedValues Γ).card : ℝ) = 2 := by linarith
      exact_mod_cast this
    · right; linarith
  · rintro (h2 | h2)
    · rw [h2]; norm_num
    · rw [h2]

/--
**Sharpness restored.** If `E_P(Y ∣ x)` does not depend on the setup `x` (over the
positive-mass setups), every cell-uniform `Γ` — Example 6's construction — attains
Proposition 8's bound, at every value of `|Γ(U)|`. This is the condition the
source's computation silently needs.
-/
public theorem inferenceAccuracy_eq_prop8_bound_of_cellUniform
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    {G : Type v'} [Fintype G] [DecidableEq G]
    (p : FinPMF U) (Γ : U → G) (h : CellUniform C p Γ)
    (hconst : ∀ x ∈ positiveMassSetups C p, ∀ x' ∈ positiveMassSetups C p,
      condExpect p C.setup x (fun u => boolPm (C.concl u)) =
        condExpect p C.setup x' (fun u => boolPm (C.concl u))) :
    inferenceAccuracy C p Γ =
      ((2 - ((realizedValues Γ).card : ℝ)) *
          (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))) /
        ((realizedValues Γ).card : ℝ) := by
  classical
  obtain ⟨w₀, -⟩ := C.concl_surjective true
  have hpos : 0 < (realizedValues Γ).card :=
    Finset.card_pos.mpr ⟨Γ w₀, mem_realizedValues.mpr ⟨w₀, rfl⟩⟩
  rcases Nat.lt_or_ge (realizedValues Γ).card 2 with h1 | h2
  · exact inferenceAccuracy_eq_prop8_bound_of_card_eq_one C p Γ h (by omega)
  · refine (inferenceAccuracy_eq_prop8_bound_iff_of_cellUniform C p Γ h h2).mpr (Or.inr ?_)
    obtain ⟨a, ha, haeq⟩ := Finset.exists_mem_eq_sup' (positiveMassSetups_nonempty C p)
      (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))
    obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_inf' (positiveMassSetups_nonempty C p)
      (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))
    rw [haeq, hbeq]
    exact hconst a ha b hb

/-! ### Example 6's construction, for every device

*"Fix some device `D` and a value `|Γ(U)|`. Next divide each cell of the partition
`X × Y` into `|Γ(U)|` parts and assign them equal probability."* Splitting every
universe `u` into `n` equal-mass copies `(u, 1), …, (u, n)` does exactly this, for
any device and any distribution: the device reads only `u`, and `Γ` reads the
copy's label. -/

/-- The distribution after the split: each copy of `u` carries `P(u)/n`. -/
@[expose] public noncomputable def refinePMF (p : FinPMF U) (n : ℕ) (hn : 0 < n) :
    FinPMF (U × Fin n) where
  mass w := p.mass w.1 / n
  nonneg w := div_nonneg (p.nonneg _) (Nat.cast_nonneg _)
  sum_one := by
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    rw [Fintype.sum_prod_type]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    simp_rw [mul_div_cancel₀ _ hn']
    exact p.sum_one

/-- The device after the split: it reads the original universe and ignores the
label. -/
public abbrev refineDevice (C : InferenceDevice.{u, v} U) (n : ℕ) (hn : 0 < n) :
    InferenceDevice.{u, v} (U × Fin n) where
  Setup := C.Setup
  setup w := C.setup w.1
  concl w := C.concl w.1
  concl_surjective b := by
    obtain ⟨w, hw⟩ := C.concl_surjective b
    exact ⟨(w, ⟨0, hn⟩), hw⟩

/-- A sum over the copies of a filter that reads only the original universe is
the original sum. -/
private theorem sum_refine_filter (p : FinPMF U) (n : ℕ) (hn : 0 < n) (P : U → Prop)
    [DecidablePred P] (g : U → ℝ) :
    (Finset.univ.filter (fun w : U × Fin n => P w.1)).sum
        (fun w => (refinePMF p n hn).mass w * g w.1) =
      (Finset.univ.filter P).sum (fun u => p.mass u * g u) := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  simp only [Finset.sum_filter, Fintype.sum_prod_type, refinePMF]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  split_ifs
  · field_simp
  · simp

public theorem refine_pushOnImage (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    (p : FinPMF U) (n : ℕ) (hn : 0 < n) (x : C.Setup) :
    pushOnImage (refinePMF p n hn) (refineDevice C n hn).setup x = pushOnImage p C.setup x := by
  have h := sum_refine_filter p n hn (fun u => C.setup u = x) (fun _ => 1)
  simp only [mul_one] at h
  exact h

/-- The split leaves the positive-mass setups unchanged. -/
public theorem refine_positiveMassSetups (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    (p : FinPMF U) (n : ℕ) (hn : 0 < n) :
    positiveMassSetups (refineDevice C n hn) (refinePMF p n hn) = positiveMassSetups C p := by
  ext x
  simp only [positiveMassSetups, Finset.mem_filter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨w, hw⟩, hpos⟩
    exact ⟨⟨w.1, hw⟩, lt_of_lt_of_eq hpos (refine_pushOnImage C p n hn x)⟩
  · rintro ⟨⟨w, hw⟩, hpos⟩
    exact ⟨⟨(w, ⟨0, hn⟩), hw⟩, lt_of_lt_of_eq hpos (refine_pushOnImage C p n hn x).symm⟩

/-- The split leaves every conditional expectation of a function of the original
universe unchanged — in particular `E_P(Y ∣ x)`. -/
public theorem refine_condExpect (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    (p : FinPMF U) (n : ℕ) (hn : 0 < n) (x : C.Setup) (g : U → ℝ) :
    condExpect (refinePMF p n hn) (refineDevice C n hn).setup x (fun w => g w.1) =
      condExpect p C.setup x g := by
  have hw := refine_pushOnImage C p n hn x
  have hnum := sum_refine_filter p n hn (fun u => C.setup u = x) g
  simp only [pushOnImage] at hw
  unfold condExpect
  simp only [refineDevice] at hw hnum ⊢
  rw [hw, hnum]

/-- The label takes every value in `Fin n`, so `|Γ(U)| = n`. -/
public theorem refine_realizedValues_card (C : InferenceDevice.{u, v} U)
    (n : ℕ) (_hn : 0 < n) : (realizedValues (Prod.snd : U × Fin n → Fin n)).card = n := by
  obtain ⟨u₀, -⟩ := C.concl_surjective true
  have : realizedValues (Prod.snd : U × Fin n → Fin n) = Finset.univ := by
    ext γ
    simp only [Finset.mem_univ, iff_true, mem_realizedValues]
    exact ⟨(u₀, γ), rfl⟩
  rw [this, Finset.card_univ, Fintype.card_fin]

/-- **The split is Example 6's construction**: every label carries a `1/n` share
of every `X × Y` cell. -/
public theorem refine_cellUniform (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    (p : FinPMF U) (n : ℕ) (hn : 0 < n) :
    CellUniform (refineDevice C n hn) (refinePMF p n hn) (Prod.snd : U × Fin n → Fin n) := by
  intro x y γ _
  rw [refine_realizedValues_card C n hn]
  have hcell := sum_refine_filter p n hn (fun u => C.setup u = x ∧ C.concl u = y) (fun _ => 1)
  simp only [mul_one] at hcell
  simp only [refineDevice] at hcell ⊢
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [hcell, eq_div_iff hn']
  simp only [Finset.sum_filter, Fintype.sum_prod_type, refinePMF, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  by_cases hP : C.setup u = x ∧ C.concl u = y
  · simp [hP, hn']
  · simp only [hP, if_false]
    exact Finset.sum_eq_zero (fun i _ => by
      rw [if_neg (fun h => hP ⟨h.1, h.2.1⟩), zero_mul])

/-- The source's `max_x E_P(Y ∣ x)` for the device `D` itself. -/
private noncomputable abbrev maxY (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] (p : FinPMF U) : ℝ :=
  (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
    (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))

/-- And `min_x E_P(Y ∣ x)`. -/
private noncomputable abbrev minY (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] (p : FinPMF U) : ℝ :=
  (positiveMassSetups C p).inf' (positiveMassSetups_nonempty C p)
    (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))

/-- After the split, the maximum and minimum of `E(Y ∣ x)` are the original
device's. -/
private theorem refine_sup'_inf' (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    (p : FinPMF U) (n : ℕ) (hn : 0 < n) :
    (positiveMassSetups (refineDevice C n hn) (refinePMF p n hn)).sup'
        (positiveMassSetups_nonempty _ _)
        (fun x => condExpect (refinePMF p n hn) (refineDevice C n hn).setup x
          (fun w => boolPm ((refineDevice C n hn).concl w))) = maxY C p ∧
      (positiveMassSetups (refineDevice C n hn) (refinePMF p n hn)).inf'
        (positiveMassSetups_nonempty _ _)
        (fun x => condExpect (refinePMF p n hn) (refineDevice C n hn).setup x
          (fun w => boolPm ((refineDevice C n hn).concl w))) = minY C p := by
  have hS := refine_positiveMassSetups C p n hn
  have hE : ∀ x, condExpect (refinePMF p n hn) (refineDevice C n hn).setup x
      (fun w => boolPm ((refineDevice C n hn).concl w)) =
      condExpect p C.setup x (fun u => boolPm (C.concl u)) :=
    fun x => refine_condExpect C p n hn x (fun u => boolPm (C.concl u))
  exact ⟨Finset.sup'_congr _ hS (fun x _ => hE x), Finset.inf'_congr _ hS (fun x _ => hE x)⟩

/--
**Example 6, corrected, for every device.** Fix any device `D`, any distribution
`P`, and `n ≥ 2`; split every universe into `n` equal parts labelled `1, …, n`
(`refineDevice`, `refinePMF`, `Γ = Prod.snd`). Then
`cov(D, Γ) = (2 − n) · min_x E_P(Y ∣ x) / n`, where the minimum is over `D`'s own
positive-mass setups and `E_P` is `D`'s own conditional expectation. The source
printed `max_x`.
-/
public theorem example6_accuracy (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    (p : FinPMF U) (n : ℕ) (hn : 2 ≤ n) :
    inferenceAccuracy (refineDevice C n (by omega)) (refinePMF p n (by omega))
        (Prod.snd : U × Fin n → Fin n) =
      ((2 - (n : ℝ)) *
          (positiveMassSetups C p).inf' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))) / n := by
  have hcard := refine_realizedValues_card C n (by omega : 0 < n)
  rw [inferenceAccuracy_eq_of_cellUniform _ _ _ (refine_cellUniform C p n (by omega))
    (by rw [hcard]; exact hn), hcard, (refine_sup'_inf' C p n (by omega)).2]

/--
**When Example 6 attains Proposition 8's bound, for every device.** With the
split of `D` into `n ≥ 1` labelled parts, the accuracy equals Proposition 8's
bound `(2 − n) max_x E_P(Y ∣ x) / n` exactly when `n ≤ 2` or
`max_x E_P(Y ∣ x) = min_x E_P(Y ∣ x)` — that is, when `D`'s inference power does
not vary across its positive-mass setups. At `n = 1` and `n = 2` the bound is
attained whatever `E_P(Y ∣ x)` is.
-/
public theorem example6_attains_prop8_bound_iff (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] (p : FinPMF U) (n : ℕ) (hn : 0 < n) :
    inferenceAccuracy (refineDevice C n hn) (refinePMF p n hn)
        (Prod.snd : U × Fin n → Fin n) =
      ((2 - (n : ℝ)) *
          (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))) / n ↔
      n ≤ 2 ∨
        (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u))) =
          (positiveMassSetups C p).inf' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u))) := by
  have hcard := refine_realizedValues_card C n hn
  have hsi := refine_sup'_inf' C p n hn
  rcases Nat.lt_or_ge n 2 with h1 | h2
  · have hn1 : n = 1 := by omega
    have hacc := inferenceAccuracy_eq_prop8_bound_of_card_eq_one _ _ _
      (refine_cellUniform C p n hn) (by rw [hcard]; exact hn1)
    rw [hcard, hsi.1] at hacc
    exact ⟨fun _ => Or.inl (by omega), fun _ => hacc⟩
  · have hiff := inferenceAccuracy_eq_prop8_bound_iff_of_cellUniform _ _ _
      (refine_cellUniform C p n hn) (by rw [hcard]; exact h2)
    rw [hcard, hsi.1, hsi.2] at hiff
    rw [hiff]
    constructor
    · rintro (h | h)
      · exact Or.inl (by omega)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (by omega)
      · exact Or.inr h

/-- **Sharpness restored, for every device.** If `E_P(Y ∣ x)` does not depend on
`x` (over `D`'s positive-mass setups), Example 6's split attains Proposition 8's
bound at every `n ≥ 1`. -/
public theorem example6_attains_prop8_bound (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] (p : FinPMF U) (n : ℕ) (hn : 0 < n)
    (hconst : ∀ x ∈ positiveMassSetups C p, ∀ x' ∈ positiveMassSetups C p,
      condExpect p C.setup x (fun u => boolPm (C.concl u)) =
        condExpect p C.setup x' (fun u => boolPm (C.concl u))) :
    inferenceAccuracy (refineDevice C n hn) (refinePMF p n hn)
        (Prod.snd : U × Fin n → Fin n) =
      ((2 - (n : ℝ)) *
          (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
            (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))) / n := by
  refine (example6_attains_prop8_bound_iff C p n hn).mpr (Or.inr ?_)
  obtain ⟨a, ha, haeq⟩ := Finset.exists_mem_eq_sup' (positiveMassSetups_nonempty C p)
    (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))
  obtain ⟨b, hb, hbeq⟩ := Finset.exists_mem_eq_inf' (positiveMassSetups_nonempty C p)
    (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))
  rw [haeq, hbeq]
  exact hconst a ha b hb

end Repair

/-! ### Witnesses: a two-setup device with prescribed inference power

Four universes `(x, y) ∈ Bool × Bool`; the setup reads `x`, the conclusion reads
`y`, and the mass `(1 + y · e(x))/4` makes `E_P(Y ∣ x) = e(x)` with both setups at
mass `1/2`. Any `e : Bool → [−1, 1]` is allowed, so the family covers both the
constant case (where the bound is attained) and the varying case (where it is not).
-/

/-- Mass `(1 + y · e(x))/4` at `(x, y)`. -/
@[expose] public noncomputable def powerMass (e : Bool → ℝ) : Bool × Bool → ℝ :=
  fun w => (1 + boolPm w.2 * e w.1) / 4

@[expose] public noncomputable def powerPMF (e : Bool → ℝ) (he : ∀ x, |e x| ≤ 1) :
    FinPMF (Bool × Bool) where
  mass := powerMass e
  nonneg w := by
    have h := abs_le.mp (he w.1)
    unfold powerMass
    cases w.2 <;> simp only [boolPm] <;> linarith
  sum_one := by
    simp only [powerMass, Fintype.sum_prod_type, Fintype.sum_bool, boolPm]
    ring

/-- Setup `x`, conclusion `y`. -/
public abbrev powerDevice : InferenceDevice.{0, 0} (Bool × Bool) :=
  { Setup := Bool, setup := Prod.fst, concl := Prod.snd,
    concl_surjective := fun b => ⟨(true, b), rfl⟩ }

public theorem power_pushOnImage (e : Bool → ℝ) (he : ∀ x, |e x| ≤ 1) (x : Bool) :
    pushOnImage (powerPMF e he) powerDevice.setup x = 1 / 2 := by
  cases x <;>
    simp only [pushOnImage, powerPMF, powerMass, Finset.sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool, boolPm] <;> norm_num <;> ring

public theorem power_positiveMassSetups (e : Bool → ℝ) (he : ∀ x, |e x| ≤ 1) :
    positiveMassSetups powerDevice (powerPMF e he) = {true, false} :=
  positiveMassSetups_eq_pair _ _ ⟨(true, true), rfl⟩ ⟨(false, true), rfl⟩
    (fun w => (Bool.dichotomy w.1).elim Or.inr Or.inl)
    (by rw [power_pushOnImage]; norm_num) (by rw [power_pushOnImage]; norm_num)

/-- `E_P(Y ∣ x) = e(x)`. -/
public theorem power_condExpect (e : Bool → ℝ) (he : ∀ x, |e x| ≤ 1) (x : Bool) :
    condExpect (powerPMF e he) powerDevice.setup x (fun w => boolPm (powerDevice.concl w)) =
      e x := by
  have hw := power_pushOnImage e he x
  simp only [condExpect, pushOnImage] at hw ⊢
  rw [hw, if_neg (by norm_num)]
  cases x <;>
    simp only [powerPMF, powerMass, Finset.sum_filter, Fintype.sum_prod_type,
      Fintype.sum_bool, boolPm] <;> norm_num <;> ring

/--
**Example 6, corrected, on a family with varying inference power.** Split the
two-setup device into `n ≥ 2` labelled parts. The accuracy is
`(2 − n) · min(e(t), e(f)) / n` — the minimum of the two conditional expectations,
not the maximum the source printed.
-/
public theorem example6_power_accuracy (e : Bool → ℝ) (he : ∀ x, |e x| ≤ 1) (n : ℕ)
    (hn : 2 ≤ n) :
    inferenceAccuracy (refineDevice powerDevice n (by omega))
        (refinePMF (powerPMF e he) n (by omega)) (Prod.snd : (Bool × Bool) × Fin n → Fin n) =
      (2 - (n : ℝ)) * min (e true) (e false) / n := by
  rw [example6_accuracy powerDevice (powerPMF e he) n hn]
  congr 2
  rw [Finset.inf'_congr _ (power_positiveMassSetups e he) (fun x _ => power_condExpect e he x)]
  simp [Finset.inf'_insert, Finset.inf'_singleton]

/--
**Proposition 8's bound is sharp, at every `|Γ(U)|` and every value of
`max_x E_P(Y ∣ x)`.** For every `n ≥ 1` and every `e ∈ [−1, 1]` there is a device,
a distribution and a target with `|Γ(U)| = n`, two positive-mass setups, inference
power `E_P(Y ∣ x) = e` at both, and covariance accuracy **equal** to Proposition 8's
bound `(2 − |Γ(U)|) max_x E_P(Y ∣ x) / |Γ(U)| = (2 − n) e / n`.

The model is Example 6's own construction (`refineDevice`/`refinePMF`) applied to
`powerDevice` with constant `e`. That is the source's claim *"This bound is
sharp"* with the condition its computation needs: `E_P(Y ∣ x)` independent of `x`.
-/
public theorem prop8_bound_sharp (n : ℕ) (hn : 0 < n) (e : ℝ) (he : |e| ≤ 1) :
    ∃ (U : Type) (_ : Fintype U) (C : InferenceDevice.{0, 0} U) (_ : DecidableEq C.Setup)
      (p : FinPMF U) (Γ : U → Fin n),
      (realizedValues Γ).card = n ∧
      (positiveMassSetups C p).card = 2 ∧
      (∀ x ∈ positiveMassSetups C p,
        condExpect p C.setup x (fun u => boolPm (C.concl u)) = e) ∧
      inferenceAccuracy C p Γ =
        ((2 - ((realizedValues Γ).card : ℝ)) *
            (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
              (fun x => condExpect p C.setup x (fun u => boolPm (C.concl u)))) /
          ((realizedValues Γ).card : ℝ) ∧
      inferenceAccuracy C p Γ = (2 - (n : ℝ)) * e / n := by
  have he' : ∀ x : Bool, |(fun _ : Bool => e) x| ≤ 1 := fun _ => he
  set p₀ := powerPMF (fun _ => e) he'
  have hcard := refine_realizedValues_card powerDevice n hn
  have hS := refine_positiveMassSetups powerDevice p₀ n hn
  have hE : ∀ x, condExpect (refinePMF p₀ n hn) (refineDevice powerDevice n hn).setup x
      (fun w => boolPm ((refineDevice powerDevice n hn).concl w)) = e := fun x =>
    (refine_condExpect powerDevice p₀ n hn x (fun u => boolPm (powerDevice.concl u))).trans
      (power_condExpect (fun _ => e) he' x)
  have hsup : (positiveMassSetups powerDevice p₀).sup' (positiveMassSetups_nonempty _ _)
      (fun x => condExpect p₀ powerDevice.setup x (fun u => boolPm (powerDevice.concl u))) = e := by
    rw [Finset.sup'_congr _ (power_positiveMassSetups (fun _ => e) he')
      (fun x _ => power_condExpect (fun _ => e) he' x)]
    simp
  have hacc := example6_attains_prop8_bound powerDevice p₀ n hn
    (fun x _ x' _ => (power_condExpect (fun _ => e) he' x).trans
      (power_condExpect (fun _ => e) he' x').symm)
  refine ⟨(Bool × Bool) × Fin n, inferInstance, refineDevice powerDevice n hn, inferInstance,
    refinePMF p₀ n hn, Prod.snd, hcard, ?_, fun x _ => hE x, ?_, ?_⟩
  · rw [hS, power_positiveMassSetups]; simp
  · rw [hacc, hcard, (refine_sup'_inf' powerDevice p₀ n hn).1]
  · rw [hacc, hsup]

/-! ### The instance above, through the repair

`ex6Device` is cell-uniform — it is Example 6's construction — so the corrected
computation applies to it and returns the accuracy `ex6_accuracy` found by hand:
`(2 − 3) · min(0, 1/3) / 3 = 0`.
-/

/-- `ex6Device` with `ex6Gamma` is Example 6's construction. -/
public theorem ex6_cellUniform : CellUniform ex6Device ex6PMF ex6Gamma := by
  intro x y γ _
  rw [show (realizedValues ex6Gamma).card = 3 by rw [ex6_realizedValues]; decide]
  cases x <;> cases y <;> fin_cases γ <;>
    simp [ex6PMF, ex6Mass, Finset.sum_filter, Fin.sum_univ_succ] <;> norm_num

/-- **The corrected computation on the instance**: the accuracy is
`(2 − |Γ(U)|) · min_x E_P(Y ∣ x) / |Γ(U)|` with `min_x E_P(Y ∣ x) = 0`. -/
public theorem ex6_accuracy_via_min :
    inferenceAccuracy ex6Device ex6PMF ex6Gamma =
      ((2 - ((realizedValues ex6Gamma).card : ℝ)) *
          (positiveMassSetups ex6Device ex6PMF).inf'
            (positiveMassSetups_nonempty ex6Device ex6PMF)
            (fun x => condExpect ex6PMF ex6Device.setup x
              (fun u => boolPm (ex6Device.concl u)))) /
        ((realizedValues ex6Gamma).card : ℝ) :=
  inferenceAccuracy_eq_of_cellUniform ex6Device ex6PMF ex6Gamma ex6_cellUniform
    (by rw [ex6_realizedValues]; decide)

end AISafetyAtlas.Inference
