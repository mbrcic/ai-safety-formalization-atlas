module

public import AISafetyAtlas.Inference.Complexity.Measure
public import AISafetyAtlas.Inference.Stochastic.Bridge

/-!
# Inference complexity against Shannon entropy — a refuted bound

Wolpert 2018 Proposition 12 claims that inference complexity is bounded by the
Shannon entropy of the setup distribution:

> **Proposition 12.** *"For any ID `D`, probability distribution `μ`, and function
> `Γ` with a countable image such that `D > Γ`, `C_μ(Γ; D) ≤ |Γ| × H_μ(X)`, where
> `H_μ(X)` is the Shannon entropy of `μ(X)`."*

**It is false, and this module refutes it with a four-state model.** It also
proves the repaired statement, `prop12_repaired`.

## Why the printed proof does not close

The proof (arXiv:1711.03499v3) is a three-step chain:

1. `∑_{δ ∈ P(Γ)} min_{x : X=x ⇒ Y=δ(Γ)} ℳ(x)  ≤  ∑_{x ∈ X(U)} ℳ(x)`
2. `∑_{x ∈ X(U)} ℳ(x)  ≤  −|Γ| ∑_{x ∈ X(U)} log₂ μ(x) / |Γ|`
3. `−|Γ| ∑_{x ∈ X(U)} log₂ μ(x) / |Γ|  ≤  |Γ| H_μ(X)  =  −|Γ| ∑_{x ∈ X(U)} μ(x) log₂ μ(x)`

**Step 2** is an identity once `ℳ(x) = −ln μ(x)` and the sum are in the same
units; the atlas uses nats throughout. The print's `log₂` is a units slip. It
does not rescue the proposition: the collision model below fails even with `ℳ`
in nats and `H_μ(X)` in bits.

**Step 3** compares the two sums term by term. That comparison needs
`|Γ| · μ(x) ≥ 1`, that is `μ(x) ≥ 1/|Γ|`, at every setup value. On a fibre of
mass strictly between `0` and `1`, the term inequality holds exactly when the
mass bound does (`prop12_step3_term_iff`). The statement assumes nothing of the
kind, and a setup value of small mass breaks it.

**Step 1** is not justified either. It reads the sum over probes as a sub-sum
over setup values, which needs the probes to be answered by **distinct** setups.
They need not be. A setup whose fibre has conclusion `false` throughout answers
the probe of every target value its fibre never takes, so with `|Γ(U)| ≥ 3` one
setup can be the only answer to several probes, and its length is then counted
once per probe on the left and once on the right. `prop12_massBound_insufficient`
is a model where one setup answers three probes. It meets the step 3 mass bound at every setup value, and the
printed conclusion still fails, by exactly `2 ln 3`. So the mass bound alone does
not repair the proposition.

## The countermodel

`prop12Device` has two setup values and a binary target. One setup answers the
`true` probe and the other answers the `false` probe, and neither answers both —
for a binary target no single setup can, since the two probes of `Γ` disagree
everywhere. So the complexity is the sum of both fibre lengths, and skewing the
mass between the two fibres drives it up while driving the entropy down.

At masses `3/4` and `1/4` the two sides are exactly

* `C_μ(Γ; D) = 4 ln 2 − ln 3`
* `|Γ| × H_μ(X) = 2 H_μ(X) = 4 ln 2 − (3/2) ln 3`

so the claimed inequality fails by exactly `(ln 3)/2`. Nothing is approximated:
`prop12_gap` is an identity, and `prop12_refuted` is its consequence.

The failure is not marginal in the parameter either. As the mass on one fibre
tends to zero the complexity grows without bound while the entropy tends to zero,
so no constant multiple of `H_μ(X)` bounds `C_μ(Γ; D)`.

## The repair

`prop12_repaired` proves the printed conclusion,
`C_μ(Γ; D) ≤ |Γ(U)| × H_μ(X)`, at the printed generality: any device, any
probability measure, `Γ` with finite image, and `D > Γ`. It adds one
hypothesis, `HeavyAnsweringSelection`: a choice of answering setup for each
realized target value that is injective and puts each chosen setup on a fibre of
mass at least `1/|Γ(U)|`. That is what the printed proof uses. Injectivity is
step 1's distinctness, and the mass bound is step 3's term condition, required
only at the setups step 1 actually sums. No measurability is needed, because the
argument never adds fibre masses together.

`prop12_repaired_of_massBound` is the printed proof's own shape, with an
injective answering selection plus the mass bound at every realized setup.

Neither half can be dropped:

* The four-state countermodel has an injective answering selection
  (`prop12_injective_selection`), fails the mass bound
  (`prop12_not_heavyAnsweringSelection`), and violates the conclusion
  (`prop12_distinct_insufficient`).
* The five-state collision model meets the mass bound everywhere, has no
  injective answering selection (`prop12Collide_not_injective_selection`), and
  violates the conclusion (`prop12_massBound_insufficient`). It fails even if
  `ℳ` is read in nats and `H_μ(X)` in bits.

This shows that each half is needed by the printed argument and that neither can
be dropped from the repair. It does not claim that either half is necessary for
the conclusion itself.

## What this does not say

The 2008 layer's own complexity results are untouched: Theorem 4's emulation
bound (`inferenceComplexityMeasure_le_of_stronglyInfers`) is a different
statement, is proved, and does not pass through Proposition 12.

Note also that no entropy dependency was needed to state or refute this. The
atlas's `entropyOn` — local discrete Shannon entropy over the setup image, built
for Definition 10 — is exactly the `H_μ(X)` the proposition names. The earlier
ledger position that Proposition 12 was gated behind an entropy purchase was
wrong on that point, and it is corrected here.
-/

namespace AISafetyAtlas.Inference

open MeasureTheory

/-! ## The four-state model -/

/-- Setup: the first two states share one setup value, the last two the other. -/
public abbrev prop12X : Fin 4 → Bool := ![true, true, false, false]

/-- Conclusion. On the first fibre it tracks `Γ`; on the second it is its
negation. -/
public abbrev prop12Y : Fin 4 → Bool := ![true, false, false, true]

/-- Target. Both values occur on each fibre, which is what lets each fibre answer
exactly one probe. -/
public abbrev prop12Gamma : Fin 4 → Bool := ![true, false, true, false]

/-- Masses `3/8, 3/8, 1/8, 1/8`, so the two setup fibres carry `3/4` and `1/4`. -/
public noncomputable def prop12Mass : Fin 4 → ℝ := ![3 / 8, 3 / 8, 1 / 8, 1 / 8]

public noncomputable def prop12PMF : FinPMF (Fin 4) where
  mass := prop12Mass
  nonneg := by intro u; fin_cases u <;> simp only [prop12Mass] <;> norm_num
  sum_one := by simp [prop12Mass, Fin.sum_univ_succ]; norm_num

/-- The device of the countermodel. -/
public abbrev prop12Device : InferenceDevice.{0, 0} (Fin 4) :=
  { Setup := Bool, setup := prop12X, concl := prop12Y, concl_surjective := by decide }

/-- `D > Γ`: the `true` probe is answered on the first fibre and the `false`
probe on the second. This is Proposition 12's own hypothesis, so the countermodel
is inside its scope. -/
public theorem prop12_weaklyInfers : WeaklyInfers prop12Device prop12Gamma := by
  intro γ f hf _
  have hfeq : f = probe γ := IsProbe.eq_of_isProbe hf (isProbe_probe γ)
  subst hfeq
  cases γ
  · exact ⟨false, ⟨2, rfl⟩, by decide⟩
  · exact ⟨true, ⟨0, rfl⟩, by decide⟩

/-! ## The two sides, computed exactly -/

/-- The measure of the countermodel. -/
public noncomputable def prop12Measure : Measure (Fin 4) := prop12PMF.toMeasure

public theorem prop12_mass_true : massOn prop12Measure prop12X true = 3 / 4 := by
  rw [prop12Measure, massOn_toMeasure]
  simp [pushOnImage, prop12PMF, prop12Mass, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

public theorem prop12_mass_false : massOn prop12Measure prop12X false = 1 / 4 := by
  rw [prop12Measure, massOn_toMeasure]
  simp [pushOnImage, prop12PMF, prop12Mass, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

/-- Only the first fibre answers the `true` probe. -/
public theorem prop12_answering_true :
    answeringSet prop12Device prop12Gamma (probe true) = {true} := by
  ext x
  rw [mem_answeringSet_iff, Finset.mem_singleton]
  cases x
  · exact ⟨fun h => absurd (h.2) (by decide), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => rfl, fun _ => ⟨⟨0, rfl⟩, by decide⟩⟩

/-- Only the second fibre answers the `false` probe. -/
public theorem prop12_answering_false :
    answeringSet prop12Device prop12Gamma (probe false) = {false} := by
  ext x
  rw [mem_answeringSet_iff, Finset.mem_singleton]
  cases x
  · exact ⟨fun _ => rfl, fun _ => ⟨⟨2, rfl⟩, by decide⟩⟩
  · exact ⟨fun h => absurd (h.2) (by decide), fun h => absurd h (by decide)⟩

public theorem prop12_rangeFinset : rangeFinset prop12Gamma = Finset.univ := by
  ext γ
  simp only [Finset.mem_univ, iff_true, mem_rangeFinset]
  cases γ
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

/-- **`C_μ(Γ; D) = 4 ln 2 − ln 3`.** Each probe is answered by exactly one setup,
so the complexity is the sum of the two fibre lengths. -/
public theorem prop12_complexity :
    inferenceComplexityMeasure prop12Measure prop12Device prop12Gamma
      prop12_weaklyInfers = 4 * Real.log 2 - Real.log 3 := by
  rw [inferenceComplexityMeasure, inferenceComplexity_eq_total, inferenceComplexityTotal,
    prop12_rangeFinset]
  rw [show (Finset.univ : Finset Bool) = {false, true} from by decide]
  rw [Finset.sum_pair (by decide : (false : Bool) ≠ true)]
  unfold minAnsweringLength
  rw [dif_pos (by rw [prop12_answering_false]; exact ⟨false, by simp⟩),
    dif_pos (by rw [prop12_answering_true]; exact ⟨true, by simp⟩)]
  simp only [prop12_answering_false, prop12_answering_true, Finset.inf'_singleton]
  unfold measureLength
  rw [prop12_mass_true, prop12_mass_false]
  rw [show (3 : ℝ) / 4 = 3 / 4 from rfl, show (1 : ℝ) / 4 = 1 / 4 from rfl]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
  push_cast
  rw [Real.log_one]
  ring

/-- **`H_μ(X) = 2 ln 2 − (3/4) ln 3`.** -/
public theorem prop12_entropy :
    entropyOn prop12Measure prop12X = 2 * Real.log 2 - 3 / 4 * Real.log 3 := by
  have hrange : rangeFinset prop12X = Finset.univ := by
    ext x
    simp only [Finset.mem_univ, iff_true, mem_rangeFinset]
    cases x
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
  unfold entropyOn
  rw [hrange, show (Finset.univ : Finset Bool) = {false, true} from by decide,
    Finset.sum_pair (by decide : (false : Bool) ≠ true),
    prop12_mass_true, prop12_mass_false,
    if_neg (by norm_num), if_neg (by norm_num)]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
  push_cast
  rw [Real.log_one]
  ring

/-- **The gap is exactly `(ln 3)/2`.** An identity, not an estimate. -/
public theorem prop12_gap :
    inferenceComplexityMeasure prop12Measure prop12Device prop12Gamma
        prop12_weaklyInfers
      - (rangeFinset prop12Gamma).card * entropyOn prop12Measure prop12X
      = Real.log 3 / 2 := by
  rw [prop12_complexity, prop12_entropy, prop12_rangeFinset]
  simp only [Finset.card_univ, Fintype.card_bool, Nat.cast_ofNat]
  ring

/--
**Wolpert 2018, Proposition 12 is refuted.** *"`C_μ(Γ; D) ≤ |Γ| × H_μ(X)`."*

The countermodel satisfies every printed hypothesis — `μ` is a probability
measure, `Γ` has a finite (hence countable) image, and `D > Γ` — and the
inequality fails by `(ln 3)/2`.
-/
public theorem prop12_refuted :
    ¬ (inferenceComplexityMeasure prop12Measure prop12Device prop12Gamma
        prop12_weaklyInfers
      ≤ (rangeFinset prop12Gamma).card * entropyOn prop12Measure prop12X) := by
  intro h
  have hgap := prop12_gap
  have hpos : 0 < Real.log 3 / 2 := by
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  linarith

/-! ## The repair

The printed chain has three steps. Step 2 is an identity. On fibres of mass
strictly between `0` and `1`, step 3 holds term by term exactly when the fibre
carries mass at least `1/|Γ|` (`prop12_step3_term_iff`). Step 1 bounds a sum over probes by a sum over distinct
setup values, which needs the probes to be answered by **distinct** setups.
`HeavyAnsweringSelection` asks for both, at the setups the argument uses, and
`prop12_repaired` proves the printed conclusion under it. -/

section Repair

universe u v v'

variable {U : Type u} [MeasurableSpace U]

/-- **What the printed proof uses.** One answering setup per realized target
value, distinct for distinct values, each on a fibre of mass at least `1/|Γ|`.

Distinctness is what lets step 1 read the probe sum as a sub-sum over `X(U)`; the
mass bound is what step 3 needs at each term. -/
@[expose] public def HeavyAnsweringSelection (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : Prop :=
  ∃ σ : G → C.Setup, Set.InjOn σ (rangeFinset Γ : Set G) ∧
    ∀ γ ∈ rangeFinset Γ, σ γ ∈ answeringSet C Γ (probe γ) ∧
      1 / ((rangeFinset Γ).card : ℝ) ≤ massOn μ C.setup (σ γ)

/-- **Step 3, one term.** On a fibre of mass strictly between `0` and `1`, the
printed term-by-term comparison `−log μ(x) / |Γ| ≤ −μ(x) log μ(x)` holds **if
and only if** `μ(x) ≥ 1/|Γ|`. So the mass bound is not merely sufficient for the
printed step; it is what that step says. -/
public theorem prop12_step3_term_iff {m n : ℝ} (hn : 0 < n) (hm0 : 0 < m) (hm1 : m < 1) :
    -Real.log m / n ≤ -(m * Real.log m) ↔ 1 / n ≤ m := by
  have hL : 0 < -Real.log m := neg_pos.mpr (Real.log_neg hm0 hm1)
  rw [div_le_iff₀ hn, div_le_iff₀ hn]
  constructor
  · intro h
    by_contra hlt
    have hlt' := not_le.mp hlt
    nlinarith
  · intro h
    nlinarith

/-- A fibre of a probability measure has length at least `0`. -/
public theorem measureLength_nonneg (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) (x : C.Setup) : 0 ≤ measureLength μ C x :=
  neg_nonneg.mpr (Real.log_nonpos (massOn_nonneg _ _ _) measureReal_le_one)

/-- `H_μ(X)` is the mass-weighted length, `∑ₓ μ(x) ℒ(x)`. -/
public theorem entropyOn_eq_sum_mul_measureLength (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup] :
    entropyOn μ C.setup =
      (rangeFinset C.setup).sum (fun x => massOn μ C.setup x * measureLength μ C x) := by
  unfold entropyOn measureLength
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun x _ => ?_
  split_ifs with h
  · simp [h]
  · ring

/--
**Wolpert 2018, Proposition 12, repaired.** *"`C_μ(Γ; D) ≤ |Γ| × H_μ(X)`."*

Every printed hypothesis is kept — any device, any probability measure, `Γ` with
finite image, and `D > Γ` — and `HeavyAnsweringSelection` is added. It is the
printed proof's own content: step 1 needs the answering setups distinct, and
step 3 needs each to carry mass at least `1/|Γ|`. No measurability is needed,
because the argument never adds fibre masses together.
-/
public theorem prop12_repaired (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hW : WeaklyInfers C Γ) (hsel : HeavyAnsweringSelection μ C Γ) :
    inferenceComplexityMeasure μ C Γ hW ≤
      (rangeFinset Γ).card * entropyOn μ C.setup := by
  obtain ⟨σ, hinj, hσ⟩ := hsel
  have hℓ := measureLength_nonneg μ C
  -- Step 1: each minimum is at most the length of the selected setup.
  have h1 : inferenceComplexityMeasure μ C Γ hW ≤
      (rangeFinset Γ).sum (fun γ => measureLength μ C (σ γ)) := by
    rw [inferenceComplexityMeasure, inferenceComplexity_eq_total, inferenceComplexityTotal]
    refine Finset.sum_le_sum fun γ hγ => ?_
    unfold minAnsweringLength
    rw [dif_pos ⟨σ γ, (hσ γ hγ).1⟩]
    exact Finset.inf'_le _ (hσ γ hγ).1
  -- Step 3, term by term, at the selected setups.
  have h3 : (rangeFinset Γ).sum (fun γ => measureLength μ C (σ γ)) ≤
      (rangeFinset Γ).sum (fun γ => ((rangeFinset Γ).card : ℝ) *
        (massOn μ C.setup (σ γ) * measureLength μ C (σ γ))) := by
    refine Finset.sum_le_sum fun γ hγ => ?_
    have hn : (0 : ℝ) < (rangeFinset Γ).card := by exact_mod_cast Finset.card_pos.mpr ⟨γ, hγ⟩
    have hm : 1 ≤ ((rangeFinset Γ).card : ℝ) * massOn μ C.setup (σ γ) := by
      have := (hσ γ hγ).2
      rwa [div_le_iff₀ hn, mul_comm] at this
    nlinarith [hℓ (σ γ)]
  -- Distinctness: the selected setups are a subset of `X(U)`.
  have hsub : (rangeFinset Γ).image σ ⊆ rangeFinset C.setup := by
    intro x hx
    obtain ⟨γ, hγ, rfl⟩ := Finset.mem_image.mp hx
    exact (mem_rangeFinset C.setup _).mpr ((mem_answeringSet_iff C Γ _ _).mp (hσ γ hγ).1).1
  have h4 := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun x _ _ => mul_nonneg (massOn_nonneg μ C.setup x) (hℓ x))
  rw [Finset.sum_image hinj] at h4
  rw [← Finset.mul_sum] at h3
  rw [entropyOn_eq_sum_mul_measureLength]
  have hn0 : (0 : ℝ) ≤ (rangeFinset Γ).card := Nat.cast_nonneg _
  calc inferenceComplexityMeasure μ C Γ hW
      ≤ _ := h1
    _ ≤ _ := h3
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 hn0

/-- **The repair in the printed proof's own shape.** Step 3 runs over all of
`X(U)`, so the printed chain asks for the mass bound at every realized setup; with
an injective answering selection that implies `HeavyAnsweringSelection`. -/
public theorem prop12_repaired_of_massBound (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hW : WeaklyInfers C Γ)
    (hdistinct : ∃ σ : G → C.Setup, Set.InjOn σ (rangeFinset Γ : Set G) ∧
      ∀ γ ∈ rangeFinset Γ, σ γ ∈ answeringSet C Γ (probe γ))
    (hmass : ∀ x ∈ realizedSetups C, 1 / ((rangeFinset Γ).card : ℝ) ≤ massOn μ C.setup x) :
    inferenceComplexityMeasure μ C Γ hW ≤
      (rangeFinset Γ).card * entropyOn μ C.setup := by
  obtain ⟨σ, hinj, hσ⟩ := hdistinct
  refine prop12_repaired μ C Γ hW ⟨σ, hinj, fun γ hγ => ⟨hσ γ hγ, hmass _ ?_⟩⟩
  unfold realizedSetups
  exact (mem_rangeFinset C.setup _).mpr ((mem_answeringSet_iff C Γ _ _).mp (hσ γ hγ)).1

end Repair

/-- **The repair excludes the countermodel.** The `false` probe is answered only
by the `false` fibre, which carries `1/4 < 1/2 = 1/|Γ|`. -/
public theorem prop12_not_heavyAnsweringSelection :
    ¬ HeavyAnsweringSelection prop12Measure prop12Device prop12Gamma := by
  rintro ⟨σ, -, hσ⟩
  have hγ : false ∈ rangeFinset prop12Gamma := by rw [prop12_rangeFinset]; exact Finset.mem_univ _
  obtain ⟨hans, hmass⟩ := hσ false hγ
  rw [prop12_answering_false, Finset.mem_singleton] at hans
  rw [hans, prop12_mass_false, prop12_rangeFinset] at hmass
  norm_num at hmass

/-- **The countermodel does have an injective answering selection.** The identity
picks the `true` fibre for the `true` probe and the `false` fibre for the `false`
probe. So what it lacks is the mass bound alone. -/
public theorem prop12_injective_selection :
    ∃ σ : Bool → Bool, Set.InjOn σ (rangeFinset prop12Gamma : Set Bool) ∧
      ∀ γ ∈ rangeFinset prop12Gamma,
        σ γ ∈ answeringSet prop12Device prop12Gamma (probe γ) := by
  refine ⟨id, Set.injOn_id _, fun γ _ => ?_⟩
  cases γ
  · rw [prop12_answering_false]; exact Finset.mem_singleton_self _
  · rw [prop12_answering_true]; exact Finset.mem_singleton_self _

/-- **Distinctness alone does not repair Proposition 12.** The four-state
countermodel has an injective answering selection and still violates the printed
conclusion. So the mass bound in `HeavyAnsweringSelection` is not removable. -/
public theorem prop12_distinct_insufficient :
    (∃ σ : Bool → Bool, Set.InjOn σ (rangeFinset prop12Gamma : Set Bool) ∧
        ∀ γ ∈ rangeFinset prop12Gamma,
          σ γ ∈ answeringSet prop12Device prop12Gamma (probe γ)) ∧
      ¬ (inferenceComplexityMeasure prop12Measure prop12Device prop12Gamma
          prop12_weaklyInfers
        ≤ (rangeFinset prop12Gamma).card * entropyOn prop12Measure prop12X) :=
  ⟨prop12_injective_selection, prop12_refuted⟩

/-! ## The mass bound alone is not enough

A setup whose fibre has conclusion `false` throughout answers the probe of every
target value its fibre never takes. So one setup can answer several probes, and
step 1 then counts its length once per probe while `X(U)` counts it once. The
model below meets the mass bound at **every** setup value, has no injective
answering selection, and violates the printed conclusion by exactly `2 ln 3`.

The target has four values, not three, so that the violation does not depend on
units. If `ℳ` is read in nats and `H_μ(X)` in bits, as the printed chain's
`log₂` would suggest, the bound still fails here: `C_μ ≈ 4.447` nats against
`4 H_μ ≈ 3.245` bits. A three-valued model sharing one setup between two probes
(fibres `1/3`, `2/3`) breaks only the same-units reading, so it was not used. -/

/-- Setup: the first state alone has setup `true`; the other four share `false`. -/
public abbrev prop12CollideX : Fin 5 → Bool := ![true, false, false, false, false]

/-- Conclusion: `false` everywhere except the last state. -/
public abbrev prop12CollideY : Fin 5 → Bool := ![false, false, false, false, true]

/-- Target with four values. The `true` fibre only ever takes `3`. -/
public abbrev prop12CollideGamma : Fin 5 → Fin 4 := ![3, 0, 1, 2, 3]

/-- Masses `1/4, 3/16, 3/16, 3/16, 3/16`, so the two setup fibres carry `1/4` and
`3/4`. -/
public noncomputable def prop12CollideMass : Fin 5 → ℝ :=
  ![1 / 4, 3 / 16, 3 / 16, 3 / 16, 3 / 16]

public noncomputable def prop12CollidePMF : FinPMF (Fin 5) where
  mass := prop12CollideMass
  nonneg := by intro u; fin_cases u <;> simp only [prop12CollideMass] <;> norm_num
  sum_one := by simp [prop12CollideMass, Fin.sum_univ_succ]; norm_num

public abbrev prop12CollideDevice : InferenceDevice.{0, 0} (Fin 5) :=
  { Setup := Bool, setup := prop12CollideX, concl := prop12CollideY,
    concl_surjective := by decide }

public noncomputable def prop12CollideMeasure : Measure (Fin 5) := prop12CollidePMF.toMeasure

public instance : IsProbabilityMeasure prop12CollideMeasure := by
  unfold prop12CollideMeasure
  infer_instance

/-- `D > Γ`: the `true` fibre answers the probes of `0`, `1` and `2`, the `false`
fibre the probe of `3`. -/
public theorem prop12Collide_weaklyInfers :
    WeaklyInfers prop12CollideDevice prop12CollideGamma := by
  intro γ f hf _
  have hfeq : f = probe γ := IsProbe.eq_of_isProbe hf (isProbe_probe γ)
  subst hfeq
  fin_cases γ
  · exact ⟨true, ⟨0, rfl⟩, by decide⟩
  · exact ⟨true, ⟨0, rfl⟩, by decide⟩
  · exact ⟨true, ⟨0, rfl⟩, by decide⟩
  · exact ⟨false, ⟨1, rfl⟩, by decide⟩

public theorem prop12Collide_mass_true :
    massOn prop12CollideMeasure prop12CollideX true = 1 / 4 := by
  rw [prop12CollideMeasure, massOn_toMeasure]
  simp [pushOnImage, prop12CollidePMF, prop12CollideMass, Finset.sum_filter, Fin.sum_univ_succ]

public theorem prop12Collide_mass_false :
    massOn prop12CollideMeasure prop12CollideX false = 3 / 4 := by
  rw [prop12CollideMeasure, massOn_toMeasure]
  simp [pushOnImage, prop12CollidePMF, prop12CollideMass, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

public theorem prop12Collide_rangeFinset : rangeFinset prop12CollideGamma = Finset.univ := by
  ext γ
  simp only [Finset.mem_univ, iff_true, mem_rangeFinset]
  fin_cases γ
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩
  · exact ⟨0, rfl⟩

/-- For `γ ∈ {0, 1, 2}` only the `true` fibre answers the probe of `γ`. -/
public theorem prop12Collide_answering_of_ne_three (γ : Fin 4) (hγ : γ ≠ 3) :
    answeringSet prop12CollideDevice prop12CollideGamma (probe γ) = {true} := by
  ext x
  rw [mem_answeringSet_iff, Finset.mem_singleton]
  fin_cases γ
  · cases x
    · exact ⟨fun h => absurd (h.2 1 rfl) (by decide), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => rfl, fun _ => ⟨⟨0, rfl⟩, by decide⟩⟩
  · cases x
    · exact ⟨fun h => absurd (h.2 2 rfl) (by decide), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => rfl, fun _ => ⟨⟨0, rfl⟩, by decide⟩⟩
  · cases x
    · exact ⟨fun h => absurd (h.2 3 rfl) (by decide), fun h => absurd h (by decide)⟩
    · exact ⟨fun _ => rfl, fun _ => ⟨⟨0, rfl⟩, by decide⟩⟩
  · exact absurd rfl hγ

/-- Only the `false` fibre answers the probe of `3`. -/
public theorem prop12Collide_answering_three :
    answeringSet prop12CollideDevice prop12CollideGamma (probe 3) = {false} := by
  ext x
  rw [mem_answeringSet_iff, Finset.mem_singleton]
  cases x
  · exact ⟨fun _ => rfl, fun _ => ⟨⟨1, rfl⟩, by decide⟩⟩
  · exact ⟨fun h => absurd (h.2 0 rfl) (by decide), fun h => absurd h (by decide)⟩

/-- **The docstring's original diagnosis holds here.** Every setup value carries
at least `1/|Γ| = 1/4`. -/
public theorem prop12Collide_massBound :
    ∀ x ∈ realizedSetups prop12CollideDevice,
      1 / ((rangeFinset prop12CollideGamma).card : ℝ) ≤
        massOn prop12CollideMeasure prop12CollideDevice.setup x := by
  intro x _
  rw [prop12Collide_rangeFinset]
  cases x
  · rw [show prop12CollideDevice.setup = prop12CollideX from rfl, prop12Collide_mass_false]
    norm_num
  · rw [show prop12CollideDevice.setup = prop12CollideX from rfl, prop12Collide_mass_true]
    norm_num

/-- **No injective answering selection exists.** The probes of `0` and `1` are
both answered only by the `true` fibre. -/
public theorem prop12Collide_not_injective_selection :
    ¬ ∃ σ : Fin 4 → Bool, Set.InjOn σ (rangeFinset prop12CollideGamma : Set (Fin 4)) ∧
      ∀ γ ∈ rangeFinset prop12CollideGamma,
        σ γ ∈ answeringSet prop12CollideDevice prop12CollideGamma (probe γ) := by
  rintro ⟨σ, hinj, hσ⟩
  have hmem : ∀ γ, γ ∈ rangeFinset prop12CollideGamma := fun γ => by
    rw [prop12Collide_rangeFinset]; exact Finset.mem_univ _
  have h0 := hσ 0 (hmem 0)
  have h1 := hσ 1 (hmem 1)
  rw [prop12Collide_answering_of_ne_three 0 (by decide), Finset.mem_singleton] at h0
  rw [prop12Collide_answering_of_ne_three 1 (by decide), Finset.mem_singleton] at h1
  exact absurd (hinj (hmem 0) (hmem 1) (h0.trans h1.symm)) (by decide)

/-- **`C_μ(Γ; D) = 8 ln 2 − ln 3`.** The `true` fibre's length `2 ln 2` is paid
three times, once for each probe it answers. -/
public theorem prop12Collide_complexity :
    inferenceComplexityMeasure prop12CollideMeasure prop12CollideDevice prop12CollideGamma
      prop12Collide_weaklyInfers = 8 * Real.log 2 - Real.log 3 := by
  rw [inferenceComplexityMeasure, inferenceComplexity_eq_total, inferenceComplexityTotal,
    prop12Collide_rangeFinset, Fin.sum_univ_four]
  unfold minAnsweringLength
  rw [prop12Collide_answering_of_ne_three 0 (by decide),
    prop12Collide_answering_of_ne_three 1 (by decide),
    prop12Collide_answering_of_ne_three 2 (by decide), prop12Collide_answering_three]
  simp only [Finset.singleton_nonempty, dif_pos, Finset.inf'_singleton]
  unfold measureLength
  rw [show prop12CollideDevice.setup = prop12CollideX from rfl,
    prop12Collide_mass_true, prop12Collide_mass_false]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow, Real.log_one]
  push_cast
  ring

/-- **`H_μ(X) = 2 ln 2 − (3/4) ln 3`.** -/
public theorem prop12Collide_entropy :
    entropyOn prop12CollideMeasure prop12CollideX = 2 * Real.log 2 - 3 / 4 * Real.log 3 := by
  have hrange : rangeFinset prop12CollideX = Finset.univ := by
    ext x
    simp only [Finset.mem_univ, iff_true, mem_rangeFinset]
    cases x
    · exact ⟨1, rfl⟩
    · exact ⟨0, rfl⟩
  unfold entropyOn
  rw [hrange, show (Finset.univ : Finset Bool) = {false, true} from by decide,
    Finset.sum_pair (by decide : (false : Bool) ≠ true),
    prop12Collide_mass_true, prop12Collide_mass_false,
    if_neg (by norm_num), if_neg (by norm_num)]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow, Real.log_one]
  push_cast
  ring

/-- **The gap is exactly `2 ln 3`.** -/
public theorem prop12Collide_gap :
    inferenceComplexityMeasure prop12CollideMeasure prop12CollideDevice prop12CollideGamma
        prop12Collide_weaklyInfers
      - (rangeFinset prop12CollideGamma).card * entropyOn prop12CollideMeasure prop12CollideX
      = 2 * Real.log 3 := by
  rw [prop12Collide_complexity, prop12Collide_entropy, prop12Collide_rangeFinset]
  simp only [Finset.card_univ, Fintype.card_fin, Nat.cast_ofNat]
  ring

/-- **The mass bound alone does not repair Proposition 12.** Every printed
hypothesis holds, every setup value carries at least `1/|Γ|`, and the conclusion
still fails, because three probes share one answering setup. So the
distinctness in `HeavyAnsweringSelection` is not removable. -/
public theorem prop12_massBound_insufficient :
    (∀ x ∈ realizedSetups prop12CollideDevice,
        1 / ((rangeFinset prop12CollideGamma).card : ℝ) ≤
          massOn prop12CollideMeasure prop12CollideDevice.setup x) ∧
      ¬ (inferenceComplexityMeasure prop12CollideMeasure prop12CollideDevice
          prop12CollideGamma prop12Collide_weaklyInfers
        ≤ (rangeFinset prop12CollideGamma).card *
            entropyOn prop12CollideMeasure prop12CollideDevice.setup) := by
  refine ⟨prop12Collide_massBound, fun h => ?_⟩
  have hgap := prop12Collide_gap
  have hpos : 0 < Real.log 3 := Real.log_pos (by norm_num)
  linarith

end AISafetyAtlas.Inference
