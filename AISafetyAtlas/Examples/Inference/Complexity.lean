module

public import AISafetyAtlas.Inference
public import AISafetyAtlas.Examples.Inference.Device

/-!
# Section 5, inhabited

Every other part of this development has a worked model. Section 5 had none: no
example mentioned `inferenceComplexity`, `setupLength`, `answeringSet` or
`emulationCost`, so Definition 6 was a number nothing had ever computed and
Theorem 4 a bound nothing had ever met.

A definition cannot be vacuous, but it can be quietly wrong. Definition 6
totalizes to `0` wherever no setup answers a probe, and the docstring warns that
total failure would then look *cheaper* than success. Nothing checked that the
totalization was not what the definition always returned.

Two models here:

1. **Definition 6 computed.** The Proposition 1(i) device: its setup is the
   identity on a three-state universe, so every fibre is a singleton, every
   length is `−log 1 = 0`, and the complexity is `0` — reached through genuine
   minima over nonempty answering sets, not through the totalization.
2. **Theorem 4 attained.** The section-6 pair `fineDevice ≫ coarseForcedDevice`
   against a target both can answer. Here the theorem's inequality holds with
   **equality**: `𝒞(Γ∣C₁) − 𝒞(Γ∣C₂) = 2 · log 2 = |Γ(U)| · emulation cost`. A
   bound that is merely satisfied might be satisfied because both sides are
   vacuous or because the bound is hopelessly loose; this one is met exactly, so
   no smaller multiple of the emulation cost would do.
-/

namespace AISafetyAtlas.Examples.Inference.Complexity

open AISafetyAtlas.Inference
open AISafetyAtlas.Examples.Inference.Device

/-! ## Shared arithmetic

Every `inf'`/`sup'` in section 5 below is over a set on which the length function
is constant, so the extremum is that constant. -/

public theorem inf'_of_const {α : Type*} {s : Finset α} (h : s.Nonempty)
    (g : α → ℝ) (c : ℝ) (hg : ∀ y ∈ s, g y = c) : s.inf' h g = c := by
  refine le_antisymm ?_ (Finset.le_inf' _ _ (fun y hy => le_of_eq (hg y hy).symm))
  obtain ⟨y, hy⟩ := h
  calc s.inf' _ g ≤ g y := Finset.inf'_le _ hy
    _ = c := hg y hy

public theorem sup'_of_const {α : Type*} {s : Finset α} (h : s.Nonempty)
    (g : α → ℝ) (c : ℝ) (hg : ∀ y ∈ s, g y = c) : s.sup' h g = c := by
  refine le_antisymm (Finset.sup'_le _ _ (fun y hy => le_of_eq (hg y hy))) ?_
  obtain ⟨y, hy⟩ := h
  calc c = g y := (hg y hy).symm
    _ ≤ s.sup' _ g := Finset.le_sup' _ hy

/-! ## 1. Definition 6 computed on the Proposition 1(i) device -/

/-- Every probe of the target is answered by some realized setup, so Definition 6's
minimum is never the totalization here. -/
public theorem witness_answeringSet_nonempty (γ : Bool) (hγ : ∃ w, wTarget w = γ) :
    (answeringSet witnessInfers wTarget (probe γ)).Nonempty :=
  answeringSet_nonempty_of_weaklyInfers witnessInfers witnessInfers_weaklyInfers γ hγ

/-- The setup is the identity, so every fibre is a singleton. -/
public theorem witness_fibreCard (x : Fin 3) : setupFibreCard witnessInfers x = 1 := by
  classical
  unfold setupFibreCard
  have : (Finset.univ.filter (fun u : Fin 3 => witnessInfers.setup u = x)) = {x} := by
    ext u
    simp [witnessInfers]
  rw [this, Finset.card_singleton]

/-- Hence every Definition 6 length is `0`. -/
public theorem witness_setupLength (x : Fin 3) : setupLength witnessInfers x = 0 := by
  unfold setupLength
  rw [witness_fibreCard]
  simp

/-- **Definition 6 computed.** The complexity of the target for this device is `0`,
and it is reached through minima over nonempty answering sets. -/
public theorem witness_inferenceComplexity :
    inferenceComplexity witnessInfers (setupLength witnessInfers) wTarget
      witnessInfers_weaklyInfers = 0 := by
  unfold inferenceComplexity inferenceComplexityTotal
  refine Finset.sum_eq_zero (fun γ hγ => ?_)
  unfold minAnsweringLength
  rw [dif_pos (witness_answeringSet_nonempty γ ((mem_rangeFinset wTarget γ).mp hγ))]
  exact inf'_of_const _ _ 0 (fun y _ => witness_setupLength y)

/-! ## 2. Theorem 4 attained

`fineDevice ≫ coarseForcedDevice` is already proved (section 6 of
`Examples.Inference.Device`). Theorem 4 needs one more thing the source demands
and nothing here had supplied: a target the *coarse* device weakly infers.

The coarse setup partitions `Fin 4` into `{0,1}` and `{2,3}`, and its conclusion
is the parity bit. So the target has to agree with parity on one block and
disagree on the other — otherwise one of the two `Bool` probes has no answering
fibre. -/

/-- The target: parity on `{0,1}`, its negation on `{2,3}`. -/
public abbrev gamma4 : Fin 4 → Bool := fun i => decide (i.val = 1 ∨ i.val = 2)

/-- **`C₂ > Γ`.** Each probe is answered, but by a *different* block: the identity
probe by `{0,1}`, the negation probe by `{2,3}`. -/
public theorem coarse_weaklyInfers_gamma4 : WeaklyInfers coarseForcedDevice gamma4 := by
  intro γ f hf _
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨false, ⟨0, by decide⟩, by decide⟩
  · exact ⟨true, ⟨2, by decide⟩, by decide⟩

/-- `C₁ > Γ` is Theorem 2(i), not a separate model obligation. -/
public theorem fine_weaklyInfers_gamma4 : WeaklyInfers fineDevice gamma4 :=
  weaklyInfers_of_stronglyInfers fine_stronglyInfers_coarse coarse_weaklyInfers_gamma4

public theorem coarse_realized (x : Bool) : coarseForcedDevice.Realized x := by
  cases x
  · exact ⟨0, by decide⟩
  · exact ⟨2, by decide⟩

/-! ### Lengths

The fine setup is the identity — singleton fibres, length `0`. The coarse setup
has two fibres of size two — length `−log 2`. -/

public theorem fine_fibreCard (x : Fin 4) : setupFibreCard fineDevice x = 1 := by
  classical
  unfold setupFibreCard
  have : (Finset.univ.filter (fun u : Fin 4 => fineDevice.setup u = x)) = {x} := by
    ext u
    simp [fineDevice]
  rw [this, Finset.card_singleton]

public theorem fine_setupLength (x : Fin 4) : setupLength fineDevice x = 0 := by
  unfold setupLength
  rw [fine_fibreCard]
  simp

public theorem coarse_fibreCard (x : Bool) : setupFibreCard coarseForcedDevice x = 2 := by
  classical
  unfold setupFibreCard
  cases x
  · have h : (Finset.univ.filter (fun u : Fin 4 => coarseForcedDevice.setup u = false))
        = ({0, 1} : Finset (Fin 4)) := by
      ext u
      fin_cases u <;> simp [coarseForcedDevice]
    rw [h]
    decide
  · have h : (Finset.univ.filter (fun u : Fin 4 => coarseForcedDevice.setup u = true))
        = ({2, 3} : Finset (Fin 4)) := by
      ext u
      fin_cases u <;> simp [coarseForcedDevice]
    rw [h]
    decide

public theorem coarse_setupLength (x : Bool) :
    setupLength coarseForcedDevice x = -Real.log 2 := by
  unfold setupLength
  rw [coarse_fibreCard]
  norm_num

/-! ### The two complexities -/

public theorem rangeFinset_gamma4 : rangeFinset gamma4 = (Finset.univ : Finset Bool) := by
  ext b
  simp only [mem_rangeFinset, Finset.mem_univ, iff_true]
  cases b
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩

/-- `𝒞(Γ∣C₁) = 0`: the fine device pays nothing, its fibres being singletons. -/
public theorem fine_complexity :
    inferenceComplexity fineDevice (setupLength fineDevice) gamma4
      fine_weaklyInfers_gamma4 = 0 := by
  unfold inferenceComplexity inferenceComplexityTotal
  refine Finset.sum_eq_zero (fun γ hγ => ?_)
  unfold minAnsweringLength
  rw [dif_pos (answeringSet_nonempty_of_weaklyInfers fineDevice fine_weaklyInfers_gamma4 γ
    ((mem_rangeFinset gamma4 γ).mp hγ))]
  exact inf'_of_const _ _ 0 (fun y _ => fine_setupLength y)

/-- `𝒞(Γ∣C₂) = −2·log 2`: each of the two probes is answered only by a
two-element fibre. -/
public theorem coarse_complexity :
    inferenceComplexity coarseForcedDevice (setupLength coarseForcedDevice) gamma4
      coarse_weaklyInfers_gamma4 = -(2 * Real.log 2) := by
  unfold inferenceComplexity inferenceComplexityTotal
  have hterm : ∀ γ ∈ rangeFinset gamma4,
      minAnsweringLength coarseForcedDevice (setupLength coarseForcedDevice) gamma4 (probe γ)
        = -Real.log 2 := by
    intro γ hγ
    unfold minAnsweringLength
    rw [dif_pos (answeringSet_nonempty_of_weaklyInfers coarseForcedDevice
      coarse_weaklyInfers_gamma4 γ ((mem_rangeFinset gamma4 γ).mp hγ))]
    exact inf'_of_const _ _ _ (fun y _ => coarse_setupLength y)
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, rangeFinset_gamma4]
  simp

/-! ### The emulation cost -/

public theorem emulationCostAt_eq (x₂ : Bool) :
    emulationCostAt fineDevice coarseForcedDevice (setupLength fineDevice)
      (setupLength coarseForcedDevice) x₂ = Real.log 2 := by
  unfold emulationCostAt
  rw [dif_pos (emulationSet_nonempty_of_stronglyInfers fine_stronglyInfers_coarse
    (coarse_realized x₂))]
  refine inf'_of_const _ _ _ (fun y _ => ?_)
  rw [fine_setupLength, coarse_setupLength]
  ring

public theorem emulationCost_eq :
    emulationCost fineDevice coarseForcedDevice (setupLength fineDevice)
      (setupLength coarseForcedDevice) = Real.log 2 := by
  unfold emulationCost
  have hne : (realizedSetups coarseForcedDevice).Nonempty := by
    refine ⟨false, ?_⟩
    unfold realizedSetups
    exact (mem_rangeFinset _ _).mpr (coarse_realized false)
  rw [dif_pos hne]
  exact sup'_of_const _ _ _ (fun y _ => emulationCostAt_eq y)

/-! ### Theorem 4 on the witness -/

/-- **Theorem 4 instantiated.** Every hypothesis holds, so the bound applies. -/
public theorem witness_thm4 :
    inferenceComplexity fineDevice (setupLength fineDevice) gamma4
        fine_weaklyInfers_gamma4 -
      inferenceComplexity coarseForcedDevice (setupLength coarseForcedDevice) gamma4
        coarse_weaklyInfers_gamma4 ≤
    ((rangeFinset gamma4).card : ℝ) *
      emulationCost fineDevice coarseForcedDevice (setupLength fineDevice)
        (setupLength coarseForcedDevice) :=
  inferenceComplexity_le_of_stronglyInfers _ _ gamma4 fine_stronglyInfers_coarse
    coarse_weaklyInfers_gamma4

/-- **Theorem 4's bound is attained.** Both sides are `2·log 2`.

So the inequality is not slack on this pair, and the factor `|Γ(U)|` in the
source's statement cannot be replaced by anything smaller: the emulation cost is
paid once per target value, and here it is paid in full every time. -/
public theorem witness_thm4_tight :
    inferenceComplexity fineDevice (setupLength fineDevice) gamma4
        fine_weaklyInfers_gamma4 -
      inferenceComplexity coarseForcedDevice (setupLength coarseForcedDevice) gamma4
        coarse_weaklyInfers_gamma4 =
    ((rangeFinset gamma4).card : ℝ) *
      emulationCost fineDevice coarseForcedDevice (setupLength fineDevice)
        (setupLength coarseForcedDevice) := by
  rw [fine_complexity, coarse_complexity, emulationCost_eq, rangeFinset_gamma4]
  simp


/-! ## The set-scope vocabulary, at the same pair of devices

The set-scope form of Theorem 4 additionally asks for attainment of both
minima, boundedness below of the answering images, and a pointwise
emulation-cost bound -- four conditions the `Finset` form gets for free from
finiteness and `witness_thm4` therefore never has to state. `witness_thm4_on`
below discharges all four at this pair, via `coe_answeringSet`/
`coe_emulationSet` transporting the same `Finset.exists_mem_eq_inf'` argument
`minAnsweringLengthOn_eq_minAnsweringLength` already makes generically.
-/

/-- **Theorem 4, set-scope, from strong inference.** The four attainment
hypotheses `inferenceComplexityOn_le_of_stronglyInfers` asks for beyond
`hs`/`hw` are all supplied by finiteness of both devices' setup types, via
`coe_answeringSet`/`coe_emulationSet` and `Finset.exists_mem_eq_inf'` — the same
route `minAnsweringLengthOn_eq_minAnsweringLength` and `emulationCostAt_eq`
already take for this pair. -/
public theorem witness_thm4_on :
    inferenceComplexityOn fineDevice (setupLength fineDevice) gamma4 -
      inferenceComplexityOn coarseForcedDevice (setupLength coarseForcedDevice) gamma4 ≤
    ((rangeFinset gamma4).card : ℝ) *
      emulationCostOn fineDevice coarseForcedDevice
        (setupLength fineDevice) (setupLength coarseForcedDevice) := by
  classical
  refine inferenceComplexityOn_le_of_stronglyInfers
    (setupLength fineDevice) (setupLength coarseForcedDevice) gamma4
    fine_stronglyInfers_coarse coarse_weaklyInfers_gamma4 ?_ ?_ ?_ ?_
  · intro γ hne
    have hFne : (answeringSet coarseForcedDevice gamma4 (probe γ)).Nonempty := by
      rw [← Finset.coe_nonempty, coe_answeringSet]; exact hne
    obtain ⟨x, hx, hxeq⟩ :=
      Finset.exists_mem_eq_inf' hFne (setupLength coarseForcedDevice)
    have hxOn : x ∈ answeringSetOn coarseForcedDevice gamma4 (probe γ) := by
      rw [← coe_answeringSet]; exact hx
    refine ⟨x, hxOn, ⟨x, hxOn, rfl⟩, ?_⟩
    rintro y ⟨x', hx', rfl⟩
    rw [← coe_answeringSet] at hx'
    rw [← hxeq]
    exact Finset.inf'_le (setupLength coarseForcedDevice) hx'
  · intro x₂ hne
    have hFne : (emulationSet fineDevice coarseForcedDevice x₂).Nonempty := by
      rw [← Finset.coe_nonempty, coe_emulationSet]; exact hne
    obtain ⟨x₁, hx₁, hxeq⟩ := Finset.exists_mem_eq_inf' hFne
      (fun y => setupLength fineDevice y - setupLength coarseForcedDevice x₂)
    have hx₁On : x₁ ∈ emulationSetOn fineDevice coarseForcedDevice x₂ := by
      rw [← coe_emulationSet]; exact hx₁
    refine ⟨x₁, hx₁On, ⟨x₁, hx₁On, rfl⟩, ?_⟩
    rintro y ⟨x', hx', rfl⟩
    rw [← coe_emulationSet] at hx'
    rw [← hxeq]
    exact Finset.inf'_le _ hx'
  · intro γ
    exact (Set.toFinite
      (setupLength fineDevice '' answeringSetOn fineDevice gamma4 (probe γ))).bddBelow
  · intro x₂ hx₂
    exact le_csSup (Set.toFinite _).bddAbove ⟨x₂, hx₂, rfl⟩

/-- **Answering-set membership is answering the probe**, at the coarse device. -/
public theorem coarse_mem_answeringSet_iff (f : Bool → Bool) (x : Bool) :
    x ∈ answeringSet coarseForcedDevice gamma4 f ↔
      AnswersProbe coarseForcedDevice gamma4 f x :=
  mem_answeringSet_iff_answersProbe coarseForcedDevice gamma4 f x

/-- **Emulation-set membership is emulating at that setup.** The realizedness
hypothesis is `coarse_realized`, which holds for every coarse setup. -/
public theorem fine_mem_emulationSet_iff (x₂ : Bool) (x₁ : Fin 4) :
    x₁ ∈ emulationSet fineDevice coarseForcedDevice x₂ ↔
      EmulatesAt fineDevice coarseForcedDevice x₁ x₂ :=
  mem_emulationSet_iff_emulatesAt fineDevice coarseForcedDevice x₂
    (coarse_realized x₂) x₁

/-- The finite emulation set and its set-scope counterpart agree, so the two
readings of Theorem 4 are about the same object. -/
public theorem fine_coe_emulationSet (x₂ : Bool) :
    (emulationSet fineDevice coarseForcedDevice x₂ : Set (Fin 4))
      = emulationSetOn fineDevice coarseForcedDevice x₂ :=
  coe_emulationSet fineDevice coarseForcedDevice x₂

/-- **The summed complexity is the printed `𝒞(Γ ∣ C)`** on this finite range,
under the definition's own weak-inference hypothesis. -/
public theorem coarse_inferenceComplexitySum_eq :
    inferenceComplexitySum coarseForcedDevice (setupLength coarseForcedDevice) gamma4
      = inferenceComplexity coarseForcedDevice (setupLength coarseForcedDevice)
          gamma4 coarse_weaklyInfers_gamma4 :=
  inferenceComplexitySum_eq coarseForcedDevice (setupLength coarseForcedDevice)
    gamma4 coarse_weaklyInfers_gamma4

end AISafetyAtlas.Examples.Inference.Complexity
