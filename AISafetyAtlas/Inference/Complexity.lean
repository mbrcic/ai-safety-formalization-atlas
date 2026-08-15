module

public import AISafetyAtlas.Inference.Device
public import AISafetyAtlas.Inference.FiniteRange
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Real.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Tactic.Linarith

/-!
# Inference complexity — Wolpert 2008 §5

The paper's analogue of Kolmogorov complexity: the length of a setup value
is `ℒ(x) = −ln |X⁻¹(x)|`, and the inference complexity of `Γ` is the sum,
over probes of `Γ`, of the shortest answering fibre (Definition 6). Theorem 4
is the encoding bound: if `C₁ ≫ C₂` and `C₂ > Γ`, the complexity difference
is at most `|Γ(U)|` times the worst-case emulation cost.

Stated under counting measure on a finite `U` (the source's Example 6). The
source allows a general measure `dμ`; the counting case is the one in which
`ℒ` is a fibre cardinality, so the bound is a statement about those
cardinalities rather than an uninterpreted integral.

The per-probe inequality is `minAnsweringLength_le_emulation` (pick the
shortest `C₂` fibre that answers the probe, then a `C₁` fibre that emulates
it); the displayed theorem sums that inequality.
-/

namespace AISafetyAtlas.Inference

open scoped Classical

variable {U : Type u}

/-- Counting volume of a setup fibre. -/
@[expose] public noncomputable def setupFibreCard [Fintype U] (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] (x : C.Setup) : ℕ :=
  (Finset.univ.filter (fun u : U => C.setup u = x)).card

/-- **Section 5 length.** `ℒ(x) = -ln |X⁻¹(x)|`. -/
@[expose] public noncomputable def setupLength [Fintype U] (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] (x : C.Setup) : ℝ :=
  -Real.log (setupFibreCard C x : ℝ)

/-- Realized setup values, as a finite set. Finiteness sits on the setup map,
which is Definition 6's own hypothesis (*"`X(U)` … countable"*), not on `U`. -/
@[expose] public noncomputable def realizedSetups (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] : Finset C.Setup :=
  rangeFinset C.setup

/-- The setup answers probe `f` of `Γ`. -/
@[expose] public def AnswersProbe (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (f : G → Bool) (x : C.Setup) : Prop :=
  C.Realized x ∧ ∀ w, C.setup w = x → C.concl w = f (Γ w)

@[expose] public noncomputable def answeringSet (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) :
    Finset C.Setup :=
  (realizedSetups C).filter (fun x => ∀ w, C.setup w = x → C.concl w = f (Γ w))

/-- Membership in the answering set, stated so callers never have to match the
`Finset.filter` decidability instance this module's `open scoped Classical` picks.

Without it a finite model elaborates `Nat.decidableForallFin` where the definition
carries `Classical.propDecidable`, and `Finset.mem_filter` fails to apply. -/
public theorem mem_answeringSet_iff (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) (x : C.Setup) :
    x ∈ answeringSet C Γ f ↔
      C.Realized x ∧ ∀ w, C.setup w = x → C.concl w = f (Γ w) := by
  unfold answeringSet realizedSetups
  rw [Finset.mem_filter, mem_rangeFinset]
  exact Iff.rfl

/-- The answering set is exactly the setups that answer the probe — the `Finset`
and the `Prop` say the same thing. Without this `AnswersProbe` is a transcription
of the source's condition that nothing in the tree consumes; the dependency view
lists such definitions for exactly this reason. -/
public theorem mem_answeringSet_iff_answersProbe (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) (x : C.Setup) :
    x ∈ answeringSet C Γ f ↔ AnswersProbe C Γ f x :=
  mem_answeringSet_iff C Γ f x

/-- **Definition 6's minima are over nonempty sets.** Under the definition's own
hypothesis `C > Γ`, every probe of a realized target value is answered by some
realized setup, so `minAnsweringLength` below never falls through to its
totalizing `0`. -/
public theorem answeringSet_nonempty_of_weaklyInfers (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] {Γ : U → G} (hw : WeaklyInfers C Γ)
    (γ : G) (hγ : ∃ w, Γ w = γ) :
    (answeringSet C Γ (probe γ)).Nonempty := by
  obtain ⟨x, hx, hfib⟩ := hw γ (probe γ) (isProbe_probe γ) hγ
  exact ⟨x, (mem_answeringSet_iff C Γ (probe γ) x).mpr ⟨hx, hfib⟩⟩

/-- The source's `min_{x : X=x ⇒ Y=f(Γ)} ℒ(x)`, for an arbitrary length
assignment `ℓ`.

`ℒ` is a **parameter**, not `setupLength`. Section 5 never uses any property of
it: every step of Theorem 4 below compares lengths through `inf'` and `sup'` and
never unfolds one. So the theorem holds for the counting length the source's
Example 6 uses, for `−log` of any measure's fibre mass, and for anything else. -/
@[expose] public noncomputable def minAnsweringLength (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  if h : (answeringSet C Γ f).Nonempty then
    (answeringSet C Γ f).inf' h ℓ
  else 0

/--
The Definition 6 sum, defined for every `C` and `Γ`.

Where no setup answers a probe, `minAnsweringLength` contributes `0`. The source
never evaluates that case: Definition 6 is stated only for `C > Γ`, so every
`min` there is over a nonempty set. Total failure would otherwise look *cheaper*
than success, since `ℒ` is `-log` of a fibre size and so is at most `0`. Use
`inferenceComplexity`, which carries the hypothesis, unless the totalization is
what you want.
-/
@[expose] public noncomputable def inferenceComplexityTotal (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum (fun γ => minAnsweringLength C ℓ Γ (probe γ))

/--
**Definition 6.** *"Let `C` be a device and `Γ` a function over `U` where `X(U)`
and `Γ(U)` are countable **and `C > Γ`**."*

The hypothesis is the source's and is carried in the signature, so the object is
never formed outside the regime the paper defines it on. It is proof-irrelevant:
`inferenceComplexity_eq_total` discharges it.
-/
@[expose] public noncomputable def inferenceComplexity
    (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (_hW : WeaklyInfers C Γ) : ℝ :=
  inferenceComplexityTotal C ℓ Γ

public theorem inferenceComplexity_eq_total (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hW : WeaklyInfers C Γ) :
    inferenceComplexity C ℓ Γ hW = inferenceComplexityTotal C ℓ Γ := rfl

@[expose] public def EmulatesAt (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) (x₁ : C₁.Setup) (x₂ : C₂.Setup) : Prop :=
  C₁.Realized x₁ ∧ C₂.Realized x₂ ∧
    ∀ w, C₁.setup w = x₁ → C₂.setup w = x₂ ∧ C₁.concl w = C₂.concl w

@[expose] public noncomputable def emulationSet (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] [FiniteRange C₁.setup]
    (x₂ : C₂.Setup) : Finset C₁.Setup :=
  (realizedSetups C₁).filter (fun x₁ =>
    ∀ w, C₁.setup w = x₁ → C₂.setup w = x₂ ∧ C₁.concl w = C₂.concl w)

@[expose] public noncomputable def emulationCostAt (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] [FiniteRange C₁.setup]
    (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ) (x₂ : C₂.Setup) : ℝ :=
  if h : (emulationSet C₁ C₂ x₂).Nonempty then
    (emulationSet C₁ C₂ x₂).inf' h (fun x₁ => ℓ₁ x₁ - ℓ₂ x₂)
  else 0

@[expose] public noncomputable def emulationCost (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ) : ℝ :=
  if h : (realizedSetups C₂).Nonempty then
    (realizedSetups C₂).sup' h (emulationCostAt C₁ C₂ ℓ₁ ℓ₂)
  else 0

/-- Likewise the emulation set is exactly the setups that emulate `x₂`. -/
public theorem mem_emulationSet_iff_emulatesAt (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] [FiniteRange C₁.setup]
    (x₂ : C₂.Setup) (hx₂ : C₂.Realized x₂) (x₁ : C₁.Setup) :
    x₁ ∈ emulationSet C₁ C₂ x₂ ↔ EmulatesAt C₁ C₂ x₁ x₂ := by
  unfold emulationSet realizedSetups EmulatesAt
  rw [Finset.mem_filter, mem_rangeFinset]
  exact ⟨fun h => ⟨h.1, hx₂, h.2⟩, fun h => ⟨h.1, h.2.2⟩⟩

public theorem emulationSet_nonempty_of_stronglyInfers
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] [FiniteRange C₁.setup]
    (hs : StronglyInfers C₁ C₂) {x₂ : C₂.Setup} (hx₂ : C₂.Realized x₂) :
    (emulationSet C₁ C₂ x₂).Nonempty := by
  obtain ⟨wt, hwt⟩ := C₂.concl_surjective true
  obtain ⟨x₁, hx₁, hfib⟩ := hs true id isProbe_id ⟨wt, hwt⟩ x₂ hx₂
  obtain ⟨w₁, hw₁⟩ := hx₁
  refine ⟨x₁, Finset.mem_filter.mpr ⟨?_, fun w hw => hfib w hw⟩⟩
  exact (mem_rangeFinset C₁.setup x₁).mpr ⟨w₁, hw₁⟩

/-- **Theorem 4.** Per-probe form, then summed. -/
public theorem minAnsweringLength_le_emulation
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ)
    {G : Type v''} [DecidableEq G] (Γ : U → G)
    (hs : StronglyInfers C₁ C₂) (hw : WeaklyInfers C₂ Γ)
    {γ : G} (hγ : ∃ w, Γ w = γ) :
    minAnsweringLength C₁ ℓ₁ Γ (probe γ) - minAnsweringLength C₂ ℓ₂ Γ (probe γ) ≤
      emulationCost C₁ C₂ ℓ₁ ℓ₂ := by
  classical
  obtain ⟨x₂0, hx₂0, hfib₂0⟩ := hw γ (probe γ) (isProbe_probe γ) hγ
  have hA₂0 : x₂0 ∈ answeringSet C₂ Γ (probe γ) := by
    simp [answeringSet, realizedSetups]
    obtain ⟨w, hw⟩ := hx₂0
    exact ⟨⟨w, hw⟩, hfib₂0⟩
  have hne₂ : (answeringSet C₂ Γ (probe γ)).Nonempty := ⟨x₂0, hA₂0⟩
  obtain ⟨x₂, hx₂mem, hx₂min⟩ := Finset.exists_mem_eq_inf' hne₂ ℓ₂
  have hx₂R : C₂.Realized x₂ := by
    have hximg : x₂ ∈ realizedSetups C₂ := (Finset.mem_filter.mp hx₂mem).1
    exact (mem_rangeFinset C₂.setup x₂).mp hximg
  have hfib₂ : ∀ w, C₂.setup w = x₂ → C₂.concl w = probe γ (Γ w) :=
    (Finset.mem_filter.mp hx₂mem).2
  have hEne := emulationSet_nonempty_of_stronglyInfers (C₁ := C₁) (C₂ := C₂) hs hx₂R
  obtain ⟨x₁, hx₁mem, hx₁min⟩ :=
    Finset.exists_mem_eq_inf' hEne (fun y => ℓ₁ y - ℓ₂ x₂)
  have hEm : ∀ w, C₁.setup w = x₁ → C₂.setup w = x₂ ∧ C₁.concl w = C₂.concl w :=
    (Finset.mem_filter.mp hx₁mem).2
  have hx₁R : C₁.Realized x₁ := by
    have hximg : x₁ ∈ realizedSetups C₁ := (Finset.mem_filter.mp hx₁mem).1
    exact (mem_rangeFinset C₁.setup x₁).mp hximg
  have hA₁ : x₁ ∈ answeringSet C₁ Γ (probe γ) := by
    simp [answeringSet, realizedSetups]
    obtain ⟨w, hw⟩ := hx₁R
    exact ⟨⟨w, hw⟩, fun w' hw' => (hEm w' hw').2.trans (hfib₂ w' (hEm w' hw').1)⟩
  have hne₁ : (answeringSet C₁ Γ (probe γ)).Nonempty := ⟨x₁, hA₁⟩
  have hmin₂ : minAnsweringLength C₂ ℓ₂ Γ (probe γ) = ℓ₂ x₂ := by
    unfold minAnsweringLength
    rw [dif_pos hne₂, hx₂min]
  have hmin₁ : minAnsweringLength C₁ ℓ₁ Γ (probe γ) ≤ ℓ₁ x₁ := by
    unfold minAnsweringLength
    rw [dif_pos hne₁]
    exact Finset.inf'_le ℓ₁ hA₁
  have hcost : ℓ₁ x₁ - ℓ₂ x₂ = emulationCostAt C₁ C₂ ℓ₁ ℓ₂ x₂ := by
    unfold emulationCostAt
    rw [dif_pos hEne, hx₁min]
  have hx₂in : x₂ ∈ realizedSetups C₂ := (Finset.mem_filter.mp hx₂mem).1
  have hneR : (realizedSetups C₂).Nonempty := ⟨x₂, hx₂in⟩
  have hle : emulationCostAt C₁ C₂ ℓ₁ ℓ₂ x₂ ≤ emulationCost C₁ C₂ ℓ₁ ℓ₂ := by
    unfold emulationCost
    rw [dif_pos hneR]
    exact Finset.le_sup' (emulationCostAt C₁ C₂ ℓ₁ ℓ₂) hx₂in
  linarith

/--
**Theorem 4.** *"Let `C₁` and `C₂` be two devices and `Γ` a function over `U`
where `Γ(U)` is finite, `C₁ ≫ C₂`, and `C₂ > Γ`. Then
`𝒞(Γ∣C₁) − 𝒞(Γ∣C₂) ≤ |Γ(U)| · max_{x₂} min_{x₁ : X₁=x₁ ⇒ X₂=x₂, Y₁=Y₂} [ℒ(x₁) − ℒ(x₂)]`."*

The bound is **one-sided in the source** — the bars in `|Γ(U)|` are the
cardinality of the target image (§1.2), not an absolute value around the
complexity difference. The hypotheses are not symmetric in `C₁` and `C₂`, so no
two-sided bound is available or claimed.

`C₁ > Γ`, needed to form `𝒞(Γ∣C₁)` at all, is Theorem 2(i) applied to the two
hypotheses.
-/
public theorem inferenceComplexity_le_of_stronglyInfers
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ)
    {G : Type v''} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hs : StronglyInfers C₁ C₂) (hw : WeaklyInfers C₂ Γ) :
    inferenceComplexity C₁ ℓ₁ Γ (weaklyInfers_of_stronglyInfers hs hw) -
        inferenceComplexity C₂ ℓ₂ Γ hw ≤
      ((rangeFinset Γ).card : ℝ) * emulationCost C₁ C₂ ℓ₁ ℓ₂ := by
  classical
  simp only [inferenceComplexity, inferenceComplexityTotal]
  rw [← Finset.sum_sub_distrib]
  have hle := Finset.sum_le_card_nsmul (rangeFinset Γ)
    (fun γ => minAnsweringLength C₁ ℓ₁ Γ (probe γ) -
      minAnsweringLength C₂ ℓ₂ Γ (probe γ))
    (emulationCost C₁ C₂ ℓ₁ ℓ₂) (fun γ hγ =>
      minAnsweringLength_le_emulation ℓ₁ ℓ₂ Γ hs hw ((mem_rangeFinset Γ γ).mp hγ))
  calc
    _ ≤ ((rangeFinset Γ).card • emulationCost C₁ C₂ ℓ₁ ℓ₂ : ℝ) := hle
    _ = ((rangeFinset Γ).card : ℝ) * emulationCost C₁ C₂ ℓ₁ ℓ₂ := nsmul_eq_mul _ _


/-! ## Definition 6 over an arbitrary setup range

2008 Definition 6 and 2018 Definition 7 both admit **countable** `X(U)`, and
`answeringSet` is a `Finset`, so every complexity object above carries
`[FiniteRange C.setup]`. 2018 Proposition 13's own scope delta names exactly
that restriction.

Under the acceptance rule the question is what the printed `min_x` needs in
order to denote. It needs the minimum to **exist** — a set of reals bounded
below and nonempty — not the index to be finite. So the restriction below is an
`IsLeast` hypothesis, which `[FiniteRange C.setup]` supplies and which a
countable range can also supply.

**What is *not* widened here, and why.** Theorem 4 multiplies by `|Γ(U)|`. On a
countably infinite target range that factor is not a real number, so the printed
inequality does not denote and finiteness of `Γ(U)` is forced rather than
chosen. The target side stays a `Finset`; only the setup side moves.
-/

/-- The answering setups as a **set**: the printed condition with no finiteness
on `X(U)`. -/
@[expose] public def answeringSetOn (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (f : G → Bool) : Set C.Setup :=
  {x | C.Realized x ∧ ∀ w, C.setup w = x → C.concl w = f (Γ w)}

/-- The printed `min_x` as an infimum over that set. It denotes for any setup
range; `IsLeast` below is what makes it the printed *minimum*. -/
@[expose] public noncomputable def minAnsweringLengthOn (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  sInf (ℓ '' answeringSetOn C Γ f)

/-- **Definition 6 with no finiteness on the setup range.** The sum is still
over `Γ(U)`, which the print keeps finite wherever it multiplies by `|Γ(U)|`. -/
@[expose] public noncomputable def inferenceComplexityOn (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum (fun γ => minAnsweringLengthOn C ℓ Γ (probe γ))

/-- Membership in the set form is the printed condition, verbatim. -/
public theorem mem_answeringSetOn_iff (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (f : G → Bool) (x : C.Setup) :
    x ∈ answeringSetOn C Γ f ↔
      C.Realized x ∧ ∀ w, C.setup w = x → C.concl w = f (Γ w) := Iff.rfl

/-- On a finite setup range the two answering sets have the same members. -/
public theorem coe_answeringSet (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) :
    (answeringSet C Γ f : Set C.Setup) = answeringSetOn C Γ f := by
  ext x
  rw [Finset.mem_coe, mem_answeringSet_iff, mem_answeringSetOn_iff]

/-- **The two forms agree wherever the printed minimum is attained.** `IsLeast`
is exactly *"the minimum exists and is this value"*, which is what `min_x`
asserts; on a finite nonempty answering set `Finset.inf'` supplies it. -/
public theorem minAnsweringLengthOn_eq_of_isLeast (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool) {m : ℝ}
    (hm : IsLeast (ℓ '' answeringSetOn C Γ f) m) :
    minAnsweringLengthOn C ℓ Γ f = m :=
  hm.csInf_eq

/-- Hence the set form recovers the `Finset` form on a finite setup range with a
nonempty answering set — the instance every existing theorem runs on. -/
public theorem minAnsweringLengthOn_eq_minAnsweringLength (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} (Γ : U → G) (f : G → Bool)
    (h : (answeringSet C Γ f).Nonempty) :
    minAnsweringLengthOn C ℓ Γ f = minAnsweringLength C ℓ Γ f := by
  classical
  rw [minAnsweringLength, dif_pos h]
  refine minAnsweringLengthOn_eq_of_isLeast C ℓ Γ f ⟨?_, ?_⟩
  · obtain ⟨x, hx, hxeq⟩ := Finset.exists_mem_eq_inf' h ℓ
    exact ⟨x, by rw [← coe_answeringSet]; exact hx, hxeq.symm⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [← coe_answeringSet] at hx
    exact Finset.inf'_le ℓ hx



/-- **Definition 6's two forms agree** on a finite setup range whose probes are
all answered, which is the instance every existing theorem runs on. The
`WeaklyInfers` hypothesis is what supplies the nonemptiness, and it is the
source's own `C > Γ`. -/
public theorem inferenceComplexityOn_eq_total (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hW : WeaklyInfers C Γ) :
    inferenceComplexityOn C ℓ Γ = inferenceComplexityTotal C ℓ Γ := by
  classical
  refine Finset.sum_congr rfl (fun γ hγ => ?_)
  refine minAnsweringLengthOn_eq_minAnsweringLength C ℓ Γ (probe γ) ?_
  obtain ⟨x, hxr, hxall⟩ := hW γ (probe γ) (isProbe_probe γ) ((mem_rangeFinset Γ γ).mp hγ)
  exact ⟨x, (mem_answeringSet_iff C Γ (probe γ) x).mpr ⟨hxr, hxall⟩⟩

/-- …and therefore with the printed `𝒞(Γ ∣ C)` itself. -/
public theorem inferenceComplexityOn_eq (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hW : WeaklyInfers C Γ) :
    inferenceComplexityOn C ℓ Γ = inferenceComplexity C ℓ Γ hW := by
  rw [inferenceComplexityOn_eq_total C ℓ Γ hW, ← inferenceComplexity_eq_total]



/-! ## Theorem 4 over an arbitrary setup range

The definition layer above needs no finiteness on `X(U)`. Theorem 4 still
consumed the `Finset` forms, because `emulationCost` is a `Finset.sup'` of
`Finset.inf'`s. The set forms below remove that, and the theorem is restated
over them.

The hypotheses are the printed `min` and `max` **existing**, which is what the
printed formula needs in order to denote and what a finite range supplies. They
are stated as `IsLeast`/`IsGreatest` rather than as boundedness, because
`min_{x₁}` and `max_{x₂}` assert attainment, not merely an infimum.
-/

/-- The emulating setups as a **set**. -/
@[expose] public def emulationSetOn (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) (x₂ : C₂.Setup) : Set C₁.Setup :=
  {x₁ | C₁.Realized x₁ ∧
    ∀ w, C₁.setup w = x₁ → C₂.setup w = x₂ ∧ C₁.concl w = C₂.concl w}

/-- The printed `min_{x₁}` of the emulation gap, as an infimum. -/
@[expose] public noncomputable def emulationCostAtOn (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ)
    (x₂ : C₂.Setup) : ℝ :=
  sInf ((fun x₁ => ℓ₁ x₁ - ℓ₂ x₂) '' emulationSetOn C₁ C₂ x₂)

/-- The printed `max_{x₂}`, as a supremum over the realized setups of `C₂`. -/
@[expose] public noncomputable def emulationCostOn (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ) : ℝ :=
  sSup (emulationCostAtOn C₁ C₂ ℓ₁ ℓ₂ '' {x₂ | C₂.Realized x₂})

public theorem mem_emulationSetOn_iff (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) (x₂ : C₂.Setup) (x₁ : C₁.Setup) :
    x₁ ∈ emulationSetOn C₁ C₂ x₂ ↔
      C₁.Realized x₁ ∧
        ∀ w, C₁.setup w = x₁ → C₂.setup w = x₂ ∧ C₁.concl w = C₂.concl w := Iff.rfl

public theorem coe_emulationSet (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    [FiniteRange C₁.setup] (x₂ : C₂.Setup) :
    (emulationSet C₁ C₂ x₂ : Set C₁.Setup) = emulationSetOn C₁ C₂ x₂ := by
  ext x₁
  simp only [Finset.mem_coe, emulationSet, Finset.mem_filter, realizedSetups,
    mem_rangeFinset, mem_emulationSetOn_iff]
  exact Iff.rfl

/--
**Theorem 4 with no finiteness on either setup range.**

Per probe: the difference of the two printed minima is at most the printed
emulation cost. The hypotheses say the printed `min`s and `max` are attained —
`hleast₂` for `C₂`'s answering minimum, `hleastE` for the emulation minimum at
that value, `hcost` for the outer maximum — and each is what the corresponding
printed operator asserts.
-/
public theorem minAnsweringLengthOn_le_emulationOn
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ)
    {G : Type v''} [DecidableEq G] (Γ : U → G) {γ : G}
    {x₂ : C₂.Setup} (hleast₂ : IsLeast (ℓ₂ '' answeringSetOn C₂ Γ (probe γ)) (ℓ₂ x₂))
    (hx₂mem : x₂ ∈ answeringSetOn C₂ Γ (probe γ))
    {x₁ : C₁.Setup}
    (hleastE : IsLeast ((fun y => ℓ₁ y - ℓ₂ x₂) '' emulationSetOn C₁ C₂ x₂)
      (ℓ₁ x₁ - ℓ₂ x₂))
    (hx₁mem : x₁ ∈ emulationSetOn C₁ C₂ x₂)
    (hbdd : BddBelow (ℓ₁ '' answeringSetOn C₁ Γ (probe γ)))
    (hcost : emulationCostAtOn C₁ C₂ ℓ₁ ℓ₂ x₂ ≤ emulationCostOn C₁ C₂ ℓ₁ ℓ₂) :
    minAnsweringLengthOn C₁ ℓ₁ Γ (probe γ) - minAnsweringLengthOn C₂ ℓ₂ Γ (probe γ)
      ≤ emulationCostOn C₁ C₂ ℓ₁ ℓ₂ := by
  -- `x₁` answers the probe, because it forces `C₂`'s answering fibre.
  have hA₁ : x₁ ∈ answeringSetOn C₁ Γ (probe γ) := by
    refine ⟨hx₁mem.1, fun w hw => ?_⟩
    obtain ⟨h₂, hcc⟩ := hx₁mem.2 w hw
    exact hcc.trans (hx₂mem.2 w h₂)
  have hmin₁ : minAnsweringLengthOn C₁ ℓ₁ Γ (probe γ) ≤ ℓ₁ x₁ :=
    csInf_le hbdd ⟨x₁, hA₁, rfl⟩
  have hmin₂ : minAnsweringLengthOn C₂ ℓ₂ Γ (probe γ) = ℓ₂ x₂ :=
    minAnsweringLengthOn_eq_of_isLeast C₂ ℓ₂ Γ (probe γ) hleast₂
  have hcostat : emulationCostAtOn C₁ C₂ ℓ₁ ℓ₂ x₂ = ℓ₁ x₁ - ℓ₂ x₂ :=
    hleastE.csInf_eq
  rw [hmin₂]
  linarith [hcost, hcostat.symm.le, hcostat.le]



/--
**Theorem 4, summed, with no finiteness on either setup range.**

`|Γ(U)|` is still a `Finset` cardinality, and that is forced: the printed bound
multiplies by it, so a countably infinite target range makes the right-hand side
not a real number. The setup ranges are free.

The single hypothesis is that each probe's per-probe bound holds — which
`minAnsweringLengthOn_le_emulationOn` supplies from attained minima, and which
`minAnsweringLength_le_emulation` supplies on a finite setup range.
-/
public theorem inferenceComplexityOn_le_of_perProbe
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ)
    {G : Type v''} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hprobe : ∀ γ ∈ rangeFinset Γ,
      minAnsweringLengthOn C₁ ℓ₁ Γ (probe γ) - minAnsweringLengthOn C₂ ℓ₂ Γ (probe γ)
        ≤ emulationCostOn C₁ C₂ ℓ₁ ℓ₂) :
    inferenceComplexityOn C₁ ℓ₁ Γ - inferenceComplexityOn C₂ ℓ₂ Γ ≤
      ((rangeFinset Γ).card : ℝ) * emulationCostOn C₁ C₂ ℓ₁ ℓ₂ := by
  classical
  simp only [inferenceComplexityOn]
  rw [← Finset.sum_sub_distrib]
  calc
    _ ≤ ((rangeFinset Γ).card • emulationCostOn C₁ C₂ ℓ₁ ℓ₂ : ℝ) :=
        Finset.sum_le_card_nsmul _ _ _ hprobe
    _ = ((rangeFinset Γ).card : ℝ) * emulationCostOn C₁ C₂ ℓ₁ ℓ₂ := nsmul_eq_mul _ _



/-! ## Definition 6 over a countable target range

The printed display is `∑_{f ∈ π(Γ)} min_x [ℒ(x)]` under the hypothesis that
`X(U)` **and** `Γ(U)` are countable. The setup side is handled above by
`answeringSetOn`. This section handles the target side.

Checked against the LaTeX source: Definition 6 carries **no `|Γ(U)|` factor** —
that belongs to Theorem 4, a different statement, which prints `Γ(U)` finite of
its own accord. So target-range finiteness here would be an atlas restriction,
not a forced one.

`∑'` totalizes to `0` when the family is not summable, so the printed sum is
this object exactly where the print denotes: on a summable family. Summability
is the hypothesis, not a property of the definition, which is why it appears on
the theorems below rather than in the definition.
-/

/-- One term of the countable complexity sum. Unrealized target values
contribute nothing — the guard is needed, because on an unrealized `γ` the probe
is constantly `false` and the answering set can still be inhabited. -/
@[expose] public noncomputable def complexityTerm (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) (γ : G) : ℝ :=
  if ∃ u, Γ u = γ then minAnsweringLengthOn C ℓ Γ (probe γ) else 0

/-- **Definition 6 with no finiteness on either range.** The sum is a `tsum`
over the whole target type; the realized values are the printed `π(Γ)`. -/
@[expose] public noncomputable def inferenceComplexitySum (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) : ℝ :=
  ∑' γ : G, complexityTerm C ℓ Γ γ

/-- Off the realized range the term vanishes, by the guard. -/
public theorem complexityTerm_eq_zero (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    {γ : G} (hγ : γ ∉ rangeFinset Γ) :
    complexityTerm C ℓ Γ γ = 0 := by
  rw [complexityTerm, if_neg]
  exact fun h => hγ ((mem_rangeFinset Γ γ).mpr h)

/-- **The countable form agrees with the finite one** wherever the finite one is
defined, so the widening adds reach and moves nothing already proved. -/
public theorem inferenceComplexitySum_eq_on (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] :
    inferenceComplexitySum C ℓ Γ = inferenceComplexityOn C ℓ Γ := by
  rw [inferenceComplexitySum, inferenceComplexityOn]
  rw [tsum_eq_sum (fun γ hγ => complexityTerm_eq_zero C ℓ Γ hγ)]
  refine Finset.sum_congr rfl (fun γ hγ => ?_)
  have h : ∃ u, Γ u = γ := (mem_rangeFinset Γ γ).mp hγ
  simp [complexityTerm, h]

/-- …and hence with the printed `𝒞(Γ ∣ C)` on a finite range under `C > Γ`. -/
public theorem inferenceComplexitySum_eq (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hW : WeaklyInfers C Γ) :
    inferenceComplexitySum C ℓ Γ = inferenceComplexity C ℓ Γ hW := by
  rw [inferenceComplexitySum_eq_on, inferenceComplexityOn_eq C ℓ Γ hW]



/-! ## Theorem 4 from strong inference, at set scope

`inferenceComplexityOn_le_of_perProbe` assumes the per-probe inequality. That
is not Theorem 4: the printed theorem derives it from `C₁ ≫ C₂` and `C₂ > Γ`,
so no scope claim may rest on the assumed-hypothesis form.

The derivation is below. What it needs beyond the printed hypotheses is
attainment of the printed `min` and `max`, and that is what the print asserts
by writing them: `min_{x₁ : X₁ = x₁ ⇒ …}` and `max_{x₂}` denote only when
attained. A finite setup range supplies attainment; so does a countable one
with the infimum reached. That is the acceptance rule, not a weakening.
-/

/-- **`C₂ > Γ` really does supply an answering setup**, so the witness `x₂` above
is not an extra assumption smuggled in beside the printed hypotheses. -/
public theorem answeringSetOn_nonempty_of_weaklyInfers
    {C : InferenceDevice.{u, v} U} {G : Type v''} [DecidableEq G] {Γ : U → G}
    (hw : WeaklyInfers C Γ) {γ : G} (hγ : ∃ w, Γ w = γ) :
    (answeringSetOn C Γ (probe γ)).Nonempty := by
  obtain ⟨x, hxr, hxall⟩ := hw γ (probe γ) (isProbe_probe γ) hγ
  exact ⟨x, hxr, hxall⟩

/-- …and `C₁ ≫ C₂` really does supply an emulating setup for any realized `x₂`. -/
public theorem emulationSetOn_nonempty_of_stronglyInfers
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) {x₂ : C₂.Setup} (hx₂ : C₂.Realized x₂) :
    (emulationSetOn C₁ C₂ x₂).Nonempty := by
  obtain ⟨x₁, hx₁r, hx₁all⟩ := hs true id isProbe_id (C₂.concl_surjective true) x₂ hx₂
  exact ⟨x₁, hx₁r, fun w hw => hx₁all w hw⟩



/--
**Theorem 4 from its printed hypotheses, with no finiteness on either setup
range.**

`hs` and `hw` are the printed premises and they are load-bearing: `hw` is what
makes each answering set nonempty and `hs` is what makes each emulation set
nonempty, so the attainment hypotheses below are only ever asked about sets that
are already known to be inhabited. That is the difference between this and
`inferenceComplexityOn_le_of_perProbe`, which assumes the conclusion per probe.

The attainment hypotheses are the printed `min` and `max` denoting. A finite
setup range supplies them — that is `minAnsweringLength_le_emulation`, which
gets both from `Finset.exists_mem_eq_inf'` — and so does a countable range whose
infima are reached.
-/
public theorem inferenceComplexityOn_le_of_stronglyInfers
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ)
    {G : Type v''} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hs : StronglyInfers C₁ C₂) (hw : WeaklyInfers C₂ Γ)
    (hattain₂ : ∀ γ : G, (answeringSetOn C₂ Γ (probe γ)).Nonempty →
      ∃ x₂ ∈ answeringSetOn C₂ Γ (probe γ),
        IsLeast (ℓ₂ '' answeringSetOn C₂ Γ (probe γ)) (ℓ₂ x₂))
    (hattainE : ∀ x₂ : C₂.Setup, (emulationSetOn C₁ C₂ x₂).Nonempty →
      ∃ x₁ ∈ emulationSetOn C₁ C₂ x₂,
        IsLeast ((fun y => ℓ₁ y - ℓ₂ x₂) '' emulationSetOn C₁ C₂ x₂) (ℓ₁ x₁ - ℓ₂ x₂))
    (hbdd : ∀ γ : G, BddBelow (ℓ₁ '' answeringSetOn C₁ Γ (probe γ)))
    (hcost : ∀ x₂ : C₂.Setup, C₂.Realized x₂ →
      emulationCostAtOn C₁ C₂ ℓ₁ ℓ₂ x₂ ≤ emulationCostOn C₁ C₂ ℓ₁ ℓ₂) :
    inferenceComplexityOn C₁ ℓ₁ Γ - inferenceComplexityOn C₂ ℓ₂ Γ ≤
      ((rangeFinset Γ).card : ℝ) * emulationCostOn C₁ C₂ ℓ₁ ℓ₂ := by
  refine inferenceComplexityOn_le_of_perProbe ℓ₁ ℓ₂ Γ (fun γ hγ => ?_)
  -- `C₂ > Γ` makes the answering set nonempty, so its minimum is asked for.
  obtain ⟨x₂, hx₂mem, hleast₂⟩ :=
    hattain₂ γ (answeringSetOn_nonempty_of_weaklyInfers hw ((mem_rangeFinset Γ γ).mp hγ))
  -- `C₁ ≫ C₂` makes the emulation set at that value nonempty.
  obtain ⟨x₁, hx₁mem, hleastE⟩ :=
    hattainE x₂ (emulationSetOn_nonempty_of_stronglyInfers hs hx₂mem.1)
  exact minAnsweringLengthOn_le_emulationOn ℓ₁ ℓ₂ Γ hleast₂ hx₂mem hleastE hx₁mem
    (hbdd γ) (hcost x₂ hx₂mem.1)


end AISafetyAtlas.Inference