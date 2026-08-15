module

public import Mathlib.Logic.Function.Defs
public import Mathlib.Data.Bool.Basic

/-!
# Inference devices — Wolpert 2008, the impossibility core

A source-faithful reconstruction of the definitions and impossibility results of
D. H. Wolpert, *Physical limits of inference*, Physica D 237(9):1257–1281, 2008
(arXiv:0708.1362), sections 3.1–3.4, 4.2 and 7. Sections 5, 6, 8 and 9
live in the sibling modules `Complexity`, `Reality`, `Stochastic` and
`SelfAware`.

## What an inference device is

The paper's claim is that observation, prediction, and recollection share one
mathematical structure. A device over a set `U` of universes is a pair of
functions on `U`: a **setup** function recording how the device is configured,
and a **conclusion** function recording what it ends up asserting. Nothing is
assumed about how the two are related.

## Fidelity to the source

Stated exactly, because the encoding is the claim.

* **Def 1** is `InferenceDevice`. The paper's conclusion function is onto
  `𝔹 = {-1, +1}`; here it is onto `Bool`. That is a renaming of a two-element
  codomain: the paper's identity probe `f(y) = y` becomes `id`, and its negation
  probe `f(y) = -y` becomes `not`. It is **not** the only encoding decision —
  the rest of this list is.
* **Def 2 as printed is `IsSourceProbe`** — *a mapping from a set with at least
  two elements **onto** `𝔹` that equals `1` for one and only one argument*. The
  working predicate below is `IsProbe`, which keeps only the unique-true clause,
  and **every consumer (`WeaklyInfers`, `StronglyInfers`, `Controls`) quantifies
  over `IsProbe`, not `IsSourceProbe`.**
  The two coincide wherever the source is defined: `surjective_of_isProbe` shows
  unique-true forces onto-`𝔹` as soon as the range has a second point, and
  `isSourceProbe_iff` packages that. The only divergence is a **singleton** range,
  which the source excludes by its global stipulation that every function over `U`
  takes at least two values. `weaklyInfers_iff_sourceProbes` is the bridge: on any
  range with two values, quantifying over `IsProbe` and over `IsSourceProbe` give
  the same Definition 3. So the working predicate is a convenience, not a weaker
  claim — but it *is* the predicate in every signature, and a consumer
  instantiating `IsProbe` on a singleton range is not using Wolpert's probe.
  Definition 3 quantifies over probe **functions**, as the source's `∀ f ∈ π(Γ)`
  does, and nothing needs decidable equality on the target range; `probe` is
  supplied as the canonical Kronecker delta when a range happens to have it,
  purely so finite models stay executable. `exists_isProbe` constructs a probe at
  every point, so `∀ f, IsProbe f γ → …` is never vacuously true.
  The source's two-value stipulation is **not** imposed here, on targets or on
  setup functions. On the setup side the drop is load-bearing: a device whose setup is constant is
  `Distinguishable` from itself, which the source denies. Theorem 1 then applies
  to that pair and yields `¬ InfersDevice C C`, already given by Proposition 1(ii).
  So Theorem 1 is **stronger** than in the source — it covers pairs the source's
  hypothesis never reaches. The witness is
  `Examples.Inference.Device.constSetup_distinguishable_self`.
* **Realized values.** Where the source writes `∀ x₁, x₂` in Definitions 4, 5 and
  8, the quantifier ranges over values the setup function actually takes, as its
  own shorthand convention in Definition 3 (`∃ x ∈ X(U)`) fixes. That reading is
  forced: over the whole setup type, distinguishability could never hold for a
  device with an unused setup value. It also makes Theorem 1 stronger, since more
  pairs of devices qualify as distinguishable.
* **Def 3** is `WeaklyInfers`, with the paper's quantifier order preserved:
  *for every probe there exists a setup value* such that the conclusion answers
  that probe throughout the fibre. The setup value is required to be **realized**,
  as the source's `∃ x ∈ X(U)` demands; dropping that would make weak inference
  vacuously true whenever the setup type has an unused value.
* **Def 4** is `Distinguishable`, quantified over realized setup values on both
  sides, matching the source's shorthand convention. Combined with the dropped
  two-value stipulation on setups, self-distinguishability is possible (above).
* **"Identical partitions"** in Theorem 5 is represented as equality of the two
  same-fibre relations. Two functions induce the same partition exactly when their
  kernels agree, so this is the partition statement, up to the relabelling of setup
  ranges the source itself describes.
* **Def 5** is `StronglyInfers`.
* **Def 8** is `SemiControls` and `Controls`.
* **Prop 1(i)**, **Prop 1(ii)**, **Prop 2(i)**, **Prop 2(ii)**, **Cor 1(i)**,
  **Cor 2**, **Thm 1**, **Thm 2**, the immediate strong-to-weak and
  strong-to-semi-control consequences, **Thm 3**, **Thm 5** and **Cor 3**
  (all three parts, with (ii) as `¬A ∧ ¬B`) are the theorems below.

**One strengthening.** The source proves Theorem 5 using the axiom of choice, to
pick a setup value for each value of the other device's setup. The proof here
needs no such selection: it shows directly that the block containing any state is
common to both partitions. The statement is unchanged.

`#print axioms` reports that Theorem 5 and every impossibility result here —
Proposition 1(ii), Theorems 1, 2 and 3, and the control transports — depend on
**no axioms at all**, not merely on the classical three the atlas permits.

The existence half is classical, and says so: `separatingDevice_weaklyInfers`,
`exists_isProbe` and the Proposition 1(i) / Corollary 1(i) wrappers report
`{propext, Classical.choice, Quot.sound}`, while the constructive
`semiControls_of_controls` reports `propext` alone. The unrestricted classical
`semiControls_of_controls_classical` carries the generic probe construction.
Constructing a device, or a probe at an arbitrary point, is where the classical
content sits; refuting one never needs it. Re-measure rather than assume — this
profile has already drifted once.

## What is not here

Section 5 (inference complexity, Def 6 and Thm 4), section 6 (realities and
copies, Def 7, Lemma 1, Props 3–5), section 8 (**stochastic devices**, Defs 9–11
and Prop 6 — the only place in the paper a probability measure `P` over `U`
appears: *"in the analysis above there is no probability measure P over U"*),
and section 9 (self-aware devices, Defs 12–14, Thms 6–7, Prop 7, Cors 4–5)
are mechanized in the sibling modules, not in this file.

**Corollary 1(ii) is refuted rather than omitted.** As literally stated — *any*
`Γ` over any `U` is inferred by some device — it is false: no device over a
two-state universe weakly infers the identity, since its conclusion function would
have to be constant against the surjectivity Definition 1 demands. The countermodel
is `Examples.Inference.Device.no_device_weaklyInfers_id_on_bool`. The statement
needs the hypothesis its own proof uses, a proper `W ⊂ U` on which `Γ` already
attains every value; over a large `U` that is automatic.

Also not here: Wolpert 2018's knowledge operator; its statement map is recorded in
[`docs/provenance/wolpert-2018-knowledge.md`](../../docs/provenance/wolpert-2018-knowledge.md).

## Relation to `Knowledge.Knowable` — none, and this was checked

`Knowable r f` is `∃ decoder, ∀ ω, f ω = decoder (r ω)`. Weak inference is
`∀ probe, ∃ setup, ∀ u in that fibre, …` over a **fixed** conclusion function.
Neither implies the other, and both failures are witnessed on finite models:

* a device whose setup is the identity and whose conclusion is the negation makes
  the target knowable while weakly inferring nothing;
* a three-state device weakly infers a target that does not factor through its
  setup at all.

See `AISafetyAtlas.Examples.Inference.Device`. Do **not** package weak inference
as a form of knowability; the quantifier alternation and the fixed conclusion
function are both load-bearing.

That non-identification stands. What builds on it is
`AISafetyAtlas.Knowledge.Devices`, which states the **conditional** transports
between the two — a knowability witness for the device's own setup-and-conclusion
pair, present in every realized block and straddling the target value, refutes
Definition 3 and Definition 11 alike. Those are atlas lemmas about when the two
mechanisms talk to each other, not a claim that they coincide, and no declaration
in this file depends on them.

## Explicit non-claims

No probability, no dynamics, no physics. `U` is an arbitrary set of universes and
nothing here makes it physical; the paper's own claim is that its results hold
*independent* of the physical laws, and the Lean statements inherit exactly that
generality and no more. No AI-system reading follows without a separate reviewed
bridge.
-/

namespace AISafetyAtlas.Inference

universe u v v' v''

/-! ## Devices -/

/--
**Definition 1.** An inference device over `U`: a setup function recording how the
device is configured, and a conclusion function recording what it asserts.

`Setup` is a field rather than a parameter so that devices with different setup
types can be compared in one statement, as the source's pairwise results require.
The conclusion function is onto `Bool` — the source's surjectivity requirement on
`Y`, which is what makes both probes of its range available.
-/
public structure InferenceDevice (U : Type u) where
  /-- The values the device can be configured to. -/
  Setup : Type v
  /-- How the device is set up in a given universe. -/
  setup : U → Setup
  /-- What the device concludes in a given universe. -/
  concl : U → Bool
  /-- Both conclusions are reachable. -/
  concl_surjective : Function.Surjective concl

variable {U : Type u}

/-- A setup value the device actually takes somewhere. -/
@[expose] public def InferenceDevice.Realized (C : InferenceDevice.{u, v} U)
    (x : C.Setup) : Prop :=
  ∃ w : U, C.setup w = x

/-! ## Probes -/

/--
**Definition 2.** A probe of a set: the map onto `Bool` that is `true` at exactly
one argument.

For a two-valued range these are the source's identity and negation probes, which
is all the impossibility results use.
-/
@[expose] public def IsProbe {A : Type v'} (f : A → Bool) (a : A) : Prop :=
  ∀ b : A, f b = true ↔ b = a

/-- The source's **identity probe** `f(y) = y` is the probe of `𝔹` at `true`. -/
public theorem isProbe_id : IsProbe (id : Bool → Bool) true := by
  intro b
  cases b
  · exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- The source's **negation probe** `f(y) = -y` is the probe of `𝔹` at `false`. -/
public theorem isProbe_not : IsProbe (fun b : Bool => !b) false := by
  intro b
  cases b
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

/--
The canonical probe when the target range has decidable equality — a Kronecker
delta. Supplied for executable models; nothing in the theory requires it.
-/
@[expose] public def probe {A : Type v'} [DecidableEq A] (a : A) : A → Bool :=
  fun b => decide (b = a)

public theorem isProbe_probe {A : Type v'} [DecidableEq A] (a : A) :
    IsProbe (probe a) a := by
  intro b; simp [probe]

/--
**A probe exists at every point.** Classically `decide (· = a)` is one, so the
`∀ f, IsProbe f γ → …` in the definitions below is never vacuously satisfied: any
proof of weak inference must handle a genuine probe. This is what makes dropping
the source's "at least two elements" stipulation safe rather than merely tidy.
-/
public theorem exists_isProbe {A : Type v'} (a : A) : ∃ f : A → Bool, IsProbe f a := by
  classical
  exact ⟨fun b => decide (b = a), fun b => by simp⟩

/-- A probe is determined by the point it selects. -/
public theorem IsProbe.eq_of_isProbe {A : Type v'} {f g : A → Bool} {a : A}
    (hf : IsProbe f a) (hg : IsProbe g a) : f = g := by
  funext b
  cases hb : f b
  · have : ¬ (b = a) := fun hc => by simp [hf b |>.mpr hc] at hb
    cases hgb : g b
    · rfl
    · exact absurd (hg b |>.mp hgb) this
  · rw [hg b |>.mpr (hf b |>.mp hb)]

/-- On every type Definition 2 admits (`∃ b ≠ a`), `IsProbe` is surjective onto
`Bool` — so it *is* the paper's probe there. -/
public theorem surjective_of_isProbe {A : Type v'} {f : A → Bool} {a : A}
    (hf : IsProbe f a) (h : ∃ b : A, b ≠ a) : Function.Surjective f := by
  intro y
  cases y
  · obtain ⟨b, hb⟩ := h
    refine ⟨b, ?_⟩
    cases hb' : f b
    · rfl
    · exact absurd (hf b |>.mp hb') hb
  · exact ⟨a, hf a |>.mpr rfl⟩

/-- **Definition 2 as printed:** unique-true *and* onto `Bool` *and* a second
point. Equivalent to `IsProbe` on every type the source considers. -/
@[expose] public def IsSourceProbe {A : Type v'} (f : A → Bool) (a : A) : Prop :=
  IsProbe f a ∧ Function.Surjective f ∧ ∃ b : A, b ≠ a

public theorem isSourceProbe_iff {A : Type v'} {f : A → Bool} {a : A} :
    IsSourceProbe f a ↔ IsProbe f a ∧ ∃ b : A, b ≠ a :=
  ⟨fun h => ⟨h.1, h.2.2⟩,
   fun h => ⟨h.1, surjective_of_isProbe h.1 h.2, h.2⟩⟩

/-! ## Weak inference -/

/--
**Definition 3.** The device *weakly infers* a function `Γ`: for every probe of a
realized value of `Γ`, the device can be set up so that its conclusion answers
that probe throughout the resulting fibre.

The quantifier order is the content. It is *not* one rule that works everywhere;
it is one setup value per question, and the answer is only required on the fibre
that setup value induces. The source writes this `C > Γ`.
-/
@[expose] public def WeaklyInfers (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) : Prop :=
  ∀ (γ : G) (f : G → Bool), IsProbe f γ → (∃ w : U, Γ w = γ) →
    ∃ x : C.Setup, C.Realized x ∧ ∀ w : U, C.setup w = x → C.concl w = f (Γ w)

/-- One device weakly infers another when it weakly infers its conclusion function. -/
@[expose] public def InfersDevice (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) : Prop :=
  WeaklyInfers C₁ C₂.concl

/-- Probe of the *image* of `Γ` — the paper's `π(Γ)`. -/
@[expose] public def IsProbeOnImage {G : Type v'} (Γ : U → G) (f : G → Bool)
    (γ : G) : Prop :=
  ∀ w : U, f (Γ w) = true ↔ Γ w = γ

/-- Ambient `IsProbe` and image probes give the same weak-inference statement. -/
public theorem weaklyInfers_iff_imageProbes (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) :
    WeaklyInfers C Γ ↔
      ∀ (γ : G) (f : G → Bool), IsProbeOnImage Γ f γ → (∃ w : U, Γ w = γ) →
        ∃ x : C.Setup, C.Realized x ∧
          ∀ w : U, C.setup w = x → C.concl w = f (Γ w) := by
  constructor
  · intro h γ f hf hγ
    obtain ⟨f', hf'⟩ := exists_isProbe γ
    obtain ⟨x, hx, hfib⟩ := h γ f' hf' hγ
    refine ⟨x, hx, fun w hw => ?_⟩
    have : f (Γ w) = f' (Γ w) := by
      cases hfw : f (Γ w)
      · have : Γ w ≠ γ := fun hc => by
          have := (hf w).mpr hc
          simp [hfw] at this
        cases hf'w : f' (Γ w)
        · rfl
        · exact absurd (hf' (Γ w) |>.mp hf'w) this
      · have : Γ w = γ := (hf w).mp (by simp [hfw])
        rw [this, hf' γ |>.mpr rfl]
    rw [this]
    exact hfib w hw
  · intro h γ f hf hγ
    refine h γ f ?_ hγ
    intro w
    exact hf (Γ w)

/-- On a target range with two distinct values — which is all the source
considers — every point has a second point beside it. -/
public theorem exists_ne_of_two_values {G : Type v'} (hG : ∃ a b : G, a ≠ b)
    (γ : G) : ∃ b : G, b ≠ γ := by
  obtain ⟨a, b, hab⟩ := hG
  by_cases ha : a = γ
  · exact ⟨b, fun hc => hab (ha.trans hc.symm)⟩
  · exact ⟨a, ha⟩

/--
**Definition 3 over the printed probes.** On any target range with at least two
values — the source's standing stipulation — quantifying over `IsProbe` and over
`IsSourceProbe` give the same weak-inference statement.

This is what licenses the working predicate: `IsProbe` and Definition 2 differ
only on a singleton range, which the source excludes. The consumers below
quantify over `IsProbe`; this theorem is the bridge to the printed definition.
-/
public theorem weaklyInfers_iff_sourceProbes (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (hG : ∃ a b : G, a ≠ b) :
    WeaklyInfers C Γ ↔
      ∀ (γ : G) (f : G → Bool), IsSourceProbe f γ → (∃ w : U, Γ w = γ) →
        ∃ x : C.Setup, C.Realized x ∧
          ∀ w : U, C.setup w = x → C.concl w = f (Γ w) := by
  constructor
  · intro h γ f hf hγ
    exact h γ f hf.1 hγ
  · intro h γ f hf hγ
    exact h γ f (isSourceProbe_iff.mpr ⟨hf, exists_ne_of_two_values hG γ⟩) hγ

/-! ## Distinguishability -/

/--
**Definition 4.** Two devices are *setup distinguishable* when every pair of
realized setup values is jointly realizable.

No device is distinguishable from itself once its setup takes two values, which is
why the source's Theorem 1 is not a statement about a device and its own copy.
-/
@[expose] public def Distinguishable (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) : Prop :=
  ∀ x₁ : C₁.Setup, C₁.Realized x₁ → ∀ x₂ : C₂.Setup, C₂.Realized x₂ →
    ∃ w : U, C₁.setup w = x₁ ∧ C₂.setup w = x₂

public theorem Distinguishable.symm
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (h : Distinguishable C₁ C₂) : Distinguishable C₂ C₁ :=
  fun x₂ hx₂ x₁ hx₁ => (h x₁ hx₁ x₂ hx₂).imp (fun _ hw => ⟨hw.2, hw.1⟩)

/-! ## Every device fails some question -/

/--
**Proposition 1(ii).** For any device there is a binary-valued function it does
not weakly infer.

The witness is the device's own conclusion function: answering the negation probe
about itself would require its conclusion to differ from itself on a nonempty
fibre. Applied to prediction, this is the source's sense in which Laplace was
wrong — even a clockwork universe contains a question its predictor cannot answer.
-/
@[grind] public theorem not_weaklyInfers_own_concl (C : InferenceDevice.{u, v} U) :
    ¬ WeaklyInfers C C.concl := by
  intro h
  obtain ⟨w₀, hw₀⟩ := C.concl_surjective false
  obtain ⟨x, ⟨w₁, hw₁⟩, hfib⟩ := h false (fun b => !b) isProbe_not ⟨w₀, hw₀⟩
  have := hfib w₁ hw₁
  exact (Bool.not_ne_self (C.concl w₁)) this.symm

/-- **Proposition 1(ii)**, in existential form. -/
public theorem exists_not_weaklyInfers (C : InferenceDevice.{u, v} U) :
    ∃ Γ : U → Bool, ¬ WeaklyInfers C Γ :=
  ⟨C.concl, not_weaklyInfers_own_concl C⟩

/-! ## Some device does infer -/

/--
**Proposition 1(i).** If a target takes at least two values on some subset `W`
which is neither empty nor everything, then a device weakly inferring it exists.

The source's construction, unchanged: the conclusion function is `false` exactly
on `W`, and the setup function separates the points of `W`. Given a probe at `γ`,
the device is set up to isolate a point of `W` where the target is *not* `γ` —
such a point exists precisely because the target takes two values on `W` — and
there both the conclusion and the probe read `false`.

Without this, the module would prove only that inference fails, never that it can
succeed.
-/
@[expose] public def separatingDevice (inW : U → Bool)
    (hin : ∃ w : U, inW w = true) (hout : ∃ w : U, inW w = false) :
    InferenceDevice.{u, u} U where
  Setup := Option U
  setup := fun w => if inW w then some w else none
  concl := fun w => !(inW w)
  concl_surjective := by
    intro b
    cases b
    · obtain ⟨w, hw⟩ := hin; exact ⟨w, by simp [hw]⟩
    · obtain ⟨w, hw⟩ := hout; exact ⟨w, by simp [hw]⟩

/--
The construction infers **any** target taking two values on `W`. The device does
not mention the target, which is what makes the source's family statement — one
device inferring every member of `{Γᵢ}` at once — immediate rather than a separate
argument.
-/
public theorem separatingDevice_weaklyInfers (inW : U → Bool)
    (hin : ∃ w : U, inW w = true) (hout : ∃ w : U, inW w = false)
    {G : Type v'} (Γ : U → G)
    (htwo : ∃ w₁ w₂ : U, inW w₁ = true ∧ inW w₂ = true ∧ Γ w₁ ≠ Γ w₂) :
    WeaklyInfers (separatingDevice inW hin hout) Γ := by
  obtain ⟨w₁, w₂, hw₁, hw₂, hne⟩ := htwo
  intro γ f hf _
  -- a point of `W` whose target value is not `γ`
  have hpick : ∃ w : U, inW w = true ∧ Γ w ≠ γ := by
    by_cases h : Γ w₁ = γ
    · exact ⟨w₂, hw₂, fun hc => hne (h.trans hc.symm)⟩
    · exact ⟨w₁, hw₁, h⟩
  obtain ⟨w, hwW, hwγ⟩ := hpick
  refine ⟨some w, ⟨w, by simp [separatingDevice, hwW]⟩, fun v hv => ?_⟩
  -- the fibre of `some w` is exactly `{w}`
  have hv' : (if inW v = true then some v else none) = some w := hv
  by_cases hb : inW v = true
  · rw [if_pos hb] at hv'
    cases hv'
    show (!(inW w)) = f (Γ w)
    simp only [hwW, Bool.not_true]
    exact (Bool.eq_false_iff.mpr (fun hc => hwγ (hf (Γ w) |>.mp hc))).symm
  · rw [if_neg hb] at hv'
    exact absurd hv' (by simp)

/--
**Proposition 1(i), family form.** One device weakly infers *every* member of a
family of targets, provided each takes two values on the same `W`.
-/
public theorem exists_weaklyInfers_family_of_two_values_on
    {ι : Type v''} {G : Type v'} (Γ : ι → U → G) (inW : U → Bool)
    (hin : ∃ w : U, inW w = true) (hout : ∃ w : U, inW w = false)
    (htwo : ∀ i : ι, ∃ w₁ w₂ : U, inW w₁ = true ∧ inW w₂ = true ∧ Γ i w₁ ≠ Γ i w₂) :
    ∃ C : InferenceDevice.{u, u} U, ∀ i : ι, WeaklyInfers C (Γ i) :=
  ⟨separatingDevice inW hin hout,
    fun i => separatingDevice_weaklyInfers inW hin hout (Γ i) (htwo i)⟩

/--
**Corollary 1(i).** If every member of the family takes all its values already on
`W`, one device infers the whole family.

The source derives this from Proposition 1(i) using its global stipulation that
every function over `U` takes at least two values; that stipulation is not imposed
in this development, so it appears here as the explicit hypothesis `htwoU`.
-/
public theorem exists_weaklyInfers_family_of_values_attained_on
    {ι : Type v''} {G : Type v'} (Γ : ι → U → G) (inW : U → Bool)
    (hin : ∃ w : U, inW w = true) (hout : ∃ w : U, inW w = false)
    (hattained : ∀ (i : ι) (u : U), ∃ w : U, inW w = true ∧ Γ i w = Γ i u)
    (htwoU : ∀ i : ι, ∃ u v : U, Γ i u ≠ Γ i v) :
    ∃ C : InferenceDevice.{u, u} U, ∀ i : ι, WeaklyInfers C (Γ i) := by
  refine exists_weaklyInfers_family_of_two_values_on Γ inW hin hout (fun i => ?_)
  obtain ⟨u, v, huv⟩ := htwoU i
  obtain ⟨w₁, hw₁, hval₁⟩ := hattained i u
  obtain ⟨w₂, hw₂, hval₂⟩ := hattained i v
  exact ⟨w₁, w₂, hw₁, hw₂, by rw [hval₁, hval₂]; exact huv⟩

/-- **Proposition 1(i)**, single-target form. -/
public theorem exists_weaklyInfers_of_two_values_on
    {G : Type v'} (Γ : U → G) (inW : U → Bool)
    (hout : ∃ w : U, inW w = false)
    (htwo : ∃ w₁ w₂ : U, inW w₁ = true ∧ inW w₂ = true ∧ Γ w₁ ≠ Γ w₂) :
    ∃ C : InferenceDevice.{u, u} U, WeaklyInfers C Γ := by
  obtain ⟨w₁, _, hw₁, _, _⟩ := id htwo
  exact ⟨separatingDevice inW ⟨w₁, hw₁⟩ hout,
    separatingDevice_weaklyInfers inW ⟨w₁, hw₁⟩ hout Γ htwo⟩

/-! ## Theorem 1 — mutual weak inference is impossible between distinguishable devices -/

/--
**Theorem 1.** No two distinguishable devices can weakly infer each other.

The source's proof, unchanged: the identity probe forces the first device's
conclusion to agree with the second's on some fibre, the negation probe forces the
second's to disagree with the first's on some fibre, and distinguishability
supplies a universe in both fibres at once.
-/
public theorem not_infersDevice_both_of_distinguishable
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hdist : Distinguishable C₁ C₂)
    (h₁₂ : InfersDevice C₁ C₂) (h₂₁ : InfersDevice C₂ C₁) : False := by
  obtain ⟨wt, hwt⟩ := C₂.concl_surjective true
  obtain ⟨x₁, hx₁, hfib₁⟩ := h₁₂ true id isProbe_id ⟨wt, hwt⟩
  obtain ⟨wf, hwf⟩ := C₁.concl_surjective false
  obtain ⟨x₂, hx₂, hfib₂⟩ := h₂₁ false (fun b => !b) isProbe_not ⟨wf, hwf⟩
  obtain ⟨w, hw₁, hw₂⟩ := hdist x₁ hx₁ x₂ hx₂
  have e₁ : C₁.concl w = C₂.concl w := hfib₁ w hw₁
  have e₂ : C₂.concl w = !(C₁.concl w) := hfib₂ w hw₂
  exact (Bool.self_ne_not (C₁.concl w)) (e₁.trans e₂)

/-! ## Strong inference -/

/--
**Definition 5.** The device *strongly infers* another when, for every probe of the
other's conclusion and every realized setup value of the other, it can be set up so
as to force that setup value **and** answer the probe.

This is the source's analogue of a universal Turing machine: the first device can
put the second into any configuration it likes and still report on it correctly.
The source writes this `C₁ ≫ C₂`.
-/
@[expose] public def StronglyInfers (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) : Prop :=
  ∀ (γ : Bool) (f : Bool → Bool), IsProbe f γ → (∃ w : U, C₂.concl w = γ) →
    ∀ x₂ : C₂.Setup, C₂.Realized x₂ →
      ∃ x₁ : C₁.Setup, C₁.Realized x₁ ∧
        ∀ w : U, C₁.setup w = x₁ → C₂.setup w = x₂ ∧ C₁.concl w = f (C₂.concl w)

/--
**Theorem 3.** No two devices can strongly infer each other.

Unlike Theorem 1 this needs no distinguishability hypothesis. Starting from any
realized setup value of the first device, the second's strong inference produces a
sub-fibre on which the conclusions disagree, and the first's strong inference then
produces a sub-fibre of *that* on which they agree.
-/
public theorem not_stronglyInfers_both
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (h₁₂ : StronglyInfers C₁ C₂) (h₂₁ : StronglyInfers C₂ C₁) : False := by
  obtain ⟨w₀, _⟩ := C₁.concl_surjective true
  obtain ⟨wf, hwf⟩ := C₁.concl_surjective false
  obtain ⟨x₂, hx₂, hfib₂⟩ :=
    h₂₁ false (fun b => !b) isProbe_not ⟨wf, hwf⟩ (C₁.setup w₀) ⟨w₀, rfl⟩
  obtain ⟨wt, hwt⟩ := C₂.concl_surjective true
  obtain ⟨x₁, ⟨w, hw⟩, hfib₁⟩ := h₁₂ true id isProbe_id ⟨wt, hwt⟩ x₂ hx₂
  obtain ⟨hset₂, hconcl₁⟩ := hfib₁ w hw
  obtain ⟨_, hconcl₂⟩ := hfib₂ w hset₂
  rw [hconcl₁] at hconcl₂
  exact (Bool.not_ne_self (C₂.concl w)) hconcl₂.symm

/-! ## Theorem 2 — strong inference dominates weak inference -/

/--
**Theorem 2(i).** Strong inference inherits weak inference: if the first device
strongly infers the second, then everything the second weakly infers, the first
weakly infers too.
-/
@[grind →] public theorem weaklyInfers_of_stronglyInfers
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    {G : Type v''} {Γ : U → G}
    (hs : StronglyInfers C₁ C₂) (hw : WeaklyInfers C₂ Γ) :
    WeaklyInfers C₁ Γ := by
  intro γ f hf hγ
  obtain ⟨x₂, hx₂, hfib₂⟩ := hw γ f hf hγ
  obtain ⟨wt, hwt⟩ := C₂.concl_surjective true
  obtain ⟨x₁, hx₁, hfib₁⟩ := hs true id isProbe_id ⟨wt, hwt⟩ x₂ hx₂
  refine ⟨x₁, hx₁, fun w hw₁ => ?_⟩
  obtain ⟨hset₂, hconcl₁⟩ := hfib₁ w hw₁
  rw [hconcl₁]
  exact hfib₂ w hset₂

/--
**Theorem 2(ii).** Strong inference is transitive.
-/
public theorem stronglyInfers_trans
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    {C₃ : InferenceDevice.{u, v''} U}
    (h₁₂ : StronglyInfers C₁ C₂) (h₂₃ : StronglyInfers C₂ C₃) :
    StronglyInfers C₁ C₃ := by
  intro γ f hf hγ x₃ hx₃
  obtain ⟨x₂, hx₂, hfib₂⟩ := h₂₃ γ f hf hγ x₃ hx₃
  obtain ⟨wt, hwt⟩ := C₂.concl_surjective true
  obtain ⟨x₁, hx₁, hfib₁⟩ := h₁₂ true id isProbe_id ⟨wt, hwt⟩ x₂ hx₂
  refine ⟨x₁, hx₁, fun w hw₁ => ?_⟩
  obtain ⟨hset₂, hconcl₁⟩ := hfib₁ w hw₁
  obtain ⟨hset₃, hconcl₂⟩ := hfib₂ w hset₂
  exact ⟨hset₃, hconcl₁.trans hconcl₂⟩

/-!
**Immediate consequence following Theorem 2.** Strong inference implies weak
inference of the target device's conclusion function. The source states this
immediately after Theorem 2(i) and (ii), without numbering it as a third part.
-/
@[grind →] public theorem infersDevice_of_stronglyInfers
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) : InfersDevice C₁ C₂ := by
  intro γ f hf hγ
  obtain ⟨w₂, hw₂⟩ := hγ
  obtain ⟨x₂, hx₂, hfib⟩ := hs γ f hf ⟨w₂, hw₂⟩
    (C₂.setup w₂) ⟨w₂, rfl⟩
  exact ⟨x₂, hx₂, fun w hw => (hfib w hw).2⟩

/--
**Corollary.** No device strongly infers itself — the special case of Theorem 3
with both devices equal, and the source's analogue of the halting theorem.
-/
@[grind] public theorem not_stronglyInfers_self (C : InferenceDevice.{u, v} U) :
    ¬ StronglyInfers C C :=
  fun h => not_stronglyInfers_both h h

/--
**Proposition 2(i).** For any device there is a device it does not strongly infer.

The source presents this as the inference analogue of the halting theorem: no
device is universal. The witness is the device itself, by the corollary above —
the statement is exactly as strong as it looks, and no construction is needed.
-/
public theorem exists_not_stronglyInfers (C : InferenceDevice.{u, v} U) :
    ∃ C' : InferenceDevice.{u, v} U, ¬ StronglyInfers C C' :=
  ⟨C, not_stronglyInfers_self C⟩

/-! ## Control (section 7) -/

/--
**Definition 8, first half.** The device *semi-controls* a function when it can be
set up so as to force any realized value of that function.

Semi-control says nothing about the conclusion function: it is entirely a
statement about which fibres of the setup sit inside which fibres of the target.
-/
@[expose] public def SemiControls (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) : Prop :=
  ∀ γ : G, (∃ w : U, Γ w = γ) →
    ∃ x : C.Setup, C.Realized x ∧ ∀ w : U, C.setup w = x → Γ w = γ

/--
**Definition 8, second half.** The device *controls* a function when, for every
probe and every truth value, it can be set up so that its conclusion **and** the
probe both take that value.

Control is strictly more than inference: inference requires the conclusion to
track the answer, control requires the device to be able to *set* the answer.
-/
@[expose] public def Controls (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) : Prop :=
  ∀ (γ : G) (f : G → Bool), IsProbe f γ → (∃ w : U, Γ w = γ) → ∀ b : Bool,
    ∃ x : C.Setup, C.Realized x ∧
      ∀ w : U, C.setup w = x → C.concl w = b ∧ f (Γ w) = b

/-!
**Section 7 consequence.** Strong inference semi-controls the target device's
setup function. The conclusion component of strong inference is not enough to
semi-control the target conclusion function; the source explicitly distinguishes
these two claims.
-/
public theorem semiControls_setup_of_stronglyInfers
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) : SemiControls C₁ C₂.setup := by
  intro x₂ hx₂
  obtain ⟨wₜ, hwt⟩ := C₂.concl_surjective true
  obtain ⟨x₁, hx₁, hfib⟩ := hs true id isProbe_id ⟨wₜ, hwt⟩ x₂ hx₂
  exact ⟨x₁, hx₁, fun w hw => (hfib w hw).1⟩

/-- **Control implies weak inference**, which is what carries every impossibility
result above over to control. -/
public theorem weaklyInfers_of_controls {C : InferenceDevice.{u, v} U}
    {G : Type v'} {Γ : U → G} (h : Controls C Γ) :
    WeaklyInfers C Γ := by
  intro γ f hf hγ
  obtain ⟨x, hx, hfib⟩ := h γ f hf hγ true
  refine ⟨x, hx, fun w hw => ?_⟩
  obtain ⟨hc, hp⟩ := hfib w hw
  rw [hc, hp]

/--
**Control implies semi-control** (the source states this in passing). Needs a probe
at the controlled value to exist, which is why this one lemma asks for decidable
equality on the target range where nothing else in the module does.
-/
public theorem semiControls_of_controls {C : InferenceDevice.{u, v} U}
    {G : Type v'} [DecidableEq G] {Γ : U → G} (h : Controls C Γ) :
    SemiControls C Γ := by
  intro γ hγ
  obtain ⟨x, hx, hfib⟩ := h γ (probe γ) (isProbe_probe γ) hγ true
  refine ⟨x, hx, fun w hw => ?_⟩
  obtain ⟨_, hp⟩ := hfib w hw
  exact (isProbe_probe γ (Γ w)).mp hp

/-!
**Section 7 consequence, unrestricted range.** The source's statement that
control implies semi-control does not require decidable equality on the target
range. This classical form uses the generic probe-existence theorem; the theorem
above remains the constructive specialization for decidable ranges.
-/
public theorem semiControls_of_controls_classical {C : InferenceDevice.{u, v} U}
    {G : Type v'} {Γ : U → G} (h : Controls C Γ) :
    SemiControls C Γ := by
  classical
  intro γ hγ
  obtain ⟨f, hf⟩ := exists_isProbe γ
  obtain ⟨x, hx, hfib⟩ := h γ f hf hγ true
  refine ⟨x, hx, fun w hw => ?_⟩
  exact (hf (Γ w)).mp (hfib w hw).2

/-- **No device controls its own conclusion function** — Proposition 1(ii)
transported along control. -/
public theorem not_controls_own_concl (C : InferenceDevice.{u, v} U) :
    ¬ Controls C C.concl :=
  fun h => not_weaklyInfers_own_concl C (weaklyInfers_of_controls h)

/-- **No two distinguishable devices control each other's conclusion functions** —
Theorem 1 transported along control. -/
public theorem not_controls_both_of_distinguishable
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hdist : Distinguishable C₁ C₂)
    (h₁₂ : Controls C₁ C₂.concl) (h₂₁ : Controls C₂ C₁.concl) : False :=
  not_infersDevice_both_of_distinguishable hdist
    (weaklyInfers_of_controls h₁₂) (weaklyInfers_of_controls h₂₁)

/-- One direction of Theorem 5: mutual semi-control of setups makes each device's
setup fibres refine the other's, hence agree. -/
public theorem setup_eq_of_semiControls_setup
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (h₁₂ : SemiControls C₁ C₂.setup) (h₂₁ : SemiControls C₂ C₁.setup)
    {w w' : U} (h : C₁.setup w = C₁.setup w') : C₂.setup w = C₂.setup w' := by
  obtain ⟨x₂, ⟨v₂, hv₂⟩, hsub₂⟩ := h₂₁ (C₁.setup w) ⟨w, rfl⟩
  obtain ⟨x₁, ⟨v₁, hv₁⟩, hsub₁⟩ := h₁₂ x₂ ⟨v₂, hv₂⟩
  have hx₁ : x₁ = C₁.setup w := by
    have hin : C₂.setup v₁ = x₂ := hsub₁ v₁ hv₁
    have := hsub₂ v₁ hin
    rw [← hv₁]
    exact this
  have hw : C₂.setup w = x₂ := hsub₁ w (by rw [hx₁])
  have hw' : C₂.setup w' = x₂ := hsub₁ w' (by rw [hx₁]; exact h.symm)
  rw [hw, hw']

/--
**Theorem 5.** If two devices simultaneously semi-control one another's setup
functions, the partitions their setups induce are identical.

The source reads this as: those setup functions are the same function up to a
relabelling of their ranges. It is the statement behind Corollary 3 — mutual
semi-control makes the two devices indistinguishable in exactly the sense
Theorem 1 needs, which is why mutual *inference* becomes possible for them where
Theorem 1 forbids it for distinguishable devices.
-/
public theorem setup_partition_eq_of_semiControls_setup
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (h₁₂ : SemiControls C₁ C₂.setup) (h₂₁ : SemiControls C₂ C₁.setup)
    (w w' : U) : C₁.setup w = C₁.setup w' ↔ C₂.setup w = C₂.setup w' :=
  ⟨setup_eq_of_semiControls_setup h₁₂ h₂₁, setup_eq_of_semiControls_setup h₂₁ h₁₂⟩

/-! ## Corollary 3 — consequences of mutual semi-control of setups -/

/-- On `Bool`, the only probes are the source's identity and negation. -/
public theorem isProbe_bool {f : Bool → Bool} {γ : Bool} (hf : IsProbe f γ) :
    (γ = true ∧ f = id) ∨ (γ = false ∧ f = fun b => !b) := by
  cases γ
  · exact Or.inr ⟨rfl, IsProbe.eq_of_isProbe hf isProbe_not⟩
  · exact Or.inl ⟨rfl, IsProbe.eq_of_isProbe hf isProbe_id⟩

/--
**Corollary 3(i).** If two devices simultaneously semi-control one another's
setup functions, then one weakly infers the other if and only if the reverse
holds.

The source's proof: Theorem 5 lets the setup images be relabelled to a common
`X`, after which the identity and negation fibres that witness `C₁ > Y₂` are
exactly the fibres that witness `C₂ > Y₁`.
-/
public theorem infersDevice_comm_of_semiControls_setup
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (h₁₂ : SemiControls C₁ C₂.setup) (h₂₁ : SemiControls C₂ C₁.setup) :
    InfersDevice C₁ C₂ ↔ InfersDevice C₂ C₁ := by
  have hpart := setup_partition_eq_of_semiControls_setup h₁₂ h₂₁
  constructor
  · intro hInf γ f hf _
    rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨wt, hwt⟩ := C₂.concl_surjective true
      obtain ⟨x₁, ⟨w₀, hw₀⟩, hfib⟩ := hInf true id isProbe_id ⟨wt, hwt⟩
      refine ⟨C₂.setup w₀, ⟨w₀, rfl⟩, fun w hw => ?_⟩
      have hx : C₁.setup w = x₁ := ((hpart w w₀).mpr hw).trans hw₀
      exact (hfib w hx).symm
    · obtain ⟨wf, hwf⟩ := C₂.concl_surjective false
      obtain ⟨x₁, ⟨w₀, hw₀⟩, hfib⟩ := hInf false (fun b => !b) isProbe_not ⟨wf, hwf⟩
      refine ⟨C₂.setup w₀, ⟨w₀, rfl⟩, fun w hw => ?_⟩
      have hx : C₁.setup w = x₁ := ((hpart w w₀).mpr hw).trans hw₀
      have hneg : C₁.concl w = !(C₂.concl w) := hfib w hx
      cases h₂ : C₂.concl w
      · simp [hneg, h₂]
      · simp [hneg, h₂]
  · intro hInf γ f hf _
    rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · obtain ⟨wt, hwt⟩ := C₁.concl_surjective true
      obtain ⟨x₂, ⟨w₀, hw₀⟩, hfib⟩ := hInf true id isProbe_id ⟨wt, hwt⟩
      refine ⟨C₁.setup w₀, ⟨w₀, rfl⟩, fun w hw => ?_⟩
      have hx : C₂.setup w = x₂ := ((hpart w w₀).mp hw).trans hw₀
      exact (hfib w hx).symm
    · obtain ⟨wf, hwf⟩ := C₁.concl_surjective false
      obtain ⟨x₂, ⟨w₀, hw₀⟩, hfib⟩ := hInf false (fun b => !b) isProbe_not ⟨wf, hwf⟩
      refine ⟨C₁.setup w₀, ⟨w₀, rfl⟩, fun w hw => ?_⟩
      have hx : C₂.setup w = x₂ := ((hpart w w₀).mp hw).trans hw₀
      have hneg : C₂.concl w = !(C₁.concl w) := hfib w hx
      cases h₁ : C₁.concl w
      · simp [hneg, h₁]
      · simp [hneg, h₁]

/--
**Corollary 3(iii).** Under the same mutual semi-control of setups, neither
device controls the other's setup function.

The source's proof: after the Theorem 5 relabelling the shared setup `X` is
what would be controlled; forcing `Y = δ_{X,x} = 1` on every fibre makes the
conclusion constantly `true`, against Definition 1.
-/
public theorem not_controls_other_setup_of_semiControls_setup
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (h₁₂ : SemiControls C₁ C₂.setup) (h₂₁ : SemiControls C₂ C₁.setup) :
    ¬ Controls C₁ C₂.setup := by
  intro hC
  have hpart := setup_partition_eq_of_semiControls_setup h₁₂ h₂₁
  have hconst : ∀ w : U, C₁.concl w = true := by
    intro w
    obtain ⟨f, hf⟩ := exists_isProbe (C₂.setup w)
    obtain ⟨x₁, ⟨w₀, hw₀⟩, hfib⟩ :=
      hC (C₂.setup w) f hf ⟨w, rfl⟩ true
    have hw0γ : C₂.setup w₀ = C₂.setup w :=
      (hf (C₂.setup w₀)).mp (hfib w₀ hw₀).2
    have hx : C₁.setup w = x₁ := ((hpart w w₀).mpr hw0γ.symm).trans hw₀
    exact (hfib w hx).1
  obtain ⟨w, hw⟩ := C₁.concl_surjective false
  exact Bool.false_ne_true (hw.symm.trans (hconst w))

/--
**Corollary 3(ii).** Under mutual semi-control of setups, **neither** device
strongly infers the other. This is `¬A ∧ ¬B`, not Theorem 3's `¬(A ∧ B)`.
The paper's appendix assumes only one `≫` and uses the shared partition.
-/
public theorem not_stronglyInfers_of_semiControls_setup
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (h₁₂ : SemiControls C₁ C₂.setup) (h₂₁ : SemiControls C₂ C₁.setup) :
    ¬ StronglyInfers C₁ C₂ := by
  intro hs
  have hpart := setup_partition_eq_of_semiControls_setup h₁₂ h₂₁
  obtain ⟨wt, hwt⟩ := C₂.concl_surjective true
  obtain ⟨wf, hwf⟩ := C₂.concl_surjective false
  obtain ⟨xa, ⟨wa, hwa⟩, hfa⟩ :=
    hs true id isProbe_id ⟨wt, hwt⟩ (C₂.setup wt) ⟨wt, rfl⟩
  obtain ⟨xb, ⟨wb, hwb⟩, hfb⟩ :=
    hs false (fun b => !b) isProbe_not ⟨wf, hwf⟩ (C₂.setup wt) ⟨wt, rfl⟩
  have ha2 : C₂.setup wa = C₂.setup wt := (hfa wa hwa).1
  have hb2 : C₂.setup wb = C₂.setup wt := (hfb wb hwb).1
  have hab : C₁.setup wa = C₁.setup wb := (hpart wa wb).mpr (ha2.trans hb2.symm)
  have hxab : xb = xa := by rw [← hwa, ← hwb, hab]
  have e₁ : C₁.concl wa = C₂.concl wa := (hfa wa hwa).2
  have e₂ : C₁.concl wa = !(C₂.concl wa) :=
    (hfb wa (by rw [hwa, hxab])).2
  rw [e₁] at e₂
  exact (Bool.not_ne_self (C₂.concl wa)) e₂.symm

public theorem not_stronglyInfers_either_of_semiControls_setup
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (h₁₂ : SemiControls C₁ C₂.setup) (h₂₁ : SemiControls C₂ C₁.setup) :
    ¬ StronglyInfers C₁ C₂ ∧ ¬ StronglyInfers C₂ C₁ :=
  ⟨not_stronglyInfers_of_semiControls_setup h₁₂ h₂₁,
    not_stronglyInfers_of_semiControls_setup h₂₁ h₁₂⟩

/-- No device controls its own setup (the engine of Cor 3(iii); needs no
semi-control). -/
public theorem not_controls_own_setup (C : InferenceDevice.{u, v} U) :
    ¬ Controls C C.setup := by
  intro hC
  have hconst : ∀ w : U, C.concl w = true := by
    intro w
    obtain ⟨f, hf⟩ := exists_isProbe (C.setup w)
    obtain ⟨x, ⟨w₀, hw₀⟩, hfib⟩ := hC (C.setup w) f hf ⟨w, rfl⟩ true
    have : C.setup w₀ = C.setup w := (hf (C.setup w₀)).mp (hfib w₀ hw₀).2
    have hx : x = C.setup w := by rw [← hw₀, this]
    exact (hfib w (by rw [hx])).1
  obtain ⟨w, hw⟩ := C.concl_surjective false
  exact Bool.false_ne_true (hw.symm.trans (hconst w))

/-- The paper's first iff for semi-control: force `Γ=γ` iff force `f(Γ)=true`. -/
public theorem semiControls_iff_probe {C : InferenceDevice.{u, v} U}
    {G : Type v'} (Γ : U → G) :
    SemiControls C Γ ↔
      ∀ (γ : G) (f : G → Bool), IsProbe f γ → (∃ w : U, Γ w = γ) →
        ∃ x : C.Setup, C.Realized x ∧
          ∀ w : U, C.setup w = x → f (Γ w) = true := by
  constructor
  · intro h γ f hf hγ
    obtain ⟨x, hx, hsub⟩ := h γ hγ
    exact ⟨x, hx, fun w hw => (hf (Γ w)).mpr (hsub w hw)⟩
  · intro h γ hγ
    obtain ⟨f, hf⟩ := exists_isProbe γ
    obtain ⟨x, hx, hsub⟩ := h γ f hf hγ
    exact ⟨x, hx, fun w hw => (hf (Γ w)).mp (hsub w hw)⟩

/-! ## Corollary 2 — cardinality of setup vs inferrability

The source: if `X` fine-grains `Y`, then `|X(U)| > 2` iff some function is
inferred. Forward: two setup blocks inside one `Y`-block give identity and
negation fibres. Reverse: `|X(U)| ≤ 2` and fine-graining force `X ≅ Y`, and
that pair answers no two-valued target.
-/

/-- Setup partition refines the conclusion partition: `X` fine-grains `Y`. -/
@[expose] public def SetupRefinesConcl (C : InferenceDevice.{u, v} U) : Prop :=
  ∀ w w' : U, C.setup w = C.setup w' → C.concl w = C.concl w'

/-- At least three distinct realized setup values — the source's `|X(U)| > 2`. -/
@[expose] public def ThreeSetupValues (C : InferenceDevice.{u, v} U) : Prop :=
  ∃ x₁ x₂ x₃ : C.Setup,
    C.Realized x₁ ∧ C.Realized x₂ ∧ C.Realized x₃ ∧
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃

/-- Three bits, two values: at least two agree. -/
public theorem two_of_three_same_bool (a b c : Bool) : a = b ∨ a = c ∨ b = c := by
  cases a <;> cases b <;> cases c <;> simp

/-- The paper's first Cor 2 step: two of three realized setups sit in one
`Y`-block. -/
public theorem two_setups_share_concl
    {C : InferenceDevice.{u, v} U} (h3 : ThreeSetupValues C) :
    ∃ (a a' : C.Setup) (w w' : U),
      C.setup w = a ∧ C.setup w' = a' ∧ a ≠ a' ∧ C.concl w = C.concl w' := by
  obtain ⟨xa, xb, xc, ⟨wa, hwa⟩, ⟨wb, hwb⟩, ⟨wc, hwc⟩, hab, hac, hbc⟩ := h3
  rcases two_of_three_same_bool (C.concl wa) (C.concl wb) (C.concl wc) with h | h | h
  · exact ⟨xa, xb, wa, wb, hwa, hwb, hab, h⟩
  · exact ⟨xa, xc, wa, wc, hwa, hwc, hac, h⟩
  · exact ⟨xb, xc, wb, wc, hwb, hwc, hbc, h⟩

/-- The paper's target for Cor 2, →: value `b` on setup-block `a` and on every
opposite-`Y` block; `¬b` on the other same-`Y` block. -/
public noncomputable def cor2Target (C : InferenceDevice.{u, v} U)
    (a : C.Setup) (b : Bool) : U → Bool := fun u =>
  have := Classical.propDecidable (C.setup u = a)
  have := Classical.propDecidable (C.concl u = b)
  if C.setup u = a ∨ C.concl u ≠ b then b else !b

/-- **Corollary 2, →.** If `X` fine-grains `Y` and `|X(U)| > 2`, some two-valued
`Γ` is inferred. -/
public theorem exists_weaklyInfers_of_three_setups
    {C : InferenceDevice.{u, v} U} (hfine : SetupRefinesConcl C)
    (h3 : ThreeSetupValues C) :
    ∃ Γ : U → Bool, (∃ u v : U, Γ u ≠ Γ v) ∧ WeaklyInfers C Γ := by
  classical
  obtain ⟨a, a', w₀, w₁, hw₀, hw₁, hneq, hyeq⟩ := two_setups_share_concl h3
  let b : Bool := C.concl w₀
  let Γ := cor2Target C a b
  refine ⟨Γ, ⟨w₀, w₁, ?_⟩, ?_⟩
  · -- `Γ` is `b` on block `a` and `¬b` on block `a'`
    have h0 : Γ w₀ = b := if_pos (Or.inl hw₀)
    have h1 : Γ w₁ = !b := by
      have hne : C.setup w₁ ≠ a := fun h => hneq (hw₁.symm.trans h).symm
      exact if_neg (not_or.mpr ⟨hne, not_not.mpr hyeq.symm⟩)
    rw [h0, h1]
    exact Bool.self_ne_not b
  · intro γ f hf _
    rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- identity: block `a` has `Y = b = Γ`
      refine ⟨a, ⟨w₀, hw₀⟩, fun u hu => ?_⟩
      have hy : C.concl u = b := hfine u w₀ (hu.trans hw₀.symm)
      have hΓ : Γ u = b := if_pos (Or.inl hu)
      cases hb : b <;> simp [hΓ, hy, hb]
    · -- negation: block `a'` has `Y = b` and `Γ = ¬b`
      refine ⟨a', ⟨w₁, hw₁⟩, fun u hu => ?_⟩
      have hy : C.concl u = b :=
        (hfine u w₁ (hu.trans hw₁.symm)).trans hyeq.symm
      have hne : C.setup u ≠ a := fun h => hneq (hu.symm.trans h).symm
      have hΓ : Γ u = !b := if_neg (not_or.mpr ⟨hne, not_not.mpr hy⟩)
      cases hb : b <;> simp [hΓ, hy, hb]

/-- Fine-graining plus two conclusion values forces exactly two realized
setups, one per conclusion bit — the paper's `|α|=|β|=2` hence `α=β`. -/
public theorem two_setups_of_refines_not_three
    {C : InferenceDevice.{u, v} U} (hfine : SetupRefinesConcl C)
    (h2 : ¬ ThreeSetupValues C) :
    ∃ xT xF : C.Setup,
      C.Realized xT ∧ C.Realized xF ∧ xT ≠ xF ∧
        (∀ w, C.setup w = xT → C.concl w = true) ∧
        (∀ w, C.setup w = xF → C.concl w = false) ∧
        (∀ w, C.setup w = xT ∨ C.setup w = xF) := by
  obtain ⟨wt, hwt⟩ := C.concl_surjective true
  obtain ⟨wf, hwf⟩ := C.concl_surjective false
  refine ⟨C.setup wt, C.setup wf, ⟨wt, rfl⟩, ⟨wf, rfl⟩, ?_, ?_, ?_, ?_⟩
  · intro h
    exact Bool.false_ne_true ((hwt.symm.trans (hfine wt wf h)).trans hwf).symm
  · intro w hw
    exact (hfine w wt hw).trans hwt
  · intro w hw
    exact (hfine w wf hw).trans hwf
  · intro w
    by_contra hw
    simp only [not_or] at hw
    refine h2 ⟨C.setup wt, C.setup wf, C.setup w, ⟨wt, rfl⟩, ⟨wf, rfl⟩, ⟨w, rfl⟩,
      ?_, Ne.symm hw.1, Ne.symm hw.2⟩
    intro h
    exact Bool.false_ne_true ((hwt.symm.trans (hfine wt wf h)).trans hwf).symm

/-- **Corollary 2, ←.** If `X` fine-grains `Y` and there are not three setup
values, `C` infers nothing with two values (the paper's `|X(U)|≤2` direction,
including the `|α|=2` case where `X` and `Y` induce the same partition). -/
public theorem not_weaklyInfers_of_at_most_two_setups
    {C : InferenceDevice.{u, v} U} (hfine : SetupRefinesConcl C)
    (h2 : ¬ ThreeSetupValues C)
    {G : Type v'} (Γ : U → G) (htwo : ∃ u v : U, Γ u ≠ Γ v) :
    ¬ WeaklyInfers C Γ := by
  classical
  intro hW
  obtain ⟨xT, xF, ⟨wt, hwt⟩, ⟨wf, hwf⟩, hxne, hT, hF, hcover⟩ :=
    two_setups_of_refines_not_three hfine h2
  obtain ⟨u0, v0, hΓne⟩ := htwo
  let γ : G := Γ wf
  obtain ⟨wγ', hγne⟩ : ∃ w' : U, Γ w' ≠ γ := by
    by_cases h : Γ u0 = γ
    · exact ⟨v0, fun hc => hΓne (h.trans hc.symm)⟩
    · exact ⟨u0, h⟩
  obtain ⟨fγ, hfγ⟩ := exists_isProbe γ
  obtain ⟨fγ', hfγ'⟩ := exists_isProbe (Γ wγ')
  obtain ⟨xγ, ⟨wans, hwans⟩, hans⟩ := hW γ fγ hfγ ⟨wf, rfl⟩
  have hxγT : xγ = xT := by
    rcases hcover wans with hTans | hFans
    · exact hwans.symm.trans hTans
    · have hansF : C.setup wf = xγ :=
        hwf.trans (hFans.symm.trans hwans)
      have hyγ : C.concl wf = true := by
        have := hans wf hansF
        simpa [γ, hfγ γ |>.mpr rfl] using this
      have : C.concl wf = false := hF wf hwf
      exact Bool.noConfusion (this.symm.trans hyγ)
  have hconst : ∀ w, C.setup w = xT → Γ w = γ := by
    intro w hw
    have hy : C.concl w = true := hT w hw
    have : C.concl w = fγ (Γ w) := hans w (hw.trans hxγT.symm)
    exact (hfγ (Γ w)).mp (this.symm.trans hy)
  have hw'F : C.setup wγ' = xF := by
    rcases hcover wγ' with hT' | hF'
    · exact absurd (hconst wγ' hT') hγne
    · exact hF'
  obtain ⟨x', ⟨w', hw'⟩, hans'⟩ := hW (Γ wγ') fγ' hfγ' ⟨wγ', rfl⟩
  rcases hcover w' with hTw' | hFw'
  · have hy : C.concl w' = true := hT w' hTw'
    have heq : C.concl w' = fγ' (Γ w') := hans' w' hw'
    have hΓT : Γ w' = γ := hconst w' hTw'
    have : fγ' (Γ w') = false := by
      have hne' : Γ w' ≠ Γ wγ' := fun h => hγne (h.symm.trans hΓT)
      exact Bool.eq_false_iff.mpr fun ht => hne' ((hfγ' (Γ w')).mp ht)
    exact Bool.noConfusion (hy.symm.trans (heq.trans this))
  · have hx'F : x' = xF := hw'.symm.trans hFw'
    have heq : C.concl wγ' = fγ' (Γ wγ') := hans' wγ' (hw'F.trans hx'F.symm)
    have htrue : fγ' (Γ wγ') = true := (hfγ' (Γ wγ')).mpr rfl
    have hyγ' : C.concl wγ' = false := hF wγ' hw'F
    exact Bool.noConfusion (hyγ'.symm.trans (heq.trans htrue))

/-- **Corollary 2.** With `X` fine-graining `Y`, the device infers some
two-valued function if and only if it has at least three setup values. -/
public theorem weaklyInfers_iff_three_setups
    {C : InferenceDevice.{u, v} U} (hfine : SetupRefinesConcl C) :
    ThreeSetupValues C ↔ ∃ Γ : U → Bool, (∃ u v : U, Γ u ≠ Γ v) ∧ WeaklyInfers C Γ := by
  constructor
  · exact exists_weaklyInfers_of_three_setups hfine
  · intro h
    obtain ⟨Γ, htwo, hW⟩ := h
    exact not_imp_not.mp
      (fun h2 => not_weaklyInfers_of_at_most_two_setups hfine h2 Γ htwo) hW

/-! ## Proposition 2(ii) — existence of a strong inferrer

The source builds, on each fibre of `C` (size `> 2`), a partial device that
answers both probes of `Y` while forcing that fibre, then stitches. Here the
stitching is the identity setup on `U`: each `C'`-fibre is a singleton, so
strong inference reduces to finding, in every `C`-fibre, one point of
**agreement** (`Y' = Y`) and one of **disagreement** (`Y' = ¬Y`). The third
point makes `Y'` surjective on that fibre.
-/

/-- Every realized setup fibre contains at least three points. -/
@[expose] public def LargeSetupFibres (C : InferenceDevice.{u, v} U) : Prop :=
  ∀ x : C.Setup, C.Realized x →
    ∃ a b d : U, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      C.setup a = x ∧ C.setup b = x ∧ C.setup d = x

/-- Three distinct points of setup-fibre `x`. -/
@[expose] public def IsFibreTriple (C : InferenceDevice.{u, v} U) (x : C.Setup)
    (p : U × U × U) : Prop :=
  p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧
    C.setup p.1 = x ∧ C.setup p.2.1 = x ∧ C.setup p.2.2 = x

/-- A triple of fibre points for setup value `x`. Depends only on `x`. -/
public noncomputable def fibreTripleOf (C : InferenceDevice.{u, v} U)
    (x : C.Setup) : U × U × U :=
  let _ : Nonempty U := ⟨Classical.choose (C.concl_surjective true)⟩
  Classical.epsilon (IsFibreTriple C x)

/-- Under `LargeSetupFibres`, the chosen triple really is three fibre points. -/
public theorem fibreTripleOf_spec {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) {x : C.Setup} (hx : C.Realized x) :
    IsFibreTriple C x (fibreTripleOf C x) := by
  obtain ⟨u, hu⟩ := hx
  let _ : Nonempty U := ⟨u⟩
  refine Classical.epsilon_spec (p := IsFibreTriple C x) ?_
  obtain ⟨a, b, d, hab, had, hbd, ha, hb, hd⟩ := h x ⟨u, hu⟩
  exact ⟨(a, b, d), hab, had, hbd, ha, hb, hd⟩

public theorem fibreTripleOf_spec_at {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    IsFibreTriple C (C.setup u) (fibreTripleOf C (C.setup u)) :=
  fibreTripleOf_spec h ⟨u, rfl⟩

/-- Agreement / disagreement / spare point of a setup fibre. -/
public noncomputable def agreeOf (C : InferenceDevice.{u, v} U) (x : C.Setup) : U :=
  (fibreTripleOf C x).1

public noncomputable def disagreeOf (C : InferenceDevice.{u, v} U) (x : C.Setup) : U :=
  (fibreTripleOf C x).2.1

public noncomputable def spareOf (C : InferenceDevice.{u, v} U) (x : C.Setup) : U :=
  (fibreTripleOf C x).2.2

public noncomputable def agreePoint (C : InferenceDevice.{u, v} U) (u : U) : U :=
  agreeOf C (C.setup u)

public noncomputable def disagreePoint (C : InferenceDevice.{u, v} U) (u : U) : U :=
  disagreeOf C (C.setup u)

public noncomputable def sparePoint (C : InferenceDevice.{u, v} U) (u : U) : U :=
  spareOf C (C.setup u)

public theorem agreePoint_in_fibre {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    C.setup (agreePoint C u) = C.setup u :=
  (fibreTripleOf_spec_at h u).2.2.2.1

public theorem disagreePoint_in_fibre {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    C.setup (disagreePoint C u) = C.setup u :=
  (fibreTripleOf_spec_at h u).2.2.2.2.1

public theorem sparePoint_in_fibre {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    C.setup (sparePoint C u) = C.setup u :=
  (fibreTripleOf_spec_at h u).2.2.2.2.2

public theorem agreePoint_ne_disagree {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    agreePoint C u ≠ disagreePoint C u :=
  (fibreTripleOf_spec_at h u).1

public theorem sparePoint_ne_agree {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    sparePoint C u ≠ agreePoint C u :=
  (fibreTripleOf_spec_at h u).2.1.symm

public theorem sparePoint_ne_disagree {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    sparePoint C u ≠ disagreePoint C u :=
  (fibreTripleOf_spec_at h u).2.2.1.symm

public theorem agreePoint_eq_of_setup_eq {C : InferenceDevice.{u, v} U}
    {u v : U} (heq : C.setup u = C.setup v) :
    agreePoint C u = agreePoint C v := by
  simp [agreePoint, heq]

/-- Proposition 2(ii) conclusion: agree with `C` at the agreement point,
disagree at the disagreement point, opposite of the agreement bit elsewhere. -/
public noncomputable def strongInferrerConcl (C : InferenceDevice.{u, v} U)
    (u : U) : Bool :=
  have := Classical.propDecidable (u = agreePoint C u)
  have := Classical.propDecidable (u = disagreePoint C u)
  if u = agreePoint C u then C.concl u
  else if u = disagreePoint C u then !(C.concl u)
  else !(C.concl (agreePoint C u))

public theorem strongInferrerConcl_agree {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    strongInferrerConcl C (agreePoint C u) = C.concl (agreePoint C u) := by
  classical
  have hsa : C.setup (agreePoint C u) = C.setup u := agreePoint_in_fibre h u
  simp [strongInferrerConcl, agreePoint_eq_of_setup_eq hsa]

public theorem strongInferrerConcl_disagree {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    strongInferrerConcl C (disagreePoint C u) =
      !(C.concl (disagreePoint C u)) := by
  classical
  have hsb : C.setup (disagreePoint C u) = C.setup u :=
    disagreePoint_in_fibre h u
  have hne : disagreePoint C u ≠ agreePoint C (disagreePoint C u) := by
    rw [agreePoint, hsb]; exact (agreePoint_ne_disagree h u).symm
  have hdd : disagreePoint C (disagreePoint C u) = disagreePoint C u := by
    change (fibreTripleOf C (C.setup (disagreePoint C u))).2.1 = disagreePoint C u
    rw [hsb]
    rfl
  unfold strongInferrerConcl
  rw [if_neg hne, hdd, if_pos rfl]

/-- **Proposition 2(ii) construction.** Identity setup; conclusion as above. -/
public noncomputable def strongInferrer (C : InferenceDevice.{u, v} U)
    (h : LargeSetupFibres C) : InferenceDevice.{u, u} U where
  Setup := U
  setup := id
  concl := strongInferrerConcl C
  concl_surjective := by
    classical
    intro b
    obtain ⟨w0, _⟩ := C.concl_surjective true
    let a := agreePoint C w0
    let s := sparePoint C w0
    have hsa : C.setup a = C.setup w0 := agreePoint_in_fibre h w0
    have hss : C.setup s = C.setup w0 := sparePoint_in_fibre h w0
    have hne : s ≠ a := sparePoint_ne_agree h w0
    have hne2 : s ≠ disagreePoint C w0 := sparePoint_ne_disagree h w0
    have hsConcl : strongInferrerConcl C s = !(C.concl a) := by
      unfold strongInferrerConcl
      have : agreePoint C s = a := agreePoint_eq_of_setup_eq hss
      have : disagreePoint C s = disagreePoint C w0 := by
        simp [disagreePoint, hss]
      rw [‹agreePoint C s = a›, ‹disagreePoint C s = disagreePoint C w0›,
        if_neg hne, if_neg hne2]
    cases b
    · cases ha : C.concl a
      · exact ⟨a, (strongInferrerConcl_agree h w0).trans ha⟩
      · exact ⟨s, hsConcl.trans (by simp [ha])⟩
    · cases ha : C.concl a
      · exact ⟨s, hsConcl.trans (by simp [ha])⟩
      · exact ⟨a, (strongInferrerConcl_agree h w0).trans ha⟩

/-- **Proposition 2(ii).** If every setup fibre has more than two states,
some device strongly infers `C`. -/
public theorem exists_stronglyInfers_of_large_fibres
    {C : InferenceDevice.{u, v} U} (h : LargeSetupFibres C) :
    ∃ C' : InferenceDevice.{u, u} U, StronglyInfers C' C := by
  refine ⟨strongInferrer C h, ?_⟩
  intro γ f hf _ x₂ hx₂
  obtain ⟨w₂, hw₂⟩ := hx₂
  have hsetup : C.setup w₂ = x₂ := hw₂
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨agreeOf C x₂, ⟨agreeOf C x₂, rfl⟩, ?_⟩
    intro w hw
    cases hw
    have hin : C.setup (agreeOf C x₂) = x₂ :=
      (fibreTripleOf_spec h ⟨w₂, hsetup⟩).2.2.2.1
    refine ⟨hin, ?_⟩
    have hcon := strongInferrerConcl_agree h (agreeOf C x₂)
    -- `agreePoint (agreeOf x₂)` reduces to `agreeOf x₂` by `hin`
    change strongInferrerConcl C
        (fibreTripleOf C (C.setup (agreeOf C x₂))).1 =
      C.concl (fibreTripleOf C (C.setup (agreeOf C x₂))).1 at hcon
    rw [hin] at hcon
    simpa [strongInferrer] using hcon
  · refine ⟨disagreeOf C x₂, ⟨disagreeOf C x₂, rfl⟩, ?_⟩
    intro w hw
    cases hw
    have hin : C.setup (disagreeOf C x₂) = x₂ :=
      (fibreTripleOf_spec h ⟨w₂, hsetup⟩).2.2.2.2.1
    refine ⟨hin, ?_⟩
    have hcon := strongInferrerConcl_disagree h (disagreeOf C x₂)
    change strongInferrerConcl C
        (fibreTripleOf C (C.setup (disagreeOf C x₂))).2.1 =
      !(C.concl (fibreTripleOf C (C.setup (disagreeOf C x₂))).2.1) at hcon
    rw [hin] at hcon
    simpa [strongInferrer] using hcon

end AISafetyAtlas.Inference
