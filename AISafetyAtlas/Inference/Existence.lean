module

public import AISafetyAtlas.Inference.Device

/-!
# When an inferring device exists

Definition 3 says what it is for a device to weakly infer a target. The
impossibility results say when no device does. This module holds the other
direction — a construction that produces one — and the condition under which the
construction works.

## The condition is sharp, and the source got it wrong once

Wolpert 2008 Corollary 1(ii) prints the existence claim with **no condition at
all**: *"For any function `Γ` with domain `U` there is a device that infers
`Γ`."* That is false, and `Examples.Inference.Device.no_device_weaklyInfers_id_on_bool`
refutes it at `Γ = id` on `Bool`, where the target attains two values.

Wolpert 2018 Proposition 7(1) prints the same claim for `|Γ(U)| ≥ 3`. Definition
2 of both papers requires only `|Γ(U)| ≥ 2`, so that is a strengthened hypothesis
and not a convention carried over — the author repaired his own corollary, and
`identityDevice_weaklyInfers` is that repair. The printed claim is now fully
adjudicated: false as stated, true at three values, with the countermodel sitting
in exactly the excluded case. Source note: clash 20 in
[`wolpert-2008-source-clashes.md`](../../docs/provenance/wolpert-2008-source-clashes.md).

## Scope

Proved without either standing hypothesis the 2018 statement carries. It says
*"Let `U` be any countable space with at least two elements"*; countability
appears nowhere in the argument, and `|U| ≥ 2` follows from the target attaining
three values. The target type is arbitrary and lives in its own universe.

`|Γ(U)| ≥ 3` is rendered as three points of `U` with pairwise distinct values,
which is what "at least three values are attained" means on a possibly infinite
image, and needs no `Fintype`.
-/

namespace AISafetyAtlas.Inference

variable {U : Type u}

open scoped Classical in
/--
The device of the source's proof: *"Let `X(u)` be the identity function (so that
each `u ∈ U` has its own, unique value `x`). Choose `Y(u)` to equal 1 for exactly
one `u`, `ū`."*

`Setup := U` with `setup := id` is that identity setup, so every fibre is a
singleton and answering a probe is a pointwise condition. `hne` is what
Definition 1's surjectivity of the conclusion needs, and it is discharged from
the three distinct values at the one call site.
-/
public noncomputable def identityDevice (ū : U) (hne : ∃ u : U, u ≠ ū) :
    InferenceDevice.{u, u} U where
  Setup := U
  setup := id
  concl := fun u => decide (u = ū)
  concl_surjective := by
    intro y
    cases y with
    | true => exact ⟨ū, by simp⟩
    | false =>
      obtain ⟨u, hu⟩ := hne
      exact ⟨u, by simp [hu]⟩

/--
**Wolpert 2018, Proposition 7(1).** *"For any function `Γ` over `U` such that
`|Γ(U)| ≥ 3` there is a device `D` that weakly infers `Γ`."*

The three values are the whole content, and the source's proof says where they
go: the probe of `Γ(ū)` is answered `true` at `ū`, and every other probe is
answered `false` at a point carrying a third value — which must exist off `ū`
precisely because a third value exists.

At `|Γ(U)| = 2` the argument breaks exactly where 2008 Corollary 1(ii) is
refuted: the only point disagreeing with the probed value may be `ū` itself,
where the conclusion is `true`.
-/
public theorem identityDevice_weaklyInfers {G : Type v} (Γ : U → G)
    {a b c : U} (hab : Γ a ≠ Γ b) (hac : Γ a ≠ Γ c) (hbc : Γ b ≠ Γ c) :
    WeaklyInfers (identityDevice a ⟨b, fun h => hab (h ▸ rfl)⟩) Γ := by
  classical
  intro γ f hf _
  -- Every fibre of the identity setup is a singleton, so a setup value answers a
  -- probe exactly when it answers it at that one point.
  have pointwise : ∀ x : U, (identityDevice a ⟨b, fun h => hab (h ▸ rfl)⟩).concl x =
      f (Γ x) → ∃ x' : U, (identityDevice a ⟨b, fun h => hab (h ▸ rfl)⟩).Realized x' ∧
        ∀ w : U, (identityDevice a ⟨b, fun h => hab (h ▸ rfl)⟩).setup w = x' →
          (identityDevice a ⟨b, fun h => hab (h ▸ rfl)⟩).concl w = f (Γ w) := by
    intro x hx
    exact ⟨x, ⟨x, rfl⟩, fun w hw => by cases hw; exact hx⟩
  by_cases hγ : γ = Γ a
  · -- The probed value is the one the device says `true` to.
    refine pointwise a ?_
    show decide (a = a) = f (Γ a)
    rw [decide_eq_true (rfl : a = a), (hf (Γ a)).mpr hγ.symm]
  · -- Some point off `a` carries a value other than `γ`: `b` and `c` both lie off
    -- `a` because their values differ from `Γ a`, and they cannot both carry `γ`
    -- because their values differ from each other.
    have hb_ne : b ≠ a := fun h => hab (h ▸ rfl)
    have hc_ne : c ≠ a := fun h => hac (h ▸ rfl)
    have hpoint : ∃ x : U, x ≠ a ∧ Γ x ≠ γ := by
      by_cases hbγ : Γ b = γ
      · exact ⟨c, hc_ne, fun h => hbc (hbγ.trans h.symm)⟩
      · exact ⟨b, hb_ne, hbγ⟩
    obtain ⟨x, hxa, hxγ⟩ := hpoint
    refine pointwise x ?_
    have hR : f (Γ x) = false := by
      cases hfx : f (Γ x) with
      | false => rfl
      | true => exact absurd ((hf (Γ x)).mp hfx) hxγ
    show decide (x = a) = f (Γ x)
    rw [decide_eq_false hxa, hR]

/-- The printed existential. -/
public theorem exists_weaklyInfers_of_three_values {G : Type v} (Γ : U → G)
    {a b c : U} (hab : Γ a ≠ Γ b) (hac : Γ a ≠ Γ c) (hbc : Γ b ≠ Γ c) :
    ∃ C : InferenceDevice.{u, u} U, WeaklyInfers C Γ :=
  ⟨_, identityDevice_weaklyInfers Γ hab hac hbc⟩

/-! ## Definition 4 and Proposition 7(2)

2008 Definition 5 lets one device strongly infer another. Wolpert 2018 Definition
4 states the same relation against an arbitrary **pair of functions** `(S, T)`,
with `S` playing the role the other device's setup played and `T` the role of its
conclusion. The generalization is **conservative**: at a device's own pair the
two definitions are the same relation, `stronglyInfers_iff_stronglyInfersPair`.
What it buys is reach, not a different notion — a pair of functions need not come
from any device, and Proposition 7(2)'s witness `(id, id)` is such a pair except
when `U = Bool`. That is the whole content of clash 28: the relation transfers,
the witness does not.
-/

/--
**Wolpert 2018, Definition 4.** *"Let `S` and `T` be functions both defined over
`U`. A device `(X, Y)` strongly infers `(S, T)` iff `∀δ ∈ P(T)` and all
`s ∈ S(U)`, `∃x` such that `X(u) = x ⇒ {S(u) = s, Y(u) = δ(T(u))}`."*

The quantifier order is the source's: one setup value per (probe, `S`-value)
pair, and both obligations hold on the fibre that value induces.
-/
@[expose] public def StronglyInfersPair (C : InferenceDevice.{u, v} U)
    {S : Type w} {T : Type w'} (s : U → S) (t : U → T) : Prop :=
  ∀ (τ : T) (f : T → Bool), IsProbe f τ → (∃ w : U, t w = τ) →
    ∀ σ : S, (∃ w : U, s w = σ) →
      ∃ x : C.Setup, C.Realized x ∧
        ∀ w : U, C.setup w = x → s w = σ ∧ C.concl w = f (t w)

/-- **Definition 5 is Definition 4 at a device's own pair.** *"By considering the
special case where `T(U) = 𝔹`, we can use strong inference to formalize what it
means for one device to emulate another."* The two definitions agree exactly,
which is what makes the generalization conservative. -/
public theorem stronglyInfers_iff_stronglyInfersPair (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) :
    StronglyInfers C₁ C₂ ↔ StronglyInfersPair C₁ C₂.setup C₂.concl := by
  constructor
  · intro h τ f hf hτ σ hσ
    obtain ⟨x, hx, hall⟩ := h τ f hf hτ σ hσ
    exact ⟨x, hx, hall⟩
  · intro h γ f hf hγ x₂ hx₂
    obtain ⟨x, hx, hall⟩ := h γ f hf hγ x₂ hx₂
    exact ⟨x, hx, hall⟩

/--
**Wolpert 2018, Proposition 7(2).** *"There is a (vector-valued) function
`(S, T)` over `U` that is not strongly inferred by any device."*

The source's construction: take both `S` and `T` to be the identity. Then the
first obligation forces the fibre over the chosen setup value to be the single
point `s`, and the second forces the conclusion there to answer the probe of `s`
at `s` — which is `true`. Since `s` was arbitrary, the conclusion is constantly
`true`, contradicting Definition 1's surjectivity.

Nothing here is finite, decidable or countable: `U` is an arbitrary type, and the
probe at each point is supplied classically by `exists_isProbe`.
-/
public theorem not_stronglyInfersPair_id (C : InferenceDevice.{u, v} U) :
    ¬ StronglyInfersPair C (id : U → U) (id : U → U) := by
  intro h
  -- The conclusion is `true` at every point of `U`.
  have hall : ∀ σ : U, C.concl σ = true := by
    intro σ
    obtain ⟨f, hf⟩ := exists_isProbe σ
    obtain ⟨x, hx, hfib⟩ := h σ f hf ⟨σ, rfl⟩ σ ⟨σ, rfl⟩
    -- The fibre is nonempty, and its first obligation pins it to `σ`.
    obtain ⟨w, hw⟩ := hx
    obtain ⟨hid, hconcl⟩ := hfib w hw
    have : w = σ := hid
    subst this
    rw [hconcl]
    exact (hf w).mpr rfl
  obtain ⟨w, hw⟩ := C.concl_surjective false
  rw [hall w] at hw
  exact Bool.noConfusion hw

/-- The printed existential: some pair of functions is strongly inferred by no
device at all. -/
public theorem exists_pair_not_stronglyInfers :
    ∃ S T : U → U, ∀ C : InferenceDevice.{u, v} U, ¬ StronglyInfersPair C S T :=
  ⟨id, id, fun C => not_stronglyInfersPair_id C⟩

/-- The source's Proposition 7(2) witness is `S = T = id`. That pair is a
**device** pair only when the second component can be a conclusion, i.e. only
when `U = Bool` and so `|U| = 2`. The printed `|U| > 3` excludes exactly that
case. Clash 28. -/
@[expose] public def idDeviceOnBool : InferenceDevice Bool where
  Setup := Bool
  setup := id
  concl := id
  concl_surjective := Function.surjective_id

public theorem id_is_device_pair_on_bool :
    idDeviceOnBool.setup = id ∧ idDeviceOnBool.concl = id :=
  ⟨rfl, rfl⟩

/-! ## A grid of paired spins — Wolpert 2008, Example 5

*"Consider a rectangular grid of particle pairs, each pair consisting of a yellow
particle and a purple particle… Then we can define a 'purple inference device'
`C_p` by `X_p ≜ i` and `Y_p ≜ s_p(i, j)`. Similarly, a 'yellow inference device'
… `X_y ≜ j` and `Y_y ≜ s_y(i, j)`. These two devices are distinguishable. In
addition, `C_p > C_y` if there is some `i'` such that `s_p(i', j) = s_y(i', j)`
for all `j`, and also some `i''` such that `s_p(i'', j) = −s_y(i'', j)` for all
`j`… However if there is such an `i'` and `i''`, then clearly there cannot also
be both a value `j'` and a value `j''` that the yellow inference device can use
to answer whether `s_p` points up and whether `s_p` points down."*

The example is the paper's concrete face of Theorem 1, which it says *"generalizes
this impossibility result"*. What Theorem 1 does not supply is the other half:
that the hypotheses are **inhabited** — that a grid meeting them exists at all.
Both halves are here, and `Examples.Inference.SpinGrid` exhibits a grid.

## Scope

Stated for an arbitrary index pair `I`, `J` in their own universes, so *"regardless
of the size of the grid and the particular pattern"* is the theorem rather than a
remark about it. The source's standing assumptions that there be at least two `i`
values and at least two `j` values are **not needed**: distinguishability of the
row and column devices holds unconditionally, because every site `(i, j)` lies in
both the row-`i` and the column-`j` fibre. Definition 1's surjectivity is the
source's own *"at least one purple spin is up and at least one is down"*.
-/

section SpinGrid

variable {I : Type v} {J : Type w}

/-- The **purple device**: set up by the row index, concluding that row's purple
spin at whichever site the universe is at. -/
public def rowSpinDevice (sp : I → J → Bool)
    (hs : Function.Surjective fun p : I × J => sp p.1 p.2) :
    InferenceDevice.{max v w, v} (I × J) where
  Setup := I
  setup := Prod.fst
  concl := fun p => sp p.1 p.2
  concl_surjective := hs

/-- The **yellow device**: the same grid read by column. -/
public def colSpinDevice (sy : I → J → Bool)
    (hs : Function.Surjective fun p : I × J => sy p.1 p.2) :
    InferenceDevice.{max v w, w} (I × J) where
  Setup := J
  setup := Prod.snd
  concl := fun p => sy p.1 p.2
  concl_surjective := hs

/--
*"These two devices are distinguishable."* Unconditionally: the site `(i, j)` is
in the row-`i` fibre and the column-`j` fibre at once, so no pair of realized
setup values excludes each other. The source's two-values-per-axis assumptions
are not used.
-/
public theorem rowSpinDevice_distinguishable_colSpinDevice
    (sp sy : I → J → Bool)
    (hp : Function.Surjective fun p : I × J => sp p.1 p.2)
    (hy : Function.Surjective fun p : I × J => sy p.1 p.2) :
    Distinguishable (rowSpinDevice sp hp) (colSpinDevice sy hy) := by
  intro i _ j _
  exact ⟨(i, j), rfl, rfl⟩

/--
*"`C_p > C_y` if there is some `i'` … and also some `i''` …"*

The agreeing row answers the identity probe and the anti-agreeing row answers the
negation probe, which are the only two probes of `𝔹`. Each row is a single fibre
of the purple setup, so answering the probe there is exactly the pointwise spin
condition the source states.
-/
public theorem rowSpinDevice_infersDevice_colSpinDevice
    (sp sy : I → J → Bool)
    (hp : Function.Surjective fun p : I × J => sp p.1 p.2)
    (hy : Function.Surjective fun p : I × J => sy p.1 p.2)
    (hagree : ∃ i : I, ∀ j : J, sp i j = sy i j)
    (hanti : ∃ i : I, ∀ j : J, sp i j = !(sy i j)) :
    InfersDevice (rowSpinDevice sp hp) (colSpinDevice sy hy) := by
  -- Surjectivity of a conclusion function already puts a site in the grid, so the
  -- source's nonemptiness assumptions come for free.
  obtain ⟨site, -⟩ := hp true
  intro γ f hf _
  cases γ with
  | true =>
    -- A probe of `𝔹` at `true` is the identity, pointwise.
    have hid : ∀ b : Bool, f b = b := by
      intro b
      cases b with
      | true => exact (hf true).mpr rfl
      | false =>
        cases hfb : f false with
        | false => rfl
        | true => exact Bool.noConfusion ((hf false).mp hfb)
    obtain ⟨i, hi⟩ := hagree
    refine ⟨i, ⟨(i, site.2), rfl⟩, ?_⟩
    rintro ⟨a, b⟩ hw
    have ha : a = i := hw
    subst ha
    show sp a b = f (sy a b)
    rw [hid (sy a b)]
    exact hi b
  | false =>
    -- A probe of `𝔹` at `false` is the negation, pointwise.
    have hnot : ∀ b : Bool, f b = !b := by
      intro b
      cases b with
      | false => exact (hf false).mpr rfl
      | true =>
        cases hfb : f true with
        | false => rfl
        | true => exact Bool.noConfusion ((hf true).mp hfb)
    obtain ⟨i, hi⟩ := hanti
    refine ⟨i, ⟨(i, site.2), rfl⟩, ?_⟩
    rintro ⟨a, b⟩ hw
    have ha : a = i := hw
    subst ha
    show sp a b = f (sy a b)
    rw [hnot (sy a b)]
    exact hi b

/--
*"However if there is such an `i'` and `i''`, then clearly there cannot also be
both a value `j'` and a value `j''` that the yellow inference device can use to
answer whether `s_p` points up and whether `s_p` points down."*

This is the paper's own reading: the impossibility half of Example 5 **is**
Theorem 1, applied to the two devices the example builds.
-/
public theorem not_colSpinDevice_infersDevice_rowSpinDevice
    (sp sy : I → J → Bool)
    (hp : Function.Surjective fun p : I × J => sp p.1 p.2)
    (hy : Function.Surjective fun p : I × J => sy p.1 p.2)
    (hagree : ∃ i : I, ∀ j : J, sp i j = sy i j)
    (hanti : ∃ i : I, ∀ j : J, sp i j = !(sy i j)) :
    ¬ InfersDevice (colSpinDevice sy hy) (rowSpinDevice sp hp) := fun hback =>
  not_infersDevice_both_of_distinguishable
    (rowSpinDevice_distinguishable_colSpinDevice sp sy hp hy)
    (rowSpinDevice_infersDevice_colSpinDevice sp sy hp hy hagree hanti)
    hback

end SpinGrid

end AISafetyAtlas.Inference
