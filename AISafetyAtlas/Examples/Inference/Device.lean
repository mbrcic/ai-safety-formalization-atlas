module

public import AISafetyAtlas.Inference
public import AISafetyAtlas.Knowledge.Ambiguity

/-!
# Inference devices — worked models

Five things this file settles, none of which the abstract development settles on
its own.

1. **Weak inference is not vacuous.** `witnessInfers` really does weakly infer a
   target, built the way Wolpert's Proposition 1(i) builds one: a conclusion
   function that is `false` exactly on a distinguishing set, and a setup that
   separates that set's points.
2. **Theorem 1 has a genuine instance.** A distinguishable pair in which *one*
   direction of weak inference holds, so distinguishability is what rules out the
   other. (A pair where neither direction holds does not exercise the theorem.)
3. **Weak inference is not knowability, in either direction.** Both countermodels
   are here, and they are why the relationship to the atlas knowability kernel is
   recorded as `RELATED` rather than as a definitional identification. That is the
   *kernel* relationship; BY-024's own grade against Wolpert 2008 is separate.
4. **Strong inference, control, Theorem 5 and Corollary 3 are inhabited.**
   `StronglyInfers` has a positive witness; `Controls` has a positive witness;
   a shared-setup pair exhibits mutual weak inference, identical partitions, and
   the failure of either to control that setup. A constant-setup device is
   distinguishable from itself — the source excludes that case.
5. **Section 9's Theorem 6 hypotheses are inhabited.** `saDev` instantiates
   Theorem 6(i); `saStrongDev` and `saTargetDevice` instantiate the strictly
   stronger setup-pair hypotheses of Theorem 6(ii). Before these witnesses, the
   only `SelfAwareDevice` in the tree was Proposition 7's `uncorrectable`.

Every model is finite and every check is `decide`-able.
-/

namespace AISafetyAtlas.Examples.Inference.Device

open AISafetyAtlas.Inference
open AISafetyAtlas.Knowledge

/-! ## 1. Weak inference is not vacuous -/

/-- Wolpert's Proposition 1(i) conclusion function: `false` exactly on the
distinguishing set `W = {0, 1}`. -/
public abbrev wConcl : Fin 3 → Bool
  | 0 => false
  | 1 => false
  | 2 => true

public theorem wConcl_surjective : Function.Surjective wConcl := by
  intro b
  cases b
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

/-- The setup separates the points of `W`, as the construction requires. -/
public abbrev witnessInfers : InferenceDevice (Fin 3) where
  Setup := Fin 3
  setup := id
  concl := wConcl
  concl_surjective := wConcl_surjective

/-- A target taking both values on `W`. -/
public abbrev wTarget : Fin 3 → Bool
  | 0 => true
  | 1 => false
  | 2 => true

/--
The device weakly infers the target: each probe is answered on some realized
fibre. The two probes are answered on **different** fibres, which is the
quantifier order doing its work — no single setup value answers both.
-/
public theorem witnessInfers_weaklyInfers : WeaklyInfers witnessInfers wTarget := by
  intro γ f hf _
  have hfv : ∀ b : Bool, f b = decide (b = γ) := by
    intro b
    cases hb : f b
    · exact (decide_eq_false (fun hc => by simp [hf b |>.mpr hc] at hb)).symm
    · exact (decide_eq_true (hf b |>.mp hb)).symm
  have h0 : ∀ w : Fin 3, id w = (0 : Fin 3) → wConcl w = decide (wTarget w = false) := by decide
  have h1 : ∀ w : Fin 3, id w = (1 : Fin 3) → wConcl w = decide (wTarget w = true) := by decide
  cases γ
  · refine ⟨0, ⟨0, rfl⟩, fun w hw => ?_⟩
    rw [hfv]; exact h0 w hw
  · refine ⟨1, ⟨1, rfl⟩, fun w hw => ?_⟩
    rw [hfv]; exact h1 w hw

/-! ## 2. Theorem 1 — one direction holds, distinguishability kills the other

Wolpert's grid: the row device can match the column device's conclusion on one
row and mismatch it on the other, so it weakly infers that conclusion. The two
setups are independent, so Theorem 1 forbids the reverse. Independent coordinates
with matching conclusions would not exercise the theorem, so that rejected pair
is not retained as a public example.
-/

/-- Row index as setup; conclusion equals the column on row `false` and its
negation on row `true`. -/
public abbrev rowDevice : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := fun p => xor p.1 p.2
  concl_surjective := fun b => ⟨(false, b), by cases b <;> rfl⟩

/-- Column index as setup; conclusion is the column. -/
public abbrev colDevice : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.snd
  concl := Prod.snd
  concl_surjective := fun b => ⟨(b, b), rfl⟩

public theorem row_col_distinguishable : Distinguishable rowDevice colDevice := by
  intro x₁ _ x₂ _
  exact ⟨(x₁, x₂), rfl, rfl⟩

/-- The row device weakly infers the column device's conclusion. -/
public theorem row_infers_col : InfersDevice rowDevice colDevice := by
  intro γ f hf _
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨false, ⟨(false, false), rfl⟩, ?_⟩
    intro w hw
    cases w with
    | mk a b =>
      cases a
      · cases b <;> rfl
      · cases hw
  · refine ⟨true, ⟨(true, false), rfl⟩, ?_⟩
    intro w hw
    cases w with
    | mk a b =>
      cases a
      · cases hw
      · cases b <;> rfl

/-- **Theorem 1 applied.** One direction holds; distinguishability rules out
the other. -/
public theorem col_not_infers_row : ¬ InfersDevice colDevice rowDevice :=
  fun h =>
    not_infersDevice_both_of_distinguishable row_col_distinguishable
      row_infers_col h

/-! ## 3. Weak inference is not knowability

The two countermodels behind the `RELATED` relationship.
-/

/-- Setup is the identity, so the target factors through it — but the device's
conclusion is the negation, and a device's conclusion function is fixed, not
chosen the way a decoder is. -/
public abbrev negDevice : InferenceDevice Bool where
  Setup := Bool
  setup := id
  concl := not
  concl_surjective := fun b => ⟨!b, by cases b <;> rfl⟩

/-- Knowable: the identity decoder reproduces the target everywhere. -/
public theorem negDevice_target_knowable :
    Knowable negDevice.setup (id : Bool → Bool) :=
  ⟨id, fun _ => rfl⟩

/-- Yet the device weakly infers nothing about that target. -/
public theorem negDevice_not_weaklyInfers :
    ¬ WeaklyInfers negDevice (id : Bool → Bool) := by
  intro h
  obtain ⟨x, ⟨w, hw⟩, hfib⟩ := h true id isProbe_id ⟨true, rfl⟩
  exact Bool.not_ne_self w (hfib w hw)

/-- The converse failure. This setup cannot separate `1` from `2`. -/
public abbrev coarseConcl : Fin 3 → Bool
  | 0 => true
  | 1 => false
  | 2 => true

public theorem coarseConcl_surjective : Function.Surjective coarseConcl := by
  intro b
  cases b
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

/-- The target for the second countermodel. It is deliberately *not* the device's
conclusion function: the negation probe has to be answerable somewhere. -/
public abbrev coarseTarget : Fin 3 → Bool
  | 0 => true
  | 1 => true
  | 2 => false

/-- Two setup values only: `0`, and everything else. -/
public abbrev coarseDevice : InferenceDevice (Fin 3) where
  Setup := Bool
  setup := fun i => decide (i = 0)
  concl := coarseConcl
  concl_surjective := coarseConcl_surjective

/-- Every probe is answered on some fibre. -/
public theorem coarseDevice_weaklyInfers : WeaklyInfers coarseDevice coarseTarget := by
  intro γ f hf _
  have hfv : ∀ b : Bool, f b = decide (b = γ) := by
    intro b
    cases hb : f b
    · exact (decide_eq_false (fun hc => by simp [hf b |>.mpr hc] at hb)).symm
    · exact (decide_eq_true (hf b |>.mp hb)).symm
  have hF : ∀ w : Fin 3, decide (w = 0) = false →
      coarseConcl w = decide (coarseTarget w = false) := by decide
  have hT : ∀ w : Fin 3, decide (w = 0) = true →
      coarseConcl w = decide (coarseTarget w = true) := by decide
  cases γ
  · refine ⟨false, ⟨1, rfl⟩, fun w hw => ?_⟩
    rw [hfv]; exact hF w hw
  · refine ⟨true, ⟨0, rfl⟩, fun w hw => ?_⟩
    rw [hfv]; exact hT w hw

/-- Yet the target is not knowable from that setup: the fibre `{1, 2}` mixes
target values, so no decoder can work uniformly. -/
public theorem coarseDevice_target_not_knowable :
    ¬ Knowable coarseDevice.setup coarseTarget := by
  rw [knowable_iff_ambiguity_le_one]
  decide

/-! ## 4. Corollary 1(ii) needs a hypothesis the source leaves implicit

Wolpert's Corollary 1(ii) reads: *"For any function `Γ` with domain `U` there is a
device that infers `Γ`."* It is offered as a consequence of Proposition 1(i), which
requires a **proper** subset `W ⊂ U` on which `Γ` already attains all its values.

When `Γ` is injective and `U` has no spare state, no such `W` exists — and the
conclusion fails outright, not merely the construction. Two states suffice to show
it.

The failure depends on reading `∃ x` as ranging over *realized* setup values, which
is the source's own convention in Definition 3 (`∃ x ∈ X(U)`). Allowing an
unrealized setup value would make weak inference vacuously true and the corollary
trivially so.

This is a missing hypothesis, not a broken theorem: on a set of universes large
enough for some value of `Γ` to be attained twice, Proposition 1(i) applies and the
corollary holds. It is recorded because the atlas grades statements, not intentions.
-/

/-- **No device over a two-state universe weakly infers the identity.** Whichever
setup values answer the two probes, the conclusion function is forced to be
constant, contradicting its surjectivity. -/
public theorem no_device_weaklyInfers_id_on_bool :
    ¬ ∃ C : InferenceDevice.{0, 0} Bool, WeaklyInfers C (id : Bool → Bool) := by
  rintro ⟨C, h⟩
  obtain ⟨x₁, ⟨w₁, hw₁⟩, hf₁⟩ := h true id isProbe_id ⟨true, rfl⟩
  obtain ⟨x₂, ⟨w₂, hw₂⟩, hf₂⟩ := h false (fun b => !b) isProbe_not ⟨false, rfl⟩
  have e₁ : C.concl w₁ = w₁ := hf₁ w₁ hw₁
  have e₂ : C.concl w₂ = !w₂ := hf₂ w₂ hw₂
  by_cases hx : x₁ = x₂
  · -- one fibre answers both probes, so its states must disagree with themselves
    subst hx
    have := hf₂ w₁ hw₁
    rw [e₁] at this
    cases w₁ <;> simp at this
  · -- distinct fibres exhaust a two-state universe, forcing a constant conclusion
    have hne : w₁ ≠ w₂ := by
      intro hc; apply hx; rw [← hw₁, ← hw₂, hc]
    have hconst : ∀ v : Bool, C.concl v = C.concl w₁ := by
      intro v
      cases w₁ <;> cases w₂ <;> simp_all <;> cases v <;> simp_all
    obtain ⟨b, hb⟩ := C.concl_surjective (!(C.concl w₁))
    rw [hconst b] at hb
    exact Bool.self_ne_not _ hb

/-! ## 5. Constant setup — self-distinguishability

The source says no device is distinguishable from itself, under its global
two-value stipulation on every function. Dropping that on *setups* makes a
constant-setup device distinguishable from itself.
-/

public abbrev constSetupDevice : InferenceDevice Bool where
  Setup := Unit
  setup := fun _ => ()
  concl := id
  concl_surjective := fun b => ⟨b, rfl⟩

public theorem constSetup_distinguishable_self :
    Distinguishable constSetupDevice constSetupDevice := by
  intro x₁ h₁ x₂ _
  obtain ⟨w, hw⟩ := h₁
  cases x₁
  cases x₂
  exact ⟨w, hw, rfl⟩

/-! ## 6. Strong inference is satisfiable

Each coarse fibre must contain a point where the fine conclusion agrees with the
coarse conclusion and a point where it disagrees, so both probes can be answered
while forcing the coarse setup.
-/

public abbrev fineDevice : InferenceDevice (Fin 4) where
  Setup := Fin 4
  setup := id
  concl := fun i => decide (i.val < 2)
  concl_surjective := by
    intro b
    cases b
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩

public abbrev coarseForcedDevice : InferenceDevice (Fin 4) where
  Setup := Bool
  setup := fun i => decide (2 ≤ i.val)
  concl := fun i => decide (i.val % 2 = 1)
  concl_surjective := by
    intro b
    cases b
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

public theorem fine_stronglyInfers_coarse :
    StronglyInfers fineDevice coarseForcedDevice := by
  intro γ f hf _ x₂ hx₂
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases hx₂ : x₂
    · refine ⟨1, ⟨1, rfl⟩, ?_⟩
      intro w hw
      have hw1 : w = 1 := hw
      subst hw1
      exact ⟨by decide, by decide⟩
    · refine ⟨2, ⟨2, rfl⟩, ?_⟩
      intro w hw
      have hw2 : w = 2 := hw
      subst hw2
      exact ⟨by decide, by decide⟩
  · cases hx₂ : x₂
    · refine ⟨0, ⟨0, rfl⟩, ?_⟩
      intro w hw
      have hw0 : w = 0 := hw
      subst hw0
      exact ⟨by decide, by decide⟩
    · refine ⟨3, ⟨3, rfl⟩, ?_⟩
      intro w hw
      have hw3 : w = 3 := hw
      subst hw3
      exact ⟨by decide, by decide⟩

/-- Theorem 2's strong-to-weak consequence has a concrete finite consumer. -/
public theorem fine_infers_coarse : InfersDevice fineDevice coarseForcedDevice :=
  infersDevice_of_stronglyInfers fine_stronglyInfers_coarse

/-- Section 7's strong-to-semi-control consequence has the same consumer. -/
public theorem fine_semiControls_coarse_setup :
    SemiControls fineDevice coarseForcedDevice.setup :=
  semiControls_setup_of_stronglyInfers fine_stronglyInfers_coarse

/-! ## 7. Control is satisfiable

Singleton fibres: pick the pair `(desired conclusion bit, target value)` so the
probe and the conclusion both equal the requested bit.
-/

public abbrev controlDevice : InferenceDevice (Bool × Bool) where
  Setup := Bool × Bool
  setup := id
  concl := Prod.fst
  concl_surjective := fun b => ⟨(b, b), rfl⟩

/-- `controlDevice` controls the second coordinate. -/
public theorem controlDevice_controls_snd :
    Controls controlDevice (Prod.snd : Bool × Bool → Bool) := by
  intro γ f hf _ b
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · cases b
    · refine ⟨(false, false), ⟨(false, false), rfl⟩, ?_⟩
      intro w hw
      cases hw
      exact ⟨rfl, rfl⟩
    · refine ⟨(true, true), ⟨(true, true), rfl⟩, ?_⟩
      intro w hw
      cases hw
      exact ⟨rfl, rfl⟩
  · cases b
    · refine ⟨(false, true), ⟨(false, true), rfl⟩, ?_⟩
      intro w hw
      cases hw
      exact ⟨rfl, rfl⟩
    · refine ⟨(true, false), ⟨(true, false), rfl⟩, ?_⟩
      intro w hw
      cases hw
      exact ⟨rfl, rfl⟩

/-! ## 8. Shared setup — Theorem 5 and Corollary 3 -/

/-- Shared setup `Prod.fst`. Conclusion is the second bit. -/
public abbrev sharedSetupLeft : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

/-- Same setup; conclusion equals the second bit on `{true}×_` and its
negation on `{false}×_`. The two fibres are exactly the identity and negation
witnesses of Corollary 3(i). -/
public abbrev sharedSetupRight : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := fun p => decide (p.1 = p.2)
  concl_surjective := by
    intro b
    cases b
    · exact ⟨(false, true), rfl⟩
    · exact ⟨(true, true), rfl⟩

/-- Each can force every value of the shared setup, so Theorem 5 applies. -/
public theorem shared_semiControls_left :
    SemiControls sharedSetupLeft sharedSetupRight.setup := by
  intro γ _
  exact ⟨γ, ⟨(γ, γ), rfl⟩, fun w hw => hw⟩

public theorem shared_semiControls_right :
    SemiControls sharedSetupRight sharedSetupLeft.setup := by
  intro γ _
  exact ⟨γ, ⟨(γ, γ), rfl⟩, fun w hw => hw⟩

/-- **Theorem 5 applied.** The setup partitions agree — here they are identical. -/
public theorem shared_setup_partitions :
    ∀ w w' : Bool × Bool,
      sharedSetupLeft.setup w = sharedSetupLeft.setup w' ↔
        sharedSetupRight.setup w = sharedSetupRight.setup w' :=
  setup_partition_eq_of_semiControls_setup
    shared_semiControls_left shared_semiControls_right

/-- They do weakly infer each other, so Corollary 3(i) is not an empty iff. -/
public theorem shared_left_infers_right : InfersDevice sharedSetupLeft sharedSetupRight := by
  intro γ f hf _
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨true, ⟨(true, true), rfl⟩, ?_⟩
    intro w hw
    -- fibre `fst = true`: second bit equals `decide (true = second bit)`
    cases w with
    | mk a b =>
      cases a
      · cases hw
      · cases b <;> rfl
  · refine ⟨false, ⟨(false, false), rfl⟩, ?_⟩
    intro w hw
    -- fibre `fst = false`: second bit equals the negation of `decide (false = _)`
    cases w with
    | mk a b =>
      cases a
      · cases b <;> rfl
      · cases hw

public theorem shared_right_infers_left : InfersDevice sharedSetupRight sharedSetupLeft :=
  (infersDevice_comm_of_semiControls_setup
      shared_semiControls_left shared_semiControls_right).mp
    shared_left_infers_right

/-- **Corollary 3(iii) applied.** Neither controls the shared setup. -/
public theorem shared_not_controls_other_setup :
    ¬ Controls sharedSetupLeft sharedSetupRight.setup :=
  not_controls_other_setup_of_semiControls_setup
    shared_semiControls_left shared_semiControls_right

/-- **Corollary 3(ii) applied.** Neither strongly infers the other. -/
public theorem shared_not_stronglyInfers_either :
    ¬ StronglyInfers sharedSetupLeft sharedSetupRight ∧
      ¬ StronglyInfers sharedSetupRight sharedSetupLeft :=
  not_stronglyInfers_either_of_semiControls_setup
    shared_semiControls_left shared_semiControls_right

/-! ## 9. Definition 7 across two universes

Definition 7 opens *"Let `U` and `Û` be two (perhaps identical) sets"* — copies
across different realities are the concept. These two devices live over `Bool` and
over `Fin 2` and realize the same `(setup, conclusion)` pairs, so each mimics the
other. A same-universe `Copies` API could not state this.
-/

public abbrev boolDev : InferenceDevice Bool where
  Setup := Bool
  setup := id
  concl := id
  concl_surjective := fun b => ⟨b, rfl⟩

public abbrev fin2Dev : InferenceDevice (Fin 2) where
  Setup := Bool
  setup := fun i => decide (i = 1)
  concl := fun i => decide (i = 1)
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨1, rfl⟩

public theorem boolDev_realized (x : Bool) : boolDev.Realized x := ⟨x, rfl⟩

public theorem fin2Dev_realized : ∀ x : Bool, fin2Dev.Realized x
  | false => ⟨0, rfl⟩
  | true => ⟨1, rfl⟩

/-- Both devices realize exactly the diagonal pairs. -/
public theorem boolDev_pairs (x y : Bool) :
    ((x, y) ∈ realizedPairs boolDev) ↔ x = y := by
  constructor
  · rintro ⟨w, hs, hc⟩; exact hs.symm.trans hc
  · rintro rfl; exact ⟨x, rfl, rfl⟩

public theorem fin2Dev_pairs (x y : Bool) :
    ((x, y) ∈ realizedPairs fin2Dev) ↔ x = y := by
  constructor
  · rintro ⟨w, hs, hc⟩; exact hs.symm.trans hc
  · rintro rfl
    cases x
    · exact ⟨0, rfl, rfl⟩
    · exact ⟨1, rfl, rfl⟩

/-- **Definition 7 across universes.** -/
public theorem crossUniverse_copies : Copies boolDev fin2Dev := by
  constructor
  · refine ⟨fun x => ⟨x.1, boolDev_realized x.1⟩, Equiv.refl Bool, ?_, ?_⟩
    · intro a b h
      exact Subtype.ext (congrArg (fun z : {x : Bool // boolDev.Realized x} => z.1) h)
    · intro x₂ y₂
      exact (fin2Dev_pairs x₂.1 y₂).trans (boolDev_pairs x₂.1 y₂).symm
  · refine ⟨fun x => ⟨x.1, fin2Dev_realized x.1⟩, Equiv.refl Bool, ?_, ?_⟩
    · intro a b h
      exact Subtype.ext (congrArg (fun z : {x : Bool // fin2Dev.Realized x} => z.1) h)
    · intro x₂ y₂
      exact (boolDev_pairs x₂.1 y₂).trans (fin2Dev_pairs x₂.1 y₂).symm

/-! ## 10. Section 8 has an inhabited model

Definitions 9–11 take a probability measure. This is one, so the stochastic layer
is not a set of formulas with no instance.
-/

/-- The uniform mass on a two-state universe. -/
@[expose] public noncomputable def uniformBool : FinPMF Bool where
  mass := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  sum_one := by simp

public theorem uniformBool_push_id (b : Bool) :
    pushOnImage uniformBool id b = 1 / 2 := by
  cases b <;> simp [pushOnImage, uniformBool] <;> decide

/-- Setup entropy of a device under a genuine PMF is nonnegative — the instance
behind `shannonEntropyOn_nonneg`. -/
public theorem uniformBool_setupEntropy_nonneg :
    0 ≤ setupEntropy boolDev uniformBool :=
  setupEntropy_nonneg boolDev uniformBool

/-! ## 11. Proposition 6 is not vacuous — the paper's own extremal example

The source's remark after Proposition 6: *"The maximum for `α = β = 1/2` can occur
in several ways. One is when `z₁ = 1`, and `z₂, z₃, z₄` all equal `0`. At these
values, both devices have an inference accuracy of `1/2` at inferring each other."*

That is this model. `U` is the four-point square with the uniform measure, so the
two setups `X₁ = fst` and `X₂ = snd` are independent and `α = β = 1/2`. Each cell
is a single universe, so each `zᵢ` is `0` or `1`; the conclusions are chosen to
agree exactly on `(false, false)`, giving `z = (1, 0, 0, 0)`.

Without this, `prop6_product_eq` would be a theorem whose hypothesis nothing is
known to satisfy.
-/

/-- `Y₁ = 1` exactly on the left column. -/
public abbrev p6dev1 : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := fun q => !q.1
  concl_surjective := fun
    | true => ⟨(false, false), rfl⟩
    | false => ⟨(true, false), rfl⟩

/-- `Y₂ = -1` exactly at `(false, true)`, so `Y₁ = Y₂` only at `(false, false)`. -/
public abbrev p6dev2 : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.snd
  concl := fun q => q.1 || !q.2
  concl_surjective := fun
    | true => ⟨(true, false), rfl⟩
    | false => ⟨(false, true), rfl⟩

/-- The uniform measure on the square. `X₁` and `X₂` are then independent, which
is what the source's step 2 needs. -/
@[expose] public noncomputable def p6pmf : FinPMF (Bool × Bool) where
  mass := fun _ => 1 / 4
  nonneg := fun _ => by norm_num
  sum_one := by simp

/-- The two setup bits are independent under the uniform measure. This is the
direct hypothesis used by Wolpert 2018's restatement of the bound. -/
public theorem p6_setups_independent :
    StatisticallyIndependent p6pmf p6dev1.setup p6dev2.setup := by
  have hff : (Finset.univ.filter (fun u : Bool × Bool => u = (false, false))).card = 1 := by decide
  have hft : (Finset.univ.filter (fun u : Bool × Bool => u = (false, true))).card = 1 := by decide
  have htf : (Finset.univ.filter (fun u : Bool × Bool => u = (true, false))).card = 1 := by decide
  have htt : (Finset.univ.filter (fun u : Bool × Bool => u = (true, true))).card = 1 := by decide
  have hf1 : (Finset.univ.filter (fun u : Bool × Bool => u.1 = false)).card = 2 := by decide
  have ht1 : (Finset.univ.filter (fun u : Bool × Bool => u.1 = true)).card = 2 := by decide
  have hf2 : (Finset.univ.filter (fun u : Bool × Bool => u.2 = false)).card = 2 := by decide
  have ht2 : (Finset.univ.filter (fun u : Bool × Bool => u.2 = true)).card = 2 := by decide
  intro x y
  cases x <;> cases y <;>
    norm_num [StatisticallyIndependent, pushOnImage, p6pmf, p6dev1, p6dev2,
      Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool,
      hff, hft, htf, htt, hf1, ht1, hf2, ht2]

public theorem p6dev1_mass_false : setupMass p6pmf p6dev1 false = 1 / 2 := by
  have h : (Finset.univ.filter (fun u : Bool × Bool => u.1 = false)).card = 2 := by decide
  norm_num [setupMass, pushOnImage, p6pmf, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_bool, h]

public theorem p6dev1_mass_true : setupMass p6pmf p6dev1 true = 1 / 2 := by
  have h : (Finset.univ.filter (fun u : Bool × Bool => u.1 = true)).card = 2 := by decide
  norm_num [setupMass, pushOnImage, p6pmf, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_bool, h]

public theorem p6dev2_mass_false : setupMass p6pmf p6dev2 false = 1 / 2 := by
  have h : (Finset.univ.filter (fun u : Bool × Bool => u.2 = false)).card = 2 := by decide
  norm_num [setupMass, pushOnImage, p6pmf, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_bool, h]

public theorem p6dev2_mass_true : setupMass p6pmf p6dev2 true = 1 / 2 := by
  have h : (Finset.univ.filter (fun u : Bool × Bool => u.2 = true)).card = 2 := by decide
  norm_num [setupMass, pushOnImage, p6pmf, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_bool, h]

/-- **`Prop6Law` is inhabited through the general independence bridge**, rather
than by checking its four fields independently. -/
public theorem p6_law : Prop6Law p6dev1 p6dev2 p6pmf false true false true := by
  apply prop6Law_of_independent p6pmf p6dev1 p6dev2
      ⟨(false, false), rfl⟩ ⟨(true, false), rfl⟩ (by decide)
      (fun w => by cases w.1 <;> simp)
  · rw [p6dev1_mass_false]; norm_num
  · rw [p6dev1_mass_true]; norm_num
  · exact ⟨(false, false), rfl⟩
  · exact ⟨(false, true), rfl⟩
  · decide
  · exact fun w => by cases w.2 <;> simp
  · rw [p6dev2_mass_false]; norm_num
  · rw [p6dev2_mass_true]; norm_num
  · exact p6_setups_independent

/-- **Proposition 6 at the paper's maximizer.** Both devices infer each other with
accuracy `1/2`, so the product is exactly the bound `1/4`. -/
public theorem p6_product_eq_quarter :
    inferenceAccuracy p6dev1 p6pmf p6dev2.concl *
      inferenceAccuracy p6dev2 p6pmf p6dev1.concl = 1 / 4 := by
  rw [prop6_product_eq p6dev1 p6dev2 p6pmf ⟨(false, false), rfl⟩ ⟨(true, false), rfl⟩
    (by decide) (fun w => by cases w.1 <;> simp)
    (by rw [p6dev1_mass_false]; norm_num)
    (by rw [p6dev1_mass_true]; norm_num)
    ⟨(false, false), rfl⟩ ⟨(false, true), rfl⟩ (by decide)
    (fun w => by cases w.2 <;> simp)
    (by rw [p6dev2_mass_false]; norm_num)
    (by rw [p6dev2_mass_true]; norm_num) p6_law]
  have c1 : (Finset.univ.filter (fun x : Bool × Bool => x.1 = false)).card = 2 := by decide
  have c3 : (Finset.univ.filter (fun x : Bool × Bool => x.2 = false)).card = 2 := by decide
  simp only [prop6Expr, Prop6Quadruple.k, Prop6Quadruple.m, Prop6Quadruple.n,
    prop6QuadrupleOf, cellAgreeProb, setupMass, pushOnImage, p6pmf, p6dev1, p6dev2]
  -- Split from one `norm_num` call: doing the rewriting and the arithmetic in a
  -- single pass now normalises the filters into a shape `c1`/`c3` do not match.
  simp only [Finset.sum_filter, Fintype.sum_prod_type, Fintype.sum_bool,
    Finset.filter_filter]
  norm_num [c1, c3]

/-! ### Proposition 6's *printed* premise, witnessed

`p6_law` witnesses `Prop6Law`, and `p6_setups_independent` witnesses independence.
Neither witnesses what Proposition 6 actually assumes: **mutual-information
distinguishability `1`**. Without that, `prop6_half_of_miDistinguishability_eq_one`
is a theorem whose hypothesis was never shown satisfiable.

The uniform square supplies it. Both setups are fair coins, so each carries
entropy `log 2`, and they are independent, so the mutual information vanishes and
the Definition 10 ratio is `1 − 0/(2 log 2) = 1`. -/

private theorem p6dev1_image :
    Finset.univ.image p6dev1.setup = {false, true} :=
  image_setup_eq_pair p6dev1 ⟨(false, false), rfl⟩ ⟨(true, false), rfl⟩
    (fun w => by cases h : w.1 <;> simp [p6dev1, h])

private theorem p6dev2_image :
    Finset.univ.image p6dev2.setup = {false, true} :=
  image_setup_eq_pair p6dev2 ⟨(false, false), rfl⟩ ⟨(false, true), rfl⟩
    (fun w => by cases h : w.2 <;> simp [p6dev2, h])

private theorem p6_entropy_dev1 : setupEntropy p6dev1 p6pmf = Real.log 2 := by
  unfold setupEntropy shannonEntropyOn
  rw [p6dev1_image, Finset.sum_insert (by simp), Finset.sum_singleton]
  rw [show pushOnImage p6pmf p6dev1.setup false = 1 / 2 from p6dev1_mass_false,
    show pushOnImage p6pmf p6dev1.setup true = 1 / 2 from p6dev1_mass_true]
  rw [if_neg (by norm_num : (1 : ℝ) / 2 ≠ 0)]
  have hlog : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

private theorem p6_entropy_dev2 : setupEntropy p6dev2 p6pmf = Real.log 2 := by
  unfold setupEntropy shannonEntropyOn
  rw [p6dev2_image, Finset.sum_insert (by simp), Finset.sum_singleton]
  rw [show pushOnImage p6pmf p6dev2.setup false = 1 / 2 from p6dev2_mass_false,
    show pushOnImage p6pmf p6dev2.setup true = 1 / 2 from p6dev2_mass_true]
  rw [if_neg (by norm_num : (1 : ℝ) / 2 ≠ 0)]
  have hlog : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

public theorem p6_entropy_pos :
    0 < setupEntropy p6dev1 p6pmf + setupEntropy p6dev2 p6pmf := by
  rw [p6_entropy_dev1, p6_entropy_dev2]
  have := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  linarith

/-- **Proposition 6's printed premise, witnessed.** The uniform square has
mutual-information distinguishability exactly `1`. -/
public theorem p6_miDistinguishability_eq_one :
    miDistinguishability p6dev1 p6dev2 p6pmf = 1 := by
  have hM : mutualInfo p6pmf p6dev1.setup p6dev2.setup = 0 :=
    (mutualInfo_eq_zero_iff p6pmf p6dev1.setup p6dev2.setup).mpr p6_setups_independent
  rw [miDistinguishability, if_neg (ne_of_gt p6_entropy_pos), hM, zero_div, sub_zero]

/-- **Proposition 6 on a witness, from the premise the paper prints.** Nothing is
assumed and nothing is vacuous: the hypothesis holds, and the bound is attained. -/
public theorem p6_half_from_printed_premise :
    inferenceAccuracy p6dev1 p6pmf p6dev2.concl *
      inferenceAccuracy p6dev2 p6pmf p6dev1.concl ≤ 1 / 4 :=
  prop6_half_of_miDistinguishability_eq_one p6dev1 p6dev2 p6pmf
    ⟨(false, false), rfl⟩ ⟨(true, false), rfl⟩ (by decide)
    (fun w => by cases h : w.1 <;> simp [p6dev1, h])
    ⟨(false, false), rfl⟩ ⟨(false, true), rfl⟩ (by decide)
    (fun w => by cases h : w.2 <;> simp [p6dev2, h])
    (by rw [setupMass]; exact p6dev1_mass_false)
    (by rw [setupMass]; exact p6dev2_mass_false)
    p6_entropy_pos p6_miDistinguishability_eq_one

/-! ## Section 9 — an infallible self-aware device

Before the witnesses below were added, the positive hypotheses of Theorem 6
were uninhabited. The only `SelfAwareDevice` then in the tree was
`uncorrectable`, constructed inside Proposition 7's proof, whose question
function is constant and which is **not** infallible. The examples below now
inhabit both halves of Theorem 6. They do not claim to inhabit every positive
hypothesis elsewhere in section 9.

`saU = 𝔹 × 𝔹`. The first bit names the question, the second is the fact asked about.
Question `true` asks *"is the second bit set?"*; question `false` asks its negation.
The device answers by evaluating its own question, so it is infallible by
construction, and its setup **is** its question, so it semi-controls it.
-/

/-- The universe of the section 9 witness. -/
public abbrev saU : Type := Bool × Bool

/-- Question `true` asks *"is the second bit set?"*; `false` asks the negation. -/
public abbrev saEval : Bool → saU → Bool := fun q u => if q then u.2 else !u.2

public abbrev saDevice : InferenceDevice saU where
  Setup := Bool
  setup := Prod.fst
  concl := fun u => saEval u.1 u
  concl_surjective := fun
    | true => ⟨(true, true), rfl⟩
    | false => ⟨(true, false), rfl⟩

/-- **Definition 12** inhabited: `Y ⊗ Q` hits all four pairs. -/
public abbrev saDev : SelfAwareDevice saU where
  toDevice := saDevice
  Question := Bool
  question := Prod.fst
  eval := saEval
  pair_surjective := by decide

/-- **Definition 13(ii)** inhabited: the conclusion *is* the answer to the
question being asked. -/
public theorem saDev_infallible : Infallible saDev := fun _ => rfl

/-- The setup and the question are the same function, so **Definition 8**'s
semi-control of `Q` holds. -/
public theorem saDev_semiControls_question :
    SemiControls saDev.toDevice saDev.question := by
  intro q hq
  obtain ⟨w, hw⟩ := hq
  exact ⟨q, ⟨w, hw⟩, fun _ h => h⟩

/-- **Definition 13(i)** inhabited: the second bit is intelligible to `saDev`,
because each of its two probes is a realized question. -/
public theorem saDev_intelligible_snd : Intelligible saDev (fun u : saU => u.2) := by
  intro γ f hf _
  have hf' : ∀ b : Bool, f b = decide (b = γ) := by
    intro b
    cases hb : f b with
    | true => simp [(hf b).1 hb]
    | false =>
      have hne : b ≠ γ := fun h => by rw [(hf b).2 h] at hb; exact Bool.noConfusion hb
      simp [hne]
  refine ⟨γ, ⟨(γ, false), rfl⟩, fun u => ?_⟩
  cases γ <;> cases hu : u.2 <;> simp [saEval, hf', hu]

/-- **Theorem 6(i)** on a witness: the hypotheses are all inhabited, so the
conclusion is a weak inference that actually holds. -/
public theorem saDev_weaklyInfers_snd :
    WeaklyInfers saDev.toDevice (fun u : saU => u.2) :=
  weaklyInfers_of_infallible_semiControls_question saDev saDev_infallible
    saDev_semiControls_question _ saDev_intelligible_snd

/-! ### Theorem 6(ii) — the stronger hypotheses are inhabited -/

/-- Identity setup makes each setup fibre a singleton, so it can semi-control the
question/setup pair used by Theorem 6(ii). -/
public abbrev saStrongDevice : InferenceDevice saU where
  Setup := saU
  setup := id
  concl := fun u => saEval u.1 u
  concl_surjective := fun
    | true => ⟨(true, true), rfl⟩
    | false => ⟨(true, false), rfl⟩

public abbrev saStrongDev : SelfAwareDevice saU where
  toDevice := saStrongDevice
  Question := Bool
  question := Prod.fst
  eval := saEval
  pair_surjective := by decide

/-- The target device exposes the second bit as both setup and conclusion. -/
public abbrev saTargetDevice : InferenceDevice saU where
  Setup := Bool
  setup := Prod.snd
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

public theorem saStrongDev_infallible : Infallible saStrongDev := fun _ => rfl

public theorem saStrongDev_semiControls_question_setup :
    SemiControls saStrongDev.toDevice
      (fun u => (saStrongDev.question u, saTargetDevice.setup u)) := by
  intro q hq
  obtain ⟨w, hw⟩ := hq
  exact ⟨q, ⟨q, rfl⟩, fun u hu => by simpa using hu⟩

public theorem saStrongDev_question_setup_surjective_on_images :
    ∀ (q : saStrongDev.Question) (x₂ : saTargetDevice.Setup),
      (∃ u, saStrongDev.question u = q) → saTargetDevice.Realized x₂ →
        ∃ u, saStrongDev.question u = q ∧ saTargetDevice.setup u = x₂ := by
  intro q x₂ _ _
  exact ⟨(q, x₂), rfl, rfl⟩

public theorem saStrongDev_intelligible_target :
    Intelligible saStrongDev saTargetDevice.concl := by
  intro γ f hf _
  have hf' : ∀ b : Bool, f b = decide (b = γ) := by
    intro b
    cases hb : f b with
    | true => simp [(hf b).1 hb]
    | false =>
      have hne : b ≠ γ := fun h => by rw [(hf b).2 h] at hb; exact Bool.noConfusion hb
      simp [hne]
  refine ⟨γ, ⟨(γ, false), rfl⟩, fun u => ?_⟩
  cases γ <;> cases hu : u.2 <;> simp [saEval, hf', hu]

/-- **Theorem 6(ii)** on a concrete model: all its positive hypotheses hold and
the strong-inference conclusion is therefore non-vacuous. -/
public theorem saStrongDev_stronglyInfers_target :
    StronglyInfers saStrongDev.toDevice saTargetDevice :=
  stronglyInfers_of_infallible_semiControls_question_setup saStrongDev
    saStrongDev_infallible saStrongDev_semiControls_question_setup
    saStrongDev_question_setup_surjective_on_images saStrongDev_intelligible_target

/-! ## Proposition 3(ii)'s hypothesis, inhabited

`not_mutually_distinguishable_weak_cycle` derives a contradiction from mutual
distinguishability plus a weak-inference cycle. If no reality were mutually
distinguishable the theorem would hold for nothing, so the hypothesis needs a
model of its own — separately from the cycle, which the theorem refutes.

The uniform square is one: the two setups are the two coordinates, so **every**
pair of setup values is realized, by the state that has them. -/

public abbrev mutualReality : DeviceReality (Bool × Bool) 2
  | ⟨0, _⟩ => p6dev1
  | ⟨1, _⟩ => p6dev2

public theorem mutualReality_mutuallyDistinguishable :
    MutuallyDistinguishable mutualReality := by
  intro x _
  exact ⟨(x 0, x 1), fun i => by fin_cases i <;> rfl⟩

/-- Each device in it is therefore outside distinguishable — the paper's *"free
will"* reading, that the others' setups do not restrict this one's. -/
public theorem mutualReality_outsideDistinguishable (i : Fin 2) :
    OutsideDistinguishable mutualReality i :=
  outsideDistinguishable_of_mutuallyDistinguishable
    mutualReality_mutuallyDistinguishable i

/-! ## Proposition 4's hypotheses, inhabited

`unique_strong_root` asks for a weakly connected strong-inference graph whose
incomparable pairs are distinguishable, every device carrying two realized setup
values. Nothing satisfied that, so the unique root was a root of nothing.

Two devices suffice, and one strong-inference edge is already here:
`fineDevice ≫ coarseForcedDevice`. Connectivity is that single edge, and the
distinguishability clause is **vacuous** — it constrains only pairs that are
incomparable, and these two are comparable. -/

public abbrev prop4Reality : DeviceReality (Fin 4) 2
  | ⟨0, _⟩ => fineDevice
  | ⟨1, _⟩ => coarseForcedDevice

public theorem prop4Reality_connected : StrongGraphWeaklyConnected prop4Reality := by
  intro i j
  have hedge : StrongEdge prop4Reality 0 1 :=
    Or.inl (show StronglyInfers fineDevice coarseForcedDevice from fine_stronglyInfers_coarse)
  have hedge' : StrongEdge prop4Reality 1 0 :=
    Or.inr (show StronglyInfers fineDevice coarseForcedDevice from fine_stronglyInfers_coarse)
  fin_cases i <;> fin_cases j
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single hedge
  · exact Relation.ReflTransGen.single hedge'
  · exact Relation.ReflTransGen.refl

public theorem prop4Reality_two_setups : ∀ i : Fin 2, ∃ a b : (prop4Reality i).Setup,
    a ≠ b ∧ (prop4Reality i).Realized a ∧ (prop4Reality i).Realized b := by
  intro i
  fin_cases i
  · exact ⟨(0 : Fin 4), (1 : Fin 4), by decide, ⟨0, rfl⟩, ⟨1, rfl⟩⟩
  · exact ⟨false, true, by decide, ⟨0, rfl⟩, ⟨2, rfl⟩⟩

/-- **Proposition 4 on a witness.** All three hypotheses hold, so the unique root
is the root of something. -/
public theorem prop4_nonvacuous : ∃! r : Fin 2, IsStrongRoot prop4Reality r :=
  unique_strong_root prop4Reality prop4Reality_connected
    (fun i j hij hnot hnot' => by
      fin_cases i <;> fin_cases j
      · exact absurd rfl hij
      · exact absurd fine_stronglyInfers_coarse hnot
      · exact absurd fine_stronglyInfers_coarse hnot'
      · exact absurd rfl hij)
    prop4Reality_two_setups

/-! ## Theorem 7's hypotheses, inhabited

Theorem 7 asks for a pair of self-aware devices, each finding the other's `P` map
intelligible. Nothing satisfied that either, and it was not obvious that anything
could: Corollary 4 forbids mutual *device*-intelligibility whenever the question
ranges are finite, and this premise is adjacent to it.

It is satisfiable, and the reason Corollary 4 does not block it is that
intelligibility here is of the **question map alone**, not of the pair `(Y, Q)`.
A device with a single constantly-true question finds any single-valued map
intelligible, because the only probe of a one-point range is the constant `true`.

This witness is degenerate: `|Q(U)| = 1`. A non-degenerate one follows it below —
`saSelfProbe`, whose questions are the probes of its own question map, so
`|Q(U)| = 2`. It was reached by taking the condition this note stated as the
obstacle (*"would have to ask, as one of its own questions, every probe of the
other's question map"*) and building the device that satisfies it. -/

public abbrev saTrivialDevice : InferenceDevice saU where
  Setup := Bool
  setup := Prod.fst
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

/-- A Definition-12 device whose single question is constantly true. -/
public abbrev saTrivial : SelfAwareDevice saU where
  toDevice := saTrivialDevice
  Question := PUnit
  question := fun _ => PUnit.unit
  eval := fun _ _ => true
  pair_surjective := by
    rintro ⟨b, ⟨⟩⟩
    exact ⟨(false, b), rfl⟩

/-- The only probe of a one-point range is the constant `true`, so every
single-valued map is intelligible to `saTrivial`. -/
public theorem saTrivial_intelligible_question :
    Intelligible saTrivial saTrivial.question := by
  intro γ f hf _
  refine ⟨PUnit.unit, ⟨(false, false), rfl⟩, fun u => ?_⟩
  have : f PUnit.unit = true := (hf PUnit.unit).mpr (by cases γ; rfl)
  simpa [saTrivial] using this.symm

/-- **Theorem 7(i) on a witness.** Its mutual-intelligibility premise is
satisfiable, so the cardinality equality is not vacuous. -/
public theorem thm7_nonvacuous :
    Fintype.card {x // ∃ u, saTrivial.question u = x} =
        Fintype.card {x // ∃ u, saTrivial.question u = x} ∧
      Fintype.card {x // ∃ u, saTrivial.question u = x} =
        Fintype.card {x // ∃ u, saTrivial.question u = x} ∧
      Fintype.card {x // ∃ u, saTrivial.question u = x} =
        Fintype.card {x // ∃ u, saTrivial.question u = x} :=
  thm7_card saTrivial saTrivial saTrivial.question saTrivial.question id id
    (fun _ => rfl) (fun _ => rfl)
    saTrivial_intelligible_question saTrivial_intelligible_question

/-! ## A non-degenerate Theorem 7 witness, and the section-9 prose definitions

The paragraph above left one thing open: whether Theorem 7's mutual-intelligibility
premise can be met with more than one question. It can, and the device that meets
it is exactly the one the previous note described — *"a device whose question range
has two or more values would have to ask, as one of its own questions, every probe
of the other's question map"*. Make the two devices the same one, and make its
questions the probes of its own question function.

`saSelfProbe` asks, at question `q`, *"is my question `q`?"* — `eval q u =
⟦Q(u) = q⟧`. Then `eval q` **is** the probe of `Q` at `q`, so `Q` is intelligible
to it, and `Q` takes two values. `|Q(U)| = 2`, against `saTrivial`'s `1`.

The same device settles three prose items at once. Its conclusion is the second
bit while its own question is always answered `true`, so it is fallible
everywhere, and `Y Q̄` — the source's `agreesWithQuestion` — is the second bit.
That is a function `saDev` finds intelligible, so footnote 9's alternative
correction relation `CorrectsAlt` holds between them. -/

public abbrev saSelfProbeDevice : InferenceDevice saU where
  Setup := Bool
  setup := Prod.fst
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

/-- Its questions are the probes of its own question function: `q(u) = ⟦Q(u) = q⟧`. -/
public abbrev saSelfProbe : SelfAwareDevice saU where
  toDevice := saSelfProbeDevice
  Question := Bool
  question := Prod.fst
  eval := fun q u => decide (u.1 = q)
  pair_surjective := by decide

/-- **The premise of Theorem 7, met non-degenerately.** Each question of
`saSelfProbe` is a probe of its own question map, so that map is intelligible to
it — with a two-valued question range, not `saTrivial`'s one. -/
public theorem saSelfProbe_intelligible_question :
    Intelligible saSelfProbe saSelfProbe.question := by
  intro γ f hf _
  have hf' : ∀ b : Bool, f b = decide (b = γ) := by
    intro b
    cases hb : f b with
    | true => simp [(hf b).1 hb]
    | false =>
      have hne : b ≠ γ := fun h => by rw [(hf b).2 h] at hb; exact Bool.noConfusion hb
      simp [hne]
  exact ⟨γ, ⟨(γ, false), rfl⟩, fun u => by simp [hf']⟩

/-- Both question values are realized, so the witness really is two-valued. -/
public theorem saSelfProbe_questions_card :
    Fintype.card {x // ∃ u, saSelfProbe.question u = x} = 2 := by
  classical
  rw [Fintype.card_congr
    (Equiv.subtypeUnivEquiv (fun b : Bool => ⟨((b, false) : saU), rfl⟩))]
  rfl

/-- **Theorem 7(i) on a non-degenerate witness.** -/
public theorem thm7_nonvacuous_two_questions :
    Fintype.card {x // ∃ u, saSelfProbe.question u = x} =
        Fintype.card {x // ∃ u, saSelfProbe.question u = x} ∧
      Fintype.card {x // ∃ u, saSelfProbe.question u = x} =
        Fintype.card {x // ∃ u, saSelfProbe.question u = x} ∧
      Fintype.card {x // ∃ u, saSelfProbe.question u = x} =
        Fintype.card {x // ∃ u, saSelfProbe.question u = x} :=
  thm7_card saSelfProbe saSelfProbe saSelfProbe.question saSelfProbe.question id id
    (fun _ => rfl) (fun _ => rfl)
    saSelfProbe_intelligible_question saSelfProbe_intelligible_question

/-- **Theorem 7(i) without finiteness, on the same witness.** `thm7_mk` states the
printed unrestricted cardinality equality; nothing had instantiated it. -/
public theorem thm7_mk_nonvacuous :
    Cardinal.mk {x // ∃ u, saSelfProbe.question u = x} =
        Cardinal.mk {x // ∃ u, saSelfProbe.question u = x} ∧
      Cardinal.mk {x // ∃ u, saSelfProbe.question u = x} =
        Cardinal.mk {x // ∃ u, saSelfProbe.question u = x} ∧
      Cardinal.mk {x // ∃ u, saSelfProbe.question u = x} =
        Cardinal.mk {x // ∃ u, saSelfProbe.question u = x} :=
  thm7_mk saSelfProbe saSelfProbe saSelfProbe.question saSelfProbe.question id id
    (fun _ => rfl) (fun _ => rfl)
    saSelfProbe_intelligible_question saSelfProbe_intelligible_question

/-- It answers its own question `true` everywhere while concluding the second bit,
so **Definition 13(ii) fails for it** — the contrast `saDev` alone cannot provide. -/
public theorem saSelfProbe_not_infallible : ¬ Infallible saSelfProbe := by
  intro h
  have := h (false, false)
  revert this
  decide

/-- **The source's `Y₂ Q̄₂`, computed.** It is the second bit. -/
public theorem agreesWithQuestion_saSelfProbe :
    agreesWithQuestion saSelfProbe = fun u : saU => u.2 := by
  funext u
  simp [agreesWithQuestion, SelfAwareDevice.ask]

/-- **Footnote 9's alternative correction relation, on a witness.** `saDev` is
infallible, so the second of its two conditions is free, and the first is
`saDev_intelligible_snd`. -/
public theorem saDev_correctsAlt_saSelfProbe : CorrectsAlt saDev saSelfProbe := by
  refine (correctsAlt_iff_intelligible_of_infallible saDev_infallible).mpr ?_
  rw [agreesWithQuestion_saSelfProbe]
  exact saDev_intelligible_snd

/-- **Definition 14 itself, positively.** Until this, the only fact about
`Corrects` in the tree was Proposition 7's `exists_not_corrects` — a device that
*cannot* be corrected. A relation with only a negative result behind it is
consistent with holding of nothing at all.

`saDev`'s question-`true` fibre reports the second bit, which is exactly
`Y₂ Q̄₂` for `saSelfProbe`. The same pair therefore satisfies Definition 14 and
footnote 9's variant; that is two definitions witnessed on one model, and **not**
a claim that either implies the other. -/
public theorem saDev_corrects_saSelfProbe : Corrects saDev.toDevice saSelfProbe := by
  refine ⟨true, ⟨(true, false), rfl⟩, fun w hw => ?_⟩
  show saEval w.1 w = agreesWithQuestion saSelfProbe w
  have h1 : w.1 = true := hw
  rw [agreesWithQuestion_saSelfProbe]
  simp [saEval, h1]

/-- **Theorem 7(ii) on the non-degenerate witness.** All four printed equalities,
with the finiteness the source's (ii) carries. `thm7_ii_chain` had no instance. -/
public theorem thm7_ii_nonvacuous :
    evalImage saSelfProbe = probeImage saSelfProbe.question ∧
      probeImage saSelfProbe.question = probeImage saSelfProbe.question ∧
        evalImage saSelfProbe = probeImage saSelfProbe.question ∧
          probeImage saSelfProbe.question = probeImage saSelfProbe.question := by
  classical
  exact thm7_ii_chain saSelfProbe saSelfProbe saSelfProbe.question saSelfProbe.question
    id id (fun _ => rfl) (fun _ => rfl)
    saSelfProbe_intelligible_question saSelfProbe_intelligible_question

/-! ### `InfallibleFor` is strictly between nothing and `Infallible`

The relativized clause would be idle vocabulary if every device that satisfied it
on a nonempty question set were infallible outright. `saPartial` answers question
`true` correctly and question `false` backwards, so it is infallible for `{true}`
and not infallible. -/

public abbrev saPartialDevice : InferenceDevice saU where
  Setup := Bool
  setup := Prod.fst
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

public abbrev saPartial : SelfAwareDevice saU where
  toDevice := saPartialDevice
  Question := Bool
  question := Prod.fst
  eval := saEval
  pair_surjective := by decide

public theorem saPartial_infallibleFor_true :
    InfallibleFor saPartial ({true} : Set Bool) := by
  rintro q rfl u _
  rfl

public theorem saPartial_not_infallible : ¬ Infallible saPartial := by
  intro h
  have := h (false, true)
  revert this
  decide

/-! ## Definition 11, computed

`countingDistinguishability` had no worked instance — a gap the module-level
coverage gate cannot see, since `Stochastic.lean` has other coverage, and one the
declaration dependency view surfaced as a definition no statement and no example
mentions.

On the uniform square every pair of setup values is jointly realized, so the
fraction of unrealized pairs is `0`. That is the same fact
`mutualReality_mutuallyDistinguishable` records qualitatively, now as Definition
11's number. -/

public theorem p6_countingDistinguishability_eq_zero :
    countingDistinguishability p6dev1 p6dev2 = 0 := by
  classical
  have hall : ((Finset.univ.image p6dev1.setup ×ˢ Finset.univ.image p6dev2.setup).filter
      (fun q => ∃ w, p6dev1.setup w = q.1 ∧ p6dev2.setup w = q.2))
      = Finset.univ.image p6dev1.setup ×ˢ Finset.univ.image p6dev2.setup := by
    refine Finset.filter_true_of_mem (fun q _ => ⟨(q.1, q.2), rfl, rfl⟩)
  have h1 : Finset.univ.image p6dev1.setup = (Finset.univ : Finset Bool) := by decide
  have h2 : Finset.univ.image p6dev2.setup = (Finset.univ : Finset Bool) := by decide
  unfold countingDistinguishability
  simp only [hall, h1, h2, Finset.card_product, Finset.card_univ, Fintype.card_bool]
  norm_num

/-! ## The `|U| > 3` sentence — hypotheses inhabited

A one-device reality whose extra-function family is that device's own
conclusion. `func_two` holds by surjectivity onto `Bool` — the honesty check
the repaired row needs — and the device is then not universal, on any `U`.
-/

public def conclInFamilyReality :
    FullReality Bool (fun _ : Unit => Bool) (fun _ : Unit => Bool) where
  setupOf := fun _ => id
  conclOf := fun _ => id
  funcOf := fun _ => id

public theorem conclInFamilyReality_surj :
    ∀ α : Unit, Function.Surjective (conclInFamilyReality.conclOf α) :=
  fun _ => Function.surjective_id

public theorem conclInFamilyReality_func_two :
    ∃ u u' : Bool, conclInFamilyReality.funcOf () u ≠
      conclInFamilyReality.funcOf () u' :=
  conclInFamilyReality.func_two_of_concl_mem (α := ()) (β := ())
    conclInFamilyReality_surj rfl

public theorem conclInFamilyReality_not_universal :
    ¬ conclInFamilyReality.IsUniversalFull conclInFamilyReality_surj () :=
  conclInFamilyReality.not_isUniversalFull_of_concl_mem (α := ()) (β := ())
    conclInFamilyReality_surj rfl

end AISafetyAtlas.Examples.Inference.Device
