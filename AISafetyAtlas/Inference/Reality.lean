module

public import AISafetyAtlas.Inference.Device
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Finset.Max
public import Mathlib.Logic.Equiv.Defs
public import Mathlib.Logic.Relation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith

/-!
# Realities and copies — Wolpert 2008 §6

A *reality* is a universe together with a family of devices and a family of
arbitrary functions over it.

* **Definition 7** is mimicry and copies, `Mimics` / `Copies`, stated across two
  universes as the source requires.
* **Lemma 1** is `lemma1_reducedForm_iff_admissible`: the reduced forms of
  realities are exactly the admissible tuple families, `K₁ = K₂`.
* **Propositions 3–5** are the graph constraints: a pairwise-distinguishable
  weak-inference 3-cycle exists; a mutually distinguishable weak-inference cycle
  does not; a strong-inference cycle does not; copies may one-way weakly infer
  (finite) and may strongly infer only if infinite.

`DeviceReality` — used by Propositions 3 and 4 — is a **finite** family
`Fin n → InferenceDevice` over one universe. Each device may have a different
setup type, and those types are universe-polymorphic. The
source's reality may be countably infinite and carries the extra functions
`{Γ_β}`; those live in `FullReality`, which Lemma 1 uses. Propositions 3 and 4 are
therefore finite-subgraph statements, which is what their conclusions need.

**Proposition 3(ii).** The source defines *"mutually (setup) distinguishable"* in
prose just before Proposition 3: *"the reality as a whole is mutually (setup)
distinguishable iff `∀ x₁ ∈ X₁(U), x₂ ∈ X₂(U), … ∃ u ∈ U` s.t.
`X₁(u) = x₁, X₂(u) = x₂, …`"*. That is `n`-wise joint realizability, which is
`MutuallyDistinguishable` verbatim, and is strictly stronger than the pairwise
distinguishability of Definition 4 — as it must be, since Proposition 3(i) exhibits
a *pairwise*-distinguishable weak cycle.
-/

namespace AISafetyAtlas.Inference

universe u v

variable {U : Type u}

/-- A finite family of devices over one universe; setup types may differ. -/
@[expose] public def DeviceReality (U : Type u) (n : ℕ) : Type _ :=
  Fin n → InferenceDevice.{u, v} U

/-- Pairwise setup-distinguishability. -/
@[expose] public def PairwiseDistinguishable {n : ℕ} (R : DeviceReality U n) : Prop :=
  ∀ i j : Fin n, i ≠ j → Distinguishable (R i) (R j)

/-- Mutual setup-distinguishability: every tuple of realized setups is
jointly realized. -/
@[expose] public def MutuallyDistinguishable {n : ℕ} (R : DeviceReality U n) : Prop :=
  ∀ x : (i : Fin n) → (R i).Setup,
    (∀ i, (R i).Realized (x i)) →
      ∃ w : U, ∀ i, (R i).setup w = x i

/-- Successor on `Fin n`, wrapping. Needs `n ≠ 0`. -/
public def finSuccMod {n : ℕ} [NeZero n] (i : Fin n) : Fin n := i + 1

/-- Directed weak-inference edges `R i > R (i+1)`, wrapping. -/
@[expose] public def WeakInferenceCycle {n : ℕ} [NeZero n]
    (R : DeviceReality U n) : Prop :=
  ∀ i : Fin n, InfersDevice (R i) (R (finSuccMod i))

/-- Directed strong-inference edges, wrapping. -/
@[expose] public def StrongInferenceCycle {n : ℕ} [NeZero n]
    (R : DeviceReality U n) : Prop :=
  ∀ i : Fin n, StronglyInfers (R i) (R (finSuccMod i))

/-- **Outside distinguishability**, defined in §6's running prose rather than in a
numbered environment:

> *"a device `(Xᵢ, Yᵢ)` in that reality is **outside distinguishable** iff
> `∀xᵢ ∈ Xᵢ(U)` and all `x′₋ᵢ` in the range of `⊗_{j≠i} Xⱼ`, there is a `u ∈ U`
> such that simultaneously `Xᵢ(u) = xᵢ` and `Xⱼ(u) = x′ⱼ ∀j ≠ i`."*

The tuple `x′₋ᵢ` ranges over the **image** of the joint map of the other devices,
so it is written here as the values those devices take at some state `w`.

The paper reads this as free will: *"the way the other devices are setup does not
restrict how `C` can be setup"*, and Theorem 1 then says two devices that both have
it cannot observe each other with guaranteed accuracy. -/
@[expose] public def OutsideDistinguishable {n : ℕ} (R : DeviceReality U n)
    (i : Fin n) : Prop :=
  ∀ xᵢ : (R i).Setup, (R i).Realized xᵢ → ∀ w : U,
    ∃ u : U, (R i).setup u = xᵢ ∧ ∀ j : Fin n, j ≠ i → (R j).setup u = (R j).setup w

/-- Mutual distinguishability of a reality makes every device in it outside
distinguishable: fix the others at whatever `w` gives them, and vary the one. -/
public theorem outsideDistinguishable_of_mutuallyDistinguishable {n : ℕ}
    {R : DeviceReality U n} (h : MutuallyDistinguishable R) (i : Fin n) :
    OutsideDistinguishable R i := by
  classical
  intro xᵢ hxᵢ w
  obtain ⟨u, hu⟩ := h (fun j => if hj : j = i then hj ▸ xᵢ else (R j).setup w)
    (fun j => by
      by_cases hj : j = i
      · subst hj; simpa using hxᵢ
      · simp only [dif_neg hj]; exact ⟨w, rfl⟩)
  refine ⟨u, ?_, fun j hj => ?_⟩
  · simpa using hu i
  · have := hu j
    simpa [dif_neg hj] using this

/-! ## Proposition 3(i) — a pairwise-distinguishable 3-cycle

Three devices on `Fin 4` whose setups are the three nontrivial linear
partitions of the square (pairwise independent, so distinguishable).
Each conclusion is a cyclic shift of those partitions: one fibre answers
the identity probe of the next device, the other answers negation.
-/

/-- One row of the 3-cycle: `(Xᵢ, Yᵢ)` for `i = 1,2,3`. -/
public structure Cycle3Row where
  x1 : Bool
  y1 : Bool
  x2 : Bool
  y2 : Bool
  x3 : Bool
  y3 : Bool

/-- Universes `0,1,2,3` as the four corners of the square. -/
public def cycle3Table : Fin 4 → Cycle3Row
  | 0 => { x1 := false, y1 := false, x2 := false, y2 := false, x3 := false, y3 := false }
  | 1 => { x1 := false, y1 := true,  x2 := true,  y2 := true,  x3 := true,  y3 := false }
  | 2 => { x1 := true,  y1 := false, x2 := false, y2 := true,  x3 := true,  y3 := true }
  | 3 => { x1 := true,  y1 := true,  x2 := true,  y2 := false, x3 := false, y3 := true }

public def cycle3device1 : InferenceDevice (Fin 4) where
  Setup := Bool
  setup := fun u => (cycle3Table u).x1
  concl := fun u => (cycle3Table u).y1
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨1, rfl⟩

public def cycle3device2 : InferenceDevice (Fin 4) where
  Setup := Bool
  setup := fun u => (cycle3Table u).x2
  concl := fun u => (cycle3Table u).y2
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨1, rfl⟩

public def cycle3device3 : InferenceDevice (Fin 4) where
  Setup := Bool
  setup := fun u => (cycle3Table u).x3
  concl := fun u => (cycle3Table u).y3
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨2, rfl⟩

public theorem cycle3_infers_12 : InfersDevice cycle3device1 cycle3device2 := by
  intro γ f hf _
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨false, ⟨0, rfl⟩, ?_⟩
    intro w hw; fin_cases w <;> cases hw <;> rfl
  · refine ⟨true, ⟨2, rfl⟩, ?_⟩
    intro w hw; fin_cases w <;> cases hw <;> rfl

public theorem cycle3_infers_23 : InfersDevice cycle3device2 cycle3device3 := by
  intro γ f hf _
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨false, ⟨0, rfl⟩, ?_⟩
    intro w hw; fin_cases w <;> cases hw <;> rfl
  · refine ⟨true, ⟨1, rfl⟩, ?_⟩
    intro w hw; fin_cases w <;> cases hw <;> rfl

public theorem cycle3_infers_31 : InfersDevice cycle3device3 cycle3device1 := by
  intro γ f hf _
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨false, ⟨0, rfl⟩, ?_⟩
    intro w hw; fin_cases w <;> cases hw <;> rfl
  · refine ⟨true, ⟨1, rfl⟩, ?_⟩
    intro w hw; fin_cases w <;> cases hw <;> rfl

public theorem cycle3_dist_12 : Distinguishable cycle3device1 cycle3device2 := by
  intro x₁ _ x₂ _
  cases x₁ <;> cases x₂
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩
  · exact ⟨3, rfl, rfl⟩

public theorem cycle3_dist_13 : Distinguishable cycle3device1 cycle3device3 := by
  intro x₁ _ x₂ _
  cases x₁ <;> cases x₂
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨3, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩

public theorem cycle3_dist_23 : Distinguishable cycle3device2 cycle3device3 := by
  intro x₁ _ x₂ _
  cases x₁ <;> cases x₂
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩
  · exact ⟨3, rfl, rfl⟩
  · exact ⟨1, rfl, rfl⟩

public def cycle3Reality : DeviceReality (Fin 4) 3
  | ⟨0, _⟩ => cycle3device1
  | ⟨1, _⟩ => cycle3device2
  | ⟨2, _⟩ => cycle3device3

/-- **Proposition 3(i).** -/
public theorem exists_pairwise_distinguishable_weak_cycle :
    ∃ R : DeviceReality.{0, 0} (Fin 4) 3,
      PairwiseDistinguishable R ∧ WeakInferenceCycle R := by
  refine ⟨cycle3Reality, ?_, ?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · exact cycle3_dist_12
    · exact cycle3_dist_13
    · exact cycle3_dist_12.symm
    · exact (hij rfl).elim
    · exact cycle3_dist_23
    · exact cycle3_dist_13.symm
    · exact cycle3_dist_23.symm
    · exact (hij rfl).elim
  · intro i
    fin_cases i
    · exact cycle3_infers_12
    · exact cycle3_infers_23
    · exact cycle3_infers_31

/-! ## Proposition 3(ii)–(iii) -/

/-- Identity probes around the cycle except the last step, which uses negation. -/
public theorem not_mutually_distinguishable_weak_cycle
    {n : ℕ} [NeZero n] (R : DeviceReality U n)
    (hmut : MutuallyDistinguishable R) (hcyc : WeakInferenceCycle R) : False := by
  have hx : ∀ i : Fin n, ∃ x : (R i).Setup, (R i).Realized x ∧
      ∀ w, (R i).setup w = x →
        (R i).concl w =
          if (i : ℕ) + 1 = n then !((R (finSuccMod i)).concl w)
          else (R (finSuccMod i)).concl w := by
    intro i
    by_cases h : (i : ℕ) + 1 = n
    · obtain ⟨wf, hwf⟩ := (R (finSuccMod i)).concl_surjective false
      obtain ⟨x, hx, hfib⟩ := hcyc i false (fun b => !b) isProbe_not ⟨wf, hwf⟩
      exact ⟨x, hx, fun w hw => by simp [h, hfib w hw]⟩
    · obtain ⟨wt, hwt⟩ := (R (finSuccMod i)).concl_surjective true
      obtain ⟨x, hx, hfib⟩ := hcyc i true id isProbe_id ⟨wt, hwt⟩
      exact ⟨x, hx, fun w hw => by simp [h, hfib w hw]⟩
  choose x hxR hfib using hx
  obtain ⟨w, hw⟩ := hmut x hxR
  -- walk equalities up to the last vertex, then negate
  have hn : 0 < n := Nat.pos_of_neZero n
  have heq : ∀ k : ℕ, (hk : k + 1 < n) →
      (R ⟨k, Nat.lt_trans (Nat.lt_succ_self k) hk⟩).concl w =
        (R ⟨k + 1, hk⟩).concl w := by
    intro k hk
    have hik : k < n := Nat.lt_trans (Nat.lt_succ_self k) hk
    have hne : ((⟨k, hik⟩ : Fin n) : ℕ) + 1 ≠ n := by
      simp; exact Nat.ne_of_lt hk
    have hidx : finSuccMod (⟨k, hik⟩ : Fin n) = ⟨k + 1, hk⟩ := by
      simp [finSuccMod]
      ext
      simp [Fin.val_add]
      have : k + 1 < n := hk
      rw [Nat.mod_eq_of_lt this]
    have := hfib ⟨k, hik⟩ w (hw _)
    simpa [hne, hidx] using this
  have hwalk : ∀ k : ℕ, (hk : k < n) →
      (R ⟨0, hn⟩).concl w = (R ⟨k, hk⟩).concl w := by
    intro k hk
    induction k with
    | zero => rfl
    | succ k ih => exact (ih (Nat.lt_of_succ_lt hk)).trans (heq k hk)
  have hn1 : n - 1 < n := Nat.sub_one_lt_of_lt hn
  have hlast : ((⟨n - 1, hn1⟩ : Fin n) : ℕ) + 1 = n := by
    simp; exact Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
  have hidx0 : finSuccMod (⟨n - 1, hn1⟩ : Fin n) = ⟨0, hn⟩ := by
    simp [finSuccMod]
    ext
    simp [Fin.val_add]
    have : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.succ_le_of_lt hn)
    simp [this]
  have hneg : (R ⟨n - 1, hn1⟩).concl w = !((R ⟨0, hn⟩).concl w) := by
    simpa [hlast, hidx0] using hfib ⟨n - 1, hn1⟩ w (hw _)
  exact Bool.not_ne_self ((R ⟨0, hn⟩).concl w)
    ((hwalk (n - 1) hn1).trans hneg).symm

public theorem val_finSuccMod {n : ℕ} [NeZero n] (i : Fin n) :
    (finSuccMod i).val = (i.val + 1) % n := by
  simp [finSuccMod, Fin.val_add]

public theorem add_one_mod (a n : ℕ) (_hn : 0 < n) :
    (a % n + 1) % n = (a + 1) % n :=
  Nat.mod_add_mod a n 1

public theorem val_iterate_finSuccMod {n : ℕ} [NeZero n] (i : Fin n) (k : ℕ) :
    (finSuccMod^[k] i).val = (i.val + k) % n := by
  induction k with
  | zero => simp [Nat.mod_eq_of_lt i.isLt]
  | succ k ih =>
    rw [Function.iterate_succ_apply', val_finSuccMod, ih,
      add_one_mod _ n (Nat.pos_of_neZero n), Nat.add_assoc]

public theorem finSuccMod_iterate_n {n : ℕ} [NeZero n] (i : Fin n) :
    finSuccMod^[n] i = i := by
  ext
  rw [val_iterate_finSuccMod, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]

/-- `k+1` strong-inference steps from `start`. -/
public theorem stronglyInfers_walk {n : ℕ} [NeZero n] (R : DeviceReality U n)
    (hcyc : StrongInferenceCycle R) (start : Fin n) :
    ∀ k : ℕ, StronglyInfers (R start) (R (finSuccMod^[k + 1] start)) := by
  intro k
  induction k with
  | zero => simpa [finSuccMod] using hcyc start
  | succ k ih =>
    simpa [Function.iterate_succ_apply'] using
      stronglyInfers_trans ih (hcyc (finSuccMod^[k + 1] start))

/-- **Proposition 3(iii).** No strong-inference cycle. -/
public theorem not_strong_inference_cycle {n : ℕ} [NeZero n]
    (R : DeviceReality U n) (hcyc : StrongInferenceCycle R) : False := by
  let start : Fin n := ⟨0, Nat.pos_of_neZero n⟩
  have hself : StronglyInfers (R start) (R (finSuccMod^[n] start)) := by
    have hwalk := stronglyInfers_walk R hcyc start (n - 1)
    have hn : n - 1 + 1 = n :=
      Nat.sub_add_cancel (Nat.succ_le_of_lt (Nat.pos_of_neZero n))
    simpa [hn] using hwalk
  rw [finSuccMod_iterate_n start] at hself
  exact not_stronglyInfers_self (R start) hself

/-! ## Definition 7 — mimicry and copies -/

/-- Realized `(X, Y)` pairs. -/
@[expose] public def realizedPairs (C : InferenceDevice.{u, v} U) :
    Set (C.Setup × Bool) :=
  {p | ∃ w, C.setup w = p.1 ∧ C.concl w = p.2}

/--
**Definition 7.** `C₁` mimics `C₂`.

*"Let `U` and `Û` be two (perhaps identical) sets. Let `C₁` be a device in a
reality with domain `U` … let `R₂` be the relation between `X₂` and `Y₂` for some
separate device `C₂` in the reduced form of a reality having domain `Û`. Then
`C₁` mimics `C₂` iff there is an injection `ρ_X : X₂(Û) → X₁(U)` and a bijection
`ρ_Y : Y₂(Û) ↔ Y₁(U)` such that `∀ x₂, y₂`, `x₂ R₂ y₂ ⇔ ρ_X(x₂) R₁ ρ_Y(y₂)`."*

The two universes are **kept distinct**, as the source's opening sentence
requires: a device may be a copy of a device in another reality. `ρ_Y` is
`Bool ≃ Bool` because Definition 1 forces `Y₁(U) = Y₂(Û) = 𝔹`. `ρ_X` is
deliberately **not** surjective — the source notes that this is what lets one
device mimic several others.

`realizedPairs` is the single-device reduced-form relation: `(x, y)` is in it
exactly when some universe realizes both.
-/
@[expose] public def Mimics {Û : Type u'} (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u', v'} Û) : Prop :=
  ∃ (ρX : {x // C₂.Realized x} → {x // C₁.Realized x}) (ρY : Bool ≃ Bool),
    Function.Injective ρX ∧
      ∀ (x₂ : {x // C₂.Realized x}) (y₂ : Bool),
        ((x₂.1, y₂) ∈ realizedPairs C₂) ↔
          ((ρX x₂).1, ρY y₂) ∈ realizedPairs C₁

/-- **Definition 7.** Copies: mimicry in both directions. -/
@[expose] public def Copies {Û : Type u'} (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u', v'} Û) : Prop :=
  Mimics C₁ C₂ ∧ Mimics C₂ C₁

public theorem mimics_rfl (C : InferenceDevice.{u, v} U) : Mimics C C :=
  ⟨id, Equiv.refl Bool, Function.injective_id, fun _ _ => Iff.rfl⟩

/-- **Definition 7 prose:** *"The relation of one device mimicking another is
reflexive and transitive."* -/
public theorem Mimics.trans {Û : Type u'} {Ú : Type u''}
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u', v'} Û}
    {C₃ : InferenceDevice.{u'', v''} Ú}
    (h₁₂ : Mimics C₁ C₂) (h₂₃ : Mimics C₂ C₃) : Mimics C₁ C₃ := by
  obtain ⟨ρX, ρY, hinj, hiff⟩ := h₁₂
  obtain ⟨σX, σY, hsinj, hsiff⟩ := h₂₃
  refine ⟨ρX ∘ σX, σY.trans ρY, hinj.comp hsinj, fun x₃ y₃ => ?_⟩
  exact (hsiff x₃ y₃).trans (hiff (σX x₃) (σY y₃))

public theorem copies_rfl (C : InferenceDevice.{u, v} U) : Copies C C :=
  ⟨mimics_rfl C, mimics_rfl C⟩

/-- **Definition 7 prose:** *"The relation of two devices being copies is an
equivalence relation."* -/
public theorem Copies.symm {Û : Type u'}
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u', v'} Û}
    (h : Copies C₁ C₂) : Copies C₂ C₁ :=
  ⟨h.2, h.1⟩

public theorem Copies.trans {Û : Type u'} {Ú : Type u''}
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u', v'} Û}
    {C₃ : InferenceDevice.{u'', v''} Ú}
    (h₁₂ : Copies C₁ C₂) (h₂₃ : Copies C₂ C₃) : Copies C₁ C₃ :=
  ⟨h₁₂.1.trans h₂₃.1, h₂₃.2.trans h₁₂.2⟩

/-! ## Lemma 1 — reduced forms of realities are exactly the admissible families

The source defines the **reduced form** of a reality `(U; {F_φ})` as the range of
`⊗_φ F_φ`: for a device reality with extra functions, the set of tuples
`([x₁,y₁],[x₂,y₂],…; γ₁,γ₂,…)` for which some `u ∈ U` realizes all coordinates at
once.

**Lemma 1** says that set of reduced forms, `K₁`, equals `K₂`: the families of
tuples whose conclusion coordinates cover `𝔹` and whose setup and function
coordinates each take at least two values.

The `≥ 2` and `= 𝔹` conditions are the source's global stipulations. This
development drops them globally, so here they appear as `SourceStipulations` on
the reality side and as the explicit clauses of `AdmissibleTuples` on the other.
-/

/-- The device with a prescribed setup and conclusion. Lemma 1's realisation
step: the index set of the tuples *is* `U`. -/
@[expose] public def deviceOf {R S : Type*} (s : R → S) (t : R → Bool)
    (hY : Function.Surjective t) : InferenceDevice R where
  Setup := S
  setup := s
  concl := t
  concl_surjective := hY

public theorem deviceOf_setup_concl {R S : Type*} (s : R → S) (t : R → Bool)
    (hY : Function.Surjective t) :
    (deviceOf s t hY).setup = s ∧ (deviceOf s t hY).concl = t :=
  ⟨rfl, rfl⟩

/-- A tuple of a device reality: a `(setup, conclusion)` pair per device index,
and a value per extra-function index. -/
@[expose] public def RealityTuple {A B : Type*} (S : A → Type*) (V : B → Type*) :
    Type _ :=
  ((α : A) → S α × Bool) × ((β : B) → V β)

/-- A reality `(U; {C_α}; {Γ_β})`: a family of devices and a family of arbitrary
functions over one universe. -/
public structure FullReality (U : Type u) {A B : Type*}
    (S : A → Type*) (V : B → Type*) where
  /-- The setup function of device `α`. -/
  setupOf : (α : A) → U → S α
  /-- The conclusion function of device `α`. -/
  conclOf : A → U → Bool
  /-- The extra function `Γ_β`. -/
  funcOf : (β : B) → U → V β

/-- The source's standing stipulations, dropped globally in this development and
therefore stated here: every conclusion is onto `𝔹`, and every setup function and
every extra function takes at least two values. -/
public structure FullReality.SourceStipulations {U : Type u} {A B : Type*}
    {S : A → Type*} {V : B → Type*} (R : FullReality U S V) : Prop where
  /-- The source defines a reality from a nonempty family of functions. -/
  family_nonempty : Nonempty (Sum A B)
  /-- `Y_α` is onto `𝔹`. -/
  concl_surj : ∀ α, Function.Surjective (R.conclOf α)
  /-- `|X_α(U)| ≥ 2`. -/
  setup_two : ∀ α, ∃ u u', R.setupOf α u ≠ R.setupOf α u'
  /-- `|Γ_β(U)| ≥ 2`. -/
  func_two : ∀ β, ∃ u u', R.funcOf β u ≠ R.funcOf β u'

/-- **Reduced form**: the range of the tupling map `⊗_φ F_φ`. -/
@[expose] public def FullReality.reducedForm {U : Type u} {A B : Type*}
    {S : A → Type*} {V : B → Type*} (R : FullReality U S V) :
    Set (RealityTuple S V) :=
  Set.range (fun u : U =>
    ((fun α => (R.setupOf α u, R.conclOf α u)), fun β => R.funcOf β u))

/-- **`K₂`**: the tuple families the source calls admissible. -/
@[expose] public def AdmissibleTuples {A B : Type*} {S : A → Type*} {V : B → Type*}
    (k : Set (RealityTuple S V)) : Prop :=
  Nonempty (Sum A B) ∧
    (∀ (α : A) (b : Bool), ∃ t ∈ k, (t.1 α).2 = b) ∧
    (∀ α : A, ∃ t ∈ k, ∃ t' ∈ k, (t.1 α).1 ≠ (t'.1 α).1) ∧
      (∀ β : B, ∃ t ∈ k, ∃ t' ∈ k, t.2 β ≠ t'.2 β)

/-- **`K₁`**: the reduced forms of realities satisfying the source's stipulations.
The universe is the family itself, which is the source's own construction — *"the
index set of the tuples is `U`"*. -/
@[expose] public def IsReducedForm {A B : Type*} {S : A → Type*} {V : B → Type*}
    (k : Set (RealityTuple S V)) : Prop :=
  ∃ R : FullReality {t : RealityTuple S V // t ∈ k} S V,
    R.SourceStipulations ∧ R.reducedForm = k

/-- **Lemma 1, `K₁ ⊆ K₂`**, for a reality over any universe: a reduced form is
admissible. The conclusions are onto `𝔹` by Definition 1, and the setup and extra
functions take two values by the source's stipulation. -/
public theorem admissibleTuples_of_reducedForm {U : Type u} {A B : Type*}
    {S : A → Type*} {V : B → Type*} (R : FullReality U S V)
    (hstip : R.SourceStipulations) : AdmissibleTuples R.reducedForm := by
  refine ⟨hstip.family_nonempty, fun α b => ?_, fun α => ?_, fun β => ?_⟩
  · obtain ⟨u, hu⟩ := hstip.concl_surj α b
    exact ⟨_, ⟨u, rfl⟩, hu⟩
  · obtain ⟨u, u', hne⟩ := hstip.setup_two α
    exact ⟨_, ⟨u, rfl⟩, _, ⟨u', rfl⟩, hne⟩
  · obtain ⟨u, u', hne⟩ := hstip.func_two β
    exact ⟨_, ⟨u, rfl⟩, _, ⟨u', rfl⟩, hne⟩

public theorem admissibleTuples_of_isReducedForm {A B : Type*}
    {S : A → Type*} {V : B → Type*} {k : Set (RealityTuple S V)}
    (h : IsReducedForm k) : AdmissibleTuples k := by
  obtain ⟨R, hstip, hred⟩ := h
  exact hred ▸ admissibleTuples_of_reducedForm R hstip

/-- **Lemma 1, `K₂ ⊆ K₁`.** Any admissible family *is* a reduced form: take the
family itself as the universe and read each coordinate off the tuple. This is the
source's construction, and it is where the `= 𝔹` and `≥ 2` clauses are used. -/
public theorem isReducedForm_of_admissibleTuples {A B : Type*}
    {S : A → Type*} {V : B → Type*} {k : Set (RealityTuple S V)}
    (h : AdmissibleTuples k) : IsReducedForm k := by
  obtain ⟨hne, hconcl, hsetup, hfunc⟩ := h
  refine ⟨{ setupOf := fun α t => (t.1.1 α).1
            conclOf := fun α t => (t.1.1 α).2
            funcOf := fun β t => t.1.2 β }, ⟨hne, ?_, ?_, ?_⟩, ?_⟩
  · intro α b
    obtain ⟨t, htk, hb⟩ := hconcl α b
    exact ⟨⟨t, htk⟩, hb⟩
  · intro α
    obtain ⟨t, htk, t', ht'k, hne⟩ := hsetup α
    exact ⟨⟨t, htk⟩, ⟨t', ht'k⟩, hne⟩
  · intro β
    obtain ⟨t, htk, t', ht'k, hne⟩ := hfunc β
    exact ⟨⟨t, htk⟩, ⟨t', ht'k⟩, hne⟩
  · apply Set.Subset.antisymm
    · rintro s ⟨t, rfl⟩
      exact t.2
    · intro t htk
      exact ⟨⟨t, htk⟩, rfl⟩

/-- A reality over **any** universe has an `IsReducedForm` reduced form, so fixing
the universe to the family itself in `IsReducedForm` loses nothing: `K₁` as defined
is `K₁` as the source means it. -/
public theorem isReducedForm_of_reality {W : Type w} {A B : Type*}
    {S : A → Type*} {V : B → Type*} (R : FullReality W S V)
    (h : R.SourceStipulations) : IsReducedForm R.reducedForm :=
  isReducedForm_of_admissibleTuples (admissibleTuples_of_reducedForm R h)

/-- **Lemma 1.** `K₁ = K₂`: the reduced forms of device realities are exactly the
admissible tuple families. -/
public theorem lemma1_reducedForm_iff_admissible {A B : Type*}
    {S : A → Type*} {V : B → Type*} (k : Set (RealityTuple S V)) :
    IsReducedForm k ↔ AdmissibleTuples k :=
  ⟨admissibleTuples_of_isReducedForm, isReducedForm_of_admissibleTuples⟩

/-! ## Proposition 5(ii) — infinite copies with strong inference

`C₁` has identity setup and parity conclusion. `C₂` has setup `n/2` and
the same parity-of-setup conclusion. Each `C₂`-fibre `{2k, 2k+1}` holds both
`Y₁` values, so `C₁` strongly infers `C₂`. Both devices realise the pairs
`(k, k even)`, so they are copies.
-/

@[expose] public def infiniteCopy1 : InferenceDevice ℕ where
  Setup := ℕ
  setup := id
  concl := fun n => decide (n % 2 = 0)
  concl_surjective := fun
    | true => ⟨0, rfl⟩
    | false => ⟨1, rfl⟩

@[expose] public def infiniteCopy2 : InferenceDevice ℕ where
  Setup := ℕ
  setup := fun n => n / 2
  concl := fun n => decide ((n / 2) % 2 = 0)
  concl_surjective := fun
    | true => ⟨0, rfl⟩
    | false => ⟨2, rfl⟩

/-- Even point of the `C₂`-fibre of `x` (paper: `i = 2x`). -/
public theorem fibre_even (x : ℕ) : (2 * x) / 2 = x :=
  Nat.mul_div_right x (by decide : 0 < 2)

/-- Odd point of the `C₂`-fibre of `x` (paper: `i = 2x+1`). -/
public theorem fibre_odd (x : ℕ) : (2 * x + 1) / 2 = x := by
  rw [Nat.add_comm, Nat.add_mul_div_left _ _ (by decide : 0 < 2)]
  simp

public theorem even_mod_two (x : ℕ) : (2 * x) % 2 = 0 := by
  rw [Nat.mul_mod]; simp

public theorem odd_mod_two (x : ℕ) : (2 * x + 1) % 2 = 1 := by
  rw [Nat.add_mod, Nat.mul_mod]; simp

/-- `Setup` of each infinite copy is definitionally `ℕ`. Instance search
does not unfold the structure field; these wrappers do. -/
@[expose] public def asNat1 (x : infiniteCopy1.Setup) : ℕ := x
@[expose] public def asNat2 (x : infiniteCopy2.Setup) : ℕ := x

/-- **Proposition 5(ii) existence, strong-inference half.** On fibre `x` of
`C₂`, the even point answers the identity probe and the odd point the
negation (or the reverse, according to the parity of `x`). -/
public theorem infiniteCopy_stronglyInfers :
    StronglyInfers infiniteCopy1 infiniteCopy2 := by
  intro γ f hf _ x₂ _
  let x : ℕ := x₂
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · -- identity: pick the point of the fibre whose `Y₁` equals `Y₂`
    by_cases hx : x % 2 = 0
    · refine ⟨2 * x, ⟨2 * x, rfl⟩, ?_⟩
      intro w hw; cases hw
      exact ⟨fibre_even x, by
        change decide ((2 * x) % 2 = 0) = decide (((2 * x) / 2) % 2 = 0)
        rw [even_mod_two, fibre_even, hx]⟩
    · refine ⟨2 * x + 1, ⟨2 * x + 1, rfl⟩, ?_⟩
      intro w hw; cases hw
      exact ⟨fibre_odd x, by
        change decide ((2 * x + 1) % 2 = 0) = decide (((2 * x + 1) / 2) % 2 = 0)
        rw [odd_mod_two, fibre_odd]
        simp [hx]⟩
  · -- negation: the other point of the same fibre
    by_cases hx : x % 2 = 0
    · refine ⟨2 * x + 1, ⟨2 * x + 1, rfl⟩, ?_⟩
      intro w hw; cases hw
      exact ⟨fibre_odd x, by
        change decide ((2 * x + 1) % 2 = 0) = !decide (((2 * x + 1) / 2) % 2 = 0)
        rw [odd_mod_two, fibre_odd, hx]; rfl⟩
    · refine ⟨2 * x, ⟨2 * x, rfl⟩, ?_⟩
      intro w hw; cases hw
      exact ⟨fibre_even x, by
        change decide ((2 * x) % 2 = 0) = !decide (((2 * x) / 2) % 2 = 0)
        rw [even_mod_two, fibre_even]
        simp [hx]⟩

/-- Both devices realise `(x, y)` iff `y` is the parity of `x`. Identity on
setup labels is therefore a copy map. -/
public theorem infiniteCopy_copies : Copies infiniteCopy1 infiniteCopy2 := by
  have hR1 : ∀ n : ℕ, infiniteCopy1.Realized n := fun n => ⟨n, rfl⟩
  have hR2 : ∀ n : ℕ, infiniteCopy2.Realized n := fun n => ⟨2 * n, fibre_even n⟩
  constructor
  · refine ⟨fun x => ⟨x.1, hR1 x.1⟩, Equiv.refl Bool, ?_, ?_⟩
    · intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {n // infiniteCopy1.Realized n} => z.1) h
    · intro x₂ y₂
      constructor
      · intro ⟨w, hs, hy⟩
        refine ⟨x₂.1, rfl, ?_⟩
        simp [infiniteCopy1, infiniteCopy2] at hs hy ⊢
        exact hs ▸ hy
      · intro ⟨w, hs, hy⟩
        refine ⟨2 * asNat2 x₂.1, fibre_even (asNat2 x₂.1), ?_⟩
        simp [infiniteCopy1, infiniteCopy2, asNat2] at hs hy ⊢
        exact hs ▸ hy
  · refine ⟨fun x => ⟨x.1, hR2 x.1⟩, Equiv.refl Bool, ?_, ?_⟩
    · intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {n // infiniteCopy2.Realized n} => z.1) h
    · intro x₂ y₂
      constructor
      · intro ⟨w, hs, hy⟩
        refine ⟨2 * asNat1 x₂.1, fibre_even (asNat1 x₂.1), ?_⟩
        simp [infiniteCopy1, infiniteCopy2, asNat1] at hs hy ⊢
        exact hs ▸ hy
      · intro ⟨w, hs, hy⟩
        refine ⟨x₂.1, rfl, ?_⟩
        simp [infiniteCopy1, infiniteCopy2] at hs hy ⊢
        exact hs ▸ hy

/-- **Proposition 5(ii), existence.** -/
public theorem exists_copies_stronglyInfers_infinite :
    ∃ C₁ C₂ : InferenceDevice.{0, 0} ℕ,
      Copies C₁ C₂ ∧ StronglyInfers C₁ C₂ :=
  ⟨infiniteCopy1, infiniteCopy2, infiniteCopy_copies, infiniteCopy_stronglyInfers⟩

/-- **Proposition 4, uniqueness core.** Two distinguishable devices cannot
both strongly infer a third at two different setup values. -/
public theorem not_two_strong_inferrers_conflict
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    {C₃ : InferenceDevice.{u, v''} U}
    (h13 : StronglyInfers C₁ C₃) (h23 : StronglyInfers C₂ C₃)
    (hdist : Distinguishable C₁ C₂)
    {x a : C₃.Setup} (hxa : x ≠ a)
    (hx : C₃.Realized x) (ha : C₃.Realized a) : False := by
  obtain ⟨wt, hwt⟩ := C₃.concl_surjective true
  obtain ⟨x₁, hx₁, h₁⟩ := h13 true id isProbe_id ⟨wt, hwt⟩ x hx
  obtain ⟨x₂, hx₂, h₂⟩ := h23 true id isProbe_id ⟨wt, hwt⟩ a ha
  obtain ⟨w, hw₁, hw₂⟩ := hdist x₁ hx₁ x₂ hx₂
  exact hxa ((h₁ w hw₁).1.symm.trans (h₂ w hw₂).1)

/-! ## Proposition 5(i) — the paper's five quadruples

`{(−1,−1,−1,−1); (−1,−1,1,−1); (1,−1,−1,1); (1,1,1,−1); (−1,1,1,1)}`
with `−1 ↦ false`, `1 ↦ true`. Both devices realise every `Bool × Bool`
pair, so the identity on setup labels is a copy map. `X₁ = true` answers
negation of `Y₂`; `X₁ = false` answers the identity.
-/

public structure FiniteCopyRow where
  x1 : Bool
  y1 : Bool
  x2 : Bool
  y2 : Bool

@[expose] public def finiteCopyTable : Fin 5 → FiniteCopyRow
  | 0 => { x1 := false, y1 := false, x2 := false, y2 := false }
  | 1 => { x1 := false, y1 := false, x2 := true,  y2 := false }
  | 2 => { x1 := true,  y1 := false, x2 := false, y2 := true }
  | 3 => { x1 := true,  y1 := true,  x2 := true,  y2 := false }
  | 4 => { x1 := false, y1 := true,  x2 := true,  y2 := true }

@[expose] public def finiteCopy1 : InferenceDevice (Fin 5) where
  Setup := Bool
  setup := fun u => (finiteCopyTable u).x1
  concl := fun u => (finiteCopyTable u).y1
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨3, rfl⟩

@[expose] public def finiteCopy2 : InferenceDevice (Fin 5) where
  Setup := Bool
  setup := fun u => (finiteCopyTable u).x2
  concl := fun u => (finiteCopyTable u).y2
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨2, rfl⟩

/-- Every pair is realised by the first device (paper: “by inspection”). -/
public theorem finiteCopy1_all_pairs (x y : Bool) :
    (x, y) ∈ realizedPairs finiteCopy1 := by
  cases x <;> cases y
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨4, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩
  · exact ⟨3, rfl, rfl⟩

/-- Every pair is realised by the second device. -/
public theorem finiteCopy2_all_pairs (x y : Bool) :
    (x, y) ∈ realizedPairs finiteCopy2 := by
  cases x <;> cases y
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨4, rfl, rfl⟩

public theorem finiteCopy1_realized : ∀ x : Bool, finiteCopy1.Realized x
  | false => ⟨0, rfl⟩
  | true => ⟨2, rfl⟩

public theorem finiteCopy2_realized : ∀ x : Bool, finiteCopy2.Realized x
  | false => ⟨0, rfl⟩
  | true => ⟨1, rfl⟩

/-- Identity on setup labels, because both devices realise the same pairs. -/
public theorem finiteCopy_copies : Copies finiteCopy1 finiteCopy2 := by
  constructor
  · refine ⟨fun x => ⟨x.1, finiteCopy1_realized x.1⟩, Equiv.refl Bool, ?_, ?_⟩
    · intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {n // finiteCopy1.Realized n} => z.1) h
    · intro x₂ y₂
      exact ⟨fun _ => finiteCopy1_all_pairs x₂.1 y₂,
        fun _ => finiteCopy2_all_pairs x₂.1 y₂⟩
  · refine ⟨fun x => ⟨x.1, finiteCopy2_realized x.1⟩, Equiv.refl Bool, ?_, ?_⟩
    · intro a b h
      apply Subtype.ext
      exact congrArg (fun z : {n // finiteCopy2.Realized n} => z.1) h
    · intro x₂ y₂
      exact ⟨fun _ => finiteCopy2_all_pairs x₂.1 y₂,
        fun _ => finiteCopy1_all_pairs x₂.1 y₂⟩

public theorem finiteCopy_distinguishable :
    Distinguishable finiteCopy1 finiteCopy2 := by
  intro x₁ _ x₂ _
  cases x₁ <;> cases x₂
  · exact ⟨0, rfl, rfl⟩
  · exact ⟨1, rfl, rfl⟩
  · exact ⟨2, rfl, rfl⟩
  · exact ⟨3, rfl, rfl⟩

/-- `X₁ = false` answers the identity probe of `Y₂`; `X₁ = true` answers
negation (`X₁ = 1 ⇒ Y₁ = −Y₂` in the paper). -/
public theorem finiteCopy_infers : InfersDevice finiteCopy1 finiteCopy2 := by
  intro γ f hf _
  rcases isProbe_bool hf with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · refine ⟨false, ⟨0, rfl⟩, ?_⟩
    intro w hw; fin_cases w <;> cases hw <;> rfl
  · refine ⟨true, ⟨2, rfl⟩, ?_⟩
    intro w hw; fin_cases w <;> cases hw <;> rfl

/-- **Proposition 5(i).** -/
public theorem exists_copies_distinguishable_weak :
    ∃ C₁ C₂ : InferenceDevice.{0, 0} (Fin 5),
      Copies C₁ C₂ ∧ Distinguishable C₁ C₂ ∧ InfersDevice C₁ C₂ :=
  ⟨finiteCopy1, finiteCopy2, finiteCopy_copies,
    finiteCopy_distinguishable, finiteCopy_infers⟩

/-! ## Proposition 5(ii) necessity — two injective fibre maps

`C₁ ≫ C₂` supplies, for each realised `x₂`, a setup answering the identity
probe on that fibre and one answering negation. Those maps are injective
and pointwise distinct, so `|X₁(U)| ≥ 2|X₂(U)|`. Copies force equal
cardinality. Hence both images are infinite.
-/

/-- Identity-probe setup of `C₁` on the fibre of `x₂`. -/
public noncomputable def identityFibreSetup
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) (x₂ : {x // C₂.Realized x}) :
    {x // C₁.Realized x} :=
  ⟨(hs true id isProbe_id (C₂.concl_surjective true) x₂.1 x₂.2).choose,
    (hs true id isProbe_id (C₂.concl_surjective true) x₂.1 x₂.2).choose_spec.1⟩

/-- Negation-probe setup of `C₁` on the fibre of `x₂`. -/
public noncomputable def negationFibreSetup
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) (x₂ : {x // C₂.Realized x}) :
    {x // C₁.Realized x} :=
  ⟨(hs false (fun b => !b) isProbe_not (C₂.concl_surjective false)
      x₂.1 x₂.2).choose,
    (hs false (fun b => !b) isProbe_not (C₂.concl_surjective false)
      x₂.1 x₂.2).choose_spec.1⟩

public theorem identityFibreSetup_spec
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) (x₂ : {x // C₂.Realized x}) :
    ∀ w, C₁.setup w = (identityFibreSetup hs x₂).1 →
      C₂.setup w = x₂.1 ∧ C₁.concl w = C₂.concl w :=
  (hs true id isProbe_id (C₂.concl_surjective true) x₂.1 x₂.2).choose_spec.2

public theorem negationFibreSetup_spec
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) (x₂ : {x // C₂.Realized x}) :
    ∀ w, C₁.setup w = (negationFibreSetup hs x₂).1 →
      C₂.setup w = x₂.1 ∧ C₁.concl w = !C₂.concl w :=
  (hs false (fun b => !b) isProbe_not (C₂.concl_surjective false)
    x₂.1 x₂.2).choose_spec.2

public theorem identityFibreSetup_injective
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) :
    Function.Injective (identityFibreSetup (C₁ := C₁) (C₂ := C₂) hs) := by
  intro a b h
  obtain ⟨w, hw⟩ := (identityFibreSetup hs a).2
  have hval : (identityFibreSetup hs a).1 = (identityFibreSetup hs b).1 :=
    congrArg Subtype.val h
  exact Subtype.ext
    (((identityFibreSetup_spec hs a w hw).1).symm.trans
      (identityFibreSetup_spec hs b w (hval ▸ hw)).1)

public theorem identity_ne_negation_fibre
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) (x₂ : {x // C₂.Realized x}) :
    identityFibreSetup hs x₂ ≠ negationFibreSetup hs x₂ := by
  intro h
  obtain ⟨w, hw⟩ := (identityFibreSetup hs x₂).2
  have hval : (identityFibreSetup hs x₂).1 = (negationFibreSetup hs x₂).1 :=
    congrArg Subtype.val h
  have hid := (identityFibreSetup_spec hs x₂ w hw).2
  have hneg := (negationFibreSetup_spec hs x₂ w (hval ▸ hw)).2
  exact Bool.not_ne_self (C₂.concl w) (hid.symm.trans hneg).symm

/-- **Proposition 5(ii), necessity.** -/
public theorem copies_stronglyInfers_not_finite
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    [Fintype {x // C₁.Realized x}] [Fintype {x // C₂.Realized x}]
    (hC : Copies C₁ C₂) (hs : StronglyInfers C₁ C₂) : False := by
  classical
  let ξ := identityFibreSetup (C₁ := C₁) (C₂ := C₂) hs
  let ξ' := negationFibreSetup (C₁ := C₁) (C₂ := C₂) hs
  have hinj : Function.Injective ξ := identityFibreSetup_injective hs
  have hne : ∀ x₂, ξ x₂ ≠ ξ' x₂ := identity_ne_negation_fibre hs
  let s := (Finset.univ.image ξ) ∪ (Finset.univ.image ξ')
  have hdisj : Disjoint (Finset.univ.image ξ) (Finset.univ.image ξ') := by
    refine Finset.disjoint_iff_ne.mpr ?_
    intro a ha b hb heq
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    have : ξ x = ξ' y := heq
    have hxR : C₁.Realized (ξ x).1 := (ξ x).2
    obtain ⟨w, hw⟩ := hxR
    have hxa := (identityFibreSetup_spec hs x w hw).1
    have hyb := (negationFibreSetup_spec hs y w (by
      have : (ξ x).1 = (ξ' y).1 := congrArg Subtype.val this
      exact this ▸ hw)).1
    have hxy : x = y := Subtype.ext (hxa.symm.trans hyb)
    subst hxy
    exact hne x this
  have hcard2 :
      (Finset.univ.image ξ ∪ Finset.univ.image ξ').card =
        2 * Fintype.card {x // C₂.Realized x} := by
    rw [Finset.card_union_of_disjoint hdisj,
      Finset.card_image_of_injective _ hinj]
    have hinj' : Function.Injective ξ' := by
      intro a b h
      obtain ⟨w, hw⟩ := (ξ' a).2
      have hval : (ξ' a).1 = (ξ' b).1 := congrArg Subtype.val h
      exact Subtype.ext
        (((negationFibreSetup_spec hs a w hw).1).symm.trans
          (negationFibreSetup_spec hs b w (hval ▸ hw)).1)
    rw [Finset.card_image_of_injective _ hinj']
    simp [two_mul]
  have hle : 2 * Fintype.card {x // C₂.Realized x} ≤
      Fintype.card {x // C₁.Realized x} := by
    have : (Finset.univ.image ξ ∪ Finset.univ.image ξ').card ≤
        Fintype.card {x // C₁.Realized x} := Finset.card_le_univ _
    exact hcard2 ▸ this
  obtain ⟨ρ12, _, hρ12, _⟩ := hC.1
  obtain ⟨ρ21, _, hρ21, _⟩ := hC.2
  have hcard : Fintype.card {x // C₁.Realized x} =
      Fintype.card {x // C₂.Realized x} :=
    Nat.le_antisymm
      (Fintype.card_le_of_injective ρ21 hρ21)
      (Fintype.card_le_of_injective ρ12 hρ12)
  have hpos : 0 < Fintype.card {x // C₂.Realized x} := by
    obtain ⟨w, _⟩ := C₂.concl_surjective true
    exact Fintype.card_pos_iff.mpr ⟨⟨C₂.setup w, ⟨w, rfl⟩⟩⟩
  nlinarith

/-- **Proposition 4.** Unique root of a finite weakly-connected
strong-inference graph whose incomparable pairs are distinguishable.
The combinatorial core is `not_two_strong_inferrers_conflict`; existence
of a root is maximality of the successor-count (paper: finite + acyclic). -/
@[expose] public def StrongEdge {n : ℕ} (R : DeviceReality U n) (i j : Fin n) : Prop :=
  StronglyInfers (R i) (R j) ∨ StronglyInfers (R j) (R i)

@[expose] public def StrongGraphWeaklyConnected {n : ℕ} (R : DeviceReality U n) : Prop :=
  ∀ i j : Fin n, Relation.ReflTransGen (StrongEdge R) i j

@[expose] public def IsStrongRoot {n : ℕ} (R : DeviceReality U n) (r : Fin n) : Prop :=
  ∀ i : Fin n, StronglyInfers (R i) (R r) → i = r

public theorem exists_strong_root {n : ℕ} [NeZero n] (R : DeviceReality U n) :
    ∃ r : Fin n, IsStrongRoot R r := by
  classical
  let succ (i : Fin n) : Finset (Fin n) :=
    Finset.univ.filter (fun j => StronglyInfers (R i) (R j))
  let f : Fin n → ℕ := fun i => (succ i).card
  let im : Finset ℕ := Finset.univ.image f
  have him : im.Nonempty := Finset.image_nonempty.mpr Finset.univ_nonempty
  obtain ⟨r, hrU, hrm⟩ := Finset.mem_image.mp (Finset.max'_mem im him)
  have hr : ∀ k : Fin n, f k ≤ f r := fun k => by
    have hk : f k ∈ im := Finset.mem_image_of_mem f (Finset.mem_univ k)
    have : f k ≤ im.max' him := (Finset.isGreatest_max' im him).2 hk
    simpa [hrm] using this
  refine ⟨r, fun k hk => ?_⟩
  have hsub : succ r ⊆ succ k := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      stronglyInfers_trans hk (Finset.mem_filter.mp hj).2⟩
  have hlt : (succ r).card < (succ k).card ∨ k = r := by
    by_cases hkr : k = r
    · exact Or.inr hkr
    · have : r ∈ succ k :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
      have : r ∉ succ r := by
        intro hr'
        exact not_stronglyInfers_self (R r) (Finset.mem_filter.mp hr').2
      have hss : succ r ⊂ succ k :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun heq =>
          this (heq.symm ▸ ‹r ∈ succ k›)⟩
      exact Or.inl (Finset.card_lt_card hss)
  rcases hlt with hlt | rfl
  · exact (Nat.not_lt.mpr (hr k) hlt).elim
  · rfl

/-- **Proposition 4.**

`hconn` follows the source's **proof** (*"Since `D` is weakly connected"*, with
successors and predecessors taken over nodes *in* `D`), not its statement, which
asks only that the graph *of the reality* be weakly connected over `D`. The printed statement uses "over `D`" twice — the
conclusion says the graph "has one and only one root over `D`", where it can only
mean *restricted to* `D` — so statement and proof agree and this transcribes
both; see clash 7b in `docs/provenance/wolpert-2008-source-clashes.md`. `htwo` reintroduces the source's
§1.2 two-value stipulation, which this development does not impose globally. -/
public theorem unique_strong_root {n : ℕ} [NeZero n]
    (R : DeviceReality U n)
    (hconn : StrongGraphWeaklyConnected R)
    (hdist : ∀ i j : Fin n, i ≠ j →
      ¬ StronglyInfers (R i) (R j) → ¬ StronglyInfers (R j) (R i) →
        Distinguishable (R i) (R j))
    (htwo : ∀ i : Fin n, ∃ a b : (R i).Setup,
      a ≠ b ∧ (R i).Realized a ∧ (R i).Realized b) :
    ∃! r : Fin n, IsStrongRoot R r := by
  classical
  obtain ⟨r, hr⟩ := exists_strong_root R
  refine ⟨r, hr, fun k hk => ?_⟩
  by_contra hne
  have hinc : ¬ StronglyInfers (R r) (R k) := fun h => hne (hk r h).symm
  have hinc' : ¬ StronglyInfers (R k) (R r) := fun h => hne (hr k h)
  have hD : Distinguishable (R r) (R k) :=
    hdist r k (Ne.symm hne) hinc hinc'
  -- both roots strongly infer a common successor along the undirected path
  -- (paper: S({C₁}) ⊂ P[S({C₁})], then two roots of a shared child).
  -- Weak connectivity plus transitivity: walk the undirected path until
  -- an edge leaves the successor set of `r`; that child is inferred by both.
  let S : Finset (Fin n) :=
    Finset.univ.filter (fun j => j = r ∨ StronglyInfers (R r) (R j))
  have hrS : r ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inl rfl⟩
  have hkS : k ∉ S := by
    intro hkS'
    rcases (Finset.mem_filter.mp hkS').2 with rfl | h
    · exact hne rfl
    · exact hinc h
  -- there is an undirected path; some edge crosses the cut
  have hex : ∃ i j : Fin n, i ∈ S ∧ j ∉ S ∧ StrongEdge R i j := by
    have : ∀ a b : Fin n,
        Relation.ReflTransGen (StrongEdge R) a b →
          a ∈ S → b ∉ S →
            ∃ i j : Fin n, i ∈ S ∧ j ∉ S ∧ StrongEdge R i j := by
      intro a b hab haS hbS
      induction hab with
      | refl => exact (hbS haS).elim
      | @tail c b h_ac h_cb ih =>
        by_cases hc : c ∈ S
        · exact ⟨c, b, hc, hbS, h_cb⟩
        · exact ih hc
    exact this r k (hconn r k) hrS hkS
  obtain ⟨i, j, hiS, hjS, hij⟩ := hex
  -- the crossing edge cannot be i ≫ j with i in S, j out: then j ∈ S
  have hnot_out : ¬ StronglyInfers (R i) (R j) := by
    intro hij'
    have : j ∈ S := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rcases (Finset.mem_filter.mp hiS).2 with rfl | hri
      · exact Or.inr hij'
      · exact Or.inr (stronglyInfers_trans hri hij')
    exact hjS this
  have hin : StronglyInfers (R j) (R i) := hij.resolve_left hnot_out
  -- `i` is a successor of `r` (or `r` itself), so `r ≫ i`; `j` has a
  -- root-predecessor `k` is not needed: `j` itself need not be a root.
  -- Paper: `i` has a predecessor outside S; take a root of that
  -- predecessor. We already have two distinguishable devices (`r` and
  -- any root of `j`) both strongly inferring `i` if `i ≠ r`.
  have hri : StronglyInfers (R r) (R i) ∨ i = r :=
    (Finset.mem_filter.mp hiS).2.symm
  obtain ⟨a, b, hab, ha, hb⟩ := htwo i
  rcases hri with hri | rfl
  · -- `r ≫ i` and `j ≫ i`, and `r ≠ j` (j ∉ S)
    have hrj : r ≠ j := fun h => hjS (h ▸ hrS)
    have hrootj : ¬ StronglyInfers (R r) (R j) := fun h =>
      hjS (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Or.inr h⟩)
    have hjr : ¬ StronglyInfers (R j) (R r) := fun h => by
      have : StronglyInfers (R j) (R r) := h
      have : j = r := hr j this
      exact hrj this.symm
    have hDj : Distinguishable (R r) (R j) :=
      hdist r j hrj hrootj hjr
    exact not_two_strong_inferrers_conflict hri hin hDj hab ha hb
  · -- `i = r`: then `j ≫ r`, contradicting that `r` is a root unless `j = r`
    exact hjS (Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      Or.inl (hr j hin)⟩)


/-! ## Universal devices — the source's "monotheism theorem"

Both papers define this in prose and immediately draw a consequence from it.
2008, after Definition 7: *"Define a universal device as any device in a reality
that can strongly infer all other devices and weakly infer all functions in that
reality. Theorem 3 means that no reality can contain more than one universal
device."* 2018 repeats it word for word, citing its Proposition 6 — which is
2008's Theorem 3. The paper names the pair of results the **monotheism theorem**.

Neither the definition nor the uniqueness claim was tracked until an adversarial
review of the coverage tables went looking for prose that states a claim.

**Stronger than printed.** The printed definition has two clauses — strongly
infers every other device, *and* weakly infers every function of the reality —
and uniqueness needs only the first. `IsUniversal` therefore carries only the
device clause, so `universal_unique` rules out more devices than the source's
argument does. `DeviceReality` has no `{Γ_β}` component to state the second
clause against; the source's functions live in `FullReality`.
-/

/-- **A universal device**, on the clause uniqueness actually uses: it strongly
infers every other device of the reality. -/
@[expose] public def IsUniversal {n : ℕ} (R : DeviceReality U n) (i : Fin n) : Prop :=
  ∀ j : Fin n, j ≠ i → StronglyInfers (R i) (R j)

/-- **"No reality can contain more than one universal device."** Two universal
devices would strongly infer each other, which Theorem 3 forbids. -/
public theorem universal_unique {n : ℕ} (R : DeviceReality U n) {i j : Fin n}
    (hi : IsUniversal R i) (hj : IsUniversal R j) : i = j := by
  by_contra hne
  exact not_stronglyInfers_both (hi j (Ne.symm hne)) (hj i hne)

/-- **"A universal device in a reality must be a root node of the strong
inference graph."** Same argument, read off the graph. -/
public theorem isStrongRoot_of_isUniversal {n : ℕ} (R : DeviceReality U n)
    {i : Fin n} (hi : IsUniversal R i) : IsStrongRoot R i := by
  intro k hk
  by_contra hne
  exact not_stronglyInfers_both (hi k hne) hk

/-- **"...and that there cannot be any other root node."** The second half of the
printed sentence: a universal device is not merely *a* root, it is the only one. -/
public theorem strongRoot_eq_of_isUniversal {n : ℕ} (R : DeviceReality U n)
    {u r : Fin n} (hu : IsUniversal R u) (hr : IsStrongRoot R r) : r = u := by
  by_contra hne
  exact hne ((hr u (hu r hne)).symm)

/-- The printed corollary in its existential form: at most one universal device,
and if there is one it is the unique strong root. -/
public theorem subsingleton_isUniversal {n : ℕ} (R : DeviceReality U n) :
    ∀ i j : Fin n, IsUniversal R i → IsUniversal R j → i = j :=
  fun _ _ hi hj => universal_unique R hi hj


/-! ### The printed two-clause universal device

`IsUniversal` above carries only the clause uniqueness needs. The printed
definition has two:

> *"Define a universal device as any device in a reality that can **strongly
> infer all other devices** and **weakly infer all functions** in that reality."*

`DeviceReality` has no function family to state the second clause against, so it
is stated here over `FullReality`, which carries the source's `{Γ_β}`.

Uniqueness is **inherited rather than reproved**: it never used the second
clause, so the same argument applies verbatim and the two-clause version is a
weaker hypothesis with the same conclusion.
-/

variable {A B : Type*} {S : A → Type v} {V : B → Type*}

/-- The device at index `α` of a full reality, given the source's surjectivity
stipulation. -/
@[expose] public def FullReality.device (R : FullReality U S V)
    (hsurj : ∀ α, Function.Surjective (R.conclOf α)) (α : A) :
    InferenceDevice.{u, v} U :=
  deviceOf (R.setupOf α) (R.conclOf α) (hsurj α)

/--
**The printed definition of a universal device**, both clauses.

`IsUniversal` is this with the second clause dropped; that is why the uniqueness
theorem there is *stronger* than the source's, and why this one is the faithful
transcription rather than the useful one.
-/
@[expose] public def FullReality.IsUniversalFull (R : FullReality U S V)
    (hsurj : ∀ α, Function.Surjective (R.conclOf α)) (α : A) : Prop :=
  (∀ α' : A, α' ≠ α → StronglyInfers (R.device hsurj α) (R.device hsurj α')) ∧
    (∀ β : B, WeaklyInfers (R.device hsurj α) (R.funcOf β))

/-- **"No reality can contain more than one universal device"**, at the printed
two-clause definition. The proof is the one-clause argument unchanged: two
universal devices would strongly infer each other, which Theorem 3 forbids. -/
public theorem FullReality.isUniversalFull_unique (R : FullReality U S V)
    (hsurj : ∀ α, Function.Surjective (R.conclOf α)) {α α' : A}
    (h : R.IsUniversalFull hsurj α) (h' : R.IsUniversalFull hsurj α') : α = α' := by
  by_contra hne
  exact not_stronglyInfers_both (h.1 α' (Ne.symm hne)) (h'.1 α hne)

/-- The second clause is what `IsUniversal` drops. Recording the implication
makes the relationship a theorem rather than a remark: the printed notion is
strictly stronger, so `universal_unique` covers strictly more devices. -/
public theorem FullReality.stronglyInfers_of_isUniversalFull (R : FullReality U S V)
    (hsurj : ∀ α, Function.Surjective (R.conclOf α)) {α : A}
    (h : R.IsUniversalFull hsurj α) :
    ∀ α' : A, α' ≠ α → StronglyInfers (R.device hsurj α) (R.device hsurj α') :=
  h.1

/-- And the clause itself, so the printed definition's second half has a name. -/
public theorem FullReality.weaklyInfers_of_isUniversalFull (R : FullReality U S V)
    (hsurj : ∀ α, Function.Surjective (R.conclOf α)) {α : A}
    (h : R.IsUniversalFull hsurj α) (β : B) :
    WeaklyInfers (R.device hsurj α) (R.funcOf β) :=
  h.2 β

/-! ### The `|U| > 3` sentence — repaired, not bridged from Proposition 7(2)

2018, after Definition 10: *"Prop. 7(ii) means that no reality with `|U| > 3`
can have a universal device if the reality contains all functions defined over
`U`."*

Proposition 7(2) is an existential over **pairs**. Universality's first clause
quantifies over **devices**. An existential over pairs cannot discharge a
universal over devices, whatever witness is chosen. The source's own witness
`S = T = id` is a device pair only at `U = Bool`, which `|U| > 3` excludes.
Clash 28.

The conclusion is nevertheless true, and needs no cardinality: a universal
device must weakly infer every function in the reality, including — once the
family contains it — its own conclusion, which Proposition 1(ii) forbids. The
function family is specialized to `U → Bool` so the membership is an equality
of maps, not a `HEq`.
-/

/-- **Honesty check.** A device's conclusion is admissible as an extra function
under `SourceStipulations`: it is surjective onto `Bool`, so `func_two` holds
at that index. The comparison in clash 28 would shift if this failed. -/
public theorem FullReality.func_two_of_concl_mem
    {B : Type*} (R : FullReality U S (fun _ : B => Bool))
    (hsurj : ∀ α, Function.Surjective (R.conclOf α))
    {α : A} {β : B} (hmem : R.funcOf β = R.conclOf α) :
    ∃ u u' : U, R.funcOf β u ≠ R.funcOf β u' := by
  obtain ⟨u, hu⟩ := hsurj α true
  obtain ⟨u', hu'⟩ := hsurj α false
  exact ⟨u, u', by simp [hmem, hu, hu']⟩

/-- If the extra-function family contains a device's own conclusion, that
device is not universal. No `|U| > 3`: this is 2018 Proposition 1 / 2008
Proposition 1(ii), not Proposition 7(2). -/
public theorem FullReality.not_isUniversalFull_of_concl_mem
    {B : Type*} (R : FullReality U S (fun _ : B => Bool))
    (hsurj : ∀ α, Function.Surjective (R.conclOf α))
    {α : A} {β : B} (hmem : R.funcOf β = R.conclOf α) :
    ¬ R.IsUniversalFull hsurj α := by
  intro hUniv
  refine not_weaklyInfers_own_concl (R.device hsurj α) ?_
  have : (R.device hsurj α).concl = R.funcOf β := by
    simp [FullReality.device, deviceOf, hmem]
  exact this ▸ hUniv.2 β

/-- The extra-function family contains every two-valued Boolean map — the
source's own stipulation, not the type-theoretic "all functions", which would
include constants that `func_two` rejects. -/
@[expose] public def FullReality.ContainsEveryTwoValuedBool
    {B : Type*} (R : FullReality U S (fun _ : B => Bool)) : Prop :=
  ∀ Γ : U → Bool, Function.Surjective Γ → ∃ β : B, R.funcOf β = Γ

/-- **The printed conclusion**, without `|U| > 3`. A reality that contains every
admissible Boolean function contains each device's conclusion, so no device is
universal. The printed citation of Proposition 7(2) is not used. -/
public theorem FullReality.not_isUniversalFull_of_containsEveryTwoValuedBool
    {B : Type*} (R : FullReality U S (fun _ : B => Bool))
    (hsurj : ∀ α, Function.Surjective (R.conclOf α))
    (hall : R.ContainsEveryTwoValuedBool) (α : A) :
    ¬ R.IsUniversalFull hsurj α := by
  obtain ⟨β, hβ⟩ := hall (R.conclOf α) (hsurj α)
  exact R.not_isUniversalFull_of_concl_mem hsurj hβ

end AISafetyAtlas.Inference
