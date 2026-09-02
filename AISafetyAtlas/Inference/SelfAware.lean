module

public import AISafetyAtlas.Inference.Device
public import AISafetyAtlas.Inference.Complexity
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Order
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Tactic.Linarith

/-!
# Self-aware devices — Wolpert 2008 §9

A self-aware device is a triple `(X, Y, Q)`: an inference device together with
a question function whose values are binary predicates on `U`. This is **not**
`Knowledge.Knowable` and **not** Wolpert 2018's physical-knowledge operator.
-/

namespace AISafetyAtlas.Inference

universe u v v' w w'

variable {U : Type u}

-- `linter.checkUnivs` (new at Lean v4.33) observes that these universes only
-- occur together and could be merged. Merging them changes a public
-- declaration's universe parameters, which is a statement change rather than
-- a toolchain fix; it is not made as part of a version bump.
set_option linter.checkUnivs false in
/-- **Definition 12.** -/
public structure SelfAwareDevice (U : Type u) where
  toDevice : InferenceDevice.{u, v} U
  Question : Type w
  question : U → Question
  eval : Question → U → Bool
  pair_surjective :
    Function.Surjective (fun u : U => (toDevice.concl u, question u))

/-- The source's overline operator `Q̄`. -/
@[expose] public def SelfAwareDevice.ask (D : SelfAwareDevice.{u, v, w} U)
    (u : U) : Bool :=
  D.eval (D.question u) u

/-- **Definition 13(i).** -/
@[expose] public def Intelligible (D : SelfAwareDevice.{u, v, w} U)
    {G : Type v'} (Γ : U → G) : Prop :=
  ∀ (γ : G) (f : G → Bool), IsProbe f γ → (∃ w, Γ w = γ) →
    ∃ q : D.Question, (∃ u, D.question u = q) ∧ ∀ u, D.eval q u = f (Γ u)

/-- **Definition 13(ii).** -/
@[expose] public def Infallible (D : SelfAwareDevice.{u, v, w} U) : Prop :=
  ∀ u : U, D.toDevice.concl u = D.ask u

/-- **Definition 13(ii), relativized**, from the sentence after the printed clause:

> *"We say that `D` is infallible for `Q₀ ⊆ Q(U)` iff `∀q ∈ Q₀`, `∀u ∈ U` such
> that `Q(u) = q`, `Y(u) = q(u)`."*

Footnote 9's alternative definition of *correction* is stated in terms of this, so
it is not optional vocabulary. -/
@[expose] public def InfallibleFor (D : SelfAwareDevice.{u, v, w} U)
    (Q₀ : Set D.Question) : Prop :=
  ∀ q ∈ Q₀, ∀ u : U, D.question u = q → D.toDevice.concl u = D.eval q u

/-- The source's *"`D` is infallible iff it is infallible for `Q(U)`"*. -/
public theorem infallible_iff_infallibleFor_realized (D : SelfAwareDevice.{u, v, w} U) :
    Infallible D ↔ InfallibleFor D {q | ∃ u, D.question u = q} := by
  constructor
  · intro h q _ u hu
    rw [← hu]
    exact h u
  · intro h u
    exact h (D.question u) ⟨u, rfl⟩ u rfl

/-- Unrealized questions constrain nothing, so the whole label type works too. -/
public theorem infallible_iff_infallibleFor_univ (D : SelfAwareDevice.{u, v, w} U) :
    Infallible D ↔ InfallibleFor D Set.univ := by
  constructor
  · intro h q _ u hu
    rw [← hu]
    exact h u
  · intro h u
    exact h (D.question u) (Set.mem_univ _) u rfl

/-- Full infallibility gives infallibility for every set of questions. -/
public theorem InfallibleFor.of_infallible {D : SelfAwareDevice.{u, v, w} U}
    (h : Infallible D) (Q₀ : Set D.Question) : InfallibleFor D Q₀ := by
  intro q _ u hu
  rw [← hu]
  exact h u

/-- `D'` is intelligible to `D` when `(Y', Q')` is. -/
@[expose] public def DeviceIntelligible (D : SelfAwareDevice.{u, v, w} U)
    (D' : SelfAwareDevice.{u, v', w'} U) : Prop :=
  Intelligible D (fun u => (D'.toDevice.concl u, D'.question u))

/-- **Theorem 6(i).** -/
public theorem weaklyInfers_of_infallible_semiControls_question
    (D : SelfAwareDevice.{u, v, w} U) (hinf : Infallible D)
    (hs : SemiControls D.toDevice D.question)
    {G : Type v'} (Γ : U → G) (hint : Intelligible D Γ) :
    WeaklyInfers D.toDevice Γ := by
  intro γ f hf hγ
  obtain ⟨q, hqR, hq⟩ := hint γ f hf hγ
  obtain ⟨x, hx, hsub⟩ := hs q hqR
  refine ⟨x, hx, fun w hw => ?_⟩
  simpa [SelfAwareDevice.ask, hsub w hw, hq] using hinf w

/-- **Theorem 6(ii).** The source's extra hypothesis is that `(Q₁, X₂)` is
surjective *onto `Q₁(U) × X₂(U)`* — the product of the two **images**, not of the
two types. `hsurj` says exactly that: any realized question pairs with any realized
setup value. An earlier revision asked for surjectivity onto the ambient product
`D.Question × C₂.Setup`, which is strictly stronger whenever either function misses
a value of its type. See clash 10. -/
public theorem stronglyInfers_of_infallible_semiControls_question_setup
    (D : SelfAwareDevice.{u, v, w} U) (hinf : Infallible D)
    {C₂ : InferenceDevice.{u, v'} U}
    (hs : SemiControls D.toDevice (fun u => (D.question u, C₂.setup u)))
    (hsurj : ∀ (q : D.Question) (x₂ : C₂.Setup),
      (∃ u, D.question u = q) → C₂.Realized x₂ → ∃ u, D.question u = q ∧ C₂.setup u = x₂)
    (hint : Intelligible D C₂.concl) :
    StronglyInfers D.toDevice C₂ := by
  intro γ f hf hγ x₂ hx₂
  obtain ⟨q, hqR, hq⟩ := hint γ f hf hγ
  obtain ⟨u₀, hu₀⟩ : ∃ u, (fun u => (D.question u, C₂.setup u)) u = (q, x₂) := by
    obtain ⟨u, hu1, hu2⟩ := hsurj q x₂ hqR hx₂
    exact ⟨u, Prod.ext hu1 hu2⟩
  obtain ⟨x, hx, hsub⟩ := hs (q, x₂) ⟨u₀, hu₀⟩
  refine ⟨x, hx, fun w hw => ?_⟩
  have hpair := hsub w hw
  have hQ : D.question w = q := congrArg Prod.fst hpair
  have hX : C₂.setup w = x₂ := congrArg Prod.snd hpair
  refine ⟨hX, ?_⟩
  simpa [SelfAwareDevice.ask, hQ, hq] using hinf w

/-- The canonical probe at a realized value of `Γ`. -/
@[expose] public def canonProbe {G : Type v'} [DecidableEq G]
    {Γ : U → G} (z : {x // ∃ u, Γ u = x}) : G → Bool :=
  fun b => decide (b = z.1)

public theorem isProbe_canonProbe {G : Type v'} [DecidableEq G]
    {Γ : U → G} (z : {x // ∃ u, Γ u = x}) : IsProbe (canonProbe (Γ := Γ) z) z.1 :=
  fun b => by simp [canonProbe]

/-- The realized question that intelligibility supplies for the probe at `z`.
Paper Theorem 7: *each probe of `Γ` is a realized question.* -/
public noncomputable def intelligibleQuestion
    (D : SelfAwareDevice.{u, v, w} U) {G : Type v'} [DecidableEq G]
    {Γ : U → G} (hint : Intelligible D Γ) (z : {x // ∃ u, Γ u = x}) :
    {q // ∃ u, D.question u = q} :=
  ⟨(hint z.1 (canonProbe (Γ := Γ) z) (isProbe_canonProbe z) z.2).choose,
    (hint z.1 (canonProbe (Γ := Γ) z) (isProbe_canonProbe z) z.2).choose_spec.1⟩

public theorem intelligibleQuestion_eval
    (D : SelfAwareDevice.{u, v, w} U) {G : Type v'} [DecidableEq G]
    {Γ : U → G} (hint : Intelligible D Γ) (z : {x // ∃ u, Γ u = x}) :
    D.eval (intelligibleQuestion D hint z).1 = fun u => canonProbe (Γ := Γ) z (Γ u) :=
  funext (hint z.1 (canonProbe (Γ := Γ) z) (isProbe_canonProbe z) z.2).choose_spec.2

public theorem intelligibleQuestion_injective
    (D : SelfAwareDevice.{u, v, w} U) {G : Type v'} [DecidableEq G]
    {Γ : U → G} (hint : Intelligible D Γ) :
    Function.Injective (intelligibleQuestion D hint) := by
  intro a b hφ
  have hq : (intelligibleQuestion D hint a).1 = (intelligibleQuestion D hint b).1 :=
    congrArg Subtype.val hφ
  obtain ⟨ua, hua⟩ := a.2
  have heq : canonProbe (Γ := Γ) a (Γ ua) = canonProbe (Γ := Γ) b (Γ ua) := by
    have ha := congrFun (intelligibleQuestion_eval D hint a) ua
    have hb := congrFun (intelligibleQuestion_eval D hint b) ua
    rw [← ha, ← hb, hq]
  have : a.1 = b.1 := by
    simp [canonProbe, hua] at heq
    exact heq
  exact Subtype.ext this

/-- **Theorem 7(i), special case used by Corollary 4.** Each realized value
of `Γ` injects into the realized questions of an intelligible device, so
`|Q(U)| ≥ |Γ(U)|`. -/
public theorem card_image_le_questions_of_intelligible
    (D : SelfAwareDevice.{u, v, w} U) {G : Type v'} [DecidableEq G]
    (Γ : U → G)
    [Fintype {x // ∃ u, D.question u = x}]
    [Fintype {x // ∃ u, Γ u = x}]
    (hint : Intelligible D Γ) :
    Fintype.card {x // ∃ u, Γ u = x} ≤
      Fintype.card {x // ∃ u, D.question u = x} :=
  Fintype.card_le_of_injective _ (intelligibleQuestion_injective D hint)

/-- `|(Y,Q)(U)| = 2|Q(U)|` because `Y⊗Q` is surjective (Definition 12). -/
public theorem card_pair_eq_two_mul_questions
    (E : SelfAwareDevice.{u, v, w} U)
    [Fintype {x // ∃ u, E.question u = x}]
    [Fintype {p : Bool × E.Question // ∃ u,
      (E.toDevice.concl u, E.question u) = p}] :
    Fintype.card {p : Bool × E.Question // ∃ u,
      (E.toDevice.concl u, E.question u) = p} =
      2 * Fintype.card {x // ∃ u, E.question u = x} := by
  let e :
      {p : Bool × E.Question // ∃ u,
        (E.toDevice.concl u, E.question u) = p} ≃
      Bool × {x // ∃ u, E.question u = x} :=
    { toFun := fun p =>
        (p.1.1, ⟨p.1.2, p.2.imp (fun u hu => congrArg Prod.snd hu)⟩)
      invFun := fun z =>
        ⟨(z.1, z.2.1), E.pair_surjective (z.1, z.2.1)⟩
      left_inv := fun p => Subtype.ext (by
        obtain ⟨⟨b, q⟩, hp⟩ := p; rfl)
      right_inv := fun z => by obtain ⟨b, q⟩ := z; rfl }
  calc
    Fintype.card {p : Bool × E.Question // ∃ u,
        (E.toDevice.concl u, E.question u) = p}
        = Fintype.card (Bool × {x // ∃ u, E.question u = x}) :=
      Fintype.card_congr e
    _ = 2 * Fintype.card {x // ∃ u, E.question u = x} := by
        simp [Fintype.card_prod]

/-- **Corollary 4.** Mutual intelligibility of the pairs `(Y, Q)` is
impossible for finite question images: `|Q| ≥ |(Y',Q')| = 2|Q'|` and
symmetrically. -/
public theorem not_mutually_deviceIntelligible_of_finite
    (D : SelfAwareDevice.{u, v, w} U) (D' : SelfAwareDevice.{u, v', w'} U)
    [DecidableEq D.Question] [DecidableEq D'.Question]
    [Fintype {x // ∃ u, D.question u = x}]
    [Fintype {x // ∃ u, D'.question u = x}]
    [Fintype {p : Bool × D'.Question // ∃ u,
      (D'.toDevice.concl u, D'.question u) = p}]
    [Fintype {p : Bool × D.Question // ∃ u,
      (D.toDevice.concl u, D.question u) = p}]
    (h : DeviceIntelligible D D') (h' : DeviceIntelligible D' D) : False := by
  have hle := card_image_le_questions_of_intelligible D
    (fun u => (D'.toDevice.concl u, D'.question u)) h
  have hle' := card_image_le_questions_of_intelligible D'
    (fun u => (D.toDevice.concl u, D.question u)) h'
  have hD := card_pair_eq_two_mul_questions D
  have hD' := card_pair_eq_two_mul_questions D'
  have hle2 : 2 * Fintype.card {x // ∃ u, D'.question u = x} ≤
      Fintype.card {x // ∃ u, D.question u = x} := by
    rw [← hD']; exact hle
  have hle2' : 2 * Fintype.card {x // ∃ u, D.question u = x} ≤
      Fintype.card {x // ∃ u, D'.question u = x} := by
    rw [← hD]; exact hle'
  have hpos : 0 < Fintype.card {x // ∃ u, D.question u = x} := by
    obtain ⟨w, _⟩ := D.toDevice.concl_surjective true
    exact Fintype.card_pos_iff.mpr ⟨⟨D.question w, ⟨w, rfl⟩⟩⟩
  nlinarith

/-- **Definition 14.** `C` corrects `D` when some setup fibre reports
whether `D` is answering its own question. -/
@[expose] public def Corrects (C : InferenceDevice.{u, v} U)
    (D : SelfAwareDevice.{u, v', w'} U) : Prop :=
  ∃ x : C.Setup, C.Realized x ∧
    ∀ w, C.setup w = x →
      C.concl w = decide (D.toDevice.concl w = D.ask w)

/-- A Definition-12 witness in the Atlas's relaxed model: same conclusion, one
constantly-false question (`PUnit` so the question universe matches). The paper's
two-question construction `Q ∈ {Y, ¬Y}` makes `Y⊗Q` miss two of the four pairs.
The replacement satisfies Definition 12, but not the paper's separate global
convention that every function considered has at least two image values; this is
why Proposition 7 remains `REPAIRED`, not source-exact. See the tracked source-
clash note. -/
public def uncorrectable (C : InferenceDevice.{u, v} U) :
    SelfAwareDevice.{u, v, w} U where
  toDevice := C
  Question := PUnit.{w + 1}
  question := fun _ => PUnit.unit
  eval := fun _ _ => false
  pair_surjective := by
    intro p
    obtain ⟨w, hw⟩ := C.concl_surjective p.1
    exact ⟨w, Prod.ext hw (by cases p.2; rfl)⟩

/-- The source's `Y₂ Q̄₂`: `true` exactly where the device answers its own
question. Definition 14 asks a second device to report this function. -/
@[expose] public def agreesWithQuestion (D : SelfAwareDevice.{u, v, w} U) : U → Bool :=
  fun u => decide (D.toDevice.concl u = D.ask u)

/-- **Footnote 9's alternative definition of correction.**

> *"Then we can modify the definition to say that `D₁` corrects `D₂` iff two
> conditions are met: all probes in `π(Y₂ Q̄₂)` are intelligible to `D₁`, and `D₁`
> is infallible for `π(Y₂ Q̄₂)`."*

Two things the footnote does not say, recorded rather than smoothed over:

* Definition 14's `D₁` is a **plain device**. This variant needs it to be
  **self-aware**, since intelligibility and infallibility are both defined only
  for those. The signature says so.
* `π(Y₂ Q̄₂)` is a set of probe *functions*, while `InfallibleFor` takes a set of
  `D₁`'s question labels. The two agree in the source, where `Q(U)` **is** a set of
  functions; here the second clause ranges over those labels of `D₁` whose
  evaluation is such a probe, which is the label-model reading of
  `π(Y₂ Q̄₂) ∩ Q₁(U)`.

No relation to `Corrects` is claimed. The footnote presents this as a different
definition, and Proposition 7 is stated for Definition 14. -/
@[expose] public def CorrectsAlt (C : SelfAwareDevice.{u, v, w} U)
    (D : SelfAwareDevice.{u, v', w'} U) : Prop :=
  Intelligible C (agreesWithQuestion D) ∧
    InfallibleFor C {q : C.Question |
      ∃ (γ : Bool) (f : Bool → Bool), IsProbe f γ ∧
        C.eval q = fun u => f (agreesWithQuestion D u)}

/-- An infallible device meets the second of footnote 9's two conditions for free,
so the variant reduces to intelligibility of `Y₂ Q̄₂` there. -/
public theorem correctsAlt_iff_intelligible_of_infallible
    {C : SelfAwareDevice.{u, v, w} U} {D : SelfAwareDevice.{u, v', w'} U}
    (h : Infallible C) :
    CorrectsAlt C D ↔ Intelligible C (agreesWithQuestion D) :=
  ⟨fun hc => hc.1, fun hi => ⟨hi, InfallibleFor.of_infallible h _⟩⟩

/-- **Proposition 7.** `ask` is constantly false, so a correcting fibre
would require `Y = decide (Y = false)`, i.e. `Y = ¬Y`. -/
public theorem exists_not_corrects (C : InferenceDevice.{u, v} U) :
    ∃ D : SelfAwareDevice.{u, v, w} U, ¬ Corrects C D := by
  refine ⟨uncorrectable C, ?_⟩
  intro ⟨x, hx, hfib⟩
  obtain ⟨w, hw⟩ := hx
  have h := hfib w hw
  -- `h` reduces to `Y = decide (Y = false)`, i.e. `Y = !Y`. `simp` no longer
  -- closes that on its own, so the two cases are named.
  simp [uncorrectable, SelfAwareDevice.ask] at h
  cases hY : C.concl w <;> simp [hY] at h

/-- **Theorem 7(i).** v2 writes the hypothesis twice as “`P` intelligible
to `D′`”; the proof uses `P` intelligible to `D′` and `P′` intelligible
to `D`. Then `|Q(U)| = |Q′(U)| = |P(U)| = |P′(U)|`. -/
public theorem thm7_card
    (D : SelfAwareDevice.{u, v, w} U) (D' : SelfAwareDevice.{u, v', w'} U)
    {P P' : Type*} [DecidableEq P] [DecidableEq P']
    (pMap : U → P) (pMap' : U → P')
    (R : P → D.Question) (R' : P' → D'.Question)
    (hQ : ∀ u, D.question u = R (pMap u))
    (hQ' : ∀ u, D'.question u = R' (pMap' u))
    (hint : Intelligible D' pMap) (hint' : Intelligible D pMap')
    [Fintype {x // ∃ u, D.question u = x}]
    [Fintype {x // ∃ u, D'.question u = x}]
    [Fintype {x // ∃ u, pMap u = x}]
    [Fintype {x // ∃ u, pMap' u = x}] :
    Fintype.card {x // ∃ u, D.question u = x} =
      Fintype.card {x // ∃ u, D'.question u = x} ∧
    Fintype.card {x // ∃ u, D.question u = x} =
      Fintype.card {x // ∃ u, pMap u = x} ∧
    Fintype.card {x // ∃ u, D'.question u = x} =
      Fintype.card {x // ∃ u, pMap' u = x} := by
  classical
  have hQleP : Fintype.card {x // ∃ u, D.question u = x} ≤
      Fintype.card {x // ∃ u, pMap u = x} := by
    let φ (z : {x // ∃ u, D.question u = x}) :
        {x // ∃ u, pMap u = x} :=
      ⟨pMap z.2.choose, ⟨z.2.choose, rfl⟩⟩
    refine Fintype.card_le_of_injective φ ?_
    intro a b hab
    have hp : pMap a.2.choose = pMap b.2.choose := congrArg Subtype.val hab
    apply Subtype.ext
    calc
      a.1 = D.question a.2.choose := (a.2.choose_spec).symm
      _ = R (pMap a.2.choose) := hQ _
      _ = R (pMap b.2.choose) := congrArg R hp
      _ = D.question b.2.choose := (hQ _).symm
      _ = b.1 := b.2.choose_spec
  have hQ'leP' : Fintype.card {x // ∃ u, D'.question u = x} ≤
      Fintype.card {x // ∃ u, pMap' u = x} := by
    let φ (z : {x // ∃ u, D'.question u = x}) :
        {x // ∃ u, pMap' u = x} :=
      ⟨pMap' z.2.choose, ⟨z.2.choose, rfl⟩⟩
    refine Fintype.card_le_of_injective φ ?_
    intro a b hab
    have hp : pMap' a.2.choose = pMap' b.2.choose := congrArg Subtype.val hab
    apply Subtype.ext
    calc
      a.1 = D'.question a.2.choose := (a.2.choose_spec).symm
      _ = R' (pMap' a.2.choose) := hQ' _
      _ = R' (pMap' b.2.choose) := congrArg R' hp
      _ = D'.question b.2.choose := (hQ' _).symm
      _ = b.1 := b.2.choose_spec
  have hPleQ' := card_image_le_questions_of_intelligible D' pMap hint
  have hP'leQ := card_image_le_questions_of_intelligible D pMap' hint'
  have hQQ' : Fintype.card {x // ∃ u, D.question u = x} =
      Fintype.card {x // ∃ u, D'.question u = x} :=
    Nat.le_antisymm (hQleP.trans hPleQ') (hQ'leP'.trans hP'leQ)
  refine ⟨hQQ', Nat.le_antisymm hQleP ?_, Nat.le_antisymm hQ'leP' ?_⟩
  · calc
      Fintype.card {x // ∃ u, pMap u = x}
          ≤ Fintype.card {x // ∃ u, D'.question u = x} := hPleQ'
      _ = Fintype.card {x // ∃ u, D.question u = x} := hQQ'.symm
  · calc
      Fintype.card {x // ∃ u, pMap' u = x}
          ≤ Fintype.card {x // ∃ u, D.question u = x} := hP'leQ
      _ = Fintype.card {x // ∃ u, D'.question u = x} := hQQ'

/-! ## Theorem 7(i) without finiteness

The source puts *"if `Q(U)` is finite"* in **(ii)**. Its **(i)** is an unrestricted
cardinality equality, so `Fintype.card` is a restriction the printed statement does
not carry. `Cardinal.mk` removes it: the three inequalities are the same
injections, and antisymmetry on `Cardinal` is Schröder–Bernstein, which is exactly
what the printed proof appeals to when it says two cardinalities that each dominate
the other are equal.

One restriction remains, and it is Lean's rather than the paper's: `Cardinal.mk`
compares types in a single universe, so the four types here share one. `thm7_card`
stays as the finite instance, where `Fintype.card : ℕ` sidesteps universes
entirely.
-/

/-- Theorem 7(i)'s injection, without finiteness. -/
public theorem mk_image_le_questions_of_intelligible
    (D : SelfAwareDevice.{u, v, w} U) {G : Type w} [DecidableEq G]
    (Γ : U → G) (hint : Intelligible D Γ) :
    Cardinal.mk {x // ∃ u, Γ u = x} ≤ Cardinal.mk {q // ∃ u, D.question u = q} :=
  Cardinal.mk_le_of_injective (intelligibleQuestion_injective D hint)

/-- The realized questions inject into the labels their question map factors
through. Extracted from Theorem 7(i)'s proof, where it appeared twice inline,
and stated with the label type in its **own** universe. -/
@[expose] public noncomputable def questionLabel (D : SelfAwareDevice.{u, v, w} U)
    {P : Type p₀} (pMap : U → P) (R : P → D.Question)
    (_hQ : ∀ u, D.question u = R (pMap u))
    (z : {x // ∃ u, D.question u = x}) : {x // ∃ u, pMap u = x} :=
  ⟨pMap z.2.choose, ⟨z.2.choose, rfl⟩⟩

public theorem questionLabel_injective (D : SelfAwareDevice.{u, v, w} U)
    {P : Type p₀} (pMap : U → P) (R : P → D.Question)
    (hQ : ∀ u, D.question u = R (pMap u)) :
    Function.Injective (questionLabel D pMap R hQ) := by
  intro a b hab
  have hp : pMap a.2.choose = pMap b.2.choose := congrArg Subtype.val hab
  apply Subtype.ext
  calc
    a.1 = D.question a.2.choose := (a.2.choose_spec).symm
    _ = R (pMap a.2.choose) := hQ _
    _ = R (pMap b.2.choose) := congrArg R hp
    _ = D.question b.2.choose := (hQ _).symm
    _ = b.1 := b.2.choose_spec

/--
**Theorem 7(i) with no universe restriction at all.**

`thm7_mk` compares four types with `Cardinal.mk`, which forces them into one
universe — the last restriction the 2008 map recorded as *"Lean's, not the
paper's"*. Stating the conclusion as `Nonempty (· ≃ ·)` removes it: `Equiv` is
defined across universes, and `Function.Embedding.antisymm` is the
Schröder–Bernstein step in that form. The two question types, and the two label
types, now live in four independent universes.

Equal cardinality is exactly what a bijection is, so nothing is weakened; in a
single universe `Cardinal.eq` turns each conjunct back into `thm7_mk`.
-/
public theorem thm7_equiv
    (D : SelfAwareDevice.{u, v, w} U) (D' : SelfAwareDevice.{u, v', w'} U)
    {P : Type p} {P' : Type p'} [DecidableEq P] [DecidableEq P']
    (pMap : U → P) (pMap' : U → P')
    (R : P → D.Question) (R' : P' → D'.Question)
    (hQ : ∀ u, D.question u = R (pMap u))
    (hQ' : ∀ u, D'.question u = R' (pMap' u))
    (hint : Intelligible D' pMap) (hint' : Intelligible D pMap') :
    Nonempty ({x // ∃ u, D.question u = x} ≃ {x // ∃ u, D'.question u = x}) ∧
      Nonempty ({x // ∃ u, D.question u = x} ≃ {x // ∃ u, pMap u = x}) ∧
      Nonempty ({x // ∃ u, D'.question u = x} ≃ {x // ∃ u, pMap' u = x}) := by
  classical
  -- Q ↪ P, P ↪ Q', Q' ↪ P', P' ↪ Q.
  let eQP : {x // ∃ u, D.question u = x} ↪ {x // ∃ u, pMap u = x} :=
    ⟨questionLabel D pMap R hQ, questionLabel_injective D pMap R hQ⟩
  let ePQ' : {x // ∃ u, pMap u = x} ↪ {x // ∃ u, D'.question u = x} :=
    ⟨intelligibleQuestion D' hint, intelligibleQuestion_injective D' hint⟩
  let eQ'P' : {x // ∃ u, D'.question u = x} ↪ {x // ∃ u, pMap' u = x} :=
    ⟨questionLabel D' pMap' R' hQ', questionLabel_injective D' pMap' R' hQ'⟩
  let eP'Q : {x // ∃ u, pMap' u = x} ↪ {x // ∃ u, D.question u = x} :=
    ⟨intelligibleQuestion D hint', intelligibleQuestion_injective D hint'⟩
  refine ⟨Function.Embedding.antisymm (eQP.trans ePQ') (eQ'P'.trans eP'Q), ?_, ?_⟩
  · exact Function.Embedding.antisymm eQP (ePQ'.trans (eQ'P'.trans eP'Q))
  · exact Function.Embedding.antisymm eQ'P' (eP'Q.trans (eQP.trans ePQ'))

/-- **Theorem 7(i), unrestricted.** `|Q(U)| = |Q′(U)| = |P(U)| = |P′(U)|`, with no
finiteness hypothesis anywhere. -/
public theorem thm7_mk
    (D : SelfAwareDevice.{u, v, w} U) (D' : SelfAwareDevice.{u, v', w} U)
    {P P' : Type w} [DecidableEq P] [DecidableEq P']
    (pMap : U → P) (pMap' : U → P')
    (R : P → D.Question) (R' : P' → D'.Question)
    (hQ : ∀ u, D.question u = R (pMap u))
    (hQ' : ∀ u, D'.question u = R' (pMap' u))
    (hint : Intelligible D' pMap) (hint' : Intelligible D pMap') :
    Cardinal.mk {x // ∃ u, D.question u = x} =
        Cardinal.mk {x // ∃ u, D'.question u = x} ∧
      Cardinal.mk {x // ∃ u, D.question u = x} =
        Cardinal.mk {x // ∃ u, pMap u = x} ∧
      Cardinal.mk {x // ∃ u, D'.question u = x} =
        Cardinal.mk {x // ∃ u, pMap' u = x} := by
  classical
  have hQleP : Cardinal.mk {x // ∃ u, D.question u = x} ≤
      Cardinal.mk {x // ∃ u, pMap u = x} :=
    Cardinal.mk_le_of_injective (questionLabel_injective D pMap R hQ)
  have hQ'leP' : Cardinal.mk {x // ∃ u, D'.question u = x} ≤
      Cardinal.mk {x // ∃ u, pMap' u = x} :=
    Cardinal.mk_le_of_injective (questionLabel_injective D' pMap' R' hQ')
  have hPleQ' := mk_image_le_questions_of_intelligible D' pMap hint
  have hP'leQ := mk_image_le_questions_of_intelligible D pMap' hint'
  have hQQ' : Cardinal.mk {x // ∃ u, D.question u = x} =
      Cardinal.mk {x // ∃ u, D'.question u = x} :=
    le_antisymm (hQleP.trans hPleQ') (hQ'leP'.trans hP'leQ)
  exact ⟨hQQ', le_antisymm hQleP (hPleQ'.trans hQQ'.ge),
    le_antisymm hQ'leP' (hP'leQ.trans hQQ'.le)⟩

/-! ## Theorem 7(ii) — the realized questions *are* the probes

The source concludes an equality of **sets of functions** on `U`:
`Q′ = π(P) = π(Q)`. Questions here are a label type plus `eval`, so the
comparison is made after evaluation: `evalImage` is the set of binary functions
the device can actually ask, which is the source's `Q(U)`. Two labels with equal
`eval` collapse to one element of `evalImage`, exactly as the source's function
set would have them.
-/

/-- The source's `Q(U)`: the binary functions on `U` that `D` can ask,
recovered from the label model by evaluation. -/
@[expose] public def evalImage (D : SelfAwareDevice.{u, v, w} U) : Set (U → Bool) :=
  {g | ∃ q : D.Question, (∃ u, D.question u = q) ∧ D.eval q = g}

/-- The source's `π(P)`: probes of `P` at realized values, composed with `P`. -/
@[expose] public def probeImage {P : Type v'} (pMap : U → P) : Set (U → Bool) :=
  {g | ∃ (γ : P) (f : P → Bool), IsProbe f γ ∧ (∃ u, pMap u = γ) ∧
        g = fun u => f (pMap u)}

/-- Intelligibility is exactly `π(P) ⊆ Q(U)`. This direction needs no finiteness. -/
public theorem probeImage_subset_evalImage
    (D : SelfAwareDevice.{u, v, w} U) {P : Type v'} {pMap : U → P}
    (hint : Intelligible D pMap) : probeImage pMap ⊆ evalImage D := by
  rintro g ⟨γ, f, hf, hγ, rfl⟩
  obtain ⟨q, hqR, hev⟩ := hint γ f hf hγ
  exact ⟨q, hqR, funext hev⟩

/--
**Theorem 7(ii).** With `Q(U)` finite and `P` intelligible to `D`, the questions
`D` can ask are precisely the probes of `P`: `Q(U) = π(P)`.

The finiteness is the source's own (*"If `Q(U)` is finite"*). It is what turns the
probe-to-question injection into a bijection, which is the step from
Theorem 7(i)'s cardinality equality to the printed set equality.
-/
public theorem thm7_ii
    (D : SelfAwareDevice.{u, v, w} U) {P : Type v'} [DecidableEq P] {pMap : U → P}
    (hint : Intelligible D pMap)
    [Fintype {q // ∃ u, D.question u = q}]
    [Fintype {x // ∃ u, pMap u = x}]
    (hcard : Fintype.card {x // ∃ u, pMap u = x} =
      Fintype.card {q // ∃ u, D.question u = q}) :
    evalImage D = probeImage pMap := by
  classical
  have hbij : Function.Bijective (intelligibleQuestion D hint) :=
    (Fintype.bijective_iff_injective_and_card _).mpr
      ⟨intelligibleQuestion_injective D hint, hcard⟩
  refine Set.Subset.antisymm ?_ (probeImage_subset_evalImage D hint)
  rintro g ⟨q, hqR, rfl⟩
  obtain ⟨z, hz⟩ := hbij.2 ⟨q, hqR⟩
  have hq : (intelligibleQuestion D hint z).1 = q := congrArg Subtype.val hz
  refine ⟨z.1, canonProbe (Γ := pMap) z, isProbe_canonProbe z, z.2, ?_⟩
  rw [← hq]
  exact intelligibleQuestion_eval D hint z

/-! ### The other half of Theorem 7(ii): `π(P) = π(Q)`

Printed (ii) is a chain, not one equality: *"`Q′ = π(P) = π(Q)` and
`Q = π(P′) = π(Q′)`"*. `thm7_ii` gives the outer equalities. The inner ones come
from `Q = R(P)` with equally many realized values, which forces `R` to be injective
on the image, so `P` and `Q` induce the same partition of `U` and therefore have the
same probes.
-/

/-- Equal finite images and `Q = R(P)` force `R` injective on the realized image. -/
public theorem eq_of_apply_eq_of_card_eq {P : Type v'} {Q : Type v''}
    [DecidableEq P] [DecidableEq Q]
    {pMap : U → P} {qMap : U → Q} (R : P → Q) (hQ : ∀ u, qMap u = R (pMap u))
    [Fintype {x // ∃ u, pMap u = x}] [Fintype {x // ∃ u, qMap u = x}]
    (hcard : Fintype.card {x // ∃ u, pMap u = x} = Fintype.card {x // ∃ u, qMap u = x})
    {a b : P} (ha : ∃ u, pMap u = a) (hb : ∃ u, pMap u = b) (hab : R a = R b) :
    a = b := by
  classical
  let φ : {x // ∃ u, pMap u = x} → {x // ∃ u, qMap u = x} :=
    fun z => ⟨R z.1, by obtain ⟨u, hu⟩ := z.2; exact ⟨u, by rw [hQ u, hu]⟩⟩
  have hsurj : Function.Surjective φ := by
    rintro ⟨q, u, hu⟩
    exact ⟨⟨pMap u, ⟨u, rfl⟩⟩, Subtype.ext (by simp only [φ]; rw [← hQ u, hu])⟩
  have hbij : Function.Bijective φ :=
    (Fintype.bijective_iff_surjective_and_card φ).mpr ⟨hsurj, hcard⟩
  have := hbij.1 (a₁ := ⟨a, ha⟩) (a₂ := ⟨b, hb⟩) (Subtype.ext hab)
  exact congrArg Subtype.val this

/-- **Theorem 7(ii), inner equality.** `π(P) = π(Q)` when `Q = R(P)` and the two
images have the same finite cardinality. -/
public theorem probeImage_eq_of_card_eq {P : Type v'} {Q : Type v''}
    [DecidableEq P] [DecidableEq Q]
    {pMap : U → P} {qMap : U → Q} (R : P → Q) (hQ : ∀ u, qMap u = R (pMap u))
    [Fintype {x // ∃ u, pMap u = x}] [Fintype {x // ∃ u, qMap u = x}]
    (hcard : Fintype.card {x // ∃ u, pMap u = x} = Fintype.card {x // ∃ u, qMap u = x}) :
    probeImage pMap = probeImage qMap := by
  classical
  have hinj : ∀ {a b : P}, (∃ u, pMap u = a) → (∃ u, pMap u = b) → R a = R b → a = b :=
    fun ha hb hab => eq_of_apply_eq_of_card_eq (pMap := pMap) (qMap := qMap) R hQ hcard ha hb hab
  apply Set.Subset.antisymm
  · rintro g ⟨γ, f, hf, ⟨u₀, hu₀⟩, rfl⟩
    refine ⟨R γ, fun q => decide (q = R γ), fun q => by simp, ⟨u₀, by rw [hQ u₀, hu₀]⟩, ?_⟩
    funext u
    have : (decide (qMap u = R γ)) = (f (pMap u)) := by
      rw [hQ u]
      cases hfu : f (pMap u)
      · refine decide_eq_false (fun hc => ?_)
        exact absurd ((hf (pMap u)).mpr (hinj ⟨u, rfl⟩ ⟨u₀, hu₀⟩ hc)) (by rw [hfu]; simp)
      · exact decide_eq_true (congrArg R ((hf (pMap u)).mp hfu))
    exact this.symm
  · rintro g ⟨δ, f, hf, ⟨u₀, hu₀⟩, rfl⟩
    refine ⟨pMap u₀, fun p => decide (p = pMap u₀), fun p => by simp, ⟨u₀, rfl⟩, ?_⟩
    funext u
    have hδ : δ = R (pMap u₀) := by rw [← hu₀, hQ u₀]
    have : (decide (pMap u = pMap u₀)) = f (qMap u) := by
      cases hfu : f (qMap u)
      · refine decide_eq_false (fun hc => ?_)
        have : qMap u = δ := by rw [hQ u, hc, hδ]
        exact absurd ((hf (qMap u)).mpr this) (by rw [hfu]; simp)
      · have : qMap u = δ := (hf (qMap u)).mp hfu
        rw [hQ u, hδ] at this
        exact decide_eq_true (hinj ⟨u, rfl⟩ ⟨u₀, rfl⟩ this)
    exact this.symm

/--
**Theorem 7(ii), as printed.** *"If `Q(U)` is finite, `Q′ = π(P) = π(Q)` and
`Q = π(P′) = π(Q′)`."*

All four equalities, under Theorem 7's own hypotheses. The cardinality equalities
are discharged from `thm7_card` rather than assumed, so this is (ii) following from
(i) exactly as the source has it.
-/
public theorem thm7_ii_chain
    (D : SelfAwareDevice.{u, v, w} U) (D' : SelfAwareDevice.{u, v', w'} U)
    {P P' : Type*} [DecidableEq P] [DecidableEq P']
    [DecidableEq D.Question] [DecidableEq D'.Question]
    (pMap : U → P) (pMap' : U → P')
    (R : P → D.Question) (R' : P' → D'.Question)
    (hQ : ∀ u, D.question u = R (pMap u))
    (hQ' : ∀ u, D'.question u = R' (pMap' u))
    (hint : Intelligible D' pMap) (hint' : Intelligible D pMap')
    [Fintype {x // ∃ u, D.question u = x}]
    [Fintype {x // ∃ u, D'.question u = x}]
    [Fintype {x // ∃ u, pMap u = x}]
    [Fintype {x // ∃ u, pMap' u = x}] :
    evalImage D' = probeImage pMap ∧
      probeImage pMap = probeImage D.question ∧
      evalImage D = probeImage pMap' ∧
      probeImage pMap' = probeImage D'.question := by
  obtain ⟨hQQ', hQP, hQ'P'⟩ :=
    thm7_card D D' pMap pMap' R R' hQ hQ' hint hint'
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact thm7_ii D' hint (hQP.symm.trans hQQ')
  · exact probeImage_eq_of_card_eq R hQ hQP.symm
  · exact thm7_ii D hint' (hQ'P'.symm.trans hQQ'.symm)
  · exact probeImage_eq_of_card_eq R' hQ' hQ'P'.symm

/-- **Corollary 5.** Infallible, question-semi-controlling, distinguishable
devices cannot have each other's conclusions both intelligible (Thm 6(i)
would give mutual weak inference, contradicting Thm 1). -/
public theorem not_both_concl_intelligible
    (D₁ : SelfAwareDevice.{u, v, w} U) (D₂ : SelfAwareDevice.{u, v', w'} U)
    (hinf₁ : Infallible D₁) (hinf₂ : Infallible D₂)
    (hs₁ : SemiControls D₁.toDevice D₁.question)
    (hs₂ : SemiControls D₂.toDevice D₂.question)
    (hdist : Distinguishable D₁.toDevice D₂.toDevice)
    (hint₁ : Intelligible D₁ D₂.toDevice.concl)
    (hint₂ : Intelligible D₂ D₁.toDevice.concl) : False :=
  not_infersDevice_both_of_distinguishable hdist
    (weaklyInfers_of_infallible_semiControls_question D₁ hinf₁ hs₁
      D₂.toDevice.concl hint₁)
    (weaklyInfers_of_infallible_semiControls_question D₂ hinf₂ hs₂
      D₁.toDevice.concl hint₂)


/-! ## Self-aware inference complexity

Section 9 displays, in running prose rather than a numbered environment:

> *"one might want to modify the definition of inference complexity slightly for
> self-aware devices. Let `D` be a self-aware infallible device that
> semi-controls its question function and `Γ` a function over `U` where `Γ(U)` is
> countable and `Γ` is intelligible to `D`. Then rather than `𝒞(Γ ∣ (X,Y))`, it
> may be more appropriate to consider the self-aware inference complexity of `Γ`
> with respect to `D`, defined as*
>
> `𝒟(Γ ∣ (X,Y,Q)) ≜ Σ_{f ∈ π(Γ)} min_{x : X = x ⇒ Q = f(Γ)} [ℒ(x)]`

Definition 6 with the answering condition moved from the **conclusion** to the
**question**: a setup counts when it forces the device to be *asking* the probe,
regardless of what it then answers. Like `Ĉ`, it is a displayed definition that
no numbered environment announces.

**One interpretive choice, and it is Definition 12's.** `Q = f(Γ)` equates a
question with a function, and questions here are a label type plus `eval`
(clashes 9–10). The reading taken is the pointwise one already used by
`Intelligible`: the label the device asks at `u` *denotes* `f ∘ Γ`, i.e.
`∀ v, eval (question u) v = f (Γ v)`. That is the only reading under which the
source's own hypothesis — `Γ` intelligible to `D` — supplies the questions the
minimum ranges over.

The source's standing hypotheses for this display (infallible, semi-controls its
question function, `Γ(U)` countable, `Γ` intelligible) are **not** attached: the
object is defined for every self-aware device, and `ℒ` is a parameter as in
`inferenceComplexityTotal`, so counting measure and `−ln μ(X⁻¹(x))` are both
instances.
-/

open scoped Classical in
/-- The setups whose fibre forces the device to be **asking** the probe `f` of
`Γ` — the source's `X = x ⇒ Q = f(Γ)`. -/
@[expose] public noncomputable def questionAnsweringSet (D : SelfAwareDevice.{u, v, w} U)
    [DecidableEq D.toDevice.Setup] [FiniteRange D.toDevice.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) : Finset D.toDevice.Setup :=
  (realizedSetups D.toDevice).filter fun x =>
    ∀ u : U, D.toDevice.setup u = x → ∀ v : U, D.eval (D.question u) v = f (Γ v)

/-- The cheapest such setup, totalized by `0` where none exists — as
`minAnsweringLength` is. -/
@[expose] public noncomputable def minQuestionLength (D : SelfAwareDevice.{u, v, w} U)
    [DecidableEq D.toDevice.Setup] [FiniteRange D.toDevice.setup]
    (ℓ : D.toDevice.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  if h : (questionAnsweringSet D Γ f).Nonempty then
    (questionAnsweringSet D Γ f).inf' h ℓ
  else 0

/-- **Self-aware inference complexity**, `𝒟(Γ ∣ (X,Y,Q))`. -/
@[expose] public noncomputable def selfAwareInferenceComplexity
    (D : SelfAwareDevice.{u, v, w} U)
    [DecidableEq D.toDevice.Setup] [FiniteRange D.toDevice.setup]
    (ℓ : D.toDevice.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G)
    [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum fun γ => minQuestionLength D ℓ Γ (probe γ)

open scoped Classical in
/-- Membership, stated so callers never match the `Finset.filter` decidability
instance this module's classical opening picks. -/
public theorem mem_questionAnsweringSet_iff (D : SelfAwareDevice.{u, v, w} U)
    [DecidableEq D.toDevice.Setup] [FiniteRange D.toDevice.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) (x : D.toDevice.Setup) :
    x ∈ questionAnsweringSet D Γ f ↔
      D.toDevice.Realized x ∧
        ∀ u : U, D.toDevice.setup u = x → ∀ v : U, D.eval (D.question u) v = f (Γ v) := by
  unfold questionAnsweringSet realizedSetups
  rw [Finset.mem_filter, mem_rangeFinset]
  exact Iff.rfl

/-- **An infallible device that asks the probe also answers it.** So on the
setups `𝒟` charges for, the device's conclusion is correct — which is why the
source can call `𝒟` a complexity of *inference* and not merely of asking. -/
public theorem concl_eq_of_mem_questionAnsweringSet {D : SelfAwareDevice.{u, v, w} U}
    [DecidableEq D.toDevice.Setup] [FiniteRange D.toDevice.setup]
    {G : Type v'} {Γ : U → G} {f : G → Bool} {x : D.toDevice.Setup}
    (hinf : Infallible D) (hx : x ∈ questionAnsweringSet D Γ f)
    (u : U) (hu : D.toDevice.setup u = x) :
    D.toDevice.concl u = f (Γ u) := by
  have hq := ((mem_questionAnsweringSet_iff D Γ f x).mp hx).2 u hu u
  rw [hinf u]
  exact hq


/-! ### Why Proposition 7 has no source-admissible witness on a small universe

`uncorrectable` takes `Question := PUnit`, one question value, and so violates
the paper's §1.2 stipulation that every function considered takes at least two
values. That is why Proposition 7 is graded `REPAIRED` rather than
`SOURCE-EXACT`, and it raises the question of whether an admissible witness
exists at all.

Half of that question has a short answer. Definition 12's `pair_surjective`
makes `u ↦ (Y(u), Q(u))` **onto** `𝔹 × Q(U)`, so an admissible self-aware
device — one whose question map takes at least two values, as §1.2 requires —
needs at least four states to exist. On `|U| ∈ {2, 3}` there is no admissible
self-aware device whatever, so the printed *"there is a self-aware device that
`C` cannot correct"* has nothing to quantify over and fails there.

The other half — whether an admissible witness exists for **every** device once
`|U| ≥ 4` — is open. It is not the same construction: `uncorrectable` sets
`D.toDevice := C`, and that choice cannot generally be made admissible, since
`(Y, Q)` surjective onto `𝔹 × Q(U)` fails outright when one of `C`'s conclusion
fibres is a singleton.
-/

/-- **Definition 12 costs four states.** If a self-aware device's question map
takes two distinct values, `pair_surjective` forces four distinct states of `U`:
the four preimages of `(true, q₁)`, `(true, q₂)`, `(false, q₁)`, `(false, q₂)`
are pairwise distinct because their images are. -/
public theorem four_states_of_two_questions (D : SelfAwareDevice.{u, v, w} U)
    {q₁ q₂ : D.Question} (hq : q₁ ≠ q₂) :
    ∃ a b c d : U, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d := by
  obtain ⟨a, ha⟩ := D.pair_surjective (true, q₁)
  obtain ⟨b, hb⟩ := D.pair_surjective (true, q₂)
  obtain ⟨c, hc⟩ := D.pair_surjective (false, q₁)
  obtain ⟨d, hd⟩ := D.pair_surjective (false, q₂)
  refine ⟨a, b, c, d, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    intro h <;> subst h <;> simp_all

/-- The same fact as a cardinality bound: an admissible self-aware device needs
a universe of at least four states, so `\|U\| ∈ {2, 3}` admits none. -/
public theorem four_le_card_of_two_questions [Fintype U]
    (D : SelfAwareDevice.{u, v, w} U) {q₁ q₂ : D.Question} (hq : q₁ ≠ q₂) :
    4 ≤ Fintype.card U := by
  classical
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd⟩ :=
    four_states_of_two_questions D hq
  have hsub : ({a, b, c, d} : Finset U) ⊆ Finset.univ := Finset.subset_univ _
  have hcard : ({a, b, c, d} : Finset U).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hab, hac, had]),
      Finset.card_insert_of_notMem (by simp [hbc, hbd]),
      Finset.card_insert_of_notMem (by simp [hcd]), Finset.card_singleton]
  calc (4 : ℕ) = ({a, b, c, d} : Finset U).card := hcard.symm
  _ ≤ Fintype.card U := Finset.card_le_univ _

/-- **No admissible self-aware device exists on fewer than four states.**
`pair_surjective` is onto `𝔹 × Q(U)` — the whole question *type* — so a universe
of fewer than four states forces the question type to be a subsingleton, and the
question map is then constant. -/
public theorem question_subsingleton_of_card_lt_four [Fintype U]
    (D : SelfAwareDevice.{u, v, w} U) (h : Fintype.card U < 4) :
    Subsingleton D.Question := by
  refine ⟨fun q₁ q₂ => ?_⟩
  by_contra hq
  exact absurd (four_le_card_of_two_questions D hq) (by omega)

/--
**Proposition 7 is false on a small universe, under the paper's own convention.**

The printed claim is *"for every device there **is** a self-aware device it
cannot correct"*. On a universe of fewer than four states there is no
source-admissible self-aware device **at all**: every one of them has a constant
question map, and §1.2 stipulates that every function considered takes at least
two values. So the printed existential has nothing to range over.

This is the decisive artifact for clash 2. `exists_not_corrects` repairs the
proposition by dropping the two-value convention; this theorem shows the
convention cannot be kept on a small universe, so the repair is not a matter of
taste. `U = Bool` is the smallest instance and `Fin 2`, `Fin 3` are the others.
-/
public theorem question_constant_of_card_lt_four [Fintype U]
    (D : SelfAwareDevice.{u, v, w} U) (h : Fintype.card U < 4) (u u' : U) :
    D.question u = D.question u' :=
  (question_subsingleton_of_card_lt_four D h).allEq _ _

/-- The same on the smallest universe that carries a device at all. Every
self-aware device over `𝔹` has a one-valued question map, so none is admissible
and Proposition 7's witness cannot exist there. -/
public theorem no_admissible_selfAware_on_bool (D : SelfAwareDevice.{0, v, w} Bool)
    (u u' : Bool) : D.question u = D.question u' :=
  question_constant_of_card_lt_four D (by simp) u u'



/-! ## Definition 12 as the source prints it, and the encoding that represents it

Clash 9 records that questions here are a **label type plus `eval`** where the
source's `Q(U)` is a set of binary functions on `U`, and argues the encoding is a
generalization rather than a distortion: *"instantiating `Question` as the
source's `Q(U)` with `eval := id` recovers the printed model."* That was an
argument, not a theorem. It is a theorem now.

`FunctionValuedSelfAware` is Definition 12 read literally — a device together
with one binary function per state, and the printed surjectivity of `Y ⊗ Q` onto
`𝔹 × Q(U)`. `toSelfAware` is the representation, and the three theorems after it
say the representation loses nothing: the source's `Q̄` is the encoding's `ask`,
the evaluated questions are exactly the printed `Q(U)`, and the round trip is the
identity on both.
-/

/-- **Definition 12 as printed.** `Q` assigns a binary function on `U` to each
state, and `Y ⊗ Q` is onto `𝔹 × Q(U)` — the product with the **image**, which is
what the source writes. -/
public structure FunctionValuedSelfAware (U : Type u) where
  /-- The underlying device. -/
  toDevice : InferenceDevice.{u, v} U
  /-- The question at a state, as a binary function on `U`. -/
  askOf : U → (U → Bool)
  /-- `Y ⊗ Q` is onto `𝔹 × Q(U)`. -/
  pair_surjective : ∀ (b : Bool) (f : U → Bool), (∃ u, askOf u = f) →
    ∃ u, toDevice.concl u = b ∧ askOf u = f

/-- The printed device, represented in the label encoding: take the labels to be
the image of `Q` and `eval` to be the inclusion. -/
@[expose] public def FunctionValuedSelfAware.toSelfAware
    (F : FunctionValuedSelfAware.{u, v} U) : SelfAwareDevice.{u, v, u} U where
  toDevice := F.toDevice
  Question := {f : U → Bool // ∃ u, F.askOf u = f}
  question := fun u => ⟨F.askOf u, u, rfl⟩
  eval := fun f => f.1
  pair_surjective := by
    rintro ⟨b, ⟨f, u₀, hu₀⟩⟩
    obtain ⟨u, hb, hf⟩ := F.pair_surjective b f ⟨u₀, hu₀⟩
    exact ⟨u, by simp [hb, Subtype.ext_iff]; exact hf⟩

/-- **The source's `Q̄` is the encoding's `ask`.** Definition 12's overline
operator is *"the question at `u`, evaluated at `u`"*, and that survives the
representation unchanged. -/
public theorem FunctionValuedSelfAware.toSelfAware_ask
    (F : FunctionValuedSelfAware.{u, v} U) (u : U) :
    F.toSelfAware.ask u = F.askOf u u := rfl

/-- **No question is added and none is lost.** The evaluated questions of the
representation are exactly the printed `Q(U)`. This is the statement clash 9
needed: labels with equal `eval` collapse, and here there are none to collapse
because the labels *are* the functions. -/
public theorem FunctionValuedSelfAware.evalImage_toSelfAware
    (F : FunctionValuedSelfAware.{u, v} U) :
    evalImage F.toSelfAware = {g | ∃ u, F.askOf u = g} := by
  ext g
  constructor
  · rintro ⟨q, ⟨u, hu⟩, rfl⟩
    exact ⟨u, by rw [← hu]; rfl⟩
  · rintro ⟨u, rfl⟩
    exact ⟨⟨F.askOf u, u, rfl⟩, ⟨u, rfl⟩, rfl⟩

/-- The other direction: every device in the label encoding **is** a printed
device, by forgetting the labels. -/
@[expose] public def SelfAwareDevice.toFunctionValued
    (D : SelfAwareDevice.{u, v, w} U) : FunctionValuedSelfAware.{u, v} U where
  toDevice := D.toDevice
  askOf := fun u => D.eval (D.question u)
  pair_surjective := by
    rintro b f ⟨u₀, hu₀⟩
    obtain ⟨u, hu⟩ := D.pair_surjective (b, D.question u₀)
    refine ⟨u, ?_, ?_⟩
    · exact congrArg Prod.fst hu
    · rw [show D.question u = D.question u₀ from congrArg Prod.snd hu, hu₀]

/-- **The round trip is the identity on the printed data**: forgetting the
labels and representing again returns the same question functions. -/
public theorem SelfAwareDevice.askOf_toFunctionValued_toSelfAware
    (D : SelfAwareDevice.{u, v, w} U) (u : U) :
    D.toFunctionValued.toSelfAware.ask u = D.ask u := rfl

/-- …and on the question set. -/
public theorem SelfAwareDevice.evalImage_toFunctionValued
    (D : SelfAwareDevice.{u, v, w} U) :
    evalImage D.toFunctionValued.toSelfAware = evalImage D := by
  rw [FunctionValuedSelfAware.evalImage_toSelfAware]
  ext g
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨D.question u, ⟨u, rfl⟩, rfl⟩
  · rintro ⟨q, ⟨u, rfl⟩, rfl⟩
    exact ⟨u, rfl⟩



/-! ## Proposition 7's positive half, at four states

`question_constant_of_card_lt_four` shows the printed existential **fails**
below four states, because no source-admissible self-aware device exists there
at all. The converse was left open twice, on the ground that `uncorrectable`
sets `D.toDevice := C` and that choice cannot generally be made admissible —
`(Y, Q)` onto `𝔹 × Q(U)` fails outright when one of `C`'s conclusion fibres is a
singleton.

That reasoning was right about `uncorrectable` and wrong about the proposition.
**`D`'s device is not required to be `C`.** Choosing it freely, with a
conclusion whose two fibres each hold two of four named states, makes
admissibility available for *every* `C`, and the evaluation can then be tuned so
that `Q̄` disagrees with `D`'s own conclusion exactly where `C` concludes `true`.
The agreement function is then `¬Y_C`, which no fibre of `C` can report, since
that would need `Y_C(w) = ¬Y_C(w)`.

So the printed proposition is **true at four or more states and false below**,
and the two theorems together settle it.
-/

section Prop7Positive

variable {a b c d : U}

/-- `D`'s conclusion: `true` on `{a, b}`, `false` on `{c, d}`. Both fibres hold
two of the four states, which is what `pair_surjective` needs. -/
@[expose] public def splitOn (a b : U) [DecidableEq U] : U → Bool :=
  fun u => decide (u = a ∨ u = b)

/-- `D`'s question map, chosen to cross `splitOn` so all four pairs are
realized. -/
@[expose] public def crossOn (a c : U) [DecidableEq U] : U → Bool :=
  fun u => decide (u = a ∨ u = c)

/-- `D`'s evaluation, tuned against `C`: it agrees with `D`'s own conclusion
exactly where `C` concludes `false`. -/
@[expose] public def tunedAsk [DecidableEq U] (C : InferenceDevice.{u, v} U)
    (a b : U) : U → Bool :=
  fun w => if C.concl w then !splitOn a b w else splitOn a b w

/-- **A source-admissible self-aware device that `C` cannot correct.** Its
question map takes two values — `crossOn` separates `a` from `b` — so it meets
the §1.2 stipulation `uncorrectable` violates, and **so does its setup map**,
which is `crossOn` as well. A `Unit` setup would satisfy Definition 12 while
violating the same stipulation the row exists to record. -/
@[expose] public def admissibleUncorrectable [DecidableEq U]
    (C : InferenceDevice.{u, v} U) (a b c d : U)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    SelfAwareDevice.{u, 0, 0} U where
  toDevice :=
    { Setup := Bool
      -- The setup map is two-valued, as §1.2 requires of every function
      -- considered. A `Unit` setup would satisfy Definition 12 and violate the
      -- paper's own stipulation, which is the defect this whole row is about.
      setup := crossOn a c
      concl := splitOn a b
      concl_surjective := by
        intro t
        cases t with
        | true => exact ⟨a, by simp [splitOn]⟩
        | false => exact ⟨c, by simp [splitOn, hac.symm, hbc.symm]⟩ }
  Question := Bool
  question := crossOn a c
  eval := fun _ => tunedAsk C a b
  pair_surjective := by
    rintro ⟨t, q⟩
    cases t <;> cases q
    · exact ⟨d, by simp [splitOn, crossOn, had.symm, hbd.symm, hcd.symm]⟩
    · exact ⟨c, by simp [splitOn, crossOn, hac.symm, hbc.symm]⟩
    · exact ⟨b, by simp [splitOn, crossOn, hab.symm, hbc]⟩
    · exact ⟨a, by simp [splitOn, crossOn]⟩

/-- **The agreement function is `¬Y_C`.** This is the whole construction: the
evaluation was tuned so that `D` agrees with itself exactly where `C` concludes
`false`. -/
public theorem agreesWithQuestion_admissibleUncorrectable [DecidableEq U]
    (C : InferenceDevice.{u, v} U) (a b c d : U)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (w : U) :
    agreesWithQuestion (admissibleUncorrectable C a b c d hab hac had hbc hbd hcd) w
      = !C.concl w := by
  show decide (splitOn a b w = tunedAsk C a b w) = !C.concl w
  unfold tunedAsk
  cases hC : C.concl w <;> simp_all

/-- **Every function of the witness is two-valued**, which is the §1.2
stipulation in full: the question map separates `a` from `b`, the setup map is
the same map, and the conclusion separates `a` from `c`. -/
public theorem admissibleUncorrectable_two_valued [DecidableEq U]
    (C : InferenceDevice.{u, v} U) (a b c d : U)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    (∃ u u' : U, (admissibleUncorrectable C a b c d hab hac had hbc hbd hcd).question u
        ≠ (admissibleUncorrectable C a b c d hab hac had hbc hbd hcd).question u') ∧
      (∃ u u' : U,
        (admissibleUncorrectable C a b c d hab hac had hbc hbd hcd).toDevice.setup u
          ≠ (admissibleUncorrectable C a b c d hab hac had hbc hbd hcd).toDevice.setup u') ∧
      (∃ u u' : U,
        (admissibleUncorrectable C a b c d hab hac had hbc hbd hcd).toDevice.concl u
          ≠ (admissibleUncorrectable C a b c d hab hac had hbc hbd hcd).toDevice.concl u') := by
  refine ⟨⟨a, b, ?_⟩, ⟨a, b, ?_⟩, ⟨a, c, ?_⟩⟩
  · show crossOn a c a ≠ crossOn a c b
    simp [crossOn, hab.symm, hbc]
  · show crossOn a c a ≠ crossOn a c b
    simp [crossOn, hab.symm, hbc]
  · show splitOn a b a ≠ splitOn a b c
    simp [splitOn, hac.symm, hbc.symm]

/-- **The witness's evaluated question is two-valued as well**, provided `a` and
`b` straddle `C`'s conclusion.

This is the §1.2 stipulation at its last hiding place. `Q(U)` is a set of
**binary functions of `U`**, so the stipulation *"every function we consider has
at least two image values"* applies to each question itself, not only to the
question map. Without `hY` the evaluated question can be constant — take
`Y_C = splitOn a b` and `tunedAsk` collapses to `false` everywhere.

`hY` is free: `Y_C` is surjective, so a `true` point and a `false` point always
exist. -/
public theorem tunedAsk_two_valued [DecidableEq U] (C : InferenceDevice.{u, v} U)
    (a b : U) (hY : C.concl a ≠ C.concl b) :
    tunedAsk C a b a ≠ tunedAsk C a b b := by
  have ha : splitOn a b a = true := by simp [splitOn]
  have hb : splitOn a b b = true := by simp [splitOn]
  simp only [tunedAsk, ha, hb]
  cases hca : C.concl a <;> cases hcb : C.concl b <;> simp_all

/-- **Proposition 7 with the paper's own convention kept, in full.** For every
device over a universe with four distinct states — two of which its conclusion
separates — there is a self-aware device it cannot correct whose question map
**and** whose evaluated question both take two values, as §1.2 requires of every
function the paper considers.

`hY` costs nothing: `Y_C` is surjective onto `𝔹`, so a `true` point and a
`false` point always exist and can be taken as `a` and `b`. -/
public theorem exists_admissible_not_corrects [DecidableEq U]
    (C : InferenceDevice.{u, v} U) (a b c d : U)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) (hY : C.concl a ≠ C.concl b) :
    ∃ D : SelfAwareDevice.{u, 0, 0} U,
      (∃ u u' : U, D.question u ≠ D.question u') ∧
        (∃ u u' : U, D.eval (D.question u) u ≠ D.eval (D.question u') u') ∧
        ¬ Corrects C D := by
  refine ⟨admissibleUncorrectable C a b c d hab hac had hbc hbd hcd, ⟨a, b, ?_⟩,
    ⟨a, b, tunedAsk_two_valued C a b hY⟩, ?_⟩
  · show crossOn a c a ≠ crossOn a c b
    simp [crossOn, hab.symm, hbc]
  · rintro ⟨x, ⟨w, hw⟩, hfib⟩
    have h := hfib w hw
    rw [show (decide (
        (admissibleUncorrectable C a b c d hab hac had hbc hbd hcd).toDevice.concl w =
        (admissibleUncorrectable C a b c d hab hac had hbc hbd hcd).ask w))
      = agreesWithQuestion (admissibleUncorrectable C a b c d hab hac had hbc hbd hcd) w
      from rfl,
      agreesWithQuestion_admissibleUncorrectable C a b c d hab hac had hbc hbd hcd w] at h
    simp at h

/--
**Proposition 7 at its printed quantifier.**

`exists_admissible_not_corrects` asks the caller for four named states and for
`a`, `b` to straddle `C`'s conclusion. The printed proposition asks for none of
that: it says *for every device there is a self-aware device it cannot
correct*, and under §1.2 and Definition 12 its only real hypothesis is that the
universe is large enough to carry an admissible self-aware device at all —
which `four_le_card_of_two_questions` shows is four states.

Everything the caller was supplying is derivable. `a` and `b` come from
`concl_surjective`, which also makes them distinct and gives `hY` for free; `c`
and `d` come from the two states left over once `{a, b}` is removed from a
universe of at least four.

This closes an asymmetry rather than adding mathematics: the same standard is
applied to Theorem 4, where assuming the per-probe bound rather than deriving it
from the printed premises would be an overclaim.
-/
public theorem exists_admissible_not_corrects_of_four_states [DecidableEq U]
    [Fintype U] (C : InferenceDevice.{u, v} U) (hcard : 4 ≤ Fintype.card U) :
    ∃ D : SelfAwareDevice.{u, 0, 0} U,
      (∃ u u' : U, D.question u ≠ D.question u') ∧
        (∃ u u' : U, D.eval (D.question u) u ≠ D.eval (D.question u') u') ∧
        ¬ Corrects C D := by
  classical
  obtain ⟨a, ha⟩ := C.concl_surjective true
  obtain ⟨b, hb⟩ := C.concl_surjective false
  have hY : C.concl a ≠ C.concl b := by rw [ha, hb]; exact Bool.noConfusion
  have hab : a ≠ b := fun h => hY (by rw [h])
  -- Two states remain once `a` and `b` are removed.
  have hpair : ({a, b} : Finset U).card = 2 := by
    rw [Finset.card_insert_of_notMem (by simp [hab]), Finset.card_singleton]
  have hdiff : (Finset.univ \ ({a, b} : Finset U)).card = Fintype.card U - 2 := by
    simp [Finset.card_sdiff, hpair]
  have hlt : 1 < (Finset.univ \ ({a, b} : Finset U)).card := by omega
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp hlt
  have hcne := Finset.mem_sdiff.mp hc
  have hdne := Finset.mem_sdiff.mp hd
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcne hdne
  exact exists_admissible_not_corrects C a b c d hab
    (fun h => hcne.2.1 h.symm) (fun h => hdne.2.1 h.symm)
    (fun h => hcne.2.2 h.symm) (fun h => hdne.2.2 h.symm) hcd hY

end Prop7Positive



/-! ## §9's `𝒟` over an arbitrary setup range

`questionAnsweringSet` is a `Finset`, so `selfAwareInferenceComplexity` carries
`[FiniteRange D.toDevice.setup]` where §9 inherits Definition 6's **countable**
setup range. This is the same restriction `answeringSetOn` removed for
Definition 6, and it comes off the same way: the printed `min` needs the minimum
to **exist**, not the index to be finite.
-/

/-- The setups whose question, evaluated, is the probe — as a **set**. -/
@[expose] public def questionAnsweringSetOn (D : SelfAwareDevice.{u, v, w} U)
    {G : Type v'} (Γ : U → G) (f : G → Bool) : Set D.toDevice.Setup :=
  {x | D.toDevice.Realized x ∧
    ∀ u : U, D.toDevice.setup u = x → ∀ v : U, D.eval (D.question u) v = f (Γ v)}

/-- The printed `min` over them, as an infimum. -/
@[expose] public noncomputable def minQuestionLengthOn (D : SelfAwareDevice.{u, v, w} U)
    (ℓ : D.toDevice.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  sInf (ℓ '' questionAnsweringSetOn D Γ f)

/-- **§9's `𝒟` with no finiteness on the setup range.** -/
@[expose] public noncomputable def selfAwareInferenceComplexityOn
    (D : SelfAwareDevice.{u, v, w} U) (ℓ : D.toDevice.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum fun γ => minQuestionLengthOn D ℓ Γ (probe γ)

public theorem mem_questionAnsweringSetOn_iff (D : SelfAwareDevice.{u, v, w} U)
    {G : Type v'} (Γ : U → G) (f : G → Bool) (x : D.toDevice.Setup) :
    x ∈ questionAnsweringSetOn D Γ f ↔
      D.toDevice.Realized x ∧
        ∀ u : U, D.toDevice.setup u = x → ∀ v : U, D.eval (D.question u) v = f (Γ v) :=
  Iff.rfl

public theorem coe_questionAnsweringSet (D : SelfAwareDevice.{u, v, w} U)
    [DecidableEq D.toDevice.Setup] [FiniteRange D.toDevice.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) :
    (questionAnsweringSet D Γ f : Set D.toDevice.Setup) = questionAnsweringSetOn D Γ f := by
  ext x
  rw [Finset.mem_coe, mem_questionAnsweringSet_iff, mem_questionAnsweringSetOn_iff]

/-- The value is the printed minimum wherever that minimum exists. -/
public theorem minQuestionLengthOn_eq_of_isLeast (D : SelfAwareDevice.{u, v, w} U)
    (ℓ : D.toDevice.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool) {m : ℝ}
    (hm : IsLeast (ℓ '' questionAnsweringSetOn D Γ f) m) :
    minQuestionLengthOn D ℓ Γ f = m :=
  hm.csInf_eq

/-- …and it recovers the `Finset` form on a finite setup range with a nonempty
answering set. -/
public theorem minQuestionLengthOn_eq (D : SelfAwareDevice.{u, v, w} U)
    [DecidableEq D.toDevice.Setup] [FiniteRange D.toDevice.setup]
    (ℓ : D.toDevice.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool)
    (h : (questionAnsweringSet D Γ f).Nonempty) :
    minQuestionLengthOn D ℓ Γ f = minQuestionLength D ℓ Γ f := by
  classical
  rw [minQuestionLength, dif_pos h]
  refine minQuestionLengthOn_eq_of_isLeast D ℓ Γ f ⟨?_, ?_⟩
  · obtain ⟨x, hx, hxeq⟩ := Finset.exists_mem_eq_inf' h ℓ
    exact ⟨x, by rw [← coe_questionAnsweringSet]; exact hx, hxeq.symm⟩
  · rintro y ⟨x, hx, rfl⟩
    rw [← coe_questionAnsweringSet] at hx
    exact Finset.inf'_le ℓ hx


end AISafetyAtlas.Inference
