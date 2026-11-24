import AISafetyAtlas.Examples.InformationTheory.DataProcessing

/-!
Cover and Thomas (2006), §2.10, corollary (2.140). With a deterministic
estimator `g : 𝒴 → 𝒳` and `Pₑ = Pr(X ≠ g(Y))`, the printed inequality is
`H(X | Y) ≤ H(Pₑ) + Pₑ log (|𝒳| − 1)`. Definedness requires `|𝒳| ≥ 2`.
The cited `AISafetyAtlas.Examples.InformationTheory.fano_of_markov_countable`
and `fano_of_estimator_chain_countable` include their finite-range forms
`fano_of_markov` and `fano_of_estimator_chain` by specialization.

The map takes the joint PMF of the truth and the augmented observation `(Y, X̂)`,
with the estimator given by the second projection. It adds unused alphabet
symbols only where needed to define the printed logarithm. In that case the
error probability is zero. Both statements express entropy in nats.

Checked: `lake env lean docs/provenance/transfers/045-fano-markov-estimator.lean`
-/

namespace Transfer045

open MeasureTheory ProbabilityTheory Function Real AISafetyAtlas.InformationTheory

universe uΩ uS uT uB

def PrintConclusion {A : Type uS} {B : Type uB} [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSpace B] (ν : Measure (A × B)) (g : B → A) : Prop :=
  let e := errorProb ν Prod.fst (g ∘ Prod.snd)
  H[Prod.fst | Prod.snd ; ν] ≤ e * Real.log ((Fintype.card A : ℝ) - 1) + binEntropy e

def PrintStatement : Prop :=
  ∀ (A : Type uS) (B : Type uB) [Fintype A] [DecidableEq A]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A]
    [MeasurableSingletonClass B] [Countable B] (ν : Measure (A × B))
    [IsProbabilityMeasure ν] (g : B → A), 2 ≤ Fintype.card A → PrintConclusion ν g

def Bound {Ω S T : Type*} [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [DecidableEq S] (A : Finset S) (μ : Measure Ω) (X : Ω → S) (Y : Ω → T)
    (Z : Ω → S) : Prop :=
  let e := errorProb μ X Z
  H[X | Y ; μ] ≤ e * Real.log ((A.card : ℝ) - 1) + binEntropy e

def MarkovStatement : Prop :=
  ∀ (Ω : Type uΩ) (S : Type uS) (T : Type uT)
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [Countable S] [Countable T]
    [DecidableEq S] (A : Finset S) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (Z : Ω → S), Measurable X → Measurable Y → Measurable Z →
    (∀ ω, X ω ∈ A) → (∀ ω, Z ω ∈ A) → ∀ [FiniteRange X],
    IsMarkovChain X Y Z μ → Bound A μ X Y Z

def EstimatorStatement : Prop :=
  ∀ (Ω : Type uΩ) (S : Type uS) (T : Type uT)
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [Countable S] [Countable T]
    [DecidableEq S] (A : Finset S) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Y : Ω → T) (g : T → S), Measurable X → Measurable Y →
    (∀ ω, X ω ∈ A) → (∀ ω, g (Y ω) ∈ A) → ∀ [FiniteRange X], Bound A μ X Y (g ∘ Y)

def LeanStatement : Prop := MarkovStatement.{uΩ, uS, uT} ∧ EstimatorStatement.{uΩ, uS, uT}

private theorem condEntropy_map {D Ω A B : Type*}
    [MeasurableSpace D] [MeasurableSpace Ω] [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass B] {μ : Measure Ω} {f : Ω → D} {X : D → A} {Y : D → B}
    (hf : Measurable f) (hX : Measurable X) (hY : Measurable Y) :
    H[X | Y ; μ.map f] = H[X ∘ f | Y ∘ f ; μ] := by
  rw [condEntropy_def, condEntropy_def, Measure.map_map hY hf]
  congr 1
  funext b
  change H[X ; (μ.map f)[|Y ⁻¹' {b}]] = H[X ∘ f ; μ[|(Y ∘ f) ⁻¹' {b}]]
  rw [entropy_def, entropy_def]
  congr 1
  ext s hs
  have hb := hY (measurableSet_singleton b)
  rw [Measure.map_apply hX hs, Measure.map_apply (hX.comp hf) hs, cond_apply hb,
    cond_apply ((hY.comp hf) (measurableSet_singleton b)), Measure.map_apply hf hb,
    Measure.map_apply hf (hb.inter (hX hs))]
  rfl

abbrev Alphabet {S : Type*} (A : Finset S) := (A : Type _) ⊕ Fin (2 - A.card)

local instance {S : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] (A : Finset S) :
    MeasurableSingletonClass (Alphabet A) := ⟨fun x ↦ by
  cases x with
  | inl a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inl_image
  | inr a => simpa only [Set.image_singleton] using (measurableSet_singleton a).inr_image⟩

private theorem alphabet_card {S : Type*} (A : Finset S) :
    Fintype.card (Alphabet A) = A.card + (2 - A.card) := by simp [Alphabet]

section

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
variable {A : Finset S} {X Z : Ω → S} {Y : Ω → T} {μ : Measure Ω}

def toSample (hXA : ∀ ω, X ω ∈ A) (Y : Ω → T) (hZA : ∀ ω, Z ω ∈ A) (ω : Ω) :
    Alphabet A × T × Alphabet A :=
  (Sum.inl ⟨X ω, hXA ω⟩, Y ω, Sum.inl ⟨Z ω, hZA ω⟩)

noncomputable def phi (μ : Measure Ω) (hXA : ∀ ω, X ω ∈ A) (Y : Ω → T)
    (hZA : ∀ ω, Z ω ∈ A) : Measure (Alphabet A × T × Alphabet A) :=
  μ.map (toSample hXA Y hZA)

private theorem measurable_toSample (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXA : ∀ ω, X ω ∈ A) (hZA : ∀ ω, Z ω ∈ A) : Measurable (toSample hXA Y hZA) :=
  (measurable_inl.comp hX.subtype_mk).prodMk (hY.prodMk (measurable_inl.comp hZ.subtype_mk))

theorem H [IsProbabilityMeasure μ] (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (hXA : ∀ ω, X ω ∈ A) (hZA : ∀ ω, Z ω ∈ A) :
    IsProbabilityMeasure (phi μ hXA Y hZA) ∧ 2 ≤ Fintype.card (Alphabet A) := by
  refine ⟨Measure.isProbabilityMeasure_map (measurable_toSample hX hY hZ hXA hZA).aemeasurable, ?_⟩
  rw [alphabet_card]
  omega

theorem C [MeasurableSingletonClass S] [MeasurableSingletonClass T] [Countable S] [Countable T]
    [DecidableEq S] [IsProbabilityMeasure μ] [FiniteRange X] (hX : Measurable X) (hY : Measurable Y)
    (hZ : Measurable Z) (hXA : ∀ ω, X ω ∈ A) (hZA : ∀ ω, Z ω ∈ A)
    (hM : IsMarkovChain X Y Z μ) (hp : PrintConclusion (phi μ hXA Y hZA) Prod.snd) :
    Bound A μ X Y Z := by
  let Xa : Ω → A := fun ω ↦ ⟨X ω, hXA ω⟩
  let Yp : Ω → T × Alphabet A := Prod.snd ∘ toSample hXA Y hZA
  have hm := measurable_toSample hX hY hZ hXA hZA
  have hInl : Injective (fun p : T × A ↦ (p.1, (Sum.inl p.2 : Alphabet A))) := by
    rintro ⟨t, a⟩ ⟨t', a'⟩ h
    obtain ⟨ht, ha⟩ := Prod.mk.inj h
    exact Prod.ext ht (Sum.inl_injective ha)
  have hVal : Injective (fun p : T × A ↦ (p.1, p.2.val)) := by
    rintro ⟨t, a⟩ ⟨t', a'⟩ h
    obtain ⟨ht, ha⟩ := Prod.mk.inj h
    exact Prod.ext ht (Subtype.ext ha)
  let Za : Ω → A := fun ω ↦ ⟨Z ω, hZA ω⟩
  have hYZ : H[X | Yp ; μ] = H[X | Y ; μ] := by
    have hPair := hY.prodMk (show Measurable Za from hZ.subtype_mk)
    calc
      H[X | Yp ; μ] = H[X | fun ω ↦ (Y ω, Za ω) ; μ] :=
        condEntropy_comp_of_injective_countable hX hPair hInl
      _ = H[X | fun ω ↦ (Y ω, Z ω) ; μ] :=
        (condEntropy_comp_of_injective_countable hX hPair hVal).symm
      _ = H[X | Y ; μ] := condEntropy_pair_eq_of_isMarkovChain hX hY hZ hM
  have hEntropy : H[Prod.fst | Prod.snd ; phi μ hXA Y hZA] = H[X | Y ; μ] := by
    rw [phi, condEntropy_map hm measurable_fst measurable_snd]
    have hXa : Measurable Xa := hX.subtype_mk
    exact (condEntropy_comp_of_injective μ hXa Sum.inl Sum.inl_injective).trans
      ((condEntropy_comp_of_injective μ hXa Subtype.val Subtype.val_injective).symm.trans hYZ)
  have hError : errorProb (phi μ hXA Y hZA) Prod.fst (Prod.snd ∘ Prod.snd) = errorProb μ X Z := by
    unfold errorProb phi
    rw [Measure.map_apply hm MeasurableSet.of_discrete]
    congr 2
    ext ω
    simp [toSample, Subtype.ext_iff]
  have hLog : errorProb μ X Z * Real.log ((Fintype.card (Alphabet A) : ℝ) - 1) =
      errorProb μ X Z * Real.log ((A.card : ℝ) - 1) := by
    by_cases hA : 2 ≤ A.card
    · rw [alphabet_card, Nat.sub_eq_zero_of_le hA, Nat.add_zero]
    · have heq : ∀ ω, X ω = Z ω :=
        fun ω ↦ Finset.card_le_one_iff.mp (by omega) (hXA ω) (hZA ω)
      simp [errorProb, heq]
  simpa only [PrintConclusion, hEntropy, hError, hLog, Bound] using hp

end

theorem lean_of_print : PrintStatement.{uS, max uT uS} → LeanStatement.{uΩ, uS, uT} := by
  intro hp
  have hMarkov : MarkovStatement.{uΩ, uS, uT} := by
    intro Ω S T _ _ _ _ _ _ _ _ A μ _ X Y Z hX hY hZ hXA hZA _ hM
    obtain ⟨hν, hCard⟩ := H (μ := μ) hX hY hZ hXA hZA
    exact C hX hY hZ hXA hZA hM
      (hp (Alphabet A) (T × Alphabet A) (phi μ hXA Y hZA) Prod.snd hCard)
  refine ⟨hMarkov, ?_⟩
  intro Ω S T _ _ _ _ _ _ _ _ A μ _ X Y g hX hY hXA hgA _
  exact hMarkov Ω S T A μ X Y (g ∘ Y) hX hY (Measurable.of_discrete.comp hY) hXA hgA
    (isMarkovChain_comp_countable hY g)

theorem print_of_lean : LeanStatement.{max uS uB, uS, uB} → PrintStatement.{uS, uB} := by
  classical
  intro hl A B _ _ _ _ _ _ _ ν _ g _
  let X : A × B → A := Prod.fst
  have : FiniteRange X := ⟨Set.toFinite (Set.range X)⟩
  have h := hl.2 (A × B) A B Finset.univ ν X Prod.snd g measurable_fst measurable_snd
    (fun _ ↦ Finset.mem_univ _) (fun _ ↦ Finset.mem_univ _)
  simpa [PrintConclusion, Bound, X] using h

end Transfer045
