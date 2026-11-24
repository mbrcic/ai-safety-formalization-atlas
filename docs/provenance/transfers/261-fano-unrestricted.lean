import AISafetyAtlas.InformationTheory.Fano

/-!
Cover and Thomas (2006), Theorem 2.10.1, first inequality of (2.130). For a
discrete Markov chain `X → Y → X̂` with finite truth alphabet `𝒳`,
`H(X | X̂) ≤ H(Pₑ) + Pₑ log |𝒳|`, where `Pₑ = Pr(X ≠ X̂)`.
The cited `AISafetyAtlas.InformationTheory.fano_of_embedding_countable`
specializes to `fano_unrestricted_countable` at the identity embedding. Adding
the finite-range hypotheses gives the other cited forms, `fano_of_embedding`
and `fano_unrestricted`.

The map pushes the joint law of the truth and estimate onto the finite truth
alphabet and countable estimate alphabet, with `Y = X̂`. We represent the PMF by
a probability measure on the discrete product. All entropy terms and logarithms
are in nats, a common positive rescaling of the printed bit quantities.

Checked: `lake env lean docs/provenance/transfers/261-fano-unrestricted.lean`
-/

namespace Transfer261

open MeasureTheory ProbabilityTheory Function Real AISafetyAtlas.InformationTheory

universe uΩ uS uT uY

def PrintConclusion {A : Type uS} {Y : Type uY} {T : Type uT} [Fintype A]
    [MeasurableSpace A] [MeasurableSpace Y] [MeasurableSpace T] [DecidableEq T]
    (ν : Measure (A × Y × T)) (ι : A → T) : Prop :=
  let e := errorProb ν (fun d ↦ ι d.1) (fun d ↦ d.2.2)
  let estimate : A × Y × T → T := fun d ↦ d.2.2
  (∑' t, (ν.map estimate).real {t} * H[Prod.fst | estimate ← t ; ν]) ≤
    e * Real.log (Fintype.card A : ℝ) + binEntropy e

private theorem printEntropy_eq {A Y T : Type*} [Fintype A] [Countable T]
    [MeasurableSpace A] [MeasurableSpace Y] [MeasurableSpace T]
    [MeasurableSingletonClass A] [MeasurableSingletonClass T]
    (ν : Measure (A × Y × T)) [IsFiniteMeasure ν] :
    (∑' t, (ν.map (fun d ↦ d.2.2)).real {t} * H[Prod.fst | (fun d ↦ d.2.2) ← t ; ν]) =
      H[Prod.fst | fun d ↦ d.2.2 ; ν] := by
  let X : A × Y × T → A := Prod.fst
  have : FiniteRange X := ⟨Set.toFinite (Set.range X)⟩
  exact (hasSum_condEntropy (X := X) measurable_fst (fun d ↦ d.2.2) (μ := ν)).tsum_eq

def PrintStatement : Prop :=
  ∀ (A : Type uS) (Y : Type uY) (T : Type uT) [Fintype A]
    [MeasurableSpace A] [MeasurableSpace Y] [MeasurableSpace T]
    [MeasurableSingletonClass A] [MeasurableSingletonClass Y] [MeasurableSingletonClass T]
    [Countable Y] [Countable T] [DecidableEq T] (ν : Measure (A × Y × T))
    [IsProbabilityMeasure ν] (ι : A → T), Injective ι →
    IsMarkovChain Prod.fst (fun d ↦ d.2.1) (fun d ↦ d.2.2) ν → PrintConclusion ν ι

def LeanStatement : Prop :=
  ∀ (Ω : Type uΩ) (S : Type uS) (T : Type uT)
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
    [MeasurableSingletonClass S] [MeasurableSingletonClass T] [Countable S] [Countable T]
    [DecidableEq T] (A : Finset S) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : Ω → S) (Z : Ω → T) (ι : S → T), Injective ι → Measurable X → Measurable Z →
    (∀ ω, X ω ∈ A) → ∀ [FiniteRange X],
    H[X | Z ; μ] ≤ errorProb μ (ι ∘ X) Z * Real.log (A.card : ℝ)
      + binEntropy (errorProb μ (ι ∘ X) Z)

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

section

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T]
variable [MeasurableSingletonClass T] [Countable T]
variable {A : Finset S} {X : Ω → S} {Z : Ω → T} {μ : Measure Ω}

def toSample (hXA : ∀ ω, X ω ∈ A) (Z : Ω → T) (ω : Ω) : A × T × T :=
  (⟨X ω, hXA ω⟩, Z ω, Z ω)

noncomputable def phi (μ : Measure Ω) (hXA : ∀ ω, X ω ∈ A) (Z : Ω → T) :
    Measure (A × T × T) := μ.map (toSample hXA Z)

omit [MeasurableSingletonClass T] [Countable T] in
private theorem measurable_toSample (hX : Measurable X) (hZ : Measurable Z)
    (hXA : ∀ ω, X ω ∈ A) : Measurable (toSample hXA Z) :=
  hX.subtype_mk.prodMk (hZ.prodMk hZ)

theorem H [MeasurableSingletonClass S] [IsProbabilityMeasure μ] (hX : Measurable X)
    (hZ : Measurable Z) (hXA : ∀ ω, X ω ∈ A) {ι : S → T} (hι : Injective ι) :
    IsProbabilityMeasure (phi μ hXA Z) ∧ Injective (ι ∘ (Subtype.val : A → S)) ∧
      IsMarkovChain Prod.fst (fun d ↦ d.2.1) (fun d ↦ d.2.2) (phi μ hXA Z) := by
  have hm := measurable_toSample hX hZ hXA
  refine ⟨Measure.isProbabilityMeasure_map hm.aemeasurable, hι.comp Subtype.val_injective, ?_⟩
  let ν := phi μ hXA Z
  let Yp : A × T × T → T := fun d ↦ d.2.1
  let Zp : A × T × T → T := fun d ↦ d.2.2
  have hy : Measurable Yp := measurable_fst.comp measurable_snd
  have hz : Measurable Zp := measurable_snd.comp measurable_snd
  have hd : ∀ᵐ d ∂ν, Zp d = Yp d :=
    (ae_map_iff hm.aemeasurable (measurableSet_eq_fun hz hy)).2 (ae_of_all _ fun _ ↦ rfl)
  show ∀ᵐ t ∂ν.map Yp, IndepFun Prod.fst Zp (ν[|Yp ⁻¹' {t}])
  refine ae_of_all _ fun t ↦ ?_
  have hc : (fun _ ↦ t) =ᵐ[ν[|Yp ⁻¹' {t}]] Zp := by
    filter_upwards [cond_absolutelyContinuous hd, ae_cond_mem (hy (measurableSet_singleton t))]
      with d hdiag ht
    exact (hdiag.trans ht).symm
  exact (indepFun_const_right Prod.fst t).congr (Filter.EventuallyEq.refl _ _) hc

theorem C [MeasurableSingletonClass S] [Countable S] [DecidableEq T] (hX : Measurable X)
    (hZ : Measurable Z) (hXA : ∀ ω, X ω ∈ A) (ι : S → T)
    [IsProbabilityMeasure (phi μ hXA Z)]
    (hp : PrintConclusion (phi μ hXA Z) (ι ∘ Subtype.val)) :
    H[X | Z ; μ] ≤ errorProb μ (ι ∘ X) Z * Real.log (A.card : ℝ)
      + binEntropy (errorProb μ (ι ∘ X) Z) := by
  let Xp : Ω → A := fun ω ↦ ⟨X ω, hXA ω⟩
  have hm := measurable_toSample hX hZ hXA
  have hEntropy : H[Prod.fst | fun d ↦ d.2.2 ; phi μ hXA Z] = H[X | Z ; μ] := by
    have hmZ : Measurable (fun d : A × T × T ↦ d.2.2) := measurable_snd.comp measurable_snd
    rw [phi, condEntropy_map hm measurable_fst hmZ]
    exact (condEntropy_comp_of_injective (Y := Z) μ (f := Subtype.val)
      (show Measurable Xp from hX.subtype_mk) Subtype.val_injective).symm
  have hError : errorProb (phi μ hXA Z) (fun d ↦ (ι ∘ Subtype.val) d.1) (fun d ↦ d.2.2) =
      errorProb μ (ι ∘ X) Z := by
    unfold errorProb phi
    rw [Measure.map_apply hm MeasurableSet.of_discrete]
    rfl
  simpa only [PrintConclusion, printEntropy_eq, hEntropy, hError, Fintype.card_coe] using hp

end

theorem lean_of_print : PrintStatement.{uS, uT, uT} → LeanStatement.{uΩ, uS, uT} := by
  intro hp Ω S T _ _ _ _ _ _ _ _ A μ _ X Z ι hι hX hZ hXA _
  obtain ⟨hν, hι', hM⟩ := H (μ := μ) hX hZ hXA hι
  exact C hX hZ hXA ι (hp A T T (phi μ hXA Z) (ι ∘ Subtype.val) hι' hM)

theorem print_of_lean : LeanStatement.{max uS uY uT, uS, uT} → PrintStatement.{uS, uT, uY} := by
  classical
  intro hl A Y T _ _ _ _ _ _ _ _ _ _ ν _ ι hι _
  let X : A × Y × T → A := Prod.fst
  have : FiniteRange X := ⟨Set.toFinite (Set.range X)⟩
  have h := hl (A × Y × T) A T Finset.univ ν X (fun d ↦ d.2.2) ι hι measurable_fst
    (measurable_snd.comp measurable_snd) (fun _ ↦ Finset.mem_univ _)
  simpa [PrintConclusion, printEntropy_eq, X, Function.comp_def] using h

end Transfer261
