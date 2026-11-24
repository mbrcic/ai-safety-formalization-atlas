import AISafetyAtlas.Control.OpenLoop

/-!
Touchette and Lloyd (2004), Lemma 8, equations (38)–(39). For finite open-loop
control, `ΔH_open ≤ H(X) − H(X' | C)`, with equality iff `I(X'; C) = 0`.
The cited declarations are `AISafetyAtlas.Control.entropyReduction_le_condEntropy_form`
and `AISafetyAtlas.Control.entropyReduction_eq_condEntropy_form_iff`.

The map takes the joint mass law of the outcome and controller on its finite
range and uses a constant initial state. The actuation law is the conditional
outcome law on each controller fibre. The zero-measure case has zero entropies.
Both statements use nats, which multiply all printed bit quantities by `log 2`.

Checked: `lake env lean docs/provenance/transfers/024-open-loop-entropy.lean`
-/

namespace Transfer024

open MeasureTheory ProbabilityTheory AISafetyAtlas.Control

universe uΩ uS uT uK uD

def PrintConclusion {D : Type*} {T : Type*} {K : Type*}
    [MeasurableSpace D] [MeasurableSpace T] [MeasurableSpace K]
    (ν : Measure D) (X X' : D → T) (Y : D → K) : Prop :=
  (H[X ; ν] - H[X' ; ν] ≤ H[X ; ν] - H[X' | Y ; ν]) ∧
    (H[X ; ν] - H[X' ; ν] = H[X ; ν] - H[X' | Y ; ν] ↔ I[X' : Y ; ν] = 0)

def PrintStatement : Prop :=
  ∀ (D : Type uD) [Finite D] [MeasurableSpace D] [MeasurableSingletonClass D]
    (T : Type uT) (K : Type uK) [MeasurableSpace T] [MeasurableSpace K]
    [MeasurableSingletonClass T] [MeasurableSingletonClass K] [Countable T] [Countable K]
    (ν : Measure D) [IsProbabilityMeasure ν] (X X' : D → T) (Y : D → K),
    IndepFun X Y ν → PrintConclusion ν X X' Y

def LeanConclusion {Ω S T K : Type*}
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace K]
    (μ : Measure Ω) (X : Ω → S) (X' : Ω → T) (Y : Ω → K) : Prop :=
  (entropyReduction μ X X' ≤ H[X ; μ] - H[X' | Y ; μ]) ∧
    (entropyReduction μ X X' = H[X ; μ] - H[X' | Y ; μ] ↔ I[X' : Y ; μ] = 0)

def LeanStatement : Prop :=
  ∀ (Ω : Type uΩ) (S : Type uS) (T : Type uT) (K : Type uK)
    [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace K]
    [MeasurableSingletonClass T] [MeasurableSingletonClass K] [Countable T] [Countable K]
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ] (X : Ω → S) (X' : Ω → T) (Y : Ω → K),
    Measurable X' → Measurable Y → ∀ [FiniteRange X'] [FiniteRange Y], LeanConclusion μ X X' Y

section

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {K : Type uK}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace K]
variable [MeasurableSingletonClass T] [MeasurableSingletonClass K] [Countable T] [Countable K]
variable {μ : Measure Ω} {X : Ω → S} {X' : Ω → T} {Y : Ω → K}

abbrev Sample (X' : Ω → T) (Y : Ω → K) := Set.range fun ω ↦ (X' ω, Y ω)

def toSample (X' : Ω → T) (Y : Ω → K) (ω : Ω) : Sample X' Y :=
  ⟨(X' ω, Y ω), ⟨ω, rfl⟩⟩

noncomputable def phi (μ : Measure Ω) (X' : Ω → T) (Y : Ω → K) : Measure (Sample X' Y) :=
  μ.map (toSample X' Y)

omit [MeasurableSingletonClass T] [MeasurableSingletonClass K] [Countable T] [Countable K] in
theorem H [IsProbabilityMeasure μ] (hX' : Measurable X') (hY : Measurable Y)
    [FiniteRange X'] [FiniteRange Y] (t : T) :
    Finite (Sample X' Y) ∧ IsProbabilityMeasure (phi μ X' Y) ∧
      IndepFun (fun _ : Sample X' Y ↦ t) (fun d ↦ d.val.2) (phi μ X' Y) := by
  have hm : Measurable (toSample X' Y) := (hX'.prodMk hY).subtype_mk
  have : IsProbabilityMeasure (phi μ X' Y) := Measure.isProbabilityMeasure_map hm.aemeasurable
  exact ⟨FiniteRange.finite (X := fun ω ↦ (X' ω, Y ω)), inferInstance, indepFun_const_left t _⟩

theorem C [IsProbabilityMeasure μ] (hX' : Measurable X') (hY : Measurable Y)
    [FiniteRange X'] [FiniteRange Y] (t : T) [IsProbabilityMeasure (phi μ X' Y)]
    (hp : PrintConclusion (phi μ X' Y) (fun _ ↦ t) (fun d ↦ d.val.1) (fun d ↦ d.val.2)) :
    LeanConclusion μ X X' Y := by
  have : Finite (Sample X' Y) := FiniteRange.finite (X := fun ω ↦ (X' ω, Y ω))
  let Xp : Sample X' Y → T := fun d ↦ d.val.1
  let Yp : Sample X' Y → K := fun d ↦ d.val.2
  have : FiniteRange Xp := ⟨Set.finite_range _⟩
  have : FiniteRange Yp := ⟨Set.finite_range _⟩
  have hm : Measurable (toSample X' Y) := (hX'.prodMk hY).subtype_mk
  have hXp : Measurable Xp := measurable_fst.comp measurable_subtype_coe
  have hYp : Measurable Yp := measurable_snd.comp measurable_subtype_coe
  have hd : IdentDistrib (fun ω ↦ (X' ω, Y ω)) (fun d ↦ (Xp d, Yp d)) μ (phi μ X' Y) := by
    refine ⟨(hX'.prodMk hY).aemeasurable, (hXp.prodMk hYp).aemeasurable, ?_⟩
    rw [phi, Measure.map_map (hXp.prodMk hYp) hm]
    rfl
  change PrintConclusion (phi μ X' Y) (fun _ ↦ t) Xp Yp at hp
  unfold PrintConclusion at hp
  have he : H[X' ; μ] = H[Xp ; phi μ X' Y] := (hd.comp measurable_fst).entropy_congr
  rw [entropy_const, ← he, ← hd.condEntropy_eq hX' hY hXp hYp, ← hd.mutualInfo_eq] at hp
  change (H[X ; μ] - H[X' ; μ] ≤ H[X ; μ] - H[X' | Y ; μ]) ∧
      (H[X ; μ] - H[X' ; μ] = H[X ; μ] - H[X' | Y ; μ] ↔ I[X' : Y ; μ] = 0)
  exact ⟨by linarith [hp.1], ⟨fun he ↦ hp.2.mp (by linarith), fun hi ↦ by linarith [hp.2.mpr hi]⟩⟩

end

theorem lean_of_print : PrintStatement.{uT, uK, max uT uK} → LeanStatement.{uΩ, uS, uT, uK} := by
  intro hp Ω S T K _ _ _ _ _ _ _ _ μ _ X X' Y hX' hY _ _
  rcases eq_zero_or_isProbabilityMeasure μ with rfl | hμ
  · simp [LeanConclusion, entropyReduction, mutualInfo_def]
  let t := X' (nonempty_of_isProbabilityMeasure μ).some
  obtain ⟨hD, hν, hIndep⟩ := H (μ := μ) hX' hY t
  exact C hX' hY t (hp (Sample X' Y) T K (phi μ X' Y) (fun _ ↦ t) _ _ hIndep)

theorem print_of_lean : LeanStatement.{uD, uT, uT, uK} → PrintStatement.{uT, uK, uD} := by
  intro hl D _ _ _ T K _ _ _ _ _ _ ν _ X X' Y _
  have : FiniteRange X' := ⟨Set.finite_range _⟩
  have : FiniteRange Y := ⟨Set.finite_range _⟩
  exact hl D T T K ν X X' Y Measurable.of_discrete Measurable.of_discrete

end Transfer024
