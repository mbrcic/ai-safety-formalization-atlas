module

public import AISafetyAtlas.Inference
public import AISafetyAtlas.Examples.Inference.Complexity

/-!
# Worked model: an admissible self-aware device, and `𝒟` at a value

Two gaps close here, and they turn out to be the same construction.

**`𝒟` was never evaluated.** `selfAwareInferenceComplexity` is the §9 displayed
definition — the inference complexity of `Γ` charged against the setups whose
*question*, evaluated, is the probe of `Γ` — and until now nothing in the tree
computed it. A definition cannot be vacuous, but the 2008 map's own standard for
the section-5 layer is a computed value: a complexity of `0` reached through the
totalization proves nothing.

**No self-aware device met the paper's own convention.** `uncorrectable`, the
Proposition 7 witness, has a one-valued question map, which is why that row is
`REPAIRED` rather than `SOURCE-EXACT`. `four_le_card_of_two_questions` says an
admissible one needs four states. This is the first device in the tree that has
them.

**And the printed hypotheses are discharged, not dropped.** §9 introduces the
display for a device that is *infallible*, that *semi-controls its question*,
and that finds `Γ` *intelligible*. The Lean definition attaches none of them —
that is the §9 row's recorded delta — so evaluating the definition is not by
itself a model of the printed object. All three are proved below.

The design is forced by four constraints at once:

* `pair_surjective` needs `u ↦ (Y(u), Q(u))` onto `𝔹 × Q(U)`, so with two
  question values the four states must realize all four pairs;
* a setup value answers a probe only if **every** state in its fibre asks the
  same question, so the setup partition must refine the question partition;
* charging a nonzero length needs fibres larger than a point;
* **infallibility fixes the target.** Taking `Γ = Y` — the obvious choice, and
  the one this module first made — fails: at a state whose question is `false`
  the evaluation returns `¬Γ`, so `Q̄ ≠ Y` there. Twisting `Γ` by the question,
  `Γ(v) = Y(v)` where `Q(v)` and `¬Y(v)` where not, makes `Q̄ = Y` everywhere.

Taking the setup map to *be* the question map satisfies the middle two at once,
and `𝒟` then charges `−log 2` per probe against a two-element fibre. The value
is unchanged by the twist, because the setup partition is what carries it.
-/

namespace AISafetyAtlas.Examples.Inference.SelfAwareComplexity

open AISafetyAtlas.Inference

/-- The conclusion: the low half against the high half. -/
public abbrev saConcl : Fin 4 → Bool := ![true, true, false, false]

/-- The question map, chosen **independent** of the conclusion so that all four
`(Y, Q)` pairs are realized. -/
public abbrev saQuestion : Fin 4 → Bool := ![true, false, true, false]

/-- The target. **Not** the conclusion: taking `Γ = Y` makes the device fallible,
because a state whose question is `false` then evaluates to `¬Γ = ¬Y`. Twisting
`Γ` by the question instead makes `Q̄` agree with `Y` everywhere, which is what
§9's standing *infallible* hypothesis requires. Both values are still realized,
so `Γ(U) = 𝔹` and both probes are in play. -/
public abbrev saGamma : Fin 4 → Bool :=
  fun v => if saQuestion v then saConcl v else !saConcl v

/-- The base device. Its setup **is** the question map, so every fibre asks one
question — which is what lets a fibre answer a probe at all — and each fibre has
two states, so the charge is not `0`. -/
public abbrev saBase : InferenceDevice.{0, 0} (Fin 4) where
  Setup := Bool
  setup := saQuestion
  concl := saConcl
  concl_surjective := by decide

/-- The two probes of a `Bool`-valued target, as the device's evaluation map:
question `true` asks *"is `Γ` true?"*, question `false` asks *"is it false?"*. -/
public abbrev saEval : Bool → Fin 4 → Bool :=
  fun q v => if q then saGamma v else !saGamma v

/-- **An admissible self-aware device.** Two question values, four states, all
four `(Y, Q)` pairs realized. -/
public abbrev saDevice : SelfAwareDevice.{0, 0, 0} (Fin 4) where
  toDevice := saBase
  Question := Bool
  question := saQuestion
  eval := saEval
  pair_surjective := by decide

/-- **The paper's §1.2 convention is met**, which `uncorrectable` cannot do: the
question map takes two values. -/
public theorem saDevice_question_two_valued :
    ∃ u u' : Fin 4, saDevice.question u ≠ saDevice.question u' :=
  ⟨0, 1, by decide⟩

/-- …and the four states `four_le_card_of_two_questions` demands are there. -/
public theorem saDevice_card : 4 ≤ Fintype.card (Fin 4) := by decide

/-- The probe of `true` is answered by the setup value `true`, and the probe of
`false` by `false`. Both answering sets are nonempty, so `𝒟` is reached through
genuine minima rather than through the totalization. -/
public theorem saDevice_answers (γ : Bool) :
    γ ∈ questionAnsweringSet saDevice saGamma (probe γ) := by
  rw [mem_questionAnsweringSet_iff]
  refine ⟨?_, ?_⟩
  · cases γ with
    | true => exact ⟨0, by decide⟩
    | false => exact ⟨1, by decide⟩
  · revert γ; decide

public theorem saDevice_answering_nonempty (γ : Bool) :
    (questionAnsweringSet saDevice saGamma (probe γ)).Nonempty :=
  ⟨γ, saDevice_answers γ⟩

/-- Each fibre of the setup map holds two of the four states. -/
public theorem saDevice_fibreCard (x : Bool) : setupFibreCard saBase x = 2 := by
  revert x; decide

/-- So every setup value costs `−log 2`, and the minimum is that constant. -/
public theorem saDevice_setupLength (x : Bool) :
    setupLength saBase x = -Real.log 2 := by
  rw [setupLength, saDevice_fibreCard]
  norm_num


/-! ## The printed hypotheses of §9, discharged

The displayed `𝒟` is introduced for a device that is **infallible**, that
**semi-controls its question**, and that finds `Γ` **intelligible**. The Lean
definition attaches none of them — that is recorded in the §9 row — so a model
of the definition is not automatically a model of the printed object. All three
are proved here, so this one is.
-/

/-- **Infallible.** `Q̄ = Y` at every state: where the question is `true` the
evaluation returns `Γ = Y`, and where it is `false` it returns `¬Γ = Y`. This is
what the twist in `saGamma` buys, and it is why `Γ` is not simply `Y`. -/
public theorem saDevice_infallible : Infallible saDevice := by
  intro u; revert u; decide

/-- **Semi-controls its question.** The setup map *is* the question map, so
fixing a setup value fixes the question. -/
public theorem saBase_semiControls_question : SemiControls saBase saQuestion := by
  intro γ hγ
  exact ⟨γ, hγ, fun _ h => h⟩

/-- **`Γ` is intelligible to the device.** Each question, evaluated, is the probe
of `Γ` at that question's own value. -/
public theorem saDevice_intelligible : Intelligible saDevice saGamma := by
  intro γ f hf _
  refine ⟨γ, ?_, ?_⟩
  · cases γ with
    | true => exact ⟨0, rfl⟩
    | false => exact ⟨1, rfl⟩
  · have hfb : ∀ b : Bool, f b = decide (b = γ) := by
      intro b
      by_cases hb : b = γ
      · simp [hb, (hf γ).mpr rfl]
      · have : f b ≠ true := fun hc => hb ((hf b).mp hc)
        simp [hb, Bool.eq_false_iff.mpr this]
    intro u
    rw [hfb]
    cases γ <;> cases hg : saGamma u <;> simp [saEval, hg]

/-- **`𝒟(Γ ∣ D) = −2 log 2`.** Two probes, each with a nonempty answering set of
two-element fibres. The value is not `0` and not reached by the totalization. -/
public theorem saDevice_selfAwareComplexity :
    selfAwareInferenceComplexity saDevice (setupLength saBase) saGamma
      = -(2 * Real.log 2) := by
  have hrange : rangeFinset saGamma = (Finset.univ : Finset Bool) :=
    Finset.eq_univ_of_forall (fun b => (mem_rangeFinset saGamma b).mpr
      (by cases b; exacts [⟨2, rfl⟩, ⟨0, rfl⟩]))
  rw [selfAwareInferenceComplexity, hrange]
  have hterm : ∀ γ ∈ (Finset.univ : Finset Bool),
      minQuestionLength saDevice (setupLength saBase) saGamma (probe γ)
        = -Real.log 2 := by
    intro γ _
    rw [minQuestionLength, dif_pos (saDevice_answering_nonempty γ)]
    exact Complexity.inf'_of_const (saDevice_answering_nonempty γ) _ _
      (fun y _ => saDevice_setupLength y)
  rw [Finset.sum_congr rfl hterm]
  simp


end AISafetyAtlas.Examples.Inference.SelfAwareComplexity
