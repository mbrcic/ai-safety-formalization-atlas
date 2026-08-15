module

public import AISafetyAtlas.Inference.Complexity.Measure
public import AISafetyAtlas.Inference.Stochastic.Bridge

/-!
# Inference complexity against Shannon entropy — a refuted bound

Wolpert 2018 Proposition 12 claims that inference complexity is bounded by the
Shannon entropy of the setup distribution:

> **Proposition 12.** *"For any ID `D`, probability distribution `μ`, and function
> `Γ` with a countable image such that `D > Γ`, `C_μ(Γ; D) ≤ |Γ| × H_μ(X)`, where
> `H_μ(X)` is the Shannon entropy of `μ(X)`."*

**It is false, and this module refutes it with a four-state model.**

## Why the printed proof does not close

The proof is a three-step chain. Its last step is

`−∑_{x ∈ X(U)} log₂ μ(x)  ≤  |Γ| H_μ(X)  =  −|Γ| ∑_{x ∈ X(U)} μ(x) log₂ μ(x)`,

which compares the two sums term by term. That comparison needs
`|Γ| · μ(x) ≥ 1` — that is, `μ(x) ≥ 1/|Γ|` — at **every** setup value. The
statement assumes nothing of the kind, and a setup value of small mass breaks it.

## The countermodel

`prop12Device` has two setup values and a binary target. One setup answers the
`true` probe and the other answers the `false` probe, and neither answers both —
for a binary target no single setup can, since the two probes of `Γ` disagree
everywhere. So the complexity is the sum of both fibre lengths, and skewing the
mass between the two fibres drives it up while driving the entropy down.

At masses `3/4` and `1/4` the two sides are exactly

* `C_μ(Γ; D) = 4 ln 2 − ln 3`
* `|Γ| × H_μ(X) = 2 H_μ(X) = 4 ln 2 − (3/2) ln 3`

so the claimed inequality fails by exactly `(ln 3)/2`. Nothing is approximated:
`prop12_gap` is an identity, and `prop12_refuted` is its consequence.

The failure is not marginal in the parameter either. As the mass on one fibre
tends to zero the complexity grows without bound while the entropy tends to zero,
so no constant multiple of `H_μ(X)` bounds `C_μ(Γ; D)`.

## What this does not say

The 2008 layer's own complexity results are untouched: Theorem 4's emulation
bound (`inferenceComplexityMeasure_le_of_stronglyInfers`) is a different
statement, is proved, and does not pass through Proposition 12.

Note also that no entropy dependency was needed to state or refute this. The
atlas's `entropyOn` — local discrete Shannon entropy over the setup image, built
for Definition 10 — is exactly the `H_μ(X)` the proposition names. The earlier
ledger position that Proposition 12 was gated behind an entropy purchase was
wrong on that point, and it is corrected here.
-/

namespace AISafetyAtlas.Inference

open MeasureTheory

/-! ## The four-state model -/

/-- Setup: the first two states share one setup value, the last two the other. -/
public abbrev prop12X : Fin 4 → Bool := ![true, true, false, false]

/-- Conclusion. On the first fibre it tracks `Γ`; on the second it is its
negation. -/
public abbrev prop12Y : Fin 4 → Bool := ![true, false, false, true]

/-- Target. Both values occur on each fibre, which is what lets each fibre answer
exactly one probe. -/
public abbrev prop12Gamma : Fin 4 → Bool := ![true, false, true, false]

/-- Masses `3/8, 3/8, 1/8, 1/8`, so the two setup fibres carry `3/4` and `1/4`. -/
public noncomputable def prop12Mass : Fin 4 → ℝ := ![3 / 8, 3 / 8, 1 / 8, 1 / 8]

public noncomputable def prop12PMF : FinPMF (Fin 4) where
  mass := prop12Mass
  nonneg := by intro u; fin_cases u <;> simp only [prop12Mass] <;> norm_num
  sum_one := by simp [prop12Mass, Fin.sum_univ_succ]; norm_num

/-- The device of the countermodel. -/
public abbrev prop12Device : InferenceDevice.{0, 0} (Fin 4) :=
  { Setup := Bool, setup := prop12X, concl := prop12Y, concl_surjective := by decide }

/-- `D > Γ`: the `true` probe is answered on the first fibre and the `false`
probe on the second. This is Proposition 12's own hypothesis, so the countermodel
is inside its scope. -/
public theorem prop12_weaklyInfers : WeaklyInfers prop12Device prop12Gamma := by
  intro γ f hf _
  have hfeq : f = probe γ := IsProbe.eq_of_isProbe hf (isProbe_probe γ)
  subst hfeq
  cases γ
  · exact ⟨false, ⟨2, rfl⟩, by decide⟩
  · exact ⟨true, ⟨0, rfl⟩, by decide⟩

/-! ## The two sides, computed exactly -/

/-- The measure of the countermodel. -/
public noncomputable def prop12Measure : Measure (Fin 4) := prop12PMF.toMeasure

public theorem prop12_mass_true : massOn prop12Measure prop12X true = 3 / 4 := by
  rw [prop12Measure, massOn_toMeasure]
  simp [pushOnImage, prop12PMF, prop12Mass, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

public theorem prop12_mass_false : massOn prop12Measure prop12X false = 1 / 4 := by
  rw [prop12Measure, massOn_toMeasure]
  simp [pushOnImage, prop12PMF, prop12Mass, Finset.sum_filter, Fin.sum_univ_succ]
  norm_num

/-- Only the first fibre answers the `true` probe. -/
public theorem prop12_answering_true :
    answeringSet prop12Device prop12Gamma (probe true) = {true} := by
  ext x
  rw [mem_answeringSet_iff, Finset.mem_singleton]
  cases x
  · exact ⟨fun h => absurd (h.2) (by decide), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => rfl, fun _ => ⟨⟨0, rfl⟩, by decide⟩⟩

/-- Only the second fibre answers the `false` probe. -/
public theorem prop12_answering_false :
    answeringSet prop12Device prop12Gamma (probe false) = {false} := by
  ext x
  rw [mem_answeringSet_iff, Finset.mem_singleton]
  cases x
  · exact ⟨fun _ => rfl, fun _ => ⟨⟨2, rfl⟩, by decide⟩⟩
  · exact ⟨fun h => absurd (h.2) (by decide), fun h => absurd h (by decide)⟩

public theorem prop12_rangeFinset : rangeFinset prop12Gamma = Finset.univ := by
  ext γ
  simp only [Finset.mem_univ, iff_true, mem_rangeFinset]
  cases γ
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

/-- **`C_μ(Γ; D) = 4 ln 2 − ln 3`.** Each probe is answered by exactly one setup,
so the complexity is the sum of the two fibre lengths. -/
public theorem prop12_complexity :
    inferenceComplexityMeasure prop12Measure prop12Device prop12Gamma
      prop12_weaklyInfers = 4 * Real.log 2 - Real.log 3 := by
  rw [inferenceComplexityMeasure, inferenceComplexity_eq_total, inferenceComplexityTotal,
    prop12_rangeFinset]
  rw [show (Finset.univ : Finset Bool) = {false, true} from by decide]
  rw [Finset.sum_pair (by decide : (false : Bool) ≠ true)]
  unfold minAnsweringLength
  rw [dif_pos (by rw [prop12_answering_false]; exact ⟨false, by simp⟩),
    dif_pos (by rw [prop12_answering_true]; exact ⟨true, by simp⟩)]
  simp only [prop12_answering_false, prop12_answering_true, Finset.inf'_singleton]
  unfold measureLength
  rw [prop12_mass_true, prop12_mass_false]
  rw [show (3 : ℝ) / 4 = 3 / 4 from rfl, show (1 : ℝ) / 4 = 1 / 4 from rfl]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
  push_cast
  rw [Real.log_one]
  ring

/-- **`H_μ(X) = 2 ln 2 − (3/4) ln 3`.** -/
public theorem prop12_entropy :
    entropyOn prop12Measure prop12X = 2 * Real.log 2 - 3 / 4 * Real.log 3 := by
  have hrange : rangeFinset prop12X = Finset.univ := by
    ext x
    simp only [Finset.mem_univ, iff_true, mem_rangeFinset]
    cases x
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩
  unfold entropyOn
  rw [hrange, show (Finset.univ : Finset Bool) = {false, true} from by decide,
    Finset.sum_pair (by decide : (false : Bool) ≠ true),
    prop12_mass_true, prop12_mass_false,
    if_neg (by norm_num), if_neg (by norm_num)]
  rw [Real.log_div (by norm_num) (by norm_num), Real.log_div (by norm_num) (by norm_num),
    show (4 : ℝ) = 2 ^ 2 from by norm_num, Real.log_pow]
  push_cast
  rw [Real.log_one]
  ring

/-- **The gap is exactly `(ln 3)/2`.** An identity, not an estimate. -/
public theorem prop12_gap :
    inferenceComplexityMeasure prop12Measure prop12Device prop12Gamma
        prop12_weaklyInfers
      - (rangeFinset prop12Gamma).card * entropyOn prop12Measure prop12X
      = Real.log 3 / 2 := by
  rw [prop12_complexity, prop12_entropy, prop12_rangeFinset]
  simp only [Finset.card_univ, Fintype.card_bool, Nat.cast_ofNat]
  ring

/--
**Wolpert 2018, Proposition 12 is refuted.** *"`C_μ(Γ; D) ≤ |Γ| × H_μ(X)`."*

The countermodel satisfies every printed hypothesis — `μ` is a probability
measure, `Γ` has a finite (hence countable) image, and `D > Γ` — and the
inequality fails by `(ln 3)/2`.
-/
public theorem prop12_refuted :
    ¬ (inferenceComplexityMeasure prop12Measure prop12Device prop12Gamma
        prop12_weaklyInfers
      ≤ (rangeFinset prop12Gamma).card * entropyOn prop12Measure prop12X) := by
  intro h
  have hgap := prop12_gap
  have hpos : 0 < Real.log 3 / 2 := by
    have : 0 < Real.log 3 := Real.log_pos (by norm_num)
    linarith
  linarith

end AISafetyAtlas.Inference
