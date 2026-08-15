module

public import AISafetyAtlas.Inference.Complexity.Measure
public import AISafetyAtlas.Inference.Stochastic.Bridge

/-!
# Complexity inversion under strong inference

Wolpert 2018 Proposition 14:

> *"There are devices `D`, `D′`, probability distribution `P` defined over `U`,
> and function `Γ`, such that `D > Γ`, `D′ ≫ D`, and `C_P(Γ; D)` is arbitrarily
> large, while `C_P(Γ; D′)` is arbitrarily close to the minimum value of
> `|Γ| × ln(|Γ(U)|)`."*

A device that can emulate another can be far *simpler* to use than the device it
emulates. Proposition 13 bounds `C(D′) − C(D)` from above; Proposition 14 says
nothing bounds it from below.

**The statement is true and is proved here. The printed proof is not.**

## The floor is real

For a binary target the two probes disagree at every point, so no single setup
answers both: any device inferring `Γ` needs two distinct answering fibres, of
masses `m₁ + m₂ ≤ 1`, and `−ln m₁ − ln m₂ ≥ 2 ln 2` with equality at
`m₁ = m₂ = 1/2`. So `|Γ(U)| ln |Γ(U)| = 2 ln 2` is genuinely the least value
`C_P(Γ; ·)` can take, which is what the proposition's target value names.

## Why Figure 7 does not establish it

The printed proof is the twelve-state Figure 7 with `1/4 < p < 1`, completed by
taking `p → 1`. Its first claim checks out: `C_P(Γ; D) = −2 ln((1 − p)/2)`, which
does diverge, exactly as the source computes.

The second does not. Reading Figure 7's columns, the fibres of `D′` that answer
the `−1`-probe are `X′ ∈ {2, 3}`, and **both** carry mass `(1 − p)/4`. The two
fibres carrying the large mass `p/2`, namely `X′ ∈ {5, 6}`, both answer the
`+1`-probe and neither answers the `−1`-probe. So

`C_P(Γ; D′) = −ln(max((1−p)/4, p/2)) − ln((1 − p)/4)`,

which **also diverges** as `p → 1`, rather than approaching `2 ln 2`. Minimizing
over the admissible range gives `≈ 3.47` at `p = 1/2`, never near `1.386`. The
figure does exhibit an unbounded *gap* — `C(Γ; D) − C(Γ; D′) → ∞` — but not the
printed convergence. Recorded as clash 24.

## The construction that does work

`invDevice` and `invDevice'` below, over eight states. The point Figure 7 misses
is that the two large fibres of `D′` must answer *different* probes. Here they
do: the emulating device splits one heavy fibre of `D` into two halves, one
carrying `Y′ = Y` and the other `Y′ = −Y`, and because `Y = δ_{+1}(Γ)` there,
those halves answer the `+1` and `−1` probes respectively. Each has mass
`(1 − ε)/2`, so

* `C_P(Γ; D′) = 2 ln 2 − 2 ln(1 − ε)`, which tends to the floor `2 ln 2`;
* `C_P(Γ; D)  = −ln(1 − ε) − ln ε`, which diverges.

Both are identities in `ε`, so the "arbitrarily large" and "arbitrarily close"
of the printed statement follow from algebra rather than from an estimate.
-/

namespace AISafetyAtlas.Inference

open MeasureTheory

/-! ## The eight-state model -/

/-- `D`'s setup: one heavy fibre and one light one. -/
public abbrev invX : Fin 8 → Bool := ![true, true, true, true, false, false, false, false]

/-- `D`'s conclusion. On the heavy fibre it is `δ_{+1}(Γ)`; on the light one
`δ_{−1}(Γ)`. That is what makes each fibre answer exactly one probe. -/
public abbrev invY : Fin 8 → Bool := ![true, false, true, false, false, true, false, true]

/-- `D′`'s setup: each fibre of `D` split in two, which is the least strong
inference can require. -/
public abbrev invX' : Fin 8 → Fin 4 := ![0, 0, 1, 1, 2, 2, 3, 3]

/-- `D′`'s conclusion: `Y` on the first half of each `D`-fibre, `¬Y` on the
second. -/
public abbrev invY' : Fin 8 → Bool := ![true, false, false, true, false, true, true, false]

/-- The target, alternating within every `D′` fibre. -/
public abbrev invGamma : Fin 8 → Bool := ![true, false, true, false, true, false, true, false]

/-- Mass `(1 − ε)/4` on each heavy state and `ε/4` on each light one, so the two
`D`-fibres carry `1 − ε` and `ε`, and the four `D′`-fibres carry `(1 − ε)/2`
twice and `ε/2` twice. -/
public noncomputable def invMass (ε : ℝ) : Fin 8 → ℝ :=
  ![(1 - ε) / 4, (1 - ε) / 4, (1 - ε) / 4, (1 - ε) / 4, ε / 4, ε / 4, ε / 4, ε / 4]

public noncomputable def invPMF (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : FinPMF (Fin 8) where
  mass := invMass ε
  nonneg := by intro u; fin_cases u <;> simp only [invMass] <;> norm_num <;> linarith
  sum_one := by simp [invMass, Fin.sum_univ_succ]; ring

public noncomputable def invMeasure (ε : ℝ) (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : Measure (Fin 8) :=
  (invPMF ε h0 h1).toMeasure

/-- `D`. -/
public abbrev invDevice : InferenceDevice.{0, 0} (Fin 8) :=
  { Setup := Bool, setup := invX, concl := invY, concl_surjective := by decide }

/-- `D′`, which strongly infers `D`. -/
public abbrev invDevice' : InferenceDevice.{0, 0} (Fin 8) :=
  { Setup := Fin 4, setup := invX', concl := invY', concl_surjective := by decide }

/-- `D > Γ`: the heavy fibre answers the `+1` probe, the light one the `−1`
probe. -/
public theorem inv_weaklyInfers : WeaklyInfers invDevice invGamma := by
  intro γ f hf _
  have hfeq : f = probe γ := IsProbe.eq_of_isProbe hf (isProbe_probe γ)
  subst hfeq
  cases γ
  · exact ⟨false, ⟨4, rfl⟩, by decide⟩
  · exact ⟨true, ⟨0, rfl⟩, by decide⟩

/-- `D′ ≫ D`: each `D`-fibre is split into a half carrying `Y` and a half
carrying `¬Y`, which is exactly what the two probes of `Y` require. -/
public theorem inv_stronglyInfers : StronglyInfers invDevice' invDevice := by
  intro γ f hf _ x₂ _
  have hfeq : f = probe γ := IsProbe.eq_of_isProbe hf (isProbe_probe γ)
  subst hfeq
  cases γ <;> cases x₂
  · exact ⟨3, ⟨6, rfl⟩, by decide⟩
  · exact ⟨1, ⟨2, rfl⟩, by decide⟩
  · exact ⟨2, ⟨4, rfl⟩, by decide⟩
  · exact ⟨0, ⟨0, rfl⟩, by decide⟩

/-! ## The two complexities, computed exactly -/

section Values

variable {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)

public theorem inv_mass_X_true :
    massOn (invMeasure ε h0 h1) invX true = 1 - ε := by
  rw [invMeasure, massOn_toMeasure]
  simp [pushOnImage, invPMF, invMass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

public theorem inv_mass_X_false :
    massOn (invMeasure ε h0 h1) invX false = ε := by
  rw [invMeasure, massOn_toMeasure]
  simp [pushOnImage, invPMF, invMass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

public theorem inv_mass_X'_zero :
    massOn (invMeasure ε h0 h1) invX' 0 = (1 - ε) / 2 := by
  rw [invMeasure, massOn_toMeasure]
  simp [pushOnImage, invPMF, invMass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

public theorem inv_mass_X'_one :
    massOn (invMeasure ε h0 h1) invX' 1 = (1 - ε) / 2 := by
  rw [invMeasure, massOn_toMeasure]
  simp [pushOnImage, invPMF, invMass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

public theorem inv_mass_X'_two :
    massOn (invMeasure ε h0 h1) invX' 2 = ε / 2 := by
  rw [invMeasure, massOn_toMeasure]
  simp [pushOnImage, invPMF, invMass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

public theorem inv_mass_X'_three :
    massOn (invMeasure ε h0 h1) invX' 3 = ε / 2 := by
  rw [invMeasure, massOn_toMeasure]
  simp [pushOnImage, invPMF, invMass, Finset.sum_filter, Fin.sum_univ_succ]
  ring

end Values

public theorem inv_rangeFinset : rangeFinset invGamma = Finset.univ := by
  ext γ
  simp only [Finset.mem_univ, iff_true, mem_rangeFinset]
  cases γ
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

/-! ### Answering sets

`D` answers each probe on exactly one fibre. `D′` answers each on two — one heavy
and one light — and **the two heavy fibres answer different probes**, which is
precisely what Figure 7 fails to arrange.
-/

public theorem inv_answering_true :
    answeringSet invDevice invGamma (probe true) = {true} := by
  ext x
  rw [mem_answeringSet_iff, Finset.mem_singleton]
  cases x
  · exact ⟨fun h => absurd h.2 (by decide), fun h => absurd h (by decide)⟩
  · exact ⟨fun _ => rfl, fun _ => ⟨⟨0, rfl⟩, by decide⟩⟩

public theorem inv_answering_false :
    answeringSet invDevice invGamma (probe false) = {false} := by
  ext x
  rw [mem_answeringSet_iff, Finset.mem_singleton]
  cases x
  · exact ⟨fun _ => rfl, fun _ => ⟨⟨4, rfl⟩, by decide⟩⟩
  · exact ⟨fun h => absurd h.2 (by decide), fun h => absurd h (by decide)⟩

public theorem inv_answering'_true :
    answeringSet invDevice' invGamma (probe true) = {0, 3} := by
  ext x
  rw [mem_answeringSet_iff, Finset.mem_insert, Finset.mem_singleton]
  fin_cases x
  · exact ⟨fun _ => Or.inl rfl, fun _ => ⟨⟨0, rfl⟩, by decide⟩⟩
  · exact ⟨fun h => absurd h.2 (by decide), fun h => by rcases h with h | h <;> exact absurd h (by decide)⟩
  · exact ⟨fun h => absurd h.2 (by decide), fun h => by rcases h with h | h <;> exact absurd h (by decide)⟩
  · exact ⟨fun _ => Or.inr rfl, fun _ => ⟨⟨6, rfl⟩, by decide⟩⟩

public theorem inv_answering'_false :
    answeringSet invDevice' invGamma (probe false) = {1, 2} := by
  ext x
  rw [mem_answeringSet_iff, Finset.mem_insert, Finset.mem_singleton]
  fin_cases x
  · exact ⟨fun h => absurd h.2 (by decide), fun h => by rcases h with h | h <;> exact absurd h (by decide)⟩
  · exact ⟨fun _ => Or.inl rfl, fun _ => ⟨⟨2, rfl⟩, by decide⟩⟩
  · exact ⟨fun _ => Or.inr rfl, fun _ => ⟨⟨4, rfl⟩, by decide⟩⟩
  · exact ⟨fun h => absurd h.2 (by decide), fun h => by rcases h with h | h <;> exact absurd h (by decide)⟩

private theorem inf'_pair {α : Type w} [DecidableEq α] {a b : α} (f : α → ℝ)
    (h : ({a, b} : Finset α).Nonempty) :
    ({a, b} : Finset α).inf' h f = min (f a) (f b) := by
  apply le_antisymm
  · exact le_min (Finset.inf'_le _ (by simp)) (Finset.inf'_le _ (by simp))
  · refine Finset.le_inf' _ _ (fun x hx => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact min_le_left _ _
    · exact min_le_right _ _

section Complexity

variable {ε : ℝ} (hpos : 0 < ε) (hhalf : ε ≤ 1 / 2)

/-- **`C_P(Γ; D) = −ln ε − ln(1 − ε)`**, which diverges as `ε → 0`. -/
public theorem inv_complexity :
    inferenceComplexityMeasure (invMeasure ε hpos.le (by linarith)) invDevice invGamma
        inv_weaklyInfers
      = -Real.log ε - Real.log (1 - ε) := by
  rw [inferenceComplexityMeasure, inferenceComplexity_eq_total, inferenceComplexityTotal,
    inv_rangeFinset, show (Finset.univ : Finset Bool) = {false, true} from by decide,
    Finset.sum_pair (by decide : (false : Bool) ≠ true)]
  unfold minAnsweringLength
  rw [dif_pos (by rw [inv_answering_false]; exact ⟨false, by simp⟩),
    dif_pos (by rw [inv_answering_true]; exact ⟨true, by simp⟩)]
  simp only [inv_answering_false, inv_answering_true, Finset.inf'_singleton]
  unfold measureLength
  rw [inv_mass_X_true, inv_mass_X_false]
  ring

/-- **`C_P(Γ; D′) = 2 ln 2 − 2 ln(1 − ε)`**, which tends to the floor `2 ln 2`.

The heavy fibres `0` and `3` answer *different* probes, so both minima are taken
at mass `(1 − ε)/2`. That is the step Figure 7 does not achieve. -/
public theorem inv_complexity' :
    inferenceComplexityMeasure (invMeasure ε hpos.le (by linarith)) invDevice' invGamma
        (weaklyInfers_of_stronglyInfers inv_stronglyInfers inv_weaklyInfers)
      = 2 * Real.log 2 - 2 * Real.log (1 - ε) := by
  have hlt : ε / 2 ≤ (1 - ε) / 2 := by linarith
  have hp2 : (0 : ℝ) < ε / 2 := by linarith
  have hmin : -Real.log ((1 - ε) / 2) ≤ -Real.log (ε / 2) := by
    simpa using Real.log_le_log hp2 hlt
  rw [inferenceComplexityMeasure, inferenceComplexity_eq_total, inferenceComplexityTotal,
    inv_rangeFinset, show (Finset.univ : Finset Bool) = {false, true} from by decide,
    Finset.sum_pair (by decide : (false : Bool) ≠ true)]
  unfold minAnsweringLength
  rw [dif_pos (by rw [inv_answering'_false]; exact ⟨1, by simp⟩),
    dif_pos (by rw [inv_answering'_true]; exact ⟨0, by simp⟩)]
  simp only [inv_answering'_false, inv_answering'_true]
  rw [inf'_pair, inf'_pair]
  unfold measureLength
  rw [inv_mass_X'_zero, inv_mass_X'_one, inv_mass_X'_two, inv_mass_X'_three,
    min_eq_left hmin, Real.log_div (by linarith) (by norm_num)]
  ring

end Complexity

/--
**Wolpert 2018, Proposition 14.** *"There are devices `D`, `D′`, probability
distribution `P`, and function `Γ`, such that `D > Γ`, `D′ ≫ D`, and
`C_P(Γ; D)` is arbitrarily large, while `C_P(Γ; D′)` is arbitrarily close to the
minimum value `|Γ(U)| ln|Γ(U)|`."*

`|Γ(U)| = 2` here, so the floor is `2 ln 2`. Both quantities are exact
identities in `ε`, so no limit is taken: given a target `M` for the first and a
tolerance `δ` for the second, the `ε` achieving both is named.

`M` is unconstrained: the complexity of `D` exceeds *any* real, not merely any
positive one.
-/
public theorem exists_complexity_inversion {M δ : ℝ} (hδ : 0 < δ) :
    ∃ (ε : ℝ) (hpos : 0 < ε) (hhalf : ε ≤ 1 / 2),
      StronglyInfers invDevice' invDevice ∧
      WeaklyInfers invDevice invGamma ∧
      M < inferenceComplexityMeasure (invMeasure ε hpos.le (by linarith)) invDevice
            invGamma inv_weaklyInfers ∧
      inferenceComplexityMeasure (invMeasure ε hpos.le (by linarith)) invDevice'
            invGamma (weaklyInfers_of_stronglyInfers inv_stronglyInfers inv_weaklyInfers)
        < 2 * Real.log 2 + δ := by
  -- Small enough to make `−ln ε` exceed `M`, and to keep `−2 ln(1 − ε)` under `δ`.
  set e : ℝ := min (Real.exp (-M - 1)) (min ((1 - Real.exp (-δ / 2)) / 2) (1 / 2)) with he
  have hexp1 : (0 : ℝ) < Real.exp (-M - 1) := Real.exp_pos _
  have hd : Real.exp (-δ / 2) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  have hexp2 : (0 : ℝ) < (1 - Real.exp (-δ / 2)) / 2 := by linarith
  have hpos : 0 < e := lt_min hexp1 (lt_min hexp2 (by norm_num))
  have hhalf : e ≤ 1 / 2 := le_trans (min_le_right _ _) (min_le_right _ _)
  refine ⟨e, hpos, hhalf, inv_stronglyInfers, inv_weaklyInfers, ?_, ?_⟩
  · rw [inv_complexity hpos hhalf]
    have h1 : e ≤ Real.exp (-M - 1) := min_le_left _ _
    have h2 : Real.log e ≤ -M - 1 := by
      calc Real.log e ≤ Real.log (Real.exp (-M - 1)) := Real.log_le_log hpos h1
        _ = -M - 1 := Real.log_exp _
    have h3 : Real.log (1 - e) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  · rw [inv_complexity' hpos hhalf]
    have h1 : e ≤ (1 - Real.exp (-δ / 2)) / 2 := le_trans (min_le_right _ _) (min_le_left _ _)
    -- Strictly less, which is what the strict `<` in the conclusion needs:
    -- `1 − e ≥ (1 + exp(−δ/2))/2 > exp(−δ/2)` because `exp(−δ/2) < 1`.
    have h2 : Real.exp (-δ / 2) < 1 - e := by linarith
    have h3 : -δ / 2 < Real.log (1 - e) := by
      calc -δ / 2 = Real.log (Real.exp (-δ / 2)) := (Real.log_exp _).symm
        _ < Real.log (1 - e) := Real.log_lt_log (Real.exp_pos _) h2
    linarith

end AISafetyAtlas.Inference
