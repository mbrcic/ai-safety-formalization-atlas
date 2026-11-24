module

public import AISafetyAtlas.Control.RequisiteVariety
public import AISafetyAtlas.InformationTheory.DataProcessing

/-!
# Ashby's channel capacity: an entropy *rate*

W. R. Ashby, *An Introduction to Cybernetics*, Chapman & Hall, 1956 (second
impression 1957), §9/12, §9/15 and §11/11.

`AISafetyAtlas.InformationTheory.channelCapacity` renders §11/11's capacity
as the noiseless alphabet ceiling `log |O|`. That reproduces the four §11/11
exercises, which count signals, but it is not the quantity §9/15 defines. This
module supplies the printed one.

## What §9/12 defines

> Shannon defines the entropy (of one step of the chain) as the average of these
> entropies, each being weighted by the proportion in which that state,
> corresponding to the column, occurs when the sequence has settled to its
> equilibrium.

That is `chainRate` below: a weighted average of the column entropies of a
transition kernel, the weights being an equilibrium distribution. It is written
here from the printed data — an equilibrium law and a kernel — with no sample
space, and `chainRate_eq_condEntropy` identifies it with `H[X₁ | X₀]` on any
process realizing that pair law.

## What §9/15 asserts

Two things. First, a theorem:

> Briefly it can be said that the entropy of a length of Markov chain is
> proportional to its length (provided always that it has settled down to
> equilibrium).

`entropy_traj` is that statement, and it shows the printed word *proportional* is
slightly loose: the exact identity is `H[X₀ … Xₙ] = H[X₀] + n · rate`, an affine
function of the length rather than a linear one. The two agree exactly when
`H[X₀] = rate`, which is the case in Ashby's own illustration — a spun coin, where
both are one bit — so the example he checks it against cannot distinguish them.

Second, the definition of capacity, from the worked insect chain:

> if (as in S.9/12) the insects' "unit time" for one step is twenty seconds, then
> as each 20 seconds produces 0.84 bits, 60 seconds will produce (60/20)0.84
> bits; so each insect is producing variety of location at the rate of 2.53 bits
> per minute. **Such a rate is the most natural way of measuring the capacity of
> a channel.**

`ashbyCapacity` is that rate, and `ashbyCapacity_rescale` is the conversion
sentence itself: measuring in units in which a step takes `1/n` of a unit
multiplies the capacity by `n`.

## What this buys §11/11

`entropy_outcome_ge_sub_chainEntropy` is §11/11's bound —
*"R's capacity as a regulator cannot exceed R's capacity as a channel of
communication"* — with the regulator's channel taken to be its own trajectory and
the capacity taken to be the printed rate. Note the shape: because the trajectory
entropy is `H[X₀] + n · rate` and not `n · rate`, a bare *capacity × time* budget
is **not** an upper bound on what the regulator can carry; the initial state's own
entropy is there too. The exact identity is what is stated.

`eventually_regulationRate_le_ashbyCapacity` puts both sides of §11/11 per unit
time: the regulator's capacity read as `regulationRate`, the variety it removes
per unit time over a run of acts, is in the long run at most `ashbyCapacity`.
It is asymptotic because of the `H[X₀]` term of the window bound.

## Units

PFR's `Hm` is a natural-logarithm entropy; Ashby's figures are bits. Everything
here is stated unit-free, as closed forms and as the rescaling identity, so no
`log 2` conversion is buried in a statement. The worked example in
`AISafetyAtlas.Examples.Control.ChannelRate` says which quantity matches which of
Ashby's printed numbers.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uΩ uS

variable {Ω : Type uΩ} {S : Type uS}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S]

/-! ## §9/12: the entropy of one step of a chain -/

/--
**Ashby's §9/12 entropy of one step of a Markov chain**, from the printed data
alone: the average of the columns' entropies, each weighted by the equilibrium
proportion of its state.

`stat` is the equilibrium law — Ashby's *"the proportion in which that state …
occurs when the sequence has settled to its equilibrium"* — and `κ` is the
transition kernel, whose value at `s` is that state's column.
-/
@[expose] public noncomputable def chainRate [Fintype S] (stat : Measure S)
    (κ : Kernel S S) : ℝ :=
  ∑ s, stat.real {s} * Hm[κ s]

/-! ## §9/15, first claim: the entropy of a length of chain -/

section Trajectory

variable [Fintype S] [Nonempty S]

/-- The first `n` states of a process, as a single random variable. -/
@[expose] public def traj (X : ℕ → Ω → S) (n : ℕ) : Ω → (Fin n → S) :=
  fun ω i => X i ω

omit [MeasurableSingletonClass S] [Fintype S] [Nonempty S] in
public theorem measurable_traj {X : ℕ → Ω → S} (hX : ∀ n, Measurable (X n)) (n : ℕ) :
    Measurable (traj X n) :=
  measurable_pi_lambda _ fun i => hX i

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S]
  [Nonempty S] in
/-- Extending a trajectory by one step is an injective recoding of the pair
"trajectory so far, next state". -/
public theorem traj_succ (X : ℕ → Ω → S) (n : ℕ) :
    traj X (n + 1)
      = (fun p : (Fin n → S) × S => (Fin.snoc p.1 p.2 : Fin (n + 1) → S)) ∘ ⟨traj X n, X n⟩ := by
  funext ω i
  induction i using Fin.lastCases with
  | last => simp [traj]
  | cast i => simp [traj]

omit [MeasurableSpace S] [MeasurableSingletonClass S] [Fintype S] [Nonempty S] in
public theorem injective_snoc (n : ℕ) :
    Function.Injective (fun p : (Fin n → S) × S => (Fin.snoc p.1 p.2 : Fin (n + 1) → S)) := by
  rintro ⟨f, a⟩ ⟨g, b⟩ h
  have hlast : a = b := by
    simpa [Fin.snoc_last] using congrFun h (Fin.last n)
  have hrest : f = g := by
    funext i
    simpa [Fin.snoc_castSucc] using congrFun h i.castSucc
  simp [hlast, hrest]

omit [Nonempty S] in
/--
**Ashby's §9/15 proportionality, exactly.** For a process that is Markov and
stationary — his *"provided always that it has settled down to equilibrium"* —
the entropy of the first `n + 1` states is the entropy of the initial state plus
`n` times the one-step rate.

The printed word is *proportional*; the identity is **affine**. The two coincide
exactly when `H[X₀]` equals the rate, which is what happens in Ashby's own
illustration (a spun coin, both one bit), so his check does not separate them.
-/
public theorem entropy_traj (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : ℕ → Ω → S} (hX : ∀ n, Measurable (X n))
    (hMarkov : ∀ k, CondIndepFun (X (k + 1)) (traj X k) (X k) μ)
    (hStat : ∀ k, IdentDistrib (⟨X (k + 1), X k⟩ : Ω → S × S)
      (⟨X 1, X 0⟩ : Ω → S × S) μ μ) (n : ℕ) :
    H[traj X (n + 1) ; μ] = H[X 0 ; μ] + n * H[X 1 | X 0 ; μ] := by
  induction n with
  | zero =>
    have h1 : traj X 1 = (fun s : S => (fun _ => s : Fin 1 → S)) ∘ X 0 := by
      funext ω i
      simp [traj, Fin.fin_one_eq_zero i]
    have hinj : Function.Injective (fun s : S => (fun _ => s : Fin 1 → S)) := by
      intro a b h
      simpa using congrFun h 0
    rw [h1, entropy_comp_of_injective μ (hX 0) _ hinj]
    simp
  | succ k ih =>
    -- chain rule: extend the trajectory by one state
    have hstep : H[traj X (k + 2) ; μ]
        = H[traj X (k + 1) ; μ] + H[X (k + 1) | traj X (k + 1) ; μ] := by
      rw [show k + 2 = (k + 1) + 1 from rfl, traj_succ X (k + 1),
        entropy_comp_of_injective μ
          ((measurable_traj hX (k + 1)).prodMk (hX (k + 1))) _ (injective_snoc (k + 1))]
      exact chain_rule' μ (measurable_traj hX (k + 1)) (hX (k + 1))
    -- the Markov property collapses the conditioning to the previous state
    have hcollapse : H[X (k + 1) | traj X (k + 1) ; μ] = H[X (k + 1) | X k ; μ] := by
      have hI : I[X (k + 1) : traj X k | X k ; μ] = 0 :=
        (condMutualInfo_eq_zero (hX (k + 1)) (measurable_traj hX k)).mpr (hMarkov k)
      rw [condMutualInfo_eq' (hX (k + 1)) (measurable_traj hX k) (hX k) μ] at hI
      have hrecode : H[X (k + 1) | traj X (k + 1) ; μ]
          = H[X (k + 1) | ⟨traj X k, X k⟩ ; μ] := by
        rw [traj_succ X k]
        exact condEntropy_of_injective' μ (hX (k + 1))
          ((measurable_traj hX k).prodMk (hX k)) _ (injective_snoc k)
          (traj_succ X k ▸ measurable_traj hX (k + 1))
      rw [hrecode]
      linarith
    -- stationarity moves it to the first step
    have hstat : H[X (k + 1) | X k ; μ] = H[X 1 | X 0 ; μ] :=
      (hStat k).condEntropy_eq (hX (k + 1)) (hX k) (hX 1) (hX 0)
    rw [hstep, ih, hcollapse, hstat]
    push_cast
    ring

end Trajectory

/-! ## §9/15, second claim: capacity is that entropy per unit time -/

/--
**Ashby's channel capacity.** *"Such a rate is the most natural way of measuring
the capacity of a channel"*: the entropy produced per step, divided by the time a
step takes.
-/
@[expose] public noncomputable def ashbyCapacity (rate stepDuration : ℝ) : ℝ :=
  rate / stepDuration

/--
**The §9/15 conversion sentence.** *"if the insects' unit time for one step is
twenty seconds, then as each 20 seconds produces 0.84 bits, 60 seconds will
produce (60/20)0.84 bits"*: measuring time in units containing `n` steps
multiplies the capacity by `n`.
-/
public theorem ashbyCapacity_rescale (rate stepDuration : ℝ) (_hstep : stepDuration ≠ 0)
    (n : ℝ) :
    ashbyCapacity rate (stepDuration / n) = n * ashbyCapacity rate stepDuration := by
  rw [ashbyCapacity, ashbyCapacity, div_div_eq_mul_div, mul_comm, mul_div_assoc]

/-- Capacity times elapsed time recovers the entropy produced, which is what
makes the rate a budget at all. -/
public theorem ashbyCapacity_mul (rate stepDuration : ℝ) (hstep : stepDuration ≠ 0) :
    ashbyCapacity rate stepDuration * stepDuration = rate := by
  rw [ashbyCapacity, div_mul_cancel₀ _ hstep]

/-! ## §9/12's formula is the conditional entropy of one step -/

section Identification

variable [Fintype S]

omit [MeasurableSingletonClass S] [Fintype S] in
/-- The equilibrium law is the first marginal of the canonical one-step chain. -/
public theorem compProd_fst_preimage (stat : Measure S) [IsProbabilityMeasure stat]
    (κ : Kernel S S) [IsMarkovKernel κ] (s : S) (hs : MeasurableSet ({s} : Set S)) :
    (stat ⊗ₘ κ) (Prod.fst ⁻¹' {s}) = stat {s} := by
  rw [← Measure.fst_apply hs, Measure.fst_compProd]

omit [Fintype S] in
/-- The canonical chain puts mass `stat {s} * κ s {t}` on the transition `s → t`. -/
public theorem compProd_singleton (stat : Measure S) [IsProbabilityMeasure stat]
    (κ : Kernel S S) [IsMarkovKernel κ] (s t : S) :
    (stat ⊗ₘ κ) {(s, t)} = stat {s} * κ s {t} := by
  rw [Measure.compProd_apply (MeasurableSet.singleton _),
    lintegral_eq_single _ s _ ?_]
  · have hps : (Prod.mk s ⁻¹' ({(s, t)} : Set (S × S))) = ({t} : Set S) := by
      ext y; simp [Prod.ext_iff]
    rw [hps, mul_comm]
  · intro b hb
    have hempty : (Prod.mk b ⁻¹' ({(s, t)} : Set (S × S))) = (∅ : Set S) := by
      ext y; simp [Prod.ext_iff, hb]
    rw [hempty, measure_empty]

/-- On the canonical chain — draw the state from its equilibrium law, then take
one step — the conditional law of the next state given `s` is the column `κ s`. -/
public theorem map_snd_cond_compProd (stat : Measure S) [IsProbabilityMeasure stat]
    (κ : Kernel S S) [IsMarkovKernel κ] {s : S} (hs : stat {s} ≠ 0) :
    ((stat ⊗ₘ κ)[|Prod.fst ⁻¹' {s}]).map Prod.snd = κ s := by
  have hfst := compProd_fst_preimage stat κ s (MeasurableSet.singleton s)
  refine Measure.ext_of_singleton fun t => ?_
  have hrect : (Prod.fst ⁻¹' {s} ∩ Prod.snd ⁻¹' {t} : Set (S × S)) = {(s, t)} := by
    ext p; simp [Prod.ext_iff]
  rw [Measure.map_apply measurable_snd (MeasurableSet.singleton t),
    cond_apply (measurable_fst (MeasurableSet.singleton s)), hrect, hfst,
    compProd_singleton stat κ s t, ← mul_assoc,
    ENNReal.inv_mul_cancel hs (measure_ne_top stat _), one_mul]

/--
**§9/12's weighted average is the conditional entropy of one step.** Ashby's
formula — *"the average of these entropies, each being weighted by the proportion
in which that state … occurs when the sequence has settled to its equilibrium"* —
computes `H[X₁ | X₀]` on the canonical chain that draws `X₀` from the equilibrium
law and takes one step.

This is the printed object identified with the quantity `entropy_traj` is stated
in, so the rate in that theorem is Ashby's own.
-/
public theorem chainRate_eq_condEntropy (stat : Measure S) [IsProbabilityMeasure stat]
    (κ : Kernel S S) [IsMarkovKernel κ] :
    chainRate stat κ = H[Prod.snd | Prod.fst ; stat ⊗ₘ κ] := by
  rw [condEntropy_eq_sum_fintype _ _ _ measurable_fst, chainRate]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hfst : (stat ⊗ₘ κ).real (Prod.fst ⁻¹' {s}) = stat.real {s} := by
    rw [measureReal_def, compProd_fst_preimage stat κ s (MeasurableSet.singleton s),
      measureReal_def]
  by_cases hs : stat {s} = 0
  · have hz : stat.real {s} = 0 := by simp [measureReal_def, hs]
    rw [hfst, hz, zero_mul, zero_mul]
  · rw [hfst, entropy_def, map_snd_cond_compProd stat κ hs]

end Identification

/-! ## §11/11 against the printed capacity -/

section Regulation

universe uD uR uE

variable {D : Type uD} {R : Type uR} {E : Type uE}
variable [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D]
variable [MeasurableSpace R] [MeasurableSingletonClass R] [Countable R]
variable [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]

/--
**§11/11 with Ashby's own capacity.** *"R's capacity as a regulator cannot exceed
R's capacity as a channel of communication."* The regulator watches the first
`n + 1` states of a stationary Markov chain and responds with any function of what
it saw; the disturbance's entropy survives in the outcome except for what that
channel could carry.

The budget is the **exact** trajectory entropy `H[X₀] + n · rate`, not `n · rate`.
Ashby's *"proportional to its length"* would suggest the latter, and it is not an
upper bound: the initial state carries entropy of its own. See `entropy_traj`.
-/
public theorem entropy_outcome_ge_sub_chainEntropy [Fintype S] [Nonempty S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Dv : Ω → D} (hD : Measurable Dv) [FiniteRange Dv]
    {X : ℕ → Ω → S} (hX : ∀ n, Measurable (X n))
    (hMarkov : ∀ k, CondIndepFun (X (k + 1)) (traj X k) (X k) μ)
    (hStat : ∀ k, IdentDistrib (⟨X (k + 1), X k⟩ : Ω → S × S)
      (⟨X 1, X 0⟩ : Ω → S × S) μ μ) (n : ℕ)
    (σ : (Fin (n + 1) → S) → R) (hσ : Measurable σ)
    (T : D → R → E) (hT : Measurable fun p : D × R => T p.1 p.2)
    (hcol : ∀ r : R, Function.Injective fun d => T d r) :
    H[Dv ; μ] - (H[X 0 ; μ] + n * H[X 1 | X 0 ; μ])
      ≤ H[(fun ω => T (Dv ω) (σ (traj X (n + 1) ω))) ; μ] := by
  have : FiniteRange (traj X (n + 1)) := ⟨Set.toFinite _⟩
  have : FiniteRange (σ ∘ traj X (n + 1)) :=
    ⟨Set.Finite.subset (Set.finite_range σ) (Set.range_comp_subset_range _ _)⟩
  have hmain := entropy_outcome_ge (Rv := σ ∘ traj X (n + 1)) μ hD
    (hσ.comp (measurable_traj hX (n + 1))) T hT hcol
  have hnn : 0 ≤ H[σ ∘ traj X (n + 1) | Dv ; μ] := condEntropy_nonneg _ _ _
  have hcap : H[σ ∘ traj X (n + 1) ; μ] ≤ H[X 0 ; μ] + n * H[X 1 | X 0 ; μ] := by
    rw [← entropy_traj μ hX hMarkov hStat n]
    exact entropy_comp_le μ (measurable_traj hX (n + 1)) σ
  have hEq : (fun ω => T (Dv ω) ((σ ∘ traj X (n + 1)) ω))
      = fun ω => T (Dv ω) (σ (traj X (n + 1) ω)) := rfl
  rw [hEq] at hmain
  linarith

/-! ### §11/11 with both capacities as rates

Print's sentence compares two *capacities*. §9/15 defines the channel's as a rate
in time, `ashbyCapacity`. Print never defines a regulator's capacity; the reading
taken here is the matching rate: over a run of `n + 1` regulatory acts, the
variety removed from the disturbance, `H[D] − H[E]`, per unit time. The regulator
watches the chain while it acts, one step per act, and a step takes `τ`.

The window bound carries the `H[X₀]` term of
`entropy_outcome_ge_sub_chainEntropy`, and that term is load-bearing: on a chain
that never moves the rate is zero, yet a regulator reading the initial state
cancels that much of a disturbance (`Examples.Control.frozen_bound_needs_initial`
shows the bound fails without it). That is why the comparison of rates below is
asymptotic. Over a window it is exact (`regulationRate_le_chainWindow`); in the
long run the initial state's share vanishes and the regulator's rate is held to
Ashby's capacity (`eventually_regulationRate_le_ashbyCapacity`). -/

/-- **The regulator's capacity as a rate**: the variety removed from a run of
`n + 1` disturbances, `H[D] − H[E]`, divided by the time the run takes, `n + 1`
steps of duration `τ`. -/
@[expose] public noncomputable def regulationRate {n : ℕ} (μ : Measure Ω)
    (Dv : Ω → (Fin (n + 1) → D)) (Ev : Ω → (Fin (n + 1) → E)) (τ : ℝ) : ℝ :=
  (H[Dv ; μ] - H[Ev ; μ]) / ((n + 1) * τ)

/--
**§11/11 over a window, with both capacities per unit time.** A regulator acts
`n + 1` times, the `i`-th outcome being `T (D i) (R i)` for a table `T` with no
element repeated in a column; its responses are any function of the first
`n + 1` states of a stationary Markov chain. Then the variety it removes per
unit time is at most the chain's trajectory entropy per unit time,
`(H[X₀] + n · H[X₁ | X₀]) / ((n + 1) τ)`.
-/
public theorem regulationRate_le_chainWindow [Fintype S] [Nonempty S]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {n : ℕ}
    {Dv : Ω → (Fin (n + 1) → D)} (hD : Measurable Dv) [FiniteRange Dv]
    {X : ℕ → Ω → S} (hX : ∀ n, Measurable (X n))
    (hMarkov : ∀ k, CondIndepFun (X (k + 1)) (traj X k) (X k) μ)
    (hStat : ∀ k, IdentDistrib (⟨X (k + 1), X k⟩ : Ω → S × S)
      (⟨X 1, X 0⟩ : Ω → S × S) μ μ)
    (σ : (Fin (n + 1) → S) → (Fin (n + 1) → R))
    (T : D → R → E) (hcol : ∀ r : R, Function.Injective fun d => T d r)
    {τ : ℝ} (hτ : 0 < τ) :
    regulationRate μ Dv (fun ω i => T (Dv ω i) (σ (traj X (n + 1) ω) i)) τ
      ≤ (H[X 0 ; μ] + n * H[X 1 | X 0 ; μ]) / ((n + 1) * τ) := by
  have hbound := entropy_outcome_ge_sub_chainEntropy μ hD hX hMarkov hStat n σ
    (measurable_of_countable σ) (fun (dv : Fin (n + 1) → D) (rv : Fin (n + 1) → R) i =>
      T (dv i) (rv i))
    (measurable_of_countable _)
    (fun rv dv dv' h => funext fun i => hcol (rv i) (congrFun h i))
  rw [regulationRate]
  have hpos : 0 < ((n : ℝ) + 1) * τ := by positivity
  exact div_le_div_of_nonneg_right (by linarith) hpos.le

/--
**§11/11 with Ashby's own capacity, as rates** (W. R. Ashby, *An Introduction to
Cybernetics*, §11/11: *"R's capacity as a regulator cannot exceed R's capacity as
a channel of communication"*, with the channel capacity of §9/15, *"Such a rate is
the most natural way of measuring the capacity of a channel"*).

For runs of `n + 1` acts with any disturbances `Dv n` and any response policies
`σ n` reading the chain, the regulator's rate is eventually within any `ε` of
`ashbyCapacity H[X₁ | X₀] τ`: its limit superior is at most the channel's
capacity. It is stated with `ε` rather than with `Filter.limsup`, whose value on
a sequence not bounded above is a junk value. `chainRate_eq_condEntropy`
identifies `H[X₁ | X₀]` with §9/12's printed rate.
-/
public theorem eventually_regulationRate_le_ashbyCapacity [Fintype S] [Nonempty S]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Dv : ∀ n : ℕ, Ω → (Fin (n + 1) → D)} (hD : ∀ n, Measurable (Dv n))
    (hfin : ∀ n, FiniteRange (Dv n))
    {X : ℕ → Ω → S} (hX : ∀ n, Measurable (X n))
    (hMarkov : ∀ k, CondIndepFun (X (k + 1)) (traj X k) (X k) μ)
    (hStat : ∀ k, IdentDistrib (⟨X (k + 1), X k⟩ : Ω → S × S)
      (⟨X 1, X 0⟩ : Ω → S × S) μ μ)
    (σ : ∀ n : ℕ, (Fin (n + 1) → S) → (Fin (n + 1) → R))
    (T : D → R → E) (hcol : ∀ r : R, Function.Injective fun d => T d r)
    {τ : ℝ} (hτ : 0 < τ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n in Filter.atTop,
      regulationRate μ (Dv n) (fun ω i => T (Dv n ω i) (σ n (traj X (n + 1) ω) i)) τ
        ≤ ashbyCapacity H[X 1 | X 0 ; μ] τ + ε := by
  set r := H[X 1 | X 0 ; μ]
  set h₀ := H[X 0 ; μ]
  obtain ⟨N, hN⟩ := exists_nat_gt ((h₀ - r) / (ε * τ))
  filter_upwards [Filter.eventually_ge_atTop N] with n hn
  have : FiniteRange (Dv n) := hfin n
  refine (regulationRate_le_chainWindow μ (hD n) hX hMarkov hStat (σ n) T hcol hτ).trans ?_
  have hpos : 0 < ((n : ℝ) + 1) * τ := by positivity
  have hετ : 0 < ε * τ := mul_pos hε hτ
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hslack : h₀ - r ≤ ε * (((n : ℝ) + 1) * τ) := by
    have := (div_lt_iff₀ hετ).mp hN
    nlinarith
  have hcancel : r / τ * (((n : ℝ) + 1) * τ) = r * ((n : ℝ) + 1) := by
    field_simp
  rw [ashbyCapacity, div_le_iff₀ hpos, add_mul, hcancel]
  linarith

end Regulation

end AISafetyAtlas.Control
