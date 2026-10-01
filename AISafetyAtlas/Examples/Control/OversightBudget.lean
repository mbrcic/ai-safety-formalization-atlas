module

public import AISafetyAtlas.Control.OversightBudget
public import AISafetyAtlas.Control.ChannelRate
public import AISafetyAtlas.Control.RequisiteVariety

/-!
# Two oversight regimes, with the numbers written out

`AISafetyAtlas.Control.OversightBudget` carried two theorems that nothing in
`Examples/` applied, and the module said so: inhabiting their hypotheses needs a
probability space with `IsPlant` and `OpenLoopBound` discharged, and *"every
cheap model of those makes every entropy zero. A witness where the bound reads
`0 ≤ 0 + 0` would satisfy the checker and establish nothing."*

That is the standard these witnesses are built to. Every quantity in every
statement below is a **positive** number, and where a bound is slack the slack is
named and explained rather than passed over.

* `blindRegime` has a hazard carrying `log 4`, a monitoring channel that is a
  genuine coin rather than a constant, and a plant that keeps one bit. The
  channel is independent of the hazard, so the budget's second term vanishes —
  and `blindRegime_entropyReduction_eq` shows the regime still reduces
  uncertainty by `log 2`, **exactly** the blind term. The bound is attained.
  Monitoring bought nothing; the regime achieved something anyway, which is the
  distinction the theorem exists to draw.
* `oneReading` and `twoReadings` differ in **volume and in nothing else**: the
  second records the same bit twice. `duplication_mutualInfo_eq` proves their
  channels carry the same `log 2` about the hazard — positive, so the theorem is
  not applied at a dead channel — and `twoReadings_budget_eq_oneReading`
  inherits the identical bound. Here the bound is **not** attained, and
  `oneReading_entropyReduction_eq` says by how much: the reduction is `log 2`
  against a bound of `log 2 + log 2`, because `keepFirst` discards the reading
  and never spends the channel's half.
* `frozenChain` is a Markov chain with rate zero and a non-zero initial state.
  `frozen_outcome_bound` attains Ashby's budget at `log 2 ≤ log 2`, and
  `frozen_bound_needs_initial` proves the inequality **false** when `H[X₀]` is
  dropped — so the initial term is load-bearing as a theorem and not as a
  remark.

The blind regime sits on its own space. A blind channel and an informative one
cannot be the same channel, and folding them together would have meant a
constant reading somewhere.
-/

namespace AISafetyAtlas.Examples.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.Control AISafetyAtlas.Control.OversightBudget
open AISafetyAtlas.InformationTheory

/-! ## A channel that is a coin, and independent of the hazard -/

/-- A two-bit hazard together with one bit the overseer reads. -/
public abbrev BlindΩ : Type := (Fin 2 × Fin 2) × Fin 2

/-- A fair coin. -/
@[expose] public noncomputable def bit : Measure (Fin 2) :=
  uniformOn (Set.univ : Set (Fin 2))

public instance : IsProbabilityMeasure bit := by
  unfold bit; infer_instance

/-- A fair coin carries `log 2`. -/
public theorem entropy_bit : H[(id : Fin 2 → Fin 2) ; bit] = Real.log 2 := by
  rw [bit, IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
  norm_num [Set.ncard_univ, Nat.card_eq_fintype_card]

/-- The hazard is two independent fair coins and the reading is a third: a
product measure, so every independence used below is structural rather than
computed. -/
@[expose] public noncomputable def blindLaw : Measure BlindΩ := (bit.prod bit).prod bit

public instance : IsProbabilityMeasure blindLaw := by
  unfold blindLaw; infer_instance

/-- The regime: a two-bit hazard, a one-bit reading, and an outcome that is the
hazard's first bit. -/
@[expose] public def blindRegime : Oversight BlindΩ (Fin 2 × Fin 2) (Fin 2) (Fin 2) where
  hazard := Prod.fst
  reading := Prod.snd
  outcome := fun ω => (ω.1).1

/-- The plant that keeps the hazard's first bit, whatever the overseer does.
Parametric in the control type, because the two regimes below read different
things and the plant ignores both. -/
@[expose] public def keepFirst (K : Type*) : (Fin 2 × Fin 2) → K → Unit → Fin 2 :=
  fun s _ _ => s.1

public theorem isPlant_keepFirst :
    IsPlant (keepFirst (Fin 2)) blindRegime.hazard blindRegime.reading (fun _ => ())
      blindRegime.outcome :=
  fun _ => rfl

/--
**The open-loop bound holds at `log 2`, and no control action moves it.**

`keepFirst` discards one bit of a two-bit hazard, so on every conditional
ensemble the entropy drops by at most `log 2`. The argument is subadditivity,
and the control action never appears in it — which is what makes this an
*open-loop* bound rather than a claim about the regime.
-/
public theorem openLoopBound_keepFirst {Ω : Type*} [MeasurableSpace Ω] (K : Type*)
    (μ : Measure Ω) {X : Ω → Fin 2 × Fin 2} (hX : Measurable X) :
    OpenLoopBound μ (keepFirst K) X (fun _ => ()) (Real.log 2) := by
  intro s _ _ k
  have hfst : Measurable fun ω => (X ω).1 := measurable_fst.comp hX
  have hsnd : Measurable fun ω => (X ω).2 := measurable_snd.comp hX
  have hpair : H[X ; μ[|s]] ≤ H[fun ω => (X ω).1 ; μ[|s]] + H[fun ω => (X ω).2 ; μ[|s]] := by
    have h := entropy_pair_le_add hfst hsnd (μ[|s])
    have hid : (⟨fun ω => (X ω).1, fun ω => (X ω).2⟩ : Ω → Fin 2 × Fin 2) = X := rfl
    rwa [hid] at h
  have hbit : H[fun ω => (X ω).2 ; μ[|s]] ≤ Real.log 2 := by
    have := entropy_le_log_card (fun ω => (X ω).2) (μ[|s])
    simpa using this
  have hgoal : H[fun ω => keepFirst K (X ω) k (() : Unit) ; μ[|s]]
      = H[fun ω => (X ω).1 ; μ[|s]] := rfl
  rw [hgoal]
  linarith

/-- The channel is a coin independent of the hazard, so it carries nothing about
it. Structural, not arithmetic: the law is a product. -/
public theorem blind_mutualInfo_eq_zero :
    I[blindRegime.hazard : blindRegime.reading ; blindLaw] = 0 := by
  have hX : Measurable blindRegime.hazard := measurable_fst
  have hY : Measurable blindRegime.reading := measurable_snd
  rw [mutualInfo_eq_zero hX hY]
  exact ProbabilityTheory.indepFun_fst_snd

/--
**`blind_channel_buys_nothing` at a regime where nothing is zero.**

The hazard carries `log 4`, the reading is a fair coin, the plant keeps one bit,
and the bound is `log 2`.
-/
public theorem blindRegime_buys_nothing :
    entropyReduction blindLaw blindRegime.hazard blindRegime.outcome ≤ Real.log 2 :=
  blind_channel_buys_nothing blindRegime measurable_fst measurable_snd
    (measurable_fst.comp measurable_fst) isPlant_keepFirst
    (openLoopBound_keepFirst (Fin 2) blindLaw measurable_fst) blind_mutualInfo_eq_zero


/-- A first coordinate of a product law is distributed as its own factor. -/
public theorem entropy_fst_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass A] (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure ν] :
    H[(Prod.fst : A × B → A) ; μ.prod ν] = H[(id : A → A) ; μ] := by
  rw [entropy_def, entropy_def, Measure.map_fst_prod, Measure.map_id]
  simp

/-- And a second coordinate as its own factor. -/
public theorem entropy_snd_prod {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSingletonClass B] (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ]
    [SFinite ν] :
    H[(Prod.snd : A × B → B) ; μ.prod ν] = H[(id : B → B) ; ν] := by
  rw [entropy_def, entropy_def, Measure.map_snd_prod, Measure.map_id]
  simp

/-- **Two independent fair coins are a uniform pair.** Proved once so that both
entropy computations below can read the hazard either way. -/
public theorem prod_bit_eq_uniform :
    bit.prod bit = uniformOn (Set.univ : Set (Fin 2 × Fin 2)) := by
  refine Measure.ext_of_singleton fun p => ?_
  obtain ⟨a, b⟩ := p
  rw [← Set.singleton_prod_singleton, Measure.prod_prod]
  simp [bit, uniformOn, cond_apply]
  rw [← ENNReal.mul_inv (by norm_num) (by norm_num)]
  norm_num

/-- The hazard carries `log 4`: two independent fair coins. Stated so the witness
cannot be read as a regime where every entropy is zero. -/
public theorem blind_hazard_entropy :
    H[blindRegime.hazard ; blindLaw] = Real.log 4 := by
  have hpair : H[(id : Fin 2 × Fin 2 → Fin 2 × Fin 2) ; bit.prod bit] = Real.log 4 := by
    rw [prod_bit_eq_uniform,
      IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
    norm_num [Set.ncard_univ, Nat.card_eq_fintype_card]
  rw [show blindRegime.hazard = (Prod.fst : BlindΩ → Fin 2 × Fin 2) from rfl, blindLaw,
    entropy_fst_prod, hpair]

/-- The outcome carries `log 2`: the plant kept one of the two coins. -/
public theorem blind_outcome_entropy :
    H[blindRegime.outcome ; blindLaw] = Real.log 2 := by
  have h : H[(Prod.fst : Fin 2 × Fin 2 → Fin 2) ; bit.prod bit] = Real.log 2 := by
    rw [entropy_fst_prod, entropy_bit]
  rw [show blindRegime.outcome
      = (Prod.fst : Fin 2 × Fin 2 → Fin 2) ∘ (Prod.fst : BlindΩ → Fin 2 × Fin 2) from rfl,
    entropy_def, ← Measure.map_map measurable_fst measurable_fst, blindLaw,
    Measure.map_fst_prod]
  simpa [entropy_def] using h

/-- **The bound is attained.** The regime reduces uncertainty by exactly the
blind term, with an independent channel: monitoring bought nothing and the
regime achieved something anyway. -/
public theorem blindRegime_entropyReduction_eq :
    entropyReduction blindLaw blindRegime.hazard blindRegime.outcome = Real.log 2 := by
  rw [entropyReduction, blind_hazard_entropy, blind_outcome_entropy,
    show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
  ring


/-! ## Two regimes that differ in volume and in nothing else -/

/-- The hazard is the whole space here: two fair coins, and the overseer reads
the first of them. -/
public abbrev VolumeΩ : Type := Fin 2 × Fin 2

/-- The same law as above, read as a hazard with no separate channel variable. -/
@[expose] public noncomputable def volumeLaw : Measure VolumeΩ := bit.prod bit

public instance : IsProbabilityMeasure volumeLaw := by
  unfold volumeLaw; infer_instance

/-- **`I[X : f(X)] = H[f(X)]`.** A channel that is a function of the hazard
carries exactly its own entropy about it, which is why the two regimes below can
be compared without computing either mutual information from the definition. -/
public theorem mutualInfo_comp_self {Ω : Type*} [MeasurableSpace Ω]
    {S U : Type*} [MeasurableSpace S] [MeasurableSingletonClass S] [Countable S]
    [MeasurableSpace U] [MeasurableSingletonClass U] [Countable U]
    {X : Ω → S} (hX : Measurable X) (f : S → U) (μ : Measure Ω) :
    I[X : f ∘ X ; μ] = H[f ∘ X ; μ] := by
  rw [mutualInfo_def, entropy_prod_comp hX μ f]
  ring

/-- One reading: the first coin, and an unused slot. -/
@[expose] public def oneReading : VolumeΩ → Fin 2 × Fin 2 := fun ω => (ω.1, 0)

/-- Twice the volume, and not one bit more information: the same coin recorded
in both slots. -/
@[expose] public def twoReadings : VolumeΩ → Fin 2 × Fin 2 := fun ω => (ω.1, ω.1)

/-- The regime that records the first coin once. -/
@[expose] public def oneReadingRegime : Oversight VolumeΩ (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Fin 2) where
  hazard := id
  reading := oneReading
  outcome := Prod.fst

/-- The regime that records it twice. Same hazard, same outcome, double the
readings. -/
@[expose] public def twoReadingsRegime : Oversight VolumeΩ (Fin 2 × Fin 2) (Fin 2 × Fin 2) (Fin 2) where
  hazard := id
  reading := twoReadings
  outcome := Prod.fst

public theorem isPlant_oneReading :
    IsPlant (keepFirst (Fin 2 × Fin 2)) oneReadingRegime.hazard oneReadingRegime.reading
      (fun _ => ()) oneReadingRegime.outcome :=
  fun _ => rfl

/-- Each channel carries `log 2` about the hazard: the first coin, once or
twice, is the first coin. -/
public theorem oneReading_mutualInfo :
    I[oneReadingRegime.hazard : oneReadingRegime.reading ; volumeLaw] = Real.log 2 := by
  have h := mutualInfo_comp_self (X := (id : VolumeΩ → VolumeΩ)) measurable_id
    (fun p : Fin 2 × Fin 2 => (p.1, (0 : Fin 2))) volumeLaw
  rw [show oneReadingRegime.reading
      = (fun p : Fin 2 × Fin 2 => (p.1, (0 : Fin 2))) ∘ (id : VolumeΩ → VolumeΩ) from rfl,
    show oneReadingRegime.hazard = (id : VolumeΩ → VolumeΩ) from rfl, h,
    show ((fun p : Fin 2 × Fin 2 => (p.1, (0 : Fin 2))) ∘ (id : VolumeΩ → VolumeΩ))
      = (fun b : Fin 2 => (b, (0 : Fin 2))) ∘ (Prod.fst : VolumeΩ → Fin 2) from rfl,
    entropy_comp_of_injective volumeLaw measurable_fst _
      (fun _ _ hab => (Prod.ext_iff.1 hab).1),
    volumeLaw, entropy_fst_prod, entropy_bit]

public theorem twoReadings_mutualInfo :
    I[twoReadingsRegime.hazard : twoReadingsRegime.reading ; volumeLaw] = Real.log 2 := by
  have h := mutualInfo_comp_self (X := (id : VolumeΩ → VolumeΩ)) measurable_id
    (fun p : Fin 2 × Fin 2 => (p.1, p.1)) volumeLaw
  rw [show twoReadingsRegime.reading
      = (fun p : Fin 2 × Fin 2 => (p.1, p.1)) ∘ (id : VolumeΩ → VolumeΩ) from rfl,
    show twoReadingsRegime.hazard = (id : VolumeΩ → VolumeΩ) from rfl, h,
    show ((fun p : Fin 2 × Fin 2 => (p.1, p.1)) ∘ (id : VolumeΩ → VolumeΩ))
      = (fun b : Fin 2 => (b, b)) ∘ (Prod.fst : VolumeΩ → Fin 2) from rfl,
    entropy_comp_of_injective volumeLaw measurable_fst _
      (fun _ _ hab => (Prod.ext_iff.1 hab).1),
    volumeLaw, entropy_fst_prod, entropy_bit]

/-- **The two channels carry the same information**, and the mutual information
is `log 2` rather than zero, so the theorem below is not applied at a dead
channel. -/
public theorem duplication_mutualInfo_eq :
    I[twoReadingsRegime.hazard : twoReadingsRegime.reading ; volumeLaw]
      = I[oneReadingRegime.hazard : oneReadingRegime.reading ; volumeLaw] := by
  rw [twoReadings_mutualInfo, oneReading_mutualInfo]

/-- **The regime reduces uncertainty by `log 2`**, against a bound of
`log 2 + log 2`. The slack is not an accident and is worth naming: `keepFirst`
throws the reading away, so the channel's `log 2` is budget the plant never
spends. This is the module's own caveat at a witness — the bound is an upper
bound on what oversight can achieve and never a guarantee that it is achieved. -/
public theorem oneReading_entropyReduction_eq :
    entropyReduction volumeLaw oneReadingRegime.hazard oneReadingRegime.outcome
      = Real.log 2 := by
  have hh : H[oneReadingRegime.hazard ; volumeLaw] = Real.log 4 := by
    rw [show oneReadingRegime.hazard = (id : VolumeΩ → VolumeΩ) from rfl, volumeLaw,
      prod_bit_eq_uniform,
      IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
    norm_num [Set.ncard_univ, Nat.card_eq_fintype_card]
  have ho : H[oneReadingRegime.outcome ; volumeLaw] = Real.log 2 := by
    rw [show oneReadingRegime.outcome = (Prod.fst : VolumeΩ → Fin 2) from rfl, volumeLaw,
      entropy_fst_prod, entropy_bit]
  rw [entropyReduction, hh, ho, show (4 : ℝ) = 2 * 2 by norm_num,
    Real.log_mul (by norm_num) (by norm_num)]
  ring

/--
**`budget_is_the_channel_not_the_volume` at a live channel.**

The regime that records one reading inherits the bound written in terms of the
regime that records two, because the two channels carry the same `log 2` about
the hazard. Doubling the volume moved nothing.
-/
public theorem twoReadings_budget_eq_oneReading :
    entropyReduction volumeLaw oneReadingRegime.hazard oneReadingRegime.outcome
      ≤ Real.log 2 + I[twoReadingsRegime.hazard : twoReadingsRegime.reading ; volumeLaw] :=
  budget_is_the_channel_not_the_volume oneReadingRegime twoReadingsRegime
    measurable_id (by fun_prop) measurable_fst isPlant_oneReading
    (openLoopBound_keepFirst (Fin 2 × Fin 2) volumeLaw measurable_id)
    duplication_mutualInfo_eq



/-! ## A chain that never moves, against Ashby's own budget

`AISafetyAtlas.Control.entropy_outcome_ge_sub_chainEntropy` bounds the entropy
surviving in a regulated outcome by the disturbance's entropy less the
**trajectory** entropy `H[X₀] + n · rate` of what the regulator watched. Its
docstring says the initial term is load-bearing — Ashby's *"proportional to its
length"* would suggest `n · rate` alone, and that is not an upper bound.

The frozen chain is the witness for exactly that sentence, and it is built to
discriminate rather than merely to inhabit. `frozenChain` never moves, so its
rate is zero and the whole budget is `H[X₀] = log 2`, against a disturbance
carrying `log 4`. The regulator's one bit is spent cancelling one bit of the
disturbance, so the outcome carries `log 2` and `frozen_outcome_bound` reads
`log 2 ≤ log 2` — **attained**. Then `frozen_bound_needs_initial` proves that
the same inequality with `H[X₀]` dropped is **false** here, which is the whole
of Ashby's caveat as a theorem rather than as a remark.
-/

/-- The chain that never moves: every state is the first coin. -/
@[expose] public def frozenChain : ℕ → VolumeΩ → Fin 2 := fun _ ω => ω.1

/-- The disturbance the regulator is up against: both coins, `log 4` of them. -/
@[expose] public def frozenDisturbance : VolumeΩ → Fin 2 × Fin 2 := id

/-- The regulator's response: whatever it saw first, which on a frozen chain is
all it will ever see. -/
@[expose] public def frozenPolicy {n : ℕ} : (Fin (n + 1) → Fin 2) → Fin 2 := fun v => v 0

/-- The outcome map: the response is added to the disturbance's first coin and
the second coin passes through untouched. Injective in the disturbance at every
response — the regulator can offset the disturbance, never erase it, which is
the hypothesis Ashby's bound needs. -/
@[expose] public def frozenOutcome : (Fin 2 × Fin 2) → Fin 2 → (Fin 2 × Fin 2) :=
  fun d r => (d.1 + r, d.2)

/-- Conditioned on its own value, a variable is a.e. constant. -/
public theorem ae_eq_const_cond {Ω A : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A] {Y : Ω → A} (hY : Measurable Y) (μ : Measure Ω) (z : A) :
    Y =ᵐ[μ[|Y ← z]] fun _ => z := by
  have hmem : {ω | Y ω = z} ∈ ae (μ[|Y ← z]) := by
    rw [mem_ae_iff, ← cond_inter_self]
    · have hempty : (Y ⁻¹' {z}) ∩ {ω | Y ω = z}ᶜ = ∅ := by ext _; simp
      simp [hempty]
    · exact hY (MeasurableSet.singleton z)
  exact Filter.eventuallyEq_of_mem hmem fun _ h => h

/-- **A variable is conditionally independent of anything given itself.** The
frozen chain's Markov property, and nothing more than that: once the state is
known, the next state is known too, so it carries no further dependence. -/
public theorem condIndepFun_self {Ω A B : Type*} [MeasurableSpace Ω] [MeasurableSpace A]
    [MeasurableSingletonClass A] [MeasurableSpace B] {Y : Ω → A} (hY : Measurable Y)
    (g : Ω → B) (μ : Measure Ω) [IsProbabilityMeasure μ] :
    CondIndepFun Y g Y μ := by
  rw [condIndepFun_iff]
  filter_upwards with z
  exact (ProbabilityTheory.indepFun_const_left z g).congr
    (ae_eq_const_cond hY μ z).symm (Filter.EventuallyEq.refl _ _)

public theorem frozen_markov (k : ℕ) :
    CondIndepFun (frozenChain (k + 1)) (traj frozenChain k) (frozenChain k) volumeLaw :=
  condIndepFun_self measurable_fst _ volumeLaw

public theorem frozen_stationary (k : ℕ) :
    IdentDistrib (⟨frozenChain (k + 1), frozenChain k⟩ : VolumeΩ → Fin 2 × Fin 2)
      (⟨frozenChain 1, frozenChain 0⟩ : VolumeΩ → Fin 2 × Fin 2) volumeLaw volumeLaw :=
  IdentDistrib.refl (measurable_fst.prodMk measurable_fst).aemeasurable

/-- **The rate is zero**: a chain that never moves says nothing new per step. -/
public theorem frozen_rate_eq_zero :
    H[frozenChain 1 | frozenChain 0 ; volumeLaw] = 0 := by
  have : FiniteRange (Prod.fst : VolumeΩ → Fin 2) := ⟨Set.toFinite _⟩
  show H[(Prod.fst : VolumeΩ → Fin 2) | (Prod.fst : VolumeΩ → Fin 2) ; volumeLaw] = 0
  have h : H[(Prod.fst : VolumeΩ → Fin 2) | (id : Fin 2 → Fin 2) ∘ (Prod.fst : VolumeΩ → Fin 2) ;
        volumeLaw]
      = H[(Prod.fst : VolumeΩ → Fin 2) ; volumeLaw]
        - H[(id : Fin 2 → Fin 2) ∘ (Prod.fst : VolumeΩ → Fin 2) ; volumeLaw] :=
    condEntropy_comp_self (X := (Prod.fst : VolumeΩ → Fin 2)) (μ := volumeLaw)
      measurable_fst (f := (id : Fin 2 → Fin 2)) measurable_id
  simpa using h

/-- **The initial state is not free**, and on a frozen chain it is the whole
budget: `log 2`, against a disturbance carrying `log 4`. -/
public theorem frozen_initial_entropy :
    H[frozenChain 0 ; volumeLaw] = Real.log 2 := by
  rw [show (frozenChain 0 : VolumeΩ → Fin 2) = (Prod.fst : VolumeΩ → Fin 2) from rfl,
    volumeLaw, entropy_fst_prod, entropy_bit]

public theorem frozen_disturbance_entropy :
    H[frozenDisturbance ; volumeLaw] = Real.log 4 := by
  rw [show (frozenDisturbance : VolumeΩ → Fin 2 × Fin 2)
      = (id : VolumeΩ → VolumeΩ) from rfl, volumeLaw, prod_bit_eq_uniform,
    IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
  norm_num [Set.ncard_univ, Nat.card_eq_fintype_card]

/-- The regulated outcome, written out: the response cancels the first coin and
the second passes through. -/
public theorem frozen_outcome_eq (n : ℕ) :
    (fun ω => frozenOutcome (frozenDisturbance ω)
        (frozenPolicy (traj frozenChain (n + 1) ω)))
      = (fun b : Fin 2 => ((0 : Fin 2), b)) ∘ (Prod.snd : VolumeΩ → Fin 2) := by
  funext ω
  have hb : ω.1 + ω.1 = (0 : Fin 2) := by revert ω; decide +kernel
  simp [frozenOutcome, frozenDisturbance, frozenPolicy, frozenChain, traj, hb]

/-- **What the regulator managed**: `log 2` survives, the second coin it never
touched. -/
public theorem frozen_outcome_entropy (n : ℕ) :
    H[(fun ω => frozenOutcome (frozenDisturbance ω)
        (frozenPolicy (traj frozenChain (n + 1) ω))) ; volumeLaw] = Real.log 2 := by
  rw [frozen_outcome_eq n,
    entropy_comp_of_injective volumeLaw measurable_snd _
      (fun _ _ hab => (Prod.ext_iff.1 hab).2),
    volumeLaw, entropy_snd_prod, entropy_bit]

/--
**`entropy_outcome_ge_sub_chainEntropy` at Ashby's own point, with the bound
attained.**

`log 4 - (log 2 + n · 0) ≤ log 2`, an equality. Nothing here is slack and
nothing is zero but the rate, which is zero because the chain is frozen.
-/
public theorem frozen_outcome_bound (n : ℕ) :
    H[frozenDisturbance ; volumeLaw]
        - (H[frozenChain 0 ; volumeLaw] + n * H[frozenChain 1 | frozenChain 0 ; volumeLaw])
      ≤ H[(fun ω => frozenOutcome (frozenDisturbance ω)
            (frozenPolicy (traj frozenChain (n + 1) ω))) ; volumeLaw] :=
  entropy_outcome_ge_sub_chainEntropy volumeLaw measurable_id (fun _ => measurable_fst)
    frozen_markov frozen_stationary n frozenPolicy (by fun_prop) frozenOutcome (by fun_prop)
    (by decide +kernel)

/--
**The initial term is load-bearing, and here is the counterexample to dropping
it.**

Ashby's *"proportional to its length"* reads the budget as `n · rate`. At this
chain the rate is zero, so that reading would allow the regulator the whole
disturbance; `log 4 ≤ log 2` is false, and this is that statement. The theorem
above is therefore not true by slack — remove `H[X₀]` and it fails.
-/
public theorem frozen_bound_needs_initial (n : ℕ) :
    ¬ (H[frozenDisturbance ; volumeLaw]
          - n * H[frozenChain 1 | frozenChain 0 ; volumeLaw]
        ≤ H[(fun ω => frozenOutcome (frozenDisturbance ω)
              (frozenPolicy (traj frozenChain (n + 1) ω))) ; volumeLaw]) := by
  rw [frozen_disturbance_entropy, frozen_rate_eq_zero, frozen_outcome_entropy n]
  have h : Real.log 2 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
  simp only [mul_zero, sub_zero]
  linarith


/-! ## Ashby's regulator with imperfect information, on the same coins

`AISafetyAtlas.Control.entropy_ge_of_sensor` is §11/11 read through a sensor: a
regulator that sees `obs ∘ D` rather than `D` cannot push the outcome's entropy
below `H[D] - H[obs ∘ D]`. The frozen chain above already carries everything it
asks for, so this costs a sensor and nothing else — and the sensor is the honest
one for that chain, since a regulator watching a chain that never moves sees
only the coin the chain froze on.
-/

/-- The sensor: the regulator sees the first coin and not the second. -/
@[expose] public def frozenSensor : (Fin 2 × Fin 2) → Fin 2 := Prod.fst

/-- What the regulator sees is worth `log 2` of the disturbance's `log 4`. -/
public theorem frozenSensor_entropy :
    H[frozenSensor ∘ frozenDisturbance ; volumeLaw] = Real.log 2 := by
  rw [show (frozenSensor ∘ frozenDisturbance) = (Prod.fst : VolumeΩ → Fin 2) from rfl,
    volumeLaw, entropy_fst_prod, entropy_bit]

/--
**Ashby's law with an imperfect sensor, attained.** `log 4 - log 2 ≤ log 2`: half
the disturbance is invisible to the regulator, and exactly that half survives in
the outcome. Nothing is slack and nothing is zero.

The outcome is the one `frozen_outcome_eq` already computes, because the
regulator's response through this sensor *is* the frozen chain's response —
which is the point of running both statements on one model rather than two.
-/
public theorem frozen_sensor_bound :
    H[frozenDisturbance ; volumeLaw] - H[frozenSensor ∘ frozenDisturbance ; volumeLaw]
      ≤ H[(fun ω => frozenOutcome (frozenDisturbance ω)
            (id (frozenSensor (frozenDisturbance ω)))) ; volumeLaw] :=
  entropy_ge_of_sensor volumeLaw measurable_id frozenSensor (by fun_prop) id measurable_id
    frozenOutcome (by fun_prop) (by decide +kernel)


end AISafetyAtlas.Examples.Control
