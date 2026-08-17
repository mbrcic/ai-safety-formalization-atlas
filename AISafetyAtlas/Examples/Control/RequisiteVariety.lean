module

public import AISafetyAtlas.Control.RequisiteVariety

/-!
# Requisite variety — worked consequences

Three checks on `AISafetyAtlas.Control.RequisiteVariety`.

1. **The bound is attained.** `ashbyTable` is a four-disturbance, two-response
   table satisfying Ashby's column condition, and `ashbyStrategy` is a strategy
   whose admitted outcomes number exactly `4 / 2 = 2`. So the law is sharp and
   `ashby_variety_ge` cannot be improved.
2. **It forbids something.** `no_constant_outcome` reads the same table through
   `two_le_card_admittedOutcomes`: no strategy on two responses holds the
   outcome fixed against four disturbances.
3. **The `k`-form is not vacuous either.** `card_le_of_two_per_column` shows the
   multiplicity form applies to a table that fails Ashby's 11/5 condition —
   entries repeat within a column — which is exactly the case 11/9 was added
   for.

None of these is new mathematics; they pin the general statements to concrete
readings.
-/

namespace AISafetyAtlas.Examples.Control

open AISafetyAtlas.Control
open AISafetyAtlas.InformationTheory

/-! ## A tight table

Four disturbances, two responses, outcomes in a four-element alphabet. The
response shifts the outcome by `0` or `1`, so each column is injective — Ashby's
"no element repeated in a column". -/

/-- Ashby's table, shrunk to `4 × 2`: response `r` shifts the outcome by `r`. -/
@[expose] public def ashbyTable : Fin 4 → Fin 2 → Fin 4 :=
  fun d r => d + (if r = 0 then 0 else 1)

/-- Each response separates the disturbances, so the column condition holds. -/
public theorem ashbyTable_column_injective (r : Fin 2) :
    Function.Injective fun d => ashbyTable d r := by
  intro a b h
  simpa [ashbyTable] using h

/-- A strategy that alternates, and so drives four disturbances onto two outcomes. -/
@[expose] public def ashbyStrategy : Fin 4 → Fin 2 := ![1, 0, 1, 0]

/--
**The law is sharp.** This strategy admits exactly two outcomes, meeting the
bound `|D| / |R| = 4 / 2` with equality. So `ashby_variety_ge` cannot be
strengthened.
-/
public theorem ashbyStrategy_card_eq_two :
    (admittedOutcomes ashbyTable ashbyStrategy Finset.univ).card = 2 := by
  decide

/--
**And it is genuinely a bound, not an equality in general.** The constant
strategy on the same table admits all four outcomes.
-/
public theorem constant_strategy_card_eq_four :
    (admittedOutcomes ashbyTable (fun _ => 0) Finset.univ).card = 4 := by
  decide

/--
**Perfect regulation is impossible here.** Two responses cannot hold the outcome
fixed against four disturbances, whatever the strategy — Ashby's 11/10 reading,
instantiated.
-/
public theorem no_constant_outcome (ρ : Fin 4 → Fin 2) :
    2 ≤ (admittedOutcomes ashbyTable ρ Finset.univ).card :=
  two_le_card_admittedOutcomes ashbyTable ρ ashbyTable_column_injective (by decide)

/-! ## The multiplicity form

Ashby added 11/9 for tables in which a column may repeat an entry. Then the
counting law still holds with the repetition count as a factor. -/

/-- A table that collapses pairs of disturbances: each column repeats every
entry twice, so Ashby's 11/5 condition fails and only 11/9 applies. -/
@[expose] public def coarseTable : Fin 4 → Fin 2 → Fin 2 :=
  fun d _ => if d = 0 ∨ d = 1 then 0 else 1

/--
**The `k = 2` instance.** Two disturbances share every outcome, so the bound
carries the factor `2` and reads `4 ≤ 2 * (1 * 2)` for the constant strategy.
The 11/5 form would give `4 ≤ 1 * 2`, which is false — the multiplicity is
doing real work.
-/
public theorem card_le_of_two_per_column :
    (Finset.univ : Finset (Fin 4)).card
      ≤ 2 * ((admittedOutcomes coarseTable (fun _ => 0) Finset.univ).card
          * (Finset.univ : Finset (Fin 2)).card) :=
  card_le_mul_card_admittedOutcomes_mul coarseTable (fun _ => 0) Finset.univ Finset.univ 2
    (fun _ _ => Finset.mem_univ _) (by decide)

/-! ## §11/11's exercises, at Ashby's own numbers

Ashby sets four exercises under the sentence *"R's capacity as a regulator cannot
exceed R's capacity as a channel of communication"*, and they are the only place
in chapter 11 where the law is applied to a rate. Two are done here, one on each
side of the bound.

**Read them as necessary conditions.** `entropy_le_channelCapacity_of_complete`
says complete regulation *requires* capacity at least the disturbance entropy;
it does not say capacity suffices. Ex. 1 asks whether the insect's optic nerve
is "sufficient to enable it to defend itself", and what can honestly be answered
is that the constraint is not binding — a channel this wide is not what stops it.
Ex. 3 asks the question in the direction the theorem does settle, and the answer
is a genuine impossibility.

The capacity here is the noiseless `log |O|`; see the module docstring of
`AISafetyAtlas.Control.RequisiteVariety` for why Shannon's Theorem 10, which
Ashby names in the same paragraph, is not what is formalized. -/

open MeasureTheory ProbabilityTheory

/-- **Ex. 1's optic nerve**: a hundred fibres, each carrying twenty bits in the
second. -/
public abbrev InsectNerve : Type := Fin 100 → Fin 20 → Bool

/-- **Ex. 1's dangers**: ten, each of which may independently be present in the
second. -/
public abbrev InsectDangers : Type := Fin 10 → Bool

/-- Two thousand bits a second, as Ashby's arithmetic gives. -/
public theorem card_insectNerve : Fintype.card InsectNerve = 2 ^ 2000 := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_bool, ← pow_mul]

/-- The nerve's capacity, built the way Ashby builds it: a hundred fibres times
what one fibre carries. This is `channelCapacity_fun`'s reason to exist. -/
public theorem channelCapacity_insectNerve :
    channelCapacity InsectNerve = 2000 * Real.log 2 := by
  rw [channelCapacity_fun (Fin 20 → Bool) 100]
  have hfibre : Fintype.card (Fin 20 → Bool) = 2 ^ 20 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  rw [hfibre, Nat.cast_pow, Real.log_pow]
  push_cast
  ring

/--
**Ex. 1, answered as the theorem allows.** The insect's optic nerve carries
`2000 log 2` a second; ten independent dangers carry at most `10 log 2`. So the
necessary condition of `entropy_le_channelCapacity_of_complete` is met with two
orders of magnitude to spare, whatever the dangers' distribution.

This is *not* an answer to "is this sufficient to enable it to defend itself".
The law bounds regulation from one side only; a channel wide enough is not a
regulator, and none is constructed here.
-/
public theorem insect_optic_nerve_not_binding {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Dv : Ω → InsectDangers) :
    H[Dv ; μ] ≤ channelCapacity InsectNerve := by
  have hlog2 : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hDcard : Fintype.card InsectDangers = 2 ^ 10 := by
    rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
  have hD : H[Dv ; μ] ≤ (10 : ℝ) * Real.log 2 := by
    have h := entropy_le_log_card Dv μ
    rw [hDcard] at h
    refine h.trans (le_of_eq ?_)
    rw [Nat.cast_pow, Real.log_pow]
    norm_num
  rw [channelCapacity_insectNerve]
  exact hD.trans (mul_le_mul_of_nonneg_right (by norm_num) hlog2)

/-- **Ex. 2's controls**, over five seconds: a telegraph that determines one of
nine speeds no oftener than once in that window, and a wheel that determines one
of fifty rudder-positions in each of the five seconds. -/
public abbrev ShipControls : Type := Fin 9 × (Fin 5 → Fin 50)

/-- The two controls run at different rates, so they are counted by adding their
capacities — which is what `channelCapacity_prod` is for, with
`channelCapacity_fun` giving the wheel's five uses. -/
public theorem channelCapacity_shipControls :
    channelCapacity ShipControls = Real.log 9 + 5 * Real.log 50 := by
  rw [channelCapacity_prod, channelCapacity, channelCapacity_fun]
  simp

/--
**Ex. 2, answered.** Ashby asks, given that this means of control is *"normally
sufficient for full regulation"*, for *"a normal upper limit for the disturbances
(gusts, traffic, shoals, etc.) that threaten the ship's safety"*.

Full regulation forces the disturbance entropy below the capacity, so the limit
is `log 9 + 5 log 50` per five seconds. This is the one exercise whose printed
question is exactly what the law answers — Ex. 1 asks for sufficiency, which the
law does not give, and Ex. 3 asks whether regulation is possible, which it does.
-/
public theorem ship_disturbance_upper_limit {Ω : Type*} [MeasurableSpace Ω]
    {D : Type*} [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D]
    {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Dv : Ω → D} (hD : Measurable Dv) [FiniteRange Dv]
    (obs : Ω → ShipControls) (hobs : Measurable obs)
    (σ : ShipControls → ShipControls) (hσ : Measurable σ)
    (T : D → ShipControls → E)
    (hT : Measurable fun p : D × ShipControls => T p.1 p.2)
    (hcol : ∀ r : ShipControls, Function.Injective fun d => T d r)
    (hfull : H[(fun ω => T (Dv ω) (σ (obs ω))) ; μ] = 0) :
    H[Dv ; μ] ≤ Real.log 9 + 5 * Real.log 50 := by
  have h := entropy_le_channelCapacity_of_complete μ hD obs hobs σ hσ T hT hcol hfull
  rwa [channelCapacity_shipControls] at h

/-- **Ex. 3's intelligence channel**: ten signallers, each sending sixty letters
a minute for eight hours — `28800` letters a day — in a two-bit code. -/
public abbrev GeneralIntelligence : Type := Fin 10 → Fin 28800 → Fin 2 → Bool

/-- **Ex. 3's opposing army**: ten divisions, each manoeuvring with a variety of
`10^6` bits in the day. -/
public abbrev OpposingArmy : Type := Fin 10 → Fin 1000000 → Bool

/-- `10 · 28800 · 2 = 576000` bits a day. -/
public theorem card_generalIntelligence :
    Fintype.card GeneralIntelligence = 2 ^ 576000 := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, Fintype.card_fin, Fintype.card_bool, ← pow_mul, ← pow_mul]

/-- `10 · 10^6 = 10^7` bits a day. -/
public theorem card_opposingArmy : Fintype.card OpposingArmy = 2 ^ 10000000 := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin,
    Fintype.card_bool, ← pow_mul]

/--
**Ex. 3, answered: the general cannot achieve complete regulation.** Ten
divisions at `10^6` bits a day put `10^7 log 2` of disturbance against an
intelligence channel carrying `576000 log 2`. By
`entropy_le_channelCapacity_of_complete`, complete regulation would force the
disturbance entropy below the capacity, and `10^7 > 576000`.

Unlike Ex. 1 this is the direction the law settles, so the conclusion is a real
impossibility rather than a constraint that fails to bind. The army is taken to
manoeuvre uniformly, which is the reading that makes its variety the `10^6` bits
Ashby quotes.

The general's *responses* are unconstrained — any type at all, of any size. It is
what reaches him, not what he can order, that defeats him. `battleTable_column_injective`
exhibits a table meeting the hypotheses, so this is not vacuous.
-/
public theorem general_intelligence_insufficient {Ω : Type*} [MeasurableSpace Ω]
    {R : Type*} [MeasurableSpace R] [MeasurableSingletonClass R] [Countable R]
    {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E] [Countable E]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Dv : Ω → OpposingArmy} (hD : Measurable Dv)
    (huniform : IsUniform (Set.univ : Set OpposingArmy) Dv μ)
    (obs : Ω → GeneralIntelligence) (hobs : Measurable obs)
    (σ : GeneralIntelligence → R) (hσ : Measurable σ)
    (T : OpposingArmy → R → E)
    (hT : Measurable fun p : OpposingArmy × R => T p.1 p.2)
    (hcol : ∀ r : R, Function.Injective fun d => T d r) :
    H[(fun ω => T (Dv ω) (σ (obs ω))) ; μ] ≠ 0 := by
  intro hconst
  have hle := entropy_le_channelCapacity_of_complete μ hD obs hobs σ hσ T hT hcol hconst
  rw [channelCapacity_eq_of_card_eq_two_pow card_generalIntelligence,
    IsUniform.entropy_eq' Set.finite_univ huniform hD, Set.ncard_univ,
    Nat.card_eq_fintype_card, card_opposingArmy, Nat.cast_pow, Real.log_pow] at hle
  -- `hle : (10^7) * log 2 ≤ 576000 * log 2`, and `log 2 > 0`
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- no `2 ^ n` survives `Real.log_pow`, so normalizing the casts is safe here
  push_cast at hle
  nlinarith [hle, hlog2]

/-- A table that records both what the army did and what the general ordered.
Its columns separate the disturbances, which is
`general_intelligence_insufficient`'s only hypothesis on the world. -/
@[expose] public def battleTable {R : Type*} : OpposingArmy → R → OpposingArmy × R :=
  fun d r => (d, r)

/--
**The impossibility is not vacuous.** `battleTable` meets the column condition
for any response alphabet at all.

An earlier witness used `R = Unit` and a table that ignored the response
entirely, which could not support the reading that it is what reaches the general
rather than what he can order that defeats him: with one available order there is
nothing to order. Here the outcome records the order, so the response is live and
the impossibility still holds.
-/
public theorem battleTable_column_injective {R : Type*} (r : R) :
    Function.Injective fun d : OpposingArmy => battleTable d r :=
  fun _ _ h => congrArg Prod.fst h

end AISafetyAtlas.Examples.Control
