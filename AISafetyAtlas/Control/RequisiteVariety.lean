module

public import PFR.ForMathlib.Entropy.Basic
public import AISafetyAtlas.Control.VarietyCounting
public import AISafetyAtlas.InformationTheory.ChannelCapacity
public import AISafetyAtlas.InformationTheory.Determinism

/-!
# Ashby's Law of Requisite Variety

W. Ross Ashby, *An Introduction to Cybernetics* (Chapman & Hall, 1961),
chapter 11 — the source cited by `BY-004`. Ashby's slogan is *only variety can
destroy variety*: a regulator cannot hold the outcome steadier than its own
repertoire allows.

The chapter gives the law three times, and all three are formalized. **Two files
carry them**, because the two halves rest on different foundations and only one
of them needs PFR:

| section | printed statement | here |
|---|---|---|
| 11/5 | `r` rows, `c` columns, no repeat in a column ⟹ outcome variety `≥ r/c` | `ashby_variety_ge`, in `AISafetyAtlas.Control.VarietyCounting` |
| 11/7 | logarithmically, `V_O ≥ V_D − V_R` | the same statement, same file; `Real.log` is monotone |
| 11/8 | in entropies, `H(E) ≥ H(D) + H_D(R) − H(R)` | `entropy_ge_of_condEntropy_ge`, **this file** |
| 11/9 | `k` repeats per column, and the entropy slack `K` | the same theorems; `k` and `K` are parameters throughout |

The split is a compile-graph one and nothing is renamed: both files are
`namespace AISafetyAtlas.Control`, and importing `AISafetyAtlas.Control` or this
module gets both halves. It exists because `Oversight.VarietyBound` needs one
counting lemma, and the counting half needs no measure theory to state or prove;
`VarietyCounting`'s header sets out the division.

## What exceeds the source

Stated for the law as a whole, so some bullets name counting declarations that
live in `VarietyCounting`. They are in this namespace and this module imports
them, so the names resolve here.

* **`k` is not a second theorem.** Ashby proves 11/5 for tables with no repeated
  entry in a column and then repeats the argument in 11/9 for `k` repeats. Here
  `k` is a parameter of one statement, and 11/5 is `k = 1`
  (`card_le_mul_card_admittedOutcomes`). The entropy slack `K` of 11/9 is handled the
  same way.
* **The column condition is only needed where the regulator actually goes** — in
  the multiplied counting form. Ashby requires *no* column to repeat an entry;
  `card_le_mul_card_admittedOutcomes` needs only `Set.InjOn` on the fibre
  `{d | ρ d = r}`, since entries a strategy never selects are unconstrained.
  The statements derived from it — `ashby_variety_ge` and everything downstream —
  still take the full column condition, because they quantify over strategies and
  so cannot name the fibre in advance.
* **No finiteness on the disturbances or outcomes beyond what is counted.** The
  counting statements take a `Finset` of disturbances and an arbitrary type of
  outcomes; the entropy statements take any measurable space with a probability
  measure, in place of Ashby's finite table.
* **§11/11's channel, with a noiseless ceiling.** *"The law of Requisite Variety
  says that R's capacity as a regulator cannot exceed R's capacity as a channel
  of communication"*, and the exercises printed under it use noiseless signal
  counts per unit time. `channelCapacity O = log |O|` and the two rate lemmas
  reproduce that arithmetic.

  They do **not** reproduce Ashby's general definition, and are not meant to.
  §9/15 first computes the probability-weighted entropy of a three-state Markov
  chain as `0.842` bits per step, converts it to `2.53` bits per minute, and calls
  *such a rate* the natural measure of channel capacity; `log |O|` would instead
  give `log 3` per step. That general definition is
  `AISafetyAtlas.Control.chainRate`, with §9/15's own conversion in
  `ashbyCapacity` and §11/11's bound against it in
  `entropy_outcome_ge_sub_chainEntropy`.
  `entropy_outcome_ge_sub_channelCapacity` remains the sharp form for the
  noiseless exercises, which is what it was built for.
* **The table hypothesis is discharged, not assumed.** Ashby's 11/8 *assumes*
  `H_R(E) ≥ H_R(D)`. For a table with injective columns it is a theorem, and in
  fact an equality (`condEntropy_outcome_eq`), which is what ties the
  combinatorial and entropy halves into one development rather than two.

## A repair to the printed derivation

Ashby's 11/8 derivation is correct line by line but its last line is misprinted:
the text concludes

> `H(E) > H(D) + H_D(E) – H(R)`

where the preceding steps give `H_D(R)`, not `H_D(E)`. The sentence after it
("H(E)'s minimum is H(D) – H(R)" when `H_D(R) = 0`) confirms that `H_D(R)` is
meant. The corrected inequality is what is proved here. See
`docs/provenance/ashby-requisite-variety.md`.

## Provenance of the entropy layer

`H[· ; ·]`, `H[· | · ; ·]` and the chain rules are PFR's, at natural logarithm —
Ashby's own units are logarithmic but unspecified in base, and the law is
base-invariant. See `AISafetyAtlas.InformationTheory.Fano` for why the atlas's
`AISafetyAtlas.Inference.entropyOn` is a separate development.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory (channelCapacity channelCapacity_eq_of_card_eq_pow channelCapacity_eq_of_card_eq_two_pow channelCapacity_fun channelCapacity_prod channelCapacity_le_of_card_le condEntropy_comp_self_left)


universe uD uR uE


/-! ## The entropy form

Ashby 11/8 recasts the law for variables fluctuating in time, "the case specially
considered by Shannon". The argument is two chain rules and subadditivity; it
assumes nothing about how the three variables are causally related. -/

section Entropy

universe uΩ

variable {Ω : Type uΩ} {D : Type uD} {R : Type uR} {E : Type uE}
variable [MeasurableSpace Ω] [MeasurableSpace D] [MeasurableSpace R] [MeasurableSpace E]
variable [MeasurableSingletonClass D] [MeasurableSingletonClass R] [MeasurableSingletonClass E]
variable [Countable D] [Countable R] [Countable E]
variable {μ : Measure Ω}

/--
**Ashby 11/8, with the 11/9 slack, and with the misprint repaired.** For any
three variables whatever — no causal assumption — if conditioning on the
response leaves the outcome at least as uncertain as the disturbance, up to a
slack `K`, then

`H[E] ≥ H[D] + H[R | D] − K − H[R]`.

The printed text has `H_D(E)` in place of `H_D(R)` in this line; the derivation
above it, and the sentence after it, both give `H_D(R)`.
-/
public theorem entropy_ge_of_condEntropy_ge (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {Dv : Ω → D} {Rv : Ω → R} {Ev : Ω → E}
    (hD : Measurable Dv) (hR : Measurable Rv) (hE : Measurable Ev)
    [FiniteRange Dv] [FiniteRange Rv] [FiniteRange Ev]
    (K : ℝ) (hkey : H[Dv | Rv ; μ] - K ≤ H[Ev | Rv ; μ]) :
    H[Dv ; μ] + H[Rv | Dv ; μ] - K - H[Rv ; μ] ≤ H[Ev ; μ] := by
  have h₁ : H[⟨Dv, Rv⟩ ; μ] = H[Rv ; μ] + H[Dv | Rv ; μ] := chain_rule μ hD hR
  have h₂ : H[⟨Rv, Dv⟩ ; μ] = H[Dv ; μ] + H[Rv | Dv ; μ] := chain_rule μ hR hD
  have h₃ : H[⟨Dv, Rv⟩ ; μ] = H[⟨Rv, Dv⟩ ; μ] := entropy_comm hD hR μ
  have h₄ : H[Ev | Rv ; μ] ≤ H[Ev ; μ] := condEntropy_le_entropy (μ := μ) hE hR
  linarith

omit [Countable E] [Countable R] in
/--
**The table hypothesis is a theorem, and an equality.** If every response
separates the disturbances — Ashby's "no element repeated in a column" — then
conditioning on the response, the outcome carries exactly the disturbance's
uncertainty. Ashby assumes only the `≥` half, and assumes it.
-/
public theorem condEntropy_outcome_eq (μ : Measure Ω) [IsFiniteMeasure μ]
    {Dv : Ω → D} {Rv : Ω → R} (hD : Measurable Dv) (hR : Measurable Rv)
    [FiniteRange Rv] (T : D → R → E)
    (hcol : ∀ r : R, Function.Injective fun d => T d r) :
    H[(fun ω => T (Dv ω) (Rv ω)) | Rv ; μ] = H[Dv | Rv ; μ] :=
  condEntropy_of_injective μ hD hR (fun r d => T d r) hcol

/--
**The law for a regulation table.** Combining the two previous results: for any
table whose columns separate the disturbances,

`H[outcome] ≥ H[D] + H[R | D] − H[R]`.

Still no assumption on how the response is produced — it need not be a function
of the disturbance, and need not be independent of it.
-/
public theorem entropy_outcome_ge (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Dv : Ω → D} {Rv : Ω → R} (hD : Measurable Dv) (hR : Measurable Rv)
    [FiniteRange Dv] [FiniteRange Rv]
    (T : D → R → E) (hT : Measurable fun p : D × R => T p.1 p.2)
    (hcol : ∀ r : R, Function.Injective fun d => T d r) :
    H[Dv ; μ] + H[Rv | Dv ; μ] - H[Rv ; μ] ≤ H[(fun ω => T (Dv ω) (Rv ω)) ; μ] := by
  have hmeas : Measurable fun ω => T (Dv ω) (Rv ω) := hT.comp (hD.prodMk hR)
  have : FiniteRange fun ω => T (Dv ω) (Rv ω) :=
    inferInstanceAs (FiniteRange ((fun p : D × R => T p.1 p.2) ∘ fun ω => (Dv ω, Rv ω)))
  have hkey : H[Dv | Rv ; μ] - 0 ≤ H[(fun ω => T (Dv ω) (Rv ω)) | Rv ; μ] := by
    rw [condEntropy_outcome_eq μ hD hR T hcol]
    linarith
  simpa using entropy_ge_of_condEntropy_ge μ hD hR hmeas 0 hkey

/--
**Ashby's headline, 11/8.** When the regulator plays a determinate strategy —
`H_D(R) = 0`, Ashby's "R is a determinate function of D" — the bound is

`H[outcome] ≥ H[D] − H[R]`:

*only variety in R can force down the variety in the outcome*.
-/
public theorem entropy_outcome_ge_of_strategy (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Dv : Ω → D} (hD : Measurable Dv) [FiniteRange Dv]
    (ρ : D → R) (hρ : Measurable ρ)
    (T : D → R → E) (hT : Measurable fun p : D × R => T p.1 p.2)
    (hcol : ∀ r : R, Function.Injective fun d => T d r) :
    H[Dv ; μ] - H[ρ ∘ Dv ; μ] ≤ H[(fun ω => T (Dv ω) (ρ (Dv ω))) ; μ] := by
  have hzero : H[ρ ∘ Dv | Dv ; μ] = 0 := condEntropy_comp_self_left μ hD hρ
  have h := entropy_outcome_ge (Rv := ρ ∘ Dv) μ hD (hρ.comp hD) T hT hcol
  rw [hzero] at h
  simp only [Function.comp_apply] at h
  linarith

/--
**A regulator can be no better than its sensor.** Ashby assumes the regulator
plays "on full knowledge of D's move". If instead it sees only `obs` and
responds `σ ∘ obs`, the bound degrades to the entropy of the *sensor reading*:

`H[outcome] ≥ H[D] − H[obs ∘ D]`.

This is the entropy reading of §11/11's channel statement, not an extension past
the chapter — Ashby's regulator does not have perfect information there, which is
the hypothesis `BY-004`'s informal claim also records. It follows from the
determinate-strategy form by the data-processing inequality for entropy.
-/
public theorem entropy_ge_of_sensor {O : Type*} [MeasurableSpace O]
    [MeasurableSingletonClass O] [Countable O]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Dv : Ω → D} (hD : Measurable Dv) [FiniteRange Dv]
    (obs : D → O) (hobs : Measurable obs) (σ : O → R) (hσ : Measurable σ)
    (T : D → R → E) (hT : Measurable fun p : D × R => T p.1 p.2)
    (hcol : ∀ r : R, Function.Injective fun d => T d r) :
    H[Dv ; μ] - H[obs ∘ Dv ; μ] ≤ H[(fun ω => T (Dv ω) (σ (obs (Dv ω)))) ; μ] := by
  have hmain := entropy_outcome_ge_of_strategy (ρ := σ ∘ obs) μ hD (hσ.comp hobs) T hT hcol
  have hproc : H[(σ ∘ obs) ∘ Dv ; μ] ≤ H[obs ∘ Dv ; μ] := by
    have : ((σ ∘ obs) ∘ Dv) = σ ∘ (obs ∘ Dv) := rfl
    rw [this]
    exact entropy_comp_le μ (hobs.comp hD) σ
  have hEq : (fun ω => T (Dv ω) ((σ ∘ obs) (Dv ω)))
      = fun ω => T (Dv ω) (σ (obs (Dv ω))) := rfl
  rw [hEq] at hmain
  linarith

/-! ## §11/11: the regulator as a channel

*"The law of Requisite Variety says that R's capacity as a regulator cannot
exceed R's capacity as a channel of communication."*

Ashby states this and then sets four exercises that are all arithmetic in **bits
per unit time**: an insect's optic nerve of a hundred fibres at twenty bits a
second, a ship's telegraph, a general's ten signallers. To say anything about
those, the atlas needs a capacity, not just a sensor reading.

**Which capacity.** `channelCapacity` is the noiseless alphabet ceiling
`log |O|` per use — exactly what the four exercises compute, and not what §9/15
generally calls capacity: that section's worked Markov example uses its actual
entropy rate, `0.842` bits per step, not the `log 3` ceiling of its three-state
alphabet. The general definition lives in `AISafetyAtlas.Control.ChannelRate`,
where `chainRate` is §9/12's weighted column entropy and `ashbyCapacity` is
§9/15's rate. Nothing below formalizes that, nor the noisy Shannon capacity
`sup I(input : output)`; this is the exercise-level noiseless bound, which is
sharper where the alphabet is what limits the channel.

**Which direction.** Everything here is a *necessary* condition. Capacity at
least the disturbance entropy is what regulation requires; that it suffices is
not proved and does not follow. Ashby's Ex. 1 asks whether a channel is
"sufficient to enable it to defend itself", and the honest answer this gives is
that the necessary condition is not binding — see
`AISafetyAtlas.Examples.Control.insect_optic_nerve_not_binding`. -/

/-! Ashby's measure of a regulator's variety is the capacity of a discrete
noiseless channel, `channelCapacity` — `log` of the signal count. It is not
specific to regulation, so it lives in
`AISafetyAtlas.InformationTheory.ChannelCapacity` together with its closure
lemmas (`channelCapacity_fun` for repeated use, `channelCapacity_prod` for
parallel channels, `channelCapacity_eq_of_card_eq_pow` and
`channelCapacity_le_of_card_le`), and is used here. -/

/--
**§11/11, as an inequality.** A regulator acting on what a channel delivers
cannot force the outcome's entropy below `H[D]` by more than the channel's
capacity:

`H[outcome] ≥ H[D] − C`.

Two things differ from `entropy_ge_of_sensor`, in opposite directions, and both
matter for the word *channel*.

*The hypothesis is weaker.* The observation `obs` is a variable on `Ω`, not a
function of the disturbance, so the channel may be **noisy** — what the regulator
sees need not be determined by what happened. Applying to more models makes this
the stronger statement on that axis.

*The conclusion is weaker.* The bound is the channel's capacity rather than the
entropy of the particular reading, and `H[obs] ≤ log |O|` always. What is bought
is uniformity: the capacity does not depend on the disturbance law, which is what
makes this a statement about the channel rather than about one situation. Where
the reading's law is known, `entropy_ge_of_sensor` is sharper.

The regulator's response is any measurable function of the channel output. It
need not be injective, and nothing is assumed about how good it is.
-/
public theorem entropy_outcome_ge_sub_channelCapacity {O : Type*} [MeasurableSpace O]
    [MeasurableSingletonClass O] [Fintype O]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Dv : Ω → D} (hD : Measurable Dv) [FiniteRange Dv]
    (obs : Ω → O) (hobs : Measurable obs) (σ : O → R) (hσ : Measurable σ)
    (T : D → R → E) (hT : Measurable fun p : D × R => T p.1 p.2)
    (hcol : ∀ r : R, Function.Injective fun d => T d r) :
    H[Dv ; μ] - channelCapacity O ≤ H[(fun ω => T (Dv ω) (σ (obs ω))) ; μ] := by
  have : FiniteRange obs := ⟨Set.toFinite _⟩
  have : FiniteRange (σ ∘ obs) := inferInstanceAs (FiniteRange (σ ∘ obs))
  have hmain := entropy_outcome_ge (Rv := σ ∘ obs) μ hD (hσ.comp hobs) T hT hcol
  have hnn : 0 ≤ H[σ ∘ obs | Dv ; μ] := condEntropy_nonneg _ _ _
  have hcap : H[σ ∘ obs ; μ] ≤ channelCapacity O :=
    le_trans (entropy_comp_le μ hobs σ) (entropy_le_log_card obs μ)
  have hEq : (fun ω => T (Dv ω) ((σ ∘ obs) ω)) = fun ω => T (Dv ω) (σ (obs ω)) := rfl
  rw [hEq] at hmain
  linarith

/--
**§11/11, as the impossibility Ashby's exercises use.** *Complete* regulation —
the outcome held at a single value, which is Ashby's *"it is constancy that is to
be transmitted"* — requires the channel to carry the whole disturbance:

`H[D] ≤ C`.

This is the contrapositive of the inequality above, and it is a **necessary**
condition only. A channel of sufficient capacity is not thereby shown to admit a
regulator that achieves constancy; nothing here constructs one.
-/
public theorem entropy_le_channelCapacity_of_complete {O : Type*} [MeasurableSpace O]
    [MeasurableSingletonClass O] [Fintype O]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    {Dv : Ω → D} (hD : Measurable Dv) [FiniteRange Dv]
    (obs : Ω → O) (hobs : Measurable obs) (σ : O → R) (hσ : Measurable σ)
    (T : D → R → E) (hT : Measurable fun p : D × R => T p.1 p.2)
    (hcol : ∀ r : R, Function.Injective fun d => T d r)
    (hconst : H[(fun ω => T (Dv ω) (σ (obs ω))) ; μ] = 0) :
    H[Dv ; μ] ≤ channelCapacity O := by
  have h := entropy_outcome_ge_sub_channelCapacity μ hD obs hobs σ hσ T hT hcol
  rw [hconst] at h
  linarith

end Entropy

end AISafetyAtlas.Control
