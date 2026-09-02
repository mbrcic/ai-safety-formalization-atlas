module

public import AISafetyAtlas.Control.RequisiteVariety
public import AISafetyAtlas.InformationTheory.ChannelCapacity

/-!
# Ashby §11/14: control on top of regulation

W. Ross Ashby, *An Introduction to Cybernetics*, §11/14 (printed pp. 213–214).
The chapter's regulator `R` has so far played against a disturbance `D` to hold
an outcome steady. §11/14 puts a **controller** `C` upstream of `R`, choosing
which outcome is to be held, so the diagram of immediate effects becomes

```
D → T → E
C → R
```

and Ashby argues that the second capability is bought with the first:

> Suppose now that `R` is a perfect regulator. If `C` sets `a` as the target,
> then (through `R`'s agency) `E` will take the value `a`, whatever value `D`
> may take. … Thus the fact that `R` is a perfect regulator gives `C` complete
> control over the output, in spite of the entrance of disturbing effects by way
> of `D`. Thus, perfect regulation of the outcome by `R` makes possible a
> complete control over the outcome by `C`.

and then, from the other side,

> The achievement of control may thus depend necessarily on the achievement of
> regulation.

Both halves are here. `IsPerfectRegulator` is the hypothesis — one strategy per
target, holding the outcome at that target against every disturbance — and
`outcome_eq_comp` is the whole of the first half: under it the outcome is a
function of the controller's choice **alone**, with `D` eliminated. Complete
control is then `exists_strategy_forcing`, and the compound target Ashby
insists on — a printed sequence `a, b, a, c, c, a` produced *"regardless of D's
values during the sequence"* — is `seq_outcome_eq`.

## What the second half costs

*"Depend necessarily"* is made quantitative by chapter 11's own impossibility
theorem rather than by a fresh argument. Perfect regulation collapses
`admittedOutcomes` to a single outcome
(`admittedOutcomes_of_isPerfectRegulator`), which `two_le_card_admittedOutcomes`
forbids below a threshold of regulator variety; so a controller that is obeyed
at all forces

`|D| ≤ |R|` and `|C| ≤ |R|`,

`card_disturbance_le_card_regulator` and `card_controller_le_card_regulator`.
The regulator must be at least as varied as the disturbance it cancels *and* as
the controller it serves. That is requisite variety charged twice, once for each
input, and it is the content of Ashby's sentence.

## §11/14's four exercises

The exercises quantify the *internal* links of the diagram. `FactorsThrough` is
the reading that makes them statements rather than pictures: the regulator sees
`C` only through a channel `α` and `D` only through a channel `β`, and its move
is a function of the two readings. **This factorization is Ashby's diagram, not a
consequence of anything above** — the exercises are theorems about that reading.

* Ex. 2 asks the capacity of `D → R`: `channelCapacity_disturbance_le_channel`.
* Ex. 3 asks the capacity of `C → R`: `channelCapacity_controller_le_channel`.
* Ex. 4 asks the capacity of `R → T`, and its printed answer *adds* the two:
  *"R→T must carry 2 bits/sec to neutralise D (from Ex. 2), and 20 bits/sec from
  C; as these two are independent (D's values and C's not correlated), the
  capacity must be at least 22 bits/sec."* What the model forces is
  `max_channelCapacity_le_channelCapacity_regulator`, the **maximum** and not the
  sum. Whether the sum is also needed depends on `T`: it does hold when the
  `R → T` link is literally two independent sub-channels, which is
  `channelCapacity_prod`, but nothing here makes it so. For Ashby's own Table
  11/3/1 the maximum is attained and the sum is not needed — see
  `AISafetyAtlas.Examples.Control.ashbyControl_capacity_lt_sum`, which runs on his
  own answer to Ex. 1. His Ex. 2 stipulates a different, attenuating `T`, so this is
  a statement about what the general model forces, not a correction to his
  arithmetic.

These are capacities **per use**. Ashby's exercises are quoted in bits per
second; `ashbyCapacity` converts, and §9/15's own conversion sentence is
`ashbyCapacity_rescale`.

## The channel reading

§11/14's second picture is that `R` and `T` together *"form a compound channel
to E that transmits fully from C while transmitting nothing from D"*. Both
clauses are proved. `entropy_outcome_eq_entropy_controller` is full transmission:
no variety of `C` is lost, when distinct targets are distinct outcomes.
`condEntropy_outcome_controller` is transmission of nothing from `D`, and holds
whatever the disturbance's law — knowing the setting leaves no uncertainty in the
outcome for the disturbance to occupy. Under Ashby's own side condition, *"D's
values and C's not correlated"*, that becomes the flat statement that the outcome
and the disturbance share no information at all:
`mutualInfo_outcome_disturbance_eq_zero`.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory (channelCapacity channelCapacity_eq_of_card_eq_pow channelCapacity_eq_of_card_eq_two_pow channelCapacity_fun channelCapacity_prod channelCapacity_le_of_card_le condEntropy_comp_self_left)

universe uC uD uR uE uA uB

/-! ## Perfect regulation under a controller -/

section Counting

variable {C : Type uC} {D : Type uD} {R : Type uR} {E : Type uE}

/--
**§11/14's hypothesis.** `R` is a *perfect regulator* for the controller when it
has, for each target `c` the controller may set, a strategy `f c` that holds the
outcome at `g c` whatever the disturbance does.

`g` is the controller's dial: it says which outcome each setting names. Ashby's
targets *are* outcomes, which is `g = id`; keeping `g` separate costs nothing and
makes "complete control" the surjectivity of a map rather than an assumption
about the alphabets.
-/
@[expose] public def IsPerfectRegulator (T : D → R → E) (f : C → D → R) (g : C → E) : Prop :=
  ∀ c d, T d (f c d) = g c

variable {T : D → R → E} {f : C → D → R} {g : C → E}

/--
**The whole of §11/14's first half.** Under perfect regulation the outcome is a
function of the controller's choice **alone**: the disturbance has been
eliminated, not merely bounded.

Everything else in this file is a reading of this equation.
-/
public theorem outcome_eq_comp (h : IsPerfectRegulator T f g)
    {Ω : Type*} (Cv : Ω → C) (Dv : Ω → D) :
    (fun ω => T (Dv ω) (f (Cv ω) (Dv ω))) = g ∘ Cv :=
  funext fun ω => h (Cv ω) (Dv ω)

/--
**Complete control.** *"If C sets a as the target, then (through R's agency) E
will take the value a, whatever value D may take."* When every outcome is named
by some setting, the controller can force any outcome it likes.
-/
public theorem exists_strategy_forcing (h : IsPerfectRegulator T f g)
    (hg : Surjective g) (e : E) : ∃ c : C, ∀ d : D, T d (f c d) = e := by
  obtain ⟨c, hc⟩ := hg e
  exact ⟨c, fun d => (h c d).trans hc⟩

/--
**The compound target.** *"And if C sets a particular sequence — a, b, a, c, c,
a, say — as sequential or compound target, then that sequence will be produced,
regardless of D's values during the sequence."*

The disturbance sequence is arbitrary and is not quantified over jointly with the
target sequence: one strategy family answers every disturbance history.
-/
public theorem seq_outcome_eq (h : IsPerfectRegulator T f g) {n : ℕ}
    (cs : Fin n → C) (ds : Fin n → D) :
    (fun i => T (ds i) (f (cs i) (ds i))) = g ∘ cs :=
  outcome_eq_comp h cs ds

/-! ## What control costs the regulator

*"The achievement of control may thus depend necessarily on the achievement of
regulation."* Ashby leaves this qualitative; chapter 11 already contains the
theorem that makes it a count. -/

/--
Perfect regulation collapses the admitted outcomes to one — which is what
*"perfect"* means, and what §11/5's counting law is about.
-/
public theorem admittedOutcomes_of_isPerfectRegulator [DecidableEq R] [DecidableEq E]
    (h : IsPerfectRegulator T f g) (c : C) {s : Finset D} (hs : s.Nonempty) :
    admittedOutcomes T (f c) s = {g c} := by
  rw [admittedOutcomes, show (fun d => T d (f c d)) = fun _ => g c from funext (h c)]
  exact Finset.image_const hs _

/--
**Control needs as much regulator variety as there is disturbance.** Derived from
§11/10's impossibility theorem rather than from a new argument: if the regulator
had fewer moves than the disturbance has, two outcomes would have to occur, and
perfect regulation admits exactly one.
-/
public theorem card_disturbance_le_card_regulator [DecidableEq R] [DecidableEq E]
    [Fintype D] [Fintype R] [Nonempty C]
    (h : IsPerfectRegulator T f g) (hcol : ∀ r : R, Injective fun d => T d r) :
    Fintype.card D ≤ Fintype.card R := by
  by_contra hcon
  have hlt : Fintype.card R < Fintype.card D := Nat.lt_of_not_le hcon
  have : Nonempty D := Fintype.card_pos_iff.mp (by omega)
  have h2 := two_le_card_admittedOutcomes T (f (Classical.arbitrary C)) hcol hlt
  rw [admittedOutcomes_of_isPerfectRegulator h _ Finset.univ_nonempty] at h2
  simp at h2

/-- Distinct targets need distinct regulator moves, at every disturbance. -/
public theorem injective_regulator_of_target (h : IsPerfectRegulator T f g)
    (hg : Injective g) (d : D) : Injective fun c => f c d := fun c c' hcc =>
  hg (by rw [← h c d, ← h c' d]; exact congrArg (T d) hcc)

/-- Distinct disturbances need distinct regulator moves, at every target. -/
public theorem injective_regulator_of_disturbance (h : IsPerfectRegulator T f g)
    (hcol : ∀ r : R, Injective fun d => T d r) (c : C) : Injective fun d => f c d := by
  intro d d' hdd
  have hdd' : f c d = f c d' := hdd
  refine hcol (f c d') ?_
  show T d (f c d') = T d' (f c d')
  rw [← hdd', h c d, hdd', h c d']

/--
**Control needs as much regulator variety as the controller has.** The other half
of the charge: the regulator serves `|C|` distinct targets and must have a
distinct move for each, since a repeated move would produce a repeated outcome.
-/
public theorem card_controller_le_card_regulator [Fintype C] [Fintype R] [Nonempty D]
    (h : IsPerfectRegulator T f g) (hg : Injective g) :
    Fintype.card C ≤ Fintype.card R :=
  Fintype.card_le_of_injective _ (injective_regulator_of_target h hg (Classical.arbitrary D))

end Counting

/-! ## The exercises: capacity of the regulator's own links -/

section Capacity

variable {C : Type uC} {D : Type uD} {R : Type uR} {E : Type uE}
variable {A : Type uA} {B : Type uB}
variable {T : D → R → E} {f : C → D → R} {g : C → E}

/--
**Ashby's two-input diagram, as a hypothesis.** The regulator reads the
controller only through `α` and the disturbance only through `β`, and its move is
a function of the two readings.

This is a *reading* of the printed diagram `D → T → E`, `C → R`, not a
consequence of perfect regulation: nothing above forces the regulator's
information to arrive on two separate channels. §11/14's exercises are theorems
about this reading.
-/
@[expose] public def FactorsThrough (f : C → D → R) (α : C → A) (β : D → B) (σ : A → B → R) :
    Prop :=
  ∀ c d, f c d = σ (α c) (β d)

variable {α : C → A} {β : D → B} {σ : A → B → R}

/-- The controller's channel must separate the targets. -/
public theorem injective_controlChannel [Nonempty D] (h : IsPerfectRegulator T f g)
    (hg : Injective g) (hfac : FactorsThrough f α β σ) : Injective α := by
  intro c c' hcc
  refine injective_regulator_of_target h hg (Classical.arbitrary D) ?_
  show f c _ = f c' _
  rw [hfac, hfac, hcc]

/-- The disturbance's channel must separate the disturbances. -/
public theorem injective_disturbanceChannel [Nonempty C] (h : IsPerfectRegulator T f g)
    (hcol : ∀ r : R, Injective fun d => T d r) (hfac : FactorsThrough f α β σ) :
    Injective β := by
  intro d d' hdd
  refine injective_regulator_of_disturbance h hcol (Classical.arbitrary C) ?_
  show f _ d = f _ d'
  rw [hfac, hfac, hdd]

/--
**Ex. 3: the capacity of `C → R`.** *"C → E is to carry 20 bits/sec, therefore
C → R must carry at least that amount."* Per use, and by Ashby's own measure of
variety.
-/
public theorem channelCapacity_controller_le_channel [Fintype C] [Fintype A]
    [Nonempty C] [Nonempty D]
    (h : IsPerfectRegulator T f g) (hg : Injective g) (hfac : FactorsThrough f α β σ) :
    channelCapacity C ≤ channelCapacity A :=
  channelCapacity_le_of_card_le
    (Fintype.card_le_of_injective _ (injective_controlChannel h hg hfac))

/--
**Ex. 2: the capacity of `D → R`.** *"D is threatening to transmit to E at 2
bits/sec. To reduce this to zero the channel D → R must transmit at not less than
this rate."*

Ashby's `2` is what gets through his attenuating `T`, not the `5` bits/sec
emitted at `D`. Here the columns of `T` separate the disturbances, so nothing is
attenuated and the figure to cancel is the disturbance's own variety.
-/
public theorem channelCapacity_disturbance_le_channel [Fintype D] [Fintype B]
    [Nonempty C] [Nonempty D]
    (h : IsPerfectRegulator T f g) (hcol : ∀ r : R, Injective fun d => T d r)
    (hfac : FactorsThrough f α β σ) :
    channelCapacity D ≤ channelCapacity B :=
  channelCapacity_le_of_card_le
    (Fintype.card_le_of_injective _ (injective_disturbanceChannel h hcol hfac))

/--
**Ex. 4: the capacity of `R → T`, and it is a maximum, not a sum.** Ashby answers
by adding the two loads — *"R → T must carry 2 bits/sec to neutralise D (from Ex.
2), and 20 bits/sec from C; as these two are independent (D's values and C's not
correlated), the capacity must be at least 22 bits/sec"* — but what the model
forces is only that the regulator's repertoire dominate each load separately.

The sum is what `channelCapacity_prod` gives, and it is the right answer when the
`R → T` link really is two independent sub-channels carried side by side. Nothing
in §11/14 makes it so, and for Ashby's own Table 11/3/1 the maximum is attained
with no room to spare: see
`AISafetyAtlas.Examples.Control.ashbyControl_capacity_lt_sum`. Since
his Ex. 2 stipulates a different, attenuating `T`, this is a limit on what the
general model forces and not a correction to his arithmetic.
-/
public theorem max_channelCapacity_le_channelCapacity_regulator [DecidableEq R] [DecidableEq E]
    [Fintype C] [Fintype D] [Fintype R] [Nonempty C] [Nonempty D]
    (h : IsPerfectRegulator T f g) (hg : Injective g)
    (hcol : ∀ r : R, Injective fun d => T d r) :
    max (channelCapacity C) (channelCapacity D) ≤ channelCapacity R :=
  max_le
    (channelCapacity_le_of_card_le (card_controller_le_card_regulator h hg))
    (channelCapacity_le_of_card_le (card_disturbance_le_card_regulator h hcol))

end Capacity

/-! ## The compound channel

*"A suitable regulator R, taking information from both C and D, and interposed
between C and T … may be able to form, with T, a compound channel to E that
transmits fully from C while transmitting nothing from D."* -/

section Entropy

universe uΩ

variable {Ω : Type uΩ} {C : Type uC} {D : Type uD} {R : Type uR} {E : Type uE}
variable [MeasurableSpace Ω] [MeasurableSpace C] [MeasurableSpace D] [MeasurableSpace E]
variable [MeasurableSingletonClass C] [MeasurableSingletonClass D] [MeasurableSingletonClass E]
variable [Countable C] [Countable D] [Countable E]
variable {μ : Measure Ω} {T : D → R → E} {f : C → D → R} {g : C → E}

omit [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D] in
/--
**Transmitting nothing from `D`.** The compound channel's output carries no
uncertainty at all once the controller's setting is known — the disturbance
contributes nothing, whatever its law.
-/
public theorem condEntropy_outcome_controller [IsZeroOrProbabilityMeasure μ]
    (h : IsPerfectRegulator T f g) {Cv : Ω → C} (hC : Measurable Cv) [FiniteRange Cv]
    (Dv : Ω → D) (hg : Measurable g) :
    H[(fun ω => T (Dv ω) (f (Cv ω) (Dv ω))) | Cv ; μ] = 0 := by
  rw [outcome_eq_comp h Cv Dv]
  exact condEntropy_comp_self_left μ hC hg

omit [MeasurableSpace D] [MeasurableSingletonClass D] [Countable D] [Countable E] in
/--
**Transmitting fully from `C`.** When distinct settings name distinct outcomes,
the compound channel loses none of the controller's variety.
-/
public theorem entropy_outcome_eq_entropy_controller [IsZeroOrProbabilityMeasure μ]
    (h : IsPerfectRegulator T f g) {Cv : Ω → C} (hC : Measurable Cv) [FiniteRange Cv]
    (Dv : Ω → D) (hg : Injective g) :
    H[(fun ω => T (Dv ω) (f (Cv ω) (Dv ω))) ; μ] = H[Cv ; μ] := by
  rw [outcome_eq_comp h Cv Dv]
  exact entropy_comp_of_injective μ hC g hg

omit [MeasurableSingletonClass C] [Countable C] [Countable D] [Countable E] in
/--
**Ashby's own side condition, and the flat form of "nothing from `D`".** *"as
these two are independent (D's values and C's not correlated)"*: when the
controller's setting is independent of the disturbance, the outcome and the
disturbance share no information whatever.

This is weaker than `condEntropy_outcome_controller`, which needs no hypothesis
on the disturbance's law at all; it is stated because it is the sentence Ashby
writes.
-/
public theorem mutualInfo_outcome_disturbance_eq_zero [IsZeroOrProbabilityMeasure μ]
    (h : IsPerfectRegulator T f g) {Cv : Ω → C} (hC : Measurable Cv) [FiniteRange Cv]
    {Dv : Ω → D} (hD : Measurable Dv) [FiniteRange Dv] (hg : Measurable g)
    (hindep : IndepFun Cv Dv μ) :
    I[(fun ω => T (Dv ω) (f (Cv ω) (Dv ω))) : Dv ; μ] = 0 := by
  rw [outcome_eq_comp h Cv Dv]
  have : FiniteRange (g ∘ Cv) := inferInstanceAs (FiniteRange (g ∘ Cv))
  exact (hindep.comp hg measurable_id).mutualInfo_eq_zero (hg.comp hC) hD

end Entropy

end AISafetyAtlas.Control
