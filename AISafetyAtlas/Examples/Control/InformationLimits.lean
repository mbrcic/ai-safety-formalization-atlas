module

public import AISafetyAtlas.Control.InformationLimits

/-!
# Information-theoretic control limits — worked consequences

Four readings of `AISafetyAtlas.Control.InformationLimits`.

1. **A noiseless actuator has no control loss.** `controlLoss_eq_zero_of_noiseless`
   is Theorem 2 at `H(Z) = 0`: if the actuation channel is deterministic, the
   action and the initial state settle the outcome.
2. **Without measurement, feedback buys nothing.**
   `entropyReduction_le_of_no_information` is Theorem 10 at `I(X ; C) = 0`. A
   controller whose action is independent of the state cannot beat open-loop
   control at all.
3. **A controller is bounded by its sensor.** `entropyReduction_le_of_sensor`
   composes Theorem 10 with the data-processing inequality: if the action is
   computed from a sensor reading, the advantage over open-loop control is at
   most the entropy of what the sensor reported. This is the same statement
   `AISafetyAtlas.Control.entropy_ge_of_sensor` makes for Ashby's law, reached
   from the other side.
4. **The open-loop model is satisfiable, and discriminating.**
   `openLoopBound_forgetSecond` holds at `Δopen = log 2` for a plant that erases
   one bit of a two-bit state — strictly below the trivial ceiling `log 4`. And
   `not_openLoopBound_erase` shows the definition **discriminates**: a plant that
   erases the state outright fails the bound at `log 2`. Satisfiability alone
   would prove nothing, since the ceiling `log |S|` works for every plant; what
   is needed is a case where the bound fails, and that is the second witness.
-/

namespace AISafetyAtlas.Examples.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.Control AISafetyAtlas.InformationTheory

universe uΩ uS uK uN uT uO

variable {Ω : Type uΩ} {S : Type uS} {K : Type uK} {N : Type uN} {T : Type uT}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K]
variable [MeasurableSpace N] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K]
variable [MeasurableSingletonClass N] [MeasurableSingletonClass T]
variable [Countable S] [Countable K] [Countable N] [Countable T]

/--
**A noiseless actuator has no control loss.** If the actuation channel carries no
entropy, then knowing the initial state and the control action determines the
outcome exactly. Theorem 2 read at `H(Z) = 0`.
-/
public theorem controlLoss_eq_zero_of_noiseless (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {Z : Ω → N} {X' : Ω → T}
    (hX : Measurable X) (hC : Measurable C) (hZ : Measurable Z) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange C] [FiniteRange Z] [FiniteRange X']
    (hpure : Purified μ X C Z X')
    (hindep : H[Z | ⟨X, C⟩ ; μ] = H[Z ; μ])
    (hnoiseless : H[Z ; μ] = 0) :
    controlLoss μ X C X' = 0 := by
  have hle := controlLoss_le_entropy_noise μ hX hC hZ hX' hpure hindep
  have hnn : 0 ≤ controlLoss μ X C X' := condEntropy_nonneg _ _ _
  rw [hnoiseless] at hle
  linarith

/--
**Without measurement, feedback buys nothing.** If the control action carries no
information about the initial state, closed-loop control cannot beat the best
open-loop control. Theorem 10 read at `I(X ; C) = 0`.
-/
public theorem entropyReduction_le_of_no_information (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} {X' : Ω → T}
    (hX : Measurable X) (hC : Measurable C) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange C] [FiniteRange X']
    (Δopen : ℝ)
    (hstep : H[X | C ; μ] - Δopen ≤ H[X' | C ; μ])
    (hblind : I[X : C ; μ] = 0) :
    entropyReduction μ X X' ≤ Δopen := by
  have h := entropyReduction_le_of_condEntropy_ge μ hX hC hX' Δopen hstep
  rw [hblind] at h
  linarith

/-- Mutual information never exceeds the entropy of either variable. -/
public theorem mutualInfo_le_entropy_right (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {C : Ω → K} (hX : Measurable X) (hC : Measurable C)
    [FiniteRange X] [FiniteRange C] :
    I[X : C ; μ] ≤ H[C ; μ] := by
  rw [mutualInfo_comm hX hC μ, mutualInfo_eq_entropy_sub_condEntropy hC hX μ]
  have := condEntropy_nonneg C X μ
  linarith

/--
**A controller is bounded by its sensor.** If the control action is computed from
a sensor reading `obs ∘ X`, then the advantage closed-loop control has over
open-loop is at most the entropy of what the sensor reported — no matter how the
action is computed from it.

This is Theorem 10 composed with the data-processing inequality for entropy, and
it is the same conclusion `AISafetyAtlas.Control.entropy_ge_of_sensor` draws from
Ashby's law: you cannot regulate better than your sensor lets you.
-/
public theorem entropyReduction_le_of_sensor {O : Type uO} [MeasurableSpace O]
    [MeasurableSingletonClass O] [Countable O]
    (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    {X : Ω → S} {X' : Ω → T} (hX : Measurable X) (hX' : Measurable X')
    [FiniteRange X] [FiniteRange X']
    (obs : S → O) (hobs : Measurable obs) (act : O → K) (hact : Measurable act)
    (Δopen : ℝ)
    (hstep : H[X | act ∘ (obs ∘ X) ; μ] - Δopen ≤ H[X' | act ∘ (obs ∘ X) ; μ]) :
    entropyReduction μ X X' ≤ Δopen + H[obs ∘ X ; μ] := by
  have hC : Measurable (act ∘ (obs ∘ X)) := hact.comp (hobs.comp hX)
  have h := entropyReduction_le_of_condEntropy_ge μ hX hC hX' Δopen hstep
  have hbound : I[X : act ∘ (obs ∘ X) ; μ] ≤ H[act ∘ (obs ∘ X) ; μ] :=
    mutualInfo_le_entropy_right μ hX hC
  have hproc : H[act ∘ (obs ∘ X) ; μ] ≤ H[obs ∘ X ; μ] :=
    entropy_comp_le μ (hobs.comp hX) act
  linarith

/-! ## Witnesses for the open-loop model

`IsPlant` and `OpenLoopBound` are the atlas's rendering of Touchette–Lloyd's
model rather than formulas the paper writes, so they need checking. Two things
matter: that they are satisfiable at all, and that `OpenLoopBound` can hold with
a `Δopen` strictly below the trivial ceiling `log |S|` for a plant that really
does destroy entropy. Both are shown here.

The plant discards the second coordinate of a two-bit state. It reduces entropy —
by up to one bit — and `Δopen = log 2` is admissible, well under the trivial
`log 4`. A second plant, which erases the state entirely, shows the definition is
not satisfied by every `Δopen`. -/

/-- A two-bit state. -/
public abbrev TwoBit : Type := Fin 2 × Fin 2

/-- The plant that keeps the first bit and discards the second, whatever the
control action and whatever the noise. -/
@[expose] public def forgetSecond : TwoBit → Unit → Unit → Fin 2 :=
  fun s _ _ => s.1

/-- The forgetful plant really is the actuation map of the pair
`(X, first bit of X)`. -/
public theorem isPlant_forgetSecond {Ω : Type uΩ} [MeasurableSpace Ω] (X : Ω → TwoBit) :
    IsPlant forgetSecond X (fun _ => ()) (fun _ => ()) (fun ω => (X ω).1) :=
  fun _ => rfl

/--
**`OpenLoopBound` is satisfiable below the trivial ceiling.** Discarding one bit
of a two-bit state costs at most `log 2` of entropy, on every ensemble — so
`Δopen = log 2` is admissible where the trivial bound would be `log 4`.

The argument is subadditivity: the state is its own pair of bits, so its entropy
is at most the entropy of the bit that survives plus the entropy of the bit that
does not, and the latter is at most `log 2`.
-/
public theorem openLoopBound_forgetSecond {Ω : Type uΩ} [MeasurableSpace Ω]
    (μ : Measure Ω) {X : Ω → TwoBit} (hX : Measurable X) :
    OpenLoopBound μ forgetSecond X (fun _ => ()) (Real.log 2) := by
  intro s _ _ _
  have hfst : Measurable fun ω => (X ω).1 := measurable_fst.comp hX
  have hsnd : Measurable fun ω => (X ω).2 := measurable_snd.comp hX
  have hpair : H[X ; μ[|s]] ≤ H[fun ω => (X ω).1 ; μ[|s]] + H[fun ω => (X ω).2 ; μ[|s]] := by
    have h := entropy_pair_le_add hfst hsnd (μ[|s])
    have hid : (⟨fun ω => (X ω).1, fun ω => (X ω).2⟩ : Ω → Fin 2 × Fin 2) = X := rfl
    rwa [hid] at h
  have hbit : H[fun ω => (X ω).2 ; μ[|s]] ≤ Real.log 2 := by
    have := entropy_le_log_card (fun ω => (X ω).2) (μ[|s])
    simpa using this
  have hgoal : H[fun ω => forgetSecond (X ω) () (() : Unit) ; μ[|s]]
      = H[fun ω => (X ω).1 ; μ[|s]] := rfl
  rw [hgoal]
  linarith

/-- The plant that erases the state: whatever the disturbance and whatever the
action, the outcome carries nothing. -/
@[expose] public def eraseAll : TwoBit → Unit → Unit → Unit :=
  fun _ _ _ => ()

/--
**The definition discriminates.** `OpenLoopBound` is not satisfied by every
`Δopen`: a plant that erases the state outright fails it at `log 2`, because a
uniform two-bit state carries `log 4` and the plant leaves nothing.

This is the check the pair needs. That *some* `Δopen` works for every plant is
trivial — the ceiling `log |S|` always does — so a satisfiability witness alone
would say nothing. What has to be shown is a plant and a `Δopen` for which the
bound **fails**, and that is this.
-/
public theorem not_openLoopBound_erase :
    ¬ OpenLoopBound (uniformOn (Set.univ : Set TwoBit)) eraseAll id
        (fun _ => ()) (Real.log 2) := by
  intro h
  have hμ : (uniformOn (Set.univ : Set TwoBit)) Set.univ ≠ 0 := by
    have : IsProbabilityMeasure (uniformOn (Set.univ : Set TwoBit)) := inferInstance
    simp
  have hkey := h Set.univ MeasurableSet.univ hμ ()
  rw [cond_univ] at hkey
  have hent : H[(id : TwoBit → TwoBit) ; uniformOn (Set.univ : Set TwoBit)]
      = Real.log 4 := by
    rw [IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
    norm_num [Set.ncard_univ, Nat.card_eq_fintype_card]
  have hzero : H[fun ω => eraseAll (id ω) () (() : Unit)
      ; uniformOn (Set.univ : Set TwoBit)] = 0 := entropy_const _
  rw [hent, hzero] at hkey
  have h2 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast
    ring
  have hpos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [h2] at hkey
  linarith

/-! ## The minimization in eq. (28) is not decoration

`minControlLoss` is the paper's `L_C`, an infimum over the admitted controllers;
`controlLoss` is the loss of one controller. A witness has to show that the two
can differ, because if they never did then the minimization would be a formality
and the atlas's pointwise theorems would already be the printed ones. That is
what this section supplies, and it is why every `L_C` record on `BY-005` can be
read as covering the printed statement rather than a weaker one.

The plant is a gate. On action `0` it emits a fixed value and the actuation noise
never reaches the state; on action `1` it passes the noise straight through. The
initial state is trivial, so nothing but the choice of action separates the two
admitted controllers, and their losses are `0` and `log 2`. -/

/-- A gate: action `0` blocks the actuation noise, action `1` passes it through. -/
@[expose] public def noiseGate : Unit → Fin 2 → Fin 2 → Fin 2 :=
  fun _ c z => if c = 0 then 0 else z

/-- The two admitted controllers: block the noise, or pass it. -/
@[expose] public def gatePolicies : Set (Fin 2 → Fin 2) :=
  {fun _ => 0, fun _ => 1}

/-- Blocking the noise leaves nothing undetermined. -/
public theorem controlLoss_gate_block :
    controlLoss (uniformOn (Set.univ : Set (Fin 2))) (fun _ => ()) (fun _ => (0 : Fin 2))
        (plantOutcome noiseGate (fun _ => ()) (fun _ => (0 : Fin 2)) id) = 0 := by
  have hconst : plantOutcome noiseGate (fun _ => ()) (fun _ => (0 : Fin 2)) (id : Fin 2 → Fin 2)
      = fun _ => (0 : Fin 2) := rfl
  refine le_antisymm ?_ (condEntropy_nonneg _ _ _)
  have hle : controlLoss (uniformOn (Set.univ : Set (Fin 2))) (fun _ => ())
      (fun _ => (0 : Fin 2)) (plantOutcome noiseGate (fun _ => ()) (fun _ => (0 : Fin 2)) id)
      ≤ H[plantOutcome noiseGate (fun _ => ()) (fun _ => (0 : Fin 2)) (id : Fin 2 → Fin 2)
          ; uniformOn (Set.univ : Set (Fin 2))] := by
    have : FiniteRange (⟨fun _ => (), fun _ => (0 : Fin 2)⟩ : Fin 2 → Unit × Fin 2) :=
      ⟨Set.toFinite _⟩
    have : FiniteRange (plantOutcome noiseGate (fun _ => ())
        (fun _ => (0 : Fin 2)) (id : Fin 2 → Fin 2)) := ⟨Set.toFinite _⟩
    exact condEntropy_le_entropy _ (by rw [hconst]; exact measurable_const) (by fun_prop)
  refine hle.trans ?_
  rw [hconst]
  exact le_of_eq (entropy_const _)

/-- Passing the noise through leaves the whole bit undetermined: the state and the
action are both constant, so they say nothing about the outcome. -/
public theorem controlLoss_gate_pass :
    controlLoss (uniformOn (Set.univ : Set (Fin 2))) (fun _ => ()) (fun _ => (1 : Fin 2))
        (plantOutcome noiseGate (fun _ => ()) (fun _ => (1 : Fin 2)) id) = Real.log 2 := by
  have : FiniteRange (⟨fun _ => (), fun _ => (1 : Fin 2)⟩ : Fin 2 → Unit × Fin 2) :=
    ⟨Set.toFinite _⟩
  have : FiniteRange (id : Fin 2 → Fin 2) := ⟨Set.toFinite _⟩
  have hid : plantOutcome noiseGate (fun _ => ()) (fun _ => (1 : Fin 2)) (id : Fin 2 → Fin 2)
      = (id : Fin 2 → Fin 2) := rfl
  have hindep : ProbabilityTheory.IndepFun (id : Fin 2 → Fin 2)
      (⟨fun _ => (), fun _ => (1 : Fin 2)⟩ : Fin 2 → Unit × Fin 2)
      (uniformOn (Set.univ : Set (Fin 2))) :=
    ProbabilityTheory.indepFun_const_right _ ((), 1)
  rw [controlLoss, hid, hindep.condEntropy_eq_entropy measurable_id (by fun_prop),
    IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
  norm_num [Set.ncard_univ, Nat.card_eq_fintype_card]

/--
**The printed `L_C` is strictly below a controller's loss.** Over the two admitted
controllers the minimum is `0`, while the controller that passes the noise loses a
full bit. So `minControlLoss` is not `controlLoss` in disguise, and eq. (28)'s
minimization does real work.

The minimum is read off without computing the infimum: it is at most the blocking
controller's loss, which is `0`, and at least `0` because conditional entropy is
nonnegative.
-/
public theorem minControlLoss_lt_controlLoss_gate :
    minControlLoss (uniformOn (Set.univ : Set (Fin 2))) noiseGate (fun _ => ()) id
        gatePolicies
      < controlLoss (uniformOn (Set.univ : Set (Fin 2))) (fun _ => ()) (fun _ => (1 : Fin 2))
          (plantOutcome noiseGate (fun _ => ()) (fun _ => (1 : Fin 2)) id) := by
  have hmin : minControlLoss (uniformOn (Set.univ : Set (Fin 2))) noiseGate
      (fun _ => ()) id gatePolicies = 0 := by
    refine le_antisymm ?_
      (minControlLoss_nonneg _ _ _ _ ⟨fun _ => (0 : Fin 2), Or.inl rfl⟩)
    refine (minControlLoss_le _ _ _ _ (show (fun _ => (0 : Fin 2)) ∈ gatePolicies from
      Or.inl rfl)).trans ?_
    exact le_of_eq controlLoss_gate_block
  rw [hmin, controlLoss_gate_pass]
  exact Real.log_pos (by norm_num)

/-! ## The feasible set of eq. (28) is not `Set.univ`

`minControlLoss` takes the admissible controllers as a parameter, and it matters
which one is the printed `L_C`. Eq. (28) minimizes over `{p(c|x)}` — channels
from the *state*, which is `inputPolicies`. A bare map `Ω → K` can do something
no `p(c|x)` can: read the actuation noise.

The plant here lets a controller cancel the noise exactly, if it can see it. The
noise-reading controller drives the loss to zero; it is not an input policy, and
the constant controller — which is one — loses a full bit. So minimizing over
`Set.univ` returns something strictly below the printed quantity, and an earlier
revision of `minControlLoss`'s docstring calling `Set.univ` "the unconstrained
minimum" was wrong about the source. -/

/-- A plant whose noise the controller can cancel outright, if it sees it. -/
@[expose] public def shiftPlant : Unit → ZMod 2 → ZMod 2 → ZMod 2 :=
  fun _ c z => z - c

/-- The controller that *is* the actuation noise. No `p(c|x)` can be this. -/
@[expose] public def noiseReader : ZMod 2 → ZMod 2 := id

/-- Reading the noise cancels it: the outcome is constant, so nothing is lost. -/
public theorem controlLoss_noiseReader :
    controlLoss (uniformOn (Set.univ : Set (ZMod 2))) (fun _ => ()) noiseReader
        (plantOutcome shiftPlant (fun _ => ()) noiseReader id) = 0 := by
  have hconst : plantOutcome shiftPlant (fun _ => ()) noiseReader (id : ZMod 2 → ZMod 2)
      = fun _ => (0 : ZMod 2) := funext fun ω => sub_self _
  refine le_antisymm ?_ (condEntropy_nonneg _ _ _)
  have : FiniteRange (⟨fun _ => (), noiseReader⟩ : ZMod 2 → Unit × ZMod 2) :=
    ⟨Set.toFinite _⟩
  have : FiniteRange (plantOutcome shiftPlant (fun _ => ())
      noiseReader (id : ZMod 2 → ZMod 2)) := ⟨Set.toFinite _⟩
  refine le_trans (condEntropy_le_entropy _ (by rw [hconst]; exact measurable_const)
    (by fun_prop)) ?_
  rw [hconst]
  exact le_of_eq (entropy_const _)

/-- The constant controller is an input policy, and it loses the whole bit: with
the state carrying nothing and the control fixed, the outcome is the noise. -/
public theorem controlLoss_constant_shiftPlant :
    controlLoss (uniformOn (Set.univ : Set (ZMod 2))) (fun _ => ()) (fun _ => (0 : ZMod 2))
        (plantOutcome shiftPlant (fun _ => ()) (fun _ => (0 : ZMod 2)) id) = Real.log 2 := by
  have : FiniteRange (⟨fun _ => (), fun _ => (0 : ZMod 2)⟩ : ZMod 2 → Unit × ZMod 2) :=
    ⟨Set.toFinite _⟩
  have : FiniteRange (id : ZMod 2 → ZMod 2) := ⟨Set.toFinite _⟩
  have hid : plantOutcome shiftPlant (fun _ => ()) (fun _ => (0 : ZMod 2))
      (id : ZMod 2 → ZMod 2) = (id : ZMod 2 → ZMod 2) := funext fun ω => sub_zero _
  have hindep : ProbabilityTheory.IndepFun (id : ZMod 2 → ZMod 2)
      (⟨fun _ => (), fun _ => (0 : ZMod 2)⟩ : ZMod 2 → Unit × ZMod 2)
      (uniformOn (Set.univ : Set (ZMod 2))) :=
    ProbabilityTheory.indepFun_const_right _ ((), 0)
  rw [controlLoss, hid, hindep.condEntropy_eq_entropy measurable_id (by fun_prop),
    IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
  norm_num [Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card]

/-- The noise-reader is measurable, so the failure below is the conditional
independence and nothing else. -/
public theorem measurable_noiseReader : Measurable noiseReader :=
  Measurable.of_discrete

/--
**The noise-reader is not a `p(c|x)`.** Its conditional mutual information with
the noise, given the state, is a full bit — where an input policy's is zero by
definition. It fails on that count and not on measurability, which
`measurable_noiseReader` records: the map is measurable and still inadmissible.
This is what makes the distinction between `Set.univ` and `inputPolicies` a real
one rather than a bookkeeping choice.
-/
public theorem not_isInputPolicy_noiseReader :
    ¬ IsInputPolicy (uniformOn (Set.univ : Set (ZMod 2))) (fun _ => ())
        (id : ZMod 2 → ZMod 2) noiseReader := by
  have : FiniteRange (id : ZMod 2 → ZMod 2) := ⟨Set.toFinite _⟩
  have : FiniteRange (fun _ : ZMod 2 => ()) := ⟨Set.toFinite _⟩
  intro hpolicy
  have h := hpolicy.condIndep
  have hzero : I[(id : ZMod 2 → ZMod 2) : (id : ZMod 2 → ZMod 2) | (fun _ : ZMod 2 => ()) ;
      uniformOn (Set.univ : Set (ZMod 2))] = 0 :=
    (condMutualInfo_eq_zero measurable_id measurable_id).mpr h
  rw [condMutualInfo_eq' measurable_id measurable_id measurable_const _] at hzero
  -- conditioning on a constant is no conditioning at all
  have h₁ : H[(id : ZMod 2 → ZMod 2) | (fun _ : ZMod 2 => ()) ;
      uniformOn (Set.univ : Set (ZMod 2))] = Real.log 2 := by
    have hindep : ProbabilityTheory.IndepFun (id : ZMod 2 → ZMod 2)
        (fun _ : ZMod 2 => ()) (uniformOn (Set.univ : Set (ZMod 2))) :=
      ProbabilityTheory.indepFun_const_right _ ()
    rw [hindep.condEntropy_eq_entropy measurable_id measurable_const,
      IsUniform.entropy_eq' Set.finite_univ isUniform_uniformOn measurable_id]
    norm_num [Set.ncard_univ, Nat.card_eq_fintype_card, ZMod.card]
  -- and the noise determines the noise-reader
  have h₂ : H[(id : ZMod 2 → ZMod 2) | ⟨(id : ZMod 2 → ZMod 2), fun _ : ZMod 2 => ()⟩ ;
      uniformOn (Set.univ : Set (ZMod 2))] = 0 := by
    have : FiniteRange (⟨(id : ZMod 2 → ZMod 2), fun _ : ZMod 2 => ()⟩ :
        ZMod 2 → ZMod 2 × Unit) := ⟨Set.toFinite _⟩
    -- `id` is the first projection of the pair it is conditioned on, so it adds
    -- nothing: pairing a variable with a function of it is an injective recoding
    set W : ZMod 2 → ZMod 2 × Unit := ⟨(id : ZMod 2 → ZMod 2), fun _ => ()⟩ with hWdef
    have hWm : Measurable W := by fun_prop
    have : FiniteRange W := ⟨Set.toFinite _⟩
    have : FiniteRange (Prod.fst ∘ W) := ⟨Set.toFinite _⟩
    have : FiniteRange (⟨Prod.fst ∘ W, W⟩ : ZMod 2 → ZMod 2 × (ZMod 2 × Unit)) :=
      ⟨Set.toFinite _⟩
    have hpair : H[⟨Prod.fst ∘ W, W⟩ ; uniformOn (Set.univ : Set (ZMod 2))]
        = H[W ; uniformOn (Set.univ : Set (ZMod 2))] :=
      entropy_comp_of_injective _ hWm (fun w => (w.1, w))
        (fun _ _ h => congrArg Prod.snd h)
    have hchain : H[⟨Prod.fst ∘ W, W⟩ ; uniformOn (Set.univ : Set (ZMod 2))]
        = H[W ; uniformOn (Set.univ : Set (ZMod 2))]
          + H[Prod.fst ∘ W | W ; uniformOn (Set.univ : Set (ZMod 2))] :=
      chain_rule _ (measurable_fst.comp hWm) hWm
    have hfst : (Prod.fst ∘ W) = (id : ZMod 2 → ZMod 2) := rfl
    rw [← hfst]
    linarith
  rw [h₁, h₂, sub_zero] at hzero
  exact absurd hzero (ne_of_gt (Real.log_pos (by norm_num)))

/--
**`Set.univ` is not the printed feasible set.** Minimizing over every map
`Ω → K` returns `0`, while the constant controller — an input policy, so
admissible in eq. (28) — loses `log 2`. The gap is the noise-reader, which
`not_isInputPolicy_noiseReader` shows eq. (28) excludes.
-/
public theorem minControlLoss_univ_lt_inputPolicy :
    minControlLoss (uniformOn (Set.univ : Set (ZMod 2))) shiftPlant (fun _ => ())
        (id : ZMod 2 → ZMod 2) Set.univ
      < controlLoss (uniformOn (Set.univ : Set (ZMod 2))) (fun _ => ())
          (fun _ => (0 : ZMod 2))
          (plantOutcome shiftPlant (fun _ => ()) (fun _ => (0 : ZMod 2)) id) := by
  have hzero : minControlLoss (uniformOn (Set.univ : Set (ZMod 2))) shiftPlant
      (fun _ => ()) (id : ZMod 2 → ZMod 2) Set.univ = 0 := by
    refine le_antisymm ?_ (minControlLoss_nonneg _ _ _ _ ⟨noiseReader, Set.mem_univ _⟩)
    exact (minControlLoss_le _ _ _ _ (Set.mem_univ noiseReader)).trans
      (le_of_eq controlLoss_noiseReader)
  rw [hzero, controlLoss_constant_shiftPlant]
  exact Real.log_pos (by norm_num)

end AISafetyAtlas.Examples.Control
