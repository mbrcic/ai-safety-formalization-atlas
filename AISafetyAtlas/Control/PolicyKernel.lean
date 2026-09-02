module

public import AISafetyAtlas.Control.InformationLimits
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Eq. (28) as a minimum over kernels, and why deterministic feedback attains it

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004, eq. (28).

`AISafetyAtlas.Control.minControlLoss` is an infimum over controllers
*realizable on one sample space*. The source minimizes over conditional
distributions `{p(c|x)}`, and a fixed `Ω` need not realize every one of them —
a space carrying no auxiliary randomness realizes only some. That leaves the
realized infimum `≥` the source's, with no proved equality, and it is why
Theorem 2's *equality* case — a statement about a minimizer — did not transfer.

This module closes that gap by declaring the source's object and proving the two
agree.

## The argument, and where it comes from

Eq. (28) is displayed in the source in two lines, and the second is the one that
matters:

> `L_C = min over {p(c|x)} of H(X'|X,C)`
> `    = min over {p(c|x)} of ∑_x p_X(x) ∑_c H(X'|x,c) p(c|x)`

The numbers `H(X'|x,c)` are fixed by the actuation channel; only the weights
`p(c|x)` vary. So each inner sum is a weighted average of fixed numbers over
weights of the caller's choosing, and a weighted average is never below the
least number averaged. Putting all the weight on a minimizing `c` is therefore
optimal, and the minimum is

*∑_x p_X(x) · min over c of H(X'|x,c)*,

attained by the **deterministic** rule "at state `x`, play a minimizing `c`".

Deterministic rules are the ones that need no auxiliary randomness: `c ∘ X` is
realizable on *every* sample space. So the realized infimum and the kernel
infimum are attained by the same policies and are equal — and, being attained,
Theorem 2's equality case transfers with no attainment hypothesis.

This is the source's own thesis, transposed. Theorem 9 proves the open-loop half
of it in the paper's own words — *"no random choice of the controller's state
can improve upon that decrease"*, a **pure** controller beating every **mixed**
one. Eq. (28) has the same simplex structure, so `L_C` gets the same conclusion.

## What conditional independence buys

`atomLoss` is well defined — a function of `(x, c)` alone, not of the policy —
only because the controller carries no information about the noise beyond what
the state carries. That is `IsInputPolicy`, and it is exactly what fails for a
noise-reading controller: `Examples…minControlLoss_univ_lt_inputPolicy` exhibits
one that beats every input policy, so the linearity this whole module rests on
is not available on `Set.univ` and the closed form there is false.

## Finiteness

`[Finite K]` is the printed setting — the source's alphabets are finite — and it
is what makes a minimizing action exist rather than merely being approached. It
also supplies `FiniteRange C` for *arbitrary* members of `inputPolicies`, which
a bare `Countable K` does not.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uΩ uS uK uN uT

variable {Ω : Type uΩ} {S : Type uS} {K : Type uK} {N : Type uN} {T : Type uT}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K]
variable [MeasurableSpace N] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K]
variable [MeasurableSingletonClass N] [MeasurableSingletonClass T]
variable [Countable S] [Countable K] [Countable N] [Countable T]
variable {μ : Measure Ω}

/-! ## Independence at one atom -/

omit [MeasurableSingletonClass S] [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
/--
**Conditioning on an independent variable does not move the other's law.** If
`C` and `Z` are independent under `ν`, then conditioning on `C = c` leaves the
law of `Z` unchanged.

The one measure-theoretic step the argument needs that Mathlib does not already
package: independence is stated as a product formula on preimages, and what the
entropy calculation consumes is the equality of laws.
-/
public theorem map_cond_eq_of_indepFun {ν : Measure Ω} [IsFiniteMeasure ν]
    {C : Ω → K} {Z : Ω → N} (hC : Measurable C) (hZ : Measurable Z)
    (hindep : IndepFun C Z ν) (c : K) (hc : ν (C ⁻¹' {c}) ≠ 0) :
    (ν[|C ⁻¹' {c}]).map Z = ν.map Z := by
  have hCm : MeasurableSet (C ⁻¹' {c}) := hC (.singleton c)
  ext B hB
  rw [Measure.map_apply hZ hB, Measure.map_apply hZ hB, cond_apply hCm]
  rw [hindep.measure_inter_preimage_eq_mul _ _ (.singleton c) hB]
  rw [← mul_assoc, ENNReal.inv_mul_cancel hc (measure_ne_top ν _), one_mul]

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass N]
  [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable N] [Countable T] in
/--
**Conditional independence read at one atom.** `CondIndepFun` is stated `μ.map X`
-almost everywhere; on an atom of positive mass the almost-everywhere clause
cannot be dodged, so the independence holds there outright.
-/
public theorem indepFun_cond_of_condIndepFun {X : Ω → S} {C : Ω → K} {Z : Ω → N}
    (h : CondIndepFun C Z X μ) {x : S} (hx : μ.map X {x} ≠ 0) :
    IndepFun C Z (μ[|X ⁻¹' {x}]) := by
  rw [condIndepFun_iff, ae_iff] at h
  by_contra hcon
  exact hx (measure_mono_null (by simpa using hcon) h)

/-! ## The actuation loss at a state-action pair -/

/--
**`H(X'|x,c)`, the actuation loss at one state–action pair.** The entropy the
actuation channel leaves in the final state when the initial state is `x` and the
action is `c`.

Written with the law of the noise conditioned on `X = x` and *no* controller
anywhere in it: this is a property of the plant, which is the whole point of eq.
(28)'s minimization — the source puts it there "to ensure that `L_C` reflects the
properties of the actuation channel, and does not depend on one's choice of
control inputs". `condEntropy_atom_eq_atomLoss` is where an input policy's
conditional entropy at the atom is shown to be this number.
-/
@[expose] public noncomputable def atomLoss (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) (x : S) (c : K) : ℝ :=
  H[fun ω => F x c (Z ω) ; μ[|X ⁻¹' {x}]]

/--
**The best the plant can do at one state: *min over c of H(X'|x,c)*.** With `K` finite
and inhabited this infimum is attained; `exists_atomLoss_eq` produces a minimizer.
-/
@[expose] public noncomputable def minAtomLoss (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) (x : S) : ℝ :=
  ⨅ c : K, atomLoss μ F X Z x c

omit [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace N]
  [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass N]
  [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable N] [Countable T] in
/-- No action beats the best one. -/
public theorem minAtomLoss_le [Finite K] (μ : Measure Ω) (F : S → K → N → T)
    (X : Ω → S) (Z : Ω → N) (x : S) (c : K) :
    minAtomLoss μ F X Z x ≤ atomLoss μ F X Z x c :=
  ciInf_le (Finite.bddBelow_range _) c

omit [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace N]
  [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass N]
  [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable N] [Countable T] in
/-- **A minimizing action exists.** This is where `[Finite K]` is spent, and it is
what lets the printed `min` of eq. (28) be a minimum rather than an infimum. -/
public theorem exists_atomLoss_eq [Finite K] [Nonempty K] (μ : Measure Ω)
    (F : S → K → N → T) (X : Ω → S) (Z : Ω → N) (x : S) :
    ∃ c : K, atomLoss μ F X Z x c = minAtomLoss μ F X Z x := by
  obtain ⟨c, hc⟩ := Finite.exists_min (atomLoss μ F X Z x)
  exact ⟨c, le_antisymm (le_ciInf hc) (minAtomLoss_le μ F X Z x c)⟩

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K] [MeasurableSingletonClass S]
  [MeasurableSingletonClass K] [Countable S] [Countable K] in
/-- The atom of `⟨X, C⟩` is the intersection of the two atoms. -/
public theorem preimage_prodMk_singleton (X : Ω → S) (C : Ω → K) (x : S) (c : K) :
    (⟨X, C⟩ : Ω → S × K) ⁻¹' {(x, c)} = X ⁻¹' {x} ∩ C ⁻¹' {c} := by
  ext ω; simp [Prod.ext_iff]

omit [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable T] in
/--
**The atom entropy of an input policy is the plant's own number.** At a
state–action pair of positive mass, the conditional entropy of the outcome under
*any* input policy equals `atomLoss` — a quantity in which no controller appears.

This is the load-bearing step of the whole module, and it is exactly what
conditional independence buys. On the atom `X = x` the controller and the noise
are independent, so further conditioning on `C = c` does not move the law of the
noise; the outcome is then `F x c ∘ Z` against a law that the policy cannot
influence. Drop the independence and this fails — a controller that reads `Z` can
shift the noise law on its own atoms, which is how
`Examples…minControlLoss_univ_lt_inputPolicy` beats every input policy.
-/
public theorem condEntropy_atom_eq_atomLoss (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : S → K → N → T) {X : Ω → S} {Z : Ω → N} {C : Ω → K}
    (hX : Measurable X) (hZ : Measurable Z) (hC : Measurable C)
    (hpol : IsInputPolicy μ X Z C) {x : S} {c : K}
    (hxc : μ (X ⁻¹' {x} ∩ C ⁻¹' {c}) ≠ 0) :
    H[plantOutcome F X C Z | ⟨X, C⟩ ← (x, c) ; μ] = atomLoss μ F X Z x c := by
  have hXm : MeasurableSet (X ⁻¹' {x}) := hX (.singleton x)
  have hCm : MeasurableSet (C ⁻¹' {c}) := hC (.singleton c)
  -- the state atom carries the mass the pair atom does
  have hxpos : μ.map X {x} ≠ 0 := by
    rw [Measure.map_apply hX (.singleton x)]
    exact fun h => hxc (measure_mono_null Set.inter_subset_left h)
  -- so the controller and the noise are independent there
  have hind : IndepFun C Z (μ[|X ⁻¹' {x}]) :=
    indepFun_cond_of_condIndepFun hpol.condIndep hxpos
  have hcpos : (μ[|X ⁻¹' {x}]) (C ⁻¹' {c}) ≠ 0 := by
    rw [cond_apply hXm]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 (measure_ne_top μ _)) hxc
  -- conditioning twice is conditioning on the intersection
  have hcc : μ[|X ⁻¹' {x} ∩ C ⁻¹' {c}] = (μ[|X ⁻¹' {x}])[|C ⁻¹' {c}] :=
    (cond_cond_eq_cond_inter hXm hCm μ).symm
  -- on the atom the outcome is driven by the fixed pair
  have hae : plantOutcome F X C Z =ᵐ[μ[|X ⁻¹' {x} ∩ C ⁻¹' {c}]]
      fun ω => F x c (Z ω) := by
    refine ae_cond_of_forall_mem (hXm.inter hCm) fun ω hω => ?_
    simp only [plantOutcome, Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff] at hω ⊢
    rw [hω.1, hω.2]
  have : DiscreteMeasurableSpace N := MeasurableSingletonClass.toDiscreteMeasurableSpace
  have hFm : Measurable (F x c) := .of_discrete
  -- entropy sees the noise only through its law, and the law is the same on both
  have key : ∀ ν : Measure Ω,
      Measure.map (fun ω => F x c (Z ω)) ν = (ν.map Z).map (F x c) := by
    intro ν; rw [Measure.map_map hFm hZ]; rfl
  rw [preimage_prodMk_singleton, entropy_congr hae, atomLoss, entropy_def, entropy_def,
    hcc, key, key, map_cond_eq_of_indepFun hC hZ hind c hcpos]

/-! ## The closed form

From here the state and action alphabets `S` and `K` are finite. This is what
makes eq. (28)'s policy simplex finite-dimensional and turns the printed `min`
into a value that is *reached*. The noise and outcome types remain countable in
the surrounding general model; the printed all-finite setting is recovered by
specialization.
-/

omit [MeasurableSingletonClass N] [MeasurableSingletonClass T] [Countable S] [Countable K]
  [Countable N] [Countable T] in
/--
**Conditioning on a pair, state outside.** `H[W | ⟨X, C⟩] = ∑ₓ p(x) · H[W | C]`
against the ensemble conditioned on `X = x`.

PFR's `condEntropy_prod_eq_sum` sums over the *second* component; eq. (28) groups
by the state, which is the first. Same proof, transposed.
-/
public theorem condEntropy_prodMk_eq_sum [Fintype S] [Fintype K] (μ : Measure Ω)
    [IsFiniteMeasure μ] {W : Ω → T} {X : Ω → S} {C : Ω → K}
    (hX : Measurable X) (hC : Measurable C) :
    H[W | ⟨X, C⟩ ; μ] = ∑ x, μ.real (X ⁻¹' {x}) * H[W | C ; μ[|X ⁻¹' {x}]] := by
  simp_rw [condEntropy_eq_sum_fintype _ _ _ (hX.prodMk hC), condEntropy_eq_sum_fintype _ _ _ hC,
    Fintype.sum_prod_type, Finset.mul_sum, ← mul_assoc]
  congr with x
  congr with c
  have A := preimage_prodMk_singleton X C x c
  congr 2
  · rw [cond_real_apply (hX (.singleton x)), A]
    obtain hx | hx := eq_or_ne (μ.real (X ⁻¹' {x})) 0
    · have : μ.real (X ⁻¹' {x} ∩ C ⁻¹' {c}) = 0 :=
        measureReal_mono_null Set.inter_subset_left hx (by finiteness)
      simp [this, hx]
    · rw [mul_inv_cancel_left₀ hx]
  · rw [A, cond_cond_eq_cond_inter (hX (.singleton x)) (hC (.singleton c))]

/--
**Eq. (28)'s value: *∑ₓ p_X(x) · min over c of H(X'|x,c)*.** The source's own second line
with the minimization carried inside the sum, which is where it belongs once the
objective is seen to be linear in `p(c|x)`.

Nothing here mentions a controller or a sample space beyond `μ`, `X` and `Z`:
this is the number eq. (28) denotes, and `minControlLoss_inputPolicies_eq` and
`kernelMinControlLoss_eq` say the realized and kernel minima both equal it.
-/
@[expose] public noncomputable def closedFormLoss [Fintype S] (μ : Measure Ω)
    (F : S → K → N → T) (X : Ω → S) (Z : Ω → N) : ℝ :=
  ∑ x, μ.real (X ⁻¹' {x}) * minAtomLoss μ F X Z x

omit [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable T] in
/--
**No input policy beats the plant's best action, state by state.** On the
ensemble conditioned on `X = x`, the loss of any input policy is an average of
`atomLoss x c` over the actions it plays, so it is at least the least of them.

This is the inequality half of "mixing does not help": a weighted average never
falls below the smallest number averaged.
-/
public theorem minAtomLoss_le_condEntropy [Fintype S] [Fintype K] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N} {C : Ω → K}
    (hX : Measurable X) (hZ : Measurable Z) (hC : Measurable C)
    (hpol : IsInputPolicy μ X Z C) {x : S} (hx : μ (X ⁻¹' {x}) ≠ 0) :
    minAtomLoss μ F X Z x ≤ H[plantOutcome F X C Z | C ; μ[|X ⁻¹' {x}]] := by
  have : IsProbabilityMeasure (μ[|X ⁻¹' {x}]) := cond_isProbabilityMeasure hx
  rw [condEntropy_eq_sum_fintype _ _ _ hC]
  have hw : ∑ c : K, (μ[|X ⁻¹' {x}]).real (C ⁻¹' {c}) = 1 := by
    rw [sum_measureReal_preimage_singleton _ fun c _ => hC (.singleton c)]
    simp
  calc minAtomLoss μ F X Z x
      = ∑ c : K, (μ[|X ⁻¹' {x}]).real (C ⁻¹' {c}) * minAtomLoss μ F X Z x := by
        rw [← Finset.sum_mul, hw, one_mul]
    _ ≤ ∑ c : K, (μ[|X ⁻¹' {x}]).real (C ⁻¹' {c}) *
          H[plantOutcome F X C Z | C ← c ; μ[|X ⁻¹' {x}]] := by
        refine Finset.sum_le_sum fun c _ => ?_
        obtain hc | hc := eq_or_ne ((μ[|X ⁻¹' {x}]).real (C ⁻¹' {c})) 0
        · simp [hc]
        refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
        -- a fibre of positive mass is an atom of the pair, where the identity applies
        have hxc : μ (X ⁻¹' {x} ∩ C ⁻¹' {c}) ≠ 0 := by
          intro h
          refine hc ?_
          rw [cond_real_apply (hX (.singleton x))]
          simp [measureReal_def, h]
        have : H[plantOutcome F X C Z | C ← c ; μ[|X ⁻¹' {x}]]
            = H[plantOutcome F X C Z | ⟨X, C⟩ ← (x, c) ; μ] := by
          rw [preimage_prodMk_singleton,
            cond_cond_eq_cond_inter (hX (.singleton x)) (hC (.singleton c))]
        rw [this, condEntropy_atom_eq_atomLoss μ F hX hZ hC hpol hxc]
        exact minAtomLoss_le μ F X Z x c

omit [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable T] in
/--
**No input policy beats the closed form.** Half one of "the minimum of eq. (28)
is *∑ₓ p(x) · min over c of H(X'|x,c)*".
-/
public theorem closedFormLoss_le_controlLoss [Fintype S] [Fintype K] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N} {C : Ω → K}
    (hX : Measurable X) (hZ : Measurable Z) (hC : Measurable C)
    (hpol : IsInputPolicy μ X Z C) :
    closedFormLoss μ F X Z ≤ controlLoss μ X C (plantOutcome F X C Z) := by
  rw [controlLoss, condEntropy_prodMk_eq_sum μ hX hC, closedFormLoss]
  refine Finset.sum_le_sum fun x _ => ?_
  obtain hx | hx := eq_or_ne (μ.real (X ⁻¹' {x})) 0
  · simp [hx]
  refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
  exact minAtomLoss_le_condEntropy μ F hX hZ hC hpol
    fun h => hx (by simp [measureReal_def, h])

/-! ## Deterministic state feedback attains it -/

/--
**An optimal action at each state.** The `arg min` that eq. (28)'s linearity
selects: put all of `p(·|x)`'s weight here.
-/
@[expose] public noncomputable def bestAction [Finite K] [Nonempty K] (μ : Measure Ω)
    (F : S → K → N → T) (X : Ω → S) (Z : Ω → N) (x : S) : K :=
  (exists_atomLoss_eq μ F X Z x).choose

omit [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace N] [MeasurableSingletonClass S]
  [MeasurableSingletonClass K] [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
public theorem atomLoss_bestAction [Finite K] [Nonempty K] (μ : Measure Ω)
    (F : S → K → N → T) (X : Ω → S) (Z : Ω → N) (x : S) :
    atomLoss μ F X Z x (bestAction μ F X Z x) = minAtomLoss μ F X Z x :=
  (exists_atomLoss_eq μ F X Z x).choose_spec

omit [MeasurableSingletonClass K] [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable K] [Countable N] [Countable T] in
/--
**A deterministic state feedback is an input policy.** It carries nothing about
the noise for the plainest possible reason: on the ensemble `X = x` it is
*constant*, and a constant is independent of everything.

This is why the bridge closes without a realization construction — the winning
policy needs no auxiliary randomness, so it exists on every sample space.
-/
public theorem isInputPolicy_comp (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → S}
    {Z : Ω → N} (hX : Measurable X) (f : S → K) : IsInputPolicy μ X Z (f ∘ X) := by
  have : DiscreteMeasurableSpace S := MeasurableSingletonClass.toDiscreteMeasurableSpace
  refine ⟨(Measurable.of_discrete (f := f)).comp hX, ?_⟩
  rw [condIndepFun_iff]
  refine ae_of_all _ fun x => ?_
  by_cases hx : μ (X ⁻¹' {x}) = 0
  · rw [indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t _ _
    simp [ProbabilityTheory.cond, Measure.restrict_eq_zero.2 hx]
  · have : IsProbabilityMeasure (μ[|X ⁻¹' {x}]) := cond_isProbabilityMeasure hx
    have hae : (fun _ : Ω => f x) =ᵐ[μ[|X ⁻¹' {x}]] f ∘ X := by
      refine ae_cond_of_forall_mem (hX (.singleton x)) fun ω hω => ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
      simp [Function.comp_apply, hω]
    exact (indepFun_const_left (f x) Z).congr hae (ae_eq_refl Z)

/--
**The loss of a deterministic state feedback, atom by atom.** Conditioning on
`⟨X, f ∘ X⟩` is conditioning on `X`, because `s ↦ (s, f s)` is injective — so the
sum has one term per *state*, not per state–action pair, and each term is the
`atomLoss` of the action the policy chose.
-/
public theorem controlLoss_comp_eq [Fintype S] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : S → K → N → T) {X : Ω → S} {Z : Ω → N} (hX : Measurable X) (hZ : Measurable Z)
    (f : S → K) [FiniteRange (plantOutcome F X (f ∘ X) Z)] :
    controlLoss μ X (f ∘ X) (plantOutcome F X (f ∘ X) Z)
      = ∑ x, μ.real (X ⁻¹' {x}) * atomLoss μ F X Z x (f x) := by
  have : DiscreteMeasurableSpace S := MeasurableSingletonClass.toDiscreteMeasurableSpace
  have hfX : Measurable (f ∘ X) := (Measurable.of_discrete (f := f)).comp hX
  have hinj : Injective (fun s : S => (s, f s)) := fun _ _ h => (Prod.ext_iff.1 h).1
  have hmeas : Measurable ((fun s : S => (s, f s)) ∘ X) :=
    (Measurable.of_discrete (f := fun s : S => (s, f s))).comp hX
  have hcond : H[plantOutcome F X (f ∘ X) Z | ⟨X, f ∘ X⟩ ; μ]
      = H[plantOutcome F X (f ∘ X) Z | X ; μ] :=
    condEntropy_of_injective' μ (measurable_plantOutcome F hX hfX hZ) hX
      (fun s => (s, f s)) hinj hmeas
  rw [controlLoss, hcond, condEntropy_eq_sum_fintype _ _ _ hX]
  refine Finset.sum_congr rfl fun x _ => congrArg _ (entropy_congr ?_)
  refine ae_cond_of_forall_mem (hX (.singleton x)) fun ω hω => ?_
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at hω
  simp [plantOutcome, Function.comp_apply, hω]

/--
**The realized infimum is the closed form, and it is attained.**

Both halves meet: no input policy goes below *∑ₓ p(x) · min over c of H(X'|x,c)*, and the
deterministic state feedback `bestAction ∘ X` sits exactly on it. So the printed
`min` of eq. (28) is a minimum, reached by a policy that needs no randomness — and
`minControlLoss_inputPolicies_attained` names the minimizer that Theorem 2's
equality case asks for.
-/
public theorem minControlLoss_inputPolicies_eq [Fintype S] [Fintype K] [Nonempty K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    (hX : Measurable X) (hZ : Measurable Z)
    [FiniteRange (plantOutcome F X (bestAction μ F X Z ∘ X) Z)] :
    minControlLoss μ F X Z (inputPolicies μ X Z) = closedFormLoss μ F X Z := by
  have hmem : (bestAction μ F X Z ∘ X) ∈ inputPolicies μ X Z := isInputPolicy_comp μ hX _
  have hdet : controlLoss μ X (bestAction μ F X Z ∘ X)
      (plantOutcome F X (bestAction μ F X Z ∘ X) Z) = closedFormLoss μ F X Z := by
    rw [controlLoss_comp_eq μ F hX hZ, closedFormLoss]
    exact Finset.sum_congr rfl fun x _ => by rw [atomLoss_bestAction]
  refine le_antisymm ?_ ?_
  · exact hdet ▸ minControlLoss_le μ F X Z hmem
  · refine le_csInf ⟨_, _, hmem, rfl⟩ ?_
    rintro _ ⟨C, hC, rfl⟩
    exact closedFormLoss_le_controlLoss μ F hX hZ (IsInputPolicy.measurable hC) hC

/--
**A minimizer exists.** The hypothesis `minControlLoss_eq_entropy_noise_iff_of_attained`
carries as a *conclusion* here: `bestAction ∘ X` is an admitted policy no admitted
policy beats.

This is what the source's `min` asserts and never exhibits — the paper writes
`min` where its own argument supports `inf`, and constructs no optimal controller.
-/
public theorem minControlLoss_inputPolicies_attained [Fintype S] [Fintype K] [Nonempty K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    (hX : Measurable X) (hZ : Measurable Z)
    [FiniteRange (plantOutcome F X (bestAction μ F X Z ∘ X) Z)] :
    (bestAction μ F X Z ∘ X) ∈ inputPolicies μ X Z ∧
      ∀ C ∈ inputPolicies μ X Z,
        controlLoss μ X (bestAction μ F X Z ∘ X)
            (plantOutcome F X (bestAction μ F X Z ∘ X) Z)
          ≤ controlLoss μ X C (plantOutcome F X C Z) := by
  refine ⟨isInputPolicy_comp μ hX _, fun C hC => ?_⟩
  rw [controlLoss_comp_eq μ F hX hZ]
  refine le_trans (le_of_eq ?_)
    (closedFormLoss_le_controlLoss μ F hX hZ (IsInputPolicy.measurable hC) hC)
  rw [closedFormLoss]
  exact Finset.sum_congr rfl fun x _ => by rw [atomLoss_bestAction]

/-! ## Eq. (28)'s own object: a minimum over conditional distributions

`{p(c|x)}` is a set of stochastic kernels `S → K`, not a set of random variables
on `Ω`. Declared here as such, so that the printed minimization is an object in
the tree rather than a reading of one.

A kernel `κ` is realized by pairing the original space with the action drawn from
it: `μ ⊗ₘ κ.comap X hX` on `Ω × K`, where the state and noise are read off the
first coordinate and the action *is* the second. That the action is drawn from
`κ (X ω)` — the state and nothing else — is built into `comap X`, so this
construction can express every `p(c|x)` and nothing more.
-/

/-- **The joint law of state, noise and an action drawn from `p(c|x)`.** -/
@[expose] public noncomputable def kernelMeasure (μ : Measure Ω) {X : Ω → S}
    (hX : Measurable X) (κ : Kernel S K) : Measure (Ω × K) :=
  μ ⊗ₘ κ.comap X hX

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass N]
  [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable N] [Countable T] in
/-- Drawing an action from a Markov kernel keeps the joint law a probability. -/
public theorem isProbabilityMeasure_kernelMeasure (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} (hX : Measurable X) (κ : Kernel S K) [IsMarkovKernel κ] :
    IsProbabilityMeasure (kernelMeasure μ hX κ) :=
  inferInstanceAs (IsProbabilityMeasure (μ ⊗ₘ κ.comap X hX))

omit [MeasurableSingletonClass S] [MeasurableSingletonClass N] [MeasurableSingletonClass T]
  [Countable S] [Countable K] [Countable N] [Countable T] in
/-- The mass a kernel puts on a rectangle inside one state fibre: the state is
`x` throughout, so the kernel is the constant `κ x` there. -/
public theorem kernelMeasure_prod (μ : Measure Ω) [IsProbabilityMeasure μ] {X : Ω → S}
    (hX : Measurable X) (κ : Kernel S K) [IsMarkovKernel κ] {x : S} {A : Set Ω}
    (hA : MeasurableSet A) (hAx : A ⊆ X ⁻¹' {x}) (c : K) :
    kernelMeasure μ hX κ (A ×ˢ ({c} : Set K)) = κ x {c} * μ A := by
  rw [kernelMeasure, Measure.compProd_apply (hA.prod (.singleton c))]
  have hpt : ∀ ω, (κ.comap X hX) ω (Prod.mk ω ⁻¹' (A ×ˢ ({c} : Set K)))
      = A.indicator (fun _ => κ x {c}) ω := by
    intro ω
    by_cases hω : ω ∈ A
    · rw [Set.mk_preimage_prod_right hω, Set.indicator_of_mem hω, Kernel.comap_apply', hAx hω]
    · rw [Set.mk_preimage_prod_right_eq_empty hω, Set.indicator_of_notMem hω, measure_empty]
  simp_rw [hpt]
  rw [lintegral_indicator hA, lintegral_const, Measure.restrict_apply_univ]

omit [MeasurableSingletonClass N] [MeasurableSingletonClass T] [Countable S] [Countable K]
  [Countable N] [Countable T] in
/--
**The atom law of the noise, on the kernel side.** Conditioning the joint law on
`X = x` and `C = c` leaves the noise distributed exactly as `μ` conditioned on
`X = x` alone.

No conditional-independence argument is needed here, and none is available to
need: the product structure gives it. The kernel's mass `κ x {c}` appears in the
numerator and the denominator alike and cancels — which is the formal content of
"the choice of control inputs does not affect the actuation channel".
-/
public theorem map_cond_kernelMeasure (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → S} {Z : Ω → N} (hX : Measurable X) (hZ : Measurable Z)
    (κ : Kernel S K) [IsMarkovKernel κ] {x : S} {c : K}
    (hxc : kernelMeasure μ hX κ ((X ⁻¹' {x}) ×ˢ ({c} : Set K)) ≠ 0) :
    ((kernelMeasure μ hX κ)[|(X ⁻¹' {x}) ×ˢ ({c} : Set K)]).map (Z ∘ Prod.fst)
      = (μ[|X ⁻¹' {x}]).map Z := by
  have hXm : MeasurableSet (X ⁻¹' {x}) := hX (.singleton x)
  have hbox : MeasurableSet ((X ⁻¹' {x}) ×ˢ ({c} : Set K)) := hXm.prod (.singleton c)
  have hbase := kernelMeasure_prod μ hX κ hXm (le_refl _) c
  -- both the kernel mass and the state mass are nonzero, else the atom would be null
  have hκ : κ x {c} ≠ 0 := by intro h; exact hxc (by rw [hbase, h, zero_mul])
  have hμx : μ (X ⁻¹' {x}) ≠ 0 := by intro h; exact hxc (by rw [hbase, h, mul_zero])
  ext B hB
  have hZm : MeasurableSet (Z ⁻¹' B) := hZ hB
  have hinter : (X ⁻¹' {x}) ×ˢ ({c} : Set K) ∩ (Z ∘ Prod.fst) ⁻¹' B
      = (X ⁻¹' {x} ∩ Z ⁻¹' B) ×ˢ ({c} : Set K) := by
    ext p
    exact ⟨fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩, fun h => ⟨⟨h.1.1, h.2⟩, h.1.2⟩⟩
  rw [Measure.map_apply (hZ.comp measurable_fst) hB, Measure.map_apply hZ hB,
    cond_apply hbox, cond_apply hXm, hinter,
    kernelMeasure_prod μ hX κ (hXm.inter hZm) Set.inter_subset_left c, hbase]
  rw [ENNReal.mul_inv (Or.inl hκ) (Or.inl (by finiteness)), mul_comm (κ x {c})⁻¹,
    mul_assoc, ← mul_assoc (κ x {c})⁻¹, ENNReal.inv_mul_cancel hκ (by finiteness), one_mul]

/-- **`H(X'|X,C)` when the action is drawn from `p(c|x)`.** The control loss of a
conditional distribution, computed on the space where that distribution lives. -/
@[expose] public noncomputable def kernelControlLoss (μ : Measure Ω) (F : S → K → N → T)
    {X : Ω → S} (hX : Measurable X) (Z : Ω → N) (κ : Kernel S K) : ℝ :=
  controlLoss (kernelMeasure μ hX κ) (X ∘ Prod.fst) Prod.snd
    (plantOutcome F (X ∘ Prod.fst) Prod.snd (Z ∘ Prod.fst))

omit [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K] [MeasurableSingletonClass S]
  [MeasurableSingletonClass K] [MeasurableSingletonClass T] [Countable S] [Countable K]
  [Countable T] in
/-- The pair atom on the product space is the rectangle. -/
public theorem preimage_kernel_atom (X : Ω → S) (x : S) (c : K) :
    (⟨X ∘ Prod.fst, Prod.snd⟩ : Ω × K → S × K) ⁻¹' {(x, c)}
      = (X ⁻¹' {x}) ×ˢ ({c} : Set K) := by
  ext p; simp [Prod.ext_iff]

omit [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable T] in
/-- **The kernel side's atom entropy is the same plant number.** Counterpart of
`condEntropy_atom_eq_atomLoss`, obtained from the product structure instead of
from conditional independence. -/
public theorem condEntropy_atom_kernelMeasure (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : S → K → N → T) {X : Ω → S} {Z : Ω → N} (hX : Measurable X) (hZ : Measurable Z)
    (κ : Kernel S K) [IsMarkovKernel κ] {x : S} {c : K}
    (hxc : kernelMeasure μ hX κ ((X ⁻¹' {x}) ×ˢ ({c} : Set K)) ≠ 0) :
    H[plantOutcome F (X ∘ Prod.fst) Prod.snd (Z ∘ Prod.fst)
        | ⟨X ∘ Prod.fst, Prod.snd⟩ ← (x, c) ; kernelMeasure μ hX κ]
      = atomLoss μ F X Z x c := by
  have hbox : MeasurableSet ((X ⁻¹' {x}) ×ˢ ({c} : Set K)) :=
    (hX (.singleton x)).prod (.singleton c)
  have hae : plantOutcome F (X ∘ Prod.fst) Prod.snd (Z ∘ Prod.fst)
      =ᵐ[(kernelMeasure μ hX κ)[|(X ⁻¹' {x}) ×ˢ ({c} : Set K)]]
      fun p => F x c (Z p.1) := by
    refine ae_cond_of_forall_mem hbox fun p hp => ?_
    obtain ⟨hx', hc'⟩ := hp
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx' hc'
    simp [plantOutcome, hx', hc']
  have : DiscreteMeasurableSpace N := MeasurableSingletonClass.toDiscreteMeasurableSpace
  have hFm : Measurable (F x c) := .of_discrete
  have key : ∀ ν : Measure (Ω × K),
      Measure.map (fun p : Ω × K => F x c (Z p.1)) ν = (ν.map (Z ∘ Prod.fst)).map (F x c) := by
    intro ν; rw [Measure.map_map hFm (hZ.comp measurable_fst)]; rfl
  have keyμ : ∀ ν : Measure Ω,
      Measure.map (fun ω => F x c (Z ω)) ν = (ν.map Z).map (F x c) := by
    intro ν; rw [Measure.map_map hFm hZ]; rfl
  rw [preimage_kernel_atom, entropy_congr hae, atomLoss, entropy_def, entropy_def, key, keyμ,
    map_cond_kernelMeasure μ hX hZ κ hxc]

omit [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable T] in
/--
**Eq. (28)'s second displayed line, verbatim.**

> `L_C = min over {p(c|x)} of ∑ₓ p_X(x) ∑_c H(X'|x,c) p(c|x)`

This is the summand of that expression, proved equal to the control loss of the
kernel — so the objective really is *linear* in `p(c|x)`, with the numbers
`H(X'|x,c)` fixed by the plant. Everything else about the bridge is a consequence
of this one identity: a weighted average is minimized at a vertex.
-/
public theorem kernelControlLoss_eq_sum [Fintype S] [Fintype K] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    (hX : Measurable X) (hZ : Measurable Z) (κ : Kernel S K) [IsMarkovKernel κ] :
    kernelControlLoss μ F hX Z κ
      = ∑ x, μ.real (X ⁻¹' {x}) * ∑ c, (κ x {c}).toReal * atomLoss μ F X Z x c := by
  have := isProbabilityMeasure_kernelMeasure μ hX κ
  have hXt : Measurable (X ∘ (Prod.fst : Ω × K → Ω)) := hX.comp measurable_fst
  rw [kernelControlLoss, controlLoss,
    condEntropy_eq_sum_fintype _ _ _ (hXt.prodMk measurable_snd), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  have hmass : kernelMeasure μ hX κ ((⟨X ∘ Prod.fst, Prod.snd⟩ : Ω × K → S × K) ⁻¹' {(x, c)})
      = κ x {c} * μ (X ⁻¹' {x}) := by
    rw [preimage_kernel_atom]
    exact kernelMeasure_prod μ hX κ (hX (.singleton x)) (le_refl _) c
  obtain h0 | h0 := eq_or_ne (κ x {c} * μ (X ⁻¹' {x})) 0
  · have : (kernelMeasure μ hX κ).real
        ((⟨X ∘ Prod.fst, Prod.snd⟩ : Ω × K → S × K) ⁻¹' {(x, c)}) = 0 := by
      rw [measureReal_def, hmass, h0]; simp
    rw [this]
    rcases mul_eq_zero.1 h0 with hk | hm
    · simp [measureReal_def, hk]
    · simp [measureReal_def, hm]
  · rw [measureReal_def, hmass, ENNReal.toReal_mul,
      condEntropy_atom_kernelMeasure μ F hX hZ κ
        (by rw [← preimage_kernel_atom, hmass]; exact h0)]
    rw [measureReal_def]
    ring

omit [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass N]
  [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable N] [Countable T] in
/-- A Markov kernel's weights at a state sum to one. -/
public theorem sum_kernel_toReal [Fintype K] (κ : Kernel S K) [IsMarkovKernel κ]
    [MeasurableSingletonClass K] (x : S) : ∑ c : K, (κ x {c}).toReal = 1 := by
  simp [← measureReal_def]

omit [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable T] in
/-- **No conditional distribution beats the closed form.** The inner sum of eq.
(28) is an average of the numbers `H(X'|x,c)`, so it is at least the least. -/
public theorem closedFormLoss_le_kernelControlLoss [Fintype S] [Fintype K] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    (hX : Measurable X) (hZ : Measurable Z) (κ : Kernel S K) [IsMarkovKernel κ] :
    closedFormLoss μ F X Z ≤ kernelControlLoss μ F hX Z κ := by
  rw [kernelControlLoss_eq_sum μ F hX hZ κ, closedFormLoss]
  refine Finset.sum_le_sum fun x _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ measureReal_nonneg
  calc minAtomLoss μ F X Z x
      = ∑ c : K, (κ x {c}).toReal * minAtomLoss μ F X Z x := by
        rw [← Finset.sum_mul, sum_kernel_toReal κ x, one_mul]
    _ ≤ ∑ c : K, (κ x {c}).toReal * atomLoss μ F X Z x c :=
        Finset.sum_le_sum fun c _ =>
          mul_le_mul_of_nonneg_left (minAtomLoss_le μ F X Z x c) ENNReal.toReal_nonneg

omit [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable T] in
/-- **A deterministic conditional distribution loses exactly the closed form's
summand.** `Kernel.deterministic f` puts all of `p(·|x)` on `f x`, which is the
vertex the linearity argument selects. -/
public theorem kernelControlLoss_deterministic [Fintype S] [Fintype K] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    (hX : Measurable X) (hZ : Measurable Z) (f : S → K) (hf : Measurable f) :
    kernelControlLoss μ F hX Z (Kernel.deterministic f hf)
      = ∑ x, μ.real (X ⁻¹' {x}) * atomLoss μ F X Z x (f x) := by
  rw [kernelControlLoss_eq_sum μ F hX hZ _]
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  have hone : ((Kernel.deterministic f hf) x {f x}).toReal = 1 := by
    simp [Kernel.deterministic_apply]
  have hzero : ∀ c : K, c ≠ f x → ((Kernel.deterministic f hf) x {c}).toReal = 0 :=
    fun c hc => by
      rw [Kernel.deterministic_apply, Measure.dirac_apply' _ (.singleton c),
        Set.indicator_of_notMem (by simpa using Ne.symm hc), ENNReal.toReal_zero]
  rw [Finset.sum_eq_single (f x) (fun c _ hc => by rw [hzero c hc, zero_mul])
    (fun h => absurd (Finset.mem_univ _) h), hone, one_mul]

/--
**The bridge: the source's minimum over `{p(c|x)}`, as a Lean object, is the
realized minimum over input policies.**

`kernelMinControlLoss` quantifies over stochastic kernels `S → K` — eq. (28)'s own
`{p(c|x)}`, with no reference to any sample space. `minControlLoss … inputPolicies`
quantifies over the controllers realizable on one fixed `Ω`. The second was, until
now, only known to be `≥` the first.

They are equal, and the reason is not that every kernel is realizable on every
`Ω` — it is not. It is that the *optimum* is deterministic, and deterministic
policies are realizable everywhere. Both sides collapse onto the same closed form.
-/
@[expose] public noncomputable def kernelMinControlLoss (μ : Measure Ω) (F : S → K → N → T)
    {X : Ω → S} (hX : Measurable X) (Z : Ω → N) : ℝ :=
  sInf {r | ∃ κ : Kernel S K, ∃ _ : IsMarkovKernel κ, kernelControlLoss μ F hX Z κ = r}

omit [MeasurableSingletonClass T] [Countable S] [Countable K] [Countable T] in
/-- **Eq. (28) evaluated.** The source's minimum over all conditional
distributions is *∑ₓ p_X(x) · min over c of H(X'|x,c)*. -/
public theorem kernelMinControlLoss_eq [Fintype S] [Fintype K] [Nonempty K] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    (hX : Measurable X) (hZ : Measurable Z) :
    kernelMinControlLoss μ F hX Z = closedFormLoss μ F X Z := by
  have : DiscreteMeasurableSpace S := MeasurableSingletonClass.toDiscreteMeasurableSpace
  have hbest : Measurable (bestAction μ F X Z) := .of_discrete
  have hmem : kernelControlLoss μ F hX Z (Kernel.deterministic _ hbest)
      ∈ {r | ∃ κ : Kernel S K, ∃ _ : IsMarkovKernel κ, kernelControlLoss μ F hX Z κ = r} :=
    ⟨Kernel.deterministic _ hbest, inferInstance, rfl⟩
  have hdet : kernelControlLoss μ F hX Z (Kernel.deterministic _ hbest)
      = closedFormLoss μ F X Z := by
    rw [kernelControlLoss_deterministic μ F hX hZ _ hbest, closedFormLoss]
    exact Finset.sum_congr rfl fun x _ => by rw [atomLoss_bestAction]
  refine le_antisymm ?_ ?_
  · exact hdet ▸ csInf_le ⟨closedFormLoss μ F X Z, by
      rintro _ ⟨κ, hκ, rfl⟩
      exact closedFormLoss_le_kernelControlLoss μ F hX hZ κ⟩ hmem
  · refine le_csInf ⟨_, hmem⟩ ?_
    rintro _ ⟨κ, hκ, rfl⟩
    exact closedFormLoss_le_kernelControlLoss μ F hX hZ κ

/--
**Theorem 2's equality case is now unconditional: the two minima coincide.**

The realized-policy infimum over `inputPolicies` *is* the source's minimum over
`{p(c|x)}`. What blocked the printed equality case was that the atlas's minimum
might have exceeded the source's, so a minimizer of one need not minimize the
other. It cannot: they are the same number, attained by the same deterministic
policy.
-/
public theorem minControlLoss_inputPolicies_eq_kernelMin [Fintype S] [Fintype K] [Nonempty K]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : S → K → N → T) {X : Ω → S} {Z : Ω → N}
    (hX : Measurable X) (hZ : Measurable Z)
    [FiniteRange (plantOutcome F X (bestAction μ F X Z ∘ X) Z)] :
    minControlLoss μ F X Z (inputPolicies μ X Z) = kernelMinControlLoss μ F hX Z := by
  rw [kernelMinControlLoss_eq μ F hX hZ, minControlLoss_inputPolicies_eq μ F hX hZ]

end AISafetyAtlas.Control
