module

public import AISafetyAtlas.Goodhart.Overoptimization
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# A worked model for overoptimization

The library statement quantifies over an attribute space, a constraint function,
a proxy over a subset of the attributes, and an optimization sequence generated
by a rate function. This file inhabits every one of those binders at the
smallest instance on which nothing degenerates, and then reads off what the
theorem cost the principal, in exact rationals.

Two attributes, one of them measurable and one of them not. The constraint is a
budget, `s 0 + s 1 ≤ 1`, with both attributes floored at `0`. The robot is given
the first attribute as its proxy and the second is unmentioned. The principal's
own utility weights the unmentioned attribute twice as heavily.

The optimization sequence starts at `![0, 1]` -- all of the budget on the
unmentioned attribute -- and moves budget across at an exponentially decaying
rate, so that at time `t` the state is `![1 - Real.exp (-t), Real.exp (-t)]`.
Every state along it is feasible, the proxy rises to its supremum `1`, and the
sequence converges to `![1, 0]`.

The theorem then says the unmentioned attribute ends at its floor, and it does.
What that costs is exact: the principal's utility falls from `2` to `1`, and the
gap between what the proxy reports and what the principal gets rises from `-2`
to `0`. The robot did exactly what it was asked and the principal is strictly
worse off than before it started.

The file also inhabits the scope note. At an empty proxy attribute set every
hypothesis of the core lemma except nonemptiness holds at a state whose
unmentioned attribute is not at its floor, so nonemptiness is load-bearing and
not decoration.
-/

namespace AISafetyAtlas.Examples.Goodhart.Overoptimization

open Filter Set Topology MeasureTheory AISafetyAtlas.Goodhart

/-- The budget constraint: the two attributes share one unit. -/
@[expose] public def budget : (Fin 2 → ℝ) → ℝ := fun s => s 0 + s 1 - 1

/-- Both attributes are floored at zero. -/
@[expose] public def floor2 : Fin 2 → ℝ := fun _ => 0

/-- The proxy attribute set: the first attribute only. -/
@[expose] public def proxyAttrs : Set (Fin 2) := {0}

/-- The proxy utility: what the robot is told to maximize. -/
@[expose] public def proxyUtil : (proxyAttrs → ℝ) → ℝ := fun x => x ⟨0, rfl⟩

/-- The principal's utility, which weights the unmentioned attribute twice. -/
@[expose] public def trueUtil : (Fin 2 → ℝ) → ℝ := fun s => s 0 + 2 * s 1

/-- The initial state: all of the budget on the unmentioned attribute. -/
@[expose] public def initialState : Fin 2 → ℝ := ![0, 1]

/-- The rate function: budget moves from the unmentioned attribute to the proxy
attribute at an exponentially decaying rate. -/
@[expose] public noncomputable def rate : ℝ → (Fin 2 → ℝ) :=
  fun t => ![Real.exp (-t), -Real.exp (-t)]

/-- The optimization sequence the rate function generates. -/
@[expose] public noncomputable def path : ℝ → (Fin 2 → ℝ) :=
  fun t => ![1 - Real.exp (-t), Real.exp (-t)]

/-- The limit of the optimization sequence. -/
@[expose] public def limitState : Fin 2 → ℝ := ![1, 0]

private theorem rate_zero (t : ℝ) : rate t 0 = Real.exp (-t) := by simp [rate]
private theorem rate_one (t : ℝ) : rate t 1 = -Real.exp (-t) := by simp [rate]
private theorem path_zero (t : ℝ) : path t 0 = 1 - Real.exp (-t) := by simp [path]
private theorem path_one (t : ℝ) : path t 1 = Real.exp (-t) := by simp [path]
private theorem initialState_zero : initialState 0 = 0 := by simp [initialState]
private theorem initialState_one : initialState 1 = 1 := by simp [initialState]
private theorem limitState_zero : limitState 0 = 1 := by simp [limitState]
private theorem limitState_one : limitState 1 = 0 := by simp [limitState]

public theorem continuous_budget : Continuous budget := by
  unfold budget; fun_prop

public theorem strictMonoCoord_budget : StrictMonoCoord budget := by
  intro x i y h
  have hb : ∀ z : Fin 2 → ℝ, budget z = z 0 + z 1 - 1 := fun _ => rfl
  rw [hb, hb]
  by_cases h0 : i = 0
  · subst h0
    rw [Function.update_self, Function.update_of_ne (show (1:Fin 2) ≠ 0 by decide)]
    linarith
  · have h1 : i = 1 := by
      fin_cases i
      · exact absurd rfl h0
      · rfl
    subst h1
    rw [Function.update_of_ne (show (0:Fin 2) ≠ 1 by decide), Function.update_self]
    linarith

public theorem continuous_proxyUtil : Continuous proxyUtil :=
  continuous_apply _

public theorem strictMonoCoord_proxyUtil : StrictMonoCoord proxyUtil := by
  intro x i y h
  have hi : i = (⟨0, rfl⟩ : proxyAttrs) := Subtype.ext i.2
  subst hi
  show x ⟨0, rfl⟩ < Function.update x ⟨0, rfl⟩ y ⟨0, rfl⟩
  rw [Function.update_self]
  exact h

public theorem continuous_trueUtil : Continuous trueUtil := by
  unfold trueUtil; fun_prop

/-- The principal's utility satisfies print's own condition on it. -/
public theorem strictMonoCoord_trueUtil : StrictMonoCoord trueUtil := by
  intro x i y h
  have hu : ∀ z : Fin 2 → ℝ, trueUtil z = z 0 + 2 * z 1 := fun _ => rfl
  rw [hu, hu]
  by_cases h0 : i = 0
  · subst h0
    rw [Function.update_self, Function.update_of_ne (show (1:Fin 2) ≠ 0 by decide)]
    linarith
  · have h1 : i = 1 := by
      fin_cases i
      · exact absurd rfl h0
      · rfl
    subst h1
    rw [Function.update_of_ne (show (0:Fin 2) ≠ 1 by decide), Function.update_self]
    linarith

/-- Monotonicity, which the gap corollary asks for, from print's hypothesis. -/
public theorem monotone_trueUtil : Monotone trueUtil :=
  monotone_of_strictMonoCoord strictMonoCoord_trueUtil

public theorem continuous_rate : Continuous rate := by
  refine continuous_pi (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · simp only [rate_zero]; fun_prop
  · simp only [rate_one]; fun_prop

/-- The optimization sequence really is the integral of the rate function. -/
public theorem path_eq_integral (t : ℝ) (_ht : t ∈ Ici (0:ℝ)) :
    path t = initialState + ∫ u in (0:ℝ)..t, rate u := by
  have hproj : ∀ i : Fin 2, (∫ u in (0:ℝ)..t, rate u) i = ∫ u in (0:ℝ)..t, rate u i := by
    intro i
    have h := ContinuousLinearMap.intervalIntegral_comp_comm
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i)
      (continuous_rate.intervalIntegrable (μ := volume) 0 t)
    simpa using h.symm
  refine funext (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · rw [Pi.add_apply, hproj 0, path_zero, initialState_zero]
    simp only [rate_zero]
    simp
  · rw [Pi.add_apply, hproj 1, path_one, initialState_one]
    simp only [rate_one]
    simp

/-- Every state along the optimization sequence is feasible. -/
public theorem path_feasible (t : ℝ) (ht : t ∈ Ici (0:ℝ)) :
    path t ∈ feasibleStates budget floor2 := by
  have hle : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by simpa using ht)
  have hpos : (0:ℝ) < Real.exp (-t) := Real.exp_pos _
  refine ⟨?_, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · show path t 0 + path t 1 - 1 ≤ 0
    rw [path_zero, path_one]
    linarith
  · show (0:ℝ) ≤ path t 0
    rw [path_zero]
    linarith
  · show (0:ℝ) ≤ path t 1
    rw [path_one]
    linarith

/-- The optimization sequence converges. -/
public theorem path_tendsto : Tendsto path atTop (𝓝 limitState) := by
  have hexp := Real.tendsto_exp_neg_atTop_nhds_zero
  refine tendsto_pi_nhds.mpr (Fin.forall_fin_two.mpr ⟨?_, ?_⟩)
  · have h := (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℝ))).sub hexp
    rw [sub_zero] at h
    simpa only [path_zero, limitState_zero] using h
  · simpa only [path_one, limitState_one] using hexp

private theorem proxy_path (t : ℝ) :
    proxyUtil (restrictAttrs proxyAttrs (path t)) = 1 - Real.exp (-t) := path_zero t

/-- The supremum of the proxy over the feasible states is `1`, and it is
attained, so print's Complete Optimization assumption is satisfiable here. -/
public theorem isLUB_proxy :
    IsLUB ((fun x => proxyUtil (restrictAttrs proxyAttrs x)) ''
      feasibleStates budget floor2) 1 := by
  constructor
  · rintro y ⟨x, ⟨hC, hb⟩, rfl⟩
    have h0 : (0:ℝ) ≤ x 0 := hb 0
    have h1 : (0:ℝ) ≤ x 1 := hb 1
    have hC' : x 0 + x 1 - 1 ≤ 0 := hC
    show x 0 ≤ 1
    linarith
  · intro u hu
    refine hu ⟨limitState, ⟨?_, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩, ?_⟩
    · show limitState 0 + limitState 1 - 1 ≤ 0
      rw [limitState_zero, limitState_one]
      norm_num
    · show (0:ℝ) ≤ limitState 0
      rw [limitState_zero]
      norm_num
    · exact le_of_eq limitState_one.symm
    · show limitState 0 = 1
      exact limitState_zero

/-- The robot completely optimizes: the proxy reaches its supremum in the
limit. -/
public theorem complete_optimization :
    limsup (fun t => proxyUtil (restrictAttrs proxyAttrs (path t))) atTop = 1 := by
  refine Filter.Tendsto.limsup_eq ?_
  have h := (tendsto_const_nhds (x := (1:ℝ)) (f := (atTop : Filter ℝ))).sub
    Real.tendsto_exp_neg_atTop_nhds_zero
  rw [sub_zero] at h
  simpa only [proxy_path] using h

/-- **The printed theorem, at a model that satisfies every one of its
hypotheses.** The unmentioned attribute ends at its floor. -/
public theorem unmentioned_at_floor : ∀ k ∉ proxyAttrs, limitState k = floor2 k :=
  zhuang_hadfield_menell_theorem_one budget continuous_budget strictMonoCoord_budget
    floor2 proxyAttrs ⟨0, rfl⟩ proxyUtil continuous_proxyUtil strictMonoCoord_proxyUtil
    initialState rate continuous_rate.continuousOn path path_eq_integral path_feasible
    1 isLUB_proxy complete_optimization limitState path_tendsto

/-- The conclusion is not true of where the sequence started: the unmentioned
attribute begins at `1` and is driven to `0`, so what the theorem concludes is a
constraint the optimization imposed rather than one the model started with. -/
public theorem initial_not_at_floor : initialState 1 ≠ floor2 1 := by
  rw [initialState_one]
  show (1:ℝ) ≠ 0
  norm_num

/-- **What the optimization cost, exactly.** The principal's utility falls from
`2` to `1`, strictly, and the gap between what the proxy reports and what the
principal gets rises from `-2` to `0`, strictly. Every number here is a
literal. -/
public theorem trueUtil_falls_and_gap_rises :
    trueUtil limitState < trueUtil initialState
      ∧ proxyUtil (restrictAttrs proxyAttrs initialState) - trueUtil initialState
          < proxyUtil (restrictAttrs proxyAttrs limitState) - trueUtil limitState := by
  constructor
  · show limitState 0 + 2 * limitState 1 < initialState 0 + 2 * initialState 1
    rw [limitState_zero, limitState_one, initialState_zero, initialState_one]
    norm_num
  · show initialState 0 - (initialState 0 + 2 * initialState 1)
        < limitState 0 - (limitState 0 + 2 * limitState 1)
    rw [limitState_zero, limitState_one, initialState_zero, initialState_one]
    norm_num

/-- The gap corollary at this model: the limit state has the largest proxy-goal
gap of any feasible state carrying its proxy attributes. -/
public theorem gap_maximal (s : Fin 2 → ℝ) (hs : s ∈ feasibleStates budget floor2)
    (hJ : ∀ j ∈ proxyAttrs, s j = limitState j) :
    proxyUtil (restrictAttrs proxyAttrs s) - trueUtil s
      ≤ proxyUtil (restrictAttrs proxyAttrs limitState) - trueUtil limitState :=
  gap_le_of_unmentioned_eq_lowerBound (C := budget) (Ut := proxyUtil)
    monotone_trueUtil unmentioned_at_floor hs hJ

/-! ## Why the nonemptiness hypothesis is load-bearing -/

/-- A proxy utility on no attributes at all, which is a constant. -/
@[expose] public def emptyProxyUtil : ((∅ : Set (Fin 2)) → ℝ) → ℝ := fun _ => 0

/-- **The scope note, inhabited.** At an empty proxy attribute set every
hypothesis of the core lemma except the nonemptiness of that set holds at the
initial state -- the constant proxy is vacuously strictly increasing in each of
its no attributes, and every feasible state maximizes it -- and yet the
unmentioned attribute is not at its floor. So the nonemptiness hypothesis that
the printed statement leaves implicit cannot be dropped. -/
public theorem empty_proxyAttrs_breaks_the_conclusion :
    StrictMonoCoord emptyProxyUtil
      ∧ initialState ∈ feasibleStates budget floor2
      ∧ (∀ s ∈ feasibleStates budget floor2,
          emptyProxyUtil (restrictAttrs (∅ : Set (Fin 2)) s)
            ≤ emptyProxyUtil (restrictAttrs (∅ : Set (Fin 2)) initialState))
      ∧ (1 : Fin 2) ∉ (∅ : Set (Fin 2))
      ∧ initialState 1 ≠ floor2 1 := by
  refine ⟨fun _ i _ => i.2.elim, ⟨?_, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩,
    fun _ _ => le_refl _, by simp, initial_not_at_floor⟩
  · show initialState 0 + initialState 1 - 1 ≤ 0
    rw [initialState_zero, initialState_one]
    norm_num
  · exact le_of_eq initialState_zero.symm
  · show (0:ℝ) ≤ initialState 1
    rw [initialState_one]
    norm_num

end AISafetyAtlas.Examples.Goodhart.Overoptimization
