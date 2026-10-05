module

public import AISafetyAtlas.Decision.DiscountedValue
public import AISafetyAtlas.Analysis.Blackwell

/-!
# The discounted policy value on an arbitrary state type

`AISafetyAtlas.Decision.DiscountedValue` reaches `vPi` through `ContractingWith`
on `State → ℝ` under the sup metric, and that is a metric space only when
`State` is a `Fintype`. Gap 3 of that module's header is exactly this
restriction. **This module closes it**, at the price the costing named: a
`Nonempty` state type and a uniform bound on the reward, in place of finiteness.

## What is new and what is shared

Nothing here restates a Bellman operator. `qVal` and `bellmanPolicyOp` lost
their `[Fintype State]` binders in the same change that added this module —
neither definition ever used finiteness, only the *fixed point* did — so the
operator below **is** the operator there, and the two developments differ only in
which completeness argument they run on it.

* `bellmanPolicyOp_mono` and `bellmanPolicyOp_discounting` are Blackwell's two
  sufficient conditions, discharged for the stochastic Bellman operator.
* `vPiBdd` is the bounded fixed point, through
  `AISafetyAtlas.Blackwell.bddFixedPoint`.
* `vPiBdd_bellman` and `vPiBdd_unique` are its equation and its uniqueness —
  uniqueness now **among bounded solutions**, which is where the finiteness went.
* `vPiBdd_eq_vPi` is the join: on a finite nonempty state type the two value
  functions are the same function. Without it this module would be a parallel
  development rather than a widening, and the claim that it widens anything would
  rest on the reader.

## What it does not close

The other two gaps of `AISafetyAtlas.Decision.DiscountedValue` are untouched and
no external tree bears on them: `vPi` is still a *stationary deterministic*
policy's value rather than the carrier's history-dependent stochastic `Policy`,
and it is still *defined* as a fixed point rather than proved equal to the
discounted return along `AISafetyAtlas.Decision.MDP.run`.

There is no bounded counterpart of `vStar`. The optimality operator maximises
over actions with
`Finset.sup'`, so widening it is a statement about suprema over a possibly
infinite action set — a different change, and one this module does not make.

## Provenance

The fixed-point core is `AISafetyAtlas.Analysis.Blackwell`, adapted from
`danlyng/Econlib`; the costing that chose it over that repository's
`Optimization/DynamicProgramming/` subtree is in
`docs/agent/policy/lean-reuse-sources.md`.
-/

namespace AISafetyAtlas.Decision

open scoped NNReal

universe u v

variable {State : Type u} {Action : Type v}

/-! ## A bounded integrand has a bounded expectation

`AISafetyAtlas.Decision.Expect` carries the two one-sided bounds; Blackwell's
`UniformBounded` wants them together. -/

/-- The expectation of a function bounded by `B` is bounded by `B`. -/
public theorem abs_expect_le (p : PMF State) {f : State → ℝ} {B : ℝ}
    (hf : ∀ s, |f s| ≤ B) : |expect p f| ≤ B :=
  abs_le.mpr ⟨le_expect p hf (-B) fun s => neg_le_of_abs_le (hf s),
    expect_le p hf B fun s => le_of_abs_le (hf s)⟩

/-! ## Blackwell's two conditions for the policy Bellman operator -/

/-- **The policy Bellman operator maps bounded value functions to bounded value
functions**, which is what lifting it to the bounded-continuous-function space
requires. The bound is print's own: reward plus discounted continuation. -/
public theorem bellmanPolicyOp_uniformBounded (M : MDP State Action)
    (r : State → Action → ℝ) (γ : ℝ≥0) (π : State → Action) {R : ℝ}
    (hr : ∀ s, |r s (π s)| ≤ R) (v : State → ℝ)
    (hv : Blackwell.UniformBounded v) :
    Blackwell.UniformBounded (bellmanPolicyOp M r γ π v) := by
  obtain ⟨B, hB⟩ := hv
  refine ⟨R + (γ : ℝ) * |B|, fun s => ?_⟩
  have hexp : |expect (M.transition s (π s)) v| ≤ |B| :=
    abs_expect_le _ fun t => (hB t).trans (le_abs_self B)
  calc |bellmanPolicyOp M r γ π v s|
      = |r s (π s) + (γ : ℝ) * expect (M.transition s (π s)) v| := rfl
    _ ≤ |r s (π s)| + |(γ : ℝ) * expect (M.transition s (π s)) v| := abs_add_le _ _
    _ ≤ R + (γ : ℝ) * |B| := by
        refine add_le_add (hr s) ?_
        rw [abs_mul, abs_of_nonneg γ.coe_nonneg]
        exact mul_le_mul_of_nonneg_left hexp γ.coe_nonneg

/-- **Monotonicity**, the first of Blackwell's two conditions: a pointwise larger
value function has a pointwise larger Bellman image. -/
public theorem bellmanPolicyOp_mono (M : MDP State Action)
    (r : State → Action → ℝ) (γ : ℝ≥0) (π : State → Action)
    (v w : State → ℝ) (hv : Blackwell.UniformBounded v)
    (hw : Blackwell.UniformBounded w) (hvw : ∀ s, v s ≤ w s) (s : State) :
    bellmanPolicyOp M r γ π v s ≤ bellmanPolicyOp M r γ π w s := by
  obtain ⟨Bv, hBv⟩ := hv
  obtain ⟨Bw, hBw⟩ := hw
  have hv' : ∀ t, |v t| ≤ max Bv Bw := fun t => (hBv t).trans (le_max_left _ _)
  have hw' : ∀ t, |w t| ≤ max Bv Bw := fun t => (hBw t).trans (le_max_right _ _)
  have h := mul_le_mul_of_nonneg_left
    (expect_mono (M.transition s (π s)) hv' hw' hvw) γ.coe_nonneg
  simp only [bellmanPolicyOp, qVal]
  linarith

/-- **Discounting**, the second condition: adding a constant to the value function
adds at most `γ` times that constant to the Bellman image. Here it is an
equality — the expectation of a shifted integrand shifts by the same constant,
because the mass is one — and only the inequality is needed downstream. -/
public theorem bellmanPolicyOp_discounting (M : MDP State Action)
    (r : State → Action → ℝ) (γ : ℝ≥0) (π : State → Action)
    (v : State → ℝ) (c : ℝ) (hv : Blackwell.UniformBounded v) (_hc : 0 ≤ c)
    (s : State) :
    bellmanPolicyOp M r γ π (fun s' => v s' + c) s
      ≤ bellmanPolicyOp M r γ π v s + (γ : ℝ) * c := by
  obtain ⟨B, hB⟩ := hv
  have hshift : expect (M.transition s (π s)) (fun s' => v s' + c)
      = expect (M.transition s (π s)) v + c := expect_add_const _ hB c
  simp only [bellmanPolicyOp, qVal, hshift]
  ring_nf
  exact le_refl _

/-- **The contraction certificate on the lifted operator.** Blackwell's theorem
applied to the two conditions above, then transported to the bounded-continuous
function space, which is complete under the sup norm with no finiteness on
`State`. -/
public theorem bellmanPolicyOp_contractingWith_bdd [Nonempty State]
    (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    (π : State → Action) {R : ℝ} (hr : ∀ s, |r s (π s)| ≤ R) :
    ContractingWith ⟨(γ : ℝ), γ.coe_nonneg⟩
      (Blackwell.liftBddFun (bellmanPolicyOp M r γ π)
        (bellmanPolicyOp_uniformBounded M r γ π hr)) :=
  Blackwell.contractingWith_liftBddFun γ.coe_nonneg (by exact_mod_cast hγ)
    (fun v w hv hw s =>
      Blackwell.abs_sub_le_of_monotone_discounting
        (fun a b ha hb hab => bellmanPolicyOp_mono M r γ π a b ha hb hab)
        (fun a c ha hc => bellmanPolicyOp_discounting M r γ π a c ha hc)
        hv hw s)

/-! ## The value function -/

/--
**The value of a stationary deterministic policy on an arbitrary nonempty state
type**, as the bounded fixed point of its Bellman operator.

The reward bound `hr` is not decoration: uniqueness below is uniqueness *among
bounded* solutions, and on an infinite state type an unbounded solution of the
same equation may exist. Read the scope note in
`AISafetyAtlas.Decision.DiscountedValue` before using this — it is still a fixed
point, and no theorem identifies it with a discounted return along
`AISafetyAtlas.Decision.MDP.run`.
-/
@[expose] public noncomputable def vPiBdd [Nonempty State] (M : MDP State Action)
    (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1) (π : State → Action)
    {R : ℝ} (hr : ∀ s, |r s (π s)| ≤ R) : State → ℝ :=
  Blackwell.bddFixedPoint (bellmanPolicyOp_contractingWith_bdd M r hγ π hr)

/-- `vPiBdd` is uniformly bounded. -/
public theorem vPiBdd_bounded [Nonempty State] (M : MDP State Action)
    (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1) (π : State → Action)
    {R : ℝ} (hr : ∀ s, |r s (π s)| ≤ R) :
    Blackwell.UniformBounded (vPiBdd M r hγ π hr) :=
  Blackwell.bddFixedPoint_bounded _

/-- **The policy Bellman equation, pointwise**, with no finiteness on the state
type: the value at a state is the reward the policy earns there plus the
discounted expected value of the successor. -/
public theorem vPiBdd_bellman [Nonempty State] (M : MDP State Action)
    (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1) (π : State → Action)
    {R : ℝ} (hr : ∀ s, |r s (π s)| ≤ R) (s : State) :
    vPiBdd M r hγ π hr s
      = r s (π s) + (γ : ℝ) * expect (M.transition s (π s)) (vPiBdd M r hγ π hr) :=
  Blackwell.bddFixedPoint_isFixedPt _ s

/-- **Uniqueness among bounded solutions.** Any uniformly bounded solution of the
policy Bellman equation is `vPiBdd`.

This is weaker than `AISafetyAtlas.Decision.vPi_unique`, and the boundedness is
exactly what finiteness was buying there: on a finite state type every value
function is bounded, so the hypothesis is free and the two statements coincide —
which is what `vPiBdd_eq_vPi` below records. -/
public theorem vPiBdd_unique [Nonempty State] (M : MDP State Action)
    (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1) (π : State → Action)
    {R : ℝ} (hr : ∀ s, |r s (π s)| ≤ R) {v : State → ℝ}
    (hv_bdd : Blackwell.UniformBounded v)
    (hv_fp : ∀ s, v s = bellmanPolicyOp M r γ π v s) :
    v = vPiBdd M r hγ π hr :=
  Blackwell.eq_bddFixedPoint _ hv_bdd hv_fp

/-! ## The join with the finite development

Without the theorem below the two fixed points would be two objects with similar
names. It is the same statement `AISafetyAtlas.Wireheading.CRMDP` makes about its
three renderings of Theorem 11: these are the same numbers. -/

/-- On a finite state type every value function is uniformly bounded, so the
side condition `vPiBdd` carries is free there. -/
public theorem uniformBounded_of_fintype [Fintype State] (v : State → ℝ) :
    Blackwell.UniformBounded v := by
  obtain ⟨B, hB⟩ := (Set.finite_range fun s => |v s|).bddAbove
  exact ⟨B, fun s => hB (Set.mem_range_self s)⟩

/-- **The join.** On a finite nonempty state type the bounded fixed point is the
Banach fixed point of `AISafetyAtlas.Decision.DiscountedValue`: this module
widens that development rather than running beside it. -/
public theorem vPiBdd_eq_vPi [Fintype State] [Nonempty State]
    (M : MDP State Action) (r : State → Action → ℝ) {γ : ℝ≥0} (hγ : γ < 1)
    (π : State → Action) {R : ℝ} (hr : ∀ s, |r s (π s)| ≤ R) :
    vPiBdd M r hγ π hr = vPi M r hγ π :=
  (vPiBdd_unique M r hγ π hr (uniformBounded_of_fintype _)
    (fun s => (congr_fun (vPi_isFixedPt M r hγ π) s).symm)).symm

end AISafetyAtlas.Decision
