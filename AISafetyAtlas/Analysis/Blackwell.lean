/-
Statements and proofs adapted from `danlyng/Econlib`
(https://github.com/danlyng/Econlib), file `Econlib/Math/Analysis/Blackwell.lean`
at commit `003655ccf010cdf44c4f67d6675167b54ce0e9df`, licensed Apache-2.0 with no
upstream `NOTICE`. The upstream file's SHA-256 is
`1879097686a79081481812eab72871a33ac01d635ef49369759a602b333f6c9d`.

Atlas changes: namespace `Blackwell` -> `AISafetyAtlas.Blackwell`; the two
closed-invariant-set lemmas moved out of Mathlib's `ContractingWith` namespace
into this one, so they are named rather than reached by dot notation, and the
contraction certificate is therefore an explicit first argument;
`@[expose] public section` replaced by per-declaration `public` and `@[expose]`,
because a section-scoped declaration is invisible to `scripts/check_public_api.py`
and to `scripts/check_print_axioms.py`; Lean v4.29.0 / Mathlib v4.29.0 ->
v4.33.0 (`db584cd6d46c92f209a44c0f1c829460d327499d`), which costs exactly one
lemma: `abs_sub` in the form `|a - b| ≤ |a| + |b|` does not resolve at our pin,
so `abs_sub_le_abs_add_abs` below restates it from `abs_add` and `abs_neg` and is
used at the two sites upstream used `abs_sub`. The mathematics is the upstream
author's. Repository-level notice: `AISafetyAtlas/Upstream/LICENSE-NOTICE`.
-/

module

public import Mathlib.Topology.ContinuousMap.Bounded.Normed
public import Mathlib.Topology.MetricSpace.Contracting

/-!
# Blackwell contraction and the bounded fixed-point core

An operator on plain functions `(S → ℝ) → S → ℝ` that is **monotone** and
satisfies **discounting** with factor `β` admits a pointwise sup-norm contraction
estimate. Bounded plain functions embed into `BoundedContinuousFunction` over `S`
with the *discrete* topology — complete under the sup norm — so the estimate
upgrades to a `ContractingWith` certificate for the lifted operator, and Banach
gives a named bounded fixed point with its equation and its uniqueness.

## Why this is here

`AISafetyAtlas.Decision.DiscountedValue` reaches its fixed points through
`ContractingWith` on `State → ℝ` under the sup metric, which is a metric space
only when `State` is finite. That `[Fintype State]` is the third of the three
gaps that module's header names, and this file is the widening: the fixed-point
layer below asks `[Nonempty S]` and a uniform bound, and **no topology on the
state type at all**. `DState` is a `def` rather than an `abbrev` for exactly that
reason — the synonym carries its own discrete topology without colliding with any
topology `S` may already have.

`existsUnique_bdd_fixedPoint` is stated for an arbitrary `T` with a
boundedness-preservation hypothesis rather than for a Bellman shape, so the
stochastic Bellman operator of `AISafetyAtlas.Decision.BoundedValue` plugs into it
unchanged.

## Main definitions

* `UniformBounded` — uniform boundedness of a real-valued function.
* `liftBddFun` — the operator lifted to the space of bounded continuous functions.
* `bddFixedPoint` — the bounded fixed point, returned as a plain function.

## Main statements

* `abs_sub_le_of_monotone_discounting` — Blackwell's theorem: monotonicity plus
  discounting imply the `β`-contraction estimate.
* `contractingWith_liftBddFun` — that estimate yields a Banach contraction
  certificate for the lifted operator.
* `existsUnique_bdd_fixedPoint` — existence and uniqueness of the bounded fixed
  point.
* `isFixedPt_mem_of_isClosed` — shape transfer to the fixed point via a closed
  invariant set.

## What this file does not claim

It is a fixed-point core, not a dynamic-programming layer: it names no MDP, no
reward and no policy, and it states no relationship between a fixed point and a
discounted return. The `Optimization/DynamicProgramming/` subtree of the same
upstream repository was **declined** rather than ported, and the reasons are in
`docs/agent/policy/lean-reuse-sources.md`.

## References

* Stokey, Nancy L., Robert E. Lucas, and Edward C. Prescott. 1989. *Recursive
  Methods in Economic Dynamics*. Harvard University Press. Corollary 1 to
  Theorem 3.2.
-/

namespace AISafetyAtlas.Blackwell

universe u

variable {S : Type u}

/-! ## The one lemma the toolchain move costs

Upstream reaches |a - b| ≤ |a| + |b| through a Mathlib name that does not resolve
at `db584cd6…`, and uses it twice. The two Mathlib names that survive under
similar spellings are different statements. This is the same fact, restated. -/

private theorem abs_sub_le_abs_add_abs (a b : ℝ) : |a - b| ≤ |a| + |b| := by
  rw [sub_eq_add_neg]
  exact (abs_add_le a (-b)).trans_eq (by rw [abs_neg])

/-! ## Closed invariant set principle

Stated for an arbitrary contraction on a complete metric space; the layer below
specializes it to lifted operators on `BddFun`. -/

/-- **Closed Invariant Set Principle.** Let `f` be a contraction on a complete
metric space. If `C` is a nonempty closed subset with `f(C) ⊆ C`, then the unique
fixed point lies in `C`. -/
public theorem fixedPoint_mem_of_isClosed
    {α : Type*} [MetricSpace α] [Nonempty α] [CompleteSpace α]
    {K : NNReal} {f : α → α} (hf : ContractingWith K f)
    {C : Set α} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_inv : Set.MapsTo f C C) :
    hf.fixedPoint f ∈ C := by
  obtain ⟨x₀, hx₀⟩ := hC_nonempty
  have hiter : ∀ n, f^[n] x₀ ∈ C := by
    intro n; induction n with
    | zero => exact hx₀
    | succ n ih => rw [Function.iterate_succ_apply']; exact hC_inv ih
  have htend := hf.tendsto_iterate_fixedPoint x₀
  exact hC_closed.mem_of_tendsto htend (Filter.Eventually.of_forall hiter)

/-- If `C` is closed and `f`-invariant, then **every** fixed point of `f` lies in
`C`. -/
public theorem isFixedPt_mem_of_isClosed'
    {α : Type*} [MetricSpace α] [Nonempty α] [CompleteSpace α]
    {K : NNReal} {f : α → α} (hf : ContractingWith K f)
    {C : Set α} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_inv : Set.MapsTo f C C)
    {x : α} (hx : Function.IsFixedPt f x) :
    x ∈ C := by
  rw [hf.fixedPoint_unique hx]
  exact fixedPoint_mem_of_isClosed hf hC_nonempty hC_closed hC_inv

/-! ## Blackwell's sufficient conditions

Stated for operators on plain functions `(S → ℝ) → S → ℝ`, with boundedness
carried as an explicit `UniformBounded` side condition. -/

/-- Uniform boundedness of a real-valued function: a single bound `B` with
`|v s| ≤ B` across all of `S`. Definitionally the bare existential, so
`obtain ⟨B, hB⟩ := hv` destructures it directly. -/
@[expose] public def UniformBounded (v : S → ℝ) : Prop :=
  ∃ B : ℝ, ∀ s, |v s| ≤ B

/-- The pointwise distance of two bounded functions is bounded above over the
state space. -/
public theorem bddAbove_range_abs_sub (v w : S → ℝ)
    (hBv : UniformBounded v) (hBw : UniformBounded w) :
    BddAbove (Set.range fun s => |v s - w s|) := by
  obtain ⟨Bv, hBv⟩ := hBv; obtain ⟨Bw, hBw⟩ := hBw
  exact ⟨Bv + Bw, Set.forall_mem_range.mpr fun s =>
    (abs_sub_le_abs_add_abs (v s) (w s)).trans (add_le_add (hBv s) (hBw s))⟩

/-- **Blackwell's theorem.** An operator on plain functions that is monotone and
satisfies the discounting property with factor `β` admits the pointwise
`β`-contraction estimate in the sup norm.

Both conditions are required only on bounded inputs, matching how Bellman
operators provide them: monotonicity `v ≤ w → Tv ≤ Tw`, and discounting
`T(v + c) ≤ Tv + βc` for constants `c ≥ 0`. No sign condition on `β` is needed:
nonnegativity enters only through the discounting hypothesis. -/
public theorem abs_sub_le_of_monotone_discounting
    {T : (S → ℝ) → S → ℝ} {β : ℝ}
    (h_mono : ∀ v w : S → ℝ, UniformBounded v → UniformBounded w →
      (∀ s, v s ≤ w s) → ∀ s, T v s ≤ T w s)
    (h_disc : ∀ (v : S → ℝ) (c : ℝ), UniformBounded v → 0 ≤ c →
      ∀ s, T (fun s' => v s' + c) s ≤ T v s + β * c)
    {v w : S → ℝ} (hv : UniformBounded v) (hw : UniformBounded w) (s : S) :
    |T v s - T w s| ≤ β * ⨆ t, |v t - w t| := by
  -- One-sided bound, symmetric in its two arguments: `a ≤ b + ⨆|a - b|` pointwise,
  -- so monotonicity + discounting give `T a s ≤ T b s + β * ⨆|a - b|`. Both halves
  -- of the `abs_le` split below are this bound with the roles of `v`, `w` swapped.
  have one_sided : ∀ a b : S → ℝ, (∃ B : ℝ, ∀ s, |a s| ≤ B) → (∃ B : ℝ, ∀ s, |b s| ≤ B) →
      T a s - T b s ≤ β * ⨆ t, |a t - b t| := by
    intro a b ha hb
    have hbdd := bddAbove_range_abs_sub a b ha hb
    set d := ⨆ t, |a t - b t| with hd_def
    have hd_nonneg : 0 ≤ d := (abs_nonneg _).trans (le_ciSup hbdd s)
    have hle : ∀ t, a t ≤ b t + d := fun t =>
      le_add_of_sub_left_le ((le_abs_self _).trans (le_ciSup hbdd t))
    have hb_add : ∃ B : ℝ, ∀ t, |b t + d| ≤ B := by
      obtain ⟨Bb, hBb⟩ := hb
      exact ⟨Bb + |d|, fun t =>
        (abs_add_le _ _).trans (add_le_add (hBb t) le_rfl)⟩
    have h1 : T a s ≤ T (fun t => b t + d) s := h_mono a _ ha hb_add hle s
    have h2 := h_disc b d hb hd_nonneg s
    linarith
  have hsup_comm : (⨆ t, |w t - v t|) = ⨆ t, |v t - w t| := by simp_rw [abs_sub_comm]
  rw [abs_le]
  refine ⟨?_, one_sided v w hv hw⟩
  have h := one_sided w v hw hv
  rw [hsup_comm] at h
  linarith

/-! ## The bounded-continuous-function bridge

Bounded plain functions `S → ℝ` embed into `BoundedContinuousFunction` over `S`
equipped with the discrete topology — a complete metric space under the sup norm
— so Banach's fixed-point theorem applies to lifted operators. -/

/-- Type alias for `S` with the discrete topology, so every function
`DState → ℝ` is continuous. This embeds bounded `S → ℝ` into
`BoundedContinuousFunction DState ℝ`, complete under the sup norm.

Defined via `def` (not `abbrev`) so that `DState` gets its own topology instance
without conflicting with any existing topology on `S`. -/
@[expose] public def DState : Type u := S

public noncomputable instance instTopDState : TopologicalSpace (@DState S) := ⊥
public instance instDiscDState : DiscreteTopology (@DState S) := ⟨rfl⟩
public instance instNonemptyDState [Nonempty S] : Nonempty (@DState S) :=
  ⟨(Classical.arbitrary S : S)⟩

/-- Bounded continuous functions from `DState` to `ℝ` — that is, bounded functions
`S → ℝ`, continuity being automatic from the discrete topology. -/
public abbrev BddFun := BoundedContinuousFunction (@DState S) ℝ

/-- Embed a bounded function `S → ℝ` into the bounded-continuous-function space. -/
@[expose] public noncomputable def toBddFun (f : S → ℝ) (hf : UniformBounded f) :
    BoundedContinuousFunction (@DState S) ℝ :=
  BoundedContinuousFunction.mkOfDiscrete (α := @DState S) (β := ℝ) f (2 * Exists.choose hf)
    (fun x y => by
      simp only [Real.dist_eq]
      calc |f x - f y| ≤ |f x| + |f y| := abs_sub_le_abs_add_abs (f x) (f y)
        _ ≤ 2 * Exists.choose hf := by
            linarith [Exists.choose_spec hf x, Exists.choose_spec hf y])

/-- The embedding coerces back to the original function. -/
public theorem toBddFun_coe (f : S → ℝ) (hf : UniformBounded f) :
    (toBddFun f hf : DState → ℝ) = f := by
  ext x; exact BoundedContinuousFunction.mkOfDiscrete_apply _ _ _ _

/-- The embedding agrees with the original function pointwise. -/
public theorem toBddFun_apply (f : S → ℝ) (hf : UniformBounded f) (x : DState) :
    toBddFun f hf x = f x :=
  BoundedContinuousFunction.mkOfDiscrete_apply _ _ _ _

/-- Every bounded continuous function on `DState` is uniformly bounded as a plain
function. -/
public theorem bddFun_bounded (f : @BddFun S) : ∃ B : ℝ, ∀ s : S, |(f : DState → ℝ) s| ≤ B :=
  ⟨‖f‖, fun s => by
    have := BoundedContinuousFunction.norm_coe_le_norm f (s : DState)
    rwa [Real.norm_eq_abs] at this⟩

variable {T : (S → ℝ) → S → ℝ}

/-- Lift an operator on plain functions to the bounded-continuous-function space,
given that it maps bounded functions to bounded functions. -/
@[expose] public noncomputable def liftBddFun (T : (S → ℝ) → S → ℝ)
    (h_maps : ∀ v : S → ℝ, UniformBounded v → UniformBounded (T v)) :
    @BddFun S → @BddFun S :=
  fun f => toBddFun (T f) (h_maps f (bddFun_bounded f))

variable {h_maps : ∀ v : S → ℝ, UniformBounded v → UniformBounded (T v)}

/-- The lifted operator agrees with `T` pointwise. -/
public theorem liftBddFun_apply (f : @BddFun S) (s : DState) :
    liftBddFun T h_maps f s = T f s :=
  toBddFun_apply _ _ _

/-- A pointwise sup-norm contraction estimate on bounded plain functions upgrades
to a Banach contraction certificate for the lifted operator. -/
public theorem contractingWith_liftBddFun [Nonempty S] {β : ℝ} (hβ₀ : 0 ≤ β) (hβ₁ : β < 1)
    (h_contr : ∀ v w : S → ℝ, UniformBounded v → UniformBounded w →
      ∀ s, |T v s - T w s| ≤ β * ⨆ t, |v t - w t|) :
    ContractingWith ⟨β, hβ₀⟩ (liftBddFun T h_maps) := by
  refine ⟨by exact_mod_cast hβ₁, LipschitzWith.of_dist_le_mul fun f g => ?_⟩
  -- Upstream rewrote with `NNReal.coe_mk` here. At our pin the coercion of
  -- `⟨β, hβ₀⟩` is already `β` by `rfl` and the rewrite finds no pattern, so the
  -- cast is discharged by `show` instead.
  show dist (liftBddFun T h_maps f) (liftBddFun T h_maps g) ≤ β * dist f g
  rw [BoundedContinuousFunction.dist_le (mul_nonneg hβ₀ dist_nonneg)]
  intro s
  rw [Real.dist_eq, liftBddFun_apply, liftBddFun_apply]
  calc |T f s - T g s|
      ≤ β * ⨆ t, |(f : DState → ℝ) t - g t| :=
        h_contr f g (bddFun_bounded f) (bddFun_bounded g) s
    _ ≤ β * dist f g := by
        refine mul_le_mul_of_nonneg_left (ciSup_le fun t => ?_) hβ₀
        have := BoundedContinuousFunction.dist_coe_le_dist (f := f) (g := g) t
        rwa [Real.dist_eq] at this

/-! ## The bounded fixed point and its lemma suite -/

section FixedPoint

variable {K : NNReal}

/-- The unique bounded fixed point of an operator with a Banach contraction
certificate on the lifted space, returned as a plain function `S → ℝ`. -/
@[expose] public noncomputable def bddFixedPoint (hc : ContractingWith K (liftBddFun T h_maps)) :
    S → ℝ :=
  ⇑(hc.fixedPoint (liftBddFun T h_maps))

/-- The bounded fixed point is uniformly bounded. -/
public theorem bddFixedPoint_bounded (hc : ContractingWith K (liftBddFun T h_maps)) :
    UniformBounded (bddFixedPoint hc) :=
  bddFun_bounded _

/-- The bounded fixed point satisfies the fixed-point equation pointwise. -/
public theorem bddFixedPoint_isFixedPt (hc : ContractingWith K (liftBddFun T h_maps)) (s : S) :
    bddFixedPoint hc s = T (bddFixedPoint hc) s := by
  have hfp : liftBddFun T h_maps (hc.fixedPoint _) = hc.fixedPoint _ :=
    hc.fixedPoint_isFixedPt
  -- The lifted operator agrees with `T` on coercions definitionally.
  exact (congr_fun (congr_arg DFunLike.coe hfp) s).symm

/-- Bounded fixed points of `T` lift to fixed points of the lifted operator. -/
public theorem isFixedPt_liftBddFun {v : S → ℝ} (hv_bdd : UniformBounded v)
    (hv_fp : ∀ s, v s = T v s) :
    Function.IsFixedPt (liftBddFun T h_maps) (toBddFun v hv_bdd) := by
  change liftBddFun T h_maps (toBddFun v hv_bdd) = toBddFun v hv_bdd
  ext s
  exact (hv_fp s).symm

/-- **Uniqueness.** Any bounded fixed point of `T` equals `bddFixedPoint`. -/
public theorem eq_bddFixedPoint (hc : ContractingWith K (liftBddFun T h_maps)) {v : S → ℝ}
    (hv_bdd : UniformBounded v) (hv_fp : ∀ s, v s = T v s) :
    v = bddFixedPoint hc := by
  have heq : hc.fixedPoint (liftBddFun T h_maps) = toBddFun v hv_bdd :=
    hc.fixedPoint_unique' hc.fixedPoint_isFixedPt (isFixedPt_liftBddFun hv_bdd hv_fp)
  have h : v = ⇑(hc.fixedPoint (liftBddFun T h_maps)) := by
    rw [heq]; exact (toBddFun_coe v hv_bdd).symm
  exact h

/-- Existence and uniqueness of the bounded fixed point, packaged as `∃!`. -/
public theorem existsUnique_bdd_fixedPoint (hc : ContractingWith K (liftBddFun T h_maps)) :
    ∃! v : S → ℝ, UniformBounded v ∧ ∀ s, v s = T v s :=
  ⟨bddFixedPoint hc, ⟨bddFixedPoint_bounded hc, bddFixedPoint_isFixedPt hc⟩,
    fun _ ⟨hv_bdd, hv_fp⟩ => eq_bddFixedPoint hc hv_bdd hv_fp⟩

/-- **Shape transfer.** If `C ⊆ BddFun` is nonempty, closed, and invariant under
the lifted operator, then every bounded fixed point of `T` lies in `C`. This is
how shape properties (concavity, monotonicity, decreasing differences, …)
transfer to value functions. -/
public theorem isFixedPt_mem_of_isClosed (hc : ContractingWith K (liftBddFun T h_maps))
    {C : Set (@BddFun S)} (hC_nonempty : C.Nonempty) (hC_closed : IsClosed C)
    (hC_inv : Set.MapsTo (liftBddFun T h_maps) C C)
    {v : S → ℝ} (hv_bdd : UniformBounded v) (hv_fp : ∀ s, v s = T v s) :
    toBddFun v hv_bdd ∈ C :=
  isFixedPt_mem_of_isClosed' hc hC_nonempty hC_closed hC_inv
    (isFixedPt_liftBddFun hv_bdd hv_fp)

end FixedPoint

end AISafetyAtlas.Blackwell
