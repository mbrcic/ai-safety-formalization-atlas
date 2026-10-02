module

public import Mathlib.Probability.ProbabilityMassFunction.Monad
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# The expectation of a real function under a probability mass function

**This module is the atlas's one expectation against a `PMF`, as of 2026-09-10.**
Until then it was the fourth statement of the same function, which is the
opposite of what its first header claimed, and the history is worth keeping
because the mechanism that hid it is still in place.

Three developments wrote `∑' a, (p a).toReal * f a` independently:

* `AISafetyAtlas.Causal.Query` wrote it first, as pmfExpect, for the analyst's
  randomization over queries and models -- types that carry no σ-algebra;
* `AISafetyAtlas.Wireheading.StochasticCRMDP` wrote it for the expected reward
  under a state distribution, because a corrupt-reward MDP has no finiteness to
  spend;
* `AISafetyAtlas.Decision.DiscountedValue` wrote it for the expected continuation
  value, as a `Finset.sum` under `[Fintype State]`, because the contraction
  argument fixes a finite state space anyway.

The second and third were merged here on 2026-09-10; the first was on `main` the
whole time, with the **wider** API -- its summability lemma takes an arbitrary
bound `|f a| ≤ C` where the merged one was fixed to `[0, 1]` -- and neither the
merge nor `report_predicate_duplicates.py` could see it. That script scans
predicates, and this is a real-valued `def`. So the duplicate was structurally
invisible to the only tool that looks for duplicates.

All of it now lives here. `AISafetyAtlas.Causal.Query` imports this module and
pmfExpect is gone; the `C`-bounded toolkit moved across unchanged apart from
its names.

## The definition, and what it is not

`expect` is total: `∑'` is zero off summability, so the definition needs no side
condition and the lemmas that need convergence take it as a hypothesis. On a
`Fintype` it is the `Finset` sum, by `tsum_fintype`.

**Mathlib is above this module and the bridge is proved here rather than
asserted.** `expect_eq_integral` identifies it with `∫ · ∂p.toMeasure`, through
Mathlib's own `integral_eq_tsum`. The reason `expect` is not *defined* that way
is the reason `AISafetyAtlas.Causal.Query` gave for writing a `tsum` in the first
place: the integral needs `[MeasurableSpace]` and `[MeasurableSingletonClass]`
on the state type, and an `Integrable` side condition, none of which the
consumers here have or want -- a `PMF α` is a subtype of `α → ℝ≥0∞` for an
arbitrary `α`. Where those instances *are* available the bridge hands over the
whole Bochner API, and that is the intended route for anything beyond the
toolkit below.
-/

namespace AISafetyAtlas.Decision

universe u

variable {State : Type u}

/-! ## The probabilities themselves -/

/-- A probability mass function is summable after `ENNReal.toReal`, because its
total mass is one and so no value is `⊤`. -/
public theorem summable_prob (p : PMF State) : Summable fun s => (p s).toReal :=
  ENNReal.summable_toReal (by rw [p.tsum_coe]; exact ENNReal.one_ne_top)

/-- And they sum to one. -/
public theorem tsum_prob (p : PMF State) : ∑' s, (p s).toReal = 1 := by
  rw [← ENNReal.tsum_toReal_eq fun s => PMF.apply_ne_top p s, p.tsum_coe,
    ENNReal.toReal_one]

/-- The two facts above in the form a `Summable.mul_right` consumes. -/
public theorem hasSum_prob (p : PMF State) : HasSum (fun s => (p s).toReal) 1 := by
  simpa [tsum_prob p] using (summable_prob p).hasSum

/-! ## The expectation -/

/-- **The expectation of `f` under `p`.** Written as a `tsum`, so it needs no
finiteness and no measurable structure on `State`. -/
@[expose] public noncomputable def expect (p : PMF State) (f : State → ℝ) : ℝ :=
  ∑' s, (p s).toReal * f s

/-- A bounded non-negative integrand is summable against a probability mass
function, by comparison with the probabilities. -/
public theorem summable_of_bounded (p : PMF State) (f : State → ℝ)
    (hnonneg : ∀ s, 0 ≤ f s) (hle : ∀ s, f s ≤ 1) :
    Summable fun s => (p s).toReal * f s := by
  refine Summable.of_nonneg_of_le (fun s => ?_) (fun s => ?_) (summable_prob p)
  · exact mul_nonneg ENNReal.toReal_nonneg (hnonneg s)
  · calc (p s).toReal * f s
        ≤ (p s).toReal * 1 := mul_le_mul_of_nonneg_left (hle s) ENNReal.toReal_nonneg
      _ = (p s).toReal := mul_one _

/-- **The general summability hypothesis**, at an arbitrary two-sided bound.
This is the summability lemma `AISafetyAtlas.Causal.Query` carried, and it is strictly
wider than `summable_of_bounded` above: no sign condition, and the bound is a
parameter rather than `1`. -/
public theorem summable_of_abs_le (p : PMF State) {f : State → ℝ} {C : ℝ}
    (hf : ∀ s, |f s| ≤ C) : Summable fun s => (p s).toReal * f s := by
  refine Summable.of_norm_bounded ((hasSum_prob p).summable.mul_right C) fun s => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  exact mul_le_mul_of_nonneg_left (hf s) ENNReal.toReal_nonneg

/-- **On a finite state type the expectation is the finite sum.** This is the
bridge that lets `AISafetyAtlas.Decision.DiscountedValue`'s finite-sum
development and `AISafetyAtlas.Wireheading.StochasticCRMDP`'s `tsum` development
be the same function. -/
public theorem expect_eq_sum [Fintype State] (p : PMF State) (f : State → ℝ) :
    expect p f = ∑ s, (p s).toReal * f s :=
  tsum_fintype _

/-- **The expectation is affine in a mixture.** Averaging the distribution
averages the expectation, which is what makes a value affine in whatever draws
its distribution. -/
public theorem expect_bind {α : Type*} [Fintype α] [Fintype State]
    (p : PMF α) (q : α → PMF State) (f : State → ℝ) :
    expect (p.bind q) f = ∑ a, (p a).toReal * expect (q a) f := by
  classical
  rw [expect_eq_sum]
  have hterm : ∀ s : State, ((p.bind q) s).toReal * f s
      = ∑ a, (p a).toReal * (q a s).toReal * f s := by
    intro s
    rw [PMF.bind_apply, tsum_fintype,
      ENNReal.toReal_sum (fun a _ =>
        ENNReal.mul_ne_top (PMF.apply_ne_top p a) (PMF.apply_ne_top (q a) s)),
      Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [ENNReal.toReal_mul]
  rw [Finset.sum_congr rfl fun s _ => hterm s, Finset.sum_comm]
  exact Finset.sum_congr rfl fun a _ => by
    rw [expect_eq_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring

/-- **The bridge to Mathlib's integral.** Where the state type carries the
measurable structure and the integrand is integrable, this expectation *is* the
Bochner integral against `PMF.toMeasure`, and everything Mathlib proves about
that integral applies. Proved through Mathlib's own `integral_eq_tsum`; the
`•` there is multiplication on `ℝ`. -/
public theorem expect_eq_integral [MeasurableSpace State] [MeasurableSingletonClass State]
    (p : PMF State) (f : State → ℝ) (hf : MeasureTheory.Integrable f p.toMeasure) :
    expect p f = ∫ s, f s ∂(p.toMeasure) := by
  rw [expect, PMF.integral_eq_tsum p f hf]
  exact tsum_congr fun s => (smul_eq_mul _ _).symm

/-! ## The toolkit

`expect` is a `tsum` in `ℝ`, so monotonicity is not free the way it would be in
`ℝ≥0∞`: `tsum_le_tsum` wants summability on both sides. Every function pushed
through it in this repository is bounded, so these lemmas take an explicit bound
rather than trying to be general. They came from
`AISafetyAtlas.Causal.Query` unchanged. -/

/-- At a point mass the expectation is the value there. -/
@[simp] public theorem expect_pure (a : State) (f : State → ℝ) :
    expect (PMF.pure a) f = f a := by
  classical
  rw [expect]
  have h : ∀ s, ((PMF.pure a) s).toReal * f s = if s = a then f s else 0 := by
    intro s
    by_cases hs : s = a
    · subst hs; simp
    · simp [PMF.pure_apply, hs]
  rw [tsum_congr h, tsum_ite_eq]

/-- A constant integrand comes out of the expectation, because the mass is one. -/
@[simp] public theorem expect_const (p : PMF State) (c : ℝ) :
    expect p (fun _ => c) = c := by
  rw [expect, tsum_mul_right, tsum_prob, one_mul]

/-- The expectation is additive in the integrand, given summability of each part. -/
public theorem expect_add (p : PMF State) (f g : State → ℝ)
    (hf : Summable fun s => (p s).toReal * f s)
    (hg : Summable fun s => (p s).toReal * g s) :
    expect p (fun s => f s + g s) = expect p f + expect p g := by
  rw [expect, expect, expect, ← hf.tsum_add hg]
  exact tsum_congr fun s => by ring

/-- Additivity at a two-sided bound, which is the form a bounded consumer has to
hand. -/
public theorem expect_add_of_abs_le (p : PMF State) {f g : State → ℝ} {C : ℝ}
    (hf : ∀ s, |f s| ≤ C) (hg : ∀ s, |g s| ≤ C) :
    expect p (fun s => f s + g s) = expect p f + expect p g :=
  expect_add p f g (summable_of_abs_le p hf) (summable_of_abs_le p hg)

/-- Monotone in the integrand, at a common bound. -/
public theorem expect_mono (p : PMF State) {f g : State → ℝ} {C : ℝ}
    (hf : ∀ s, |f s| ≤ C) (hg : ∀ s, |g s| ≤ C) (h : ∀ s, f s ≤ g s) :
    expect p f ≤ expect p g :=
  Summable.tsum_le_tsum (fun s => mul_le_mul_of_nonneg_left (h s) ENNReal.toReal_nonneg)
    (summable_of_abs_le p hf) (summable_of_abs_le p hg)

/-- Adding a constant to the integrand adds it to the expectation. -/
public theorem expect_add_const (p : PMF State) {f : State → ℝ} {C : ℝ}
    (hf : ∀ s, |f s| ≤ C) (c : ℝ) :
    expect p (fun s => f s + c) = expect p f + c := by
  rw [expect, expect]
  have hsplit : ∀ s, (p s).toReal * (f s + c)
      = (p s).toReal * f s + (p s).toReal * c := fun s => by ring
  simp only [hsplit]
  rw [(summable_of_abs_le p hf).tsum_add ((hasSum_prob p).summable.mul_right c),
    tsum_mul_right, (hasSum_prob p).tsum_eq, one_mul]

/-- A non-negative integrand has a non-negative expectation, with no bound and
no summability needed -- `tsum` of a non-negative family is non-negative even
when it diverges. Moved from `AISafetyAtlas.Causal.Query` with the rest. -/
public theorem expect_nonneg (p : PMF State) {f : State → ℝ}
    (hf : ∀ s, 0 ≤ f s) : 0 ≤ expect p f :=
  tsum_nonneg fun s => mul_nonneg ENNReal.toReal_nonneg (hf s)

/-- A function bounded below has an expectation bounded below -- the mirror of
`expect_le`, and the direction a minimax **lower** bound needs. -/
public theorem le_expect (p : PMF State) {f : State → ℝ} {C : ℝ}
    (hf : ∀ s, |f s| ≤ C) (c : ℝ) (h : ∀ s, c ≤ f s) : c ≤ expect p f := by
  have hc : ∀ s, |(fun _ : State => c) s| ≤ max C |c| := fun _ => le_max_right _ _
  have hf' : ∀ s, |f s| ≤ max C |c| := fun s => (hf s).trans (le_max_left _ _)
  simpa using expect_mono p hc hf' h

/-- A bounded function has a bounded expectation. -/
public theorem expect_le (p : PMF State) {f : State → ℝ} {C : ℝ}
    (hf : ∀ s, |f s| ≤ C) (c : ℝ) (h : ∀ s, f s ≤ c) : expect p f ≤ c := by
  have hc : ∀ s, |(fun _ : State => c) s| ≤ max C |c| := fun _ => le_max_right _ _
  have hf' : ∀ s, |f s| ≤ max C |c| := fun s => (hf s).trans (le_max_left _ _)
  simpa using expect_mono p hf' hc h

end AISafetyAtlas.Decision
