module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-!
# Overoptimization: a proxy over a strict subset of the attributes floors the rest

## What is stated

`zhuang_hadfield_menell_theorem_one` is Theorem 1 of Zhuang and Hadfield-Menell,
*Consequences of Misaligned AI*, at the binders print carries: an attribute
space, a constraint function, a proxy utility over a subset of the attributes, a
rate function, the optimization sequence it generates, feasibility along that
sequence, Complete Optimization, and convergence. The conclusion is print's: the
attributes the proxy omits sit at their lower bounds in the limit.

`proxyMax_unmentioned_eq_lowerBound` is its mathematical core, at an arbitrary
attribute type and with the sequence replaced by the one consequence of it the
argument uses -- that the limit point maximizes the proxy over the feasible set.

Two consequences say what that costs the principal, in the vocabulary the
Goodhart cluster uses elsewhere:

* `le_of_unmentioned_eq_lowerBound` -- the limit point is the pointwise least
  feasible state carrying its own proxy attributes;
* `gap_le_of_unmentioned_eq_lowerBound` -- so for any monotone true utility, the
  proxy-goal gap at the limit point is at least its value at every feasible
  state with the same proxy attributes. Optimizing the proxy does not merely
  fail to raise the goal; it lands on the gap-maximal point of its own level
  set.

## Provenance

Zhuang and Hadfield-Menell, *Consequences of Misaligned AI*, NeurIPS 2020,
Theorem 1. The published version is pinned at
`zhuang-hadfield-menell-published-neurips-2020-consequences-of-misaligned-ai.pdf`
sha256 bb5c7b5d179c6d63a777ef946c0449adeffc036036883280248ce0e50ae32710
and is the canonical version; it defers all proofs to supplementary material.
The arXiv preprint, pinned beside it at
`zhuang-hadfield-menell-arxiv-v1-2021-consequences-of-misaligned-ai.pdf`
sha256 37723b9165855628c3b0dd11908884dde8edd145ae277017be861d40dc8724aa,
carries the four-line proof, and that proof is the one reproduced here.

Print, section 3:

> **Theorem 1** For any continuous strictly increasing proxy utility function
> based on `J < L` attributes, if `s(t)` converges to some point `s*`, then
> `s*ₖ = bₖ` for `k ∈ K`.

## Scope against print

Five hypotheses print leaves implicit or states in a form that does not survive
transcription. Each is recorded because the statement changes without it.

* **The proxy attribute set must be nonempty.** Print writes `J < L`, which
  bounds `J` above and not below, and its setup takes the proxy attributes to be
  a subset of `{1, …, L}` without excluding the empty one. At `J = 0` the proxy
  is a constant, "strictly increasing" is vacuously true of it, every feasible
  state attains its supremum, and the conclusion is false: nothing pushes the
  omitted attributes anywhere. The proof picks a proxy attribute to raise, and
  there is none. So the nonemptiness of the proxy attribute set is a hypothesis,
  and the reading under which the printed sentence is true. The strict
  inequality in `J < L` shows the authors were counting a proper nonempty
  subset.

  **Added 2026-09-11: print states this hypothesis itself, two pages later.**
  Proposition 2, the impact-minimising robot, reads "define the proxy utility
  function ... for any *non-empty* set of proxy attributes". The notion is in the
  paper's own vocabulary and is written down at the one place the authors needed
  it, so its absence from Theorem 1 is an omission rather than an intended
  generality, and this module is not reading into print a hypothesis print does
  not have. Found while grading section 18 of
  `docs/provenance/source-coverage-audit.md`, which records it in the Theorem 1
  row.

  The other half of `J < L` -- that the proxy omits something -- is not
  carried, and dropping it is a vacuous-true widening: at a proxy over every
  attribute the conclusion quantifies over an empty set of omitted attributes
  and holds for that reason.

* **The lower bounds are a second constraint, not a consequence of the first.**
  Print's setup says the feasible set is `{s : C s ≤ 0}` for a continuous `C`
  strictly increasing in each attribute, and separately that each attribute is
  bounded below at `bᵢ`. Those two sentences are jointly unsatisfiable for a
  nonempty feasible set: lowering one coordinate lowers `C`, so `{s : C s ≤ 0}`
  is unbounded below in every coordinate. The reading that makes the setup
  consistent carries the box as its own constraint, which is what
  `feasibleStates` does. Nothing else in the paper depends on the difference.

* **Print's proof leaves out the step where the lower bound enters.** It lowers
  coordinate `k` by `ε`, raises a proxy coordinate by `δ`, and justifies the
  feasibility of the perturbed state with "since `C` is strictly increasing".
  That justifies the constraint half of feasibility and says nothing about the
  box half, which is the only place `b k` is used at all: the perturbation is
  admissible exactly while coordinate `k` sits strictly above `b k`, and it is
  the failure of that condition, not of the constraint, that the conclusion
  asserts. The proof reproduced here supplies the missing step by taking `ε` to
  be the whole distance to the floor.

* **Complete Optimization equates two real numbers, so the proxy is bounded
  above on the feasible set.** That is carried here by `IsLUB`, taking the
  supremum as a hypothesis rather than as a term. Writing it with Lean's `⨆`
  instead would make the theorem false: at an unbounded proxy `⨆` returns the
  junk value `0`, which a convergent sequence can meet at a limit point whose
  omitted attributes are nowhere near their floors.

* **Closedness of the feasible set is derived, not assumed.** Print assumes `S`
  closed; under the reading above it follows from continuity of `C`, which print
  also assumes, and `isClosed_feasibleStates` proves it. So print's closedness
  hypothesis is redundant rather than dropped.

Two further readings, neither of which changes the statement:

* **The core is wider than print.** `proxyMax_unmentioned_eq_lowerBound` is
  stated at an arbitrary attribute type with no finiteness, and takes the
  maximizing property directly instead of the optimization sequence. Print's
  `Fin L` and its sequence are one instance.
* **What the printed hypotheses buy.** The rate function, its continuity, the
  initial state and the integral representation of the optimization sequence are
  carried in the binders of the print-scope theorem and are inert in its proof.
  What the argument consumes is feasibility along the sequence, convergence, and
  Complete Optimization; continuity of the proxy is what carries the limit
  through. Recording that is the point of carrying them: the statement is the
  printed one, and the fact that the printed setup is stronger than the printed
  proof needs is a finding about the paper.

## This is not the Regressional carrier

The module `AISafetyAtlas.Goodhart.Regressional` states Regressional Goodhart on
a product of two lines, with an independent goal and gap. Nothing here is
stated against it and nothing here imports it, because the two do not share an
object:

* that carrier is fixed at two real variables and every theorem on it is about a
  product probability measure, where the independence of the goal and the gap is
  the whole content; nothing in Theorem 1 is random, and its selection is a
  maximum over a constraint set rather than a superlevel set of the proxy;
* even at two attributes with one of them in the proxy, the two triples point
  opposite ways. On that carrier the proxy is the sum and the goal a coordinate;
  here the proxy is a coordinate and the goal a function of all of them.

What the two share is a shape, not a definition: a state space, a goal and a
proxy on it, the gap between them, and a set of states selection can produce.
`gap_le_of_unmentioned_eq_lowerBound` states this row's conclusion in that
shape, pointwise, so the comparison can be read off without either module
depending on the other. See `docs/provenance/by037-by038-goodhart-campbell-plan.md`,
decision D3.
-/

namespace AISafetyAtlas.Goodhart

open Filter Set Topology

/-- **Strictly increasing in each attribute**, print's condition on both the
constraint function and the proxy utility: raising one coordinate and leaving
the others alone strictly raises the value. Stated one coordinate at a time,
which is print's phrase and the weaker hypothesis. The coordinatewise order's
`Monotone` is a consequence at a finite attribute set and is not assumed:
`monotone_of_strictMonoCoord` derives it. -/
@[expose] public def StrictMonoCoord {ι : Type*} [DecidableEq ι] (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ (x : ι → ℝ) (i : ι) {y : ℝ}, x i < y → f x < f (Function.update x i y)

/-- **The feasible states**: print's attribute space. The constraint `C s ≤ 0`
and the lower bounds are separate conditions. Print writes the space as the
constraint set alone and the lower bounds as a further property of it, which is
not satisfiable -- a `C` strictly increasing in each attribute leaves its
sublevel set unbounded below in every coordinate. -/
@[expose] public def feasibleStates {ι : Type*} (C : (ι → ℝ) → ℝ) (b : ι → ℝ) : Set (ι → ℝ) :=
  {s | C s ≤ 0 ∧ ∀ i, b i ≤ s i}

/-- **What the proxy sees**: a state cut down to the proxy attributes. The proxy
utility is a function of this and not of the state, so print's "based on `J`
attributes" is structural here rather than an asserted independence. -/
@[expose] public def restrictAttrs {ι : Type*} (J : Set ι) (s : ι → ℝ) : J → ℝ :=
  fun j => s j.1

/-- The feasible states are closed, from continuity of the constraint function.
Print assumes this separately; it is a consequence. -/
public theorem isClosed_feasibleStates {ι : Type*}
    {C : (ι → ℝ) → ℝ} (hC : Continuous C) (b : ι → ℝ) :
    IsClosed (feasibleStates C b) := by
  have h1 : IsClosed {s : ι → ℝ | C s ≤ 0} := isClosed_le hC continuous_const
  have h2 : IsClosed {s : ι → ℝ | ∀ i, b i ≤ s i} := by
    have : {s : ι → ℝ | ∀ i, b i ≤ s i} = ⋂ i, {s : ι → ℝ | b i ≤ s i} := by
      ext s; simp
    rw [this]
    exact isClosed_iInter fun i => isClosed_le continuous_const (continuous_apply i)
  exact h1.inter h2

public theorem continuous_restrictAttrs {ι : Type*} (J : Set ι) :
    Continuous (restrictAttrs J) :=
  continuous_pi fun j => continuous_apply j.1

/-- **The core of Theorem 1.** A feasible state that maximizes a proxy utility
built from a nonempty set of attributes has every attribute outside that set at
its lower bound.

Wider than print in three ways, none of which is a change of content: the
attribute type is arbitrary and not `Fin L`, the maximizing property replaces
the optimization sequence that delivers it, and continuity of the proxy is not
needed once the limit has been taken. The nonemptiness of the proxy attribute
set is the hypothesis print leaves implicit; without it the proxy is constant,
every feasible state maximizes it, and the conclusion fails. -/
public theorem proxyMax_unmentioned_eq_lowerBound {ι : Type*} [DecidableEq ι]
    {C : (ι → ℝ) → ℝ} (hCcont : Continuous C) (hCmono : StrictMonoCoord C)
    {b : ι → ℝ} {J : Set ι} (hJ : J.Nonempty)
    {Ut : (J → ℝ) → ℝ} (hUtmono : StrictMonoCoord Ut)
    {sstar : ι → ℝ} (hmem : sstar ∈ feasibleStates C b)
    (hmax : ∀ s ∈ feasibleStates C b, Ut (restrictAttrs J s) ≤ Ut (restrictAttrs J sstar))
    {k : ι} (hk : k ∉ J) :
    sstar k = b k := by
  by_contra hne
  have hlt : b k < sstar k := lt_of_le_of_ne (hmem.2 k) (Ne.symm hne)
  -- lower the omitted attribute `k` to its floor: this frees constraint slack
  set s₁ : ι → ℝ := Function.update sstar k (b k) with hs₁def
  have hs₁k : s₁ k = b k := Function.update_self ..
  have hs₁ne : ∀ i, i ≠ k → s₁ i = sstar i := fun i hi => Function.update_of_ne hi _ _
  have hupd : Function.update s₁ k (sstar k) = sstar := by
    funext i
    by_cases h : i = k
    · subst h; simp [hs₁def]
    · simp [Function.update_of_ne h, hs₁ne i h]
  have hC₁ : C s₁ < 0 := by
    have h := hCmono s₁ k (y := sstar k) (by rw [hs₁k]; exact hlt)
    rw [hupd] at h
    exact lt_of_lt_of_le h hmem.1
  -- raise a proxy attribute `j`, which the nonemptiness hypothesis supplies
  obtain ⟨j, hj⟩ := hJ
  have hjk : j ≠ k := fun h => hk (h ▸ hj)
  have hcont : Continuous fun δ : ℝ => C (Function.update s₁ j (s₁ j + δ)) := by
    refine hCcont.comp (continuous_pi fun i => ?_)
    by_cases h : i = j
    · subst h
      simp only [Function.update_self]
      fun_prop
    · simp only [Function.update_of_ne h]
      exact continuous_const
  have h0 : C (Function.update s₁ j (s₁ j + 0)) < 0 := by simpa using hC₁
  have hev : ∀ᶠ δ in 𝓝 (0:ℝ), C (Function.update s₁ j (s₁ j + δ)) < 0 :=
    (hcont.tendsto 0).eventually (gt_mem_nhds h0)
  have hev' : ∀ᶠ δ in 𝓝[>] (0:ℝ),
      C (Function.update s₁ j (s₁ j + δ)) < 0 ∧ δ ∈ Ioi (0:ℝ) :=
    (hev.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin
  obtain ⟨δ, hδC, hδpos⟩ := hev'.exists
  replace hδpos : 0 < δ := hδpos
  set s₂ : ι → ℝ := Function.update s₁ j (s₁ j + δ) with hs₂def
  have hs₂mem : s₂ ∈ feasibleStates C b := by
    refine ⟨hδC.le, fun i => ?_⟩
    by_cases h : i = j
    · subst h
      rw [hs₂def, Function.update_self, hs₁ne i hjk]
      have := hmem.2 i
      linarith
    · rw [hs₂def, Function.update_of_ne h]
      by_cases h' : i = k
      · subst h'; rw [hs₁k]
      · rw [hs₁ne i h']; exact hmem.2 i
  -- on the proxy attributes, `s₂` is `sstar` with coordinate `j` raised
  have hview : restrictAttrs J s₂
      = Function.update (restrictAttrs J sstar) ⟨j, hj⟩ (sstar j + δ) := by
    funext i
    by_cases h : (i : ι) = j
    · have hi : i = (⟨j, hj⟩ : J) := Subtype.ext h
      subst hi
      simp [restrictAttrs, hs₂def, Function.update_self, hs₁ne j hjk]
    · have hi : i ≠ (⟨j, hj⟩ : J) := fun hh => h (congrArg Subtype.val hh)
      have hik : (i : ι) ≠ k := fun hh => hk (hh ▸ i.2)
      simp [restrictAttrs, hs₂def, Function.update_of_ne hi, Function.update_of_ne h,
        hs₁ne (i : ι) hik]
  have hUlt : Ut (restrictAttrs J sstar) < Ut (restrictAttrs J s₂) := by
    rw [hview]
    exact hUtmono (restrictAttrs J sstar) ⟨j, hj⟩ (by
      show sstar j < sstar j + δ
      linarith)
  exact absurd (hmax s₂ hs₂mem) (not_le.mpr hUlt)

/-- **The optimizer lands on the pointwise least state of its own proxy level
set.** Every feasible state carrying the limit point's proxy attributes is
pointwise above it. -/
public theorem le_of_unmentioned_eq_lowerBound {ι : Type*}
    {b : ι → ℝ} {J : Set ι} {sstar s : ι → ℝ}
    (hfloor : ∀ k ∉ J, sstar k = b k) (hs : ∀ i, b i ≤ s i)
    (hJeq : ∀ j ∈ J, s j = sstar j) (i : ι) :
    sstar i ≤ s i := by
  by_cases h : i ∈ J
  · exact le_of_eq (hJeq i h).symm
  · rw [hfloor i h]; exact hs i

/-- Coordinatewise strict monotonicity implies monotonicity for the
coordinatewise order, at a finite attribute set. This is what lets the gap
corollary below ask only for a monotone true utility while print supplies one
that is strictly increasing in each attribute: print's hypothesis is the
stronger of the two, so the corollary is the wider statement. -/
public theorem monotone_of_strictMonoCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → ℝ) → ℝ} (hf : StrictMonoCoord f) : Monotone f := by
  intro x y hxy
  have key : ∀ s : Finset ι, f x ≤ f (fun i => if i ∈ s then y i else x i) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s ha ih =>
        have hstep : (fun i => if i ∈ insert a s then y i else x i)
            = Function.update (fun i => if i ∈ s then y i else x i) a (y a) := by
          funext i
          by_cases h : i = a
          · subst h; simp [ha]
          · simp [Finset.mem_insert, h]
        rw [hstep]
        rcases eq_or_lt_of_le (hxy a) with heq | hlt
        · have hsame : Function.update (fun i => if i ∈ s then y i else x i) a (y a)
              = fun i => if i ∈ s then y i else x i := by
            funext i
            by_cases h : i = a
            · subst h; simp [ha, ← heq]
            · simp [Function.update_of_ne h]
          rw [hsame]
          exact ih
        · refine ih.trans (le_of_lt (hf _ a ?_))
          simpa [ha] using hlt
  simpa using key Finset.univ

/-- **The proxy-goal gap is maximal at the optimizer.** For any true utility
monotone in the attributes, no feasible state with the limit point's proxy
attributes has a larger gap between proxy and goal. This is the row's conclusion
in the vocabulary the Goodhart cluster uses elsewhere -- a goal, a proxy, and
the gap between them -- and it is pointwise, with no measure and no
independence, which is why it is stated here rather than against
`AISafetyAtlas.Goodhart.Regressional`.

Print's own utility is continuous and strictly increasing in each attribute, so
`monotone_of_strictMonoCoord` supplies this hypothesis from print's; monotonicity
is all this uses. -/
public theorem gap_le_of_unmentioned_eq_lowerBound {ι : Type*}
    {C : (ι → ℝ) → ℝ} {b : ι → ℝ} {J : Set ι} {U : (ι → ℝ) → ℝ} {Ut : (J → ℝ) → ℝ}
    (hU : Monotone U) {sstar s : ι → ℝ}
    (hfloor : ∀ k ∉ J, sstar k = b k) (hs : s ∈ feasibleStates C b)
    (hJeq : ∀ j ∈ J, s j = sstar j) :
    Ut (restrictAttrs J s) - U s ≤ Ut (restrictAttrs J sstar) - U sstar := by
  have hview : restrictAttrs J s = restrictAttrs J sstar := by
    funext j; exact hJeq j.1 j.2
  have hle : U sstar ≤ U s :=
    hU fun i => le_of_unmentioned_eq_lowerBound hfloor hs.2 hJeq i
  rw [hview]
  linarith

/-- **Zhuang and Hadfield-Menell, Theorem 1**, at print's binders.

> For any continuous strictly increasing proxy utility function based on `J < L`
> attributes, if `s(t)` converges to some point `s*`, then `s*ₖ = bₖ` for
> `k ∈ K`.

The nonemptiness of the proxy attribute set is the hypothesis print leaves
implicit and without which the statement is false. The supremum of the proxy
over the feasible set is carried as an upper-bound hypothesis rather than as a
term, and the limsup equation is print's Complete Optimization assumption.

Two binders are named with a leading underscore because print carries them and
the proof does not use them: the continuity of the rate function and the
integral representation of the optimization sequence. What the argument consumes
is feasibility along the sequence, its convergence, Complete Optimization, and
continuity of the proxy, which is what carries the limit through. -/
public theorem zhuang_hadfield_menell_theorem_one {L : ℕ}
    (C : (Fin L → ℝ) → ℝ) (hCcont : Continuous C) (hCmono : StrictMonoCoord C)
    (b : Fin L → ℝ) (J : Set (Fin L)) (hJ : J.Nonempty)
    (Ut : (J → ℝ) → ℝ) (hUtcont : Continuous Ut) (hUtmono : StrictMonoCoord Ut)
    (s0 : Fin L → ℝ) (f : ℝ → (Fin L → ℝ)) (_hf : ContinuousOn f (Ici 0))
    (s : ℝ → (Fin L → ℝ))
    (_hs : ∀ t ∈ Ici (0:ℝ), s t = s0 + ∫ u in (0:ℝ)..t, f u)
    (hfeas : ∀ t ∈ Ici (0:ℝ), s t ∈ feasibleStates C b)
    (M : ℝ) (hM : IsLUB ((fun x => Ut (restrictAttrs J x)) '' feasibleStates C b) M)
    (hcomplete : limsup (fun t => Ut (restrictAttrs J (s t))) atTop = M)
    (sstar : Fin L → ℝ) (hconv : Tendsto s atTop (𝓝 sstar)) :
    ∀ k ∉ J, sstar k = b k := by
  have hevfeas : ∀ᶠ t in atTop, s t ∈ feasibleStates C b := by
    filter_upwards [eventually_ge_atTop (0:ℝ)] with t ht using hfeas t ht
  have hmem : sstar ∈ feasibleStates C b :=
    (isClosed_feasibleStates hCcont b).mem_of_tendsto hconv hevfeas
  have htend : Tendsto (fun t => Ut (restrictAttrs J (s t))) atTop
      (𝓝 (Ut (restrictAttrs J sstar))) :=
    ((hUtcont.comp (continuous_restrictAttrs J)).tendsto sstar).comp hconv
  have hval : Ut (restrictAttrs J sstar) = M := by rw [← hcomplete, htend.limsup_eq]
  intro k hk
  refine proxyMax_unmentioned_eq_lowerBound hCcont hCmono hJ hUtmono hmem ?_ hk
  intro x hx
  rw [hval]
  exact hM.1 ⟨x, hx, rfl⟩

end AISafetyAtlas.Goodhart
