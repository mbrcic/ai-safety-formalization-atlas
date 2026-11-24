module

public import AISafetyAtlas.Causal.Model
public import Mathlib.Probability.ProductMeasure
public import Mathlib.Probability.ProbabilityMassFunction.Constructions
public import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Structural causal models

Everitt, Carey, Langlois, Ortega and Legg, *Agent Incentives: A Causal
Perspective*, AAAI 2021, Definition 1, attributed there to Pearl 2009 Chapter 7:

> A **structural causal model** (with independent errors) is a tuple
> `⟨E, V, F, P⟩`, where `E` is a set of exogenous variables; `V` is a set of
> endogenous variables; and `F = {f^V}` is a collection of functions, one for
> each `V`. Each function `f^V : dom(Pa_V ∪ {E^V}) → dom(V)` specifies the value
> of `V` in terms of the values of the corresponding exogenous variable `E^V`
> and endogenous parents `Pa_V ⊂ V`, where these functional dependencies are
> acyclic. … The uncertainty is encoded through a probability distribution
> `P(ε)` such that the exogenous variables are mutually independent.

This is a different object from `Causal.Model`. That one is a causal Bayesian
network: a graph and conditional probability tables. This one consigns all
randomness to exogenous variables and relates the endogenous ones by
**deterministic** functions. Print's own words for why the distinction matters:
*"this structural approach has significant benefits over traditional causal
Bayesian networks for analysing (nested) counterfactuals and 'individual-level'
effects."* Neither is a special case of the other as rendered here.

**Independence is a product of marginals.** Print carries one joint `P(ε)` and
requires the exogenous variables to be mutually independent. At a countably
supported distribution that is exactly the class of products of per-variable
distributions, and the product is the form every later computation reads.

**Domains are types, because print's `dom(V)` carries no cardinality
condition.** *"Finite"* occurs twice in the whole paper, both inside Definition
4 and both qualifying domains, so Definitions 1 and 2 admit domains of any size.
`SCM` therefore carries none: the marginal-sum field is unconditional, and every
finiteness instance sits on the derived operation that needs it — the `Finset`
sums of `jointProb` and `marginal`, the maximum over policies at Definition 5,
and the singleton masses in the measure layer.
`AISafetyAtlas.Examples.Causal.StructuralModel.geometricCopy` is a model with
infinite domains that `eval` and `submodel` run on.

**Evaluation is print's recursion, taken literally.** Print says the value of a
variable at a fixed `ε` is *"given by recursive application of the structural
functions"*, and `eval` is exactly that: well-founded recursion on the parent
relation, with `eval_eq_f` as its fixed-point property. There is no iteration
count, no rank, and no bound on the number of variables.

**Where well-foundedness lives, and why not on the structure.** `SCM.acyclic`
and `CID.acyclic` are print's bare word and nothing more. Well-foundedness is
strictly stronger at an unbounded vertex set, and it is what the recursion
needs: `chainParents` is the integers with `Pa_n = {n-1}`, which is acyclic, is
not well-founded, and admits **two** solutions of the equation `eval_eq_f`
asserts. Print says *the* value, so on a diagram print's own words admit,
print's own words name nothing unique.

So it is a **property of a model** rather than a field of one. `SCM.IsWellFounded`
and `CID.IsWellFounded` are classes, and every declaration whose meaning depends
on the recursion asks for the instance — `eval` and `jointProb` here,
`expectedUtility`, `optimalValue` and `IsMaterial` at the SCIM. Four instances
carry it across `submodel`, `softIntervention`, `withPolicy` and
`removeInfoLink`, so no statement asks for it twice. The structures admit
exactly print's tuples, which is what the source coverage audit grades, and
Definitions 3 and 4 are `Same` for that reason. An earlier design carried it as
a field and the audit graded Definitions 1, 2, 4 and 5 `Narrower` on the axis;
that is retracted in the audit's own §8 preamble.

**Finite indegree is gone with it.** `parents` is a `Set`, so a vertex may have
infinitely many parents, as print's unbounded `Pa_V ⊂ V` allows.
`wellFounded_iff_exists_rank` records why these two axes had to move together:
while `parents` was a `Finset`, well-foundedness and an `ℕ`-valued rank were the
same condition, so dropping the rank alone would have generalized nothing.

`Causal.Model`, the causal Bayesian network, keeps a finite vertex set and its
own acyclicity; it is a separate rendering of a separate source and this
paragraph does not apply to it.
-/

namespace AISafetyAtlas.Causal

/-- A rank strictly decreasing along parents makes the parent relation
well-founded. This is the direction a worked example needs: exhibiting a rank on
a finite diagram is the cheapest way to discharge `SCM.IsWellFounded`. -/
public theorem wellFounded_of_rank {V : Type*} {parents : V → Set V} (rank : V → ℕ)
    (h : ∀ v, ∀ p ∈ parents v, rank p < rank v) :
    WellFounded fun p v ↦ p ∈ parents v :=
  Subrelation.wf (fun {p v} hp ↦ h v p hp) (InvImage.wf rank wellFounded_lt)

/-- Every edge of a directed path strictly lowers the rank, so no path returns
to where it started. This discharges `CID.acyclic` from a rank. -/
public theorem acyclic_of_rank {V : Type*} {parents : V → Set V} (rank : V → ℕ)
    (h : ∀ v, ∀ p ∈ parents v, rank p < rank v) (v : V) :
    ¬ Relation.TransGen (fun p v ↦ p ∈ parents v) v v := by
  have key : ∀ a b, Relation.TransGen (fun p v ↦ p ∈ parents v) a b → rank a < rank b := by
    intro a b hab
    induction hab with
    | single hbc => exact h _ _ hbc
    | tail _ hbc ih => exact ih.trans (h _ _ hbc)
  exact fun hv ↦ absurd (key v v hv) (lt_irrefl _)

/-- **What well-foundedness replaced, and why the two axes had to move
together.**

Acyclicity used to be rendered as `∃ rank : V → ℕ` strictly decreasing along
parents. Under *finite indegree* that is exactly well-foundedness, as this
theorem shows -- so replacing the rank while keeping `parents : V → Finset V`
would have admitted precisely the same models and generalized nothing. What
generalizes is the pair: an unbounded parent set together with a relation that
is only well-founded.

The converse direction is where the finiteness is used: the rank is built by
well-founded recursion as one more than the largest rank among the parents, and
`ℕ` has no such largest element over an infinite parent set. -/
public theorem wellFounded_iff_exists_rank {V : Type*} {parents : V → Set V}
    (hfin : ∀ v, (parents v).Finite) :
    (WellFounded fun p v ↦ p ∈ parents v) ↔
      ∃ rank : V → ℕ, ∀ v, ∀ p ∈ parents v, rank p < rank v := by
  classical
  constructor
  · intro hwf
    set rank : V → ℕ := hwf.fix fun v ih ↦
      (hfin v).toFinset.attach.sup fun q ↦ ih q.1 ((hfin v).mem_toFinset.mp q.2) + 1
      with hdef
    refine ⟨rank, fun v p hp ↦ ?_⟩
    have hmem : (⟨p, (hfin v).mem_toFinset.mpr hp⟩ :
        {a // a ∈ (hfin v).toFinset}) ∈ (hfin v).toFinset.attach :=
      Finset.mem_attach _ _
    have hle : rank p + 1 ≤ (hfin v).toFinset.attach.sup fun q ↦ rank q.1 + 1 :=
      Finset.le_sup (f := fun q : {a // a ∈ (hfin v).toFinset} ↦ rank q.1 + 1) hmem
    have hv : rank v = (hfin v).toFinset.attach.sup fun q ↦ rank q.1 + 1 := by
      rw [hdef]; exact WellFounded.fix_eq _ _ _
    omega
  · rintro ⟨rank, hrank⟩
    exact wellFounded_of_rank rank hrank

/-! ### Why `eval` asks for more than `SCM.acyclic`

The declarations below are the witness the source coverage audit cites. They
exhibit print's own Definition 1 sentence failing to name anything on a diagram
print's words admit, which is why well-foundedness is a hypothesis on the
recursion rather than a condition anyone can drop. -/

/-- The integer chain `Pa_n = {n-1}`: print's `Pa_V ⊂ V` at every vertex. -/
@[expose] public def chainParents (n : ℤ) : Set ℤ := {n - 1}

/-- Every edge lowers the vertex, so a directed path never returns. -/
public theorem chainParents_lt {a b : ℤ}
    (h : Relation.TransGen (fun p v ↦ p ∈ chainParents v) a b) : a < b := by
  induction h with
  | single hbc => exact hbc ▸ sub_one_lt _
  | tail _ hbc ih => exact ih.trans (hbc ▸ sub_one_lt _)

/-- **The chain is acyclic in print's sense.** It satisfies `CID.acyclic`. -/
public theorem chainParents_acyclic (v : ℤ) :
    ¬ Relation.TransGen (fun p v ↦ p ∈ chainParents v) v v :=
  fun h ↦ absurd (chainParents_lt h) (lt_irrefl v)

/-- **...and it fails `SCM.IsWellFounded`.** A minimal vertex would have to have
no parent, and every integer has one. -/
public theorem chainParents_not_wellFounded :
    ¬ WellFounded fun p v ↦ p ∈ chainParents v := by
  intro hwf
  obtain ⟨m, -, hm⟩ := hwf.has_min Set.univ ⟨0, trivial⟩
  exact hm (m - 1) trivial rfl

/-- **What that costs print, and why `eval` takes a hypothesis.**

Definition 1 says the value of each variable at a fixed `ε` is *"given by
recursive application of the structural functions"* -- one value, *the* value.
Take the chain above with two states per vertex and the structural function that
copies the parent. The equation `eval_eq_f` asks for is then `W v = W (v-1)`,
and it has **two** solutions, the two constants. So on a diagram print's own
words admit, print's own words do not name a unique assignment.

So `eval` cannot be **totalised** over the class `SCM.acyclic` admits. A total
`eval` could be produced there by choice and would even satisfy `eval_eq_f`, but
`eval_eq_f` would no longer pin it down and the atlas would be asserting a
determinacy Definition 1 does not have. That is a fact about `eval`, and not a
reason for `SCM` to carry a field print does not write -- the two were confused
for part of one day, and the audit's §8 preamble records the retraction.
`SCM.IsWellFounded` is instead the condition under which the quoted sentence
names exactly one thing, asked for where the sentence is used. -/
public theorem chainParents_fixedPoint_not_unique :
    ∃ W W' : ℤ → Fin 2, W ≠ W' ∧
      (∀ v, W v = W (v - 1)) ∧ (∀ v, W' v = W' (v - 1)) :=
  ⟨fun _ ↦ 0, fun _ ↦ 1, fun h ↦ by simpa using congrFun h 0,
    fun _ ↦ rfl, fun _ ↦ rfl⟩

variable {V : Type*} [Fintype V] [DecidableEq V] {dom edom : V → Type*}

/--
**An assignment to the endogenous variables**, print's `w`.

`AISafetyAtlas.Causal.Assignment` is the same shape at `Fin`-indexed domains and
belongs to the decision layer of section 6 of the coverage audit; this one is
section 8's, and the two layers do not meet, so no bridge between them is owed.
The difference is the axis: print's `dom(V)` carries no cardinality condition,
and this is a family of **types**.
-/
public abbrev EndoAssignment (V : Type*) (dom : V → Type*) := (v : V) → dom v

/-- An assignment to the exogenous variables. -/
public abbrev ExoAssignment (V : Type*) (edom : V → Type*) := (v : V) → edom v

/-- **Definition 1.** A structural causal model with independent errors. -/
public structure SCM (V : Type*) [DecidableEq V] (dom edom : V → Type*) where
  /-- Every endogenous variable has at least one state, which is what makes the
  structural functions well-typed. -/
  dom_nonempty : ∀ v, Nonempty (dom v)
  /-- The endogenous parents `Pa_V ⊂ V`: a subset, with no cardinality bound,
  because print writes none. -/
  parents : V → Set V
  /-- *"where these functional dependencies are acyclic"*, and nothing more:
  no vertex is reachable from itself. This is print's own word, in the same
  form `CID.acyclic` carries it.

  Nothing in this file consumes this field -- `eval` asks for the strictly
  stronger `SCM.IsWellFounded` instead, and `submodel` and `softIntervention`
  only propagate it. It is here because print writes it, and because the class
  of tuples this structure admits is what the coverage audit grades. See
  `wellFounded_iff_exists_rank` for the `ℕ`-rank this replaced and
  `chainParents` for why the recursion needs more than this. -/
  acyclic : ∀ v, ¬ Relation.TransGen (fun p v ↦ p ∈ parents v) v v
  /-- `f^V : dom(Pa_V ∪ {E^V}) → dom(V)`, presented on full assignments with
  `f_parents` witnessing that only the parents are read. -/
  f : (v : V) → EndoAssignment V dom → edom v → dom v
  /-- A structural function reads only its declared parents and its own
  exogenous variable. -/
  f_parents : ∀ v a b e, (∀ p ∈ parents v, a p = b p) → f v a e = f v b e
  /-- The distribution of the exogenous variable `E^V`. Mutual independence is
  rendered as one marginal per variable; see the module docstring. -/
  exoProb : (v : V) → edom v → ℝ
  /-- Each marginal is nonnegative. -/
  exoProb_nonneg : ∀ v e, 0 ≤ exoProb v e
  /-- Each marginal is a probability distribution. The sum is unconditional, so
  it says what print says at a domain of any size; `exoProb_sum_fintype` is the
  finite reading. -/
  exoProb_tsum : ∀ v, ∑' e : edom v, exoProb v e = 1

omit [Fintype V] in
/-- **The hypothesis `eval` needs, carried where print needs it.**

Print's Definition 1 writes only *"acyclic"*, and `SCM.acyclic` is that word.
But Definition 1's next sentence gives `W(ε)` by *"recursive application of the
structural functions"*, and on an acyclic diagram that is not well-founded the
recursion names nothing unique -- `chainParents` on `ℤ` is acyclic and carries
**two** assignments satisfying `eval_eq_f`. So this is a property of a model
rather than a field of one: the structure admits exactly print's tuples, and
every declaration whose meaning depends on the recursion asks for this instance.

`wellFounded_of_rank` discharges it on any diagram with an `ℕ`-valued rank,
which is the cheapest route on a finite example. -/
public class SCM.IsWellFounded (M : SCM V dom edom) : Prop where
  /-- The parent relation is well-founded. -/
  wf : WellFounded fun p v ↦ p ∈ M.parents v

namespace SCM

variable (M : SCM V dom edom)

omit [Fintype V] in
/--
**Print's Definition 1 imposes no cardinality condition and neither does `SCM`.**

Print writes *"finite"* exactly twice in the whole paper, both inside Definition
4 and both qualifying **domains**; Definition 1 writes `dom(V)` bare. So the
domains here are a family of **types**, and every finiteness condition below sits
on the derived operation that needs it rather than on the structure — the same
move the vertex set made on 2026-08-21.

`exoProb_sum_fintype` is `exoProb_tsum` at a finite exogenous domain, which is
the case print's own Definition 4 admits and the case every witness in
`AISafetyAtlas.Examples.Causal.StructuralModel` lives in.
-/
public theorem exoProb_sum_fintype [∀ v, Fintype (edom v)] (v : V) :
    ∑ e : edom v, M.exoProb v e = 1 :=
  (tsum_fintype (M.exoProb v)).symm.trans (M.exoProb_tsum v)

section FiniteDomains

variable [∀ v, Fintype (edom v)]

/-- `P(ε)`: the exogenous variables are mutually independent, so the joint is
the product of the marginals. -/
@[expose] public noncomputable def exoJoint (ε : ExoAssignment V edom) : ℝ :=
  ∏ v : V, M.exoProb v (ε v)

omit [∀ v, Fintype (edom v)] in
public theorem exoJoint_nonneg (ε : ExoAssignment V edom) : 0 ≤ M.exoJoint ε :=
  Finset.prod_nonneg fun v _ ↦ M.exoProb_nonneg v (ε v)

public theorem exoJoint_sum : ∑ ε : ExoAssignment V edom, M.exoJoint ε = 1 := by
  classical
  have h : ∏ v : V, (∑ e : edom v, M.exoProb v e) = 1 :=
    Finset.prod_eq_one fun v _ ↦ M.exoProb_sum_fintype v
  rw [← h, Finset.prod_univ_sum]
  simp [exoJoint, Fintype.piFinset_univ]

/-- **Independence, in the form an expectation uses.** The joint expectation of
a product of one factor per exogenous variable is the product of the marginal
expectations. `exoJoint_sum` is the case `g = 1`, and this is what makes
*"mutually independent"* usable rather than merely stated. -/
public theorem exoJoint_mul_prod (g : (v : V) → edom v → ℝ) :
    ∑ ε : ExoAssignment V edom, M.exoJoint ε * ∏ v : V, g v (ε v)
      = ∏ v : V, ∑ e : edom v, M.exoProb v e * g v e := by
  classical
  rw [Finset.prod_univ_sum]
  simp [exoJoint, Fintype.piFinset_univ, ← Finset.prod_mul_distrib]

end FiniteDomains

/-! ## Evaluation

`W(ε)` is print's *"recursive application of the structural functions"*. -/

/-- The default assignment. It is used only to extend a partial assignment on
the parents of a vertex to a total one, which is what `f` expects; `f_parents`
says no structural function reads the extension. -/
@[expose] public noncomputable def seed : EndoAssignment V dom :=
  fun v ↦ (M.dom_nonempty v).some

omit [Fintype V] in
/-- **`W(ε)`**: the value of every endogenous variable at a fixed `ε`.

This is print's *"recursive application of the structural functions"* directly:
well-founded recursion on the parent relation. It reads the values already
computed at the parents of `v`, extends them by `seed` off the parent set so
that `f` receives a total assignment, and applies `f`. The decidability instance
is pinned to `Classical.propDecidable` here and in `eval_eq_f` so that the two
`dite`s are the same term.

There is no iteration count and no bound on the number of variables. -/
@[expose] public noncomputable def eval (M : SCM V dom edom) [hM : M.IsWellFounded]
    (ε : ExoAssignment V edom) : EndoAssignment V dom :=
  hM.wf.fix fun v ih ↦
    M.f v (fun p ↦ @dite _ (p ∈ M.parents v) (Classical.propDecidable _)
      (fun h ↦ ih p h) (fun _ ↦ M.seed p)) (ε v)

omit [Fintype V] in
/-- **`eval` is print's recursion.** The value of each variable at `ε` is the
structural function of that variable applied to the values of its parents at
`ε`. It is the fixed-point property of the well-founded recursion, and the step
that makes `eval` print's `W(ε)` rather than one arbitrary choice among the
functions satisfying no equation. -/
public theorem eval_eq_f (M : SCM V dom edom) [M.IsWellFounded]
    (ε : ExoAssignment V edom) (v : V) :
    M.eval ε v = M.f v (M.eval ε) (ε v) := by
  rw [eval, WellFounded.fix_eq]
  exact M.f_parents v _ _ _ fun p hp ↦ dif_pos hp

omit [Fintype V] in
/-- `eval` reads only the declared parents, which is `f_parents` transported
through the recursion. -/
public theorem eval_congr (M : SCM V dom edom) [M.IsWellFounded]
    (ε ε' : ExoAssignment V edom)
    (v : V) (hε : ε v = ε' v)
    (hp : ∀ p ∈ M.parents v, M.eval ε p = M.eval ε' p) :
    M.eval ε v = M.eval ε' v := by
  rw [M.eval_eq_f ε v, M.eval_eq_f ε' v, hε]
  exact M.f_parents v _ _ _ hp

omit [Fintype V] in
/-- **Two models that agree where it matters evaluate the same there.** Same
parent map, structural functions equal on an ancestor-closed set `S`: then the
recursions agree at every vertex of `S`, because `eval` at `v` reads only `v`'s
structural function and the values at `v`'s parents, which `S` contains.

This is the mechanism behind print's *"for a set of variables `X` not in
*Desc_D*, `Pr^π(x)` is independent of `π`"*, and it is stated separately because
nothing in it is about policies. -/
public theorem eval_eq_of_f_agree (M M' : SCM V dom edom)
    [hM : M.IsWellFounded] [M'.IsWellFounded]
    (hpar : ∀ v, M.parents v = M'.parents v)
    (S : Set V) (hS : ∀ v ∈ S, ∀ p ∈ M.parents v, p ∈ S)
    (hf : ∀ v ∈ S, M.f v = M'.f v)
    (ε : ExoAssignment V edom) : ∀ v ∈ S, M.eval ε v = M'.eval ε v := by
  intro v hv
  induction v using hM.wf.induction with
  | _ v ih =>
    rw [M.eval_eq_f ε v, M'.eval_eq_f ε v, hf v hv]
    exact M'.f_parents v _ _ _ fun p hp ↦
      ih p ((hpar v) ▸ hp) (hS v hv p ((hpar v) ▸ hp))

/-! ## The induced joint

Print: *"Together with the distribution `P(ε)` over exogenous variables, this
induces a joint distribution `Pr(W = w) = Σ_{ε | W(ε) = w} P(ε)`."*

The sums below are where print's Definition 4 finiteness lives. `SCM.endoLaw` is
the same object without them. -/

omit [Fintype V] in
/-- **`Pr(W = w)`, print's formula verbatim, at any vertex set.** Print: *"this
induces a joint distribution `Pr(W = w) = Σ_{ε | W(ε) = w} P(ε)`"*
(ec21-scm-joint, PDF p. 2), with `P(ε)` the product of the independent marginals.
So this is an unconditional sum, over the draws whose evaluation agrees with `w`
on `W`, of the unconditional product of the exogenous weights.

No finiteness, countability or measurability is asked: the formula is written
wherever print writes it, including at an uncountable vertex set where no
evaluation map need be measurable for the product measure. `SCM.sumProb_coe_eq_marginal`
is the finite computation.

The formula is print's, and so is its presupposition that `P` is atomic: at a
product of infinitely many non-degenerate marginals every draw has weight `0`, so
every value of this sum is `0` there (compare `SCM.aemeasurable_of_countable_support`).
The policy-invariance theorem `SCIM.sumProb_withPolicy_eq_of_notDownstream` holds
either way. -/
@[expose] public noncomputable def sumProb (M : SCM V dom edom) [M.IsWellFounded]
    (W : Set V) (w : EndoAssignment V dom) : ℝ :=
  ∑' ε : {ε : ExoAssignment V edom | ∀ v ∈ W, M.eval ε v = w v},
    ∏' v, M.exoProb v (ε.1 v)

section FiniteJoint

variable [∀ v, Fintype (edom v)] [∀ v, Fintype (dom v)] [∀ v, DecidableEq (dom v)]

/-- `Pr(V = w)`, the joint over all endogenous variables. -/
@[expose] public noncomputable def jointProb (M : SCM V dom edom) [M.IsWellFounded]
    (w : EndoAssignment V dom) : ℝ :=
  ∑ ε ∈ Finset.univ.filter fun ε : ExoAssignment V edom ↦ M.eval ε = w,
    M.exoJoint ε

omit [∀ v, Fintype (dom v)] in
public theorem jointProb_nonneg (M : SCM V dom edom) [M.IsWellFounded]
    (w : EndoAssignment V dom) :
    0 ≤ M.jointProb w :=
  Finset.sum_nonneg fun ε _ ↦ M.exoJoint_nonneg ε

/-- The induced joint is a probability distribution: the fibres of `eval`
partition the exogenous assignments. -/
public theorem jointProb_sum (M : SCM V dom edom) [M.IsWellFounded] :
    ∑ w : EndoAssignment V dom, M.jointProb w = 1 := by
  classical
  rw [← M.exoJoint_sum]
  exact (Finset.sum_fiberwise_of_maps_to (fun ε _ ↦ Finset.mem_univ (M.eval ε))
    fun ε ↦ M.exoJoint ε).symm ▸ rfl


/-- **`Pr(x)`**, the induced probability that the variables in `X` take the
values `x` assigns them. Print writes `Pr^π(x)` for a *set* of variables, so the
object graded is the marginal rather than the full joint. -/
@[expose] public noncomputable def marginal (M : SCM V dom edom) [M.IsWellFounded]
    (X : Finset V) (x : EndoAssignment V dom) : ℝ :=
  ∑ w ∈ Finset.univ.filter (fun w : EndoAssignment V dom ↦ ∀ c ∈ X, w c = x c),
    M.jointProb w

/-- The marginal read off the exogenous draw instead of off the joint: the
fibres of `eval` partition the exogenous assignments, so summing `jointProb`
over the `X`-fibre is summing `P(ε)` over the draws whose evaluation lands in
it. This is what turns a statement about `eval` into a statement about `Pr`. -/
public theorem marginal_eq_sum_exo (M : SCM V dom edom) [M.IsWellFounded]
    (X : Finset V) (x : EndoAssignment V dom) :
    M.marginal X x = ∑ ε ∈ Finset.univ.filter
        (fun ε : ExoAssignment V edom ↦ ∀ c ∈ X, M.eval ε c = x c), M.exoJoint ε := by
  classical
  simp only [marginal, jointProb, Finset.sum_filter]
  have key : ∀ w : EndoAssignment V dom,
      (if (∀ c ∈ X, w c = x c) then
          ∑ ε : ExoAssignment V edom, (if M.eval ε = w then M.exoJoint ε else 0) else 0)
        = ∑ ε : ExoAssignment V edom,
            (if (∀ c ∈ X, w c = x c) ∧ M.eval ε = w then M.exoJoint ε else 0) := by
    intro w
    split_ifs with h
    · simp only [eq_true h, true_and]
    · simp [h]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ε _ ↦ ?_
  rw [Finset.sum_eq_single (M.eval ε)]
  · simp
  · intro w _ hw; simp [Ne.symm hw]
  · simp

omit [∀ v, Fintype (dom v)] in
/-- **At a finite model print's formula is the finite marginal**: the
unconditional sum and product of `SCM.sumProb` are the `Finset` sum and product of
`SCM.marginal`. -/
public theorem sumProb_coe_eq_marginal (M : SCM V dom edom) [M.IsWellFounded]
    [∀ v, Fintype (dom v)] (X : Finset V) (x : EndoAssignment V dom) :
    M.sumProb (↑X) x = M.marginal X x := by
  classical
  rw [marginal_eq_sum_exo, sumProb,
    tsum_subtype _ fun ε : ExoAssignment V edom ↦ ∏' v, M.exoProb v (ε v),
    tsum_fintype, Finset.sum_filter]
  refine Finset.sum_congr rfl fun ε _ ↦ ?_
  simp only [Set.indicator, Set.mem_ofPred_eq, Finset.mem_coe, tprod_fintype, exoJoint]

end FiniteJoint

/-! ## Interventions

Print, Definition 2: *"Let `M = ⟨E, V, F, P⟩` be an SCM, `X` a set of variables
in `V`, and `x` a particular realization of `X`. The submodel `M_x` represents
the effects of an intervention `do(X = x)`, and is formally defined as the SCM
`⟨E, V, F_x, P⟩` where `F_x = {f^V | V ∉ X} ∪ {X = x}`."*

The intervened variables also lose their incoming edges, which is print's own
reading — Figure 2c notes that *"the intervention on `D` severs the link from
`ε^D` to `d`"*. Nothing downstream depends on that choice: a constant function reads no
parents, so `submodel_eval` holds either way. -/

/-- **Definition 2.** The submodel `M_x`, the effect of `do(X = x)`. -/
@[expose] public noncomputable def submodel (M : SCM V dom edom) (X : Finset V)
    (x : EndoAssignment V dom) : SCM V dom edom where
  dom_nonempty := M.dom_nonempty
  parents := fun v ↦ if v ∈ X then ∅ else M.parents v
  acyclic := fun v hv ↦ M.acyclic v (Relation.TransGen.mono (fun p w hp ↦ by
    by_cases hw : w ∈ X
    · rw [if_pos hw] at hp; exact absurd hp (Set.notMem_empty p)
    · rwa [if_neg hw] at hp) _ _ hv)
  f := fun v a e ↦ if v ∈ X then x v else M.f v a e
  f_parents := fun v a b e h ↦ by
    by_cases hv : v ∈ X
    · simp [hv]
    · simp only [if_neg hv]
      exact M.f_parents v a b e fun p hp ↦ h p (by rw [if_neg hv]; exact hp)
  exoProb := M.exoProb
  exoProb_nonneg := M.exoProb_nonneg
  exoProb_tsum := M.exoProb_tsum

omit [Fintype V] in
/-- Forcing a variable only deletes edges, so the submodel inherits the
recursion's hypothesis. This is what keeps `submodel_eval` stated at a submodel
of an evaluable model rather than asking for the hypothesis twice. -/
public instance instIsWellFoundedSubmodel (M : SCM V dom edom)
    [hM : M.IsWellFounded] (X : Finset V) (x : EndoAssignment V dom) :
    (M.submodel X x).IsWellFounded :=
  ⟨Subrelation.wf (fun {p v} hp ↦ by
      simp only [submodel] at hp
      by_cases hv : v ∈ X
      · rw [if_pos hv] at hp; exact absurd hp (Set.notMem_empty p)
      · rwa [if_neg hv] at hp) hM.wf⟩

omit [Fintype V] in
/-- An intervened variable takes its forced value, whatever the exogenous draw. -/
@[simp] public theorem submodel_eval (M : SCM V dom edom) [M.IsWellFounded]
    (X : Finset V) (x : EndoAssignment V dom) (ε : ExoAssignment V edom)
    {v : V} (hv : v ∈ X) :
    (M.submodel X x).eval ε v = x v := by
  rw [(M.submodel X x).eval_eq_f ε v]
  simp [submodel, hv]

omit [Fintype V] in
/-- A variable outside the intervention keeps its own structural function. -/
public theorem submodel_eval_notMem (M : SCM V dom edom) [M.IsWellFounded]
    (X : Finset V) (x : EndoAssignment V dom) (ε : ExoAssignment V edom)
    {v : V} (hv : v ∉ X) :
    (M.submodel X x).eval ε v = M.f v ((M.submodel X x).eval ε) (ε v) := by
  rw [(M.submodel X x).eval_eq_f ε v]
  simp [submodel, hv]

open Classical in
/-- **Definition 2 at any set of variables.** Print: *"Let `M = ⟨E, V, F, P⟩` be an
SCM, `X` a set of variables in `V`, and `x` a particular realization of `X`"* —
a set, with no finiteness, so `X` here is a `Set V` and may be infinite (every even
vertex of an `ℕ`-indexed model, say). Membership is decided classically; the body
only tests `v ∈ X`. `submodel` is the `Finset` case (`submodel_eq_submodelSet`). -/
@[expose] public noncomputable def submodelSet (M : SCM V dom edom) (X : Set V)
    (x : EndoAssignment V dom) : SCM V dom edom where
  dom_nonempty := M.dom_nonempty
  parents := fun v ↦ if v ∈ X then ∅ else M.parents v
  acyclic := fun v hv ↦ M.acyclic v (Relation.TransGen.mono (fun p w hp ↦ by
    by_cases hw : w ∈ X
    · rw [if_pos hw] at hp; exact absurd hp (Set.notMem_empty p)
    · rwa [if_neg hw] at hp) _ _ hv)
  f := fun v a e ↦ if v ∈ X then x v else M.f v a e
  f_parents := fun v a b e h ↦ by
    by_cases hv : v ∈ X
    · simp [hv]
    · simp only [if_neg hv]
      exact M.f_parents v a b e fun p hp ↦ h p (by rw [if_neg hv]; exact hp)
  exoProb := M.exoProb
  exoProb_nonneg := M.exoProb_nonneg
  exoProb_tsum := M.exoProb_tsum

omit [Fintype V] in
/-- The `Finset` submodel is the set submodel at the underlying set. -/
public theorem submodel_eq_submodelSet (M : SCM V dom edom) (X : Finset V)
    (x : EndoAssignment V dom) : M.submodel X x = M.submodelSet (↑X) x := by
  unfold submodel submodelSet
  congr 1
  · funext v
    by_cases hv : v ∈ X <;> simp [hv]
  · funext v a e
    by_cases hv : v ∈ X <;> simp [hv]

omit [Fintype V] in
/-- Forcing any set of variables only deletes edges, so the set submodel inherits
the recursion's hypothesis. -/
public instance instIsWellFoundedSubmodelSet (M : SCM V dom edom)
    [hM : M.IsWellFounded] (X : Set V) (x : EndoAssignment V dom) :
    (M.submodelSet X x).IsWellFounded :=
  ⟨Subrelation.wf (fun {p v} hp ↦ by
      simp only [submodelSet] at hp
      by_cases hv : v ∈ X
      · rw [if_pos hv] at hp; exact absurd hp (Set.notMem_empty p)
      · rwa [if_neg hv] at hp) hM.wf⟩

omit [Fintype V] in
/-- An intervened variable takes its forced value, whatever the exogenous draw,
for an intervention on any set of variables. -/
@[simp] public theorem submodelSet_eval (M : SCM V dom edom) [M.IsWellFounded]
    (X : Set V) (x : EndoAssignment V dom) (ε : ExoAssignment V edom)
    {v : V} (hv : v ∈ X) :
    (M.submodelSet X x).eval ε v = x v := by
  rw [(M.submodelSet X x).eval_eq_f ε v]
  simp [submodelSet, hv]

omit [Fintype V] in
/-- A variable outside a set intervention keeps its own structural function. -/
public theorem submodelSet_eval_notMem (M : SCM V dom edom) [M.IsWellFounded]
    (X : Set V) (x : EndoAssignment V dom) (ε : ExoAssignment V edom)
    {v : V} (hv : v ∉ X) :
    (M.submodelSet X x).eval ε v = M.f v ((M.submodelSet X x).eval ε) (ε v) := by
  rw [(M.submodelSet X x).eval_eq_f ε v]
  simp [submodelSet, hv]

/-- **Soft intervention.** Print: *"a soft intervention on a variable `X` in an
SCM `M` replaces `f^X` with a function `g^X : dom(Pa_X ∪ {E^X}) → dom(X)`"* —
the parents are the same, so acyclicity is inherited unchanged. -/
@[expose] public noncomputable def softIntervention (M : SCM V dom edom)
    (X : Finset V) (g : (v : V) → EndoAssignment V dom → edom v → dom v)
    (hg : ∀ v a b e, (∀ p ∈ M.parents v, a p = b p) → g v a e = g v b e) :
    SCM V dom edom where
  dom_nonempty := M.dom_nonempty
  parents := M.parents
  acyclic := M.acyclic
  f := fun v a e ↦ if v ∈ X then g v a e else M.f v a e
  f_parents := fun v a b e h ↦ by
    by_cases hv : v ∈ X
    · simp only [if_pos hv]; exact hg v a b e h
    · simp only [if_neg hv]; exact M.f_parents v a b e h
  exoProb := M.exoProb
  exoProb_nonneg := M.exoProb_nonneg
  exoProb_tsum := M.exoProb_tsum

omit [Fintype V] in
/-- A soft intervention keeps the parent map, so it keeps the recursion's
hypothesis with it. -/
public instance instIsWellFoundedSoftIntervention (M : SCM V dom edom)
    [hM : M.IsWellFounded] (X : Finset V)
    (g : (v : V) → EndoAssignment V dom → edom v → dom v)
    (hg : ∀ v a b e, (∀ p ∈ M.parents v, a p = b p) → g v a e = g v b e) :
    (M.softIntervention X g hg).IsWellFounded :=
  ⟨hM.wf⟩

end SCM

/-! ## Causal influence diagrams

Print, Definition 3: *"A **causal influence diagram** (CID) is a directed acyclic
graph `G` where the vertex set `V` is partitioned into structure nodes `X`,
decision nodes `D`, and utility nodes `U`. Utility nodes have no children. …
The parents of the decision, `Pa_D`, are also called observations. … Edges into
decisions are called information links."*

`D` is a **set**. Print's *"we will restrict our attention to single-decision
settings with `D = {D}`"* is a scoping remark for the theorems, not part of
Definition 3, so single-decision enters as a hypothesis where a result needs it
rather than as a field here. -/

/-- The three kinds of vertex a CID partitions its variables into. -/
public inductive NodeKind
  | /-- A structure node: an ordinary chance variable. -/ structureNode
  | /-- A decision node: the agent chooses its mechanism. -/ decision
  | /-- A utility node: a real-valued score with no children. -/ utility
  deriving DecidableEq

/-- **Definition 3.** A causal influence diagram. -/
public structure CID (V : Type*) [DecidableEq V] where
  /-- The parents of each vertex, a subset with no cardinality bound. -/
  parents : V → Set V
  /-- *"a directed **acyclic** graph"*, which is print's condition and nothing
  more: no vertex is reachable from itself along edges.

  Definition 3 is a graph and evaluates nothing, so it needs no more than this.
  Well-foundedness -- strictly stronger here, and what `SCM` carries -- enters at
  `SCIM`, which is where print first writes a model that is evaluated. -/
  acyclic : ∀ v, ¬ Relation.TransGen (fun p v ↦ p ∈ parents v) v v
  /-- The partition of `V` into structure, decision and utility nodes. -/
  kind : V → NodeKind
  /-- *"Utility nodes have no children."* Stated in print and implied by nothing
  else here, so it is a field. -/
  utility_childless :
    ∀ u, kind u = NodeKind.utility → ∀ v, u ∉ parents v

omit [Fintype V] in
/-- **What Definition 4 needs and Definition 3 does not.**

`CID.acyclic` is print's *"directed acyclic graph"* and it is all Definition 3
asks for, because a diagram evaluates nothing. Definition 4's model does
evaluate -- one definition later, `V*(M) = max_π Eπ[U]` runs `W(ε)` in `Mπ` --
and on an acyclic diagram that is not well-founded that recursion names nothing
unique. So the strengthening lives here, as a property of a diagram, and
`SCIM` itself carries print's tuple. -/
public class CID.IsWellFounded (G : CID V) : Prop where
  /-- The diagram's parent relation is well-founded. -/
  wf : WellFounded fun p v ↦ p ∈ G.parents v

/-- **At a finite vertex set the hypothesis is free**: print's *"acyclic"* alone
gives it, because a transitive irreflexive relation on a finite type is
well-founded, and `CID.acyclic` is exactly irreflexivity of the transitive
closure.

This does **not** collapse the distinction the class exists for. At unbounded
`V` the two really do differ — `chainParents` on `ℤ` is acyclic, is not
well-founded, and admits two assignments satisfying `eval_eq_f`, which is why
print's *"recursive application"* names nothing unique there. What this says is
narrower and worth having: **wherever a statement already carries `[Fintype V]`,
asking for the instance on top of `acyclic` asks for nothing.** Every such
statement can drop the hypothesis, and `CID.admitsICI_iff` does.

Not an `instance`: making it one would have `[Fintype V]` silently satisfy every
`IsWellFounded` goal in the tree, which would hide the axis at exactly the
declarations the coverage audit grades on it. -/
public theorem CID.isWellFounded_of_fintype (G : CID V) : G.IsWellFounded :=
  ⟨Subrelation.wf (r := Relation.TransGen fun p v ↦ p ∈ G.parents v)
    (fun h ↦ Relation.TransGen.single h)
    (@Finite.wellFounded_of_trans_of_irrefl V _ _
      ⟨fun _ _ _ h₁ h₂ ↦ h₁.trans h₂⟩ ⟨G.acyclic⟩)⟩

namespace CID

variable (G : CID V)

/-- `V ∈ 𝐃`, as a **property** rather than `Finset` membership.

Print writes *"the vertex set `V` is partitioned into structure nodes `X`,
decision nodes `D`, and utility nodes `U`"*, and a partition is a property of
each vertex. Reading it that way is not a convenience: it is what lets `CID` and
`SCIM` be stated without assuming the vertex set finite, which print never does.
The `Finset` forms below are the same sets whenever `V` is a `Fintype`, and
`mem_decisions_iff` / `mem_utilities_iff` say so.

Nothing else in `CID` bounds the graph either: `parents` is a `Set`, so a
vertex may have infinitely many parents, and `acyclic` is print's own condition
rather than a rank. `SCIM` is where a strictly stronger acyclicity appears,
because that is where a model is evaluated. -/
@[expose] public def IsDecision (v : V) : Prop := G.kind v = NodeKind.decision

/-- `V ∈ 𝐔`, as a property. See `IsDecision`. -/
@[expose] public def IsUtility (v : V) : Prop := G.kind v = NodeKind.utility

public instance instDecidableIsDecision (v : V) : Decidable (G.IsDecision v) := by
  unfold IsDecision; infer_instance

public instance instDecidableIsUtility (v : V) : Decidable (G.IsUtility v) := by
  unfold IsUtility; infer_instance

/-- The decision nodes `𝐃`. -/
@[expose] public def decisions : Finset V :=
  Finset.univ.filter fun v ↦ G.kind v = NodeKind.decision

/-- The utility nodes `𝐔`. -/
@[expose] public def utilities : Finset V :=
  Finset.univ.filter fun v ↦ G.kind v = NodeKind.utility

/-- The structure nodes `𝐗`. -/
@[expose] public def structureNodes : Finset V :=
  Finset.univ.filter fun v ↦ G.kind v = NodeKind.structureNode

@[simp] public theorem mem_decisions_iff (v : V) : v ∈ G.decisions ↔ G.IsDecision v := by
  simp [decisions, IsDecision]

@[simp] public theorem mem_utilities_iff (v : V) : v ∈ G.utilities ↔ G.IsUtility v := by
  simp [utilities, IsUtility]

/-- *"The parents of the decision, `Pa_D`, are also called observations."* -/
@[expose] public def observations (d : V) : Set V := G.parents d

/-- The three kinds partition the vertices. -/
public theorem decisions_disjoint_utilities :
    Disjoint G.decisions G.utilities := by
  classical
  refine Finset.disjoint_left.mpr fun v hv hv' ↦ ?_
  simp only [decisions, utilities, Finset.mem_filter] at hv hv'
  exact absurd (hv.2.symm.trans hv'.2) (by decide)

/-- ***Desc_d***, the vertices reachable from `d` along edges, `d` included.
Print uses *Desc_D* without defining it; this is the reflexive-transitive closure
of the edge relation, which is what the word means.

**Reflexive on purpose.** The decision is its own descendant, so the invariance
below is not claimed at the decision. Under a *proper* reading `D` would fall
outside *Desc_D* and print's sentence would assert that `Pr^π(d)` does not depend
on `π`, which is false. RE24's `Anc`/`Desc` are proper — a different paper and a
different sentence — and `Model.properAncestors` / `Model.properDescendants` are
where that reading lives. -/
@[expose] public def IsDescendant (d v : V) : Prop :=
  Relation.ReflTransGen (fun a b ↦ a ∈ G.parents b) d v

/-- **Print's *"not in *Desc_D*"***, at the atlas's decision *set*. Print has
already restricted to `𝐃 = {D}` where it writes this, so at that restriction
this is print's condition exactly; where the atlas allows several decisions it
is the condition on each. -/
@[expose] public def NotDownstream (v : V) : Prop :=
  ∀ d, G.IsDecision d → ¬ G.IsDescendant d v

omit [Fintype V] in
/-- A vertex outside every decision's descendants is not itself a decision: a
vertex is its own descendant. -/
public theorem not_isDecision_of_notDownstream {v : V} (hv : G.NotDownstream v) :
    ¬ G.IsDecision v :=
  fun h ↦ hv v h Relation.ReflTransGen.refl

omit [Fintype V] in
/-- The complement of the decisions' descendants is closed under taking parents,
which is what lets an induction on the parent relation stay inside it. -/
public theorem notDownstream_of_mem_parents {v : V} (hv : G.NotDownstream v)
    {p : V} (hp : p ∈ G.parents v) : G.NotDownstream p :=
  fun d hd hdesc ↦ hv d hd (hdesc.tail hp)

/-- Print's single-decision restriction, as a hypothesis rather than a field. -/
@[expose] public def IsSingleDecision : Prop := ∃ d : V, G.decisions = {d}

end CID


/-! ## Structural causal influence models

*"For our new incentive concepts, we define a hybrid of the influence diagram
and the SCM. Such a model … has structure and utility nodes with associated
functions, exogenous variables with an associated probability distributions, and
decision nodes, **without any function at all, until one is selected by an
agent**."*

That asymmetry is the whole content of Definition 4, and it is why `SCIM.f` is a
function of a proof that the vertex is **not** a decision rather than a total
family with an ignored entry: a total one would make two models differing only
in junk at a decision node distinct, which print's tuple cannot express.

The order below is forced by print. A policy *"turns a SCIM `M` into an SCM
`Mπ := ⟨E, V, F ∪ {π}, P⟩`"*, and `Prπ` and `Eπ` are *"probabilities and
expectations with respect to `Mπ`"* — so expected utility is defined by
evaluating the induced `SCM`, not by a formula written directly on the SCIM.
Doing the latter would make `Eπ[U]` an atlas definition that happens to agree
with print rather than print's own.
-/

/-- **Definition 4.** A structural causal influence model.

`𝐃` is a set. Print's *"we will restrict our attention to single-decision
settings with `𝐃 = {D}`"* scopes the theorems, not the definition, and it enters
here as `CID.IsSingleDecision` wherever a statement needs it. -/
public structure SCIM (V : Type*) [DecidableEq V] (dom edom : V → Type*) where
  /-- Every endogenous variable has at least one state. -/
  dom_nonempty : ∀ v, Nonempty (dom v)
  /-- *"`G` is a CID with finite-domain variables `V`"*. -/
  graph : CID V
  /-- *"where utility variable domains are a subset of `ℝ`"*: each utility
  vertex reads its states as reals. -/
  utilityValue : (u : V) → graph.IsUtility u → dom u → ℝ
  /-- A *subset* of `ℝ`, so distinct states are distinct reals. -/
  utilityValue_injective :
    ∀ u (hu : graph.IsUtility u), Function.Injective (utilityValue u hu)
  /-- `F = {f^V}_{V ∈ 𝐕 \ 𝐃}`. Decision vertices have no structural function
  until a policy supplies one, which is what the non-membership proof records. -/
  f : (v : V) → ¬ graph.IsDecision v →
    EndoAssignment V dom → edom v → dom v
  /-- *"specify how each non-decision endogenous variable depends on its parents
  in `G` and its associated exogenous variable"*. -/
  f_parents : ∀ v (hv : ¬ graph.IsDecision v) a b e,
    (∀ p ∈ graph.parents v, a p = b p) → f v hv a e = f v hv b e
  /-- `P`, one marginal per exogenous variable; independence is the product, as
  in `SCM`. -/
  exoProb : (v : V) → edom v → ℝ
  /-- Each marginal is nonnegative. -/
  exoProb_nonneg : ∀ v e, 0 ≤ exoProb v e
  /-- Each marginal is a probability distribution, unconditionally summed so
  that it says what print says at a domain of any size. -/
  exoProb_tsum : ∀ v, ∑' e : edom v, exoProb v e = 1

namespace SCIM

variable (M : SCIM V dom edom)

/-- **A policy.** *"The task is to select a structural function for `D` in the
form of a policy `π : dom(Pa_D ∪ {E^D}) → dom(D)`. The exogenous variable `E^D`
provides randomness to allow the policy to be a stochastic function of its
endogenous parents `Pa_D`."*

Print writes one `π` because it has restricted to a single decision. This is one
structural function per decision vertex; `policy_ext_single` proves that at
print's restriction it is exactly print's datum. Indexing by the decision
subtype rather than by a membership proof keeps `withPolicy` free of transports
between `dom v` and `dom d`. -/
public abbrev Policy : Type _ :=
  {π : (d : {d : V // M.graph.IsDecision d}) →
        EndoAssignment V dom → edom d.1 → dom d.1 //
    ∀ d a b e, (∀ p ∈ M.graph.parents d.1, a p = b p) → π d a e = π d b e}

/-- A policy may ignore its observations, so one always exists. -/
public instance instNonemptyPolicy : Nonempty M.Policy :=
  ⟨⟨fun d _ _ ↦ (M.dom_nonempty d.1).some, fun _ _ _ _ _ ↦ rfl⟩⟩

/-- Two policies agreeing at the one decision are equal. This is what makes
`Policy` print's `π` at *"single-decision settings with `𝐃 = {D}`"*. -/
public theorem policy_ext_single {d : V} (hd : M.graph.decisions = {d})
    {π π' : M.Policy}
    (h : ∀ (hd' : M.graph.IsDecision d) a e, π.1 ⟨d, hd'⟩ a e = π'.1 ⟨d, hd'⟩ a e) :
    π = π' := by
  refine Subtype.ext (funext fun v ↦ ?_)
  obtain ⟨v, hv⟩ := v
  have : v = d := by
    have hmem : v ∈ M.graph.decisions := (M.graph.mem_decisions_iff v).mpr hv
    rw [hd, Finset.mem_singleton] at hmem
    exact hmem
  subst this
  exact funext fun a ↦ funext fun e ↦ h hv a e

/-- **`Mπ`.** *"The specification of a policy turns a SCIM `M` into an SCM
`Mπ := ⟨E, V, F ∪ {π}, P⟩`."* -/
@[expose] public noncomputable def withPolicy (π : M.Policy) : SCM V dom edom where
  dom_nonempty := M.dom_nonempty
  parents := M.graph.parents
  acyclic := M.graph.acyclic
  f := fun v a e ↦
    if h : M.graph.IsDecision v then π.1 ⟨v, h⟩ a e else M.f v h a e
  f_parents := by
    intro v a b e hab
    by_cases h : M.graph.IsDecision v
    · rw [dif_pos h, dif_pos h]
      exact π.2 ⟨v, h⟩ a b e hab
    · rw [dif_neg h, dif_neg h]
      exact M.f_parents v h a b e hab
  exoProb := M.exoProb
  exoProb_nonneg := M.exoProb_nonneg
  exoProb_tsum := M.exoProb_tsum

omit [Fintype V] in
/-- `Mπ` keeps the diagram's parents, so a well-founded diagram gives an
evaluable `Mπ`. This is the instance that carries Definition 4's recursion into
Definition 5's maximum. -/
public instance instIsWellFoundedWithPolicy [hG : M.graph.IsWellFounded]
    (π : M.Policy) : (M.withPolicy π).IsWellFounded :=
  ⟨hG.wf⟩

omit [Fintype V] in
/-- `Mπ` keeps the diagram's parents, so *"with the resulting SCM, the standard
definitions of causal interventions apply"* at the diagram's own edges. -/
@[simp] public theorem withPolicy_parents (π : M.Policy) :
    (M.withPolicy π).parents = M.graph.parents := rfl

omit [Fintype V] in
/-- A non-decision vertex keeps its structural function in `Mπ`. -/
public theorem withPolicy_f_notMem (π : M.Policy) {v : V}
    (hv : ¬ M.graph.IsDecision v) (a : EndoAssignment V dom) (e : edom v) :
    (M.withPolicy π).f v a e = M.f v hv a e := by
  simp [withPolicy, dif_neg hv]

omit [Fintype V] in
/-- A decision vertex takes the policy as its structural function in `Mπ`. -/
public theorem withPolicy_f_mem (π : M.Policy) {d : V}
    (hd : M.graph.IsDecision d) (a : EndoAssignment V dom) (e : edom d) :
    (M.withPolicy π).f d a e = π.1 ⟨d, hd⟩ a e := by
  simp [withPolicy, dif_pos hd]

omit [Fintype V] in
/-- **Print's invariance sentence, at the level of `W(ε)`.** Two policies give
the same value at every vertex outside the decisions' descendants. `Mπ` and
`Mπ'` share the diagram's parent map and differ only at decision vertices, and a
vertex outside *Desc_𝐃* is not a decision and has no such vertex among its
ancestors. -/
public theorem eval_withPolicy_eq_of_notDownstream [M.graph.IsWellFounded]
    (π π' : M.Policy) (ε : ExoAssignment V edom) {v : V}
    (hv : M.graph.NotDownstream v) :
    (M.withPolicy π).eval ε v = (M.withPolicy π').eval ε v :=
  SCM.eval_eq_of_f_agree (M.withPolicy π) (M.withPolicy π') (fun _ ↦ rfl)
    {w | M.graph.NotDownstream w}
    (fun _ hw _ hp ↦ M.graph.notDownstream_of_mem_parents hw hp)
    (fun w hw ↦ by
      funext a e
      simp [withPolicy, dif_neg (M.graph.not_isDecision_of_notDownstream hw)])
    ε v hv

/-- **Print's sentence.** *"For a set of variables `X` not in *Desc_D*,
`Pr^π(x)` is independent of `π` and we simply write `Pr(x)`."*

Print asserts this without proof, one paragraph after Definition 4; it is what
makes the *"simply write `Pr(x)`"* notation well defined, and it is what
underwrites comparing `V*(M_{X↛D})` with `V*(M)` at Definition 5. -/
public theorem marginal_withPolicy_eq_of_notDownstream
    [∀ v, Fintype (edom v)] [∀ v, Fintype (dom v)] [∀ v, DecidableEq (dom v)]
    [M.graph.IsWellFounded]
    (π π' : M.Policy) (X : Finset V) (hX : ∀ c ∈ X, M.graph.NotDownstream c)
    (x : EndoAssignment V dom) :
    (M.withPolicy π).marginal X x = (M.withPolicy π').marginal X x := by
  classical
  rw [SCM.marginal_eq_sum_exo, SCM.marginal_eq_sum_exo]
  refine Finset.sum_congr (Finset.filter_congr fun ε _ ↦ ?_) (fun ε _ ↦ rfl)
  constructor
  · intro h c hc
    rw [← M.eval_withPolicy_eq_of_notDownstream π π' ε (hX c hc)]
    exact h c hc
  · intro h c hc
    rw [M.eval_withPolicy_eq_of_notDownstream π π' ε (hX c hc)]
    exact h c hc

omit [Fintype V] in
/-- **Print's sentence, on print's own formula, at any vertex set.** *"For a set
of variables `X` not in *Desc_D*, `Pr^π(x)` is independent of `π`"*
(ec21-policy-invariance, PDF p. 3), with `Pr^π(x)` read through print's
`Pr(W = w) = Σ_{ε | W(ε) = w} P(ε)` (`SCM.sumProb`).

No finiteness, countability, summability or measurability hypothesis: the two
sums run over the same draws, because the evaluations agree off *Desc_𝐃*
(`SCIM.eval_withPolicy_eq_of_notDownstream`), and weigh them by the same
exogenous marginals. -/
public theorem sumProb_withPolicy_eq_of_notDownstream [M.graph.IsWellFounded]
    (π π' : M.Policy) (X : Set V) (hX : ∀ v ∈ X, M.graph.NotDownstream v)
    (x : EndoAssignment V dom) :
    (M.withPolicy π).sumProb X x = (M.withPolicy π').sumProb X x := by
  unfold SCM.sumProb
  refine tsum_congr_set_coe (fun ε : ExoAssignment V edom ↦ ∏' v, M.exoProb v (ε v)) ?_
  ext ε
  simp only [Set.mem_ofPred_eq]
  refine forall₂_congr fun v hv ↦ ?_
  rw [M.eval_withPolicy_eq_of_notDownstream π π' ε (hX v hv)]

/-! ### Definition 4's and Definition 5's finiteness

Print writes *"finite"* twice and both times inside Definition 4, qualifying
**domains**. The expectation and the maximum over policies are exactly where
that bites, so the instances sit here and nowhere above. -/

section FiniteDecision

variable [∀ v, Fintype (edom v)] [∀ v, Fintype (dom v)] [∀ v, DecidableEq (dom v)]

/-- **`Eπ[U]`**, with `U := Σ_{U ∈ 𝐔} U`. The expectation is taken in `Mπ`,
which is where print defines `Eπ`. -/
@[expose] public noncomputable def expectedUtility [M.graph.IsWellFounded]
    (π : M.Policy) : ℝ :=
  ∑ ε : ExoAssignment V edom,
    (M.withPolicy π).exoJoint ε *
      ∑ u ∈ M.graph.utilities.attach,
        M.utilityValue u.1 ((M.graph.mem_utilities_iff u.1).mp u.2)
          ((M.withPolicy π).eval ε u.1)

/-- **An optimal policy**: *"any policy `π` that maximises `Eπ[U]`"*. -/
@[expose] public def IsOptimalPolicy [M.graph.IsWellFounded] (π : M.Policy) : Prop :=
  ∀ π' : M.Policy, M.expectedUtility π' ≤ M.expectedUtility π

/-- The policy type is finite, which is what makes `optimalValue` a maximum
rather than a supremum print never wrote.

The instance is classical. With `parents` a `Set` rather than a `Finset`, a
policy's defining property -- that it reads only its observations -- quantifies
over a set with no decidable membership, so the subtype carries no decidable
predicate. Finiteness itself is unaffected, and nothing downstream computes with
this. -/
public noncomputable instance instFintypePolicy : Fintype M.Policy := by
  classical exact Fintype.ofFinite _

/-- **`V*(M) = max_π Eπ[U]`**, the first clause of Definition 5. The policy type
is finite, so this is a maximum, and `exists_isOptimalPolicy` exhibits a policy
attaining it. -/
@[expose] public noncomputable def optimalValue [M.graph.IsWellFounded] : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty M.expectedUtility

omit [∀ v, DecidableEq (dom v)] in
public theorem expectedUtility_le_optimalValue [M.graph.IsWellFounded]
    (π : M.Policy) :
    M.expectedUtility π ≤ M.optimalValue := by
  unfold optimalValue
  exact Finset.le_sup' M.expectedUtility (Finset.mem_univ π)

omit [∀ v, DecidableEq (dom v)] in
/-- Print writes a `max`, and this is what makes it one. -/
public theorem exists_isOptimalPolicy [M.graph.IsWellFounded] :
    ∃ π : M.Policy, M.IsOptimalPolicy π ∧ M.expectedUtility π = M.optimalValue := by
  obtain ⟨π, -, hπ⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := M.Policy)) M.expectedUtility
  have hval : M.expectedUtility π = M.optimalValue := by
    unfold optimalValue
    exact hπ.symm
  exact ⟨π, fun π' ↦ hval ▸ M.expectedUtility_le_optimalValue π', hval⟩

end FiniteDecision

omit [Fintype V] in
/-- Removing an information link only deletes edges. This is the one fact
`removeInfoLink` needs twice: once to inherit the diagram's acyclicity and once
to inherit its well-foundedness. -/
public theorem removeInfoLink_sub (M : SCIM V dom edom) {d x a b : V}
    (hab : a ∈ if b = d then M.graph.parents d \ {x} else M.graph.parents b) :
    a ∈ M.graph.parents b := by
  by_cases hb : b = d
  · subst hb; rw [if_pos rfl] at hab; exact hab.1
  · rwa [if_neg hb] at hab

/-- **`M_{X↛D}`**: *"`M` modified by removing any information link `X → D`."*

Defined at a decision vertex, because erasing a parent of a vertex that *has* a
structural function would falsify that vertex's `f_parents`. -/
@[expose] public noncomputable def removeInfoLink {d : V}
    (hd : M.graph.IsDecision d) (x : V) : SCIM V dom edom where
  dom_nonempty := M.dom_nonempty
  graph :=
    { M.graph with
      parents := fun v ↦
        if v = d then M.graph.parents d \ {x} else M.graph.parents v
      acyclic := fun v hv ↦
        M.graph.acyclic v
          (Relation.TransGen.mono (fun a b hab ↦ removeInfoLink_sub M hab) _ _ hv)
      utility_childless := by
        intro u hu v
        by_cases hv : v = d
        · subst hv
          rw [if_pos rfl]
          exact fun h ↦ M.graph.utility_childless u hu v h.1
        · simp only [if_neg hv]
          exact M.graph.utility_childless u hu v }
  utilityValue := M.utilityValue
  utilityValue_injective := M.utilityValue_injective
  f := M.f
  f_parents := by
    intro v hv a b e hab
    refine M.f_parents v hv a b e fun p hp ↦ ?_
    have hvd : v ≠ d := fun h ↦ hv (h ▸ hd)
    exact hab p (by simpa [if_neg hvd] using hp)
  exoProb := M.exoProb
  exoProb_nonneg := M.exoProb_nonneg
  exoProb_tsum := M.exoProb_tsum

omit [Fintype V] in
/-- Removing an information link only deletes edges, so `M_{X↛D}` is evaluable
whenever `M` is. Without this instance `IsMaterial` would have to ask for the
hypothesis twice, once at each side of print's inequality. -/
public instance instIsWellFoundedRemoveInfoLink [hG : M.graph.IsWellFounded]
    {d : V} (hd : M.graph.IsDecision d) (x : V) :
    (M.removeInfoLink hd x).graph.IsWellFounded :=
  ⟨Subrelation.wf (fun {_ _} hab ↦ removeInfoLink_sub M hab) hG.wf⟩

/-- **Definition 5 (Materiality).** *"The observation `X ∈ Pa_D` is material if
`V*(M_{X↛D}) < V*(M)`."* -/
@[expose] public def IsMaterial [∀ v, Fintype (edom v)] [∀ v, Fintype (dom v)]
    [∀ v, DecidableEq (dom v)] [M.graph.IsWellFounded] {d : V}
    (hd : M.graph.IsDecision d) {x : V}
    (_hx : x ∈ M.graph.parents d) : Prop :=
  (M.removeInfoLink hd x).optimalValue < M.optimalValue

end SCIM

/-! ## Probability laws without a finite vertex set

The product measure uses the existing finite-domain marginals at any vertex
cardinality. Evaluation laws require measurability explicitly; arbitrary
functions of infinitely many parents need not be measurable. Expected utility
and Definition 5 have law forms (`SCIM.expectedUtilityLaw`,
`SCIM.optimalValueLaw`, `SCIM.IsMaterialLaw`, below); the conditional expectation
of `Causal.Incentive` is still a finite sum.
-/

namespace SCM

open MeasureTheory

variable {V : Type*} [DecidableEq V] {dom edom : V → Type*}
  [∀ v, MeasurableSpace (edom v)] [∀ v, MeasurableSpace (dom v)]
  (M : SCM V dom edom)

omit [∀ v, MeasurableSpace (edom v)] [∀ v, MeasurableSpace (dom v)] in
/-- **The marginals are summable**, which `exoProb_tsum` says rather than
assumes: an unsummable family has unconditional sum zero, and print's is one. -/
public theorem exoProb_summable (v : V) : Summable (M.exoProb v) := by
  by_contra hns
  have h := M.exoProb_tsum v
  rw [tsum_eq_zero_of_not_summable hns] at h
  exact zero_ne_one h

omit [∀ v, MeasurableSpace (edom v)] [∀ v, MeasurableSpace (dom v)] in
/-- The existing exogenous marginal as a probability mass function, at a domain
of any size. -/
@[expose] public noncomputable def exoPMF (v : V) : PMF (edom v) :=
  ⟨fun e ↦ ENNReal.ofReal (M.exoProb v e), by
    have h := ENNReal.ofReal_tsum_of_nonneg (M.exoProb_nonneg v) (M.exoProb_summable v)
    rw [M.exoProb_tsum v, ENNReal.ofReal_one] at h
    rw [h]
    exact ENNReal.summable.hasSum⟩

/-- Independent exogenous draws over an arbitrary vertex set. This is a
probability measure even when the space of complete assignments is uncountable. -/
@[expose] public noncomputable def exoLaw : ProbabilityMeasure (ExoAssignment V edom) :=
  ⟨Measure.infinitePi (fun v ↦ (M.exoPMF v).toMeasure), inferInstance⟩

omit [∀ v, MeasurableSpace (dom v)] in
/-- Each coordinate of the product recovers the model's original marginal. -/
public theorem exoLaw_map_eval (v : V) :
    (M.exoLaw : Measure (ExoAssignment V edom)).map (fun ε ↦ ε v) =
      (M.exoPMF v).toMeasure :=
  Measure.infinitePi_map_eval _ v

omit [∀ v, MeasurableSpace (dom v)] in
/-- At a finite vertex set, this is Mathlib's ordinary finite product measure. -/
public theorem exoLaw_eq_pi [Fintype V] :
    (M.exoLaw : Measure (ExoAssignment V edom)) =
      Measure.pi (fun v ↦ (M.exoPMF v).toMeasure) :=
  Measure.infinitePi_eq_pi _

omit [∀ v, MeasurableSpace (dom v)] in
/-- The finite product has exactly the old exogenous joint weights. This is
the bridge needed to recover the existing finite-sum calculations.

The singleton-measurability instance is where print's Definition 4 finiteness
shows up in the measure layer: a singleton of an arbitrary measurable space need
not be measurable. -/
public theorem exoLaw_singleton [Fintype V] [∀ v, MeasurableSingletonClass (edom v)]
    (ε : ExoAssignment V edom) :
    (M.exoLaw : Measure (ExoAssignment V edom)) {ε} = ENNReal.ofReal (M.exoJoint ε) := by
  rw [M.exoLaw_eq_pi, Measure.pi_singleton]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _), exoJoint]
  exact (ENNReal.ofReal_prod_of_nonneg (fun v _ ↦ M.exoProb_nonneg v (ε v))).symm

/-- Joint law of any set of evaluated variables. Measurability is checked before
a law can be constructed, so a nonmeasurable map cannot silently return zero. -/
@[expose] public noncomputable def observableLaw [M.IsWellFounded] (X : Set V)
    (hm : Measurable (fun ε : ExoAssignment V edom ↦ fun v : X ↦ M.eval ε v)) :
    ProbabilityMeasure ((v : X) → dom v) :=
  M.exoLaw.map hm.aemeasurable

/-- **`Pr(W = w)` as a distribution rather than a finite sum.** The law of the
complete evaluation, which exists at any vertex set because `SCM.exoLaw` does.

`SCM.jointProb` is a sum over the fibre of `eval`, so it exists only at
`[Fintype V]`; print's *"this induces a joint distribution"* asks for a
distribution and names no cardinality. `SCM.endoLaw_singleton` is the converting
lemma. Measurability is required for the same reason `SCM.observableLaw` requires
it. -/
@[expose] public noncomputable def endoLaw [M.IsWellFounded]
    (hm : Measurable fun ε : ExoAssignment V edom ↦ M.eval ε) :
    ProbabilityMeasure (EndoAssignment V dom) :=
  M.exoLaw.map hm.aemeasurable

omit [DecidableEq V] in
/--
**At a finite vertex set the measurability side condition vanishes.** The
exogenous space is then a finite product of finite discrete spaces, so every map
out of it is measurable and `observableLaw` carries no hypothesis print does not
have. Beyond a finite vertex set the hypothesis is real: an arbitrary function of
infinitely many parents need not be measurable.
-/
public theorem measurable_exo [Fintype V] [∀ v, DiscreteMeasurableSpace (edom v)]
    [∀ v, Countable (edom v)]
    {α : Type*} [MeasurableSpace α] (f : ExoAssignment V edom → α) : Measurable f :=
  .of_discrete

/-- **The induced joint is the law's singleton mass.** So `SCM.jointProb` is a
computation of print's distribution and not a second reading of it. -/
public theorem endoLaw_singleton [Fintype V] [∀ v, Fintype (edom v)]
    [∀ v, Fintype (dom v)] [∀ v, DecidableEq (dom v)]
    [∀ v, MeasurableSingletonClass (edom v)] [∀ v, DiscreteMeasurableSpace (edom v)]
    [∀ v, Countable (edom v)] [∀ v, MeasurableSingletonClass (dom v)]
    [M.IsWellFounded] (w : EndoAssignment V dom) :
    (M.endoLaw (measurable_exo _) : Measure (EndoAssignment V dom)).real {w} = M.jointProb w := by
  classical
  have hset : (fun ε : ExoAssignment V edom ↦ M.eval ε) ⁻¹' {w}
      = ↑(Finset.univ.filter fun ε : ExoAssignment V edom ↦ M.eval ε = w) := by
    ext ε; simp
  rw [endoLaw]
  show (((M.exoLaw : Measure (ExoAssignment V edom)).map
    (fun ε ↦ M.eval ε)).real {w}) = _
  rw [measureReal_def, Measure.map_apply (measurable_exo _) (measurableSet_singleton w),
    hset, ← measureReal_def, ← sum_measureReal_singleton, jointProb]
  exact Finset.sum_congr rfl fun ε _ ↦ by
    rw [measureReal_def, exoLaw_singleton, ENNReal.toReal_ofReal (M.exoJoint_nonneg ε)]

end SCM

namespace SCIM

variable {V : Type*} [DecidableEq V] {dom edom : V → Type*}
  [∀ v, MeasurableSpace (edom v)] [∀ v, MeasurableSpace (dom v)]
  (M : SCIM V dom edom)

/-! ## `Eπ[U]` against print's distribution rather than as a finite sum

`SCIM.expectedUtility` above is a sum over `ExoAssignment V edom`, which exists
only at `[Fintype V]`. Print's `Eπ[U]` is an expectation under `P(ε)`, and `P(ε)`
denotes at any vertex set — it is the product measure `SCM.exoLaw`. So the finite
sum is a computation of print's object and not print's object, and
`SCIM.expectedUtilityLaw_eq` is the converting lemma that says so.

**What stays finite here, and why that is print's own.** `𝐔` is a `Fintype`,
carried as an instance on the subtype rather than derived from a finite vertex
set. Print's `U := Σ_{U ∈ 𝐔} U` is a sum with no convergence clause attached, so
at infinitely many utility vertices print's own expression names nothing; the
instance is what makes it denote, exactly as `CID.IsWellFounded` is what makes
*"recursive application"* denote. It is not a bound on `V`.

**And measurability is asked for rather than assumed.** At an unbounded vertex
set an evaluation reading infinitely many parents need not be measurable, and a
Bochner integral of a nonmeasurable function is silently zero. The hypothesis is
the same one `SCM.observableLaw` carries, discharged by `SCM.measurable_exo`
wherever `V` is finite, so nothing print asserts is bought with a condition print
lacks.
-/

open MeasureTheory in
/-- **`Eπ[U]`, as print's expectation.** The integral of the total utility under
the law of the utility vertices in `Mπ`.

The space integrated over is `(u : 𝐔) → dom u`, which is finite whenever
`𝐔` is, so the integrand is integrable for free; all of the unboundedness lives
in `SCM.exoLaw`, which is where print puts it. -/
@[expose] public noncomputable def expectedUtilityLaw [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] (π : M.Policy)
    (hm : Measurable fun ε : ExoAssignment V edom ↦
      fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π).eval ε u.1) : ℝ :=
  ∫ w, ∑ u : {v : V // M.graph.IsUtility v}, M.utilityValue u.1 u.2 (w ⟨u.1, u.2⟩)
    ∂((M.withPolicy π).observableLaw {v : V | M.graph.IsUtility v} hm :
      Measure ((v : {v : V | M.graph.IsUtility v}) → dom v))

open MeasureTheory in
/-- **The finite sum is a computation of print's expectation.**

At a finite vertex set the measurability side condition is free
(`SCM.measurable_exo`), the exogenous space is finite, and the integral against
the product measure is the weighted sum `SCIM.expectedUtility` already writes.
So every result stated about that sum is a result about print's `Eπ[U]`. -/
public theorem expectedUtilityLaw_eq [Fintype V] [∀ v, Fintype (edom v)]
    [∀ v, Fintype (dom v)] [∀ v, DecidableEq (dom v)]
    [∀ v, DiscreteMeasurableSpace (edom v)] [∀ v, Countable (edom v)]
    [∀ v, DiscreteMeasurableSpace (dom v)] [∀ v, Countable (dom v)]
    [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] (π : M.Policy) :
    M.expectedUtilityLaw π (SCM.measurable_exo _) = M.expectedUtility π := by
  classical
  rw [expectedUtilityLaw, SCM.observableLaw]
  rw [show (((M.withPolicy π).exoLaw.map
      (SCM.measurable_exo (V := V) (edom := edom) _).aemeasurable :
        ProbabilityMeasure ((v : {v : V | M.graph.IsUtility v}) → dom v)) :
      Measure ((v : {v : V | M.graph.IsUtility v}) → dom v)) =
      ((M.withPolicy π).exoLaw : Measure (ExoAssignment V edom)).map
        (fun ε ↦ fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π).eval ε u.1) from rfl]
  rw [integral_map (SCM.measurable_exo _).aemeasurable
    (Measurable.aestronglyMeasurable Measurable.of_discrete)]
  rw [integral_fintype (Integrable.of_finite)]
  rw [expectedUtility]
  refine Finset.sum_congr rfl fun ε _ ↦ ?_
  have hmass : ((M.withPolicy π).exoLaw : Measure (ExoAssignment V edom)).real {ε}
      = (M.withPolicy π).exoJoint ε := by
    rw [Measure.real, SCM.exoLaw_singleton,
      ENNReal.toReal_ofReal ((M.withPolicy π).exoJoint_nonneg ε)]
  rw [hmass, smul_eq_mul]
  congr 1
  rw [Finset.attach_eq_univ]
  exact Fintype.sum_equiv
    (Equiv.subtypeEquivRight fun v ↦ (M.graph.mem_utilities_iff v).symm) _ _ fun _ ↦ rfl

/-- **An optimal policy, at an unbounded vertex set.** Print's *"any policy `π`
that maximises `Eπ[U]`"* is a comparison and not an attainment claim, so it
denotes wherever the expectation does.

**This is the half of Definition 5's sentence that generalises.** The other half
— that a maximiser *exists* — needs the policy space finite, not the vertex set:
`SCIM.exists_isOptimalPolicyLaw` proves it at any vertex set under
`[Finite M.Policy]` (which `SCIM.finite_policy` derives from finitely many
decisions with finite `Pa^D`), and `SCIM.exists_isOptimalPolicy` is the finite-sum
form. Print states no condition delivering a maximiser over an unbounded policy
space, so `SCIM.optimalValueLaw` takes attainment as print's presupposition
(a hypothesis `∃ π, IsOptimalPolicyLaw π hm`) and finiteness of the policies is
one way, not the only way, to discharge it. -/
@[expose] public def IsOptimalPolicyLaw [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] (π : M.Policy)
    (hm : ∀ π' : M.Policy, Measurable fun ε : ExoAssignment V edom ↦
      fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π').eval ε u.1) : Prop :=
  ∀ π' : M.Policy, M.expectedUtilityLaw π' (hm π') ≤ M.expectedUtilityLaw π (hm π)

/-- The finite-sum reading of *"maximises"* is print's. -/
public theorem isOptimalPolicy_iff_law [Fintype V] [∀ v, Fintype (edom v)]
    [∀ v, Fintype (dom v)] [∀ v, DecidableEq (dom v)]
    [∀ v, DiscreteMeasurableSpace (edom v)] [∀ v, Countable (edom v)]
    [∀ v, DiscreteMeasurableSpace (dom v)] [∀ v, Countable (dom v)]
    [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] (π : M.Policy) :
    M.IsOptimalPolicy π ↔ M.IsOptimalPolicyLaw π fun _ ↦ SCM.measurable_exo _ := by
  simp only [IsOptimalPolicyLaw, M.expectedUtilityLaw_eq]
  rfl

open MeasureTheory in
/-- **`V*(M)` maximises print's expectation**, not merely a finite sum that
agrees with it. This is what leaves the `[Fintype V]` on `SCIM.optimalValue`
doing only the two jobs the section preamble adjudicates as transcribing print:
supplying the maximum print writes, and making print's sum over `𝐔` denote. -/
public theorem optimalValue_eq_sup'_law [Fintype V] [∀ v, Fintype (edom v)]
    [∀ v, Fintype (dom v)] [∀ v, DecidableEq (dom v)]
    [∀ v, DiscreteMeasurableSpace (edom v)] [∀ v, Countable (edom v)]
    [∀ v, DiscreteMeasurableSpace (dom v)] [∀ v, Countable (dom v)]
    [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] :
    M.optimalValue = Finset.univ.sup' Finset.univ_nonempty
      fun π : M.Policy ↦ M.expectedUtilityLaw π (SCM.measurable_exo _) := by
  unfold optimalValue
  congr 1
  funext π
  exact (M.expectedUtilityLaw_eq π).symm

omit [∀ v, MeasurableSpace (dom v)] in
/-- Policy changes preserve the independent exogenous law on arbitrary graphs. -/
public theorem exoLaw_withPolicy_eq (π π' : M.Policy) :
    (M.withPolicy π).exoLaw = (M.withPolicy π').exoLaw := rfl

/-- The source's policy-invariance sentence at the level of probability laws,
without a finite vertex or observation set. Measurability is required of the
observables; no expectation or optimization hypothesis is used. -/
public theorem observableLaw_withPolicy_eq_of_notDownstream [M.graph.IsWellFounded]
    (π π' : M.Policy) (X : Set V) (hX : ∀ v ∈ X, M.graph.NotDownstream v)
    (hm : Measurable (fun ε : ExoAssignment V edom ↦
      fun v : X ↦ (M.withPolicy π).eval ε v))
    (hm' : Measurable (fun ε : ExoAssignment V edom ↦
      fun v : X ↦ (M.withPolicy π').eval ε v)) :
    (M.withPolicy π).observableLaw X hm = (M.withPolicy π').observableLaw X hm' := by
  apply Subtype.ext
  change MeasureTheory.Measure.map _ _ = MeasureTheory.Measure.map _ _
  congr 1
  funext ε v
  exact M.eval_withPolicy_eq_of_notDownstream π π' ε (hX v v.property)

end SCIM

/-! ## Laws at almost-everywhere measurable evaluations

`SCM.observableLaw` asks for the evaluation map to be `Measurable`, which is
stronger than forming a pushforward needs: `ProbabilityMeasure.map` reads only
`AEMeasurable` against the exogenous law. Print's joint is
*"`Pr(W = w) = Σ_{ε | W(ε) = w} P(ε)`"* (ec21-scm-joint, PDF p. 2), a sum of
point masses with no measurability clause, and at an exogenous law concentrated
on countably many draws every map is almost-everywhere measurable
(`SCM.aemeasurable_of_countable_support`). So the laws below carry the weaker
hypothesis, and at print's atomic laws none at all.
-/

namespace SCM

open MeasureTheory

variable {V : Type*} [DecidableEq V] {dom edom : V → Type*}
  [∀ v, MeasurableSpace (edom v)] [∀ v, MeasurableSpace (dom v)]
  (M : SCM V dom edom)

/-- Joint law of a set of evaluated variables, at an evaluation that is only
almost-everywhere measurable for the exogenous law. -/
@[expose] public noncomputable def observableLawAE [M.IsWellFounded] (X : Set V)
    (hm : AEMeasurable (fun ε : ExoAssignment V edom ↦ fun v : X ↦ M.eval ε v)
      (M.exoLaw : Measure (ExoAssignment V edom))) :
    ProbabilityMeasure ((v : X) → dom v) :=
  M.exoLaw.map hm

/-- At a measurable evaluation the two laws are the same measure. -/
public theorem observableLaw_eq_observableLawAE [M.IsWellFounded] (X : Set V)
    (hm : Measurable (fun ε : ExoAssignment V edom ↦ fun v : X ↦ M.eval ε v)) :
    M.observableLaw X hm = M.observableLawAE X hm.aemeasurable :=
  rfl

omit [∀ v, MeasurableSpace (dom v)] in
/-- **At an atomic exogenous law every map is almost-everywhere measurable.**

Print's `Pr(W = w) = Σ_{ε | W(ε) = w} P(ε)` (ec21-scm-joint) is a sum against
point masses, so it presupposes that `P(ε)` is carried by countably many draws;
that presupposition is the hypothesis `hfull` with `hS`. A countable vertex set
and measurable singletons make a countable set of draws measurable, and on it any
function is measurable. The hypothesis is not free: an infinite product of
non-degenerate marginals is atomless, and there print's sum formula names
nothing. -/
public theorem aemeasurable_of_countable_support [Countable V]
    [∀ v, MeasurableSingletonClass (edom v)] {S : Set (ExoAssignment V edom)}
    (hS : S.Countable) (hfull : (M.exoLaw : Measure (ExoAssignment V edom)) Sᶜ = 0)
    {α : Type*} [MeasurableSpace α] (f : ExoAssignment V edom → α) :
    AEMeasurable f (M.exoLaw : Measure (ExoAssignment V edom)) := by
  have hSm : MeasurableSet S := hS.measurableSet
  have hrestrict : (M.exoLaw : Measure (ExoAssignment V edom)).restrict S = M.exoLaw :=
    Measure.restrict_eq_self_of_ae_mem (ae_iff.mpr hfull)
  rw [← hrestrict, aemeasurable_restrict_iff_comap_subtype hSm]
  have := hS.to_subtype
  exact (measurable_of_countable _).aemeasurable

end SCM

namespace SCIM

open MeasureTheory

variable {V : Type*} [DecidableEq V] {dom edom : V → Type*}
  [∀ v, MeasurableSpace (edom v)] [∀ v, MeasurableSpace (dom v)]
  (M : SCIM V dom edom)

omit [∀ v, MeasurableSpace (dom v)] in
/-- Almost-everywhere measurability of the observables off the descendants of `𝐃` transfers
between policies: the two evaluation maps are equal there and the exogenous law
is the same. So one hypothesis serves both sides of the invariance sentence. -/
public theorem aemeasurable_withPolicy_of_notDownstream [M.graph.IsWellFounded]
    (π π' : M.Policy) (X : Set V) (hX : ∀ v ∈ X, M.graph.NotDownstream v)
    {β : V → Type*} (g : (v : V) → dom v → β v) [∀ v, MeasurableSpace (β v)]
    (hm : AEMeasurable (fun ε : ExoAssignment V edom ↦
      fun v : X ↦ g v ((M.withPolicy π).eval ε v))
      ((M.withPolicy π).exoLaw : Measure (ExoAssignment V edom))) :
    AEMeasurable (fun ε : ExoAssignment V edom ↦
      fun v : X ↦ g v ((M.withPolicy π').eval ε v))
      ((M.withPolicy π').exoLaw : Measure (ExoAssignment V edom)) := by
  have h : (fun ε : ExoAssignment V edom ↦ fun v : X ↦ g v ((M.withPolicy π').eval ε v)) =
      fun ε ↦ fun v : X ↦ g v ((M.withPolicy π).eval ε v) :=
    funext fun ε ↦ funext fun v ↦ by
      rw [M.eval_withPolicy_eq_of_notDownstream π π' ε (hX v v.property)]
  rw [h]
  exact hm

/-- **Print's policy-invariance sentence at the level of laws, with one
almost-everywhere measurability hypothesis.** *"For a set of variables `X` not in
Desc_D, `Pr^π(x)` is independent of `π`"* (ec21-policy-invariance, PDF p. 3).
`SCIM.observableLaw_withPolicy_eq_of_notDownstream` asks for `Measurable` at
both policies; here `AEMeasurable` at one policy suffices, the other side's
being derived. -/
public theorem observableLawAE_withPolicy_eq_of_notDownstream [M.graph.IsWellFounded]
    (π π' : M.Policy) (X : Set V) (hX : ∀ v ∈ X, M.graph.NotDownstream v)
    (hm : AEMeasurable (fun ε : ExoAssignment V edom ↦
      fun v : X ↦ (M.withPolicy π).eval ε v)
      ((M.withPolicy π).exoLaw : Measure (ExoAssignment V edom))) :
    (M.withPolicy π).observableLawAE X hm =
      (M.withPolicy π').observableLawAE X
        (M.aemeasurable_withPolicy_of_notDownstream π π' X hX (fun _ a ↦ a) hm) := by
  apply Subtype.ext
  change Measure.map _ _ = Measure.map _ _
  congr 1
  funext ε v
  exact M.eval_withPolicy_eq_of_notDownstream π π' ε (hX v v.property)

/-- **Print's invariance sentence with no measurability hypothesis**, at an
exogenous law carried by countably many draws over a countable vertex set —
the law print's sum formula `Pr(W = w) = Σ_{ε | W(ε) = w} P(ε)` presupposes.
Both laws exist by `SCM.aemeasurable_of_countable_support`. -/
public theorem observableLawAE_withPolicy_eq_of_countable_support
    [M.graph.IsWellFounded] [Countable V] [∀ v, MeasurableSingletonClass (edom v)]
    (π π' : M.Policy) (X : Set V) (hX : ∀ v ∈ X, M.graph.NotDownstream v)
    {S : Set (ExoAssignment V edom)} (hS : S.Countable)
    (hfull : ((M.withPolicy π).exoLaw : Measure (ExoAssignment V edom)) Sᶜ = 0) :
    (M.withPolicy π).observableLawAE X
        ((M.withPolicy π).aemeasurable_of_countable_support hS hfull _) =
      (M.withPolicy π').observableLawAE X
        ((M.withPolicy π').aemeasurable_of_countable_support hS hfull _) :=
  M.observableLawAE_withPolicy_eq_of_notDownstream π π' X hX _

/-! ### `Eπ[U]` and optimal policies at almost-everywhere measurable evaluations

`SCIM.expectedUtilityLaw` and `SCIM.IsOptimalPolicyLaw` ask the utility evaluation
to be `Measurable`, a condition print does not write: print's `P` is *"a
probability distribution for `E`"* (Definition 4) with `Pr(W = w) = Σ_{ε | W(ε) = w}
P(ε)` (ec21-scm-joint, PDF p. 2), no measurability clause. The pushforward needs
only `AEMeasurable` against `Mπ`'s exogenous law, which at print's atomic laws is
free (`SCM.aemeasurable_of_countable_support`), even where a utility reads a
non-measurable function of infinitely many parents. -/

/-- **`Eπ[U]` at an almost-everywhere measurable utility evaluation.** The
integral of print's total utility `U := Σ_{U ∈ 𝐔} U` under the law of the utility
vertices in `Mπ`, formed by `SCM.observableLawAE`. At a measurable evaluation it
is `SCIM.expectedUtilityLaw` (`SCIM.expectedUtilityLaw_eq_AE`). -/
@[expose] public noncomputable def expectedUtilityLawAE [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] (π : M.Policy)
    (hm : AEMeasurable (fun ε : ExoAssignment V edom ↦
      fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π).eval ε u.1)
      ((M.withPolicy π).exoLaw : Measure (ExoAssignment V edom))) : ℝ :=
  ∫ w, ∑ u : {v : V // M.graph.IsUtility v}, M.utilityValue u.1 u.2 (w ⟨u.1, u.2⟩)
    ∂((M.withPolicy π).observableLawAE {v : V | M.graph.IsUtility v} hm :
      Measure ((v : {v : V | M.graph.IsUtility v}) → dom v))

/-- At a measurable evaluation the almost-everywhere expectation is
`SCIM.expectedUtilityLaw`. -/
public theorem expectedUtilityLaw_eq_AE [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] (π : M.Policy)
    (hm : Measurable fun ε : ExoAssignment V edom ↦
      fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π).eval ε u.1) :
    M.expectedUtilityLaw π hm = M.expectedUtilityLawAE π hm.aemeasurable :=
  rfl

/-- **An optimal policy at almost-everywhere measurable evaluations**: print's
*"any policy `π` that maximises `Eπ[U]`"* (PDF p. 3), with `Eπ[U]` the expectation
`SCIM.expectedUtilityLawAE`. Each policy's utility evaluation need only be
almost-everywhere measurable for its own exogenous law. -/
@[expose] public def IsOptimalPolicyLawAE [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] (π : M.Policy)
    (hm : ∀ π' : M.Policy, AEMeasurable (fun ε : ExoAssignment V edom ↦
      fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π').eval ε u.1)
      ((M.withPolicy π').exoLaw : Measure (ExoAssignment V edom))) : Prop :=
  ∀ π' : M.Policy, M.expectedUtilityLawAE π' (hm π') ≤ M.expectedUtilityLawAE π (hm π)

/-- At measurable evaluations the two readings of *"maximises"* agree, so
`SCIM.IsOptimalPolicyLaw` is the measurable case of `SCIM.IsOptimalPolicyLawAE`. -/
public theorem isOptimalPolicyLaw_iff_AE [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] (π : M.Policy)
    (hm : ∀ π' : M.Policy, Measurable fun ε : ExoAssignment V edom ↦
      fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π').eval ε u.1) :
    M.IsOptimalPolicyLaw π hm ↔ M.IsOptimalPolicyLawAE π fun π' ↦ (hm π').aemeasurable :=
  Iff.rfl

end SCIM

/-! ## Definition 5 without a finite vertex set

`SCIM.optimalValue` and `SCIM.IsMaterial` are finite sums over
`ExoAssignment V edom` and exist only at `[Fintype V]`. Print's Definition 5
(*"For any given SCIM `M`, let `V*(M) = max_π E_π[U]`"*, ec21-def-5) names no
cardinality; Definition 4's *"finite"* qualifies domains, never the vertex set.
`V*(M)` needs exactly three things to denote, and each is carried here as what
it is rather than as a bound on `V`:

* the recursion (`[M.graph.IsWellFounded]`, print's *"recursive application"*);
* print's `U := Σ_{U ∈ 𝐔} U` (`[Fintype {v // IsUtility v}]`, as in
  `SCIM.expectedUtilityLaw`);
* print's `max`, which presupposes that some policy attains it: a hypothesis
  `hatt : ∃ π, M.IsOptimalPolicyLaw π hm`, print's own presupposition rather than
  a condition on the model's size. `SCIM.exists_isOptimalPolicyLaw` discharges it
  whenever the policy space is finite, which holds when the decisions are finitely
  many and each observes finitely many parents over finite domains
  (`SCIM.finite_policy`); but it also holds at an infinite policy space, for
  instance where every policy earns the same.

Measurability of each policy's utility evaluation is asked for, as everywhere in
the law layer, and is free at a finite vertex set (`SCM.measurable_exo`).
-/

namespace SCIM

open MeasureTheory

variable {V : Type*} [DecidableEq V] {dom edom : V → Type*}
  [∀ v, MeasurableSpace (edom v)] [∀ v, MeasurableSpace (dom v)]
  (M : SCIM V dom edom)

omit [∀ v, MeasurableSpace (edom v)] [∀ v, MeasurableSpace (dom v)] in
/-- **The policy space is finite when the decisions see finitely much**: finitely
many decision vertices, each with finitely many parents, over finite domains. No
bound on the other vertices is needed, because a policy reads only its
observations. -/
public theorem finite_policy [Finite {d : V // M.graph.IsDecision d}]
    (hpar : ∀ d, M.graph.IsDecision d → (M.graph.parents d).Finite)
    [∀ v, Finite (dom v)] [∀ v, Finite (edom v)] : Finite M.Policy := by
  classical
  have : ∀ d : {d : V // M.graph.IsDecision d}, Finite (M.graph.parents d.1) :=
    fun d ↦ (hpar d.1 d.2).to_subtype
  let ext : (d : {d : V // M.graph.IsDecision d}) →
      ((p : M.graph.parents d.1) → dom p.1) → EndoAssignment V dom :=
    fun d a v ↦ if h : v ∈ M.graph.parents d.1 then a ⟨v, h⟩ else (M.dom_nonempty v).some
  let F : M.Policy → (d : {d : V // M.graph.IsDecision d}) →
      ((p : M.graph.parents d.1) → dom p.1) → edom d.1 → dom d.1 :=
    fun π d a e ↦ π.1 d (ext d a) e
  refine Finite.of_injective F fun π π' h ↦ Subtype.ext (funext fun d ↦ funext fun a ↦
    funext fun e ↦ ?_)
  have hagree : ∀ p ∈ M.graph.parents d.1, a p = ext d (fun q ↦ a q.1) p := by
    intro p hp
    simp [ext, dif_pos hp]
  rw [π.2 d a _ e hagree, π'.2 d a _ e hagree]
  exact congrFun (congrFun (congrFun h d) (fun q ↦ a q.1)) e

omit [∀ v, MeasurableSpace (edom v)] [∀ v, MeasurableSpace (dom v)] in
/-- `M_{X↛D}` has the same utility vertices as `M`. -/
public instance instFintypeUtilityRemoveInfoLink [h : Fintype {v : V // M.graph.IsUtility v}]
    {d : V} (hd : M.graph.IsDecision d) (x : V) :
    Fintype {v : V // (M.removeInfoLink hd x).graph.IsUtility v} :=
  h

omit [∀ v, MeasurableSpace (edom v)] [∀ v, MeasurableSpace (dom v)] in
/-- A policy of `M_{X↛D}` reads fewer parents, so it is a policy of `M`: removing
an information link keeps the policy space finite. -/
public instance instFiniteRemoveInfoLinkPolicy [Finite M.Policy]
    {d : V} (hd : M.graph.IsDecision d) (x : V) :
    Finite (M.removeInfoLink hd x).Policy := by
  refine Finite.of_injective
    (fun π : (M.removeInfoLink hd x).Policy ↦
      (⟨fun d' a e ↦ π.1 ⟨d'.1, d'.2⟩ a e, fun d' a b e hab ↦
        π.2 ⟨d'.1, d'.2⟩ a b e fun p hp ↦ hab p (removeInfoLink_sub M hp)⟩ : M.Policy))
    fun π π' h ↦ Subtype.ext (funext fun d' ↦ ?_)
  exact congrFun (congrArg Subtype.val h) ⟨d'.1, d'.2⟩

/-- **`V*(M) = max_π E_π[U]` at an unbounded vertex set** (Definition 5,
ec21-def-5): the supremum of print's expectation `SCIM.expectedUtilityLaw` over
policies. `_hatt` is print's presupposition that the `max` is attained; with it the
supremum is the value of any maximiser (`SCIM.optimalValueLaw_eq`), and without it
a real `⨆` over an unbounded family would be junk, so the hypothesis is
load-bearing although the body does not read it. No finiteness of the policy space
is asked: `SCIM.exists_isOptimalPolicyLaw` supplies `_hatt` where that space is
finite, and nothing else about the model's size is needed. -/
@[expose] public noncomputable def optimalValueLaw [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}]
    (hm : ∀ π : M.Policy, Measurable fun ε : ExoAssignment V edom ↦
      fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π).eval ε u.1)
    (_hatt : ∃ π, M.IsOptimalPolicyLaw π hm) : ℝ :=
  ⨆ π : M.Policy, M.expectedUtilityLaw π (hm π)

/-- **`V*(M)` is the value of any maximiser**: print's `max_π E_π[U]`
(Definition 5, ec21-def-5) is attained at every policy that maximises `E_π[U]`. -/
public theorem optimalValueLaw_eq [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}]
    (hm : ∀ π : M.Policy, Measurable fun ε : ExoAssignment V edom ↦
      fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π).eval ε u.1)
    (hatt : ∃ π, M.IsOptimalPolicyLaw π hm) {π : M.Policy}
    (hπ : M.IsOptimalPolicyLaw π hm) :
    M.optimalValueLaw hm hatt = M.expectedUtilityLaw π (hm π) :=
  le_antisymm (ciSup_le hπ) (le_ciSup ⟨_, Set.forall_mem_range.2 hπ⟩ π)

/-- **Print's `max` is attained when the policy space is finite**: some policy
is optimal in print's sense, at any vertex set. This is the lemma that discharges
`SCIM.optimalValueLaw`'s attainment hypothesis; `SCIM.optimalValueLaw_eq` gives
its value. -/
public theorem exists_isOptimalPolicyLaw [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] [Finite M.Policy]
    (hm : ∀ π : M.Policy, Measurable fun ε : ExoAssignment V edom ↦
      fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π).eval ε u.1) :
    ∃ π : M.Policy, M.IsOptimalPolicyLaw π hm := by
  obtain ⟨π, hπ⟩ := exists_eq_ciSup_of_finite (ι := M.Policy)
    (f := fun π : M.Policy ↦ M.expectedUtilityLaw π (hm π))
  refine ⟨π, fun π' ↦ ?_⟩
  rw [hπ]
  exact le_ciSup (Set.finite_range fun π : M.Policy ↦ M.expectedUtilityLaw π (hm π)).bddAbove π'

/-- **Definition 5 (Materiality) at an unbounded vertex set.** *"The observation
`X ∈ Pa_D` is material if `V*(M_{X↛D}) < V*(M)`"* (ec21-def-5), with both values
`SCIM.optimalValueLaw`. Measurability is asked of the policies of both models,
and attainment of both maxima is print's presupposition (`hatt`, `hatt'`), so the
policy spaces may be infinite. -/
@[expose] public def IsMaterialLaw [M.graph.IsWellFounded]
    [Fintype {v : V // M.graph.IsUtility v}] {d : V}
    (hd : M.graph.IsDecision d) {x : V} (_hx : x ∈ M.graph.parents d)
    (hm : ∀ π : M.Policy, Measurable fun ε : ExoAssignment V edom ↦
      fun u : {v : V // M.graph.IsUtility v} ↦ (M.withPolicy π).eval ε u.1)
    (hm' : ∀ π : (M.removeInfoLink hd x).Policy, Measurable fun ε : ExoAssignment V edom ↦
      fun u : {v : V // (M.removeInfoLink hd x).graph.IsUtility v} ↦
        ((M.removeInfoLink hd x).withPolicy π).eval ε u.1)
    (hatt : ∃ π, M.IsOptimalPolicyLaw π hm)
    (hatt' : ∃ π, (M.removeInfoLink hd x).IsOptimalPolicyLaw π hm') : Prop :=
  (M.removeInfoLink hd x).optimalValueLaw hm' hatt' < M.optimalValueLaw hm hatt

/-- At a finite vertex set `V*(M)` is the finite maximum `SCIM.optimalValue`. -/
public theorem optimalValue_eq_optimalValueLaw [Fintype V] [∀ v, Fintype (edom v)]
    [∀ v, Fintype (dom v)] [∀ v, DecidableEq (dom v)]
    [∀ v, DiscreteMeasurableSpace (edom v)] [∀ v, Countable (edom v)]
    [∀ v, DiscreteMeasurableSpace (dom v)] [∀ v, Countable (dom v)]
    [M.graph.IsWellFounded] [Fintype {v : V // M.graph.IsUtility v}] :
    M.optimalValue =
      M.optimalValueLaw (fun _ ↦ SCM.measurable_exo _) (M.exists_isOptimalPolicyLaw _) := by
  rw [M.optimalValue_eq_sup'_law, optimalValueLaw, Finset.sup'_univ_eq_ciSup]

/-- **The bridge**: at a finite vertex set materiality in the law sense is
`SCIM.IsMaterial`, so the unbounded definition extends the finite one. -/
public theorem isMaterial_iff_law [Fintype V] [∀ v, Fintype (edom v)]
    [∀ v, Fintype (dom v)] [∀ v, DecidableEq (dom v)]
    [∀ v, DiscreteMeasurableSpace (edom v)] [∀ v, Countable (edom v)]
    [∀ v, DiscreteMeasurableSpace (dom v)] [∀ v, Countable (dom v)]
    [M.graph.IsWellFounded] [Fintype {v : V // M.graph.IsUtility v}] {d : V}
    (hd : M.graph.IsDecision d) {x : V} (hx : x ∈ M.graph.parents d) :
    M.IsMaterial hd hx ↔
      M.IsMaterialLaw hd hx (fun _ ↦ SCM.measurable_exo _) (fun _ ↦ SCM.measurable_exo _)
        (M.exists_isOptimalPolicyLaw _) ((M.removeInfoLink hd x).exists_isOptimalPolicyLaw _) := by
  rw [IsMaterial, IsMaterialLaw, M.optimalValue_eq_optimalValueLaw,
    (M.removeInfoLink hd x).optimalValue_eq_optimalValueLaw]

end SCIM

end AISafetyAtlas.Causal
