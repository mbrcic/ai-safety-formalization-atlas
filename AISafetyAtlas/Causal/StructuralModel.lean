module

public import AISafetyAtlas.Causal.Model

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
requires the exogenous variables to be mutually independent. On finite domains
that is exactly the class of products of per-variable distributions, and the
product is the form every later computation reads.

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

variable {V : Type*} [Fintype V] [DecidableEq V] {dom edom : V → ℕ}

/-- An assignment to the exogenous variables. -/
public abbrev ExoAssignment (V : Type*) (edom : V → ℕ) := (v : V) → Fin (edom v)

/-- **Definition 1.** A structural causal model with independent errors. -/
public structure SCM (V : Type*) [DecidableEq V] (dom edom : V → ℕ) where
  /-- Every endogenous variable has at least one state. -/
  dom_pos : ∀ v, 0 < dom v
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
  f : (v : V) → Assignment V dom → Fin (edom v) → Fin (dom v)
  /-- A structural function reads only its declared parents and its own
  exogenous variable. -/
  f_parents : ∀ v a b e, (∀ p ∈ parents v, a p = b p) → f v a e = f v b e
  /-- The distribution of the exogenous variable `E^V`. Mutual independence is
  rendered as one marginal per variable; see the module docstring. -/
  exoProb : (v : V) → Fin (edom v) → ℝ
  /-- Each marginal is nonnegative. -/
  exoProb_nonneg : ∀ v e, 0 ≤ exoProb v e
  /-- Each marginal is a probability distribution. -/
  exoProb_sum : ∀ v, ∑ e : Fin (edom v), exoProb v e = 1

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

/-- `P(ε)`: the exogenous variables are mutually independent, so the joint is
the product of the marginals. -/
@[expose] public noncomputable def exoJoint (ε : ExoAssignment V edom) : ℝ :=
  ∏ v : V, M.exoProb v (ε v)

public theorem exoJoint_nonneg (ε : ExoAssignment V edom) : 0 ≤ M.exoJoint ε :=
  Finset.prod_nonneg fun v _ ↦ M.exoProb_nonneg v (ε v)

public theorem exoJoint_sum : ∑ ε : ExoAssignment V edom, M.exoJoint ε = 1 := by
  classical
  have h : ∏ v : V, (∑ e : Fin (edom v), M.exoProb v e) = 1 :=
    Finset.prod_eq_one fun v _ ↦ M.exoProb_sum v
  rw [← h, Finset.prod_univ_sum]
  simp [exoJoint, Fintype.piFinset_univ]

/-- **Independence, in the form an expectation uses.** The joint expectation of
a product of one factor per exogenous variable is the product of the marginal
expectations. `exoJoint_sum` is the case `g = 1`, and this is what makes
*"mutually independent"* usable rather than merely stated. -/
public theorem exoJoint_mul_prod (g : (v : V) → Fin (edom v) → ℝ) :
    ∑ ε : ExoAssignment V edom, M.exoJoint ε * ∏ v : V, g v (ε v)
      = ∏ v : V, ∑ e : Fin (edom v), M.exoProb v e * g v e := by
  classical
  rw [Finset.prod_univ_sum]
  simp [exoJoint, Fintype.piFinset_univ, ← Finset.prod_mul_distrib]

/-! ## Evaluation

`W(ε)` is print's *"recursive application of the structural functions"*. -/

/-- The default assignment. It is used only to extend a partial assignment on
the parents of a vertex to a total one, which is what `f` expects; `f_parents`
says no structural function reads the extension. -/
@[expose] public def seed : Assignment V dom := fun v ↦ ⟨0, M.dom_pos v⟩

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
    (ε : ExoAssignment V edom) : Assignment V dom :=
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
induces a joint distribution `Pr(W = w) = Σ_{ε | W(ε) = w} P(ε)`."* -/

/-- `Pr(V = w)`, the joint over all endogenous variables. -/
@[expose] public noncomputable def jointProb (M : SCM V dom edom) [M.IsWellFounded]
    (w : Assignment V dom) : ℝ :=
  ∑ ε ∈ Finset.univ.filter fun ε : ExoAssignment V edom ↦ M.eval ε = w,
    M.exoJoint ε

public theorem jointProb_nonneg (M : SCM V dom edom) [M.IsWellFounded]
    (w : Assignment V dom) :
    0 ≤ M.jointProb w :=
  Finset.sum_nonneg fun ε _ ↦ M.exoJoint_nonneg ε

/-- The induced joint is a probability distribution: the fibres of `eval`
partition the exogenous assignments. -/
public theorem jointProb_sum (M : SCM V dom edom) [M.IsWellFounded] :
    ∑ w : Assignment V dom, M.jointProb w = 1 := by
  classical
  rw [← M.exoJoint_sum]
  exact (Finset.sum_fiberwise_of_maps_to (fun ε _ ↦ Finset.mem_univ (M.eval ε))
    fun ε ↦ M.exoJoint ε).symm ▸ rfl


/-- **`Pr(x)`**, the induced probability that the variables in `X` take the
values `x` assigns them. Print writes `Pr^π(x)` for a *set* of variables, so the
object graded is the marginal rather than the full joint. -/
@[expose] public noncomputable def marginal (M : SCM V dom edom) [M.IsWellFounded]
    (X : Finset V) (x : Assignment V dom) : ℝ :=
  ∑ w ∈ Finset.univ.filter (fun w : Assignment V dom ↦ ∀ c ∈ X, w c = x c),
    M.jointProb w

/-- The marginal read off the exogenous draw instead of off the joint: the
fibres of `eval` partition the exogenous assignments, so summing `jointProb`
over the `X`-fibre is summing `P(ε)` over the draws whose evaluation lands in
it. This is what turns a statement about `eval` into a statement about `Pr`. -/
public theorem marginal_eq_sum_exo (M : SCM V dom edom) [M.IsWellFounded]
    (X : Finset V) (x : Assignment V dom) :
    M.marginal X x = ∑ ε ∈ Finset.univ.filter
        (fun ε : ExoAssignment V edom ↦ ∀ c ∈ X, M.eval ε c = x c), M.exoJoint ε := by
  classical
  simp only [marginal, jointProb, Finset.sum_filter]
  have key : ∀ w : Assignment V dom,
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
    (x : Assignment V dom) : SCM V dom edom where
  dom_pos := M.dom_pos
  parents := fun v ↦ if v ∈ X then ∅ else M.parents v
  acyclic := fun v hv ↦ M.acyclic v (hv.mono fun p w hp ↦ by
    by_cases hw : w ∈ X
    · rw [if_pos hw] at hp; exact absurd hp (Set.notMem_empty p)
    · rwa [if_neg hw] at hp)
  f := fun v a e ↦ if v ∈ X then x v else M.f v a e
  f_parents := fun v a b e h ↦ by
    by_cases hv : v ∈ X
    · simp [hv]
    · simp only [if_neg hv]
      exact M.f_parents v a b e fun p hp ↦ h p (by rw [if_neg hv]; exact hp)
  exoProb := M.exoProb
  exoProb_nonneg := M.exoProb_nonneg
  exoProb_sum := M.exoProb_sum

omit [Fintype V] in
/-- Forcing a variable only deletes edges, so the submodel inherits the
recursion's hypothesis. This is what keeps `submodel_eval` stated at a submodel
of an evaluable model rather than asking for the hypothesis twice. -/
public instance instIsWellFoundedSubmodel (M : SCM V dom edom)
    [hM : M.IsWellFounded] (X : Finset V) (x : Assignment V dom) :
    (M.submodel X x).IsWellFounded :=
  ⟨Subrelation.wf (fun {p v} hp ↦ by
      simp only [submodel] at hp
      by_cases hv : v ∈ X
      · rw [if_pos hv] at hp; exact absurd hp (Set.notMem_empty p)
      · rwa [if_neg hv] at hp) hM.wf⟩

omit [Fintype V] in
/-- An intervened variable takes its forced value, whatever the exogenous draw. -/
@[simp] public theorem submodel_eval (M : SCM V dom edom) [M.IsWellFounded]
    (X : Finset V) (x : Assignment V dom) (ε : ExoAssignment V edom)
    {v : V} (hv : v ∈ X) :
    (M.submodel X x).eval ε v = x v := by
  rw [(M.submodel X x).eval_eq_f ε v]
  simp [submodel, hv]

omit [Fintype V] in
/-- A variable outside the intervention keeps its own structural function. -/
public theorem submodel_eval_notMem (M : SCM V dom edom) [M.IsWellFounded]
    (X : Finset V) (x : Assignment V dom) (ε : ExoAssignment V edom)
    {v : V} (hv : v ∉ X) :
    (M.submodel X x).eval ε v = M.f v ((M.submodel X x).eval ε) (ε v) := by
  rw [(M.submodel X x).eval_eq_f ε v]
  simp [submodel, hv]

/-- **Soft intervention.** Print: *"a soft intervention on a variable `X` in an
SCM `M` replaces `f^X` with a function `g^X : dom(Pa_X ∪ {E^X}) → dom(X)`"* —
the parents are the same, so acyclicity is inherited unchanged. -/
@[expose] public noncomputable def softIntervention (M : SCM V dom edom)
    (X : Finset V) (g : (v : V) → Assignment V dom → Fin (edom v) → Fin (dom v))
    (hg : ∀ v a b e, (∀ p ∈ M.parents v, a p = b p) → g v a e = g v b e) :
    SCM V dom edom where
  dom_pos := M.dom_pos
  parents := M.parents
  acyclic := M.acyclic
  f := fun v a e ↦ if v ∈ X then g v a e else M.f v a e
  f_parents := fun v a b e h ↦ by
    by_cases hv : v ∈ X
    · simp only [if_pos hv]; exact hg v a b e h
    · simp only [if_neg hv]; exact M.f_parents v a b e h
  exoProb := M.exoProb
  exoProb_nonneg := M.exoProb_nonneg
  exoProb_sum := M.exoProb_sum

omit [Fintype V] in
/-- A soft intervention keeps the parent map, so it keeps the recursion's
hypothesis with it. -/
public instance instIsWellFoundedSoftIntervention (M : SCM V dom edom)
    [hM : M.IsWellFounded] (X : Finset V)
    (g : (v : V) → Assignment V dom → Fin (edom v) → Fin (dom v))
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
public structure SCIM (V : Type*) [DecidableEq V] (dom edom : V → ℕ) where
  /-- Every endogenous variable has at least one state. -/
  dom_pos : ∀ v, 0 < dom v
  /-- *"`G` is a CID with finite-domain variables `V`"*. -/
  graph : CID V
  /-- *"where utility variable domains are a subset of `ℝ`"*: each utility
  vertex reads its states as reals. -/
  utilityValue : (u : V) → graph.IsUtility u → Fin (dom u) → ℝ
  /-- A *subset* of `ℝ`, so distinct states are distinct reals. -/
  utilityValue_injective :
    ∀ u (hu : graph.IsUtility u), Function.Injective (utilityValue u hu)
  /-- `F = {f^V}_{V ∈ 𝐕 \ 𝐃}`. Decision vertices have no structural function
  until a policy supplies one, which is what the non-membership proof records. -/
  f : (v : V) → ¬ graph.IsDecision v →
    Assignment V dom → Fin (edom v) → Fin (dom v)
  /-- *"specify how each non-decision endogenous variable depends on its parents
  in `G` and its associated exogenous variable"*. -/
  f_parents : ∀ v (hv : ¬ graph.IsDecision v) a b e,
    (∀ p ∈ graph.parents v, a p = b p) → f v hv a e = f v hv b e
  /-- `P`, one marginal per exogenous variable; independence is the product, as
  in `SCM`. -/
  exoProb : (v : V) → Fin (edom v) → ℝ
  /-- Each marginal is nonnegative. -/
  exoProb_nonneg : ∀ v e, 0 ≤ exoProb v e
  /-- Each marginal is a probability distribution. -/
  exoProb_sum : ∀ v, ∑ e : Fin (edom v), exoProb v e = 1

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
between `Fin (dom v)` and `Fin (dom d)`. -/
public abbrev Policy : Type _ :=
  {π : (d : {d : V // M.graph.IsDecision d}) →
        Assignment V dom → Fin (edom d.1) → Fin (dom d.1) //
    ∀ d a b e, (∀ p ∈ M.graph.parents d.1, a p = b p) → π d a e = π d b e}

/-- A policy may ignore its observations, so one always exists. -/
public instance instNonemptyPolicy : Nonempty M.Policy :=
  ⟨⟨fun d _ _ ↦ ⟨0, M.dom_pos d.1⟩, fun _ _ _ _ _ ↦ rfl⟩⟩

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
  dom_pos := M.dom_pos
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
  exoProb_sum := M.exoProb_sum

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
    (hv : ¬ M.graph.IsDecision v) (a : Assignment V dom) (e : Fin (edom v)) :
    (M.withPolicy π).f v a e = M.f v hv a e := by
  simp [withPolicy, dif_neg hv]

omit [Fintype V] in
/-- A decision vertex takes the policy as its structural function in `Mπ`. -/
public theorem withPolicy_f_mem (π : M.Policy) {d : V}
    (hd : M.graph.IsDecision d) (a : Assignment V dom) (e : Fin (edom d)) :
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
public theorem marginal_withPolicy_eq_of_notDownstream [M.graph.IsWellFounded]
    (π π' : M.Policy) (X : Finset V) (hX : ∀ c ∈ X, M.graph.NotDownstream c)
    (x : Assignment V dom) :
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

public theorem expectedUtility_le_optimalValue [M.graph.IsWellFounded]
    (π : M.Policy) :
    M.expectedUtility π ≤ M.optimalValue := by
  unfold optimalValue
  exact Finset.le_sup' M.expectedUtility (Finset.mem_univ π)

/-- Print writes a `max`, and this is what makes it one. -/
public theorem exists_isOptimalPolicy [M.graph.IsWellFounded] :
    ∃ π : M.Policy, M.IsOptimalPolicy π ∧ M.expectedUtility π = M.optimalValue := by
  obtain ⟨π, -, hπ⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := M.Policy)) M.expectedUtility
  have hval : M.expectedUtility π = M.optimalValue := by
    unfold optimalValue
    exact hπ.symm
  exact ⟨π, fun π' ↦ hval ▸ M.expectedUtility_le_optimalValue π', hval⟩

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
  dom_pos := M.dom_pos
  graph :=
    { M.graph with
      parents := fun v ↦
        if v = d then M.graph.parents d \ {x} else M.graph.parents v
      acyclic := fun v hv ↦
        M.graph.acyclic v (hv.mono fun a b hab ↦ removeInfoLink_sub M hab)
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
  exoProb_sum := M.exoProb_sum

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
@[expose] public def IsMaterial [M.graph.IsWellFounded] {d : V}
    (hd : M.graph.IsDecision d) {x : V}
    (_hx : x ∈ M.graph.parents d) : Prop :=
  (M.removeInfoLink hd x).optimalValue < M.optimalValue

end SCIM

end AISafetyAtlas.Causal
