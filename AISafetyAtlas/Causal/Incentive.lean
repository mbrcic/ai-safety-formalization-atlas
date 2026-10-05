module

public import AISafetyAtlas.Causal.StructuralModel

/-!
# Instrumental control incentives

Everitt, Carey, Langlois, Ortega and Legg, *Agent Incentives: A Causal
Perspective*, AAAI 2021, Definition 17 and Theorem 18.

> In a single-decision SCIM `M`, there is an **instrumental control incentive**
> on a variable `X` in decision context `pa^D` if, for all optimal policies
> `π*`, `E_{π*}[U_{X_d} | pa^D] ≠ E_{π*}[U | pa^D]`.

> **Theorem 18** (Instrumental Control Incentive Criterion). *A single-decision
> CID `G` admits an instrumental control incentive on `X ∈ 𝐕` if and only if `G`
> has a directed path from the decision `D` to a utility node `U ∈ 𝐔` that
> passes through `X`, i.e. a directed path `D ⇢ X ⇢ 𝐔`.*

This is the one incentive criterion in that paper stated over the diagram
itself rather than over its minimal reduction, and the one whose soundness
proof reads no separation property. Theorems 9, 12 and 16 need d-separation and
are not here; the assessment of what depending on an external formalization of
it would cost is `docs/provenance/d-separation-build-or-depend.md`.

## Three readings print settles and a paraphrase does not

**The path is reflexive.** Definition 3 defines a directed path as being *"of
length at least zero"*, and Theorem 18 quantifies `X ∈ 𝐕` — deliberately, in
contrast with Theorem 16 one page earlier, which writes `X ∈ 𝐕 \ {D}`. So
`X = D` and `X ∈ 𝐔` are inside the criterion, and print's completeness
construction handles them: it fixes a path `D = Z⁰ → ⋯ → Zⁿ = U` and takes
`Zⁱ = X` for some `i ∈ {0, …, n}`, both endpoints included.
`CID.IsDescendant` is `Relation.ReflTransGen` and is the relation this needs.
Under a proper reading the theorem would be false, missing the incentive on the
decision itself.

**The counterfactual decision is existential.** Definition 17's displayed
inequality contains a free `d` and print quantifies it nowhere on the page. The
two readings are not equivalent, and print's own completeness witness decides
between them: its model gives `U_{X_d} = d`, so the inequality holds at `d = 0`
and *fails* at `d = 1`. A universally quantified `d` would make Theorem 18
false as printed. `HasICIAt` therefore reads `∃ d`, and the docstring there
carries the argument rather than leaving the choice silent.

**A null decision context carries no incentive, and since 2026-09-21 that is a
ruled reading rather than a default.** Print conditions on `pa^D` without the
positivity side condition its Definition 13 states explicitly for the analogous
conditioning — Definition 13 ends *"with `Pr(pa^D, a) > 0`"* and Definition 17,
four definitions later, conditions on the same `pa^D` and says nothing. Here
division by zero is zero, so both sides of the inequality collapse to `0` on a
context of probability zero and `HasICIAt` is false there.

Two things make that the right reading rather than merely the cheap one. It is
the **conservative** direction for an incentive predicate: a false *"no
incentive here"* is a missed warning, a false *"incentive here"* is a warning
about nothing. And it is the only one of the two candidate readings that does
not put words in print's mouth — defining the conditional expectation on a null
event would be a decision made *for* the paper, not transcribed from it.

Nothing in the tree depends on the choice either way. Soundness runs through
`SCIM.condExp_congr`, which equates two conditional expectations whose
integrands agree pointwise on the conditioning event **whatever that event's
probability**, so it never touches the division; and print's completeness
context has probability one.

## Where this is wider than print, and why each widening is free

Print states Theorem 18 for a **single-decision** CID and proves both halves
under that. Neither half needs it in that form, and stating each at its own
strength costs nothing here — the proofs are the same proofs.

| | print | here |
|---|---|---|
| soundness | single-decision CID | `not_admitsICI_of_not_pathThrough`: **no hypothesis at all**. Any diagram, any number of decisions, and `D` need not be a decision |
| completeness | single-decision CID | `admitsICI_of_pathThrough`: `CID.DecisionFree` — no decision *other than `D`* on either segment or in `Pa^D`. Other decisions elsewhere are fine, and `D` need not be a decision |
| evaluability | — | `[CID.IsWellFounded]` is **not** a hypothesis: at finite `V` it follows from `CID.acyclic`, by `CID.isWellFounded_of_fintype`. That trades the class for `[Fintype V]`, which is not a loss: `AdmitsICI` mentions `condExp`, so it does not state at unbounded `V` for the expectation-layer reason below whatever this row says |
| the witness | one optimal policy, incentive read off it | `iciWitness_forall_policy`: the incentive is present against **every** policy, so which are optimal is never settled |

`admitsICI_iff` is print's statement exactly, as the corollary of
`admitsICI_iff_of_decisionFree` at `decisionFree_of_singleDecision`.

`DecisionFree` is not a technicality that could be dropped with more work. Each
of its two clauses excludes a stray decision that breaks the construction by
making a *deviating policy optimal*, which is a fact about Definition 17 rather
than about this proof — and the first clause is **witnessed**:
`Examples.Causal.Incentive.segSCIM_not_hasICI` exhibits a model over a diagram
carrying the full path, with a second decision on the segment, that has no
incentive, under a policy `segConstPolicy_optimal` proves optimal.

The one axis on which this is **narrower** than print is conditioning, and it is
specific to this module. It used to be described here as the source's whole
expectation layer, *"adjudicated once in section 8 of the source coverage audit
and not specific to anything here"*; that layer closed at Definition 5 on
2026-09-20 and this paragraph was not swept with it. What remains is
`SCIM.condExp`'s own `[Fintype V]`: it is a ratio of two `Finset` sums over
`SCIM.contextFiber`, a filtered `Finset.univ` over `ExoAssignment V edom`, while
print's `P(ε)` denotes at unbounded `V` as a product measure.

**The cost of closing it is now the machinery alone.** It used to be a
conditional expectation given a σ-algebra *plus* a reading of Definition 17 that
print does not supply, and the second half could not be priced from print. The
maintainer ruled that half on 2026-09-21 — the null-context reading above — so
what is left is a measure-theoretic conditional expectation and nothing
interpretive. Section 8 of the source coverage audit carries the cost.
-/

namespace AISafetyAtlas.Causal

variable {V : Type*} [Fintype V] [DecidableEq V] {dom edom : V → Type*}
  [∀ v, Fintype (dom v)] [∀ v, Fintype (edom v)] [∀ v, DecidableEq (dom v)]

namespace SCIM

variable (M : SCIM V dom edom)

/-! ## The total utility at a fixed exogenous draw

`SCIM.expectedUtility` already sums `P(ε)` against print's `U := Σ_{U ∈ 𝐔} U`,
with that inner sum written inline. Definition 17 compares two *different*
models evaluated at the same `ε`, so the inner sum has to name a function of the
model. `totalUtilityIn` is that function and `expectedUtility_eq_sum` is the
statement that nothing changed.
-/

/-- **`U(ε) = Σ_{U ∈ 𝐔} U(ε)`**, print's total utility, read off an arbitrary
structural model over this diagram's vertices rather than off `Mπ` alone.

The utility *values* are the SCIM's — print's *"utility variable domains are a
subset of `ℝ`"* is a property of the model, not of the intervention performed on
it — while the *states* are whatever `N` evaluates to. Definition 17 needs
exactly this split: `U_{X_d}` and `U` are the same real-valued readout of two
different submodels. -/
@[expose] public noncomputable def totalUtilityIn (N : SCM V dom edom)
    [N.IsWellFounded] (ε : ExoAssignment V edom) : ℝ :=
  ∑ u ∈ M.graph.utilities.attach,
    M.utilityValue u.1 ((M.graph.mem_utilities_iff u.1).mp u.2) (N.eval ε u.1)

omit [(v : V) → Fintype (dom v)] [(v : V) → Fintype (edom v)] [(v : V) → DecidableEq (dom v)] in
/-- Two models that agree on the utility vertices at `ε` have the same total
utility there. This is the whole of the arithmetic in Theorem 18's soundness:
the proof establishes an equality of *evaluations* and needs it as an equality
of *reals*. -/
public theorem totalUtilityIn_congr (N N' : SCM V dom edom)
    [N.IsWellFounded] [N'.IsWellFounded] (ε : ExoAssignment V edom)
    (h : ∀ u, M.graph.IsUtility u → N.eval ε u = N'.eval ε u) :
    M.totalUtilityIn N ε = M.totalUtilityIn N' ε := by
  unfold totalUtilityIn
  refine Finset.sum_congr rfl fun u _ ↦ ?_
  rw [h u.1 ((M.graph.mem_utilities_iff u.1).mp u.2)]

omit [(v : V) → Fintype (dom v)] [(v : V) → DecidableEq (dom v)] in
/-- `Eπ[U]` is `P(ε)` summed against `totalUtilityIn`, which is what
`expectedUtility` already writes with the inner sum inline. -/
public theorem expectedUtility_eq_sum [M.graph.IsWellFounded] (π : M.Policy) :
    M.expectedUtility π =
      ∑ ε : ExoAssignment V edom,
        (M.withPolicy π).exoJoint ε * M.totalUtilityIn (M.withPolicy π) ε :=
  rfl

/-! ## Forcing one vertex

`SCM.submodel` takes a total assignment and reads it only at the intervened
vertices, so `do(V = k)` needs some assignment carrying `k` at `V` and anything
at all elsewhere. `point` is that assignment, and print's requirement that every domain be inhabited is what makes one exist.
-/

/-- An assignment sending `v` to `k`, used only as the argument of a submodel at
`{v}`, where nothing else in it is read. -/
@[expose] public noncomputable def point (v : V) (k : dom v) : EndoAssignment V dom :=
  Function.update (fun w ↦ (M.dom_nonempty w).some) v k

omit [(v : V) → Fintype (dom v)] [(v : V) → Fintype (edom v)] [(v : V) → DecidableEq (dom v)] in
omit [Fintype V] in
@[simp] public theorem point_self (v : V) (k : dom v) :
    M.point v k v = k :=
  Function.update_self (β := fun w ↦ dom w) v k _

/-! ## The nested potential response

> If `W` is a variable in an SCM `M`, then `W_x` refers to the same variable in
> the submodel `M_x` and is called a *potential response variable*. … More
> elaborate hypotheticals can be described with a *nested counterfactual*, in
> which the intervention is itself a potential response variable.

`U_{X_d}(ε) := U_x(ε)` where `x = X_d(ε)`: two composed hard interventions, the
inner one at the decision and the outer one at `X`. Print is explicit that the
policy is fixed first: *"we first assign the policy `π*` then intervene to set
`D = d`, which renders `π*` effectively irrelevant but formally necessary for
creating an SCM."*
-/

/-- **`X_d(ε)`**, the potential response of `x` to `do(D = d)` under `π`. -/
@[expose] public noncomputable def responseTo [M.graph.IsWellFounded]
    (π : M.Policy) (D : V) (d : dom D) (ε : ExoAssignment V edom)
    (x : V) : dom x :=
  ((M.withPolicy π).submodel {D} (M.point D d)).eval ε x

/-- **`U_{X_d}(ε)`**, print's nested potential response: the total utility in the
model where `X` is forced to the value it would have taken under `do(D = d)`. -/
@[expose] public noncomputable def nestedUtility [M.graph.IsWellFounded]
    (π : M.Policy) (D : V) (d : dom D) (X : V)
    (ε : ExoAssignment V edom) : ℝ :=
  M.totalUtilityIn
    ((M.withPolicy π).submodel {X} (M.point X (M.responseTo π D d ε X))) ε

/-! ## Conditioning on a decision context -/

open Classical in
/-- The event `Pa^D = pa^D` in `Mπ`: the exogenous draws under which the
decision's observations take the given values. A *decision context* is carried
as a total assignment and read only at `Pa^D`, exactly as `point` is read only
at one vertex. -/
@[expose] public noncomputable def contextFiber [M.graph.IsWellFounded]
    (π : M.Policy) (D : V) (c : EndoAssignment V dom) :
    Finset (ExoAssignment V edom) :=
  Finset.univ.filter fun ε ↦ ∀ p ∈ M.graph.parents D, (M.withPolicy π).eval ε p = c p

/-- **`E_π[· | pa^D]`.** On a context of probability zero this is `0`, so
`HasICIAt` is false there; the module docstring says why that is the right
convention and why no theorem below depends on it. -/
@[expose] public noncomputable def condExp [M.graph.IsWellFounded]
    (π : M.Policy) (D : V) (c : EndoAssignment V dom)
    (g : ExoAssignment V edom → ℝ) : ℝ :=
  (∑ ε ∈ M.contextFiber π D c, (M.withPolicy π).exoJoint ε * g ε) /
    ∑ ε ∈ M.contextFiber π D c, (M.withPolicy π).exoJoint ε

omit [(v : V) → Fintype (dom v)] in
/-- Two integrands agreeing pointwise on the conditioning event have the same
conditional expectation, whatever the event's probability. This is what lets
Theorem 18's soundness stop at an equality of evaluations and never touch the
division. -/
public theorem condExp_congr [M.graph.IsWellFounded]
    (π : M.Policy) (D : V) (c : EndoAssignment V dom)
    {g g' : ExoAssignment V edom → ℝ}
    (h : ∀ ε ∈ M.contextFiber π D c, g ε = g' ε) :
    M.condExp π D c g = M.condExp π D c g' := by
  unfold condExp
  exact congrArg (· / _) (Finset.sum_congr rfl fun ε hε ↦ by rw [h ε hε])

/-! ## Definition 17 -/

/-- **Definition 17**, at one decision context.

> there is an *instrumental control incentive* on a variable `X` in decision
> context `pa^D` if, for all optimal policies `π*`,
> `E_{π*}[U_{X_d} | pa^D] ≠ E_{π*}[U | pa^D]`.

**`d` is existential, and print's own witness is why.** The displayed formula
leaves `d` free. Under a universal reading Theorem 18 is false: print's
completeness construction (its Lemma 30) builds a model in which `U_{X_d} = d`,
so the inequality holds at `d = 0` and fails at `d = 1`, and that model is
offered as a witness that the criterion is sufficient. The existential reading
is the only one under which the printed theorem is true, so it is the one
transcribed, with `d` inside the scope of the policy quantifier. -/
@[expose] public def HasICIAt [M.graph.IsWellFounded] (D X : V)
    (c : EndoAssignment V dom) : Prop :=
  ∀ π : M.Policy, M.IsOptimalPolicy π →
    ∃ d : dom D,
      M.condExp π D c (M.nestedUtility π D d X) ≠
        M.condExp π D c (M.totalUtilityIn (M.withPolicy π))

/-- **Definition 17**: an instrumental control incentive on `X`, at some
decision context. -/
@[expose] public def HasICI [M.graph.IsWellFounded] (D X : V) : Prop :=
  ∃ c : EndoAssignment V dom, M.HasICIAt D X c

end SCIM

/-! ## Causal irrelevance

Print's Lemma 20, at an empty conditioning set: *"For every SCM `M` compatible
with a DAG `G`, `(X ⇢̸ Y | Z)_G ⇒ (X ↛ Y | Z)`."* Theorem 18's soundness reads
this and nothing else about the graph.

The form proved here is the one that soundness consumes: forcing a vertex `x`
changes no vertex `y` that `x` does not reach. The proof is print's *"induction
over variables"* run as a well-founded induction on the parent relation, which
is available because `eval` is that recursion.
-/

namespace SCM

variable (N : SCM V dom edom)

omit [Fintype V] [(v : V) → Fintype (dom v)] [(v : V) → Fintype (edom v)] [(v : V) → DecidableEq (dom v)] in
/-- **Print's Lemma 20 at `Z = ∅`.** If `x` reaches `y` along no directed path
then `do(x = k)` leaves `y` at its factual value.

`IsDescendant` is stated on a `CID` and this is a bare `SCM`, so the reachability
hypothesis is spelled out here as the reflexive-transitive closure of this
model's own parent relation; `SCIM.withPolicy` keeps the diagram's parent map, so
the two agree wherever both are written. -/
public theorem eval_submodel_singleton_of_not_reaches [N.IsWellFounded]
    {x : V} (k : EndoAssignment V dom) (ε : ExoAssignment V edom) {y : V}
    (h : ¬ Relation.ReflTransGen (fun a b ↦ a ∈ N.parents b) x y) :
    (N.submodel {x} k).eval ε y = N.eval ε y := by
  induction y using (‹N.IsWellFounded›.wf).induction with
  | _ y ih =>
    have hxy : y ≠ x := fun hy ↦ h (hy ▸ Relation.ReflTransGen.refl)
    have hyX : y ∉ ({x} : Finset V) := by simpa using hxy
    rw [N.submodel_eval_notMem {x} k ε hyX, N.eval_eq_f ε y]
    exact N.f_parents y _ _ _ fun p hp ↦ ih p hp fun hpath ↦ h (hpath.tail hp)

omit [Fintype V] [(v : V) → Fintype (dom v)] [(v : V) → Fintype (edom v)] [(v : V) → DecidableEq (dom v)] in
/-- **Consistency**, the step print's soundness proof leaves implicit when it
concludes `U(ε) = U_{X_d}(ε)` from `X_d(ε) = X(ε)`: forcing a vertex to the value
it already takes at `ε` changes nothing anywhere.

Unlike `eval_submodel_singleton_of_not_reaches` this needs no reachability
hypothesis — it holds at every vertex, including `x` itself. -/
public theorem eval_submodel_singleton_of_eq [N.IsWellFounded]
    {x : V} (k : EndoAssignment V dom) (ε : ExoAssignment V edom)
    (hk : k x = N.eval ε x) (y : V) :
    (N.submodel {x} k).eval ε y = N.eval ε y := by
  induction y using (‹N.IsWellFounded›.wf).induction with
  | _ y ih =>
    by_cases hyx : y = x
    · subst hyx
      rw [N.submodel_eval {y} k ε (Finset.mem_singleton_self y)]
      exact hk
    · have hyX : y ∉ ({x} : Finset V) := by simpa using hyx
      rw [N.submodel_eval_notMem {x} k ε hyX, N.eval_eq_f ε y]
      exact N.f_parents y _ _ _ fun p hp ↦ ih p hp

end SCM

/-! ## Theorem 18, soundness

> If there is no directed path `D ⇢ X ⇢ 𝐔` in `G`, then either `D ⇢̸ X` or
> `X ⇢̸ 𝐔`. If `D ⇢̸ X`, then `X_d(ε) = X(ε)` for any setting `ε ∈ dom(𝓔)` and
> decision `d` (Lemma 20). Therefore, `U(ε) = U_{X_d}(ε)`. Similarly, if
> `X ⇢̸ 𝐔` then `U(ε) = U_x(ε)` for every setting `ε`, `x`, and `U ∈ 𝐔` so
> `U(ε) = U_{X_d}(ε)`. In either case, `E_π[U | pa^D] = E_π[U_{X_d} | pa^D]` and
> there is no instrumental control incentive on `X`.

The step print leaves implicit in the first branch is **consistency**: when the
forced value *is* the factual value, forcing changes nothing. That is
`eval_submodel_singleton_of_not_reaches` used at `y = X` in the second branch
and, in the first, the observation that `X_d(ε) = X(ε)` makes the outer
intervention an intervention at the value already taken.
-/

namespace SCIM

variable (M : SCIM V dom edom)

/-- **Print's `D ⇢ X ⇢ 𝐔`**, the right-hand side of Theorem 18.

Written as a conjunction of two reachability facts rather than as one path
through `X`. The two agree on a diagram: concatenating a directed walk `D ⇢ X`
with a directed walk `X ⇢ U` gives a directed walk `D ⇢ U` through `X`, and on
an acyclic graph a directed walk cannot repeat a vertex, so it is a path. Print's
own soundness argument uses the conjunctive form — *"either `D ⇢̸ X` or
`X ⇢̸ 𝐔`"* — and its completeness argument produces the single path. -/
@[expose] public def PathThrough (D X : V) : Prop :=
  M.graph.IsDescendant D X ∧ ∃ u, M.graph.IsUtility u ∧ M.graph.IsDescendant X u

omit [(v : V) → Fintype (dom v)] [(v : V) → Fintype (edom v)] [(v : V) → DecidableEq (dom v)] in
/-- **The nested potential response equals the factual utility** at every `ε`,
whenever `X` lies off every path from the decision to a utility node. This is the
whole content of Theorem 18's soundness; everything after it is the observation
that equal integrands give equal conditional expectations. -/
public theorem nestedUtility_eq_of_not_pathThrough [M.graph.IsWellFounded]
    {D X : V} (h : ¬ M.PathThrough D X) (π : M.Policy) (d : dom D)
    (ε : ExoAssignment V edom) :
    M.nestedUtility π D d X ε = M.totalUtilityIn (M.withPolicy π) ε := by
  unfold nestedUtility
  rw [PathThrough, not_and_or] at h
  rcases h with hDX | hXU
  · -- `D ⇢̸ X`, so `X_d(ε) = X(ε)` and the outer intervention is at the factual
    -- value: consistency finishes it, at every vertex rather than only at `𝐔`.
    have hval : M.responseTo π D d ε X = (M.withPolicy π).eval ε X :=
      (M.withPolicy π).eval_submodel_singleton_of_not_reaches _ ε hDX
    exact M.totalUtilityIn_congr _ _ ε fun u _ ↦
      (M.withPolicy π).eval_submodel_singleton_of_eq _ ε
        (by rw [M.point_self, hval]) u
  · -- `X ⇢̸ 𝐔`, so forcing `X` moves no utility vertex, whatever it is forced to.
    push Not at hXU
    exact M.totalUtilityIn_congr _ _ ε fun u hu ↦
      (M.withPolicy π).eval_submodel_singleton_of_not_reaches _ ε (hXU u hu)

/-- **Theorem 18, soundness** (print's *only if*). Off every directed path from
the decision through `X` to a utility node there is no instrumental control
incentive on `X`, in **any** compatible model and at **any** decision context. -/
public theorem not_hasICI_of_not_pathThrough [M.graph.IsWellFounded]
    {D X : V} (h : ¬ M.PathThrough D X) : ¬ M.HasICI D X := by
  rintro ⟨c, hc⟩
  obtain ⟨π, hπ, -⟩ := M.exists_isOptimalPolicy
  obtain ⟨d, hd⟩ := hc π hπ
  exact hd (M.condExp_congr π D c fun ε _ ↦
    M.nestedUtility_eq_of_not_pathThrough h π d ε)

end SCIM

/-! ## Theorem 18, completeness

> **Lemma 30** (ICI Criterion Completeness). *If a single-decision CID `G`
> contains a path of the form `D ⇢ X ⇢ 𝐔` then there is an instrumental control
> incentive on `X` in at least one SCIM `M` compatible with `G`.*
>
> *Proof.* Assume that `G` contains a directed path `D = Z⁰ → Z¹ → ⋯ → Zⁿ = U`
> where `U ∈ 𝐔` and `Zⁱ = X` for some `i ∈ {0, …, n}`. We construct a compatible
> SCIM for which there is an instrumental control incentive on `X`. Let all
> variables along the path `Z⁰ → … → Zⁿ` be equal to their predecessor, except
> `Z⁰ = D`, which has no structure function. All other variables are set to `0`.

**The construction here copies along reachability rather than along a chosen
path**, and that is a deliberate departure from print's own proof. Extracting a
path and giving each vertex on it a predecessor is real work in a formalization
— a list, a `Chain`, and a `Nodup` argument from acyclicity — and it buys
nothing, because the two-segment reachability predicates below have exactly the
propagation property the copy chain was for. What print needs is that `U`'s
value is `X`'s and `X`'s is `D`'s; `Seg1` and `Seg2` deliver that directly.

**Copying along a single reachability predicate would be wrong**, and the reason
is worth recording. If a vertex copied whenever it lay between `D` and `𝐔`, a
diagram with a second route `D → Y → U` bypassing `X` would carry the decision's
value to `U` without passing through `X`, forcing `X` would change nothing, and
the constructed model would have no incentive. Splitting at `X` is what closes
that: every `Seg2` vertex is a descendant of `X`, so forcing `X` moves all of
them, whatever else the diagram contains.
-/

namespace CID

variable (G : CID V)

/-- Vertices between the decision and `X`. -/
@[expose] public def Seg1 (D X v : V) : Prop :=
  G.IsDescendant D v ∧ G.IsDescendant v X

/-- Vertices between `X` and the utility node. -/
@[expose] public def Seg2 (X U v : V) : Prop :=
  G.IsDescendant X v ∧ G.IsDescendant v U

/-- **The hypothesis Theorem 18's completeness actually needs.**

Print writes *"a single-decision CID"*, and that is sufficient rather than
necessary. What the construction below needs is only that **no decision other
than `D` sits where the construction writes**: on either segment, or among `D`'s
own observations. A diagram may carry any number of other decisions elsewhere.

Both clauses are load-bearing, and each fails for its own reason.

* **A decision on a segment can cut the chain.** Its structural function is the
  agent's, not the model's, so a policy that ignores its parents and plays `1`
  makes the utility constant. That policy is *optimal* — the utility is already
  at its maximum — and under it `X` no longer moves with the decision, so the
  incentive is absent at an optimal policy and Definition 17 fails.
* **A decision among `Pa^D` can move the decision context.** Definition 17 fixes
  one context and quantifies over optimal policies inside it. An off-segment
  decision contributes nothing to the utility, so *every* value it plays is
  optimal, and no single context has positive probability under all of them.

`D` itself is exempt, and **`D` need not be a decision at all** — see
`iciWitness_hasICI`, which asks nothing of it.

**The first clause is witnessed, not merely argued.**
`Examples.Causal.Incentive.segSCIM_not_hasICI` is a diagram `D → D' → X → U`
with `D'` a second decision on the near segment, carrying the path in full, and a
compatible SCIM over it with **no** instrumental control incentive on `X`; the
policy that does it is proved optimal by `segConstPolicy_optimal`. That is the
mechanism above, machine-checked. It is not a refutation of Theorem 18's
criterion on that diagram — `¬ AdmitsICI` quantifies over every compatible SCIM
and this is one — and that question is open. The second clause is argued here and
has no such witness. -/
@[expose] public def DecisionFree (G : CID V) (D X U : V) : Prop :=
  ∀ w, G.IsDecision w → w ≠ D →
    ¬ G.Seg1 D X w ∧ ¬ G.Seg2 X U w ∧ w ∉ G.parents D

/-- Print's single-decision restriction is one way to satisfy `DecisionFree`,
and the way Theorem 18 states. -/
public theorem decisionFree_of_singleDecision {G : CID V} {D : V}
    (hD : G.decisions = {D}) (X U : V) : G.DecisionFree D X U := fun w hw hne ↦
  absurd (Finset.mem_singleton.mp (hD ▸ (G.mem_decisions_iff w).mpr hw)) hne

variable {G}

omit [Fintype V] in
/-- The two segments meet only at `X`: a vertex on both sides of `X` reaches `X`
and is reached by it, which on an acyclic diagram makes it `X`. -/
public theorem eq_of_seg1_of_seg2 {D X U v : V}
    (h1 : G.Seg1 D X v) (h2 : G.Seg2 X U v) : v = X := by
  rcases Relation.reflTransGen_iff_eq_or_transGen.mp h1.2 with h | h
  · exact h.symm
  · exact absurd (h.trans_left h2.1) (G.acyclic v)

omit [Fintype V] in
/-- A segment vertex other than its own root has a parent in the same segment.
This is what the propagation induction steps along. -/
public theorem exists_parent_reflTransGen {a v : V}
    (h : Relation.ReflTransGen (fun p w ↦ p ∈ G.parents w) a v) (hv : v ≠ a) :
    ∃ p ∈ G.parents v, Relation.ReflTransGen (fun p w ↦ p ∈ G.parents w) a p := by
  rcases Relation.ReflTransGen.cases_tail h with rfl | ⟨p, hap, hpv⟩
  · exact absurd rfl hv
  · exact ⟨p, hpv, hap⟩

end CID

/-! ## The witnessing model -/

namespace SCIM

/-- Every domain is `{0, 1}` and nothing is random: print's Lemma 30 sets every
domain to `{0, 1}` and its model reads no noise. -/
public abbrev binDom : V → Type := fun _ ↦ Fin 2

/-- One exogenous state per variable, so the policies are the deterministic
ones and `ExoAssignment` is a singleton. -/
public abbrev unitExo : V → Type := fun _ ↦ Fin 1

open Classical in
/-- The structural function of the witnessing model: a vertex on the far segment
copies the far segment, a vertex on the near segment copies the near segment,
and everything else is `0`.

Reachability is not decidable at an arbitrary vertex type, so the branches are
decided classically; the model is a witness and is never run.

`X` itself falls to the near branch — it is on both segments and the far branch
excludes it — which is what makes `X` copy `D` while everything beyond `X` copies
`X`. -/
@[expose] public noncomputable def iciF (G : CID V) (D X U v : V)
    (a : EndoAssignment V (binDom (V := V))) : Fin 2 :=
  if G.Seg2 X U v ∧ v ≠ X then
    (if ∃ p ∈ G.parents v, G.Seg2 X U p ∧ a p = 1 then 1 else 0)
  else if G.Seg1 D X v then
    (if ∃ p ∈ G.parents v, G.Seg1 D X p ∧ a p = 1 then 1 else 0)
  else 0

/-- **Print's Lemma 30 model.** -/
@[expose] public noncomputable def iciWitness (G : CID V) (D X U : V) :
    SCIM V (binDom (V := V)) (unitExo (V := V)) where
  dom_nonempty := fun _ ↦ ⟨0⟩
  graph := G
  utilityValue := fun _ _ i ↦ (i.val : ℝ)
  utilityValue_injective := fun _ _ i j h ↦
    Fin.ext (Nat.cast_injective (R := ℝ) h)
  f := fun v _ a _ ↦ iciF G D X U v a
  f_parents := fun v _ a b _ hab ↦ by
    classical
    unfold iciF
    have hcong : ∀ Seg : V → Prop,
        (∃ p ∈ G.parents v, Seg p ∧ a p = 1) ↔ ∃ p ∈ G.parents v, Seg p ∧ b p = 1 :=
      fun Seg ↦ ⟨fun ⟨p, hp, hs, he⟩ ↦ ⟨p, hp, hs, (hab p hp) ▸ he⟩,
        fun ⟨p, hp, hs, he⟩ ↦ ⟨p, hp, hs, (hab p hp).symm ▸ he⟩⟩
    by_cases h2 : G.Seg2 X U v ∧ v ≠ X
    · rw [if_pos h2, if_pos h2]
      exact if_congr (hcong _) rfl rfl
    · rw [if_neg h2, if_neg h2]
      by_cases h1 : G.Seg1 D X v
      · rw [if_pos h1, if_pos h1]
        exact if_congr (hcong _) rfl rfl
      · rw [if_neg h1, if_neg h1]
  exoProb := fun _ _ ↦ 1
  exoProb_nonneg := fun _ _ ↦ zero_le_one
  exoProb_tsum := fun _ ↦ by simp

@[simp] public theorem iciWitness_graph (G : CID V) (D X U : V) :
    (iciWitness G D X U).graph = G := rfl

/-- The witness is evaluable exactly when the diagram it is built on is: it
carries that diagram unchanged. -/
public instance instIsWellFoundedIciWitness (G : CID V) (D X U : V)
    [h : G.IsWellFounded] : (iciWitness G D X U).graph.IsWellFounded := h

/-! ### Propagation

One induction, used three times: in the factual model along `Seg1` from `D`, in
the model where `D` is forced along `Seg1` from `D` again, and in the model where
`X` is forced along `Seg2` from `X`. Everything print's copy chain does is here.
-/

open Classical in
/-- A vertex in a segment takes the segment root's value, whenever every
non-root vertex of the segment has a parent in it and copies its segment
parents. Print's *"let all variables along the path be equal to their
predecessor"*, with reachability in place of the path. -/
public theorem seg_propagate {N : SCM V (binDom (V := V)) (unitExo (V := V))}
    [hN : N.IsWellFounded] (Seg : V → Prop) (root : V)
    (hpar : ∀ v, Seg v → v ≠ root → ∃ p ∈ N.parents v, Seg p)
    (hf : ∀ v, Seg v → v ≠ root → ∀ (a : EndoAssignment V (binDom (V := V)))
        (e : unitExo (V := V) v),
        N.f v a e = if ∃ p ∈ N.parents v, Seg p ∧ a p = 1 then 1 else 0)
    (ε : ExoAssignment V (unitExo (V := V))) (v : V) (hv : Seg v) :
    N.eval ε v = N.eval ε root := by
  induction v using hN.wf.induction with
  | _ v ih =>
    by_cases hvr : v = root
    · rw [hvr]
    · rw [N.eval_eq_f ε v, hf v hv hvr]
      obtain ⟨y, hy⟩ : ∃ y : Fin 2, N.eval ε root = y := ⟨_, rfl⟩
      by_cases h1 : y = 1
      · obtain ⟨p, hp, hsp⟩ := hpar v hv hvr
        rw [if_pos ⟨p, hp, hsp, by rw [ih p hp hsp, hy, h1]⟩, hy, h1]
      · have hy0 : y = 0 := by fin_cases y <;> simp_all
        have hno : ¬ ∃ p ∈ N.parents v, Seg p ∧ N.eval ε p = 1 := by
          rintro ⟨p, hp, hsp, he⟩
          rw [ih p hp hsp, hy] at he
          exact h1 he
        rw [if_neg hno, hy, hy0]

/-! ### The three branches of `iciF`, read off -/

variable {G : CID V} {D X U v : V}

open Classical in
/-- A near-segment vertex copies the near segment. The far branch cannot fire at
one, because a vertex on both segments is `X`, which the far branch excludes. -/
public theorem iciF_seg1 (h1 : G.Seg1 D X v) (a : EndoAssignment V (binDom (V := V))) :
    iciF G D X U v a =
      if ∃ p ∈ G.parents v, G.Seg1 D X p ∧ a p = 1 then 1 else 0 := by
  unfold iciF
  rw [if_neg fun h ↦ h.2 (CID.eq_of_seg1_of_seg2 h1 h.1), if_pos h1]

open Classical in
/-- A far-segment vertex other than `X` copies the far segment. -/
public theorem iciF_seg2 (h2 : G.Seg2 X U v) (hne : v ≠ X)
    (a : EndoAssignment V (binDom (V := V))) :
    iciF G D X U v a =
      if ∃ p ∈ G.parents v, G.Seg2 X U p ∧ a p = 1 then 1 else 0 := by
  unfold iciF
  rw [if_pos ⟨h2, hne⟩]

open Classical in
/-- *"All other variables are set to `0`."* -/
public theorem iciF_none (h1 : ¬ G.Seg1 D X v) (h2 : ¬ G.Seg2 X U v)
    (a : EndoAssignment V (binDom (V := V))) : iciF G D X U v a = 0 := by
  unfold iciF
  rw [if_neg fun h ↦ h2 h.1, if_neg h1]

/-- An off-segment vertex evaluates to `0` in any model whose structural
function there is the witness's. -/
public theorem eval_zero_of_not_seg {N : SCM V (binDom (V := V)) (unitExo (V := V))}
    [N.IsWellFounded]
    (hf : ∀ (a : EndoAssignment V (binDom (V := V))) (e : unitExo (V := V) v),
      N.f v a e = iciF G D X U v a)
    (h1 : ¬ G.Seg1 D X v) (h2 : ¬ G.Seg2 X U v)
    (ε : ExoAssignment V (unitExo (V := V))) : N.eval ε v = 0 := by
  rw [N.eval_eq_f ε v, hf, iciF_none h1 h2]

/-! ### What the two segments contain

Three facts, each of which the construction turns on and none of which is about
the model: a segment vertex other than its root has a parent in the segment, a
utility node reaches only itself, and no parent of the decision is on either
segment. The last is what makes the single decision context have probability one.
-/

omit [Fintype V] in
/-- **A utility node reaches nothing but itself**: *"utility nodes have no
children"*, read along a directed path. -/
public theorem eq_of_isUtility_isDescendant {u w : V} (hu : G.IsUtility u)
    (h : G.IsDescendant u w) : u = w := by
  rcases Relation.ReflTransGen.cases_head h with rfl | ⟨b, hb, -⟩
  · rfl
  · exact absurd hb (G.utility_childless u hu b)

omit [Fintype V] in
/-- Every utility node but `U` is off both segments, so it contributes `0` to the
total utility. -/
public theorem not_seg_of_isUtility_ne {u : V}
    (hXU : G.IsDescendant X U) (hu : G.IsUtility u) (hne : u ≠ U) :
    ¬ G.Seg1 D X u ∧ ¬ G.Seg2 X U u := by
  refine ⟨fun h1 ↦ hne ?_, fun h2 ↦ hne (eq_of_isUtility_isDescendant hu h2.2)⟩
  have hux : u = X := eq_of_isUtility_isDescendant hu h1.2
  exact hux.trans (eq_of_isUtility_isDescendant (hux ▸ hu) hXU)

omit [Fintype V] in
/-- **No parent of the decision is on either segment.** A parent on the near
segment closes a cycle at the decision, and one on the far segment closes the
same cycle through `X`. -/
public theorem not_seg_of_mem_parents_decision (hDX : G.IsDescendant D X)
    {p : V} (hp : p ∈ G.parents D) :
    ¬ G.Seg1 D X p ∧ ¬ G.Seg2 X U p := by
  have key : ∀ q, G.IsDescendant D q → q ∉ G.parents D := fun q hq hqp ↦
    G.acyclic D (Relation.TransGen.tail' hq hqp)
  exact ⟨fun h1 ↦ key p h1.1 hp, fun h2 ↦ key p (hDX.trans h2.1) hp⟩

omit [Fintype V] in
/-- A far-segment vertex other than `X` is not the decision: the decision reaches
`X`, so a vertex `X` reaches cannot be it without collapsing the two. -/
public theorem ne_decision_of_seg2 (hDX : G.IsDescendant D X)
    (h2 : G.Seg2 X U v) (hne : v ≠ X) : v ≠ D := by
  rintro rfl
  exact hne (CID.eq_of_seg1_of_seg2 ⟨Relation.ReflTransGen.refl, hDX⟩ h2)

/-! ### The two segments, evaluated

`seg_propagate` specialised to each segment. Both are stated at an arbitrary
model that agrees with the witness where the induction looks, so the factual
model and both counterfactual submodels are instances of the same two lemmas.
-/

open Classical in
/-- Everything between the decision and `X` takes the decision's value. -/
public theorem seg1_eval {N : SCM V (binDom (V := V)) (unitExo (V := V))}
    [N.IsWellFounded]
    (hpar : ∀ w, G.Seg1 D X w → w ≠ D → N.parents w = G.parents w)
    (hf : ∀ w, G.Seg1 D X w → w ≠ D → ∀ (a : EndoAssignment V (binDom (V := V)))
      (e : unitExo (V := V) w), N.f w a e = iciF G D X U w a)
    (ε : ExoAssignment V (unitExo (V := V))) (hv : G.Seg1 D X v) :
    N.eval ε v = N.eval ε D := by
  refine seg_propagate (G.Seg1 D X) D ?_ ?_ ε v hv
  · intro w hw hwD
    obtain ⟨p, hp, hDp⟩ := CID.exists_parent_reflTransGen hw.1 hwD
    exact ⟨p, (hpar w hw hwD) ▸ hp, hDp, Relation.ReflTransGen.head hp hw.2⟩
  · intro w hw hwD a e
    rw [hf w hw hwD, iciF_seg1 hw, hpar w hw hwD]

open Classical in
/-- Everything between `X` and the utility node takes `X`'s value. This is the
half that forcing `X` moves, and the reason the construction splits at `X`. -/
public theorem seg2_eval {N : SCM V (binDom (V := V)) (unitExo (V := V))}
    [N.IsWellFounded]
    (hpar : ∀ w, G.Seg2 X U w → w ≠ X → N.parents w = G.parents w)
    (hf : ∀ w, G.Seg2 X U w → w ≠ X → ∀ (a : EndoAssignment V (binDom (V := V)))
      (e : unitExo (V := V) w), N.f w a e = iciF G D X U w a)
    (ε : ExoAssignment V (unitExo (V := V))) (hv : G.Seg2 X U v) :
    N.eval ε v = N.eval ε X := by
  refine seg_propagate (G.Seg2 X U) X ?_ ?_ ε v hv
  · intro w hw hwX
    obtain ⟨p, hp, hXp⟩ := CID.exists_parent_reflTransGen hw.1 hwX
    exact ⟨p, (hpar w hw hwX) ▸ hp, hXp, Relation.ReflTransGen.head hp hw.2⟩
  · intro w hw hwX a e
    rw [hf w hw hwX, iciF_seg2 hw hwX, hpar w hw hwX]

/-- `𝐔`'s only contributing member is `U`, so the total utility is `U`'s state
read as a real. -/
public theorem iciWitness_totalUtility
    {N : SCM V (binDom (V := V)) (unitExo (V := V))} [N.IsWellFounded]
    (hU : G.IsUtility U) (hXU : G.IsDescendant X U)
    (hf : ∀ w, G.IsUtility w → w ≠ U → ∀ (a : EndoAssignment V (binDom (V := V)))
      (e : unitExo (V := V) w), N.f w a e = iciF G D X U w a)
    (ε : ExoAssignment V (unitExo (V := V))) :
    (iciWitness G D X U).totalUtilityIn N ε = ((N.eval ε U).val : ℝ) := by
  have hval : ∀ u ∈ (iciWitness G D X U).graph.utilities.attach,
      (iciWitness G D X U).utilityValue u.1
          (((iciWitness G D X U).graph.mem_utilities_iff u.1).mp u.2)
          (N.eval ε u.1) = ((N.eval ε u.1).val : ℝ) := fun _ _ ↦ rfl
  rw [SCIM.totalUtilityIn, Finset.sum_congr rfl hval,
    Finset.sum_attach _ fun u ↦ ((N.eval ε u).val : ℝ)]
  refine Finset.sum_eq_single U (fun u hu hne ↦ ?_) (fun hU' ↦ ?_)
  · have hIsU : G.IsUtility u := (G.mem_utilities_iff u).mp hu
    obtain ⟨h1, h2⟩ := not_seg_of_isUtility_ne hXU hIsU hne
    rw [eval_zero_of_not_seg (hf u hIsU hne) h1 h2]
    simp
  · exact absurd ((G.mem_utilities_iff U).mpr hU) hU'

/-! ### The witness, evaluated

The decision is the one vertex whose function the policy supplies, so every
other vertex keeps `iciF` in `Mπ` and in both submodels. From there the two
segment lemmas give the three values print's proof needs: `U`'s factual value is
the decision's, `X`'s value under `do(D = d)` is `d`, and `U`'s value once `X` is
forced to `d` is `d`.
-/

omit [Fintype V] in
/-- A utility vertex is not a decision: `kind` is one function and the two
predicates read it at different values. This needs nothing about how many
decisions the diagram has. -/
public theorem not_isDecision_of_isUtility {w : V} (hw : G.IsUtility w) :
    ¬ G.IsDecision w := fun h ↦ by
  rw [CID.IsDecision, hw] at h; exact absurd h (by decide)

/-- **At any non-decision vertex, `Mπ` is the witness.** The policy supplies a
structural function at the decisions and nowhere else, which is Definition 4's
asymmetry, so this is the only hypothesis the construction ever needs about a
vertex. -/
public theorem iciWitness_withPolicy_f (π : (iciWitness G D X U).Policy)
    {w : V} (hw : ¬ G.IsDecision w)
    (a : EndoAssignment V (binDom (V := V))) (e : unitExo (V := V) w) :
    ((iciWitness G D X U).withPolicy π).f w a e = iciF G D X U w a :=
  SCIM.withPolicy_f_notMem (iciWitness G D X U) π hw a e

omit [Fintype V] in
/-- A near-segment vertex other than `D` is not a decision, under `DecisionFree`. -/
public theorem not_isDecision_of_seg1 (hfree : G.DecisionFree D X U)
    (hw : G.Seg1 D X v) (hne : v ≠ D) : ¬ G.IsDecision v :=
  fun h ↦ (hfree v h hne).1 hw

omit [Fintype V] in
/-- A far-segment vertex other than `X` is not a decision, under `DecisionFree`
together with the fact that such a vertex is not `D` either. -/
public theorem not_isDecision_of_seg2 (hfree : G.DecisionFree D X U)
    (hDX : G.IsDescendant D X) (hw : G.Seg2 X U v) (hne : v ≠ X) :
    ¬ G.IsDecision v :=
  fun h ↦ (hfree v h (ne_decision_of_seg2 hDX hw hne)).2.1 hw

omit [Fintype V] in
/-- An observation of `D` other than `D` is not a decision, under
`DecisionFree`. -/
public theorem not_isDecision_of_mem_parents_decision (hfree : G.DecisionFree D X U)
    {p : V} (hp : p ∈ G.parents D) (hne : p ≠ D) : ¬ G.IsDecision p :=
  fun h ↦ (hfree p h hne).2.2 hp

variable [G.IsWellFounded]

/-- **`U(ε)` is the decision's own bit.** `X` copies `D` along the near segment
and `U` copies `X` along the far one. -/
public theorem iciWitness_factualUtility (hfree : G.DecisionFree D X U)
    (hU : G.IsUtility U) (hDX : G.IsDescendant D X) (hXU : G.IsDescendant X U)
    (π : (iciWitness G D X U).Policy)
    (ε : ExoAssignment V (unitExo (V := V))) :
    (iciWitness G D X U).totalUtilityIn ((iciWitness G D X U).withPolicy π) ε =
      ((((iciWitness G D X U).withPolicy π).eval ε D).val : ℝ) := by
  have hUeq : ((iciWitness G D X U).withPolicy π).eval ε U =
      ((iciWitness G D X U).withPolicy π).eval ε D := by
    rw [seg2_eval (fun _ _ _ ↦ rfl)
        (fun w hw hwX ↦ iciWitness_withPolicy_f π
          (not_isDecision_of_seg2 hfree hDX hw hwX)) ε
        ⟨hXU, Relation.ReflTransGen.refl⟩,
      seg1_eval (fun _ _ _ ↦ rfl)
        (fun w hw hwD ↦ iciWitness_withPolicy_f π
          (not_isDecision_of_seg1 hfree hw hwD)) ε
        ⟨hDX, Relation.ReflTransGen.refl⟩]
  rw [iciWitness_totalUtility hU hXU
    (fun w hw _ ↦ iciWitness_withPolicy_f π (not_isDecision_of_isUtility hw)) ε]
  rw [hUeq]

/-- **`X_d(ε) = d`.** Forcing the decision to `d` carries `d` down the near
segment to `X`. -/
public theorem iciWitness_responseTo (hfree : G.DecisionFree D X U)
    (hDX : G.IsDescendant D X) (π : (iciWitness G D X U).Policy)
    (d : binDom (V := V) D) (ε : ExoAssignment V (unitExo (V := V))) :
    (iciWitness G D X U).responseTo π D d ε X = d := by
  rw [SCIM.responseTo,
    seg1_eval
      (fun w _ hwD ↦ by simp [SCM.submodel, Finset.mem_singleton, hwD])
      (fun w hw hwD a e ↦ by
        simp only [SCM.submodel, Finset.mem_singleton, if_neg hwD]
        exact iciWitness_withPolicy_f π (not_isDecision_of_seg1 hfree hw hwD) a e)
      ε ⟨hDX, Relation.ReflTransGen.refl⟩,
    SCM.submodel_eval _ {D} _ ε (Finset.mem_singleton_self D), SCIM.point_self]

/-- **`U_{X_d}(ε) = d`.** Forcing `X` to what it would have been under
`do(D = d)` carries `d` down the far segment to `U`, and every other utility
vertex is off both segments and contributes nothing. -/
public theorem iciWitness_nestedUtility (hfree : G.DecisionFree D X U)
    (hU : G.IsUtility U) (hDX : G.IsDescendant D X) (hXU : G.IsDescendant X U)
    (π : (iciWitness G D X U).Policy) (d : binDom (V := V) D)
    (ε : ExoAssignment V (unitExo (V := V))) :
    (iciWitness G D X U).nestedUtility π D d X ε = (d.val : ℝ) := by
  have hXne : ∀ w, G.IsUtility w → w ≠ U → w ≠ X := by
    intro w hw hne hwX
    exact hne ((hwX ▸ hw : G.IsUtility X) |> fun h ↦
      hwX.trans (eq_of_isUtility_isDescendant h hXU))
  rw [SCIM.nestedUtility,
    iciWitness_totalUtility hU hXU
      (fun w hw hne a e ↦ by
        simp only [SCM.submodel, Finset.mem_singleton, if_neg (hXne w hw hne)]
        exact iciWitness_withPolicy_f π (not_isDecision_of_isUtility hw) a e) ε,
    seg2_eval
      (fun w _ hwX ↦ by simp [SCM.submodel, Finset.mem_singleton, hwX])
      (fun w hw hwX a e ↦ by
        simp only [SCM.submodel, Finset.mem_singleton, if_neg hwX]
        exact iciWitness_withPolicy_f π
          (not_isDecision_of_seg2 hfree hDX hw hwX) a e)
      ε ⟨hXU, Relation.ReflTransGen.refl⟩,
    SCM.submodel_eval _ {X} _ ε (Finset.mem_singleton_self X), SCIM.point_self,
    iciWitness_responseTo hfree hDX π d ε]

/-! ### Conditioning at the witness

Print's Lemma 30 evaluates at the context `𝐏𝐚^D = 𝟎`. Here that context has
probability one — no parent of the decision is on either segment, so every
observation is `0` at every draw — and the exogenous space is a single point, so
both conditional expectations are their integrand there and the division
convention never arises.
-/

public instance instUniqueUnitExo : Unique (ExoAssignment V (unitExo (V := V))) :=
  inferInstanceAs (Unique ((_ : V) → Fin 1))

omit [G.IsWellFounded] in
public theorem iciWitness_exoJoint (π : (iciWitness G D X U).Policy)
    (ε : ExoAssignment V (unitExo (V := V))) :
    ((iciWitness G D X U).withPolicy π).exoJoint ε = 1 := by
  simp [SCM.exoJoint, SCIM.withPolicy, iciWitness]

/-- **The decision context `𝐏𝐚^D = 𝟎` has probability one.** -/
public theorem iciWitness_contextFiber (hfree : G.DecisionFree D X U)
    (hDX : G.IsDescendant D X) (π : (iciWitness G D X U).Policy) :
    (iciWitness G D X U).contextFiber π D (fun _ ↦ 0) = Finset.univ := by
  classical
  ext ε
  simp only [SCIM.contextFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    iff_true]
  intro p hp
  have hpD : p ≠ D := by
    rintro rfl
    exact G.acyclic p (Relation.TransGen.single hp)
  obtain ⟨h1, h2⟩ := not_seg_of_mem_parents_decision (U := U) hDX hp
  exact eval_zero_of_not_seg
    (fun a e ↦ iciWitness_withPolicy_f π
      (not_isDecision_of_mem_parents_decision hfree hp hpD) a e) h1 h2 ε

/-- Conditioning at that context is evaluation at the single exogenous draw. -/
public theorem iciWitness_condExp (hfree : G.DecisionFree D X U)
    (hDX : G.IsDescendant D X) (π : (iciWitness G D X U).Policy)
    (g : ExoAssignment V (unitExo (V := V)) → ℝ) :
    (iciWitness G D X U).condExp π D (fun _ ↦ 0) g = g default := by
  rw [SCIM.condExp, iciWitness_contextFiber hfree hDX π]
  simp [iciWitness_exoJoint]

/-! ### Lemma 30 -/

/-- **Stronger than Definition 17 at this witness.** Print's model is arranged so
that it has a unique optimal policy, and reads the incentive off that. Here the
inequality holds at **every** policy, optimal or not: whatever the policy plays
at the realized context, the counterfactual decision that disagrees with it
separates the two conditional expectations.

Definition 17 quantifies over optimal policies, so `iciWitness_hasICI` is the
immediate corollary — and the analysis of *which* policies are optimal, which is
the expensive step in print's proof, never has to be done. -/
public theorem iciWitness_forall_policy (hfree : G.DecisionFree D X U)
    (hU : G.IsUtility U) (hDX : G.IsDescendant D X) (hXU : G.IsDescendant X U)
    (π : (iciWitness G D X U).Policy) :
    ∃ d : binDom (V := V) D,
      (iciWitness G D X U).condExp π D (fun _ ↦ 0)
          ((iciWitness G D X U).nestedUtility π D d X) ≠
        (iciWitness G D X U).condExp π D (fun _ ↦ 0)
          ((iciWitness G D X U).totalUtilityIn
            ((iciWitness G D X U).withPolicy π)) := by
  obtain ⟨b, hb⟩ : ∃ b : Fin 2,
      ((iciWitness G D X U).withPolicy π).eval default D = b := ⟨_, rfl⟩
  refine ⟨if b = 0 then 1 else 0, ?_⟩
  rw [iciWitness_condExp hfree hDX, iciWitness_condExp hfree hDX,
    iciWitness_nestedUtility hfree hU hDX hXU,
    iciWitness_factualUtility hfree hU hDX hXU, hb]
  intro h
  have hn : (if b = 0 then (1 : Fin 2) else 0).val = b.val := Nat.cast_injective h
  fin_cases b <;> simp at hn

/-- **Print's Lemma 30**, the completeness half of Theorem 18.

**What the `∃ d` reading is and is not settled by.** `HasICIAt` reads
`∀ π*, ∃ d`, which is print's `∃ d` in print's own quantifier order; the module
docstring gives the argument for `∃ d` over `∀ d`, and it is print's own Lemma 30
witness. The *stronger* order `∃ d, ∀ π*` is **not** claimed and is not proved
here. It may well hold of this witness — in print's case, where `D` is the diagram's
only decision, every optimal policy plays `1` and `d = 0` serves all of them —
but that is exactly the which-policies-are-optimal analysis
`iciWitness_forall_policy` is arranged to avoid, and it is not even the right
sentence once `D` is allowed not to be a decision, where `D` evaluates to `0`
under every policy and `d = 1` is what serves. Print states the weaker order and
so does this. -/
public theorem iciWitness_hasICI (hfree : G.DecisionFree D X U) (hU : G.IsUtility U)
    (hDX : G.IsDescendant D X) (hXU : G.IsDescendant X U) :
    (iciWitness G D X U).HasICI D X :=
  ⟨fun _ ↦ 0, fun π _ ↦ iciWitness_forall_policy hfree hU hDX hXU π⟩

end SCIM

namespace CID

/-! ## Theorem 18 -/

/-- **Print's *"a CID `G` admits an instrumental control incentive on `X`"***:
some SCIM compatible with `G` has one.

Domains live on the SCIM rather than on the diagram, so they are existentially
quantified here, and so is the diagram's evaluability: print's `Eπ[U]` denotes
only on a diagram whose recursion determines a value, and a model that supplies
the incentive supplies that too. -/
@[expose] public def AdmitsICI (G : CID V) (D X : V) : Prop :=
  ∃ (dm ed : V → ℕ) (M : SCIM V (fun v ↦ Fin (dm v)) (fun v ↦ Fin (ed v)))
      (_ : M.graph = G) (h : M.graph.IsWellFounded),
    haveI := h
    M.HasICI D X
-- The domains are quantified as `Fin`-indexed families deliberately, and not
-- generalised when `SCM`'s became types on 2026-09-20. That is the class print's
-- Definition 4 admits, and keeping it is what makes this the same statement
-- Theorem 18's row in the coverage audit has been graded against throughout.

/-! ### The two directions, each stated where it is actually true

Neither half of Theorem 18 needs print's hypotheses in full, and they do not need
the same ones. Both are recorded separately so that a user of either does not pay
for the other's.
-/

/-- **Soundness, at its own strength.** Print says *"a single-decision CID"*;
this asks for **nothing at all** — not that the diagram be single-decision, not
that it be evaluable, and not even that `D` be a decision vertex. It holds at
every SCIM over every diagram, and it is what `admitsICI_iff`'s forward direction
is; the hypotheses there are for the converse. -/
public theorem not_admitsICI_of_not_pathThrough {G : CID V} {D X : V}
    (h : ¬ (G.IsDescendant D X ∧ ∃ u, G.IsUtility u ∧ G.IsDescendant X u)) :
    ¬ G.AdmitsICI D X := by
  rintro ⟨dm, ed, M, rfl, hwf, hici⟩
  have := hwf
  exact M.not_hasICI_of_not_pathThrough h hici

/-- **Completeness, at its own strength**, which is wider than print's Lemma 30
on three axes at once.

Print builds its witness inside a *single-decision* CID. What the construction
needs is `DecisionFree`: no decision **other than `D`** on either segment or
among `D`'s observations. So

* the diagram may carry **any number of other decisions**, provided they sit
  clear of the two segments and of `Pa^D`;
* **`D` need not be a decision vertex at all** — nothing here asks it to be, and
  the witness gives it a structural function when it is not;
* the utility node is **named rather than existential**, so a caller who knows
  which utility node closes the path keeps that information.

`DecisionFree`'s own docstring records why neither of its clauses can be dropped:
a decision on a segment can cut the chain with a policy that is still optimal,
and a decision among `Pa^D` can move the context Definition 17 fixes. -/
public theorem admitsICI_of_pathThrough {G : CID V} {D X U : V}
    (hfree : G.DecisionFree D X U) (hU : G.IsUtility U)
    (hDX : G.IsDescendant D X) (hXU : G.IsDescendant X U) :
    G.AdmitsICI D X := by
  have hwf : G.IsWellFounded := G.isWellFounded_of_fintype
  exact ⟨fun _ ↦ 2, fun _ ↦ 1, SCIM.iciWitness G D X U, rfl, hwf,
    SCIM.iciWitness_hasICI (G := G) hfree hU hDX hXU⟩

/-- **Theorem 18 at the weakest hypothesis this development can state it under.**

The criterion is unchanged; what changes is what the diagram must look like for
the converse to hold. Print's `decisions = {D}` is replaced by `DecisionFree` at
the utility node that closes the path, so the equivalence is available on
multi-decision diagrams. `admitsICI_iff` is the corollary at print's own
hypothesis, through `decisionFree_of_singleDecision`.

`[G.IsWellFounded]` is absent from both, and that is not an oversight: at a
finite vertex set it follows from `CID.acyclic` alone, by
`CID.isWellFounded_of_fintype`. -/
public theorem admitsICI_iff_of_decisionFree (G : CID V) {D X : V}
    (hfree : ∀ u, G.IsUtility u → G.IsDescendant X u → G.DecisionFree D X u) :
    G.AdmitsICI D X ↔
      G.IsDescendant D X ∧ ∃ u, G.IsUtility u ∧ G.IsDescendant X u := by
  refine ⟨fun h ↦ ?_, fun ⟨hDX, u, hu, hXu⟩ ↦
    admitsICI_of_pathThrough (hfree u hu hXu) hu hDX hXu⟩
  by_contra hpath
  exact not_admitsICI_of_not_pathThrough hpath h

/-- **Theorem 18** (Instrumental Control Incentive Criterion).

> *A single-decision CID `G` admits an instrumental control incentive on
> `X ∈ 𝐕` if and only if `G` has a directed path from the decision `D` to a
> utility node `U ∈ 𝐔` that passes through `X`, i.e. a directed path
> `D ⇢ X ⇢ 𝐔`.*

The right-hand side is the conjunction of two reachability facts rather than one
path through `X`; `SCIM.PathThrough`'s docstring says why they agree, and print's
own soundness argument uses the conjunctive form. Both closures are **reflexive**,
which is Definition 3's *"of length at least zero"* and is what puts `X = D` and
`X ∈ 𝐔` inside the criterion, as Theorem 18's `X ∈ 𝐕` — against Theorem 16's
`X ∈ 𝐕 \ {D}` — requires. -/
public theorem admitsICI_iff (G : CID V) {D X : V} (hD : G.decisions = {D}) :
    G.AdmitsICI D X ↔
      G.IsDescendant D X ∧ ∃ u, G.IsUtility u ∧ G.IsDescendant X u :=
  admitsICI_iff_of_decisionFree G
    fun u _ _ ↦ decisionFree_of_singleDecision hD X u

end CID


end AISafetyAtlas.Causal
