module

public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Causal.ParameterChart
public import AISafetyAtlas.InformationTheory.PrefixCode
public import Mathlib.Algebra.MvPolynomial.Degrees
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.Computability.TuringMachine.Computable

/-!
# MAIS-O24's polynomial certificate, and the class `𝕄(sk, λ, μ)` it cuts

`prob:effective` asks, for each diagram shape and compatible graph `G`, for a
finite explicit list of **rational polynomials** `Q^G_1, …, Q^G_r` in `(θ, u)`,
with size and construction bounds in `S = K(G) + 2^{|𝐙|}`, cutting out

  `𝕄(sk, λ, μ) := {M ∈ 𝕄(sk, λ) : |Q^G_j(θ, u)| ≥ μ for all j, G being M's own graph}`

on which three conclusions hold. MAIS-O26 is stated over exactly that class, so
the class cannot be formalized without the list, and a stand-in for the list is a
stand-in for the conjecture.

This module supplies the list, the class, the three conclusions, the size and
construction-time bounds, and the bundled `O24Solution` that carries all of them
at once.

**The list is chosen before the utility, and that is a quantifier print fixes.**
*"For each diagram shape `(𝐂, 𝐎, 𝐙)` and each compatible graph `G`, exhibit a
finite explicit list … in `(θ, u)`."* The list answers to the **shape** — the
chance set, the observation set, the utility-parent set — and `u` is a *variable*
of the polynomials, not an input to their construction. An earlier version indexed
the list by a whole `Skeleton`, which carries a numeric utility, so a solution
could have supplied a different list for each utility it was supposed to treat
symbolically. `O24Assignment` is therefore a function of `(𝐎, 𝐙, G)` alone, and
every statement below applies it at `sk.observed` and `sk.utilityParents` rather
than letting `sk` reach it.

**The variables are print's `(θ, u)`.** Print writes the polynomials in
`(θ, u)` and sets `S = K(G) + 2^{|𝐙|}`. Those two counts differ:
`u : {0,1} × dom(𝐙) → [0,1]` has `2·2^{|𝐙|}` values, while `S`'s second summand
counts `2^{|𝐙|}`. That difference is **not** a reason to change coordinates.
`S` is introduced in one clause -- *"require the list length, degrees,
coefficient bit lengths, and construction time to be polynomial in `S`"* -- so it
is a complexity budget, and `poly(S)` cannot see a factor of two. `O24Var` is
therefore `ChartIndex G ⊕ (Bool × UtilityConfig Z)`, with both utility cells per
configuration, and `card_o24Var_le` records that the true count is within a
factor of two of `S`.

**A reading this module carried until 2026-08-21, and why it was wrong.** The
`u`-coordinates were taken to be the **gap** values `g(z) = u(1,z) - u(0,z)`, one
per utility-parent configuration, on the grounds that this is the count `S`
states. That treated `S` as a variable count, which print never says. The gap
reading remains defensible mathematics -- `gap_determines_marginClass` and
`gap_determines_behaviorEq` show the discarded coordinate is invisible to
conclusions (a) and (b) -- but it is strictly more demanding than print, and a
Prop quantified over solutions therefore asserted less. The
alternative — `2·2^{|𝐙|}` raw coordinates — contradicts `S`, and is anyway a
reparametrization of the same problem, since `g` is an affine function of `u`. It
is recorded here because a reader checking fidelity should see the ambiguity
rather than inherit the resolution silently.

**The rest of the setting is evidence for which reading carries the content.**
`Skeleton.gap_determines_marginClass` and `Skeleton.gap_determines_behaviorEq`
prove that two skeletons sharing a shape and a gap have the same margin class and
the same behavioural family: `def:margin`'s (M2), (M3) and (M6) are conditions on
`gap`, (M1) and (M4) are conditions on the model, (M5) reads only the two
variable sets, and `Δmask` takes the gap as its argument. So the second raw
`u`-coordinate is invisible to everything conclusions (a) and (b) are stated
over. That does not *close* the ambiguity — a raw-`u` certificate could still cut
the class using information the conclusions cannot see, and such a list has no
counterpart here — but it does say which of print's two sentences the problem's
own content follows.

**The machine's syntax names its variables; nothing mediates.** The construction
clause needs a code, and every code it uses is a definition — the input code, the
output code, and `encodeO24Var`, which names a coordinate by *what it is*. Until
2026-08-21 `O24Solution` instead carried a supplied bijection
`O24Var Z G ≃ Fin S` and the machine wrote indices. That is an encoding chosen by
the solution, so it is advice: an unrestricted bijection carries `log₂(S!)` bits
of per-instance choice about which coordinate each monomial is about, and a
machine emitting fixed syntax could "construct" a certificate it never computed.
The bundle admitted more solutions than print's problem, and `conj:exact`, which
quantifies over them, would have come out stronger than print.

**One convention is print's own and it fixes a quantifier.** `prob:effective`
closes: *"Fix one list supplied by a solution; every occurrence of
`𝕄(sk,λ,μ)` below refers to that list."* Nothing distinguishes one solution's
list from another's, so a downstream statement about `𝕄(sk,λ,μ)` is a statement
about whichever list was fixed — which is universal quantification over lists,
not existential. That is why the conclusions below are predicates *of* a list.
-/

namespace AISafetyAtlas.Causal

open MeasureTheory MvPolynomial
open AISafetyAtlas.Analysis AISafetyAtlas.InformationTheory

variable {C : Type*} [Fintype C] [DecidableEq C]

/-! ## The coordinates `(θ, u)` -/

/-- `dom(𝐙)`: an assignment of a bit to each declared utility parent. There are
`2^{|𝐙|}` of these, which is print's second summand in `S`.

Indexed by the utility-parent set rather than by a skeleton: `dom(𝐙)` is part of
the *shape*, and nothing about it depends on the numeric utility. -/
public abbrev UtilityConfig (Z : Finset C) := Z → Fin 2

/-- The full assignment a utility configuration names, padding non-parents with
`0`. Which padding is used never matters, by `Skeleton.utility_parents`. -/
@[expose] public def UtilityConfig.extend {Z : Finset C} (z : UtilityConfig Z) :
    Assignment C (binaryDim C) :=
  fun c ↦ if hc : c ∈ Z then z ⟨c, hc⟩ else 0

/-- The variables MAIS-O24's polynomials are in: *"a finite explicit list of
rational polynomials `Q^G_1, …, Q^G_r` in `(θ, u)`"*. The `K(G)` table
coordinates `θ`, and one utility coordinate per **decision and** utility-parent
configuration, because `u : {0,1} × dom(𝐙) → [0,1]` has two cells per
configuration.

**This carried only the gap `g(z) = u(1,z) - u(0,z)` until 2026-08-21**, on the
reading that `S = K(G) + 2^{|𝐙|}` counts the variables and therefore names the
`u`-coordinates. `S` does no such thing: `prob:effective` introduces it only as a
budget — *"require the list length, degrees, coefficient bit lengths, and
construction time to be polynomial in `S`"* — and `poly(S)` is insensitive to the
factor of two. There is one printed variable set and this is it. Restricting to
gap polynomials admitted strictly fewer solutions than print, which made
`conj:exact`, a universal quantifier over solutions, assert less than print's. -/
public abbrev O24Var (Z : Finset C) (G : C → Finset C) :=
  ChartIndex G ⊕ (Bool × UtilityConfig Z)

/-- **`prob:effective`'s "compatible graph"**: one a model can carry, which is
exactly acyclicity — the condition `Model.acyclic` states.

Print asks for a list *"for each diagram shape and each **compatible** graph
`G`"*, so a bare `C → Finset C` is too many graphs: it includes cyclic ones, for
which no model exists and `𝕄(sk, λ, μ)` is empty. Requiring a certificate at
those would strengthen the problem past print. -/
@[expose] public def IsCompatibleGraph (G : C → Finset C) : Prop :=
  ∃ rank : C → ℕ, ∀ c, ∀ p ∈ G c, rank p < rank c

/-- Every model's graph is compatible; this is its acyclicity field. -/
public theorem isCompatibleGraph_parents (M : Model C (binaryDim C) ℝ) :
    IsCompatibleGraph M.parents :=
  M.acyclic

/-- `S = K(G) + 2^{|𝐙|}`, as `prob:effective` writes it. `chartDim` is `K(G)`,
proved equal to the printed `Σᵢ 2^{|Pa_G(Cᵢ)|}` by `card_chartIndex`. -/
@[expose] public noncomputable def o24Size (Z : Finset C) (G : C → Finset C) : ℕ :=
  chartDim G + 2 ^ Z.card

/-- **`S` is a budget, not a variable count.** `prob:effective` defines
`S = K(G) + 2^{|𝐙|}` and requires the list length, degrees, coefficient bit
lengths and construction time to be polynomial in it. The `(θ, u)` variables
number `K(G) + 2·2^{|𝐙|}`, which is `S` up to the factor of two that `poly(S)`
cannot see.

An earlier version of this file asserted `Fintype.card (O24Var Z G) = S` and
took that as fixing the `u`-coordinates to be gaps. The equality was true of the
gap reading and is what made it look forced; it is not something print states,
and `S` is a budget in the sentence that introduces it. -/
public theorem card_o24Var (Z : Finset C) (G : C → Finset C) :
    Fintype.card (O24Var Z G) = chartDim G + 2 * 2 ^ Z.card := by
  classical
  rw [Fintype.card_sum, card_chartIndex]
  simp [UtilityConfig, Fintype.card_prod]

/-- The variable count is within a factor of two of `S`, which is all a
`poly(S)` requirement can distinguish. -/
public theorem card_o24Var_le (Z : Finset C) (G : C → Finset C) :
    Fintype.card (O24Var Z G) ≤ 2 * o24Size Z G := by
  rw [card_o24Var, o24Size]
  omega

/-- The point `(θ, u)` a model presents to the polynomials, at a named graph:
its chart coordinates, and the skeleton's **utility** at each decision and each
utility-parent configuration — print's `u`, not its gap. -/
@[expose] public noncomputable def o24Point (sk : Skeleton C (binaryDim C) Bool ℝ)
    (M : Model C (binaryDim C) ℝ) (G : C → Finset C) :
    O24Var sk.utilityParents G → ℝ :=
  Sum.elim (M.chartOn G) fun dz ↦ sk.utility dz.1 dz.2.extend

/-! ## The list, and the class it cuts -/

/-- The lists a candidate answer supplies at one diagram shape: one per
compatible graph.

`List` rather than `Finset` because print says *"a finite explicit **list**
`Q^G_1, …, Q^G_r`"* and bounds its **length** `r`; repetitions are permitted and
counted, which a `Finset` would silently discard. -/
public abbrev O24List (Z : Finset C) :=
  (G : C → Finset C) → List (MvPolynomial (O24Var Z G) ℚ)

/-- **A candidate answer to `prob:effective`**, at one chance-variable set: a list
for each diagram shape `(𝐎, 𝐙)` and each graph.

The shape is all a solution may read. The utility is a variable of the
polynomials it produces, never an input to the choice of which polynomials to
produce. -/
public abbrev O24Assignment (C : Type*) [Fintype C] [DecidableEq C] :=
  (O Z : Finset C) → O24List Z

/-- The list a solution supplies at a given skeleton: read off the skeleton's
shape, and at nothing else. -/
@[expose] public def O24Assignment.at (Q : O24Assignment C)
    (sk : Skeleton C (binaryDim C) Bool ℝ) : O24List sk.utilityParents :=
  Q sk.observed sk.utilityParents

/-- One polynomial's value at a model, over `ℝ`. The polynomial is rational and
the model's tables are real, so this is `aeval` along `ℚ → ℝ` rather than a
same-field evaluation. -/
@[expose] public noncomputable def o24Value (sk : Skeleton C (binaryDim C) Bool ℝ)
    (M : Model C (binaryDim C) ℝ) {G : C → Finset C}
    (q : MvPolynomial (O24Var sk.utilityParents G) ℚ) : ℝ :=
  aeval (o24Point sk M G) q

/-- **`𝕄(sk, λ, μ)`**, exactly as `prob:effective` displays it: the margin class
cut down by the supplied list, each polynomial evaluated at the model's **own**
graph. -/
@[expose] public noncomputable def effectiveMarginClass
    (sk : Skeleton C (binaryDim C) Bool ℝ) (lam mu : ℝ) (Q : O24Assignment C) :
    Set (Model C (binaryDim C) ℝ) :=
  {M | sk.MarginClass M lam ∧ ∀ q ∈ Q.at sk M.parents, mu ≤ |o24Value sk M q|}

/-- The cut is a subclass of the margin class, which is the containment
`prob:effective` writes into the display. -/
public theorem effectiveMarginClass_subset (sk : Skeleton C (binaryDim C) Bool ℝ)
    (lam mu : ℝ) (Q : O24Assignment C) :
    effectiveMarginClass sk lam mu Q ⊆ {M | sk.MarginClass M lam} :=
  fun _ hM ↦ hM.1

/-- Raising the margin shrinks the class: `μ ≤ ν` gives
`𝕄(sk,λ,ν) ⊆ 𝕄(sk,λ,μ)`. -/
public theorem effectiveMarginClass_mono (sk : Skeleton C (binaryDim C) Bool ℝ)
    (lam : ℝ) {mu nu : ℝ} (h : mu ≤ nu) (Q : O24Assignment C) :
    effectiveMarginClass sk lam nu Q ⊆ effectiveMarginClass sk lam mu Q :=
  fun _ hM ↦ ⟨hM.1, fun q hq ↦ le_trans h (hM.2 q hq)⟩

/-! ## The size bounds

Print: *"require the list length, degrees, coefficient bit lengths, and
construction time to be polynomial in `S` (using sparse monomial encoding)"*.
Three of the four are structural and are here; construction time is a claim about
a machine and is `O24Constructor` below. -/

/-- The bit length of a rational, as a coefficient size. Both the numerator and
the denominator are counted, since a sparse encoding must write both. The `+1`s
keep the measure defined and positive at `0` and at `±1`. -/
@[expose] public def ratBitLength (r : ℚ) : ℕ :=
  Nat.log 2 (r.num.natAbs + 1) + Nat.log 2 (r.den + 1)

/-- The size of one polynomial under print's **sparse monomial encoding**: the
number of monomials actually carried, the total degree, and the coefficient bit
lengths. A dense encoding would instead charge `(deg+1)^S` coefficients, which
is what "sparse" excludes. -/
@[expose] public noncomputable def polySize {σ : Type*} [DecidableEq σ]
    (q : MvPolynomial σ ℚ) : ℕ :=
  q.support.card + q.totalDegree + ∑ m ∈ q.support, ratBitLength (q.coeff m)

/-- **The structural size bounds of `prob:effective`.**

Print names three quantities and asks each to be polynomial in `S`; one
polynomial bounding all of them is the same requirement, since a maximum of
finitely many polynomials is dominated by one. Stating it with a single `p`
chosen before the shape and the graph is what makes "polynomial in `S`" a bound
rather than a per-instance accident. -/
@[expose] public noncomputable def HasPolySizeAt (p : Polynomial ℕ)
    (Q : O24Assignment C) : Prop :=
  ∀ (O Z : Finset C) (G : C → Finset C), IsCompatibleGraph G →
    (Q O Z G).length ≤ p.eval (o24Size Z G) ∧
      ∀ q ∈ Q O Z G, polySize q ≤ p.eval (o24Size Z G)

/-- The size bounds hold at *some* polynomial, on one chance-variable set.

`O24Solution` does **not** use this form. Print separates two kinds of
quantity in one sentence: `a` and `b` are *"constants depending only on
`(m, S)`"*, while the list length, degrees, coefficient bit lengths and
construction time are *"polynomial in `S`"* with no `m` named. So the size
polynomial is chosen once, before the diagram size, and the bundle hoists it —
this form exists for stating the bound at a fixed `C`. -/
@[expose] public noncomputable def HasPolySizeList (Q : O24Assignment C) : Prop :=
  ∃ p : Polynomial ℕ, HasPolySizeAt p Q

/-! ## The constants, and the three conclusions

Print: *"Find constants `a, b > 0` depending only on `(m, S)` such that for all
`λ, μ ∈ (0, ½)`, on the subclass `𝕄(sk,λ,μ)`: (a) … (b) … (c)"*.

Two things in that sentence are structural and are carried by `O24Constants`
rather than by the conclusions. The constants are **positive** — without that,
`b = 0` kills the decay in `μ` that (c) is about, and (c) becomes a bound with no
content. And they depend **only on `(m, S)`**, so they are functions of exactly
those two numbers, fixed before `λ`, `μ`, and the model; existential
quantification inside a conclusion would let them depend on all three.

They are **real**, not natural. Print writes `a, b > 0` and uses them as
exponents; reading them as integers is a restriction that would need a rounding
argument to justify, so the exponentiation here is `Real.rpow`.

Conclusion (b)'s threshold is **not** carried the same way, and reading print's
quantifier order is what settles where it goes. `a` and `b` are scoped
*"depending only on `(m, S)`"*. The threshold is not mentioned there at all — it
is named inside `(b)`, which sits inside *"for all `λ, μ ∈ (0, ½)`"*, itself
inside the per-shape *"for each diagram shape and each compatible graph"*. So
print lets it vary with the shape and with both margins, and restricts only `a`
and `b` to `(m, S)`.

It therefore does not live on `O24Constants`. `O24Threshold` carries it, indexed
by the skeleton and applied at `λ` and `μ`, and `O24Solution.thresholds` supplies
one family per chance-variable count, exactly as `lists` does.

This is the second sign this clause has been graded under, and both earlier ones
were wrong. It was first called a **widening**, on the ground that a structure
field quantified existentially is only *"there exists a threshold"* while print
says *explicit*. That does not survive comparison with `a` and `b`, which have
the identical shape — a function of `(m, S)` into the reals with a positivity
proof, no formula, no computability — and are graded `Same`. In this genre
*explicit* means *exhibited as part of the answer*, which a field is; demanding a
computable real is an obligation print does not state, as the paragraph below
already conceded. The same note said a solution might supply an *"uncomputably
small"* threshold; computability and magnitude are independent, and neither was
what bit.

It was then called a **narrowing**, which was right: read at `(m, S)`, the
threshold varied with `λ` only through the integer `S` and with `μ` not at all,
so one threshold had to serve every margin pair — including as `μ` tends to `0`
and the cut subclass shrinks around it. That demanded more of a solution than
print does, so the predicate admitted fewer constructions and a downstream
*"for every solution…"* came out weaker than print's.

What it is **not** is an `∃ δ₀` inside conclusion (b). That would put the
threshold at print's quantifier position and lose what *explicit* asks for: the
threshold belongs to the exhibited answer, not to a proof that consumes it.
Keeping it a supplied field and giving it print's own arguments is the only
rendering that satisfies both halves of the printed sentence. -/

/-- `prob:effective`'s constants `a, b > 0`, which print scopes to `(m, S)`.
Conclusion (b)'s threshold is **not** here: print does not scope it this way, so
it lives on `O24Threshold`. -/
public structure O24Constants where
  /-- The exponent in conclusions (b) and (c). -/
  a : ℕ → ℕ → ℝ
  /-- The exponent on `μ` in conclusion (c). -/
  b : ℕ → ℕ → ℝ
  /-- Print writes `a > 0`. -/
  a_pos : ∀ m S, 0 < a m S
  /-- Print writes `b > 0`; at `b = 0` conclusion (c) says nothing about `μ`. -/
  b_pos : ∀ m S, 0 < b m S

/-- Conclusion (b)'s threshold, at print's own quantifier: a positive bound that
may depend on the skeleton and on both margins.

`prob:effective` restricts `a` and `b` to `(m, S)` and restricts this to
nothing, so it is carried separately from `O24Constants` rather than as two more
arguments to it. It is a **supplied** datum — that is what *"an explicit
threshold"* asks for — and not an `∃` a proof of (b) may produce. -/
public structure O24Threshold (C : Type*) [Fintype C] [DecidableEq C] where
  /-- The threshold on `δ`, per skeleton and per margin pair. -/
  bound : Skeleton C (binaryDim C) Bool ℝ → ℝ → ℝ → ℝ
  /-- A threshold of `0` would make conclusion (b) vacuous. -/
  bound_pos : ∀ sk lam mu, 0 < bound sk lam mu

/-- **(a)** *"`𝚫_M = 𝚫_{M'}` implies `M = M'`"*, on the cut subclass. -/
@[expose] public noncomputable def O24Identifies
    (sk : Skeleton C (binaryDim C) Bool ℝ) (Q : O24Assignment C) : Prop :=
  ∀ lam mu : ℝ, Skeleton.ValidMargin lam → Skeleton.ValidMargin mu →
    ∀ M ∈ effectiveMarginClass sk lam mu Q,
      ∀ M' ∈ effectiveMarginClass sk lam mu Q,
        sk.BehaviorEq M M' → M = M'

/-- The class-level size `S = K(sk,λ) + 2^{|𝐙|}`, built on `def:margin`'s class
maximum `K` rather than on one graph's `K(G)`.

Conclusion (b) ranges over models of the whole subclass, which may carry
different graphs, so `S` cannot be read at a graph that the statement does not
name. An earlier version quantified a free `G` and used it only inside the
exponent — the same defect as a free `K`, where a printed symbol reaches the
statement only through the conclusion. -/
@[expose] public noncomputable def o24ClassSize (Z : Finset C) (K : ℕ) : ℕ :=
  K + 2 ^ Z.card

/-- **(b)** *"quantitatively, `M' ∈ I_δ(M)` implies `e(M; M') ≤ (K/λμ)^a δ` for
all `δ` below an explicit threshold"*.

`K` is `def:margin`'s class maximum, pinned by `IsGreatest` rather than free.
`I_δ(M)` is `InIdentifiedSet`, which is print's own set: it places both models in
`𝕄(sk, λ)` and asks them to share an admissible family. Note that `M'` is
therefore **not** required to lie in the cut subclass — print's `I_δ(M)` is taken
in the margin class, and requiring more of `M'` would weaken the conclusion.

The threshold is supplied rather than produced by an `∃` inside the conclusion,
which is what *explicit* asks for, and it is read at `(sk, λ, μ)`, which is where
print's quantifier order puts it. -/
@[expose] public noncomputable def O24RecoveryModulus [Nonempty C]
    (sk : Skeleton C (binaryDim C) Bool ℝ) (Q : O24Assignment C)
    (const : O24Constants) (thr : O24Threshold C) : Prop :=
  ∀ lam mu : ℝ, Skeleton.ValidMargin lam → Skeleton.ValidMargin mu →
    ∀ K : ℕ,
      IsGreatest {k | ∃ M : Model C (binaryDim C) ℝ,
        sk.MarginClass M lam ∧ k = chartDim M.parents} K →
      ∀ δ : ℝ, 0 ≤ δ →
        δ < thr.bound sk lam mu →
          ∀ M ∈ effectiveMarginClass sk lam mu Q,
            ∀ M' : Model C (binaryDim C) ℝ,
              InIdentifiedSet sk lam δ M M' →
                modelError M M' ≤
                  ((K : ℝ) / (lam * mu)) ^
                    (const.a (Fintype.card C)
                      (o24ClassSize sk.utilityParents K)) * δ

/-! ## Conclusion (c), and the domains it integrates over

Print: *"the excluded set is small: for each fixed graph `G` and
Lebesgue-almost-every `u`, `Leb{θ : |Q^G_j(θ,u)| < μ for some j} ≤ S^a μ^b"*.

Both domains are bounded in print and neither bound is decorative.

`θ` ranges over table entries, which are probabilities. Measuring the excluded
set in all of `ℝ^{K(G)}` would let a set of **infinite** measure satisfy the
bound after a `toReal`, and is not the printed domain either.

`u` ranges over `{0,1} × dom(𝐙) → [0,1]` — `def:cid` says so — which is
`utilityBox` exactly. Taking *"Lebesgue-almost-every `u`"* over all of
`ℝ^{2·2^{|𝐙|}}` instead is **stronger** than print, and the direction is worth
being exact about because it is easy to get backwards. `utilityBox` has positive
measure, so a null subset of the ambient space meets it in a set null for the
box: almost-everywhere on the ambient space *implies* almost-everywhere on the
box, not the other way round. The unbounded form therefore demands the estimate
at utilities no skeleton realizes, admits **fewer** solutions than print's
problem, and would make every downstream *"for every O24 solution, …"* weaker
than print. -/

/-- The chart points a model can actually present: every table entry is a
probability, so the coordinates lie in `[0,1]`. -/
@[expose] public noncomputable def chartBox (G : C → Finset C) :
    Set (ChartIndex G → ℝ) :=
  ClosedBox (fun _ ↦ 0) 1

/-- Every model's chart point lies in the box, so restricting (c) to it discards
no parameter that any model realizes. -/
public theorem chartOn_mem_chartBox (M : Model C (binaryDim C) ℝ)
    (G : C → Finset C) : M.chartOn G ∈ chartBox G := by
  intro i
  obtain ⟨h0, h1⟩ := M.chartOn_mem_unitInterval G i
  exact ⟨h0, by simpa using h1⟩

/-- The gap coordinates a skeleton can present: `g(z) = u(1,z) - u(0,z)` with
`u` valued in `[0,1]`, so `g` lies in `[-1,1]`. -/
@[expose] public noncomputable def utilityBox (Z : Finset C) :
    Set (Bool × UtilityConfig Z → ℝ) :=
  ClosedBox (fun _ ↦ 0) 1

/-- Every skeleton's utility vector lies in the box, so restricting (c)'s
almost-every quantifier to it discards no utility any skeleton realizes. -/
public theorem utility_mem_utilityBox (sk : Skeleton C (binaryDim C) Bool ℝ) :
    (fun dz : Bool × UtilityConfig sk.utilityParents ↦ sk.utility dz.1 dz.2.extend) ∈
      utilityBox sk.utilityParents := by
  intro dz
  have h := sk.utility_mem_unitInterval dz.1 (UtilityConfig.extend dz.2)
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- The `θ`-slice at which some supplied polynomial is smaller than `μ`, at a
fixed graph and a fixed utility, inside the box of realizable table entries.
This is the set `prob:effective`(c) measures. -/
@[expose] public noncomputable def o24ExcludedSlice (Q : O24Assignment C)
    (O Z : Finset C) (G : C → Finset C) (u : Bool × UtilityConfig Z → ℝ) (mu : ℝ) :
    Set (ChartIndex G → ℝ) :=
  {θ ∈ chartBox G | ∃ q ∈ Q O Z G, |aeval (Sum.elim θ u) q| < mu}

/-- **(c)** *"the excluded set is small: for each fixed graph `G` and
Lebesgue-almost-every `u`, `Leb{θ : |Q^G_j(θ,u)| < μ for some j} ≤ S^a μ^b"*.

The comparison is in `ℝ≥0∞` and **not** through `ENNReal.toReal`. That is not a
stylistic choice: `toReal ⊤ = 0`, so a `toReal` comparison is satisfied by an
excluded set of infinite measure — the certificate consisting of the zero
polynomial would pass, with every `θ` excluded and the class empty.

The almost-every quantifier is restricted to `utilityBox`, which is print's own
utility domain; see the section note for why the unbounded form is **stronger**
rather than weaker. -/
@[expose] public noncomputable def O24ExcludedSetSmall (Q : O24Assignment C)
    (const : O24Constants) : Prop :=
  ∀ (O Z : Finset C) (G : C → Finset C), IsCompatibleGraph G →
    ∀ mu : ℝ, Skeleton.ValidMargin mu →
      ∀ᵐ u : Bool × UtilityConfig Z → ℝ,
        u ∈ utilityBox Z →
          volume (o24ExcludedSlice Q O Z G u mu) ≤
            ENNReal.ofReal
              ((o24Size Z G : ℝ) ^ (const.a (Fintype.card C) (o24Size Z G)) *
                mu ^ (const.b (Fintype.card C) (o24Size Z G)))

/-! ## Construction time

Print: *"require the list length, degrees, coefficient bit lengths, and
**construction time** to be polynomial in `S` (using sparse monomial
encoding)"*.

This is the one clause that is a statement about a machine, and it is the reason
`O24Solution` was not assembled until now: a bundle missing a clause admits a
*superset* of genuine solutions, so every downstream *"for every O24 solution,
…"* would be **stronger** than print.

Three design points, each of which a weaker rendering would get wrong.

**One machine and one polynomial, quantified outside the input.** Print asks for
a construction, and a construction that may vary with the diagram is a table of
answers rather than an algorithm. So the machine and the time bound are
fields, and the fields that quantify the input sit under them.

**The input and output codes are fixed, not existential.** A predicate reading
*"there exist a machine and encodings such that …"* is met by advice: pick an
encoding that already carries the answer and let the machine copy its input.
`AISafetyAtlas.InformationTheory.PrefixCode` supplies both codes as definitions, and both
are proved prefix-free, so *"the machine outputs this"* is a statement about what
it constructed.

**The output is required to decode correctly, not to match one serialization.**
The sparse form of a polynomial is a set of monomials; fixing a serialization
would also fix an arbitrary order over that set and demand the machine reproduce
it. Print makes no such demand. The order of `Q₁, …, Q_r` is not free — print
numbers those — so the decoded *list* must match. -/

/-- A diagram shape together with a graph: everything a solution's construction
may read. `𝐂 = {C₁, …, C_m}` is `Fin m`, which is print's own indexing of the
chance variables and is what lets the input be serialized at all.

Compatibility of the graph is a hypothesis on the statement rather than a field,
so that the input is pure data and its code is a code on data. -/
public structure O24Input (m : ℕ) where
  /-- `𝐎`, the observation set. -/
  observed : Finset (Fin m)
  /-- `𝐙`, the utility-parent set. -/
  utilityParents : Finset (Fin m)
  /-- The compatible graph the list is asked for. -/
  graph : Fin m → Finset (Fin m)

/-- `S` at an input. -/
@[expose] public noncomputable def O24Input.size {m : ℕ} (i : O24Input m) : ℕ :=
  o24Size i.utilityParents i.graph

/-- A subset of `Fin m` as its indicator string, terminated by the separator. -/
@[expose] public def encodeFinsetFin {m : ℕ} (s : Finset (Fin m)) : List CodeSym :=
  encodeBoolList (List.ofFn fun i : Fin m ↦ decide (i ∈ s))

public theorem isPrefixCode_encodeFinsetFin {m : ℕ} :
    IsPrefixCode (encodeFinsetFin (m := m)) := by
  refine IsPrefixCode.ofBoolList ?_
  intro a b h
  have hfun := List.ofFn_injective h
  ext i
  simpa using congrFun hfun i

/-! ### Naming a variable

`prob:effective`'s polynomials are written in the `S` variables `(θ, u)`, and the
machine has to name them. It names them **by what they are** — a table
coordinate is a chance variable together with a parent configuration, a utility
coordinate is a configuration of `𝐙` — and the code below is a definition, like
the input and output codes.

The alternative, syntax over `Fin S` together with a supplied bijection
`O24Var Z G ≃ Fin S`, is not equivalent and is not neutral. An unrestricted
bijection carries `log₂(S!)` bits of per-instance choice about *which*
coordinate each monomial is about, is not required to be computable, and is
chosen by the solution rather than fixed by the problem. A machine could emit
fixed syntax and let the bijection decide what it means, "constructing" a
certificate it never computed. That widens the solution class, and every
downstream *"for every O24 solution, …"* — which is what `conj:exact` is — comes
out **stronger** than print.

`card_le_o24Size` is what keeps names short enough for the clause to be
meaningful: a name is `O(m)` symbols and `m ≤ S`, so `poly(S)` monomials still
have a `poly(S)` transcript. -/

omit [DecidableEq C] in
/-- Every chance variable owns at least one table coordinate, so `m ≤ S`. -/
public theorem card_le_o24Size (Z : Finset C) (G : C → Finset C) :
    Fintype.card C ≤ o24Size Z G := by
  have h : ∑ _c : C, 1 ≤ ∑ c : C, 2 ^ (G c).card :=
    Finset.sum_le_sum fun c _ ↦ Nat.one_le_two_pow
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] at h
  exact le_trans h (Nat.le_add_right _ _)

/-- A bit assignment to the elements of a subset of `Fin m`, as an `m`-bit
string: the assigned bit inside the subset and `false` outside it. -/
@[expose] public def finsetFunBits {m : ℕ} (s : Finset (Fin m)) (v : s → Fin 2) :
    List Bool :=
  List.ofFn fun i : Fin m ↦ if h : i ∈ s then decide (v ⟨i, h⟩ = 1) else false

public theorem finsetFunBits_injective {m : ℕ} (s : Finset (Fin m)) :
    Function.Injective (finsetFunBits s) := by
  have hbin : ∀ a : Fin 2, a = 0 ∨ a = 1 := by decide
  intro v w h
  have hfun := List.ofFn_injective h
  funext c
  have hc := congrFun hfun c.1
  simp only [c.2, dif_pos, Subtype.coe_eta, decide_eq_decide] at hc
  rcases hbin (v c) with hv | hv <;> rcases hbin (w c) with hw | hw <;>
    simp_all

/-- **The canonical variable name code.** A table coordinate `θ` is named by its
chance variable and that variable's parent configuration; a utility coordinate
`u` is named by its configuration of `𝐙`. The leading symbol says which kind. -/
@[expose] public def encodeO24Var {m : ℕ} (Z : Finset (Fin m))
    (G : Fin m → Finset (Fin m)) : O24Var Z G → List CodeSym
  | .inl i => CodeSym.zero :: (encodeNat i.1.val ++ encodeBoolList (finsetFunBits (G i.1) i.2))
  | .inr v => CodeSym.one :: encodeBoolList (v.1 :: finsetFunBits Z v.2)

public theorem isPrefixCode_encodeO24Var {m : ℕ} (Z : Finset (Fin m))
    (G : Fin m → Finset (Fin m)) : IsPrefixCode (encodeO24Var Z G) := by
  rintro (⟨c₁, v₁⟩ | v₁) (⟨c₂, v₂⟩ | v₂) x y h <;>
    simp only [encodeO24Var, List.cons_append, List.append_assoc] at h
  · obtain ⟨-, h⟩ := List.cons_eq_cons.mp h
    obtain ⟨hc, h⟩ := isPrefixCode_encodeNat _ _ _ _ h
    have hc' : c₁ = c₂ := Fin.ext hc
    subst hc'
    obtain ⟨hv, hxy⟩ := isPrefixCode_encodeBoolList _ _ _ _ h
    exact ⟨by rw [finsetFunBits_injective _ hv], hxy⟩
  · simp at h
  · simp at h
  · obtain ⟨-, h⟩ := List.cons_eq_cons.mp h
    obtain ⟨hv, hxy⟩ := isPrefixCode_encodeBoolList _ _ _ _ h
    obtain ⟨hd, hbits⟩ := List.cons_eq_cons.mp hv
    refine ⟨congrArg Sum.inr (Prod.ext hd (finsetFunBits_injective _ hbits)), hxy⟩

/-- **The canonical input code**: the diagram size, the two subsets, and the
adjacency lists, each self-delimiting. -/
@[expose] public def o24EncodeInput {m : ℕ} (i : O24Input m) : List CodeSym :=
  encodeNat m ++ encodeFinsetFin i.observed ++ encodeFinsetFin i.utilityParents ++
    encodeList encodeFinsetFin (List.ofFn i.graph)

/-- The input code is injective. Without this the construction clause would be
contradictory rather than demanding: one machine run cannot produce the outputs
of two different inputs. -/
public theorem o24EncodeInput_injective {m : ℕ} :
    Function.Injective (o24EncodeInput (m := m)) := by
  intro a b h
  simp only [o24EncodeInput, List.append_assoc] at h
  obtain ⟨-, h₁⟩ := isPrefixCode_encodeNat _ _ _ _ h
  obtain ⟨hobs, h₂⟩ := isPrefixCode_encodeFinsetFin _ _ _ _ h₁
  obtain ⟨hz, h₃⟩ := isPrefixCode_encodeFinsetFin _ _ _ _ h₂
  obtain ⟨hg, -⟩ := isPrefixCode_encodeFinsetFin.list _ _ [] [] (by simpa using h₃)
  have hgraph : a.graph = b.graph := List.ofFn_injective hg
  cases a; cases b
  simp_all

/-- **The construction-time clause of `prob:effective`.**

One machine, one polynomial, both fixed before any diagram; on each compatible
input it writes, within `time(S)` steps, some sparse syntax that decodes to
exactly the list `Q` supplies there. -/
public structure O24Constructor
    (lists : ∀ m : ℕ, O24Assignment (Fin m)) where
  /-- The machine, with its alphabets named as the code's. **One** machine: `m`
  is quantified in the obligation fields below, not in front of this one. A
  machine per diagram size is a family of algorithms rather than an algorithm,
  and `o24EncodeInput` writes `m` first precisely so that one machine can read
  it off its own input. -/
  aux : Turing.TM2ComputableAux CodeSym CodeSym
  /-- The construction-time bound, in `S`. One polynomial, for the same reason. -/
  time : Polynomial ℕ
  /-- The syntax the machine writes at each input. Its monomials name the
  variables `(θ, u)` themselves, so no numbering mediates between what the
  machine writes and which polynomial it wrote. -/
  output : ∀ (m : ℕ) (i : O24Input m),
    List (SparsePoly (O24Var i.utilityParents i.graph))
  /-- It decodes to exactly the list `lists` supplies there. The *list* order is
  pinned, since print numbers `Q₁, …, Q_r`; the order of monomials inside each
  polynomial is not, and print does not fix one. -/
  output_decodes : ∀ (m : ℕ) (i : O24Input m), IsCompatibleGraph i.graph →
    (output m i).map ofSparsePoly = lists m i.observed i.utilityParents i.graph
  /-- And the machine writes it within `time(S)` steps.

  `Turing.TM2OutputsInTime` is `Type`-valued rather than a `Prop`, since it
  carries the halting run; that is why this field is data, exactly as
  `Turing.TM2ComputableInPolyTime.outputsFun` is. -/
  outputs_in_time : ∀ (m : ℕ) (i : O24Input m), IsCompatibleGraph i.graph →
    Turing.TM2OutputsInTime aux.tm
      (List.map aux.inputAlphabet.invFun (o24EncodeInput i))
      (some (List.map aux.outputAlphabet.invFun
        (encodeSparseList (encodeO24Var i.utilityParents i.graph) (output m i))))
      (time.eval i.size)

/-! ## The bundled solution

`prob:effective` is a **construction problem**: *"exhibit a finite explicit list
… Find constants `a, b > 0` …"*. No `Prop` is the same statement as a
construction problem, so what is offered is the predicate *"this is a solution"*,
and downstream statements quantify over solutions.

Every printed clause is a field. That is the point of the bundle: a predicate
missing one admits a superset of genuine solutions, and `conj:exact`, which reads
*"For `𝒩 = 𝕄(sk, λ, μ)`"*, would then be a statement about more classes than
print's — stronger, not weaker.

`m` is quantified **inside** every field, so the machine, the polynomial and the
constants are uniform across diagram sizes. A solution that supplied a different
machine per `m` would be a family of algorithms rather than an algorithm. -/

/-- **A solution to MAIS-O24.** -/
public structure O24Solution where
  /-- The lists, one family per chance-variable count, each reading only the
  diagram shape and the graph. -/
  lists : ∀ m : ℕ, O24Assignment (Fin m)
  /-- Print's `a, b > 0`, scoped to `(m, S)` as print scopes them. -/
  constants : O24Constants
  /-- Conclusion (b)'s thresholds, one family per chance-variable count, each
  reading the skeleton and both margins — the scope print's quantifier order
  gives them, and the reason they are not fields of `constants`. -/
  thresholds : ∀ m : ℕ, O24Threshold (Fin m)
  /-- The one polynomial bounding list length, degrees and coefficient bit
  lengths. Chosen before the diagram size: print qualifies `a` and `b` as
  *"depending only on `(m, S)`"* and leaves the size quantities as *"polynomial
  in `S`"*, and that contrast is the whole difference between a bound and a
  table of bounds. -/
  sizePoly : Polynomial ℕ
  /-- List length, degrees and coefficient bit lengths are polynomial in `S`. -/
  sizes : ∀ m : ℕ, HasPolySizeAt sizePoly (lists m)
  /-- Construction time is polynomial in `S`, for one machine and one polynomial
  across all diagram sizes. -/
  construction : O24Constructor lists
  /-- Conclusion (a). -/
  identifies : ∀ (m : ℕ) (sk : Skeleton (Fin m) (binaryDim (Fin m)) Bool ℝ),
    O24Identifies sk (lists m)
  /-- Conclusion (b). -/
  recovery : ∀ (m : ℕ) (_ : Nonempty (Fin m))
    (sk : Skeleton (Fin m) (binaryDim (Fin m)) Bool ℝ),
    O24RecoveryModulus sk (lists m) constants (thresholds m)
  /-- Conclusion (c). -/
  excluded : ∀ m : ℕ, O24ExcludedSetSmall (lists m) constants

/-- The class `𝕄(sk, λ, μ)` a solution cuts, which is the object `conj:exact`
is stated over. -/
@[expose] public noncomputable def O24Solution.marginClass {m : ℕ} (sol : O24Solution)
    (sk : Skeleton (Fin m) (binaryDim (Fin m)) Bool ℝ) (lam mu : ℝ) :
    Set (Model (Fin m) (binaryDim (Fin m)) ℝ) :=
  effectiveMarginClass sk lam mu (sol.lists m)

/-- A solution's class is a subclass of the margin class, which is the
containment `prob:effective` writes into its display. -/
public theorem O24Solution.marginClass_subset {m : ℕ} (sol : O24Solution)
    (sk : Skeleton (Fin m) (binaryDim (Fin m)) Bool ℝ) (lam mu : ℝ) :
    sol.marginClass sk lam mu ⊆ {M | sk.MarginClass M lam} :=
  effectiveMarginClass_subset sk lam mu _

/-- Behaviour identifies a model inside a solution's class — conclusion (a),
read off the bundle. This is the form `conj:exact` and `prob:exact` use. -/
public theorem O24Solution.behaviorEq_imp_eq {m : ℕ} (sol : O24Solution)
    (sk : Skeleton (Fin m) (binaryDim (Fin m)) Bool ℝ) {lam mu : ℝ}
    (hlam : Skeleton.ValidMargin lam) (hmu : Skeleton.ValidMargin mu)
    {M M' : Model (Fin m) (binaryDim (Fin m)) ℝ}
    (hM : M ∈ sol.marginClass sk lam mu) (hM' : M' ∈ sol.marginClass sk lam mu)
    (hbeh : sk.BehaviorEq M M') : M = M' :=
  sol.identifies m sk lam mu hlam hmu M hM M' hM' hbeh

end AISafetyAtlas.Causal
