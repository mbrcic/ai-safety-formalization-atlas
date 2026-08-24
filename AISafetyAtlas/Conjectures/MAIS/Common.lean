module

public import AISafetyAtlas.Conjectures.BinaryPair
public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Causal.EffectiveGenericity
public import AISafetyAtlas.Causal.ParameterChart
public import AISafetyAtlas.Causal.Query
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic

/-!
# Shared vocabulary for the MAIS-A2 statements

Definitions used by more than one printed problem. Nothing here is a
statement of a problem; each problem lives in its own module beside this one.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Defining a proposition asserts nothing about its truth; resolutions live in
`AISafetyAtlas/Examples/Conjectures/`.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.BinaryPair

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}


/-! ## Negative answers already witnessed in the atlas -/

/-- The source's binary-variable restriction on a categorical dimension map.

**This is not an atlas restriction and it is barely used.** `def:cid` declares
the chance variables and the decision `D` binary, so `binaryDim` and `Bool`
match print rather than narrowing it, and every live statement writes `binaryDim`
into the type instead of carrying this predicate as a hypothesis. What survives
here is the hypothesis of the withdrawn MAIS-O27 encoding, kept as a record
rather than maintained.

`def:cid`'s policy is the induced conditional `π : dom(𝐎) → [0,1]` with the
unmediated-task assumption built into the definition, so the atlas decision layer
is A2's object rather than a projection of it. Tables, utilities and mixture
weights are real, as in `def:margin`. -/
public def IsBinaryDimension (dim : C → ℕ) : Prop :=
  ∀ c, dim c = 2

/-! ## Explicit assumptions on the class -/

/-- **`prob:effective`(b)'s linear recovery modulus**, as `prob:exact` reuses it:
*"satisfying conclusions (a)–(b) of Problem 24 with modulus `ω(δ) = Lδ`"*.

`M'` ranges over `I_δ(M)` — `InIdentifiedSet`, print's own set, which places both
models in `𝕄(sk, λ)` and asks them to share an admissible family. It is **not**
restricted to `modelClass`: print takes the identified set in the margin class,
and requiring `M' ∈ 𝒩` would let classes print rejects satisfy the condition. -/
@[expose] public noncomputable def HasLinearRecoveryModulus
    (sk : Skeleton C (binaryDim C) Bool ℝ)
    (modelClass : Set (Model C (binaryDim C) ℝ)) (lam L δmax : ℝ) : Prop :=
  0 < δmax ∧ ∀ δ : ℝ, 0 ≤ δ → δ < δmax →
    ∀ M ∈ modelClass, ∀ M' : Model C (binaryDim C) ℝ,
      InIdentifiedSet sk lam δ M M' → modelError M M' ≤ L * δ

/-- `def:margin`'s `K`, bound to the class it is defined from.

The source closes `def:margin` with *"Write `K(G) = Σᵢ 2^{|Pa_G(Cᵢ)|}` for the
number of free table entries, and `K = K(sk, λ)` for its **maximum over the
class**"*. So `K` is a quantity determined by `(sk, lam)`, not a free parameter,
and `IsGreatest` is that maximum: `K` is attained by some model of the margin
class and bounds every other.

Leaving `K` free is not a harmless looseness. A rate stated as
`Θ(K · log(1/ε))` with `K` universally quantified and unconstrained is
refutable by substitution alone: `K = 0` forces the budget to vanish and
`K = 1` forces it to grow, under one and the same class. The binding is what
makes the printed rate a claim about the class rather than about the letter. -/
@[expose] public def IsClassChartDim {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] (sk : Skeleton C dim Bool 𝕜) (lam : 𝕜) (K : ℕ) : Prop :=
  IsGreatest {k | ∃ M : Model C dim 𝕜, sk.MarginClass M lam ∧ k = chartDim M.parents} K

/-- **`prob:exact`'s class**, as print fixes it.

*"Let `𝒩 ⊆ 𝕄(sk,λ)` be a compact semialgebraic class satisfying conclusions
(a)–(b) of Problem 24 with modulus `ω(δ) = Lδ`. Assume also a richness
condition: for some graph `G` and `ρ > 0`, its table-parameter projection
contains a `K(G)`-dimensional box of side `ρ`."*

Every clause is now a printed one and none is a stand-in:

* `IsCompactSemialgebraicClass` is *"compact semialgebraic"*, read graph-wise on
  the coordinate spaces `def:margin`'s `K(G)` lives in. An earlier version asked
  for neither word, which quantified O25 over classes print excludes.
* the injectivity clause is `prob:effective`(a) on `𝒩`;
* `HasLinearRecoveryModulus` is `prob:effective`(b) at `ω(δ) = Lδ`, with `M'`
  in print's `I_δ(M)` rather than in `𝒩`;
* `ContainsChartBox` is the richness condition literally: `ClosedBox` is an
  affine box over *all* `K(G)` chart coordinates, so the dimension is forced by
  the space rather than chosen, and `card_chartIndex` proves that count is the
  printed `Σᵢ 2^{|Pa_G(Cᵢ)|}`. The rational stand-in it replaces supplied an
  arbitrary map into models with a noncontraction condition and never required
  its coordinates to be table entries at all.
* `IsClassChartDim` binds `K` to `def:margin`'s maximum over the class.

**Non-vacuity was open and is now closed**, against a package that demands
strictly more than its predecessor: a compact semialgebraic class, a genuinely
`K(G)`-dimensional chart box, and print's larger identified set in the recovery
modulus. `Examples.Conjectures.MAIS.oneNode_exactClassAssumptions` meets all
eight clauses on one binary chance variable, with `K = 1`, `L = 10`,
`ρ = 1 - 2λ` and `δmax = 1`.

What that settles is that the antecedent is nonempty. It does not settle that
the antecedent is *selective*: at one vertex `acyclic` admits only the edgeless
graph, so several clauses hold for reasons about the vertex set rather than
about the class. `conjectures.yaml` records both halves. -/
@[expose] public noncomputable def ExactClassAssumptions (sk : Skeleton C (binaryDim C) Bool ℝ)
    (modelClass : Set (Model C (binaryDim C) ℝ)) (lam : ℝ) (K : ℕ) (L : ℝ)
    (rho : ℝ) (δmax : ℝ) : Prop :=
  Skeleton.ValidMargin lam ∧ 0 < L ∧
    IsClassChartDim sk lam K ∧
    (∀ M ∈ modelClass, sk.MarginClass M lam) ∧
    IsCompactSemialgebraicClass modelClass ∧
    (∀ M ∈ modelClass, ∀ M' ∈ modelClass, sk.BehaviorEq M M' → M = M') ∧
    HasLinearRecoveryModulus sk modelClass lam L δmax ∧
    ContainsChartBox modelClass rho


end AISafetyAtlas.Conjectures.MAIS
