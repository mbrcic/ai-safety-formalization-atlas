module

public import AISafetyAtlas.Conjectures.BinaryPair
public import AISafetyAtlas.Causal.Decision
public import AISafetyAtlas.Causal.EffectiveGenericity
public import AISafetyAtlas.Causal.ParameterChart
public import AISafetyAtlas.Causal.Query
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Data.Real.Basic
public import AISafetyAtlas.Conjectures.MAIS.Common

/-!
# MAIS-O27 — the regret floor

`prob:floor` is a *determine* problem, so its three clauses are exposed as
target objects rather than as an invented truth value.

**Two layers, and the real one is print's.** All three clauses are stated over
`def:margin`'s real class — `O27RealRadiusVanishes`,
`O27RealHasFirstOrderConstant`, `O27RealEdgeSurvivalRegion`, bundled as
`o27RealProblemTargets`. The rational layer beside it is the instance a
decidable witness is computed at, and `Skeleton.marginClass_mapRat` and
`Skeleton.behaviorEq_mapRat` are the transport, the same pair MAIS-O23 uses.
Until 2026-08-23 only the rational layer existed and it was graded as if it were
print's.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Defining a proposition asserts nothing about its truth; resolutions live in
`AISafetyAtlas/Examples/Conjectures/`.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.BinaryPair

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}

/-! ## MAIS-O27 regret-floor answer object -/

/-- The source radius set embedded in `ℝ`, where its least upper bound always
has the intended codomain even when the rational supremum is irrational. -/
public def realRadiusErrors (sk : Skeleton C dim Bool ℚ) (lam δ : ℚ) : Set ℝ :=
  ((fun q : ℚ ↦ (q : ℝ)) '' radiusErrors sk lam δ)

/-- A real number is the worst-case identified-set radius at `δ`. -/
public def IsRealRadius (sk : Skeleton C dim Bool ℚ) (lam δ : ℚ) (r : ℝ) : Prop :=
  IsLUB (realRadiusErrors sk lam δ) r

/-- The selected radius tends to zero from positive rational regrets. -/
public def RadiusTendsToZero (radius : ℚ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℚ, 0 < δ → (δ : ℝ) < δ₀ → |radius δ| < ε

/-- First-order linear radius together with the source's matching
indistinguishable-pair lower witness. -/
public noncomputable def HasFirstOrderRadius (sk : Skeleton C dim Bool ℚ)
    (lam : ℚ) (radius : ℚ → ℝ) (c : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℚ, 0 < δ → (δ : ℝ) < δ₀ →
      |radius δ / (δ : ℝ) - c| < η ∧
      ∃ M M' : Model C dim ℚ, InIdentifiedSet sk lam δ M M' ∧
        (c - η) * (δ : ℝ) ≤ ((modelError M M' : ℚ) : ℝ)

/-- An edge of `M` has strength at least `s`, using the finite witness form of
the maximum in O27(c). -/
public def EdgeStrengthAtLeast (M : Model C dim ℚ) (parent child : C) (s : ℚ) : Prop :=
  parent ∈ M.parents child ∧ ∃ v : Assignment C dim,
    ∃ x y : Fin (dim parent), ∃ a : Fin (dim child), x ≠ y ∧
      s ≤ |M.cpt child a (Function.update v parent x) -
        M.cpt child a (Function.update v parent y)|

/-- Every edge at least as strong as `s` survives every shared
`δ`-admissible policy family. -/
public noncomputable def EdgesSurviveAt (sk : Skeleton C dim Bool ℚ)
    (lam δ s : ℚ) : Prop :=
  ∀ M M' : Model C dim ℚ, InIdentifiedSet sk lam δ M M' →
    ∀ parent child, EdgeStrengthAtLeast M parent child s →
      parent ∈ M'.parents child

/-- The worst-case identified-set radius itself, rather than an answer claiming
that a least upper bound exists for every possibly empty margin class. -/
@[expose] public noncomputable def regretRadius (sk : Skeleton C dim Bool ℚ) (lam δ : ℚ) : ℝ :=
  sSup (realRadiusErrors sk lam δ)

/-- Part (a) of O27 as a precise yes/no proposition for one supplied skeleton. -/
public def O27RadiusVanishes (sk : Skeleton C dim Bool ℚ) (lam : ℚ) : Prop :=
  RadiusTendsToZero (regretRadius sk lam)

/-! ### Characterizations

These three carry the bodies of the definitions above across the module
boundary. Without them a downstream file can name `O27RadiusVanishes` but cannot
reason about it, since a `public def` exports its type and not its body — which
is how a claim about the O27 radius came to live in a coverage note instead of
in a theorem.

The rest of this layer stays opaque, and that is a decision rather than the same
omission: this is the transported instance and not the statement of record, and
its consumers *construct* `EdgeStrengthAtLeast` and `EdgesSurviveAt` rather than
destruct them. The real layer below is where a downstream proof has to reason,
which is why it carries the full set. -/

public theorem mem_realRadiusErrors_iff (sk : Skeleton C dim Bool ℚ) (lam δ : ℚ)
    (x : ℝ) : x ∈ realRadiusErrors sk lam δ ↔
      ∃ q ∈ radiusErrors sk lam δ, (q : ℝ) = x := Iff.rfl

public theorem regretRadius_eq_sSup (sk : Skeleton C dim Bool ℚ) (lam δ : ℚ) :
    regretRadius sk lam δ = sSup (realRadiusErrors sk lam δ) := rfl

public theorem o27RadiusVanishes_iff (sk : Skeleton C dim Bool ℚ) (lam : ℚ) :
    O27RadiusVanishes sk lam ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ δ : ℚ, 0 < δ → (δ : ℝ) < δ₀ → |regretRadius sk lam δ| < ε := Iff.rfl

/-! ### The radius at print's own quantifier

`prob:floor` is stated over `def:margin`'s class, whose tables are **real**.
Everything above is the rational instance: `regretRadius` takes a rational
skeleton and a rational regret, embeds the resulting rational errors in `ℝ`
through `realRadiusErrors`, and takes the supremum there. That layer is not
wrong — it is where the atlas's witnesses are computed, because a rational
witness is decidable where a real one is not — but it is **narrower than print**,
and a grade of `Same` belongs to the layer below rather than to it.

So the real layer is the one that answers to the source, and the rational layer
is its transported instance. `Skeleton.marginClass_mapRat` and
`Skeleton.behaviorEq_mapRat` are the transport, and they are the same two lemmas
that carry the MAIS-O23 witness from `ℚ` to `ℝ`.

Neither layer is a *conjecture* row: `prob:floor` reads *"Determine the
asymptotics of `φ(δ; sk, λ)`"*, and no truth-valued `Prop` is `Same` as a
determine-problem — the rule that retired CONJ-007. That is a fact about
transcription and not about solvability. `prob:floor` has a **target** row,
CONJ-013, whose answer fields carry one specification per clause in print's
order. One printed problem, one row: splitting the clauses into three rows would
make this the only printed problem in the ledger with three,
and the cause was the schema rather than the source. A target row is resolved by
an answer arriving, which then earns an `answer` row of its own — the route
CONJ-009 and CONJ-010 take. -/

/-- **`φ(δ; sk, λ)` at print's quantifier**: real tables, real margin, real
regret, real radius.

The supremum is taken directly in `ℝ` rather than through an embedding, because
here the errors are already real. On an empty margin class this is `sSup ∅ = 0`
by the conditionally-complete-lattice convention, which is the same convention
`regretRadius` inherits and the same one `exactAnalystRisk` uses.

**That convention makes a *positive* answer to (a) cheap on a degenerate class**
and is worth saying at the definition rather than leaving for a reader to find:
if `𝕄(sk, λ)` is empty then `φ ≡ 0`, so `O27RealRadiusVanishes` holds for a
reason about the class being empty rather than about the identified set
shrinking. Nothing here proves the printed class nonempty in general, and print
does not either. The instances proved in
`Examples/Conjectures/MAIS/O27.lean` are unaffected in both directions: they are
*refutations*, which an empty class cannot produce, and their class is
independently inhabited — `Examples.Causal.edgeless_mem`, `arrowXY_mem` and
`arrowYX_mem` each place a model in it. -/
@[expose] public noncomputable def realRegretRadius (sk : Skeleton C dim Bool ℝ)
    (lam δ : ℝ) : ℝ :=
  sSup (radiusErrors sk lam δ)

/-- The radius tends to zero as the regret does, with `δ` ranging over the
**reals** as `prob:floor` writes it rather than over the rationals a witness is
computed at. -/
public def RealRadiusTendsToZero (radius : ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ → |radius δ| < ε

/-- **MAIS-O27(a) at print's quantifier**: *"decide whether `φ(0⁺) = 0`"*, over
real tables and a real regret.

`O27RadiusVanishes` is the rational instance of this. Refuting the real form is
strictly the stronger statement, since a real skeleton and a real regret range
are what `prob:floor` quantifies over. -/
public def O27RealRadiusVanishes (sk : Skeleton C dim Bool ℝ) (lam : ℝ) : Prop :=
  RealRadiusTendsToZero (realRegretRadius sk lam)

/-! Characterizations for the real layer, for the same reason the rational layer
needs them: a `public def` exports its type and not its body, so without these a
downstream module can name these propositions and prove nothing about them. -/

public theorem realRegretRadius_eq_sSup (sk : Skeleton C dim Bool ℝ) (lam δ : ℝ) :
    realRegretRadius sk lam δ = sSup (radiusErrors sk lam δ) := rfl

public theorem mem_radiusErrors_iff (sk : Skeleton C dim Bool ℝ) (lam δ x : ℝ) :
    x ∈ radiusErrors sk lam δ ↔
      ∃ M M' : Model C dim ℝ, sk.MarginClass M lam ∧
        InIdentifiedSet sk lam δ M M' ∧ x = modelError M M' := Iff.rfl

public theorem o27RealRadiusVanishes_iff (sk : Skeleton C dim Bool ℝ) (lam : ℝ) :
    O27RealRadiusVanishes sk lam ↔
      ∀ ε : ℝ, 0 < ε → ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ δ : ℝ, 0 < δ → δ < δ₀ → |realRegretRadius sk lam δ| < ε := Iff.rfl

/-- The real radius is pinned by the two facts every instance uses: some pair
attains `x`, and no pair exceeds `1`. Stated once here so a witness module
supplies the two facts rather than re-deriving the `sSup` argument. -/
public theorem realRegretRadius_eq_of_mem_of_le (sk : Skeleton C dim Bool ℝ)
    {lam δ x : ℝ} (hmem : x ∈ radiusErrors sk lam δ)
    (hle : ∀ y ∈ radiusErrors sk lam δ, y ≤ x) :
    realRegretRadius sk lam δ = x :=
  le_antisymm (csSup_le ⟨x, hmem⟩ hle) (le_csSup ⟨x, hle⟩ hmem)

/-- Part (b) of O27 for a proposed first-order constant, including its matching
indistinguishable-pair lower witnesses. -/
public noncomputable def O27HasFirstOrderConstant (sk : Skeleton C dim Bool ℚ)
    (lam : ℚ) (c : ℝ) : Prop :=
  0 ≤ c ∧ HasFirstOrderRadius sk lam (regretRadius sk lam) c

/-- Part (c) of O27 is a predicate on pairs `(s, δ)`, not necessarily a cut
described by one threshold function. -/
public noncomputable def O27EdgeSurvivalRegion (sk : Skeleton C dim Bool ℚ)
    (lam : ℚ) : Set (ℚ × ℚ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ EdgesSurviveAt sk lam p.2 p.1}

/-! ### Clauses (b) and (c) at print's own quantifier

Clause (a) reached `prob:floor`'s real setting above. These are the other two,
and with them the answer bundle a solver would fill.

Nothing here is a translation of the rational predicates: `def:margin`'s tables
are real, `prob:floor`'s `δ` is real, and clause (c)'s `(s, δ)` pairs are real,
so these are the printed statements and the rational ones above are the instance
a decidable witness is computed at. The rational layer is kept for exactly that
reason and for no other. -/

/-- **O27(c)'s edge strength, over real tables.**

`prob:floor`(c) defines the *strength* of an edge as *"the maximum, over pairs of
parent configurations differing only in the tail variable, of the induced table
difference"*. A maximum being at least `s` is the existential written here; at
binary variables *"differing only in the tail variable"* forces the pair `0, 1`,
which is what `x ≠ y` says on `Fin 2`. -/
public def RealEdgeStrengthAtLeast (M : Model C dim ℝ) (parent child : C) (s : ℝ) : Prop :=
  parent ∈ M.parents child ∧ ∃ v : Assignment C dim,
    ∃ x y : Fin (dim parent), ∃ a : Fin (dim child), x ≠ y ∧
      s ≤ |M.cpt child a (Function.update v parent x) -
        M.cpt child a (Function.update v parent y)|

/-- **O27(c)'s survival condition, over real tables.** Every edge of strength at
least `s` is present in every model of `I_δ(M)`. -/
public noncomputable def RealEdgesSurviveAt (sk : Skeleton C dim Bool ℝ)
    (lam δ s : ℝ) : Prop :=
  ∀ M M' : Model C dim ℝ, InIdentifiedSet sk lam δ M M' →
    ∀ parent child, RealEdgeStrengthAtLeast M parent child s →
      parent ∈ M'.parents child

/-- **O27(b) at print's quantifier**: the first-order constant together with the
matching lower witness print asks for in the same breath.

`prob:floor`(b) reads *"assuming it is zero, determine `lim_{δ→0} φ(δ)/δ` as an
explicit function of `(sk, λ)`, together with the matching statement that some
pair of models at distance `cδ` is `δ`-indistinguishable"*. The limit is the
first conjunct; the *matching statement* is the second, and it is not a
consequence of the first — a limit of a supremum does not by itself produce a
pair attaining it, which is why print names both. -/
public noncomputable def HasRealFirstOrderRadius (sk : Skeleton C dim Bool ℝ)
    (lam : ℝ) (radius : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧
    ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      |radius δ / δ - c| < η ∧
      ∃ M M' : Model C dim ℝ, InIdentifiedSet sk lam δ M M' ∧
        (c - η) * δ ≤ modelError M M'

/-- Part (b) of O27 for a proposed first-order constant, at print's quantifier. -/
public noncomputable def O27RealHasFirstOrderConstant (sk : Skeleton C dim Bool ℝ)
    (lam : ℝ) (c : ℝ) : Prop :=
  0 ≤ c ∧ HasRealFirstOrderRadius sk lam (realRegretRadius sk lam) c

/-- Part (c) of O27 at print's quantifier: the full two-dimensional region, not
a cut described by one threshold function. The withdrawn encoding below assumed
the closed-threshold shape and was false for that reason. -/
public noncomputable def O27RealEdgeSurvivalRegion (sk : Skeleton C dim Bool ℝ)
    (lam : ℝ) : Set (ℝ × ℝ) :=
  {p | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ RealEdgesSurviveAt sk lam p.2 p.1}

/-! Characterizations for the real (b) and (c), for the reason the other layers
need them: a `public def` exports its type and not its body. -/

omit [Nonempty C] in
public theorem realEdgesSurviveAt_iff (sk : Skeleton C dim Bool ℝ) (lam δ s : ℝ) :
    RealEdgesSurviveAt sk lam δ s ↔
      ∀ M M' : Model C dim ℝ, InIdentifiedSet sk lam δ M M' →
        ∀ parent child, RealEdgeStrengthAtLeast M parent child s →
          parent ∈ M'.parents child := Iff.rfl

omit [Nonempty C] in
public theorem mem_o27RealEdgeSurvivalRegion_iff (sk : Skeleton C dim Bool ℝ)
    (lam : ℝ) (p : ℝ × ℝ) :
    p ∈ O27RealEdgeSurvivalRegion sk lam ↔
      0 ≤ p.1 ∧ 0 ≤ p.2 ∧ RealEdgesSurviveAt sk lam p.2 p.1 := Iff.rfl

public theorem o27RealHasFirstOrderConstant_iff (sk : Skeleton C dim Bool ℝ)
    (lam c : ℝ) :
    O27RealHasFirstOrderConstant sk lam c ↔
      0 ≤ c ∧ HasRealFirstOrderRadius sk lam (realRegretRadius sk lam) c := Iff.rfl

omit [Nonempty C] in
/-- Print's *strength of an edge*, spelled out across the module boundary.

`realEdgesSurviveAt_iff` stops one step short of this: it exposes the shape of
(c)'s survival condition but leaves `RealEdgeStrengthAtLeast` opaque, so a
downstream module could supply the hypothesis and never read it. Constructing one
has a route already -- `realEdgeStrengthAtLeast_lam_of_printedM4` -- and
*destructing* one had none, which is the half a proof of survival at some `(s,
δ)` needs. -/
public theorem realEdgeStrengthAtLeast_iff (M : Model C dim ℝ) (parent child : C)
    (s : ℝ) :
    RealEdgeStrengthAtLeast M parent child s ↔
      parent ∈ M.parents child ∧ ∃ v : Assignment C dim,
        ∃ x y : Fin (dim parent), ∃ a : Fin (dim child), x ≠ y ∧
          s ≤ |M.cpt child a (Function.update v parent x) -
            M.cpt child a (Function.update v parent y)| := Iff.rfl

/-- **Clause (b) at print's quantifier, spelled out across the module boundary.**

Without this, `O27RealHasFirstOrderConstant` is reachable downstream and
`HasRealFirstOrderRadius` -- everything the clause actually says -- is not:
`unfold` and `simp only` both fail on it, since a `public def` exports its type
and not its body. Clause (b) is the one clause of `prob:floor` with no instance
in either direction, so the module boundary stood in front of exactly the open
question, and the section above claimed the opposite for three definitions while
being silent about this one. -/
public theorem hasRealFirstOrderRadius_iff (sk : Skeleton C dim Bool ℝ)
    (lam : ℝ) (radius : ℝ → ℝ) (c : ℝ) :
    HasRealFirstOrderRadius sk lam radius c ↔
      ∀ η : ℝ, 0 < η → ∃ δ₀ : ℝ, 0 < δ₀ ∧
        ∀ δ : ℝ, 0 < δ → δ < δ₀ →
          |radius δ / δ - c| < η ∧
          ∃ M M' : Model C dim ℝ, InIdentifiedSet sk lam δ M M' ∧
            (c - η) * δ ≤ modelError M M' := Iff.rfl

omit [Nonempty C] in
/-- **(M4) gives every edge of a margin-class model strength at least `λ`.**

Print defines edge strength in `prob:floor`(c) and bounds it below in
`def:margin`'s (M4), in the same words. Naming the connection makes clause (c)
non-vacuous at `s = λ`: without it, a reader cannot tell whether any edge in the
class is strong enough for (c) to say anything about. -/
public theorem realEdgeStrengthAtLeast_lam_of_printedM4
    {M : Model C (binaryDim C) ℝ} {lam : ℝ}
    (hM : Skeleton.PrintedM4 M lam) {parent child : C}
    (hmem : parent ∈ M.parents child) :
    RealEdgeStrengthAtLeast M parent child lam := by
  obtain ⟨v, hv⟩ := hM child parent hmem
  refine ⟨hmem, v, 0, 1, 1, ?_, hv⟩
  intro hcon
  exact absurd (congrArg Fin.val hcon) (by simp)

/-- The O27 answer shape at print's quantifier. -/
public structure O27RealProblemTargets (C : Type*) [Fintype C] [DecidableEq C]
    (dim : C → ℕ) where
  radius : ℝ → ℝ
  edgeSurvivalRegion : Set (ℝ × ℝ)

/-- **The O27 targets, over `def:margin`'s real class.** This is what
`prob:floor` asks a solver to determine; `o27ProblemTargets` below is its
rational instance. -/
public noncomputable def o27RealProblemTargets (sk : Skeleton C dim Bool ℝ)
    (lam : ℝ) : O27RealProblemTargets C dim where
  radius := realRegretRadius sk lam
  edgeSurvivalRegion := O27RealEdgeSurvivalRegion sk lam

/-- The mathematical targets that the three clauses of O27 ask a solver to determine.

An open problem phrased as "determine" is not itself a conjecture. The radius,
its asymptotic predicates, and the full two-dimensional edge-survival region
are therefore exposed directly, without postulating a false closed-threshold
shape. -/
public structure O27ProblemTargets (C : Type*) [Fintype C] [DecidableEq C]
    (dim : C → ℕ) where
  radius : ℚ → ℝ
  edgeSurvivalRegion : Set (ℚ × ℚ)

/-- The O27 targets for a supplied **rational** margin-class instance.

**This is the rational instance, and `o27RealProblemTargets` is print's.**
`prob:floor` writes `φ(δ; sk, λ)` over `def:margin`'s real class with `δ` real,
and asks for the real `(s, δ)` region in clause (c). This bundle takes `δ : ℚ`
and returns `Set (ℚ × ℚ)`, so a solver who filled *these* fields would have
answered the rational instance of the problem.

All three clauses are stated in the real setting —
`O27RealRadiusVanishes`, `O27RealHasFirstOrderConstant`,
`O27RealEdgeSurvivalRegion` — so this layer is not where the problem is stated. It is kept because it is where a *decidable* witness is computed: the
collision pair is built on rational literals, and the real instances are its
image under `Skeleton.marginClass_mapRat` and `Skeleton.behaviorEq_mapRat`.

Direction is worth keeping in view when reading a rational result: `φ` is a
supremum over the class, so replacing `ℝ` by `ℚ` can only lower it. A rational
*negative* answer therefore transports up to print, and a rational *positive*
one does not. -/
public noncomputable def o27ProblemTargets (sk : Skeleton C dim Bool ℚ)
    (lam : ℚ) : O27ProblemTargets C dim where
  radius := regretRadius sk lam
  edgeSurvivalRegion := O27EdgeSurvivalRegion sk lam

/-- Withdrawn threshold encoding from the first atlas transcription of O27(c).

The source asks for the complete set of pairs `(s, δ)`. That set need not be a
closed cut generated by one threshold, so this stronger shape is retained only
to make the historical withdrawn encoding auditable. It is not a ledger row. -/
public noncomputable def IsExactEdgeThreshold (sk : Skeleton C dim Bool ℚ)
    (lam : ℚ) (threshold : ℚ → ℚ) : Prop :=
  ∀ δ s : ℚ, 0 ≤ δ → 0 ≤ s →
    (threshold δ ≤ s → EdgesSurviveAt sk lam δ s) ∧
    (s < threshold δ → ∃ M M' : Model C dim ℚ, ∃ parent child,
      InIdentifiedSet sk lam δ M M' ∧
      EdgeStrengthAtLeast M parent child s ∧ parent ∉ M'.parents child)

/-- Withdrawn answer shape from the first rational transcription of O27. -/
public structure O27Answer where
  radius : ℚ → ℝ
  vanishes : Bool
  linearConstant : ℝ
  edgeThreshold : ℚ → ℚ

/-- Correctness predicate for the withdrawn answer shape. -/
public noncomputable def IsCorrectO27Answer (sk : Skeleton C dim Bool ℚ)
    (lam : ℚ) (answer : O27Answer) : Prop :=
  (∀ δ : ℚ, 0 ≤ δ → IsRealRadius sk lam δ (answer.radius δ)) ∧
    (answer.vanishes = true ↔ RadiusTendsToZero answer.radius) ∧
    (answer.vanishes = true →
      0 ≤ answer.linearConstant ∧
        HasFirstOrderRadius sk lam answer.radius answer.linearConstant) ∧
    IsExactEdgeThreshold sk lam answer.edgeThreshold

/--
**Withdrawn first encoding of MAIS-O27.**

This proposition incorrectly requires a closed edge-threshold cut and fails on
empty margin classes. It is retained under an explicit withdrawn name so the
ledger can record the defect; use `o27ProblemTargets`, `O27RadiusVanishes`,
`O27HasFirstOrderConstant`, and `O27EdgeSurvivalRegion` for the source problem.
-/
public noncomputable def maisO27_regretFloor_withdrawnThresholdEncoding : Prop :=
  ∀ (C : Type) [Fintype C] [DecidableEq C] [Nonempty C]
    (dim : C → ℕ) (sk : Skeleton C dim Bool ℚ) (lam : ℚ),
    IsBinaryDimension dim → Skeleton.ValidMargin lam →
      ∃ answer : O27Answer, IsCorrectO27Answer sk lam answer

/-! ## Specifications over a supplied answer

The definitions above name the objects `prob:floor` asks about. These say what
it means for a *proposed answer* to be right, which is the shape an
answer-construction problem needs and the shape a fillable record does not have:
`o27RealProblemTargets` can be inhabited with anything, so a term of it proves
nothing, while a proof of a predicate below is a proof about the printed
quantity.

The atlas cannot ship the answer slot itself. Formal Conjectures marks one with
`answer(sorry)`, which elaborates `sorryAx` into the statement's *type* — under
its default setting a `Prop`-valued slot becomes `True` so a challenge file
compiles — and both the forbidden-token scan and the kernel axiom audit reject
that here, correctly: those are benchmark-harness semantics. The sorry-free
equivalent is the factored answer, where the candidate is an ordinary parameter
and the specification is an ordinary `Prop`. CONJ-009 and CONJ-010 already
worked this way before the ledger had a name for it. -/

/-- **O27(b) with the answer bound outside the problem instance.**

`prob:floor`(b) asks for the first-order constant *"as an explicit function of
`(sk, λ)`"*. `O27RealHasFirstOrderConstant sk lam c` binds `c` after `sk` and
`lam`, so it says only that each instance *has* a constant — which is weaker,
since a family of pointwise constants need not be a function anyone can write
down. Here the candidate is a function and the quantifiers over `sk` and `lam`
sit inside it, which is print's order.

Formal Conjectures enforces the same discipline syntactically: its answer linter
warns when an answer slot appears to the right of the theorem's own binders,
precisely so the answer is one answer to the whole question rather than
something that may vary with an argument. -/
public noncomputable def IsO27FirstOrderConstantFunction
    (c : Skeleton C dim Bool ℝ → ℝ → ℝ) : Prop :=
  ∀ (sk : Skeleton C dim Bool ℝ) (lam : ℝ),
    O27RealHasFirstOrderConstant sk lam (c sk lam)

omit [Nonempty C] in
/-- **O27(a) with the answer bound outside the problem instance.**

`prob:floor`(a) reads *"decide whether `φ(0⁺) = 0`"* while the quantity itself
depends on `(sk, λ)`, and clause (b) opens *"assuming it is zero"*. The
criterion below is the extensional correctness specification for that
parameterized question: membership says exactly that the printed equality holds
at the supplied instance.

This packaging imposes no answer language. In particular, print does not ask
for a human-readable, computable or semialgebraic criterion here; the phrase
*"the human-readable answer"* occurs in the later discussion of
`prob:starter-set`(a), not in `prob:floor`. A criterion defined by the printed
condition itself satisfies this specification, so admissibility remains an
explicitly recorded open gap rather than an atlas-added premise. -/
public noncomputable def IsO27RadiusVanishingCriterion
    (P : Skeleton C dim Bool ℝ → ℝ → Prop) : Prop :=
  ∀ (sk : Skeleton C dim Bool ℝ) (lam : ℝ),
    P sk lam ↔ O27RealRadiusVanishes sk lam

/-- **O27(c) as a find-all specification**: a candidate region is correct when
its membership agrees with the printed survival condition at every pair.

Soundness and completeness together, which is what *"decide for which pairs"*
asks and what a one-directional inclusion would not give. -/
public noncomputable def IsO27EdgeSurvivalRegion (sk : Skeleton C dim Bool ℝ)
    (lam : ℝ) (S : Set (ℝ × ℝ)) : Prop :=
  ∀ p : ℝ × ℝ, p ∈ S ↔ (0 ≤ p.1 ∧ 0 ≤ p.2 ∧ RealEdgesSurviveAt sk lam p.2 p.1)

/-! ### `prob:floor` names no answer language, and this section does not supply one

`IsO27EdgeSurvivalRegion` takes a `Set (ℝ × ℝ)`, which in Lean is a predicate,
so the region defined *as* the survival condition satisfies it by unfolding —
`isO27EdgeSurvivalRegion_self` below is that proof. Ruling the restatement out
would need a language an answer has to be written in, and **`prob:floor` names
none, for any of its three clauses.**

That is a fact about the printed text rather than a gap in reading it.
*Semialgebraic* appears twice in MAIS-A2: as a hypothesis on the model class in
`prob:exact`, and as a demand on the answer in `prob:starter-set`(a) —
*"Determine, as an explicit semialgebraic condition on `(u, θ)`"*. `prob:floor`
says only *"decide for which pairs `(s, δ)`"*, and for clause (b) *"as an
explicit function of `(sk, λ)`"* without defining *explicit*. A hypothesis in
one printed problem does not impose an answer language on another, so reading
`prob:exact`'s adjective onto `prob:floor` would make this row **narrower than
print**.

`IsO27EdgeSurvivalAnswer` below is therefore an **atlas strengthening offered
for study, not an admissibility condition the source requires**, and the ledger
does not grade it as one. Two limits are worth stating before anyone reaches for
it. First, `Causal.IsSemialgebraic` is an *existential* — it asserts that some
finite family of polynomial pieces cuts the set out — so the canonical region
together with a proof that it happens to be semialgebraic satisfies the
conjunction, and the restatement is not excluded after all. An answer language
that does exclude it has to make the pieces **data**: a finite list of sign
conditions, its interpretation as a plane set, and a theorem equating that with
the survival region. Second, whether the printed region *is* semialgebraic is
open. It is plausible — the tables are finitely many reals, the margin and
edge-strength conditions are polynomial inequalities, and Tarski–Seidenberg
carries real quantifiers — but `InIdentifiedSet` quantifies over a policy family
indexed by every real intervention mixture, and reducing that function-valued
existential to a first-order real formula is a step no theorem here takes.

The same is true of clauses (a) and (b), whose answers are a criterion
`Skeleton … → ℝ → Prop` and a function `Skeleton … → ℝ → ℝ`. Those are
chartable: with `C`, `dim` and the two `Finset`s fixed, a skeleton's `utility`
field is finitely many reals cut out by `utility_parents`' linear equalities and
the `[0,1]` box, so a fibrewise semialgebraic condition on the locus, or on the
graph of the function, is definable. What is missing is not the notion but the
warrant to demand it, and — for a criterion asked of every `C` and `dim` — a
decision about whether *explicit* should also mean uniform in the discrete data.
The ledger records both clauses as open on this axis, with what a solver would
have to state, rather than choosing on print's behalf. -/

/-- **A plane set is semialgebraic** when the set of `(x 0, x 1)` pairs that
land in it is, read through `Fin 2 → ℝ`, which is where `Causal.IsSemialgebraic`
is stated. -/
@[expose] public def IsSemialgebraicPlaneSet (S : Set (ℝ × ℝ)) : Prop :=
  Causal.IsSemialgebraic {x : Fin 2 → ℝ | (x 0, x 1) ∈ S}

/-- **An atlas strengthening of clause (c), not a source demand.** A candidate
region is asked to be semialgebraic as well as correct.

`prob:floor` does not ask for this — see the section header — and the ledger
does not grade it as admissibility. It is kept because the question *is the
printed region semialgebraic* is worth asking and this is the statement of it,
and because a solver who answers with polynomial data can discharge it. It does
**not** by itself exclude a restatement: `Causal.IsSemialgebraic` is an
existential, so the canonical region plus a proof of semialgebraicity satisfies
this conjunction. -/
public noncomputable def IsO27EdgeSurvivalAnswer (sk : Skeleton C dim Bool ℝ)
    (lam : ℝ) (S : Set (ℝ × ℝ)) : Prop :=
  IsSemialgebraicPlaneSet S ∧ IsO27EdgeSurvivalRegion sk lam S

omit [Nonempty C] in
public theorem isO27EdgeSurvivalAnswer_iff (sk : Skeleton C dim Bool ℝ)
    (lam : ℝ) (S : Set (ℝ × ℝ)) :
    IsO27EdgeSurvivalAnswer sk lam S ↔
      IsSemialgebraicPlaneSet S ∧ IsO27EdgeSurvivalRegion sk lam S :=
  Iff.rfl

/-- The empty region is semialgebraic, so the demand is not empty of instances. -/
public theorem isSemialgebraicPlaneSet_empty :
    IsSemialgebraicPlaneSet (∅ : Set (ℝ × ℝ)) := by
  unfold IsSemialgebraicPlaneSet
  simpa using Causal.isSemialgebraic_empty (ι := Fin 2)

/-- **The quadrant the printed region lives in is semialgebraic.**
`IsO27EdgeSurvivalRegion` requires `0 ≤ p.1 ∧ 0 ≤ p.2` of every member, so any
answer is a subset of this set; that the ambient constraint is expressible in
the admissible language is what makes the demand a condition on the *survival*
part rather than on the bookkeeping. -/
public theorem isSemialgebraicPlaneSet_nonnegQuadrant :
    IsSemialgebraicPlaneSet {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2} := by
  unfold IsSemialgebraicPlaneSet
  have h0 : Causal.IsSemialgebraic
      {x : Fin 2 → ℝ | 0 ≤ MvPolynomial.eval x (MvPolynomial.X 0 :
        MvPolynomial (Fin 2) ℝ)} :=
    Causal.isSemialgebraic_setOf_eval_nonneg _
  have h1 : Causal.IsSemialgebraic
      {x : Fin 2 → ℝ | 0 ≤ MvPolynomial.eval x (MvPolynomial.X 1 :
        MvPolynomial (Fin 2) ℝ)} :=
    Causal.isSemialgebraic_setOf_eval_nonneg _
  refine Causal.IsSemialgebraic.setOf_congr (fun x ↦ ?_)
    (Causal.IsSemialgebraic.setOf_and h0 h1)
  simp

omit [Nonempty C] in
/-- **The specification admits a circular answer, and this is the proof.**

`O27RealEdgeSurvivalRegion` is the region defined *as* the set of pairs
satisfying the survival condition, so it satisfies the specification by
unfolding and contributes nothing a reader did not already have. That is not a
defect in the definition above — it is the reason an answer-construction problem
needs an *admissibility* condition on top of a correctness condition, and the
reason `conjectures.yaml` records an *Unformalized* admissibility status for this
row rather than leaving the field to suggest the question is closed.

Formal Conjectures documents the identical hole with the identical example and
declines to police it; ECP adds a separate admissible-vocabulary layer instead.
Stating the circularity as a theorem is the cheapest honest thing to do with a
gap that no checker will otherwise surface. -/
public theorem isO27EdgeSurvivalRegion_self (sk : Skeleton C dim Bool ℝ) (lam : ℝ) :
    IsO27EdgeSurvivalRegion sk lam (O27RealEdgeSurvivalRegion sk lam) :=
  fun _ ↦ Iff.rfl

/-- Clause (a)'s specification admits the same circular answer, for the same
reason: the criterion defined *as* the vanishing condition satisfies it by
unfolding. -/
public theorem isO27RadiusVanishingCriterion_self :
    IsO27RadiusVanishingCriterion (C := C) (dim := dim)
      (fun sk lam ↦ O27RealRadiusVanishes sk lam) :=
  fun _ _ ↦ Iff.rfl


end AISafetyAtlas.Conjectures.MAIS
