module

public import PFR.ForMathlib.Entropy.Basic

/-!
# The data-processing inequality

Cover & Thomas, Theorem 2.8.1: if `X → Y → Z` is a Markov chain then
`I(X ; Z) ≤ I(X ; Y)` — no processing of `Y` can increase what it says about `X`.

| | printed source | this module |
|---|---|---|
| conclusion | the one inequality | both directions, the difference *identity*, and the equality case |

That is the whole of it. The module also takes any measurable space with an
`IsZeroOrProbabilityMeasure` where the source takes a discrete distribution, and
that **is not a widening**: the variables are `FiniteRange`, so they push the
measure forward to a pmf on finite alphabets, the printed theorem applies to that
pmf, and the statement here is the printed statement at the pushforward. The two
are inter-derivable, so those rows are graded `Same`; see the sample-space note
in `docs/provenance/source-coverage-audit.md` and the worked case in
`AISafetyAtlas.Examples.InformationTheory.ContinuousSampleSpace`. The
sole object outside print's reach is the zero measure, where every quantity is
`0`, which is vacuity rather than generality.

The two corollaries Cover & Thomas draw from it — both unnumbered in the 2nd
edition — are recovered rather than reproved: `Z := g ∘ Y` is a Markov chain
(`isMarkovChain_comp`), so `I(X;Y) ≥ I(X;g(Y))` is an instance of the main
theorem, and `I(X;Y|Z) ≤ I(X;Y)` falls out of the difference identity.

## What is new here

PFR already proves the *functional* data-processing inequalities
(`entropy_comp_le`, `mutual_comp_le`, `mutual_comp_comp_le`,
`condMutual_comp_comp_le`) — those need no restating. What PFR does not have,
and what this module supplies, is:

* `mutualInfo_chain_rule` and `mutualInfo_chain_rule'`, the chain rule for
  mutual information, `I[X : ⟨Y,Z⟩] = I[X : Z] + I[X : Y | Z]` in both
  argument orders. These are the only new mathematics in the file; everything
  else is assembly. They are natural upstream candidates.
* the Markov-chain form itself, which is strictly more general than the
  functional form: `mutualInfo_comp_le` is derived from it here, whereas the
  converse derivation is impossible — a Markov chain need not be functional.
* `isMarkovChain_iff_measure_factorizes_singleton`, the bridge back to the
  book's own definition. `IsMarkovChain` is `CondIndepFun`, which is (2.118)'s
  right-hand side; Cover & Thomas start instead from the factorization (2.117).
  Proving the two equivalent is what stops the choice of definition from being a
  convention the section then trades on. See *The definitional bridge* below.

## The equality case

`mutualInfo_sub_eq` states the exact identity behind the inequality,

```
I[X : Y] - I[X : Z] = I[X : Y | Z] - I[X : Z | Y]
```

which holds with **no hypothesis on the three variables at all**. The Markov
assumption enters only by killing the second term. Consequently equality holds
in the data-processing inequality precisely when `X → Z → Y` is *also* a Markov
chain (`mutualInfo_eq_iff_isMarkovChain`). Cover & Thomas assert this inside the
proof of Theorem 2.8.1, as a remark, without proving it — as they do the dual
conclusion `I(Y;Z) ≥ I(X;Z)`, which they leave at "similarly, one can prove".
Both are proved here.

## The definitional bridge

The equivalence comes in two strengths, and both are here.

`isMarkovChain_iff_measure_factorizes_singleton` is the printed (2.118): Markov
chain iff `p(y)·p(x,y,z) = p(x,y)·p(y,z)` at every point mass. That is the
equivalence Cover & Thomas prove, at the hypothesis they prove it from. Its
left-hand side is the book's (2.117) cleared of denominators; the three-factor
`p(x) p(y|x) p(z|y)` is not written anywhere in Lean.

`isMarkovChain_iff_measure_factorizes` widens the factorization to arbitrary
measurable `s`, `t`. Read as a *conclusion* that is stronger than the printed
one, and read as a *hypothesis* it is stronger too — so as an `iff` it is neither
above nor below the printed form. `measure_preimage_inter_eq_tsum`
is what connects them: a measurable slice of a countable-valued variable splits
over its point masses, applied once in `X` and once in `Z`.

Which one to reach for: the singleton form to *check* that something is a Markov
chain, the set form to *use* one.

## Not covered

The conditioned form `I[X : Z | W] ≤ I[X : Y | W]`, under conditional
independence of `X` and `Z` given `⟨Y, W⟩`, is a further generalisation. It is
not in the printed source and is not proved here; it needs a conditional
counterpart of `mutualInfo_chain_rule`, which in turn needs the
pair-reassociation transport for conditional entropy.

## Provenance of the entropy layer

`H[· ; ·]`, `I[· : · ; ·]`, `I[· : · | · ; ·]` and `CondIndepFun` are PFR's, at
natural logarithm. See `AISafetyAtlas.InformationTheory.Fano` for why the
atlas's own `AISafetyAtlas.Inference.entropyOn` is a separate development and is
not migrated.
-/

namespace AISafetyAtlas.InformationTheory

open MeasureTheory ProbabilityTheory Real Function

universe uΩ uS uT uU

variable {Ω : Type uΩ} {S : Type uS} {T : Type uT} {U : Type uU}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace T] [MeasurableSpace U]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass T] [MeasurableSingletonClass U]
variable [Countable S] [Countable T] [Countable U]
variable {X : Ω → S} {Y : Ω → T} {Z : Ω → U} {μ : Measure Ω}

/-! ## Markov chains -/

/--
`X → Y → Z` is a Markov chain: `Z` depends on `X` only through `Y`, stated as
conditional independence of `X` and `Z` given `Y`.

This is the hypothesis of Cover & Thomas, Theorem 2.8.1. It is weaker than
requiring `Z` to be a function of `Y` (see `isMarkovChain_comp`), and it does
not presuppose any joint density or finiteness: it is `CondIndepFun`, which is
defined for arbitrary measurable spaces.
-/
@[expose] public def IsMarkovChain (X : Ω → S) (Y : Ω → T) (Z : Ω → U)
    (μ : Measure Ω) : Prop :=
  CondIndepFun X Z Y μ

omit [MeasurableSingletonClass S] [MeasurableSingletonClass U] [Countable S] [Countable U] in
/--
**Cover & Thomas (2.117), the defining factorization.** `X → Y → Z` exactly when

`p(y) · p(x, y, z) = p(x, y) · p(y, z)`

for every `x`, `y`, `z` — which is `p(x, y, z) = p(x) p(y|x) p(z|y)` cleared of
denominators, so it needs no positivity side condition and says the right thing
on null fibres of `Y`.

The atlas *defines* `IsMarkovChain` as `CondIndepFun`, taking (2.118)'s
right-hand side where the book takes (2.117). This is the bridge back: it makes
the printed definition a theorem rather than a convention, so the section's
equivalence is derived and not assumed.

Stated over arbitrary measurable `s`, `t` rather than the printed point masses.
`isMarkovChain_iff_measure_factorizes_singleton` is the printed form, with the
hypothesis weakened to point masses; this one is the stronger statement forwards
and the weaker one in reverse, and both are available.

Only `Y` needs to be measurable. `X` and `Z` are unconstrained, and `S` and `U`
need neither countability nor measurable singletons — the conditioning happens
on `Y`'s fibres and nothing else in the argument looks at the other two.
-/
public theorem isMarkovChain_iff_measure_factorizes [IsProbabilityMeasure μ]
    (hY : Measurable Y) :
    IsMarkovChain X Y Z μ ↔
      ∀ (y : T) (s : Set S) (t : Set U), MeasurableSet s → MeasurableSet t →
        μ (Y ⁻¹' {y}) * μ (X ⁻¹' s ∩ Y ⁻¹' {y} ∩ Z ⁻¹' t)
          = μ (X ⁻¹' s ∩ Y ⁻¹' {y}) * μ (Y ⁻¹' {y} ∩ Z ⁻¹' t) := by
  have hfib : ∀ y : T, MeasurableSet (Y ⁻¹' {y}) := fun y => hY (measurableSet_singleton y)
  have hne : ∀ y : T, μ (Y ⁻¹' {y}) ≠ ⊤ := fun y => measure_ne_top μ _
  -- the three intersections, rewritten so `cond_apply` applies to each
  have hswap : ∀ (y : T) (s : Set S) (t : Set U),
      Y ⁻¹' {y} ∩ (X ⁻¹' s ∩ Z ⁻¹' t) = X ⁻¹' s ∩ Y ⁻¹' {y} ∩ Z ⁻¹' t := by
    intro y s t
    ext ω
    simp only [Set.mem_inter_iff]
    tauto
  have hswapX : ∀ (y : T) (s : Set S), Y ⁻¹' {y} ∩ X ⁻¹' s = X ⁻¹' s ∩ Y ⁻¹' {y} :=
    fun _ _ => Set.inter_comm _ _
  rw [show IsMarkovChain X Y Z μ ↔ ∀ᵐ y ∂(μ.map Y), IndepFun X Z (μ[|Y ← y]) from Iff.rfl,
    ae_iff_of_countable]
  constructor
  · intro h y s t hs ht
    by_cases hy : μ (Y ⁻¹' {y}) = 0
    · -- a null fibre contains both sides
      have h₁ : μ (X ⁻¹' s ∩ Y ⁻¹' {y} ∩ Z ⁻¹' t) = 0 :=
        measure_mono_null (by intro ω hω; exact hω.1.2) hy
      have h₂ : μ (X ⁻¹' s ∩ Y ⁻¹' {y}) = 0 :=
        measure_mono_null (fun ω hω => hω.2) hy
      simp [hy, h₁, h₂]
    · have hmapy : (μ.map Y) {y} ≠ 0 := by
        rwa [Measure.map_apply hY (measurableSet_singleton y)]
      have hind := h y hmapy
      rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul] at hind
      have hthis := hind s t hs ht
      rw [cond_apply (hfib y), cond_apply (hfib y), cond_apply (hfib y),
        hswap y s t, hswapX y s] at hthis
      -- cancel one copy of `(μ (Y ⁻¹' {y}))⁻¹`, then clear the other
      have hinv0 : (μ (Y ⁻¹' {y}))⁻¹ ≠ 0 := ENNReal.inv_ne_zero.mpr (hne y)
      have hinvt : (μ (Y ⁻¹' {y}))⁻¹ ≠ ⊤ := ENNReal.inv_ne_top.mpr hy
      have hP : μ (X ⁻¹' s ∩ Y ⁻¹' {y} ∩ Z ⁻¹' t)
          = (μ (Y ⁻¹' {y}))⁻¹ * (μ (X ⁻¹' s ∩ Y ⁻¹' {y}) * μ (Y ⁻¹' {y} ∩ Z ⁻¹' t)) :=
        (ENNReal.mul_right_inj hinv0 hinvt).mp (by rw [hthis]; ring)
      rw [hP, ← mul_assoc, ENNReal.mul_inv_cancel hy (hne y), one_mul]
  · intro h y hmapy
    have hy : μ (Y ⁻¹' {y}) ≠ 0 := by
      rwa [Measure.map_apply hY (measurableSet_singleton y)] at hmapy
    rw [ProbabilityTheory.indepFun_iff_measure_inter_preimage_eq_mul]
    intro s t hs ht
    rw [cond_apply (hfib y), cond_apply (hfib y), cond_apply (hfib y),
      hswap y s t, hswapX y s]
    have hkey := h y s t hs ht
    rw [show ∀ a b c : ENNReal, a⁻¹ * b * (a⁻¹ * c) = a⁻¹ * (a⁻¹ * (b * c)) from
      fun a b c => by ring, ← hkey,
      ← mul_assoc (μ (Y ⁻¹' {y}))⁻¹ (μ (Y ⁻¹' {y})),
      ENNReal.inv_mul_cancel hy (hne y), one_mul]

omit [MeasurableSingletonClass T] [Countable T] [MeasurableSingletonClass U] [Countable U] in
/-- A measurable slice of a countable-valued variable splits over its point
masses: `μ (X ⁻¹' s ∩ A) = ∑' x ∈ s, μ (X ⁻¹' {x} ∩ A)`. This is what carries the
factorization from the printed point masses up to arbitrary measurable sets. -/
public theorem measure_preimage_inter_eq_tsum (hX : Measurable X)
    (s : Set S) {A : Set Ω} (hA : MeasurableSet A) :
    μ (X ⁻¹' s ∩ A) = ∑' x : s, μ (X ⁻¹' {(x : S)} ∩ A) := by
  have hcover : X ⁻¹' s ∩ A = ⋃ x : s, X ⁻¹' {(x : S)} ∩ A := by
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_iUnion, Set.mem_singleton_iff,
      Subtype.exists, exists_prop]
    exact ⟨fun h => ⟨X ω, h.1, rfl, h.2⟩, fun ⟨x, hxs, hx, hA⟩ => ⟨hx ▸ hxs, hA⟩⟩
  rw [hcover]
  refine measure_iUnion (fun a b hab => ?_) fun x =>
    (hX (measurableSet_singleton _)).inter hA
  refine Set.disjoint_left.mpr fun ω hωa hωb => hab (Subtype.ext ?_)
  exact (hωa.1 : X ω = (a : S)) ▸ (hωb.1 : X ω = (b : S)) ▸ rfl

/--
**(2.118), at the point masses (2.117) is written in.** The same equivalence as
`isMarkovChain_iff_measure_factorizes`, with the hypothesis weakened from every
measurable `s`, `t` to single `x`, `y`, `z`.

**What is and is not literally the printed expression.** (2.118) is the printed
*equivalence* — "`X → Y → Z` if and only if `X` and `Z` are conditionally
independent given `Y`" — and that is what this states, with `IsMarkovChain`
unfolding to the conditional independence on one side. (2.117) is the printed
*definition* of `X → Y → Z`, and the book writes it as the three-factor product
`p(x,y,z) = p(x) p(y|x) p(z|y)`. What appears here is `p(y)·p(x,y,z) =
p(x,y)·p(y,z)`, which is that product cleared of denominators: equivalent given
the marginals, and better behaved, since it needs no positivity side condition
and says the right thing on null fibres of `Y`. The three-factor form itself is
never written in Lean.

The `mpr` runs through `measure_preimage_inter_eq_tsum` twice, once in `X` and
once in `Z`, which is the countable additivity the set-level form assumes away.
-/
public theorem isMarkovChain_iff_measure_factorizes_singleton [IsProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) :
    IsMarkovChain X Y Z μ ↔
      ∀ (x : S) (y : T) (z : U),
        μ (Y ⁻¹' {y}) * μ (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z})
          = μ (X ⁻¹' {x} ∩ Y ⁻¹' {y}) * μ (Y ⁻¹' {y} ∩ Z ⁻¹' {z}) := by
  refine ⟨fun hM x y z => (isMarkovChain_iff_measure_factorizes hY).mp hM y {x} {z}
      (measurableSet_singleton x) (measurableSet_singleton z), fun h => ?_⟩
  refine (isMarkovChain_iff_measure_factorizes hY).mpr fun y s t _hs ht => ?_
  have hfibY : MeasurableSet (Y ⁻¹' {y}) := hY (measurableSet_singleton y)
  have hZt : MeasurableSet (Z ⁻¹' t) := hZ ht
  -- split the triple intersection in `X`, then each summand in `Z`
  have hXYZ : μ (X ⁻¹' s ∩ Y ⁻¹' {y} ∩ Z ⁻¹' t)
      = ∑' x : s, ∑' z : t, μ (X ⁻¹' {(x : S)} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {(z : U)}) := by
    rw [Set.inter_assoc, measure_preimage_inter_eq_tsum hX s (hfibY.inter hZt)]
    refine tsum_congr fun x => ?_
    have hcomm : X ⁻¹' {(x : S)} ∩ (Y ⁻¹' {y} ∩ Z ⁻¹' t)
        = Z ⁻¹' t ∩ (X ⁻¹' {(x : S)} ∩ Y ⁻¹' {y}) := by
      ext ω; simp only [Set.mem_inter_iff]; tauto
    rw [hcomm, measure_preimage_inter_eq_tsum hZ t
      ((hX (measurableSet_singleton _)).inter hfibY)]
    refine tsum_congr fun z => congrArg μ ?_
    ext ω; simp only [Set.mem_inter_iff]; tauto
  have hXY : μ (X ⁻¹' s ∩ Y ⁻¹' {y}) = ∑' x : s, μ (X ⁻¹' {(x : S)} ∩ Y ⁻¹' {y}) :=
    measure_preimage_inter_eq_tsum hX s hfibY
  have hYZ : μ (Y ⁻¹' {y} ∩ Z ⁻¹' t) = ∑' z : t, μ (Y ⁻¹' {y} ∩ Z ⁻¹' {(z : U)}) := by
    rw [Set.inter_comm, measure_preimage_inter_eq_tsum hZ t hfibY]
    exact tsum_congr fun z => congrArg μ (Set.inter_comm _ _)
  rw [hXYZ, hXY, hYZ, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left]
  exact tsum_congr fun z => h (x : S) y (z : U)

omit [Countable S] [Countable U] in
/--
**(2.117) at the printed point masses.** A Markov chain factorizes as
`p(y) · p(x, y, z) = p(x, y) · p(y, z)`, which is the book's
`p(x, y, z) = p(x) p(y|x) p(z|y)` cleared of denominators.

The direction of (2.118) that the atlas's definitional choice makes free —
`isMarkovChain_iff_measure_factorizes` at singletons. The converse from point
masses is `isMarkovChain_iff_measure_factorizes_singleton`, which is the same
equivalence with the hypothesis at the printed strength.
-/
public theorem measure_factorizes_of_isMarkovChain [IsProbabilityMeasure μ]
    (hY : Measurable Y) (h : IsMarkovChain X Y Z μ) (x : S) (y : T) (z : U) :
    μ (Y ⁻¹' {y}) * μ (X ⁻¹' {x} ∩ Y ⁻¹' {y} ∩ Z ⁻¹' {z})
      = μ (X ⁻¹' {x} ∩ Y ⁻¹' {y}) * μ (Y ⁻¹' {y} ∩ Z ⁻¹' {z}) :=
  (isMarkovChain_iff_measure_factorizes hY).mp h y {x} {z}
    (measurableSet_singleton x) (measurableSet_singleton z)

omit [Countable S] [Countable U] in
/--
The information-theoretic reading of the Markov hypothesis: `X → Y → Z` exactly
when `Y` already accounts for everything `Z` says about `X`.
-/
public theorem isMarkovChain_iff_condMutualInfo_eq_zero [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    IsMarkovChain X Y Z μ ↔ I[X : Z | Y ; μ] = 0 :=
  (condMutualInfo_eq_zero hX hZ).symm

/-- A Markov chain read backwards is a Markov chain: `X → Y → Z` gives `Z → Y → X`. -/
public theorem IsMarkovChain.symm [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (h : IsMarkovChain X Y Z μ) : IsMarkovChain Z Y X μ := by
  rw [isMarkovChain_iff_condMutualInfo_eq_zero hZ hX, condMutualInfo_comm hZ hX]
  exact (isMarkovChain_iff_condMutualInfo_eq_zero hX hZ).mp h

/-! ## The chain rule for mutual information

`I[X : ⟨Y, Z⟩] = I[X : Z] + I[X : Y | Z]`: what the pair `⟨Y, Z⟩` says about `X`
is what `Z` says, plus what `Y` adds once `Z` is known. Both argument orders are
given, because the data-processing argument needs to split the same quantity two
ways. -/

/-- Reordering a conditioning pair leaves conditional entropy unchanged. -/
public theorem condEntropy_pair_comm (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    H[X | ⟨Y, Z⟩ ; μ] = H[X | ⟨Z, Y⟩ ; μ] :=
  condEntropy_of_injective' μ hX (hZ.prodMk hY) Prod.swap Prod.swap_injective
    (by fun_prop)

/-- **Chain rule for mutual information.** `I[X : ⟨Y,Z⟩] = I[X : Z] + I[X : Y | Z]`. -/
public theorem mutualInfo_chain_rule (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : ⟨Y, Z⟩ ; μ] = I[X : Z ; μ] + I[X : Y | Z ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX (hY.prodMk hZ) μ,
    mutualInfo_eq_entropy_sub_condEntropy hX hZ μ,
    condMutualInfo_eq' hX hY hZ μ]
  ring

/-- The chain rule with the roles of the two components exchanged:
`I[X : ⟨Y,Z⟩] = I[X : Y] + I[X : Z | Y]`. -/
public theorem mutualInfo_chain_rule' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : ⟨Y, Z⟩ ; μ] = I[X : Y ; μ] + I[X : Z | Y ; μ] := by
  rw [mutualInfo_eq_entropy_sub_condEntropy hX (hY.prodMk hZ) μ,
    mutualInfo_eq_entropy_sub_condEntropy hX hY μ,
    condMutualInfo_eq' hX hZ hY μ,
    ← condEntropy_pair_comm μ hX hY hZ]
  ring

/-! ## The inequality -/

/--
**The exact identity behind data processing.** For *any* three variables, with no
Markov or functional hypothesis whatsoever,

`I[X : Y] - I[X : Z] = I[X : Y | Z] - I[X : Z | Y]`.

The data-processing inequality is the special case in which the second term
vanishes; the equality case is the special case in which the first does.
-/
public theorem mutualInfo_sub_eq (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z] :
    I[X : Y ; μ] - I[X : Z ; μ] = I[X : Y | Z ; μ] - I[X : Z | Y ; μ] := by
  have h := mutualInfo_chain_rule μ hX hY hZ
  have h' := mutualInfo_chain_rule' μ hX hY hZ
  linarith

/--
**Data-processing inequality** (Cover & Thomas, Theorem 2.8.1). If `X → Y → Z`
then `Z` says no more about `X` than `Y` does.
-/
public theorem mutualInfo_le_of_isMarkovChain (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (h : IsMarkovChain X Y Z μ) :
    I[X : Z ; μ] ≤ I[X : Y ; μ] := by
  have hzero : I[X : Z | Y ; μ] = 0 :=
    (isMarkovChain_iff_condMutualInfo_eq_zero hX hZ).mp h
  have hsub := mutualInfo_sub_eq μ hX hY hZ
  have hnn : 0 ≤ I[X : Y | Z ; μ] := condMutualInfo_nonneg hX hY
  linarith

/--
The dual reading. Reversing the chain gives `I[X : Z] ≤ I[Y : Z]`: the *source*
too can only lose information along the chain. This is a different conclusion
from `mutualInfo_le_of_isMarkovChain`, not a restatement; Cover & Thomas state
it at the end of Theorem 2.8.1's proof as "similarly, one can prove", and leave
it there.
-/
public theorem mutualInfo_le_of_isMarkovChain' (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (h : IsMarkovChain X Y Z μ) :
    I[X : Z ; μ] ≤ I[Y : Z ; μ] := by
  have := mutualInfo_le_of_isMarkovChain μ hZ hY hX (h.symm hX hZ)
  rwa [mutualInfo_comm hZ hX μ, mutualInfo_comm hZ hY μ] at this

/--
**Equality in data processing.** Under `X → Y → Z`, no information is lost at the
second step exactly when the chain also runs `X → Z → Y`. Cover & Thomas assert
this inside the proof of Theorem 2.8.1 without proving it.
-/
public theorem mutualInfo_eq_iff_isMarkovChain (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (h : IsMarkovChain X Y Z μ) :
    I[X : Z ; μ] = I[X : Y ; μ] ↔ IsMarkovChain X Z Y μ := by
  have hzero : I[X : Z | Y ; μ] = 0 :=
    (isMarkovChain_iff_condMutualInfo_eq_zero hX hZ).mp h
  have hsub := mutualInfo_sub_eq μ hX hY hZ
  rw [isMarkovChain_iff_condMutualInfo_eq_zero hX hY]
  constructor
  · intro heq; linarith
  · intro hzero'; linarith

/--
**Cover & Thomas's second corollary to Theorem 2.8.1** (unnumbered). Along a
Markov chain, conditioning on the downstream variable cannot increase
dependence: `I[X : Y | Z] ≤ I[X : Y]`. (In
general conditioning *can* increase mutual information; the Markov hypothesis is
what rules that out.)
-/
public theorem condMutualInfo_le_mutualInfo (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (h : IsMarkovChain X Y Z μ) :
    I[X : Y | Z ; μ] ≤ I[X : Y ; μ] := by
  have hzero : I[X : Z | Y ; μ] = 0 :=
    (isMarkovChain_iff_condMutualInfo_eq_zero hX hZ).mp h
  have hsub := mutualInfo_sub_eq μ hX hY hZ
  have hnn : 0 ≤ I[X : Z ; μ] := mutualInfo_nonneg hX hZ μ
  linarith

/--
The entropy form: along `X → Y → Z`, the downstream variable leaves at least as
much uncertainty about `X` as the upstream one. This is the shape that composes
with Fano's inequality.
-/
public theorem condEntropy_le_condEntropy_of_isMarkovChain (μ : Measure Ω)
    [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    [FiniteRange X] [FiniteRange Y] [FiniteRange Z]
    (h : IsMarkovChain X Y Z μ) :
    H[X | Y ; μ] ≤ H[X | Z ; μ] := by
  have hle := mutualInfo_le_of_isMarkovChain μ hX hY hZ h
  rw [mutualInfo_eq_entropy_sub_condEntropy hX hY μ,
    mutualInfo_eq_entropy_sub_condEntropy hX hZ μ] at hle
  linarith

/-! ## The functional case is an instance -/

/--
Post-processing is a Markov chain. Whatever `X` is, `X → Y → g ∘ Y` holds: a
function of `Y` is conditionally independent of everything given `Y`.

This is what makes the Markov statement strictly stronger than the functional
one. No converse holds — a Markov chain need not be functional.
-/
public theorem isMarkovChain_comp (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) {g : T → U} (hg : Measurable g)
    [FiniteRange X] [FiniteRange Y] :
    IsMarkovChain X Y (g ∘ Y) μ := by
  rw [isMarkovChain_iff_condMutualInfo_eq_zero hX (hg.comp hY),
    condMutualInfo_eq' hX (hg.comp hY) hY μ]
  have hinj : Injective (fun t : T => (g t, t)) := fun _ _ h => congrArg Prod.snd h
  have : H[X | ⟨g ∘ Y, Y⟩ ; μ] = H[X | Y ; μ] :=
    condEntropy_of_injective' μ hX hY (fun t => (g t, t)) hinj (by fun_prop)
  rw [this]
  ring

/--
**Cover & Thomas's first corollary to Theorem 2.8.1** (unnumbered), obtained by
instantiating the Markov statement rather than by a separate argument:
processing `Y` through any measurable `g` cannot increase what it says about
`X`.

PFR proves this directly as `mutual_comp_le`; it is re-derived here to exhibit
that the Markov form subsumes it.
-/
public theorem mutualInfo_comp_le (μ : Measure Ω) [IsZeroOrProbabilityMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) {g : T → U} (hg : Measurable g)
    [FiniteRange X] [FiniteRange Y] :
    I[X : g ∘ Y ; μ] ≤ I[X : Y ; μ] :=
  mutualInfo_le_of_isMarkovChain μ hX hY (hg.comp hY) (isMarkovChain_comp μ hX hY hg)

end AISafetyAtlas.InformationTheory
