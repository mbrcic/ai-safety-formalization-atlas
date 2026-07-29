module

public import AISafetyAtlas.Preference.Reasonable

/-!
# Propositions 7 and 8 in the source's own parameterization

## Statement intent

- **Objects.** The source's composite operations
  `F = {F₁ = f₁ ∘ f₅ ∘ f₃, F₂ = f₂ ∘ f₆ ∘ f₃, F₃ = f₄ ∘ f₂ ∘ f₆ ∘ f₃, F₄ = f₄}`
  of §5.1.2, and a complexity assignment on planner/reward pairs.
- **Assumptions.** The source defines the *`F`-complexity* of a language `L` as
  `max_{(p,R), Fᵢ ∈ F} K_L(Fᵢ(p,R)) − K_L(p,R)`, and calls `L` a
  *`c`-reasonable language for `F`* when that quantity is at most `c`.
  `ReasonableForF` records exactly that, as a single bound indexed by `Fin 4`.
- **Quantifier order.** The constant is fixed by the language, before any pair
  or policy is chosen.
- **Conclusion.** Proposition 7 at distance **`c`**, and Proposition 8 in both
  directions at distance `c`.

## Why this module exists

`AISafetyAtlas.Preference.Reasonable` states the same two propositions under a
*reparameterized* interface: it assumes separate evaluation and construction
bounds mediated by a complexity on policies, and therefore concludes `2 * c`.
That is a valid conditional variation but is not the source's definition.

The difference is structural, not a proof artifact. Each `Fᵢ` maps a pair to a
pair, so a bound on `Fᵢ` never passes through the complexity of a policy. There
is consequently no `KPolicy` field here at all, and the constant does not
double. Both modules are kept: this one for source parity, the other because
`AISafetyAtlas.Preference.Complexity` instantiates its evaluation bound
concretely.

## Difference from the source

The source formalizes "amongst the lowest complexity in `S`" using
`min_{(p',R') ∈ S} K_L(p',R')`, an attained minimum, and its proof begins "pick
`(p, R)` to be the simplest pair compatible with `π̇`". `AmongLowestCompatible`
instead quantifies universally over compatible pairs. That avoids assuming the
minimum is attained and is implied by the source's reading whenever it is, so
the statement here is the more general of the two.

## Explicit non-claims

- **Not** a construction of any `c`-reasonable language, nor a proof that a
  nontrivial one exists. The source argues for existence informally. The only
  inhabitant exhibited in the atlas is degenerate; see the non-claims in
  `AISafetyAtlas.Preference.Reasonable`.
- **Not** the source's Conjecture 9, which is the missing half that would make
  the informal Theorem 2 bite.
- **Not** a claim that the *intended* pair has high complexity.

Survey row: **BY-011**. No AI-system bridge is asserted.
-/

namespace AISafetyAtlas.Preference.Source

open AISafetyAtlas.Preference

variable {S A : Type*} [Fintype A] [Nonempty A] [DecidableEq A]

/-! ## The composite operations -/

/-- `F₁ = f₁ ∘ f₅ ∘ f₃`: evaluate the pair, then build the indifferent pair. -/
@[expose] public def F₁ (x : Pair S A) : Pair S A := op1 (op5 (op3 x))

/-- `F₂ = f₂ ∘ f₆ ∘ f₃`: evaluate the pair, then build the greedy pair. -/
@[expose] public noncomputable def F₂ (x : Pair S A) : Pair S A := op2 (op6 (op3 x))

/-- `F₃ = f₄ ∘ f₂ ∘ f₆ ∘ f₃`: as `F₂`, then negate. -/
@[expose] public noncomputable def F₃ (x : Pair S A) : Pair S A :=
  op4 (op2 (op6 (op3 x)))

/-- `F₄ = f₄`: the anti-rational negation, included so that `F`-complexity is
non-negative, as the source's footnote observes. -/
@[expose] public def F₄ (x : Pair S A) : Pair S A := op4 x

/-- The family `F` as a single indexed operation, so that the source's
`max` over `Fᵢ ∈ F` becomes one uniform bound. -/
@[expose] public noncomputable def Fmap : Fin 4 → Pair S A → Pair S A
  | 0 => F₁
  | 1 => F₂
  | 2 => F₃
  | 3 => F₄

/-! ## `c`-reasonable languages for `F` -/

/--
A complexity assignment on pairs whose `F`-complexity is at most `c`.

This is the source's definition: no policy complexity appears, because every
`Fᵢ` maps a pair to a pair.
-/
public structure ReasonableForF (S A : Type*)
    [Fintype A] [Nonempty A] [DecidableEq A] where
  /-- Complexity of a planner/reward pair. -/
  KPair : Pair S A → ℕ
  /-- The bound on the `F`-complexity. -/
  c : ℕ
  /-- The `F`-complexity of the language is at most `c`. -/
  F_complexity_le : ∀ (i : Fin 4) (x : Pair S A), KPair (Fmap i x) ≤ KPair x + c

namespace ReasonableForF

variable (L : ReasonableForF S A)

/-- Compatibility, as in the source: the pair evaluates to the policy. -/
@[expose] public def Compatible (x : Pair S A) (π : Policy S A) : Prop := op3 x = π

omit [Fintype A] [Nonempty A] [DecidableEq A] in
/-- This is the same relation as `ReasonableLanguage.Compatible`. -/
public theorem compatible_iff (x : Pair S A) (π : Policy S A) :
    Compatible x π ↔ ReasonableLanguage.Compatible x π := Iff.rfl

/--
`x` is amongst the lowest-complexity pairs compatible with `π`.

Stated without assuming an attained minimum: `x` is compatible, and no
compatible pair beats it by more than `c`.
-/
@[expose] public def AmongLowestCompatible (π : Policy S A) (x : Pair S A) : Prop :=
  Compatible x π ∧ ∀ y : Pair S A, Compatible y π → L.KPair x ≤ L.KPair y + L.c

/-! ### The composites send any compatible pair to the degenerate pairs -/

omit [Fintype A] [Nonempty A] [DecidableEq A] in
/-- `F₁(p, R) = (p_π, 0)` for any `π`-compatible pair. -/
public theorem F₁_of_compatible {x : Pair S A} {π : Policy S A}
    (h : Compatible x π) : F₁ x = op1 (op5 π) := by
  unfold F₁
  rw [show op3 x = π from h]

/-- `F₂(p, R) = (p_g, R_π)` for any `π`-compatible pair. -/
public theorem F₂_of_compatible {x : Pair S A} {π : Policy S A}
    (h : Compatible x π) : F₂ x = op2 (op6 π) := by
  unfold F₂
  rw [show op3 x = π from h]

/-- `F₃(p, R) = (-p_g, -R_π)` for any `π`-compatible pair. -/
public theorem F₃_of_compatible {x : Pair S A} {π : Policy S A}
    (h : Compatible x π) : F₃ x = op4 (op2 (op6 π)) := by
  unfold F₃
  rw [show op3 x = π from h]

/-! ### Proposition 7, at distance `c` -/

omit [Fintype A] [Nonempty A] [DecidableEq A] in
/-- The set of pairs compatible with `π` is never empty, so the universal
quantifier in `AmongLowestCompatible` is not vacuous. -/
public theorem compatible_indifferent (π : Policy S A) :
    Compatible (op1 (op5 π)) π := op3_op1_op5 π

/-- **Proposition 7, first pair.** `(p_π, 0)` is amongst the lowest-complexity
pairs compatible with `π`, at distance `c`. -/
public theorem indifferent_amongLowest (π : Policy S A) :
    L.AmongLowestCompatible π (op1 (op5 π)) := by
  refine ⟨compatible_indifferent π, fun y hy => ?_⟩
  have hb := L.F_complexity_le 0 y
  rw [show (Fmap 0 : Pair S A → Pair S A) = F₁ from rfl, F₁_of_compatible hy] at hb
  exact hb

/-- **Proposition 7, second pair.** `(p_g, R_π)` is amongst the lowest, at `c`. -/
public theorem greedy_amongLowest (π : Policy S A) :
    L.AmongLowestCompatible π (op2 (op6 π)) := by
  refine ⟨op3_op2_op6 π, fun y hy => ?_⟩
  have hb := L.F_complexity_le 1 y
  rw [show (Fmap 1 : Pair S A → Pair S A) = F₂ from rfl, F₂_of_compatible hy] at hb
  exact hb

/-- **Proposition 7, third pair.** `(-p_g, -R_π)` is amongst the lowest, at `c`. -/
public theorem antirational_amongLowest (π : Policy S A) :
    L.AmongLowestCompatible π (op4 (op2 (op6 π))) := by
  refine ⟨op3_op4_op2_op6 π, fun y hy => ?_⟩
  have hb := L.F_complexity_le 2 y
  rw [show (Fmap 2 : Pair S A → Pair S A) = F₃ from rfl, F₃_of_compatible hy] at hb
  exact hb

/--
**Proposition 7.**

If `L` is a `c`-reasonable language for `F`, the three degenerate
planner/reward pairs are amongst the pairs of lowest complexity among the pairs
compatible with `π`.

The distance is `c`, matching the source. Contrast
`AISafetyAtlas.Preference.ReasonableLanguage.proposition_seven`, whose
reparameterized hypotheses give `2 * c`.
-/
public theorem proposition_seven (π : Policy S A) :
    L.AmongLowestCompatible π (op1 (op5 π)) ∧
      L.AmongLowestCompatible π (op2 (op6 π)) ∧
      L.AmongLowestCompatible π (op4 (op2 (op6 π))) :=
  ⟨L.indifferent_amongLowest π, L.greedy_amongLowest π, L.antirational_amongLowest π⟩

/-! ### Proposition 8, both directions at `c` -/

omit [Fintype A] [Nonempty A] [DecidableEq A] in
/-- `F₄` is an involution, the source's footnote-10 observation. -/
public theorem F₄_F₄ (x : Pair S A) : F₄ (F₄ x) = x := op4_op4 x

/--
**Proposition 8.**

A compatible pair's negation is compatible with the same policy, and the two
are of comparable complexity: each is within `c` of the other.

So complexity does not distinguish a reasonable human reward function from its
negative. Unlike Proposition 7 this applies to *every* compatible pair,
including the intended one.
-/
public theorem proposition_eight {x : Pair S A} {π : Policy S A}
    (h : Compatible x π) :
    Compatible (F₄ x) π ∧
      L.KPair (F₄ x) ≤ L.KPair x + L.c ∧
      L.KPair x ≤ L.KPair (F₄ x) + L.c := by
  refine ⟨?_, ?_, ?_⟩
  · show op3 (op4 x) = π
    rw [op3_op4]
    exact h
  · exact L.F_complexity_le 3 x
  · have hb := L.F_complexity_le 3 (F₄ x)
    rw [show (Fmap 3 : Pair S A → Pair S A) = F₄ from rfl, F₄_F₄] at hb
    exact hb

/-! ### Conjecture 9 and the conditional form of the informal Theorem 2 -/

/--
**Conjecture 9 (informal complexity proposition), as a predicate.**

The source's conjecture is that for a human policy `π` and a *reasonable*
compatible pair `x`, the complexity of `x` "is not close to minimal amongst the
pairs compatible with `π`".

Negating `AmongLowestCompatible` gives exactly that: some compatible pair beats
`x` by more than `c`.

This is a **definition, never an assumption**. Nothing in the atlas asserts it,
and no axiom or structure field carries it. The source itself argues for it
qualitatively and does not prove it. It is stated here only so that the
conditional theorem below can be recorded honestly.
-/
@[expose] public def NotAmongLowestCompatible (π : Policy S A) (x : Pair S A) : Prop :=
  Compatible x π ∧ ∃ y : Pair S A, Compatible y π ∧ L.KPair y + L.c < L.KPair x

/-- Negating `AmongLowestCompatible` is exactly `NotAmongLowestCompatible`, for
a compatible pair. -/
public theorem notAmongLowest_iff (π : Policy S A) (x : Pair S A)
    (hx : Compatible x π) :
    L.NotAmongLowestCompatible π x ↔ ¬ L.AmongLowestCompatible π x := by
  constructor
  · rintro ⟨-, y, hy, hlt⟩ ⟨-, hmin⟩
    exact absurd (hmin y hy) (by omega)
  · intro h
    refine ⟨hx, ?_⟩
    by_contra hno
    refine h ⟨hx, fun y hy => ?_⟩
    by_contra hgt
    exact hno ⟨y, hy, by omega⟩

/--
**The informal Theorem 2, conditionally.**

*If* Conjecture 9 holds for an intended compatible pair, then each of the three
degenerate pairs is **strictly** simpler than it. A simplicity prior would
therefore rank a degenerate decomposition above the intended one.

The hypothesis is Conjecture 9 as a hypothesis, not as an assumed fact: this
theorem says only what follows from it. The source leaves it open, and so does
the atlas.
-/
public theorem theorem_two_conditional (π : Policy S A) (intended : Pair S A)
    (h9 : L.NotAmongLowestCompatible π intended) :
    L.KPair (op1 (op5 π)) < L.KPair intended ∧
      L.KPair (op2 (op6 π)) < L.KPair intended ∧
      L.KPair (op4 (op2 (op6 π))) < L.KPair intended := by
  obtain ⟨-, y, hy, hlt⟩ := h9
  refine ⟨?_, ?_, ?_⟩
  · have := (L.indifferent_amongLowest π).2 y hy
    omega
  · have := (L.greedy_amongLowest π).2 y hy
    omega
  · have := (L.antirational_amongLowest π).2 y hy
    omega

end ReasonableForF

end AISafetyAtlas.Preference.Source
