module

public import AISafetyAtlas.Preference.Reasonable
public import Mathlib.Data.EReal.Basic

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
the statement here is the more general of the two. Since complexities are
natural numbers the minimum over a nonempty set is in fact always attained, and
`AISafetyAtlas.Preference.amongLowest_iff_min` proves the two readings equal for
an arbitrary set; `amongLowestCompatible_iff` identifies this definition with
that general one at the compatible set.

The source's `F`-complexity itself is `fComplexity` (a supremum in `EReal`, for
any complexity), `fComplexity_le_iff_nat` shows `ReasonableForF` is exactly
"`F`-complexity at most `c`", and `fComplexity_nonneg` is footnote 10.

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

/-! ## The `F`-complexity of a language -/

/--
**The `F`-complexity of a language** (Armstrong and Mindermann, §5.1.2,
`am-f-complexity`, PDF p. 6): `max_{(p,R), Fᵢ ∈ F} K_L(Fᵢ(p,R)) − K_L(p,R)`, for
any complexity `K` on pairs, with no reasonableness assumed.

Print's `max` is rendered as a supremum in `EReal`: over infinitely many pairs
the differences need not be bounded above, and when they are the supremum need
not be attained, so a `max` would presuppose what print does not prove. When it
is attained the two agree. `fComplexity_le_iff_nat` is print's "`L` is
`c`-reasonable for `F`" and `fComplexity_nonneg` is print's footnote 10.
-/
@[expose] public noncomputable def fComplexity (K : Pair S A → ℕ) : EReal :=
  ⨆ (i : Fin 4) (x : Pair S A), ((((K (Fmap i x) : ℝ) - K x : ℝ)) : EReal)

/-- The `F`-complexity is at most a real `c` exactly when every `Fᵢ` raises
the complexity of every pair by at most `c`. -/
public theorem fComplexity_le_iff (K : Pair S A → ℕ) (c : ℝ) :
    fComplexity K ≤ (c : EReal) ↔
      ∀ (i : Fin 4) (x : Pair S A), (K (Fmap i x) : ℝ) ≤ K x + c := by
  unfold fComplexity
  simp only [iSup_le_iff, EReal.coe_le_coe_iff]
  refine forall_congr' fun i => forall_congr' fun x => ?_
  constructor <;> intro h <;> linarith

/-- **`c`-reasonable for `F`, as print defines it**: the `F`-complexity is at
most `c`. At a natural constant this is exactly the field
`ReasonableForF.F_complexity_le`, so `ReasonableForF` is print's definition. -/
public theorem fComplexity_le_iff_nat (K : Pair S A → ℕ) (c : ℕ) :
    fComplexity K ≤ ((c : ℝ) : EReal) ↔
      ∀ (i : Fin 4) (x : Pair S A), K (Fmap i x) ≤ K x + c := by
  rw [fComplexity_le_iff]
  refine forall_congr' fun i => forall_congr' fun x => ?_
  exact_mod_cast Iff.rfl

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

/-- Compatibility, as in the source: the pair evaluates to the policy.

`AISafetyAtlas.Preference.ReasonableLanguage.Compatible` is this same definition,
character for character and with the same type, in the other language
structure's namespace. `scripts/report_predicate_duplicates.py` surfaced the
pair; the cross-reference is here so neither can be read as the only one. -/
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

/-- `AmongLowestCompatible` is the general `AmongLowest` (`am-lowest`, for an
arbitrary set) at the set of pairs compatible with `π`, with the language's
complexity and constant. -/
public theorem amongLowestCompatible_iff (π : Policy S A) (x : Pair S A) :
    L.AmongLowestCompatible π x ↔ AmongLowest L.KPair L.c {y | Compatible y π} x := by
  unfold AmongLowestCompatible AmongLowest
  simp only [Set.mem_ofPred_eq]
  refine and_congr Iff.rfl (forall_congr' fun y => imp_congr_right fun _ => ?_)
  exact_mod_cast Iff.rfl

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

end ReasonableForF

/-- **Footnote 10 of the source**: the `F`-complexity of any language is
non-negative, because `F₄` is an involution -- of a pair and its negation, one
is at least as complex as the other, and `F₄` maps it to the other. -/
public theorem fComplexity_nonneg
    (K : Pair S A → ℕ) : 0 ≤ fComplexity K := by
  obtain ⟨x⟩ := (inferInstance : Nonempty (Pair S A))
  unfold fComplexity
  by_cases h : K x ≤ K (F₄ x)
  · refine le_iSup₂_of_le (3 : Fin 4) x ?_
    rw [show (Fmap 3 : Pair S A → Pair S A) = F₄ from rfl, ← EReal.coe_zero,
      EReal.coe_le_coe_iff]
    have : (K x : ℝ) ≤ K (F₄ x) := by exact_mod_cast h
    linarith
  · refine le_iSup₂_of_le (3 : Fin 4) (F₄ x) ?_
    rw [show (Fmap 3 : Pair S A → Pair S A) = F₄ from rfl, ReasonableForF.F₄_F₄, ← EReal.coe_zero,
      EReal.coe_le_coe_iff]
    have : (K (F₄ x) : ℝ) ≤ K x := by exact_mod_cast (le_of_not_ge h)
    linarith

namespace ReasonableForF

variable (L : ReasonableForF S A)

/-- A `c`-reasonable language for `F` has `F`-complexity at most `c`, in the
sense of `fComplexity`. -/
public theorem fComplexity_le : fComplexity L.KPair ≤ ((L.c : ℝ) : EReal) :=
  (fComplexity_le_iff_nat L.KPair L.c).mpr L.F_complexity_le

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

/-- **Proposition 8, in print's vocabulary**: a compatible pair's negation is
compatible with the same policy, and the two are *of comparable complexity*
(`ComparableComplexity`, `am-comparable`) at the language's constant. A
corollary of `proposition_eight`, which is unchanged. -/
public theorem proposition_eight_comparable {x : Pair S A} {π : Policy S A}
    (h : Compatible x π) :
    Compatible (F₄ x) π ∧ ComparableComplexity L.KPair L.c x (F₄ x) := by
  obtain ⟨hc, h1, h2⟩ := L.proposition_eight h
  exact ⟨hc, (comparableComplexity_iff _ _ _ _).mpr ⟨h2, h1⟩⟩

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

/-! ## Proposition 7 at any complexity measure (appendix A, Proposition 10)

`ReasonableForF` fixes a natural-number-valued complexity and a natural constant.
Appendix A's Proposition 10 asks the same question of the time-bounded measures
`Kt_L(p, R) = min l(α_p) + l(α_R) + log t(α_p(α_R))` and `KT_L`, the first of
which is real-valued, and print's argument for the indifferent pair uses only
that `F₁` costs little under the measure. The declarations below take the
complexity `K` and the constant `c` as explicit parameters in any type with an
addition and an order, and take each composite's bound separately, so the
indifferent pair needs only the `F₁` bound. -/

/-- **Amongst the lowest-complexity compatible pairs, for any complexity
measure** (Armstrong and Mindermann, §5.1.3, `am-lowest`, read at an arbitrary
measure as appendix A's Proposition 10 requires): `x` is compatible with `π`
and no compatible pair beats it by more than `c`. At `K` natural-valued this is
`ReasonableForF.AmongLowestCompatible` (`ReasonableForF.amongLowestCompatible_iff_amongLowestFor`). -/
@[expose] public def AmongLowestFor {α : Type*} [Add α] [LE α] (K : Pair S A → α) (c : α)
    (π : Policy S A) (x : Pair S A) : Prop :=
  ReasonableForF.Compatible x π ∧
    ∀ y : Pair S A, ReasonableForF.Compatible y π → K x ≤ K y + c

omit [Fintype A] [Nonempty A] [DecidableEq A] in
/-- **Proposition 10, first clause, from the `F₁` bound alone** (Armstrong and
Mindermann, appendix A, `amapp-prop10`, PDF p. 1: *"The results of Proposition 7
still apply to `(p_π̇, 0)` if `Kt_L` or `KT_L` are used instead of `K_L`"*). For
any complexity measure under which `F₁` raises complexity by at most `c`, the
indifferent pair `(p_π, 0)` is amongst the lowest-complexity pairs compatible
with `π`. No bound on `F₂`, `F₃` or `F₄` is asked for. -/
public theorem indifferent_amongLowestFor {α : Type*} [Add α] [LE α]
    (K : Pair S A → α) (c : α) (h₁ : ∀ x : Pair S A, K (F₁ x) ≤ K x + c)
    (π : Policy S A) : AmongLowestFor K c π (op1 (op5 π)) := by
  refine ⟨ReasonableForF.compatible_indifferent π, fun y hy => ?_⟩
  have hb := h₁ y
  rwa [ReasonableForF.F₁_of_compatible hy] at hb

/-- **Proposition 10, second clause, greedy pair, from the `F₂` bound alone**:
under any measure where `F₂` raises complexity by at most `c`, `(p_g, R_π)` is
amongst the lowest. Print's second clause supplies that bound for planners
taking algorithms; this lemma is what it is fed into. -/
public theorem greedy_amongLowestFor {α : Type*} [Add α] [LE α]
    (K : Pair S A → α) (c : α) (h₂ : ∀ x : Pair S A, K (F₂ x) ≤ K x + c)
    (π : Policy S A) : AmongLowestFor K c π (op2 (op6 π)) := by
  refine ⟨op3_op2_op6 π, fun y hy => ?_⟩
  have hb := h₂ y
  rwa [ReasonableForF.F₂_of_compatible hy] at hb

/-- **Proposition 10, second clause, anti-rational pair, from the `F₃` bound
alone.** -/
public theorem antirational_amongLowestFor {α : Type*} [Add α] [LE α]
    (K : Pair S A → α) (c : α) (h₃ : ∀ x : Pair S A, K (F₃ x) ≤ K x + c)
    (π : Policy S A) : AmongLowestFor K c π (op4 (op2 (op6 π))) := by
  refine ⟨op3_op4_op2_op6 π, fun y hy => ?_⟩
  have hb := h₃ y
  rwa [ReasonableForF.F₃_of_compatible hy] at hb

/-- **Proposition 7 at any complexity measure** (Armstrong and Mindermann,
§5.1.3, `am-prop7`, with the measure widened as appendix A's Proposition 10
needs): for any `K` valued in a type with addition and order, real-valued
`Kt_L` included, and any `c` such that every composite raises `K` by at most
`c`, the three degenerate pairs are amongst the lowest-complexity pairs
compatible with `π`. `ReasonableForF.proposition_seven` is the natural-valued
case, through `ReasonableForF.amongLowestCompatible_iff_amongLowestFor`. -/
public theorem proposition_seven_of_bounds {α : Type*} [Add α] [LE α]
    (K : Pair S A → α) (c : α) (hF : ∀ (i : Fin 4) (x : Pair S A), K (Fmap i x) ≤ K x + c)
    (π : Policy S A) :
    AmongLowestFor K c π (op1 (op5 π)) ∧ AmongLowestFor K c π (op2 (op6 π)) ∧
      AmongLowestFor K c π (op4 (op2 (op6 π))) :=
  ⟨indifferent_amongLowestFor K c (hF 0) π, greedy_amongLowestFor K c (hF 1) π,
    antirational_amongLowestFor K c (hF 2) π⟩

namespace ReasonableForF

variable (L : ReasonableForF S A)

/-- The language structure's predicate is `AmongLowestFor` at its own
natural-valued complexity and constant. -/
public theorem amongLowestCompatible_iff_amongLowestFor (π : Policy S A) (x : Pair S A) :
    L.AmongLowestCompatible π x ↔ AmongLowestFor L.KPair L.c π x := Iff.rfl

end ReasonableForF

/-! ## Conjecture 9 at the printed quantifier

`ReasonableForF.NotAmongLowestCompatible` is the conjecture's conclusion for one
pair. The conjecture itself quantifies: for every reasonable language, every
human policy and every reasonable compatible pair. Print leaves "reasonable
language", "human policy" and "reasonable pair" informal (§5.1.2: a `c` "that
we feel is intuitively low enough"; §6: "compatible with human judgements about
rationality"), so they enter as predicates the reader supplies. -/

/-- **Conjecture 9 (informal complexity proposition)**, as a statement
(Armstrong and Mindermann, §6, `am-conj9`): for every language satisfying
`ReasonableLanguage`, every policy satisfying `Human` and every pair satisfying
`Reasonable` that is compatible with that policy, the pair is not close to
minimal amongst the compatible pairs. A statement, not an assumption: nothing in
the atlas asserts or proves it, and the source leaves it open. -/
@[expose] public def ConjectureNine (ReasonableLanguage : ReasonableForF S A → Prop)
    (Human : Policy S A → Prop) (Reasonable : Pair S A → Prop) : Prop :=
  ∀ L : ReasonableForF S A, ReasonableLanguage L → ∀ π : Policy S A, Human π →
    ∀ x : Pair S A, Reasonable x → ReasonableForF.Compatible x π →
      L.NotAmongLowestCompatible π x

/-- **The informal Theorem 2 from Conjecture 9**: where the conjecture holds,
each degenerate pair is strictly simpler than every reasonable compatible pair,
through `ReasonableForF.theorem_two_conditional`. -/
public theorem ConjectureNine.theorem_two
    {ReasonableLanguage : ReasonableForF S A → Prop} {Human : Policy S A → Prop}
    {Reasonable : Pair S A → Prop} (h : ConjectureNine ReasonableLanguage Human Reasonable)
    {L : ReasonableForF S A} (hL : ReasonableLanguage L) {π : Policy S A} (hπ : Human π)
    {x : Pair S A} (hx : Reasonable x) (hc : ReasonableForF.Compatible x π) :
    L.KPair (op1 (op5 π)) < L.KPair x ∧
      L.KPair (op2 (op6 π)) < L.KPair x ∧
      L.KPair (op4 (op2 (op6 π))) < L.KPair x :=
  L.theorem_two_conditional π x (h L hL π hπ x hx hc)

/-- **The reasonableness premise carries weight**: if `Reasonable` admits the
indifferent pair `(p_π, 0)` of some human policy, at some reasonable language,
Conjecture 9 fails, by Proposition 7 (`ReasonableForF.indifferent_amongLowest`). -/
public theorem not_conjectureNine_of_indifferent
    {ReasonableLanguage : ReasonableForF S A → Prop} {Human : Policy S A → Prop}
    {Reasonable : Pair S A → Prop} {L : ReasonableForF S A} (hL : ReasonableLanguage L)
    {π : Policy S A} (hπ : Human π) (hind : Reasonable (op1 (op5 π))) :
    ¬ ConjectureNine ReasonableLanguage Human Reasonable := fun h =>
  (L.notAmongLowest_iff π _ (ReasonableForF.compatible_indifferent π)).1
    (h L hL π hπ _ hind (ReasonableForF.compatible_indifferent π)) (L.indifferent_amongLowest π)

end AISafetyAtlas.Preference.Source
