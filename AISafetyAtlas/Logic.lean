module

public import AISafetyAtlas.Upstream.KolmogorovMathlib.Complexity.Chaitin
public import Foundation.FirstOrder.Incompleteness.First
public import Foundation.FirstOrder.Incompleteness.Second
public import Foundation.FirstOrder.Incompleteness.Tarski
public import Foundation.FirstOrder.Incompleteness.Löb

/-!
# Logic limits

Thin wrappers over upstream incompleteness / undefinability. No AI-safety bridge.

## Primary surface

| Role | Declaration | Survey |
|---|---|---|
| **Law** | `chaitin_incompleteness` / `chaitin_bound` | BY-015 |
| **Law** | `godel_first_incompleteness` | BY-013 |
| **Related companion** | `godel_second_incompleteness` | BY-013 companion |
| **Law** | `tarski_undefinability` | BY-016 |
| **Law** | `loeb` | BY-027 |

## Sources

* Chaitin: vendored KolmogorovMathlib @ `005ac4c…`.
* Gödel / Tarski / Löb: FormalizedFormalLogic/Foundation @ `b47cf44…`.

See `docs/guide/logic-incompleteness.md`.
-/

namespace AISafetyAtlas.Logic

/--
Chaitin's incompleteness theorem for plain Kolmogorov complexity: in any sound,
computably enumerable formal system that can express bounds `K(x) > L`, there
exist true unprovable lower bounds.

Source: `Kolmogorov.FormalSystem.chaitinIncompleteness`.
-/
public theorem chaitin_incompleteness
    {U : Kolmogorov.Map}
    (F : Kolmogorov.FormalSystem U)
    (hU : Kolmogorov.isOptimalConditional U) :
    ∃ x L : ℕ,
      (L : ENat) < Kolmogorov.plainKNat U x ∧
      ¬ F.provable (F.exprKGt x L) :=
  F.chaitinIncompleteness hU

/--
Chaitin's bound: every such system has a constant beyond which it cannot prove
true complexity lower bounds.

Source: `Kolmogorov.FormalSystem.chaitinBound`.
-/
public theorem chaitin_bound
    {U : Kolmogorov.Map}
    (F : Kolmogorov.FormalSystem U)
    (hU : Kolmogorov.isOptimalConditional U) :
    ∃ c : ℕ, ∀ i x L, F.enumBounds i = some (x, L) → L ≤ c :=
  F.chaitinBound hU

open LO LO.FirstOrder LO.FirstOrder.Arithmetic in
/--
Gödel's **first** incompleteness theorem for a concrete arithmetic theory:
any `Δ₁`-definable, `𝚺₁`-sound theory `T` interpreting `𝗥₀` has a sentence that
is true in the standard model `ℕ` yet unprovable in `T`.

Source: `LO.FirstOrder.Arithmetic.exists_true_but_unprovable_sentence`
(FormalizedFormalLogic/Foundation).
-/
public theorem godel_first_incompleteness
    (T : ArithmeticTheory) [T.Δ₁] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ :=
  LO.FirstOrder.Arithmetic.exists_true_but_unprovable_sentence T

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment in
/--
Gödel's **second** incompleteness theorem for a concrete arithmetic theory:
any consistent, `Δ₁`-definable theory `T` interpreting `𝗜𝚺₁` cannot prove its
own consistency statement.

Source: `LO.FirstOrder.Arithmetic.consistent_unprovable`
(FormalizedFormalLogic/Foundation).
-/
public theorem godel_second_incompleteness
    (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T] :
    T ⊬ ↑T.consistent :=
  LO.FirstOrder.Arithmetic.consistent_unprovable T

open LO LO.FirstOrder LO.FirstOrder.Arithmetic in
/--
Tarski's undefinability of truth: there is no arithmetic formula \(\tau(x)\) such
that for every sentence \(\sigma\), \(\mathbb{N} \models \sigma\) if and only if
\(\mathbb{N} \models \tau[\ulcorner\sigma\urcorner]\).

Source: `LO.FirstOrder.Arithmetic.undefinability_of_truth`
(FormalizedFormalLogic/Foundation).
-/
public theorem tarski_undefinability :
    ¬∃ τ : ArithmeticSemisentence 1,
      ∀ σ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ σ ↔ ℕ↓[ℒₒᵣ] ⊧ τ/[⌜σ⌝] :=
  LO.FirstOrder.Arithmetic.undefinability_of_truth

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment in
/--
Löb's theorem: if a sufficiently strong arithmetic theory `T` proves
\(\mathrm{Prov}_T(\sigma) \to \sigma\), then `T` already proves \(\sigma\).

This is the classical Hilbert–Bernays–Löb form used for “self-verification”
limits; the survey's informal “cannot prove its own soundness” reading is a
consequence of this schema under standard hypotheses, not a separate theorem.

Source: `LO.FirstOrder.Arithmetic.löb_theorem`
(FormalizedFormalLogic/Foundation).
-/
public theorem loeb
    {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] {σ : ArithmeticSentence} :
    T ⊢ Bootstrapping.provabilityPred T σ 🡒 σ → T ⊢ σ :=
  LO.FirstOrder.Arithmetic.löb_theorem (T := T) (σ := σ)

end AISafetyAtlas.Logic
