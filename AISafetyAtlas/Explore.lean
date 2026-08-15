module

public import AISafetyAtlas.Inference.Search
public import Mathlib.Tactic
public import Plausible

/-!
# Exploration workbench — tactics for discovery, never for shipping

The library modules import narrowly on purpose: `Inference/Device.lean` reaches
for two Mathlib modules and nothing else, which is what keeps the impossibility
core cheap to build and cheap to audit. The cost is that the discovery tactics —
`plausible`, `exact?`, `#leansearch`, the full `Mathlib.Tactic` surface — are not
in scope where the work happens.

This module is the other side of that trade. It imports everything, is **not** on
the public root import, and is built by CI as an explicit target so it cannot rot.
Nothing here is a dependency of anything the facade exposes.

## The loop

1. **State the conjecture** as a compiling `Prop`.
2. **Test it before proving it.** Instantiate on a finite model and run
   `plausible`, or `decide` if the model is small enough to exhaust. A
   counterexample here is worth more than a proof attempt: the Wolpert
   transcription has four machine-checked refutations of published statements,
   and every one of them was a conjecture that looked true.
3. **Try automation.** `grind` first — it is Lean core and needs no import at
   all, so it is available even inside `Device.lean`. Then
   `aesop (rule_sets := [inference])` for goals about devices, then `decide`.
4. **Only then** write the proof by hand.

## `plausible` leaves a `sorry`

Measured, not assumed. On a goal with no counterexample, `plausible` reports
*"Unable to find a counter-example"* and closes the goal with `sorry`:

```
example : ∀ a b : Nat, a + b = b + a := by plausible
-- warning: declaration uses `sorry`
```

So a `plausible` call **can never appear in committed code**. It would be caught
— `validate_current_state` rejects `sorry` in Lean sources and
`check_print_axioms` would report `sorryAx` — but the point is to know before
running the gate rather than after. Use it interactively; commit either the
counterexample it found, as a real theorem, or the proof it failed to refute.
-/

namespace AISafetyAtlas.Explore

open AISafetyAtlas.Inference

/-! ## Step 3, demonstrated

The `inference` rule set answers *"what does this object satisfy?"* without the
caller knowing which theorem to name. -/

example {U : Type} {C₁ C₂ : InferenceDevice U} (h : StronglyInfers C₁ C₂) :
    SemiControls C₁ C₂.setup := by
  aesop (rule_sets := [inference])

example {U : Type} {C₁ C₂ : InferenceDevice U} (h : StronglyInfers C₁ C₂) :
    InfersDevice C₁ C₂ := by
  aesop (rule_sets := [inference])

example {U : Type} {C : InferenceDevice U} : ¬ StronglyInfers C C := by
  aesop (rule_sets := [inference])

/-- What the rule set does **not** do, stated so the gap is not mistaken for
coverage: Theorem 2(i) quantifies over an intermediate device the goal never
mentions, so no backward rule can guess it. Name it. -/
example {U : Type} {C₁ C₂ : InferenceDevice U} {G : Type} {Γ : U → G}
    (h : StronglyInfers C₁ C₂) (hw : WeaklyInfers C₂ Γ) : WeaklyInfers C₁ Γ :=
  weaklyInfers_of_stronglyInfers h hw

/-! ## Step 2, demonstrated on the shape that actually caught a paper

Wolpert 2018's Corollary 21(ii) concludes `Γ₂ ⇒ Γ₃` from premises that do not
support it. Its propositional core is a three-variable Boolean statement, so the
finite layer settles it outright — and `decide` proves the repair. Running
`plausible` on the printed form returns `g1 := false, g2 := true, g3 := false`,
which is the valuation `Examples.…Epistemic.corollary21_ii_counterexample`
builds a full Definition 11 certificate around. -/

example : ¬ ∀ g₁ g₂ g₃ : Bool,
    boolImplies g₁ g₂ = true → boolImplies g₁ g₃ = true →
      boolImplies g₂ g₃ = true := by decide

example : ∀ g₁ g₂ g₃ : Bool,
    boolImplies g₁ g₂ = true → boolImplies g₂ g₃ = true →
      boolImplies g₁ g₃ = true := by decide

end AISafetyAtlas.Explore

/-! ## `grind` on the frozen core

Four Layer-0 facts carry `@[grind]` attributes, so `grind` closes goals about
them with no lemma named. Registered as a demonstration, not as decoration: an
attribute that does not fire is indistinguishable from no attribute, and this
file is where that gets checked.

`not_stronglyInfers_self` and `not_weaklyInfers_own_concl` are plain facts, so
they take `@[grind]`; `weaklyInfers_of_stronglyInfers` and
`infersDevice_of_stronglyInfers` are implications, so they take `@[grind →]`.
The forward form is **rejected** for the first two — `grind` reports
*"does not have propositional hypotheses"* — which is why the two attributes are
not interchangeable.
-/

section GrindDemo

open AISafetyAtlas.Inference

variable {U : Type} (C₁ C₂ : InferenceDevice U)

example (h : StronglyInfers C₁ C₁) : False := by grind

example {G : Type} (Γ : U → G) (hs : StronglyInfers C₁ C₂) (hw : WeaklyInfers C₂ Γ) :
    WeaklyInfers C₁ Γ := by grind

example (h : WeaklyInfers C₁ C₁.concl) : False := by grind

end GrindDemo
