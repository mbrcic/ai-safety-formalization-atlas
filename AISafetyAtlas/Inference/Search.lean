module

public import AISafetyAtlas.Inference
public import AISafetyAtlas.Inference.Search.RuleSet

/-!
# A proof-search surface for inference devices

*"For an object of this kind, what does it satisfy?"* is the question a reuse
layer has to answer, and the deterministic core cannot answer it on its own: it
is a set of `def`s and standalone theorems, so nothing indexes the implications
between them.

This module registers those implications in a named `aesop` rule set, so the
question becomes one tactic call:

```lean
example (C₁ C₂ : InferenceDevice U) (h : StronglyInfers C₁ C₂) :
    SemiControls C₁ C₂.setup := by
  aesop (rule_sets := [inference])
```

## Why this is a separate module

`Device.lean` imports two Mathlib modules and nothing else, and that narrowness
is deliberate — it is what keeps the impossibility core cheap to build and cheap
to audit. Importing `Aesop` there would push it onto every consumer of the public
facade. Attributes can be attached to constants declared elsewhere, so the rules
live here instead and cost nothing unless a caller opts in with
`import AISafetyAtlas.Inference.Search`.

## What is registered, and what is not

Only **section 3–7 and section 9 implications**, whose statements are frozen:
Theorems 1–5, Proposition 1(ii), the control transports and the physical-knowledge
kernel are explicitly not to be restated. Section 8 is *not* registered — it is
being restated over a general measure space, and annotating a signature that is
about to change is work done twice.

Transitivity rules (`stronglyInfers_trans`, `Copies.trans`, `Mimics.trans`) are
deliberately **absent**: as backward rules they apply to their own conclusion and
send the search into a loop with nothing to make progress on.

**A rule is registered only if its conclusion determines every argument.**
`SemiControls C₁ C₂.setup` fixes both devices, so
`semiControls_setup_of_stronglyInfers` is a usable backward rule. Theorem 2(i)
is not: it concludes `WeaklyInfers C₁ Γ` while quantifying over an intermediate
`C₂` the goal cannot supply, and `PhysicallyKnows.weaklyInfers` drops
Definition 11's `γ` and `W` entirely. Registered backwards they leave
metavariables and the search fails; `safe forward` and `unsafe apply` were both
tried and neither fires. They are therefore **not registered**, and a caller who
wants them names them: `exact weaklyInfers_of_stronglyInfers h hw`.

Recorded because a rule that never fires is worse than an absent one — it reads
as coverage. Reopening this means finding the aesop idiom that indexes a premise
the conclusion does not mention, not adding the attribute back.
-/

namespace AISafetyAtlas.Inference

/-! ## Section 5–7: what strong inference and control give you -/

attribute [aesop safe apply (rule_sets := [inference])] infersDevice_of_stronglyInfers
attribute [aesop safe apply (rule_sets := [inference])] semiControls_setup_of_stronglyInfers
attribute [aesop safe apply (rule_sets := [inference])] weaklyInfers_of_controls

/-! ## Section 9: what physical knowledge gives you -/


/-! ## The impossibility results, as closing rules

These have `False` or a negation as their conclusion, so they close a goal rather
than decompose one. -/

attribute [aesop safe forward (rule_sets := [inference])] not_stronglyInfers_self
attribute [aesop safe forward (rule_sets := [inference])] not_weaklyInfers_own_concl

end AISafetyAtlas.Inference
