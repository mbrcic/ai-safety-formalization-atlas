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
# MAIS-O23 — do the margins alone identify a model?

`q:ident` asks whether equal behavioural transforms force equal models inside
`𝕄(sk, λ)`. The atlas answers no; the witness is proved in
`Examples/Conjectures/`.

Stated at the MAIS revision pinned in `docs/provenance/mais-source-pin.md`.
Defining a proposition asserts nothing about its truth; resolutions live in
`AISafetyAtlas/Examples/Conjectures/`.
-/

namespace AISafetyAtlas.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.BinaryPair

variable {C : Type*} [Fintype C] [DecidableEq C] [Nonempty C]
variable {dim : C → ℕ}

/--
**MAIS-O23, negative-answer statement.**

MAIS-A2 `q:ident` fixes an arbitrary skeleton `sk` and `λ ∈ (0, ½)` and asks
whether `𝚫_M = 𝚫_M'` forces `M = M'` on `𝕄(sk, λ)`. The negative answer is the
existential below, stated at the source's own quantifier: *some* skeleton over
*some* finite set of binary chance variables carries two distinct margin-class
models with the same complete masked behavioral transform.

Nothing here is narrower than print. `Fin (m + 1)` is A2's own indexing
`𝐂 = {C₁, …, C_m}` of a finite chance-variable set, which (M5)'s `𝐎 ⊊ 𝐂`
already forces to be nonempty; `binaryDim` is `def:cid`'s "binary chance
variables"; `Bool` is its binary decision `D`; and the tables are real.
-/
@[expose] public noncomputable def maisO23_marginsDoNotSuffice : Prop :=
  ∃ (m : ℕ) (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ) (lam : ℝ),
    Skeleton.ValidMargin lam ∧
      ∃ M M' : Model (Fin (m + 1)) (binaryDim (Fin (m + 1))) ℝ,
        sk.MarginClass M lam ∧ sk.MarginClass M' lam ∧
          M ≠ M' ∧ sk.BehaviorEq M M'


end AISafetyAtlas.Conjectures.MAIS
