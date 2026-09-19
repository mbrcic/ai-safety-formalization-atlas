# Tau Ceti Morse cone (vendored)

| Field | Value |
|---|---|
| Upstream | https://github.com/TauCetiProject/TauCeti |
| Pin revision | `d7bf8387e88bbf5f262414f5e112d480b24b2519` (2026-09-05) |
| Upstream toolchain | `leanprover/lean4:v4.34.0-rc2`, Mathlib `master` |
| Atlas toolchain | `leanprover/lean4:v4.33.0`, Mathlib `v4.33.0` |
| License | Apache-2.0 (text in `LICENSE`) |
| Governance | Incubated by the Lean FRO and the Mathlib Initiative; human-written roadmaps in `TauCetiRoadmap`, review machinery in `TauCetiReview` |
| Principal declarations | `TauCeti.IsNondegenerateCriticalPoint.exists_normal_form`, `TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart`, `TauCeti.exists_congruence_of_symmetric_family` |
| Scope | The Morse lemma in a Banach space and its dependency cone. Eight modules, 1,396 lines. Not the rest of Tau Ceti (4,430 files, 1.02M lines). |
| Build target | Yes — `[[lean_lib]] TauCeti`, `srcDir = "vendor/TauCeti"`, in `scripts/lean_build_targets.txt` |

## Why vendored rather than required

Tau Ceti pins Lean `v4.34.0-rc2` on Mathlib `master`. This repository pins
`v4.33.0` through PFR, Foundation and AddCombi — the lakefile says so in a
comment on the PFR `require` — and Lake resolves one Mathlib for the whole
build. A `require` would therefore be a joint toolchain migration of the
Gödel/Tarski/Löb layer and the whole information-theoretic layer, plus a fresh
elaboration-drift baseline pair, in exchange for 1,396 of 1.02M lines.

Vendoring is also the reversible choice. This directory can be deleted.

## The backport, in full

Two lines. Nothing else in the eight files differs from upstream.

| File | Upstream | Here | Why |
|---|---|---|---|
| `Topology/Algebra/Module/BilinearForm.lean` | `import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible` | `import Mathlib.Topology.Algebra.Module.Equiv` | Mathlib file split after `v4.33.0`; `ContinuousLinearMap.IsInvertible` lives in `Equiv.lean` at our pin |
| `Analysis/Calculus/Morse/NormalForm.lean` | `hf.of_le (by norm_num)` (×2) | `hf.of_le (by decide)` (×2) | `norm_num` no longer closes `(2 : WithTop ℕ∞) ≤ ∞` at our pin |

Verify with `diff -r` against the upstream tree at the pinned revision.

## Build and axiom state

`lake build TauCeti` succeeds at the atlas toolchain. The vendored tree contains
no `sorry`, no `axiom`, and no `native_decide`. Every headline declaration prints
exactly the atlas's allowlist:

```
TauCeti.IsNondegenerateCriticalPoint.exists_normal_form   [propext, Classical.choice, Quot.sound]
TauCeti.IsNondegenerateCriticalPoint.exists_morse_chart   [propext, Classical.choice, Quot.sound]
TauCeti.exists_congruence_of_symmetric_family             [propext, Classical.choice, Quot.sound]
TauCeti.map_add_eq_add_hessianAverage                     [propext, Classical.choice, Quot.sound]
TauCeti.analyticAt_sqrtNearOne                            [propext, Classical.choice, Quot.sound]
```

By this repository's own standing rule that is **not** evidence of anything
except the absence of axioms. The audit below is the evidence.

---

# Statement-fidelity audit

Read on 2026-09-05 against the printed mathematics, declaration by declaration.
Proof bodies were not audited: the kernel checks those, and an audit that reads
a proof and not a statement is checking the thing that cannot silently fail.

Upstream cites its own references — Audin–Damian *Morse Theory and Floer
Homology* Ch. 1; Palais, *Morse theory on Hilbert manifolds*, Topology **2**
(1963) 299–340; Schwarz, *Morse Homology* Ch. 1; Lang, *Real and Functional
Analysis* Ch. XIV. Those are the right sources for what is stated, and the
statements are checked against them below rather than against the citations
being present.

## 1. `IsNondegenerateCriticalPoint` — **faithful**

```lean
structure IsNondegenerateCriticalPoint (f : E → ℝ) (x : E) : Prop where
  contDiffAt : ContDiffAt ℝ 2 f x
  fderiv_eq_zero : fderiv ℝ f x = 0
  isInvertible : (fderiv ℝ (fderiv ℝ f) x).IsInvertible
```

This is Palais's condition: the second derivative, read as `E → E∗`, is a linear
homeomorphism. In finite dimensions it reduces to the classical nondegenerate
Hessian, and upstream proves that reduction
(`isNondegenerateCriticalPoint_iff_separatingLeft`) rather than asserting it.

Three things the definition gets right that a careless one would not:

* **Regularity is inside the structure.** Mathlib totalizes `fderiv` by zero off
  the differentiability locus, so a predicate phrased on `fderiv` alone would
  call a function nondegenerate at a point where it is not continuous. Upstream
  says this in the docstring and acts on it.
* **Invertibility, not injectivity.** In infinite dimensions these differ, and
  the docstring says so.
* **`IsMorseOn` is deliberately not defined.** `HasNondegenerateCriticalPointsOn`
  asks nothing away from critical points, which is *weaker* than a Morse function
  in the textbook sense, and the name for the stronger notion is left free. This
  is exactly the discipline the atlas asks of its own rows.

**Verdict: faithful, and better scoped than the textbook statement.**

## 2. `map_add_eq_add_hessianAverage` — **faithful**

```lean
f (x + v) = f x + fderiv ℝ f x v + (2 : ℝ)⁻¹ • hessianAverage f x v v v
```

with `hessianAverage f x v = ∫₀¹ 2(1−t) · D²f(x + t•v) dt`. Unfolding, this is

    f(x + v) = f(x) + Df(x)v + ∫₀¹ (1 − t) · D²f(x + tv)(v, v) dt,

the standard integral form of Taylor's theorem to second order. The weight
normalisation is checked, not assumed: `hessianAverage_zero` proves
`∫₀¹ 2(1−t) dt = 1`, so the family really does specialise to the Hessian at
`v = 0`. Hypothesis is `ContDiff ℝ 2 f`, which is what the printed statement
needs.

**Verdict: faithful.**

## 3. `exists_congruence_of_symmetric_family` — **faithful; one thing not claimed**

```lean
{B : E → E →L[ℝ] E →L[ℝ] ℝ} (hB : ContDiff ℝ ∞ B)
(hsymm : ∀ v w w', B v w w' = B v w' w)
(B₀ : E ≃L[ℝ] (E →L[ℝ] ℝ)) (hB₀ : (B₀ : E →L[ℝ] E →L[ℝ] ℝ) = B 0) :
∃ R U, IsOpen U ∧ 0 ∈ U ∧ R 0 = 1 ∧ ContDiffOn ℝ ∞ R U ∧
  ∀ v ∈ U, ∀ w w', B₀ (R v w) (R v w') = B v w w'
```

This is the linear-algebraic core of the Banach Morse lemma as Palais and Lang
prove it: a smooth family of symmetric forms with invertible value at the origin
is, near the origin, the congruence `B(v) = R(v)ᵀ B₀ R(v)` by a smooth family
`R` with `R 0 = 1`. The route is the one in print — `C v = B₀⁻¹ ∘ B v` is
self-adjoint for the `B₀` pairing, and `R v` is its square root — and upstream
says so in the docstring.

**What is not claimed, and a consumer must not assume:** the conclusion does not
say `R v` is invertible. `R 0 = 1` together with continuity gives invertibility
on a possibly smaller neighbourhood, and upstream recovers it downstream through
the derivative of `v ↦ R v v` rather than by asserting it here. Any atlas
consumer needing an invertible `R v` must derive it, not read it off.

**Verdict: faithful. One absence to respect.**

## 4. `IsNondegenerateCriticalPoint.exists_normal_form` — **faithful, with a stronger hypothesis than print**

```lean
(hf : ContDiff ℝ ∞ f) (h : IsNondegenerateCriticalPoint f x) :
∃ φ U, IsOpen U ∧ 0 ∈ U ∧ φ 0 = 0 ∧ ContDiffOn ℝ ∞ φ U ∧
  HasFDerivAt φ (ContinuousLinearMap.id ℝ E) 0 ∧
  ∀ v ∈ U, f (x + v) = f x + (2 : ℝ)⁻¹ * fderiv ℝ (fderiv ℝ f) x (φ v) (φ v)
```

This is the Morse lemma in the Palais/Lang form: near a nondegenerate critical
point there are coordinates in which `f` is exactly `f(x) + ½ D²f(x)(u, u)`.

Two differences from Milnor's finite-dimensional statement, both correct and
both worth stating explicitly because a reader who expects Milnor will misread
this:

* **No diagonalisation.** Milnor's Lemma 2.2 gives `f = f(p) − x₁² − … − x_λ² +
  x_{λ+1}² + … + x_n²`. That is the *finite-dimensional refinement*, obtained by
  applying Sylvester's law of inertia to the Hessian afterwards. Upstream stops
  at the Hessian quadratic form, which is the correct Banach statement.
* **`ContDiff ℝ ∞ f` is global, not local.** The printed statement needs
  smoothness near the point; this asks it everywhere. That is a *stronger
  hypothesis*, so the theorem is weaker than print — safe to consume, but a
  consumer with a merely locally-smooth `f` cannot apply it. For the atlas's
  intended use the loss is a polynomial, so the gap does not bite.

**Verdict: faithful to the Banach form. Hypothesis stronger than print; the
conclusion is not diagonalised, by design.**

## 5. `IsNondegenerateCriticalPoint.exists_morse_chart` — **faithful, and the one to consume**

Same content packaged as an `OpenPartialHomeomorph` with `ContDiffOn` in both
directions. This, not `exists_normal_form`, is the version a volume-transport
argument wants, because it supplies the local inverse and the open domains that
`AISafetyAtlas.SingularLearning.hasLocalVolumeOrder_comp_of_analytic` and
`..._comp_of_lipschitz` require.

**Verdict: faithful.**

## 6. `sqrtNearOne` and its four facts — **faithful; scope carefully stated**

`sqrtNearOne A` is the local inverse of `a ↦ a * a` at `1` in a real Banach
algebra, obtained from the inverse function theorem. The four facts are: it
fixes `1`; it is analytic at `1`; near `1` it is a right inverse of squaring
(so its value is a square root); near `1` it is a left inverse (the uniqueness
half).

The docstring draws the distinction that matters and that a careless port would
lose: **this is not `CFC.sqrt`.** The continuous functional calculus computes the
*positive* square root of a positive element of a C⋆-algebra; this is a square
root near `1` in a bare Banach algebra with smooth dependence on the element.
Neither implies the other, and the statements here claim only the latter.

`sqrtNearOne` is meaningful only near `1` — it is totalised elsewhere by the
`localInverse` construction and its value away from `1` means nothing. Every
statement about it is a `Filter.Eventually` at `𝓝 1`, which is the honest
packaging.

**Verdict: faithful, with the scope stated rather than left to be discovered.**

## 7. Support files — **faithful**

* `Hadamard.lean`: `segmentAverage`, `hadamardFactor`, and
  `sub_eq_hadamardFactor_apply` — the first-order Taylor expansion along a
  segment with the coefficient bundled as a continuous linear map. Standard
  Hadamard factorisation.
* `SecondDerivative.lean`: `fderiv_fderiv_comp_apply_of_fderiv_eq_zero` carries
  the hypothesis `fderiv 𝕜 f (φ b) = 0` that makes the first-order chain-rule
  term drop out — the statement is false without it and the hypothesis is
  present. `eventually_fderiv_ne` warns in its own docstring that it is
  avoidance of one fixed value, not local injectivity of `fderiv`.
* `Bilinear.lean`: derivatives of `z ↦ B z z`. `fderiv_apply_self` gives
  `B.flip y + B y`, correct for a not-necessarily-symmetric `B`.
* `BilinearForm.lean`: `isInvertible_of_injective` carries
  `[FiniteDimensional 𝕜 E]`. The statement is false in infinite dimensions and
  the hypothesis is present.
* `ParametricIntegral.lean`: differentiation under an integral over `Icc 0 1`
  for a continuously differentiable integrand. Standard.

**Verdict: faithful. Every statement that needs a side condition to be true
carries it.**

## Overall

No fidelity defect found. The docstrings are unusually careful about what is
*not* claimed — the `CFC.sqrt` distinction, the `IsMorseOn` reservation, the
"avoidance of one value, not local injectivity" warning, the Palais-vs-injectivity
point — which is the same discipline this repository applies to its own rows.

Two things a consumer must carry forward rather than assume:

1. `exists_congruence_of_symmetric_family` does not claim `R v` invertible.
2. `exists_normal_form` needs `ContDiff ℝ ∞ f` globally, and does not diagonalise
   the Hessian; Sylvester is a separate step, and this repository already has it
   as `AISafetyAtlas.SingularLearning.hasLocalVolumeOrder_abs_of_diagonal`.

## What this cone does **not** contain

The result MAIS-O77(b) actually needs is a **splitting lemma for a *degenerate*
critical point** (Gromoll–Meyer / Morse–Bott): the rung points of the O77 loss
have degenerate Hessians, and every theorem above assumes nondegeneracy. Nothing
here closes that gap. See `docs/provenance/mais-o7-o77-verification.md` §8.2 and
`reviews/mais-issues-5-12/03-stage-4-finding.md`.
