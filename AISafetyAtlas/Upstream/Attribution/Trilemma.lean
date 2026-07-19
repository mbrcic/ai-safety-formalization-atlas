module

public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith

/-!
# Attribution impossibility (core trilemma)

Adapted from DrakeCaraker/dash-impossibility-lean
(`DASHImpossibility/Trilemma.lean`) at revision
`7ec3ef9813a7642fdabe5b73c71d1bed4d5488e2` (software Apache-2.0 per
`CITATION.cff`).

Model-agnostic layer only: feature index type, abstract model + attribution,
Rashomon property, impossibility. Upstream GBDT axioms are not included
(atlas strict-trust). Proof body matches upstream.

Naming note: the predicate is spelled `RashomonProperty` here; upstream names
the identical declaration `RashimonProperty` (misspelled). Identifier corrected
for the atlas facade; the statement and proof are unchanged.
-/

namespace AISafetyAtlas.Upstream.Attribution

/-- Finite set of features with a group labeling (collinearity classes). -/
public structure FeatureIndex where
  /-- Number of features. -/
  P : ℕ
  /-- Number of groups. -/
  L : ℕ
  hP : 0 < P
  /-- Group of each feature. -/
  groupOf : Fin P → Fin L

/-- Membership of feature `j` in group `ℓ`. -/
public def inGroup (fs : FeatureIndex) (ℓ : Fin fs.L) (j : Fin fs.P) : Prop :=
  fs.groupOf j = ℓ

/-- Rashomon: within a group, models exist ranking two features oppositely. -/
public def RashomonProperty
    (fs : FeatureIndex)
    (Model : Type)
    (attribution : Fin fs.P → Model → ℝ) : Prop :=
  ∀ (ℓ : Fin fs.L) (j k : Fin fs.P),
    inGroup fs ℓ j → inGroup fs ℓ k → j ≠ k →
    ∃ f f' : Model,
      attribution j f > attribution k f ∧
      attribution k f' > attribution j f'

/--
**Attribution impossibility.**

Faithfulness of a fixed ranking to every model's attribution order is
impossible under the Rashomon property (stable ranking cannot match opposite
orders). Upstream: `DASHImpossibility.attribution_impossibility`.
-/
public theorem attribution_impossibility
    (fs : FeatureIndex)
    (Model : Type)
    (attribution : Fin fs.P → Model → ℝ)
    (hrash : RashomonProperty fs Model attribution)
    (ℓ : Fin fs.L) (j k : Fin fs.P)
    (hj : inGroup fs ℓ j) (hk : inGroup fs ℓ k) (hjk : j ≠ k)
    (ranking : Fin fs.P → Fin fs.P → Prop)
    (h_faithful : ∀ f : Model,
      ranking j k ↔ attribution j f > attribution k f) :
    False := by
  obtain ⟨f, f', h1, h2⟩ := hrash ℓ j k hj hk hjk
  have hrank : ranking j k := (h_faithful f).mpr h1
  have hcontra : attribution j f' > attribution k f' := (h_faithful f').mp hrank
  linarith

/-- Weak faithfulness + antisymmetry ⇒ ranking cannot decide the pair. -/
public theorem attribution_impossibility_weak
    (fs : FeatureIndex)
    (Model : Type)
    (attribution : Fin fs.P → Model → ℝ)
    (hrash : RashomonProperty fs Model attribution)
    (ℓ : Fin fs.L) (j k : Fin fs.P)
    (hj : inGroup fs ℓ j) (hk : inGroup fs ℓ k) (hjk : j ≠ k)
    (ranking : Fin fs.P → Fin fs.P → Prop)
    (h_faithful_jk : ∀ f : Model,
      attribution j f > attribution k f → ranking j k)
    (h_faithful_kj : ∀ f : Model,
      attribution k f > attribution j f → ranking k j)
    (h_antisym : ¬ (ranking j k ∧ ranking k j)) :
    ¬ (ranking j k ∨ ranking k j) := by
  intro hcomp
  obtain ⟨f, f', h1, h2⟩ := hrash ℓ j k hj hk hjk
  cases hcomp with
  | inl hjk_rank =>
    exact h_antisym ⟨hjk_rank, h_faithful_kj f' h2⟩
  | inr hkj_rank =>
    exact h_antisym ⟨h_faithful_jk f h1, hkj_rank⟩

end AISafetyAtlas.Upstream.Attribution
