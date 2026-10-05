module

public import Mathlib.Topology.Sion
public import Mathlib.Analysis.Convex.StdSimplex
public import Mathlib.Data.Matrix.Basic

/-!
# Mixed strategies close the gap a pure one leaves

The proposal's `Q3`: for a finite zero-sum normal form with mixed strategies
and a bounded payoff matrix, the lower and upper values coincide.

Print reaches it through linear-programming strong duality, writing out the
row player's program and its dual. That route is unavailable here -- the pinned
Mathlib has no linear program -- and it is not needed: `Mathlib.Topology.Sion`
carries Sion's form of the von Neumann theorem, whose hypotheses the mixed
extension satisfies. The mixed strategy sets are standard simplices, hence
nonempty, convex and compact; the expected payoff is linear in each argument
separately, hence continuous and both quasiconvex and quasiconcave there. So
`exists_mixed_saddlePoint` is Sion's theorem instantiated, and the route
differs from print's while the statement does not.

`exists_mixed_value` is the form `Q3` is used in. `payoff` is the row player's,
so the row player maximizes and the column player minimizes, which is print's
orientation: a mixture the **row** player can commit to that keeps the payoff
at `v` or above against every reply, and a mixture the **column** player can
commit to that holds it at `v` or below against every reply. That *is* the
coincidence of the two security levels, and it is stated without a supremum, so
no conditional-completeness bookkeeping enters.

Mathlib's saddle-point predicate reads `∀ x ∈ X, ∀ y ∈ Y, f a y ≤ f x b`, so
its first set is the **minimizing** side. The column player is therefore `X` in
the instantiation and the row player is `Y`. Getting that backwards produces a
statement that is still provable and is not `Q3`; the asymmetric witness in the
examples is there to pin the orientation by a computation, since a symmetric
payoff matrix cannot tell the two apart.

Mathlib's own `Sion.lean` lists "spell out the particular case of von Neumann
theorem" as a TODO, so the finite bilinear instance is not there.

Source and scope: `docs/provenance/formal-power-proposal-triage.md`. The
document is unpublished and nothing here is coverage.
-/

namespace AISafetyAtlas.Sovereignty

open scoped Matrix

variable {m n : ℕ}

/-- **The mixed strategies** over `k` pure strategies: the standard simplex. -/
@[expose] public def mixed (k : ℕ) : Set (Fin k → ℝ) := stdSimplex ℝ (Fin k)

/-- **The expected payoff to the row player.** -/
@[expose] public def payoff (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin m → ℝ)
    (q : Fin n → ℝ) : ℝ :=
  ∑ i, ∑ j, p i * A i j * q j

/-- The payoff as a linear map in the row player's mixture. -/
@[expose] public def payoffLeft (A : Matrix (Fin m) (Fin n) ℝ) (q : Fin n → ℝ) :
    (Fin m → ℝ) →ₗ[ℝ] ℝ where
  toFun p := payoff A p q
  map_add' p p' := by
    simp only [payoff, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [payoff, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum,
      mul_assoc]

/-- The payoff as a linear map in the column player's mixture. -/
@[expose] public def payoffRight (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin m → ℝ) :
    (Fin n → ℝ) →ₗ[ℝ] ℝ where
  toFun q := payoff A p q
  map_add' q q' := by
    simp only [payoff, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c q := by
    simp only [payoff, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring

/-- Mixed strategies exist as soon as there is a pure one. -/
public theorem mixed_nonempty (hk : 0 < m) : (mixed m).Nonempty := by
  classical
  refine ⟨fun i => if i = ⟨0, hk⟩ then 1 else 0, fun i => ?_, ?_⟩
  · by_cases h : i = ⟨0, hk⟩ <;> simp [h]
  · simp

/-- The mixed strategies are convex. -/
public theorem mixed_convex : Convex ℝ (mixed m) := convex_stdSimplex ℝ (Fin m)

/-- And compact. -/
public theorem mixed_isCompact : IsCompact (mixed m) := isCompact_stdSimplex ℝ (Fin m)

/-- The payoff is continuous in the row player's mixture. -/
public theorem continuous_payoffLeft (A : Matrix (Fin m) (Fin n) ℝ) (q : Fin n → ℝ) :
    Continuous fun p : Fin m → ℝ => payoff A p q := by
  unfold payoff
  fun_prop

/-- And in the column player's. -/
public theorem continuous_payoffRight (A : Matrix (Fin m) (Fin n) ℝ) (p : Fin m → ℝ) :
    Continuous fun q : Fin n → ℝ => payoff A p q := by
  unfold payoff
  fun_prop

/--
**`Q3`: the mixed extension has a saddle point.**

Sion's theorem instantiated at the standard simplices. Print derives the same
statement from linear-programming strong duality; the pinned Mathlib has no
linear program, and the convexity route needs none.
-/
public theorem exists_mixed_saddlePoint (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ p ∈ mixed m, ∃ q ∈ mixed n,
      ∀ p' ∈ mixed m, ∀ q' ∈ mixed n, payoff A p' q ≤ payoff A p q' := by
  obtain ⟨q, hq, p, hp, hsaddle⟩ :=
    Sion.exists_isSaddlePointOn (X := mixed n) (Y := mixed m)
      (f := fun q p => payoff A p q)
      (mixed_nonempty hn) mixed_convex mixed_isCompact
      (fun p _ => (continuous_payoffRight A p).continuousOn.lowerSemicontinuousOn)
      (fun p _ => ((payoffRight A p).convexOn mixed_convex).quasiconvexOn)
      mixed_convex (mixed_nonempty hm) mixed_isCompact
      (fun q _ => (continuous_payoffLeft A q).continuousOn.upperSemicontinuousOn)
      (fun q _ => ((payoffLeft A q).concaveOn mixed_convex).quasiconcaveOn)
  exact ⟨p, hp, q, hq, fun p' hp' q' hq' => hsaddle q' hq' p' hp'⟩

/--
**`Q3`, in the form it is used in: the two security levels coincide.**

`v` is the value. The row player has a mixture keeping its payoff at `v` or
above against every reply, and the column player has one holding that payoff to
`v` or below against every reply. Neither can do better against a best reply,
which is what "lower and upper values coincide" says, and nothing here is a
supremum.
-/
public theorem exists_mixed_value (hm : 0 < m) (hn : 0 < n)
    (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ v : ℝ, ∃ p ∈ mixed m, ∃ q ∈ mixed n,
      (∀ q' ∈ mixed n, v ≤ payoff A p q') ∧ (∀ p' ∈ mixed m, payoff A p' q ≤ v) := by
  obtain ⟨p, hp, q, hq, hsaddle⟩ := exists_mixed_saddlePoint hm hn A
  exact ⟨payoff A p q, p, hp, q, hq, fun q' hq' => hsaddle p hp q' hq',
    fun p' hp' => hsaddle p' hp' q hq⟩

end AISafetyAtlas.Sovereignty
