module

public import AISafetyAtlas.Inference.Stochastic.Gibbs
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Positivity

/-!
# Proposition 6's algebra, with no probability in it

Everything Proposition 6 does after the four conditional-expectation identities is
arithmetic: `H` is the unit hypercube, `k`, `m`, `n` are differences of its
coordinates, and the bound at `α = β = 1/2` is a closed form in them.

None of it mentions a measure, a device, or a universe. It therefore lives here,
where the `FinPMF` layer and the general measure layer both reach it and neither
depends on the other — the same reason `Gibbs.lean` exists.
-/

namespace AISafetyAtlas.Inference

public theorem sup'_eq_max_of_eq_pair {α : Type*} [DecidableEq α]
    {s : Finset α} (hs : s.Nonempty) (h : α → ℝ) {a b : α} (hsab : s = {a, b}) :
    s.sup' hs h = max (h a) (h b) := by
  subst hsab
  apply le_antisymm
  · refine Finset.sup'_le _ _ (fun c hc => ?_)
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with rfl | rfl
    · exact le_max_left _ _
    · exact le_max_right _ _
  · exact max_le (Finset.le_sup' h (by simp)) (Finset.le_sup' h (by simp))


/-- The paper's `z⃗ ∈ H`: the four conditional probabilities
`zᵢ = P(g = 1 ∣ x₁, x₂)`. `H` is the **unit** hypercube, since the `zᵢ` are
probabilities. -/
public structure Prop6Quadruple where
  /-- `P(g = 1 ∣ x₁ = −1, x₂ = −1)`. -/
  z1 : ℝ
  /-- `P(g = 1 ∣ x₁ = −1, x₂ = +1)`. -/
  z2 : ℝ
  /-- `P(g = 1 ∣ x₁ = +1, x₂ = −1)`. -/
  z3 : ℝ
  /-- `P(g = 1 ∣ x₁ = +1, x₂ = +1)`. -/
  z4 : ℝ
  z1_mem : 0 ≤ z1 ∧ z1 ≤ 1
  z2_mem : 0 ≤ z2 ∧ z2 ≤ 1
  z3_mem : 0 ≤ z3 ∧ z3 ≤ 1
  z4_mem : 0 ≤ z4 ∧ z4 ≤ 1

/-- `k(z⃗) = z₁ + z₄ − z₂ − z₃`. -/
@[expose] public def Prop6Quadruple.k (z : Prop6Quadruple) : ℝ :=
  z.z1 + z.z4 - z.z2 - z.z3

/-- `m(z⃗) = z₂ − z₄`. -/
@[expose] public def Prop6Quadruple.m (z : Prop6Quadruple) : ℝ := z.z2 - z.z4

/-- `n(z⃗) = z₃ − z₄`. -/
@[expose] public def Prop6Quadruple.n (z : Prop6Quadruple) : ℝ := z.z3 - z.z4

/-- The source's right-hand side at a point of `H`. -/
@[expose] public def prop6Expr (α β : ℝ) (z : Prop6Quadruple) : ℝ :=
  |α * β * (z.k) ^ 2 + α * z.k * z.m + β * z.k * z.n + z.m * z.n|


/-- `|x|/2 · |y|/2 = |e|` whenever `x·y = 4e`. -/
public theorem abs_div_two_mul_abs_div_two {x y e : ℝ} (h : x * y = 4 * e) :
    |x| / 2 * (|y| / 2) = |e| := by
  calc |x| / 2 * (|y| / 2) = (|x| * |y|) / 4 := by ring
    _ = |x * y| / 4 := by rw [abs_mul]
    _ = |4 * e| / 4 := by rw [h]
    _ = (4 * |e|) / 4 := by
        rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    _ = |e| := by ring


/-- **Proposition 6, the `α = β = 1/2` closed form.**
*"the product of inference accuracies reduces to
`|[(z₁−z₄)² − (z₂−z₃)²] / 4|`."* -/
public theorem prop6Expr_half_closed (z : Prop6Quadruple) :
    prop6Expr (1 / 2) (1 / 2) z =
      |((z.z1 - z.z4) ^ 2 - (z.z2 - z.z3) ^ 2) / 4| := by
  unfold prop6Expr Prop6Quadruple.k Prop6Quadruple.m Prop6Quadruple.n
  congr 1
  ring

/-- **Proposition 6, final claim.** *"= 1/4."* The maximum of the closed form over
`H` is `1/4`: each squared difference lies in `[0,1]`. -/
public theorem prop6Expr_half_le_quarter (z : Prop6Quadruple) :
    prop6Expr (1 / 2) (1 / 2) z ≤ 1 / 4 := by
  rw [prop6Expr_half_closed]
  obtain ⟨h1l, h1r⟩ := z.z1_mem
  obtain ⟨h2l, h2r⟩ := z.z2_mem
  obtain ⟨h3l, h3r⟩ := z.z3_mem
  obtain ⟨h4l, h4r⟩ := z.z4_mem
  have hA : (z.z1 - z.z4) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - z.z1 + z.z4)
      (by linarith : (0:ℝ) ≤ 1 + z.z1 - z.z4)]
  have hB : (z.z2 - z.z3) ^ 2 ≤ 1 := by
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - z.z2 + z.z3)
      (by linarith : (0:ℝ) ≤ 1 + z.z2 - z.z3)]
  have hbound : |(z.z1 - z.z4) ^ 2 - (z.z2 - z.z3) ^ 2| ≤ 1 :=
    abs_le.mpr ⟨by nlinarith [sq_nonneg (z.z1 - z.z4), sq_nonneg (z.z2 - z.z3)],
      by nlinarith [sq_nonneg (z.z1 - z.z4), sq_nonneg (z.z2 - z.z3)]⟩
  calc |((z.z1 - z.z4) ^ 2 - (z.z2 - z.z3) ^ 2) / 4|
      = |(z.z1 - z.z4) ^ 2 - (z.z2 - z.z3) ^ 2| / 4 := by
        rw [abs_div, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 4)]
    _ ≤ 1 / 4 := by linarith

/-- The source's own maximizer: *"One is when `z₁ = 1`, and `z₂, z₃, z₄` all equal
`0`."* -/
@[expose] public def prop6Maximizer : Prop6Quadruple where
  z1 := 1
  z2 := 0
  z3 := 0
  z4 := 0
  z1_mem := ⟨by norm_num, le_refl 1⟩
  z2_mem := ⟨le_refl 0, by norm_num⟩
  z3_mem := ⟨le_refl 0, by norm_num⟩
  z4_mem := ⟨le_refl 0, by norm_num⟩

/-- **Proposition 6, final claim.** *"= 1/4."* The bound is attained, so `1/4` is
the maximum over `H` and not merely an upper bound. -/
public theorem prop6Expr_half_maximizer :
    prop6Expr (1 / 2) (1 / 2) prop6Maximizer = 1 / 4 := by
  rw [prop6Expr_half_closed]
  norm_num [prop6Maximizer]


/-! ### The maximum over `M` exists

Wolpert 2018 Proposition 11 prints its bound as `ε₁ε₂ ≤ max_{z⃗ ∈ M} |…|`, with
`M` the unit hypercube — which is exactly `Prop6Quadruple`, whose membership
conditions are bundled into the structure. Writing that maximum in Lean needs the
family to be bounded above, which is what these two give.
-/

/-- `|k| ≤ 2`, `|m| ≤ 1`, `|n| ≤ 1` on the unit hypercube. -/
public theorem Prop6Quadruple.abs_k_le (z : Prop6Quadruple) : |z.k| ≤ 2 := by
  obtain ⟨h1, h1'⟩ := z.z1_mem; obtain ⟨h2, h2'⟩ := z.z2_mem
  obtain ⟨h3, h3'⟩ := z.z3_mem; obtain ⟨h4, h4'⟩ := z.z4_mem
  rw [abs_le]
  unfold Prop6Quadruple.k
  constructor <;> linarith

public theorem Prop6Quadruple.abs_m_le (z : Prop6Quadruple) : |z.m| ≤ 1 := by
  obtain ⟨h2, h2'⟩ := z.z2_mem; obtain ⟨h4, h4'⟩ := z.z4_mem
  rw [abs_le]
  unfold Prop6Quadruple.m
  constructor <;> linarith

public theorem Prop6Quadruple.abs_n_le (z : Prop6Quadruple) : |z.n| ≤ 1 := by
  obtain ⟨h3, h3'⟩ := z.z3_mem; obtain ⟨h4, h4'⟩ := z.z4_mem
  rw [abs_le]
  unfold Prop6Quadruple.n
  constructor <;> linarith

/-- The source's expression is bounded on `M`, uniformly in `z⃗`. -/
public theorem prop6Expr_le (α β : ℝ) (z : Prop6Quadruple) :
    prop6Expr α β z ≤ 4 * |α| * |β| + 2 * |α| + 2 * |β| + 1 := by
  have hk := z.abs_k_le
  have hm := z.abs_m_le
  have hn := z.abs_n_le
  have hα : 0 ≤ |α| := abs_nonneg α
  have hβ : 0 ≤ |β| := abs_nonneg β
  have hk0 : 0 ≤ |z.k| := abs_nonneg _
  have hm0 : 0 ≤ |z.m| := abs_nonneg _
  have hn0 : 0 ≤ |z.n| := abs_nonneg _
  have hsq : z.k ^ 2 ≤ 4 := by nlinarith [sq_abs z.k]
  have hsq0 : (0 : ℝ) ≤ z.k ^ 2 := sq_nonneg _
  unfold prop6Expr
  calc |α * β * z.k ^ 2 + α * z.k * z.m + β * z.k * z.n + z.m * z.n|
      ≤ |α * β * z.k ^ 2 + α * z.k * z.m + β * z.k * z.n| + |z.m * z.n| := abs_add_le _ _
    _ ≤ (|α * β * z.k ^ 2 + α * z.k * z.m| + |β * z.k * z.n|) + |z.m * z.n| := by
        gcongr; exact abs_add_le _ _
    _ ≤ ((|α * β * z.k ^ 2| + |α * z.k * z.m|) + |β * z.k * z.n|) + |z.m * z.n| := by
        gcongr; exact abs_add_le _ _
    _ = ((|α| * |β| * z.k ^ 2 + |α| * |z.k| * |z.m|) + |β| * |z.k| * |z.n|) +
          |z.m| * |z.n| := by
        simp only [abs_mul, abs_of_nonneg (sq_nonneg z.k)]
    _ ≤ 4 * |α| * |β| + 2 * |α| + 2 * |β| + 1 := by
        have e1 : |α| * |β| * z.k ^ 2 ≤ 4 * |α| * |β| := by nlinarith [mul_nonneg hα hβ]
        have e2 : |α| * |z.k| * |z.m| ≤ |α| * 2 * 1 := by gcongr
        have e3 : |β| * |z.k| * |z.n| ≤ |β| * 2 * 1 := by gcongr
        have e4 : |z.m| * |z.n| ≤ 1 * 1 := by gcongr
        linarith

/-- Hence `max_{z⃗ ∈ M}` is a genuine supremum. -/
public theorem prop6Expr_bddAbove (α β : ℝ) :
    BddAbove (Set.range (prop6Expr α β)) := by
  refine ⟨4 * |α| * |β| + 2 * |α| + 2 * |β| + 1, ?_⟩
  rintro y ⟨z, rfl⟩
  exact prop6Expr_le α β z

end AISafetyAtlas.Inference
