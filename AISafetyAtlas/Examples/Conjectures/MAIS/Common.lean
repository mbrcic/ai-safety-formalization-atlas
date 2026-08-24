module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import AISafetyAtlas.Examples.Causal.OneNodeClass
public import AISafetyAtlas.Examples.Causal.Query

/-!
# Shared checks behind more than one MAIS proof

`def:margin`'s chart dimension on the collision skeleton, and the equality of
the budget under `PMF`-valued and measure-valued analyst outputs, which both
query-complexity problems read.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ## `def:margin`'s `K` on this skeleton

`O26ClassAssumptions` carries `IsClassChartDim`, which pins `K` to the
maximum of `K(G) = Σᵢ 2^{|Pa_G(Cᵢ)|}` over the margin class. That is a real
obligation and not a formality: it is what stops `K` from being a free number
that reaches MAIS-O26 only through the rate `K log(1/ε)`, where `K = 0` and
`K = 1` refute the conjecture against each other on one and the same class.

On two chance variables the maximum is `3`, and the upper half of the argument
needs nothing from the margin conditions — acyclicity alone caps it. -/

/-- Acyclicity caps the chart at three coordinates over two chance variables.

No variable is its own parent, so each has at most one; and they cannot both
have one, since `X → Y` and `Y → X` together would force `rank X < rank Y` and
`rank Y < rank X`. So the two cards are `(0,0)`, `(1,0)` or `(0,1)`, giving
`1 + 1`, `2 + 1` or `1 + 2`. -/
public theorem chartDim_le_three (M : Model (Fin 2) (binaryDim (Fin 2)) ℚ) :
    chartDim M.parents ≤ 3 := by
  classical
  obtain ⟨rank, hrank⟩ := M.acyclic
  have hsub : ∀ c : Fin 2, M.parents c ⊆ Finset.univ.erase c := by
    intro c p hp
    refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ p⟩
    rintro rfl
    exact absurd (hrank _ _ hp) (lt_irrefl _)
  have hcard : ∀ c : Fin 2, (M.parents c).card ≤ 1 := by
    intro c
    have hle := Finset.card_le_card (hsub c)
    rwa [Finset.card_erase_of_mem (Finset.mem_univ c), Finset.card_univ,
      Fintype.card_fin] at hle
  have hnotboth : ¬ ((M.parents X).card = 1 ∧ (M.parents Y).card = 1) := by
    rintro ⟨hX, hY⟩
    have heX : M.parents X = {Y} := by
      refine Finset.eq_of_subset_of_card_le ?_ (by simp [hX])
      simpa [show Finset.univ.erase X = ({Y} : Finset (Fin 2)) from by decide]
        using hsub X
    have heY : M.parents Y = {X} := by
      refine Finset.eq_of_subset_of_card_le ?_ (by simp [hY])
      simpa [show Finset.univ.erase Y = ({X} : Finset (Fin 2)) from by decide]
        using hsub Y
    have h1 := hrank X Y (by rw [heX]; exact Finset.mem_singleton_self Y)
    have h2 := hrank Y X (by rw [heY]; exact Finset.mem_singleton_self X)
    omega
  have h0 := hcard X
  have h1 := hcard Y
  unfold chartDim
  rw [Fin.sum_univ_two]
  interval_cases hcX : (M.parents X).card <;> interval_cases hcY : (M.parents Y).card <;>
    simp_all

/-- The maximum is attained: `arrowXYb lam` carries one edge, so its chart has
`2^0 + 2^1 = 3` coordinates, and it sits in the margin class. -/
public theorem chartDim_arrowXYb (b0 : ℚ) (hlo : 0 ≤ b0) (hhi : b0 ≤ 1) :
    chartDim (arrowXYb b0 hlo hhi).parents = 3 := by
  unfold chartDim
  rw [Fin.sum_univ_two]
  simp [arrowXYb]

/-- `def:margin`'s `K = K(skel, lam)` is `3`. -/
public theorem classChartDim_skel : IsClassChartDim skel lam 3 := by
  constructor
  · exact ⟨arrowXYb lam (by norm_num [lam]) (by norm_num [lam]),
      ⟨lam_valid, arrowXYb_M1 lam _ _ (by norm_num [lam]) (by norm_num [lam]),
        skel_M2, skel_M3, arrowXYb_M4 lam _ _ (by norm_num [lam]), skel_M5 _, skel_M6⟩,
      (chartDim_arrowXYb _ _ _).symm⟩
  · rintro k ⟨M, -, rfl⟩
    exact chartDim_le_three M

/-! ## The output-law equality reaches MAIS-O26's own quantifier

`Causal.measureMinimalBudget_eq_exactMinimalBudget_binary` is stated for a
skeleton over any finite binary chance-variable set. MAIS-O26 is stated over
`Fin (m + 1)`, which is an instance of that — but "is an instance of" is a claim
about typeclass resolution, not a proof, and the closure of CONJ-003's scope axis
rests on it. So it is instantiated here rather than asserted. -/

/-- `N(ε)` computed over `PMF`-valued analysts is `N(ε)` computed over arbitrary
output measures, at exactly the skeleton MAIS-O26 quantifies over. -/
public theorem o26_minimalBudget_eq_measure {m : ℕ}
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (modelClass : Set (Model (Fin (m + 1)) (binaryDim (Fin (m + 1))) ℝ)) (ε : ℝ) :
    measureMinimalBudget sk modelClass ε = exactMinimalBudget sk modelClass ε :=
  measureMinimalBudget_eq_exactMinimalBudget_binary sk modelClass ε

/-- The same at MAIS-O25's quantifier, which is the general finite binary one. -/
public theorem o25_minimalBudget_eq_measure {C : Type} [Fintype C] [DecidableEq C]
    [Nonempty C] (sk : Skeleton C (binaryDim C) Bool ℝ)
    (modelClass : Set (Model C (binaryDim C) ℝ)) (ε : ℝ) :
    measureMinimalBudget sk modelClass ε = exactMinimalBudget sk modelClass ε :=
  measureMinimalBudget_eq_exactMinimalBudget_binary sk modelClass ε


end AISafetyAtlas.Examples.Conjectures.MAIS
