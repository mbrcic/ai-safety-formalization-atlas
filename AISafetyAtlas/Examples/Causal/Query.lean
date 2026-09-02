module

public import AISafetyAtlas.Causal.Query
public import AISafetyAtlas.Examples.Causal.BehavioralCollision

/-!
# Worked model of the MAIS-A2 query protocol

`AISafetyAtlas.Causal.Query` renders `subsec:queries`. This module exercises it
on the two-variable skeleton `skel`, so that the shapes the protocol commits to
are checked against something concrete rather than only asserted in a docstring.

Four things are worth seeing run, and each corresponds to a printed commitment:

* a query really is a **rational** mixture read against the model's value field;
* a **deterministic** analyst is the special case of a randomized one whose laws
  are point masses, so nothing was lost by randomizing the type;
* a **non-adaptive** analyst is the special case that ignores its history;
* `N(ε)` is `⊤` exactly when no budget achieves `ε`, which is the case a
  `ℕ`-valued budget could not express.
-/

namespace AISafetyAtlas.Examples.Causal.Query

open AISafetyAtlas.Causal
open AISafetyAtlas.Examples.Causal

/-! ## A concrete query -/

/-- The query that masks nothing, mixes nothing, and reads the policy at
`X = 0, Y = 0`. `skel.observed` is empty here, so the empty visible set is the
only legal mask — which is `q:chain`'s `𝐎 = ∅` situation, not a restriction the
protocol imposes. -/
public noncomputable def trivialQuery : ShiftedQuery skel where
  visible := ∅
  visible_subset := Finset.empty_subset _
  mix := ProbMixture.dirac (fun _ ↦ id)
  observation := asg false false

/-- The query's weights are rational and its answer lands in the skeleton's
value field. This is the coercion `subsec:queries` forces by writing *"rational
mixture weights"* over `def:margin`'s real tables. -/
public theorem trivialQuery_mix_rational :
    (trivialQuery.mix : Mixture (Fin 2) (binaryDim (Fin 2)) ℚ) (fun _ ↦ id) = 1 := by
  simp [trivialQuery]

/-! ## Deterministic analysts are randomized analysts -/

/-- A deterministic strategy, embedded by taking point masses. -/
public noncomputable def constStrategy (q : ShiftedQuery skel) :
    RandomizedQueryStrategy skel :=
  fun _ ↦ PMF.pure q

/-- A strategy that ignores its transcript entirely is non-adaptive: it reads no
answers, which is all non-adaptivity forbids. -/
public theorem constStrategy_nonadaptive (q : ShiftedQuery skel) :
    IsNonadaptiveRandomizedStrategy skel (constStrategy q) :=
  fun _ _ _ ↦ rfl

/-- Non-adaptivity constrains only the **answers**. A strategy that reads its own
past queries — replaying whatever it played first — is still non-adaptive, which
is what lets a non-adaptive analyst carry a *correlated* schedule drawn in
advance. Requiring the law to depend only on the round number would exclude this
and compare O25's adaptive analyst against an artificially weak opponent. -/
public theorem replayFirstQuery_nonadaptive (q₀ : ShiftedQuery skel) :
    IsNonadaptiveRandomizedStrategy skel
      (fun h ↦ PMF.pure ((h.map Prod.fst).head?.getD q₀)) := by
  intro h h' hq
  simp only []
  rw [hq]

/-- Before any query the transcript is empty, with probability one. -/
public theorem runRandomizedTranscript_zero (family : PolicyFamily skel)
    (strategy : RandomizedQueryStrategy skel) :
    runRandomizedTranscript skel family strategy 0 = PMF.pure ([] : Transcript skel) :=
  rfl

/-- One query against a deterministic strategy produces one `(query, answer)`
pair, with probability one: the oracle is exact, so the analyst's randomization
is the only source of spread and a point mass stays a point mass.

The pair is the point — the transcript keeps the query the analyst issued, so a
later round can tell two queries apart even when they answered alike. -/
public theorem runRandomizedTranscript_one_const (family : PolicyFamily skel)
    (q : ShiftedQuery skel) :
    runRandomizedTranscript skel family (constStrategy q) 1
      = PMF.pure [(q, exactPolicyAnswer skel family q)] := by
  show PMF.bind (PMF.pure ([] : Transcript skel))
      (fun history ↦ PMF.map
        (fun r ↦ history ++ [(r, exactPolicyAnswer skel family r)])
        (constStrategy q history)) = _
  rw [PMF.pure_bind]
  simp [constStrategy, PMF.map, PMF.pure_bind]

/-! ## Expectation collapses on a point mass -/

/-- Against a point mass the expectation is the value, so a deterministic
analyst's *expected* error is its error. This is what makes print's
*"expected error"* a genuine generalization of the deterministic reading rather
than a different quantity on the deterministic instances. -/
public theorem pmfExpect_const_strategy (f : List ℚ → ℝ) (r : List ℚ) :
    pmfExpect (PMF.pure r) f = f r :=
  pmfExpect_pure r f

/-! ## `N(ε)` is `⊤` when nothing achieves `ε`

The `ℕ∞` codomain exists for this case. A `ℕ`-valued budget has to return some
natural number when no budget is feasible, and `0` — the value the previous
definition returned — asserts that *zero queries suffice*, which is the opposite
of the truth. Every upper bound on `N(ε)` then holds vacuously on exactly the
instances print would answer *no* for. -/

/-- No budget can drive a risk below a negative target, so `N(ε) = ⊤` there.

This is deliberately the cheapest instance of the `⊤` branch: it needs no
knowledge of the risk's value, only that a real supremum of model errors is
never below a negative number when it is achieved at all. It is a worked example
of the codomain, not a claim about `skel`'s query complexity. -/
public theorem exactMinimalBudget_of_empty
    (mc : Set (Model (Fin 2) (binaryDim (Fin 2)) ℝ)) (ε : ℝ)
    (h : ∀ m : ℕ, ¬ exactMinimaxRisk (skel.mapRat ℝ) mc m ≤ ε) :
    exactMinimalBudget (skel.mapRat ℝ) mc ε = ⊤ := by
  have hempty : {n : ℕ∞ | ∃ m : ℕ, (m : ℕ∞) = n ∧
      exactMinimaxRisk (skel.mapRat ℝ) mc m ≤ ε} = ∅ := by
    ext n
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨m, -, hm⟩
    exact h m hm
  unfold exactMinimalBudget
  rw [hempty, sInf_empty]

/-- On an empty model class, every nonnegative target is achieved with zero
queries. This is the `sSup ∅ = 0` convention propagated through the actual
randomized minimax and `ℕ∞` budget definitions used by MAIS-O26. -/
public theorem exactMinimalBudget_emptyClass {m : ℕ}
    (sk : Skeleton (Fin (m + 1)) (binaryDim (Fin (m + 1))) Bool ℝ)
    (ε : ℝ) (hε : 0 ≤ ε) :
    exactMinimalBudget sk
      (∅ : Set (Model (Fin (m + 1)) (binaryDim (Fin (m + 1))) ℝ)) ε = 0 := by
  unfold exactMinimalBudget exactMinimaxRisk
  simp [hε]
  apply le_antisymm
  · apply sInf_le
    exact ⟨0, rfl⟩
  · exact bot_le

end AISafetyAtlas.Examples.Causal.Query
