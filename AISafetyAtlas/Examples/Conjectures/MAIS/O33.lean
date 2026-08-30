module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.O33Corruption

/-!
# MAIS-O33 answered: `η* = 0`, so no positive corruption fraction is tolerable

`prob:corruption` asks *"Determine `η* := sup{η : η uniformly tolerable}`. Is
`η* > 0`?"* The answer here is **no**, and it is the answer proposed in MAIS
issue [#9](https://github.com/lionellevine/MAIS/issues/9).

## What the proof is, in one paragraph

Fix `n = 101` and `δ = 1/2`, which clears print's `(n−1)(1−δ) > 4` with the
product `50`. Take `𝐒 = Fin (m+2)`, `𝐀 = Fin 2`, and two environments whose
transition law ignores the action — print's own action-independent class — one
staying at state `0` with probability `9/10` and the other with probability
`1/10`, so they are `4/5` apart while the target radius is only `2/√50`. In each
world build a `(δ,n)`-bounded agent that opens with action `0` at every
(start state, goal) pair whose goal carries a depth-one *Now* disjunct that
`(s,0)` already satisfies, and near-optimally elsewhere. The two agents therefore
differ only on the goals carrying no such disjunct, and
`Causal.exceptional_ratio_lt` bounds those by `2^{1−R}` with `R = 2^{2|𝐒|−1}` —
doubly exponentially small, so raising `m` clears any positive budget. One
agent's honest first-action map is then an admissible `η`-corruption of the
other's, both worlds present the analyst with the same oracle, and its single
output law would have to put `2/3` on each of two disjoint reconstruction balls.

## What this does not settle

That `η = 0` *is* tolerable is Theorem `thm:rabe` (Richens–Abel–Bellot–Everitt),
which print cites and this repository does not formalize. So `etaStar_eq_zero`
below reads `0` either because nothing positive is tolerable and `0` is, or
because the tolerable set is empty and `Real.sSup ∅ = 0`. The dependence is not
left to prose: `maisO33_etaStarIsZeroGivenBaseline_holds` proves the same
equation from print's baseline as a hypothesis, with the `0 ≤ η*` half coming
from an inhabitant rather than from the convention, so a reader can see exactly
what the value costs. Print's actual question — *is `η* > 0`* — is answered
without that distinction mattering, and `not_maisO33_etaStarPos` is the clause to
read.

Nor does the word *"algorithm"* narrow anything: `UniformlyTolerable`
quantifies over Lean functions, which is at least as wide as print's computable
analysts, and `not_uniformlyTolerableWithin` refutes tolerability inside *every*
subclass, so the widening changes no answer.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal.O33Corruption

/-- **No positive corruption fraction is uniformly tolerable.** -/
public theorem not_uniformlyTolerable {η : ℝ} (hη : 0 < η) : ¬ UniformlyTolerable η := by
  intro h
  obtain ⟨m, hm⟩ := exists_not_tolerantAt hη
  exact hm (tolerantAt_of_uniformlyTolerable h (Fin (m + 2)) (Fin 2) o33Depth o33Delta
    (by simp) (by norm_num [o33Depth]) (by norm_num [o33Delta]) (by norm_num [o33Delta])
    o33_admissible)

/-- **Under every reading of *"a single randomized algorithm"***. `C` is an
arbitrary predicate on analysts, so it covers computable strategies, finitely
describable ones, and any other restriction the word could carry: none of them
is tolerable at a positive fraction. The reason is structural — the witness
defeats *every* strategy at one instance, so narrowing the class cannot rescue
it — and this is the theorem that closes the scope axis `UniformlyTolerable`
would otherwise widen. -/
public theorem not_uniformlyTolerableWithin (C : UniformAnalyst → Prop) {η : ℝ}
    (hη : 0 < η) : ¬ UniformlyTolerableWithin C η := fun h ↦
  not_uniformlyTolerable hη (uniformlyTolerable_of_within h)

public theorem etaStar_le_zero : etaStar ≤ 0 :=
  Real.sSup_le (fun x hx ↦ by
    by_contra hpos
    exact not_uniformlyTolerable (lt_of_not_ge hpos) hx.2) le_rfl

public theorem bddAbove_uniformlyTolerable :
    BddAbove {η : ℝ | 0 ≤ η ∧ UniformlyTolerable η} :=
  ⟨0, fun x hx ↦ by
    by_contra hpos
    exact not_uniformlyTolerable (lt_of_not_ge hpos) hx.2⟩

public theorem zero_le_etaStar : 0 ≤ etaStar := by
  rcases Set.eq_empty_or_nonempty {η : ℝ | 0 ≤ η ∧ UniformlyTolerable η} with
    hemp | ⟨x, hx⟩
  · rw [etaStar, hemp, Real.sSup_empty]
  · exact le_trans hx.1 (le_csSup bddAbove_uniformlyTolerable hx)

/-- **`η* = 0`.** See the module note: the `≥` half does not certify that print's
`η = 0` endpoint is tolerable, which is `thm:rabe` and is not formalized here. -/
public theorem etaStar_eq_zero : etaStar = 0 :=
  le_antisymm etaStar_le_zero zero_le_etaStar

/-- **The `0 ≤ η*` half, from an inhabitant rather than from a convention.**
Print's baseline — that the uncorrupted problem is solved, which is `thm:rabe` —
puts `0` in the tolerable set, and then `0 ≤ η*` is `le_csSup`. -/
public theorem zero_le_etaStar_of_baseline (h : UniformlyTolerable 0) : 0 ≤ etaStar :=
  le_csSup bddAbove_uniformlyTolerable ⟨le_rfl, h⟩

/-- **`η* = 0` without the empty-supremum convention.** -/
public theorem etaStar_eq_zero_of_baseline (h : UniformlyTolerable 0) : etaStar = 0 :=
  le_antisymm etaStar_le_zero (zero_le_etaStar_of_baseline h)

/-- **MAIS-O33's determine-clause, with its one dependence explicit.** This is
the form to read: everything else here is proved outright, and this says what
print's `η* = 0` needs beyond it — print's own cited `thm:rabe`, which this
repository does not formalize. -/
public theorem maisO33_etaStarIsZeroGivenBaseline_holds :
    maisO33_etaStarIsZeroGivenBaseline := by
  intro h
  unfold maisO33_etaStarIsZero maisO33_etaStarCandidate
  exact etaStar_eq_zero_of_baseline h

/-- **The submitted value `η* = 0` is the value of `etaStar`.** Read with the
module note: the `≤` half is the proved content, and the `≥` half comes from the
sign clause together with `Real.sSup ∅ = 0` rather than from a proof that print's
`η = 0` endpoint is tolerable. -/
public theorem maisO33_etaStarIsZero_holds : maisO33_etaStarIsZero := by
  unfold maisO33_etaStarIsZero maisO33_etaStarCandidate
  exact etaStar_eq_zero

/-- **MAIS-O33 answered: `η*` is not positive.** -/
public theorem not_maisO33_etaStarPos : ¬ maisO33_etaStarPos := by
  unfold maisO33_etaStarPos
  rw [etaStar_eq_zero]
  exact lt_irrefl 0

end AISafetyAtlas.Examples.Conjectures.MAIS
