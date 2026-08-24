module

public import AISafetyAtlas.Conjectures.MAIS
public import AISafetyAtlas.Examples.Causal.BehavioralCollision
public import AISafetyAtlas.Examples.Causal.OneNodeClass
public import AISafetyAtlas.Examples.Causal.Query
public import AISafetyAtlas.Examples.Conjectures.MAIS.Common

/-!
# MAIS-O27(a) — a negative instance

The O23 collision pins the identified-set radius at `1` at every positive
regret, so the regret floor does not vanish at that skeleton. This settles (a)
at one print-legal `(sk, λ)` and not at every one.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ## MAIS-O27(a): a negative instance

`prob:floor`(a) asks to decide whether `φ(0⁺) = 0`, and says the clause *refines*
`q:ident`. The atlas answers `q:ident` negatively, so that refinement has a
consequence the O27 targets never drew: at the collision skeleton the identified
set is nontrivial at every regret, so the radius never falls.

This settles (a) at one print-legal `(sk, λ)` and not at every one — `prob:floor`
opens clause (b) with *"assuming it is zero"*, so print contemplates the answer
varying with the skeleton. It is also not new mathematics: it is the O23
refutation pushed through the definition of `φ`. It is here because a coverage
note claiming a settled instance is invisible to the build, and this is not.
-/

/-- The collision pair sits in one identified set at every positive regret, and
its two graphs differ, so `modelError` — print's own `e` — is `1` throughout. -/
public theorem regretRadius_collision_eq_one {δ : ℚ} (hδ : 0 < δ) :
    regretRadius Examples.Causal.skel Examples.Causal.lam δ = 1 := by
  obtain ⟨-, M, M', hM, hM', hparents, -, hbeh⟩ :=
    Examples.Causal.margin_class_not_identifiable
  have hId : InIdentifiedSet Examples.Causal.skel Examples.Causal.lam δ M M' :=
    inIdentifiedSet_mono hδ.le
      (inIdentifiedSet_zero_of_behaviorEq Examples.Causal.skel _ hM hM' hbeh)
  have hmem : (1 : ℝ) ∈ realRadiusErrors Examples.Causal.skel Examples.Causal.lam δ :=
    (mem_realRadiusErrors_iff _ _ _ _).2
      ⟨1, ⟨M, M', hId.1, hId, by simp [modelError, hparents]⟩, by norm_num⟩
  have hle : ∀ x ∈ realRadiusErrors Examples.Causal.skel Examples.Causal.lam δ, x ≤ 1 := by
    intro x hx
    obtain ⟨q, ⟨N, N', -, -, rfl⟩, rfl⟩ := (mem_realRadiusErrors_iff _ _ _ _).1 hx
    exact_mod_cast modelError_le_one N N'
  rw [regretRadius_eq_sSup]
  exact le_antisymm (csSup_le ⟨1, hmem⟩ hle) (le_csSup ⟨1, hle⟩ hmem)

/-- **MAIS-O27(a) fails at the collision skeleton.** The regret floor does not
vanish there, so `φ(0⁺) = 0` is not a universal answer to `prob:floor`(a). -/
public theorem not_o27RadiusVanishes_collision :
    ¬ O27RadiusVanishes Examples.Causal.skel Examples.Causal.lam := by
  intro hvan
  obtain ⟨δ₀, hδ₀, hlt⟩ := (o27RadiusVanishes_iff _ _).1 hvan (1 / 2) (by norm_num)
  obtain ⟨δ, hδpos, hδlt⟩ := exists_rat_btwn hδ₀
  have hδQ : (0 : ℚ) < δ := by exact_mod_cast hδpos
  have h2 := hlt δ hδQ hδlt
  rw [regretRadius_collision_eq_one hδQ] at h2
  norm_num at h2


/-! ## The same instance at print's real quantifier

Everything above is stated over rational tables, because that is where the
witness is computed. `prob:floor` is stated over `def:margin`'s class, whose
tables are real, so the rational statement is the transported instance and the
real one is what answers to the source. The transport is
`Skeleton.marginClass_mapRat` and `Skeleton.behaviorEq_mapRat` — the same pair
that carries the MAIS-O23 witness — and it is not a cast of the hypothesis:
real mixtures are not images of rational ones, so the two margin-class
memberships and the two behavioural equalities are separate facts.

Refuting the real form is the stronger statement, and it is the one that grades
against print. -/

/-- The collision pins the **real** radius at `1` at every positive real regret.

`realRegretRadius` takes its supremum in `ℝ` over real errors, so nothing here
passes through the rational embedding: the witness pair is the real one, its
membership is `margin_class_not_identifiable_real`'s, and the two graphs differ,
so `modelError` — print's own `e` — is `1`. -/
public theorem realRegretRadius_collision_eq_one {δ : ℝ} (hδ : 0 < δ) :
    realRegretRadius (Examples.Causal.skel.mapRat ℝ)
      ((Examples.Causal.lam : ℚ) : ℝ) δ = 1 := by
  obtain ⟨-, M, M', hM, hM', hparents, -, hbeh⟩ :=
    Examples.Causal.margin_class_not_identifiable_real
  have hId : InIdentifiedSet (Examples.Causal.skel.mapRat ℝ)
      ((Examples.Causal.lam : ℚ) : ℝ) δ M M' :=
    inIdentifiedSet_mono hδ.le
      (inIdentifiedSet_zero_of_behaviorEq (Examples.Causal.skel.mapRat ℝ) _ hM hM' hbeh)
  refine realRegretRadius_eq_of_mem_of_le _
    ((mem_radiusErrors_iff _ _ _ _).2 ⟨M, M', hId.1, hId, by simp [modelError, hparents]⟩)
    ?_
  intro y hy
  obtain ⟨N, N', -, -, rfl⟩ := (mem_radiusErrors_iff _ _ _ _).1 hy
  exact modelError_le_one N N'

/-- **MAIS-O27(a) fails at the collision skeleton, at print's own quantifier.**

`φ(0⁺) = 0` is therefore not a universal answer to `prob:floor`(a) over real
tables and a real regret range, which is the class `def:margin` writes. This
settles (a) at one print-legal `(sk, λ)` and not at every one — clause (b) opens
*"assuming it is zero"*, so print contemplates the answer varying with the
skeleton. -/
public theorem not_o27RealRadiusVanishes_collision :
    ¬ O27RealRadiusVanishes (Examples.Causal.skel.mapRat ℝ)
      ((Examples.Causal.lam : ℚ) : ℝ) := by
  intro hvan
  obtain ⟨δ₀, hδ₀, hlt⟩ := (o27RealRadiusVanishes_iff _ _).1 hvan (1 / 2) (by norm_num)
  have h2 := hlt (δ₀ / 2) (by linarith) (by linarith)
  rw [realRegretRadius_collision_eq_one (by linarith : (0 : ℝ) < δ₀ / 2)] at h2
  norm_num at h2


/-! ## A negative instance of MAIS-O27(c), at print's real quantifier

Clause (c) asks *"for which pairs `(s, δ)` every `M ∈ 𝕄(sk, λ)` carrying an edge
of strength at least `s` has that edge present in every model of `I_δ(M)`"*, and
then to exhibit, for the complementary pairs, an `M` and an `M' ∈ I_δ(M)`
omitting the edge.

The two-graph collision exhibits exactly that, at every positive regret. Its two
models carry opposite one-edge graphs and share a zero-regret policy family, so
each lies in the other's identified set at `δ = 0` and hence at every `δ > 0`,
and the edge of one is absent from the other. (M4) makes that edge's strength at
least `λ`, which is the largest `s` any model of the class is guaranteed to
supply — so the failure is not at some vanishingly weak edge.

**Both halves of (c) are theorems here.**
`exists_strong_edge_omitted_collision` is print's exhibition at the complementary
pair; `not_realEdgesSurviveAt_collision` and
`lam_pair_not_mem_o27RealEdgeSurvivalRegion` are the answer to *"for which
pairs"* at that pair. The exhibition was implicit in the negative result — a
reader could recover it by negating `RealEdgesSurviveAt` — but that def's body
does not cross the module boundary, so recovering it was not something a
downstream module could do.

This settles (c) at one print-legal `(sk, λ)` and not at every one, the same
standing as the (a) instance above. -/

/-- The collision pair carries an edge in one model that the other omits. -/
public theorem exists_edge_not_shared
    {M M' : Model (Fin 2) (binaryDim (Fin 2)) ℝ}
    (hpne : M.parents ≠ M'.parents)
    (hor : M.parents = Examples.Causal.arrowXY.parents ∨
      M.parents = Examples.Causal.arrowYX.parents)
    (hor' : M'.parents = Examples.Causal.arrowXY.parents ∨
      M'.parents = Examples.Causal.arrowYX.parents) :
    ∃ parent child, parent ∈ M.parents child ∧ parent ∉ M'.parents child := by
  rcases hor with h | h <;> rcases hor' with h' | h'
  · exact absurd (h.trans h'.symm) hpne
  · exact ⟨Examples.Causal.X, Examples.Causal.Y, by
      rw [h]; simp [Examples.Causal.arrowXY], by
      rw [h']; simp [Examples.Causal.arrowYX, Examples.Causal.X, Examples.Causal.Y]⟩
  · exact ⟨Examples.Causal.Y, Examples.Causal.X, by
      rw [h]; simp [Examples.Causal.arrowYX], by
      rw [h']; simp [Examples.Causal.arrowXY, Examples.Causal.X, Examples.Causal.Y]⟩
  · exact absurd (h.trans h'.symm) hpne

/-- **The exhibition `prob:floor`(c) asks for, at the complementary pair
`(λ, δ)`.**

Clause (c) has two halves joined by a dash, and this is the second one: *"exhibit,
for the complementary pairs, an `M` and an `M' ∈ I_δ(M)` omitting the edge"*.
Read literally, that is a model of the class, a second model sharing a possible
behaviour with it, an edge of the first whose strength print's own (M4) puts at
least at `λ`, and its absence from the second — which is what this statement
carries. The atlas answered this half from the day the collision landed and said
so only in prose; the negative result below is now a corollary of it rather than
the other way round. -/
public theorem exists_strong_edge_omitted_collision {δ : ℝ} (hδ : 0 < δ) :
    ∃ M M' : Model (Fin 2) (binaryDim (Fin 2)) ℝ,
      InIdentifiedSet (Examples.Causal.skel.mapRat ℝ)
          ((Examples.Causal.lam : ℚ) : ℝ) δ M M' ∧
        ∃ parent child,
          RealEdgeStrengthAtLeast M parent child ((Examples.Causal.lam : ℚ) : ℝ) ∧
            parent ∉ M'.parents child := by
  obtain ⟨-, M, M', hM, hM', hpne, -, hor, hor', hbeh⟩ :=
    Examples.Causal.margin_class_not_identifiable_two_graphs_real
  have hId : InIdentifiedSet (Examples.Causal.skel.mapRat ℝ)
      ((Examples.Causal.lam : ℚ) : ℝ) δ M M' :=
    inIdentifiedSet_mono hδ.le
      (inIdentifiedSet_zero_of_behaviorEq _ _ hM hM' hbeh)
  obtain ⟨parent, child, hpc, hnpc⟩ := exists_edge_not_shared hpne hor hor'
  have hM4 : Skeleton.PrintedM4 M ((Examples.Causal.lam : ℚ) : ℝ) :=
    ((Skeleton.marginClass_iff_printed _ _ _).mp hM).2.2.2.2.1
  exact ⟨M, M', hId, parent, child,
    realEdgeStrengthAtLeast_lam_of_printedM4 hM4 hpc, hnpc⟩

/-- **MAIS-O27(c) fails at `s = λ` on the collision skeleton**, at every positive
regret and at print's own real quantifier. An edge as strong as the margin
allows is still not guaranteed to survive `I_δ(M)`. -/
public theorem not_realEdgesSurviveAt_collision {δ : ℝ} (hδ : 0 < δ) :
    ¬ RealEdgesSurviveAt (Examples.Causal.skel.mapRat ℝ)
      ((Examples.Causal.lam : ℚ) : ℝ) δ ((Examples.Causal.lam : ℚ) : ℝ) := by
  obtain ⟨M, M', hId, parent, child, hstr, hnpc⟩ :=
    exists_strong_edge_omitted_collision hδ
  exact fun hsurv ↦
    hnpc ((realEdgesSurviveAt_iff _ _ _ _).1 hsurv M M' hId parent child hstr)

/-- The printed `(s, δ)` region therefore omits `(λ, δ)` for every `δ > 0` at
this skeleton — read directly off `O27RealEdgeSurvivalRegion`, which is the
object `prob:floor`(c) asks a solver to determine. -/
public theorem lam_pair_not_mem_o27RealEdgeSurvivalRegion {δ : ℝ} (hδ : 0 < δ) :
    (((Examples.Causal.lam : ℚ) : ℝ), δ) ∉
      O27RealEdgeSurvivalRegion (Examples.Causal.skel.mapRat ℝ)
        ((Examples.Causal.lam : ℚ) : ℝ) := by
  intro hmem
  exact not_realEdgesSurviveAt_collision hδ
    ((mem_o27RealEdgeSurvivalRegion_iff _ _ _).1 hmem).2.2


end AISafetyAtlas.Examples.Conjectures.MAIS
