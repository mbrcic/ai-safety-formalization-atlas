module

public import AISafetyAtlas.Causal.Model

/-!
# The A2 margin-class composite

The six numbered conditions are a categorical extension of the binary A2
composite, stated on the simplex supplied by `Causal.Model`. They specialize to
the source conditions when every chance variable is binary. They are not
Richens--Everitt's theorem and not Uhler et al.'s strong-faithfulness definition.

## Grounding

| Condition | Role |
|---|---|
| (M1) interior full-simplex cells | explicit replacement for boundary degeneracy |
| (M2)--(M3) nonzero, sign-varying binary utility gap | checkable domain dependence |
| (M4) categorical max-entry CPT variation along each edge | excludes weak graph edges |
| (M5) all scored ancestors, some hidden state | graphical scope of the task |
| (M6) categorical variation along each utility parent | excludes redundant parents |

Uhler et al. 2013 motivates an explicit margin in place of a measure-zero
exception, but its object is a partial-correlation bound, not these inequalities.
RE24 Assumption 2 and its almost-every discussion motivate (M2)--(M6); A2 is the
source that names and packages the six binary conditions.

`MarginClass` includes `ValidMargin`, so membership itself says
`0 < λ < 1/2`. `Δmask` and `BehaviorEq` quantify over `ProbMixture C dim 𝕜`,
the source's simplex at whichever field a statement picks; the identified-set
packaging remains an A2 object. In
particular, `Δmask` is not RE24 Section 2.3's operation of dropping an
information edge inside the intervention family.
-/

namespace AISafetyAtlas.Causal

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
variable {C : Type*} [Fintype C] [DecidableEq C]
variable {dim : C → ℕ}
variable {Decision : Type*} [Fintype Decision] [DecidableEq Decision]

/-- The unmediated task data used with a chance-variable model.

Decision and utility are deliberately not graph vertices here. That is the
Assumption 1 projection of a single-decision CID, not a full CID. -/
public structure Skeleton (C : Type*) [Fintype C] [DecidableEq C]
    (dim : C → ℕ) (Decision : Type*)
    (𝕜 : Type*) [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] where
  /-- Chance variables visible to the policy. -/
  observed : Finset C
  /-- Chance variables read by utility. -/
  utilityParents : Finset C
  /-- Utility of a decision at an environment assignment. -/
  utility : Decision → Assignment C dim → 𝕜
  /-- Utility factors through the declared utility parents. -/
  utility_parents :
    ∀ d v w, (∀ z ∈ utilityParents, v z = w z) → utility d v = utility d w
  /-- Normalized utility values lie in `[0,1]`, as in RE24 Appendix A.2. -/
  utility_mem_unitInterval : ∀ d v, 0 ≤ utility d v ∧ utility d v ≤ 1

namespace Skeleton

/-- The utility's range over its parents — RE24 Appendix A.2's `min` and `max`
in eq. (2). The utility node's parents are the decision together with the
utility parents, so the extremes are taken over both. -/
@[expose] public noncomputable def utilityLo [Nonempty Decision]
    [Nonempty (Assignment C dim)] (u : Decision → Assignment C dim → 𝕜) : 𝕜 :=
  Finset.univ.inf' Finset.univ_nonempty fun p : Decision × Assignment C dim ↦ u p.1 p.2

@[expose] public noncomputable def utilityHi [Nonempty Decision]
    [Nonempty (Assignment C dim)] (u : Decision → Assignment C dim → 𝕜) : 𝕜 :=
  Finset.univ.sup' Finset.univ_nonempty fun p : Decision × Assignment C dim ↦ u p.1 p.2

/-- **RE24 Appendix A.2, eq. (2).** The normalising map itself: subtract the
utility's minimum over parent states and divide by its range.

Until this landed the atlas carried eq. (2)'s *output* — `Skeleton.utility` is
`[0,1]`-valued by construction — without ever building the map that produces it,
so no unnormalized utility could be written down and then rescaled. `ofUtility`
below closes that: any utility at all becomes a skeleton.

On a constant utility the range is zero and the quotient is `0`, which is still
in `[0,1]`; RE24 states eq. (2) for the non-degenerate case, and this is the
value that keeps the invariant unconditional rather than a claim about print. -/
@[expose] public noncomputable def normalizeUtility [Nonempty Decision]
    [Nonempty (Assignment C dim)] (u : Decision → Assignment C dim → 𝕜) :
    Decision → Assignment C dim → 𝕜 :=
  fun d v ↦ (u d v - utilityLo u) / (utilityHi u - utilityLo u)

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] [DecidableEq Decision] in
public theorem utilityLo_le [Nonempty Decision] [Nonempty (Assignment C dim)]
    (u : Decision → Assignment C dim → 𝕜) (d : Decision) (v : Assignment C dim) :
    utilityLo u ≤ u d v :=
  Finset.inf'_le (fun p : Decision × Assignment C dim ↦ u p.1 p.2)
    (Finset.mem_univ (d, v))

omit [Field 𝕜] [IsStrictOrderedRing 𝕜] [DecidableEq Decision] in
public theorem le_utilityHi [Nonempty Decision] [Nonempty (Assignment C dim)]
    (u : Decision → Assignment C dim → 𝕜) (d : Decision) (v : Assignment C dim) :
    u d v ≤ utilityHi u :=
  Finset.le_sup' (fun p : Decision × Assignment C dim ↦ u p.1 p.2)
    (Finset.mem_univ (d, v))

omit [DecidableEq Decision] in
/-- The normalised utility satisfies the `[0,1]` invariant a `Skeleton` demands. -/
public theorem normalizeUtility_mem_unitInterval [Nonempty Decision]
    [Nonempty (Assignment C dim)] (u : Decision → Assignment C dim → 𝕜)
    (d : Decision) (v : Assignment C dim) :
    0 ≤ normalizeUtility u d v ∧ normalizeUtility u d v ≤ 1 := by
  have hlo := utilityLo_le u d v
  have hhi := le_utilityHi u d v
  unfold normalizeUtility
  rcases eq_or_lt_of_le (hlo.trans hhi) with hdeg | hpos
  · have : u d v = utilityLo u := le_antisymm (hdeg ▸ hhi) hlo
    simp [this, hdeg]
  · have hrange : 0 < utilityHi u - utilityLo u := sub_pos.mpr hpos
    exact ⟨div_nonneg (sub_nonneg.mpr hlo) hrange.le,
      (div_le_one hrange).mpr (by linarith)⟩

omit [IsStrictOrderedRing 𝕜] [DecidableEq Decision] in
/-- Normalisation is affine in the utility, so it preserves factoring through
the declared utility parents. -/
public theorem normalizeUtility_parents [Nonempty Decision]
    [Nonempty (Assignment C dim)] {u : Decision → Assignment C dim → 𝕜}
    {parents : Finset C}
    (hu : ∀ d v w, (∀ z ∈ parents, v z = w z) → u d v = u d w)
    (d : Decision) (v w : Assignment C dim) (h : ∀ z ∈ parents, v z = w z) :
    normalizeUtility u d v = normalizeUtility u d w := by
  unfold normalizeUtility
  rw [hu d v w h]

/-- **Any utility becomes a skeleton.** This is eq. (2) applied: the caller
supplies an arbitrary `𝕜`-valued utility factoring through `utilityParents`, and
the normalising map supplies the `[0,1]` invariant. -/
@[expose] public noncomputable def ofUtility [Nonempty Decision]
    [Nonempty (Assignment C dim)] (observed utilityParents : Finset C)
    (u : Decision → Assignment C dim → 𝕜)
    (hu : ∀ d v w, (∀ z ∈ utilityParents, v z = w z) → u d v = u d w) :
    Skeleton C dim Decision 𝕜 where
  observed := observed
  utilityParents := utilityParents
  utility := normalizeUtility u
  utility_parents := fun d v w h ↦ normalizeUtility_parents hu d v w h
  utility_mem_unitInterval := normalizeUtility_mem_unitInterval u

omit [DecidableEq Decision] in
@[simp] public theorem ofUtility_utility [Nonempty Decision]
    [Nonempty (Assignment C dim)] (observed utilityParents : Finset C)
    (u : Decision → Assignment C dim → 𝕜)
    (hu : ∀ d v w, (∀ z ∈ utilityParents, v z = w z) → u d v = u d w) :
    (ofUtility observed utilityParents u hu).utility = normalizeUtility u := rfl

/-- For binary decisions, the advantage of decision `true` over `false`. -/
@[expose] public def gap (sk : Skeleton C dim Bool 𝕜) : Assignment C dim → 𝕜 :=
  fun v ↦ sk.utility true v - sk.utility false v

public theorem gap_parents (sk : Skeleton C dim Bool 𝕜) (v w : Assignment C dim)
    (h : ∀ z ∈ sk.utilityParents, v z = w z) : sk.gap v = sk.gap w := by
  simp only [gap, sk.utility_parents true v w h, sk.utility_parents false v w h]

public theorem gap_le_one (sk : Skeleton C dim Bool 𝕜) (v : Assignment C dim) :
    |sk.gap v| ≤ 1 := by
  have htrue := sk.utility_mem_unitInterval true v
  have hfalse := sk.utility_mem_unitInterval false v
  rw [abs_le]
  simp only [gap]
  constructor <;> linarith [htrue.1, htrue.2, hfalse.1, hfalse.2]

end Skeleton

namespace Model

/-- The A2 masked gap transform, indexed redundantly by a full assignment. -/
@[expose] public def Δmask (M : Model C dim 𝕜) (gap : Assignment C dim → 𝕜)
    (visible : Finset C) (w : Assignment C dim) (mix : ProbMixture C dim 𝕜) : 𝕜 :=
  ∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
    ∀ c ∈ visible, v c = w c), M.jointProbMix mix.1 v * gap v

public theorem Δmask_empty (M : Model C dim 𝕜) (gap : Assignment C dim → 𝕜)
    (w : Assignment C dim) (mix : ProbMixture C dim 𝕜) :
    M.Δmask gap ∅ w mix = M.Δmix gap mix.1 := by
  unfold Δmask Δmix
  congr 1
  exact Finset.filter_true_of_mem (by simp)

/-- `Δmask` rearranged as a mixture-weighted sum over intervention profiles,
the masked analogue of `Δmix_eq_sum`. -/
public theorem Δmask_eq_sum (M : Model C dim 𝕜) (gap : Assignment C dim → 𝕜)
    (visible : Finset C) (w : Assignment C dim) (mix : ProbMixture C dim 𝕜) :
    M.Δmask gap visible w mix =
      ∑ σ, mix.1 σ * ∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
        ∀ c ∈ visible, v c = w c), M.jointProb σ v * gap v := by
  unfold Δmask jointProbMix
  simp only [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun σ _ ↦ Finset.sum_congr rfl fun v _ ↦ by ring

/-- `Δmask` equality on every rational probability mixture is equivalent to
equality of the masked profile sum for every intervention profile — the
masked analogue of `Δmix_eq_on_probMixture_iff`. -/
public theorem Δmask_eq_on_probMixture_iff (M M' : Model C dim 𝕜)
    (gap : Assignment C dim → 𝕜) (visible : Finset C) (w : Assignment C dim) :
    (∀ mix : ProbMixture C dim 𝕜, M.Δmask gap visible w mix = M'.Δmask gap visible w mix) ↔
      ∀ σ : InterventionProfile C dim,
        (∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
          ∀ c ∈ visible, v c = w c), M.jointProb σ v * gap v) =
        ∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
          ∀ c ∈ visible, v c = w c), M'.jointProb σ v * gap v := by
  constructor
  · intro h σ
    simpa [Δmask_eq_sum] using h (ProbMixture.dirac σ)
  · intro h mix
    rw [Δmask_eq_sum, Δmask_eq_sum]
    exact Finset.sum_congr rfl fun σ _ ↦ by rw [h σ]

end Model

omit [Fintype C] [DecidableEq C] in
/-- Over two points a finite supremum minus the infimum is the absolute difference.

A general fact about `Finset.sup'` and `Finset.inf'` in an ordered field, not a
fact about skeletons, so it sits outside the `Skeleton` namespace. It is what
makes `Skeleton.realizable_iff` the `Decision = Bool` instance of
`Skeleton.realizable_iff_general`: there the fibrewise spread is `|gap|`. -/
public theorem sup'_sub_inf'_bool (f : Bool → 𝕜) :
    Finset.univ.sup' Finset.univ_nonempty f -
      Finset.univ.inf' Finset.univ_nonempty f = |f true - f false| := by
  rcases le_total (f false) (f true) with h | h <;> simp <;> rw [abs_sub_comm] <;>
    simp [abs_of_nonneg, abs_of_nonpos, sub_nonneg, h]


namespace Skeleton

/-- The admissible margin range printed for `M(s, λ)`. -/
@[expose] public def ValidMargin (lam : 𝕜) : Prop := 0 < lam ∧ lam < 1 / 2

/-- (M1): every full-simplex CPT cell lies in `[λ, 1-λ]`. -/
@[expose] public def M1 (M : Model C dim 𝕜) (lam : 𝕜) : Prop :=
  ∀ c a v, lam ≤ M.cpt c a v ∧ M.cpt c a v ≤ 1 - lam

/-- (M2): the binary decision matters at every environment assignment. -/
@[expose] public def M2 (sk : Skeleton C dim Bool 𝕜) (lam : 𝕜) : Prop :=
  ∀ v, lam ≤ |sk.gap v|

/-- (M3): both binary decisions are strictly preferred somewhere on every
observation-compatible slice. -/
@[expose] public def M3 (sk : Skeleton C dim Bool 𝕜) : Prop :=
  ∀ w : Assignment C dim, ∃ vp vm : Assignment C dim,
    (∀ c ∈ sk.observed ∩ sk.utilityParents, vp c = w c) ∧
    (∀ c ∈ sk.observed ∩ sk.utilityParents, vm c = w c) ∧
    0 < sk.gap vp ∧ sk.gap vm < 0

/-- (M4): every graph edge changes some child CPT cell by at least `λ` when
only that categorical parent coordinate changes. -/
@[expose] public def M4 (M : Model C dim 𝕜) (lam : 𝕜) : Prop :=
  ∀ c, ∀ p ∈ M.parents c, ∃ v : Assignment C dim,
    ∃ x y : Fin (dim p), ∃ a : Fin (dim c), x ≠ y ∧
      lam ≤ |M.cpt c a (Function.update v p x) -
        M.cpt c a (Function.update v p y)|

/-- (M5): every chance variable is an ancestor of the score and at least one is hidden. -/
@[expose] public def M5 (sk : Skeleton C dim Bool 𝕜) (M : Model C dim 𝕜) : Prop :=
  (∀ t : Finset C, sk.utilityParents ∪ sk.observed ⊆ t → M.ParentClosed t →
    t = Finset.univ) ∧
  sk.observed ⊂ Finset.univ

/-- (M6): each categorical utility parent changes the binary utility gap by `λ`. -/
@[expose] public def M6 (sk : Skeleton C dim Bool 𝕜) (lam : 𝕜) : Prop :=
  ∀ j ∈ sk.utilityParents, ∃ v : Assignment C dim,
    ∃ x y : Fin (dim j), x ≠ y ∧
      lam ≤ |sk.gap (Function.update v j x) - sk.gap (Function.update v j y)|

/-- The printed margin class, including its required range `0 < λ < 1/2`. -/
@[expose] public def MarginClass (sk : Skeleton C dim Bool 𝕜) (M : Model C dim 𝕜)
    (lam : 𝕜) : Prop :=
  ValidMargin lam ∧ M1 M lam ∧ sk.M2 lam ∧ sk.M3 ∧ M4 M lam ∧ sk.M5 M ∧ sk.M6 lam

/-! ## `def:margin` at binary chance variables

The six conditions above are stated for categorical variables of arbitrary arity;
`def:margin` prints them for binary ones. Every MAIS row in the atlas is stated
over `MarginClass`, so that widening cannot be left to inspection: if the
categorical form had drifted from the printed inequalities, no gate would fail
and every conjecture would quietly be about a different class.

This section writes the printed conditions the way print writes them — at
`binaryDim`, over the `1`-cell of each table — and proves the two forms agree.

Three of the six need no restatement, for a proved reason rather than a
convention: `gap_parents` says `sk.gap` factors through `𝐙`, so quantifying
(M2), (M3) and (M6) over full assignments *is* quantifying over print's
`dom(𝐙)`. `m2_of_padded` makes that concrete by reducing (M2) to the `2^{|𝐙|}`
padded configurations. The content of the collapse is in (M1), (M4) and (M5).
-/

/-- **(M1) as printed**: *"every table entry satisfies `λ ≤ P(cᵢ | paᵢ) ≤ 1-λ`"*.

A binary table *is* its `1`-cells: `P(Cᵢ = 0 | pa)` is not a stored entry but
`1 - P(Cᵢ = 1 | pa)`. The atlas condition ranges over both cells of the stored
simplex, which is the same requirement — `m1_iff_printed` proves it — but only
because the simplex sums to one. -/
@[expose] public def PrintedM1 (M : Model C (binaryDim C) 𝕜) (lam : 𝕜) : Prop :=
  ∀ c v, lam ≤ M.cpt c 1 v ∧ M.cpt c 1 v ≤ 1 - lam

/-- **(M4) as printed**: *"some pair of parent configurations differing only in
`Cᵢ` gives `|P(C_j = 1 | pa) - P(C_j = 1 | pa')| ≥ λ`"*.

Two specializations of the categorical form are visible here. The child cell
print names is the `1`-cell, not an arbitrary one; and at binary, *"differing
only in `Cᵢ`"* forces the pair `0, 1`, so the categorical `x ≠ y` collapses. -/
@[expose] public def PrintedM4 (M : Model C (binaryDim C) 𝕜) (lam : 𝕜) : Prop :=
  ∀ c, ∀ p ∈ M.parents c, ∃ v : Assignment C (binaryDim C),
    lam ≤ |M.cpt c 1 (Function.update v p 0) - M.cpt c 1 (Function.update v p 1)|

/-- **(M5) as printed**: *"`Anc(U) = 𝐂` and `𝐎 ⊊ 𝐂`"*.

`Anc(U)` is read off `def:cid`, which gives `U` the parents `{D} ∪ 𝐙` and `D` the
parents `𝐎`. So the chance variables ancestral to the utility are the ancestor
closure of `𝐙 ∪ 𝐎`, not of `𝐙` alone — the observation set reaches `U` through
the decision. That is why `M5` closes over `utilityParents ∪ observed`. -/
@[expose] public def PrintedM5 (sk : Skeleton C (binaryDim C) Bool 𝕜)
    (M : Model C (binaryDim C) 𝕜) : Prop :=
  M.ancestors (sk.utilityParents ∪ sk.observed) = Finset.univ ∧
    sk.observed ⊂ Finset.univ

/-- `def:margin`'s class, written at binary chance variables as print writes it. -/
@[expose] public def PrintedMarginClass (sk : Skeleton C (binaryDim C) Bool 𝕜)
    (M : Model C (binaryDim C) 𝕜) (lam : 𝕜) : Prop :=
  ValidMargin lam ∧ PrintedM1 M lam ∧ sk.M2 lam ∧ sk.M3 ∧ PrintedM4 M lam ∧
    sk.PrintedM5 M ∧ sk.M6 lam

omit [Fintype C] [DecidableEq C] in
private theorem binary_index_cases {c : C} (a : Fin (binaryDim C c)) : a = 0 ∨ a = 1 := by
  have hlt : (a : ℕ) < 2 := a.isLt
  have hval : (a : ℕ) = 0 ∨ (a : ℕ) = 1 := by omega
  rcases hval with h | h
  · exact Or.inl (Fin.ext (by simpa using h))
  · exact Or.inr (Fin.ext (by simpa using h))

omit [Fintype C] [DecidableEq C] in
private theorem binary_zero_ne_one {c : C} : (0 : Fin (binaryDim C c)) ≠ 1 := by
  intro h
  simpa using congrArg Fin.val h

/-- The `0`-cell of a binary table is determined by the `1`-cell. -/
public theorem cpt_zero_eq (M : Model C (binaryDim C) 𝕜) (c : C)
    (v : Assignment C (binaryDim C)) : M.cpt c 0 v = 1 - M.cpt c 1 v := by
  have h := M.cpt_sum c v
  rw [Fin.sum_univ_two] at h
  linarith

/-- (M1) collapses to its printed form. The reverse direction is where the
simplex is used: constraining the `1`-cell to `[λ, 1-λ]` puts the `0`-cell there
too, and only because the two sum to one. -/
public theorem m1_iff_printed (M : Model C (binaryDim C) 𝕜) (lam : 𝕜) :
    M1 M lam ↔ PrintedM1 M lam := by
  constructor
  · intro h c v
    exact h c 1 v
  · intro h c a v
    have h1 := h c v
    rcases binary_index_cases a with rfl | rfl
    · rw [cpt_zero_eq]
      exact ⟨by linarith [h1.2], by linarith [h1.1]⟩
    · exact h1

/-- (M4) collapses to its printed form. Forward needs both specializations: a
witnessing `0`-cell difference equals the `1`-cell difference up to sign, and a
witnessing pair `x ≠ y` in `Fin 2` is `(0,1)` in one of two orders. -/
public theorem m4_iff_printed (M : Model C (binaryDim C) 𝕜) (lam : 𝕜) :
    M4 M lam ↔ PrintedM4 M lam := by
  constructor
  · rintro h c p hp
    obtain ⟨v, x, y, a, hxy, hle⟩ := h c p hp
    have hcell :
        |M.cpt c a (Function.update v p x) - M.cpt c a (Function.update v p y)| =
          |M.cpt c 1 (Function.update v p x) - M.cpt c 1 (Function.update v p y)| := by
      rcases binary_index_cases a with rfl | rfl
      · rw [cpt_zero_eq, cpt_zero_eq,
          show 1 - M.cpt c 1 (Function.update v p x) -
              (1 - M.cpt c 1 (Function.update v p y)) =
            M.cpt c 1 (Function.update v p y) - M.cpt c 1 (Function.update v p x) by ring,
          abs_sub_comm]
      · rfl
    rw [hcell] at hle
    rcases binary_index_cases x with rfl | rfl <;> rcases binary_index_cases y with rfl | rfl
    · exact absurd rfl hxy
    · exact ⟨v, hle⟩
    · exact ⟨v, by rwa [abs_sub_comm] at hle⟩
    · exact absurd rfl hxy
  · rintro h c p hp
    obtain ⟨v, hle⟩ := h c p hp
    exact ⟨v, 0, 1, 1, binary_zero_ne_one, hle⟩

/-- (M5) collapses to its printed form: `ancestors` is the least parent-closed
superset, so the elimination form the atlas stores is the printed equality. -/
public theorem m5_iff_printed (sk : Skeleton C (binaryDim C) Bool 𝕜)
    (M : Model C (binaryDim C) 𝕜) : sk.M5 M ↔ sk.PrintedM5 M :=
  and_congr_left' (M.ancestors_eq_univ_iff _).symm

/-- **The specialization certificate.** The categorical margin class is
`def:margin`'s printed class whenever the chance variables are binary.

Without this the widening from print's binary conditions to arbitrary arity is
unchecked by the build, and a drift in any of the six would be invisible. -/
public theorem marginClass_iff_printed (sk : Skeleton C (binaryDim C) Bool 𝕜)
    (M : Model C (binaryDim C) 𝕜) (lam : 𝕜) :
    sk.MarginClass M lam ↔ sk.PrintedMarginClass M lam := by
  unfold MarginClass PrintedMarginClass
  rw [m1_iff_printed, m4_iff_printed, m5_iff_printed]

/-- (M2) is decided by the `2^{|𝐙|}` configurations of `dom(𝐙)`, padded with `0`
off the utility parents. This is `gap_parents` made concrete: print quantifies
(M2) over `dom(𝐙)` and the atlas over all of `dom(𝐂)`, and the two agree because
the gap cannot see the difference. The same argument covers (M3) and (M6). -/
public theorem m2_of_padded (sk : Skeleton C (binaryDim C) Bool 𝕜) (lam : 𝕜)
    (h : ∀ z : Assignment C (binaryDim C),
      (∀ c, c ∉ sk.utilityParents → z c = 0) → lam ≤ |sk.gap z|) :
    sk.M2 lam := by
  classical
  intro v
  have hgap : sk.gap v =
      sk.gap (fun c ↦ if c ∈ sk.utilityParents then v c else 0) :=
    sk.gap_parents _ _ (by intro c hc; simp [hc])
  rw [hgap]
  exact h _ (by intro c hc; simp [hc])

public theorem ancestors_eq_univ_of_M5 (sk : Skeleton C dim Bool 𝕜) (M : Model C dim 𝕜)
    (h : sk.M5 M) :
    M.ancestors (sk.utilityParents ∪ sk.observed) = Finset.univ :=
  (M.ancestors_eq_univ_iff _).mpr h.1

omit [Fintype C] [DecidableEq C] [DecidableEq Decision] in
/-- The general-arity form: a decision family's fibrewise spread is bounded by one
exactly when it is realized, up to a fibrewise shift, by a normalized utility.

RE24 Appendix A.2 equation (2) normalizes a utility over its parent states at any
decision arity. `realizable_iff` is this at `Decision = Bool`, where the spread is
`|gap|`; the general statement replaces that two-point difference with the
fibrewise supremum-and-infimum pair. `Nonempty Decision` is required for those to
exist and is the same hypothesis `bestDecision` carries. -/
public theorem realizable_iff_general [Nonempty Decision] (utilityParents : Finset C)
    (g : Decision → Assignment C dim → 𝕜)
    (hfac : ∀ d v w, (∀ z ∈ utilityParents, v z = w z) → g d v = g d w) :
    (∀ v, Finset.univ.sup' Finset.univ_nonempty (fun d ↦ g d v) -
            Finset.univ.inf' Finset.univ_nonempty (fun d ↦ g d v) ≤ 1) ↔
      ∃ u : Decision → Assignment C dim → 𝕜,
        (∀ d v, 0 ≤ u d v ∧ u d v ≤ 1) ∧
        (∀ d v w, (∀ z ∈ utilityParents, v z = w z) → u d v = u d w) ∧
        (∀ d d' v, u d v - u d' v = g d v - g d' v) := by
  classical
  constructor
  · intro h
    refine ⟨fun d v ↦ g d v - Finset.univ.inf' Finset.univ_nonempty (fun d' ↦ g d' v),
      ?_, ?_, ?_⟩
    · intro d v
      have hlo := Finset.inf'_le (fun d' ↦ g d' v) (Finset.mem_univ d)
      have hhi : g d v ≤ Finset.univ.sup' Finset.univ_nonempty (fun d' ↦ g d' v) :=
        Finset.le_sup' (fun d' ↦ g d' v) (Finset.mem_univ d)
      simp only
      exact ⟨by linarith, by linarith [h v]⟩
    · intro d v w hvw
      have hinf : (Finset.univ.inf' Finset.univ_nonempty (fun d' ↦ g d' v)) =
          Finset.univ.inf' Finset.univ_nonempty (fun d' ↦ g d' w) :=
        Finset.inf'_congr Finset.univ_nonempty rfl (fun d' _ ↦ hfac d' v w hvw)
      simp only
      rw [hfac d v w hvw, hinf]
    · intro d d' v
      simp only
      ring
  · rintro ⟨u, hu, -, hg⟩ v
    obtain ⟨a, -, ha⟩ :=
      Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := Decision)) (fun d ↦ g d v)
    obtain ⟨b, -, hb⟩ :=
      Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Decision)) (fun d ↦ g d v)
    rw [ha, hb, ← hg a b v]
    linarith [(hu a v).1, (hu a v).2, (hu b v).1, (hu b v).2]

/-- Bounded parent-factoring gaps are exactly gaps of normalized binary utilities.

This is `realizable_iff_general` at `Decision = Bool`, and is proved from it: the
gap is the two-point family `if d then gap else 0`, whose fibrewise spread is
`|gap|` by `sup'_sub_inf'_bool`. -/
public theorem realizable_iff (sk : Skeleton C dim Bool 𝕜) :
    (∀ v, |sk.gap v| ≤ 1) ↔
      ∃ u : Bool → Assignment C dim → 𝕜,
        (∀ d v, 0 ≤ u d v ∧ u d v ≤ 1) ∧
        (∀ d v w, (∀ z ∈ sk.utilityParents, v z = w z) → u d v = u d w) ∧
        (∀ v, u true v - u false v = sk.gap v) := by
  classical
  set g : Bool → Assignment C dim → 𝕜 := fun d v ↦ if d then sk.gap v else 0 with hg
  have hfac : ∀ d v w, (∀ z ∈ sk.utilityParents, v z = w z) → g d v = g d w := by
    intro d v w hvw
    cases d <;> simp [hg, sk.gap_parents v w hvw]
  have hspread : ∀ v, Finset.univ.sup' Finset.univ_nonempty (fun d ↦ g d v) -
      Finset.univ.inf' Finset.univ_nonempty (fun d ↦ g d v) = |sk.gap v| := by
    intro v
    rw [sup'_sub_inf'_bool (fun d ↦ g d v)]
    simp [hg]
  constructor
  · intro h
    obtain ⟨u, hu, hufac, hud⟩ :=
      (realizable_iff_general (dim := dim) sk.utilityParents g hfac).mp
        (fun v ↦ by rw [hspread v]; exact h v)
    exact ⟨u, hu, hufac, fun v ↦ by simpa [hg] using hud true false v⟩
  · rintro ⟨u, hu, hufac, hud⟩ v
    have := (realizable_iff_general (dim := dim) sk.utilityParents g hfac).mpr
      ⟨u, hu, hufac, ?_⟩ v
    · rwa [hspread v] at this
    · intro d d' w
      cases d <;> cases d' <;> simp [hg, ← hud w]

/-! ## Behavioral family -/

@[expose] public def BehaviorEq (sk : Skeleton C dim Bool 𝕜) (M M' : Model C dim 𝕜) : Prop :=
  ∀ visible ⊆ sk.observed, ∀ w : Assignment C dim, ∀ mix : ProbMixture C dim 𝕜,
    M.Δmask sk.gap visible w mix = M'.Δmask sk.gap visible w mix

public theorem behaviorEq_of_observed_eq_empty {sk : Skeleton C dim Bool 𝕜}
    (h : sk.observed = ∅) {M M' : Model C dim 𝕜}
    (heq : ∀ mix : ProbMixture C dim 𝕜, M.Δmix sk.gap mix.1 = M'.Δmix sk.gap mix.1) :
    sk.BehaviorEq M M' := by
  intro visible hvisible w mix
  rw [h] at hvisible
  rw [Finset.subset_empty.mp hvisible, Model.Δmask_empty, Model.Δmask_empty]
  exact heq mix

/-! ## The utility enters only through its gap

`def:margin` and the behavioural family are written with a utility
`u : {0,1} × dom(𝐙) → [0,1]`, but every condition that reads it reads
`g(z) = u(1,z) - u(0,z)`: (M2) and (M6) are inequalities on `gap`, (M3) is a sign
condition on `gap`, and `Δmask` takes the gap as its argument. (M1) and (M4) are
conditions on the model alone, and (M5) reads only the two variable sets.

The two theorems below say exactly that, and they are what makes MAIS-O24's
`u`-coordinates a *reading* of print rather than a guess. `prob:effective` writes
its polynomials in `(θ, u)` and simultaneously sets `S = K(G) + 2^{|𝐙|}`, which
counts one coordinate per utility-parent configuration where a raw `u` has two.
The two sentences cannot both be transcribed. `gap_determines_marginClass` and
`gap_determines_behaviorEq` show which one carries the content: two skeletons
that share a shape and a gap are interchangeable in every condition
`prob:effective`'s conclusions (a) and (b) are stated over, so the second
`u`-coordinate is not information those conclusions can use. Conclusion (c),
which quantifies over `u` directly, is where the count is visible, and it is the
count print states. -/

/-- Two skeletons on the same shape with the same utility gap have the same
margin class. -/
public theorem gap_determines_marginClass {sk sk' : Skeleton C dim Bool 𝕜}
    (hobs : sk.observed = sk'.observed) (hz : sk.utilityParents = sk'.utilityParents)
    (hgap : sk.gap = sk'.gap) (M : Model C dim 𝕜) (lam : 𝕜) :
    sk.MarginClass M lam ↔ sk'.MarginClass M lam := by
  simp only [MarginClass, M2, M3, M5, M6, hobs, hz, hgap]

/-- And the same behavioural family, so `𝚫_M = 𝚫_{M'}` is a condition on the gap
rather than on the utility that produced it. -/
public theorem gap_determines_behaviorEq {sk sk' : Skeleton C dim Bool 𝕜}
    (hobs : sk.observed = sk'.observed) (hgap : sk.gap = sk'.gap)
    (M M' : Model C dim 𝕜) :
    sk.BehaviorEq M M' ↔ sk'.BehaviorEq M M' := by
  simp only [BehaviorEq, hobs, hgap]

end Skeleton


/-! ## Transport along the rational cast

A witness checked at `ℚ` has a canonical image at every characteristic-zero
ordered field, and that image keeps exactly what the source's question asks
about: membership in the margin class, and the whole behavioural family. This is
what lets a counterexample computed on rational literals answer a question the
agenda states over the reals, without a second kernel and without restating the
witness.
-/

section Transport

variable {𝕝 : Type*} [Field 𝕝] [LinearOrder 𝕝] [IsStrictOrderedRing 𝕝] [CharZero 𝕝]

/-- A rational intervention mixture read in any characteristic-zero ordered
field. The weights do not move; only the field they are read in does.

This is not a convenience. MAIS-A2 `subsec:queries` fixes the analyst's queries
to be triples *"`(σ_t, 𝐎'_t, w_t)` with **rational** mixture weights"*, while
`def:margin`'s tables are real. So a query is genuinely a rational object acting
on a real model, and the two fields have to meet somewhere; this is that place.
Widening the weights to the value field instead would state a query problem the
source does not pose. -/
@[expose] public def ProbMixture.mapRat (w : ProbMixture C dim ℚ)
    (𝕝 : Type*) [Field 𝕝] [LinearOrder 𝕝] [IsStrictOrderedRing 𝕝] [CharZero 𝕝] :
    ProbMixture C dim 𝕝 :=
  ⟨fun σ ↦ ((w.1 σ : ℚ) : 𝕝), by
    constructor
    · intro σ
      show (0 : 𝕝) ≤ ((w.1 σ : ℚ) : 𝕝)
      exact_mod_cast w.2.1 σ
    · have hsum : ∑ σ : InterventionProfile C dim, ((w.1 σ : ℚ) : 𝕝)
          = ((∑ σ : InterventionProfile C dim, w.1 σ : ℚ) : 𝕝) := by
        rw [show ((∑ σ : InterventionProfile C dim, w.1 σ : ℚ) : 𝕝)
            = Rat.castHom 𝕝 (∑ σ : InterventionProfile C dim, w.1 σ) from rfl, map_sum]
        rfl
      show ∑ σ : InterventionProfile C dim, ((w.1 σ : ℚ) : 𝕝) = 1
      rw [hsum, w.2.2, Rat.cast_one]⟩

/-- A rational model read in any characteristic-zero ordered field. The graph is
untouched; only the tables move. -/
@[expose] public def Model.mapRat (M : Model C dim ℚ)
    (𝕝 : Type*) [Field 𝕝] [LinearOrder 𝕝] [IsStrictOrderedRing 𝕝] [CharZero 𝕝] :
    Model C dim 𝕝 where
  dim_pos := M.dim_pos
  parents := M.parents
  acyclic := M.acyclic
  cpt := fun c a v ↦ ((M.cpt c a v : ℚ) : 𝕝)
  cpt_parents := fun c a v w h ↦ by rw [M.cpt_parents c a v w h]
  cpt_nonneg := fun c a v ↦ by exact_mod_cast M.cpt_nonneg c a v
  cpt_sum := fun c v ↦ by
    have h := congrArg (Rat.castHom 𝕝) (M.cpt_sum c v)
    rw [map_sum, map_one] at h
    simpa [Rat.coe_castHom] using h

@[simp] public theorem Model.parents_mapRat (M : Model C dim ℚ) :
    (M.mapRat 𝕝).parents = M.parents := rfl

@[simp] public theorem Model.cpt_mapRat (M : Model C dim ℚ) (c : C) (a : Fin (dim c))
    (v : Assignment C dim) : (M.mapRat 𝕝).cpt c a v = ((M.cpt c a v : ℚ) : 𝕝) := rfl

public theorem Model.factor_mapRat (M : Model C dim ℚ)
    (σ : InterventionProfile C dim) (v : Assignment C dim) (c : C) :
    (M.mapRat 𝕝).factor σ v c = ((M.factor σ v c : ℚ) : 𝕝) := by
  simp only [Model.factor, Model.mapRat]
  rw [show ((∑ a : Fin (dim c), if σ c a = v c then M.cpt c a v else 0 : ℚ) : 𝕝)
      = Rat.castHom 𝕝 (∑ a : Fin (dim c), if σ c a = v c then M.cpt c a v else 0) from rfl,
    map_sum]
  exact Finset.sum_congr rfl fun a _ ↦ by
    by_cases hb : σ c a = v c <;> simp [hb]

public theorem Model.jointProb_mapRat (M : Model C dim ℚ)
    (σ : InterventionProfile C dim) (v : Assignment C dim) :
    (M.mapRat 𝕝).jointProb σ v = ((M.jointProb σ v : ℚ) : 𝕝) := by
  simp only [Model.jointProb]
  rw [show ((∏ c : C, M.factor σ v c : ℚ) : 𝕝) = Rat.castHom 𝕝 (∏ c : C, M.factor σ v c) from rfl,
    map_prod]
  exact Finset.prod_congr rfl fun c _ ↦ M.factor_mapRat σ v c

/-- A rational skeleton read in the same field. -/
@[expose] public def Skeleton.mapRat (sk : Skeleton C dim Bool ℚ)
    (𝕝 : Type*) [Field 𝕝] [LinearOrder 𝕝] [IsStrictOrderedRing 𝕝] [CharZero 𝕝] :
    Skeleton C dim Bool 𝕝 where
  observed := sk.observed
  utilityParents := sk.utilityParents
  utility := fun d v ↦ ((sk.utility d v : ℚ) : 𝕝)
  utility_parents := fun d v w h ↦ by rw [sk.utility_parents d v w h]
  utility_mem_unitInterval := fun d v ↦ by
    obtain ⟨h0, h1⟩ := sk.utility_mem_unitInterval d v
    exact ⟨by exact_mod_cast h0, by exact_mod_cast h1⟩

@[simp] public theorem Skeleton.observed_mapRat (sk : Skeleton C dim Bool ℚ) :
    (sk.mapRat 𝕝).observed = sk.observed := rfl

@[simp] public theorem Skeleton.utilityParents_mapRat (sk : Skeleton C dim Bool ℚ) :
    (sk.mapRat 𝕝).utilityParents = sk.utilityParents := rfl

@[simp] public theorem Skeleton.gap_mapRat (sk : Skeleton C dim Bool ℚ)
    (v : Assignment C dim) : (sk.mapRat 𝕝).gap v = ((sk.gap v : ℚ) : 𝕝) := by
  simp [Skeleton.gap, Skeleton.mapRat]

/-- **Margin-class membership transports.** All six conditions are inequalities,
absolute values, or statements about the graph, and the cast preserves each. -/
public theorem Skeleton.marginClass_mapRat {sk : Skeleton C dim Bool ℚ}
    {M : Model C dim ℚ} {lam : ℚ} (h : sk.MarginClass M lam) :
    (sk.mapRat 𝕝).MarginClass (M.mapRat 𝕝) ((lam : ℚ) : 𝕝) := by
  obtain ⟨⟨hl0, hl2⟩, h1, h2, h3, h4, h5, h6⟩ := h
  have hhalf : ((lam : ℚ) : 𝕝) < 1 / 2 := by
    rw [show (1 : 𝕝) / 2 = ((1 / 2 : ℚ) : 𝕝) by norm_num]
    exact_mod_cast hl2
  refine ⟨⟨by exact_mod_cast hl0, hhalf⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro c a v
    obtain ⟨ha, hb⟩ := h1 c a v
    simp only [Model.cpt_mapRat]
    refine ⟨by exact_mod_cast ha, ?_⟩
    rw [show (1 : 𝕝) - ((lam : ℚ) : 𝕝) = ((1 - lam : ℚ) : 𝕝) by push_cast; ring]
    exact_mod_cast hb
  · intro v
    rw [Skeleton.gap_mapRat, ← Rat.cast_abs]
    exact_mod_cast h2 v
  · intro w
    obtain ⟨vp, vm, hp, hm, hgp, hgm⟩ := h3 w
    refine ⟨vp, vm, hp, hm, ?_, ?_⟩
    · rw [Skeleton.gap_mapRat]; exact_mod_cast hgp
    · rw [Skeleton.gap_mapRat]; exact_mod_cast hgm
  · intro c p hp
    obtain ⟨v, x, y, a, hxy, hle⟩ := h4 c p (by simpa using hp)
    refine ⟨v, x, y, a, hxy, ?_⟩
    rw [Model.cpt_mapRat, Model.cpt_mapRat, ← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast hle
  · exact ⟨fun t ht hclosed ↦ h5.1 t (by simpa using ht) (by simpa [Model.ParentClosed] using hclosed),
      by simpa using h5.2⟩
  · intro j hj
    obtain ⟨v, x, y, hxy, hle⟩ := h6 j (by simpa using hj)
    refine ⟨v, x, y, hxy, ?_⟩
    rw [Skeleton.gap_mapRat, Skeleton.gap_mapRat, ← Rat.cast_sub, ← Rat.cast_abs]
    exact_mod_cast hle

/-- **The behavioural family transports.** The target field's mixture space is
strictly larger than the image of the rational one, so this is not a cast of the
hypothesis: `Δmask_eq_on_probMixture_iff` first reduces both sides to agreement
at each deterministic profile, and it is that finite identity which casts. -/
public theorem Skeleton.behaviorEq_mapRat {sk : Skeleton C dim Bool ℚ}
    {M M' : Model C dim ℚ} (h : sk.BehaviorEq M M') :
    (sk.mapRat 𝕝).BehaviorEq (M.mapRat 𝕝) (M'.mapRat 𝕝) := by
  intro visible hvisible w mix
  have hrat : ∀ σ : InterventionProfile C dim,
      (∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
        ∀ c ∈ visible, v c = w c), M.jointProb σ v * sk.gap v) =
      ∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
        ∀ c ∈ visible, v c = w c), M'.jointProb σ v * sk.gap v :=
    (Model.Δmask_eq_on_probMixture_iff M M' sk.gap visible w).mp
      (fun m ↦ h visible (by simpa using hvisible) w m)
  refine (Model.Δmask_eq_on_probMixture_iff (M.mapRat 𝕝) (M'.mapRat 𝕝)
    (sk.mapRat 𝕝).gap visible w).mpr ?_ mix
  intro σ
  have hcast : ∀ N : Model C dim ℚ,
      (∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
        ∀ c ∈ visible, v c = w c), (N.mapRat 𝕝).jointProb σ v * (sk.mapRat 𝕝).gap v)
      = (((∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
        ∀ c ∈ visible, v c = w c), N.jointProb σ v * sk.gap v : ℚ)) : 𝕝) := by
    intro N
    rw [show (((∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
        ∀ c ∈ visible, v c = w c), N.jointProb σ v * sk.gap v : ℚ)) : 𝕝)
      = Rat.castHom 𝕝 (∑ v ∈ Finset.univ.filter (fun v : Assignment C dim ↦
        ∀ c ∈ visible, v c = w c), N.jointProb σ v * sk.gap v) from rfl, map_sum]
    exact Finset.sum_congr rfl fun v _ ↦ by
      rw [N.jointProb_mapRat, Skeleton.gap_mapRat, map_mul]
      simp
  rw [hcast M, hcast M', hrat σ]

end Transport

end AISafetyAtlas.Causal
